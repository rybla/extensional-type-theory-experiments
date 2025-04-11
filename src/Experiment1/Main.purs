module Experiment1.Main where

import Prelude

import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Reader (ReaderT, ask, local, runReaderT)
import Control.Monad.State (StateT, get, runStateT)
import Control.Monad.Writer (WriterT, runWriterT)
import Control.Plus (empty)
import Data.Either.Nested (type (\/))
import Data.Eq.Generic (genericEq)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Generic.Rep (class Generic)
import Data.Identity (Identity)
import Data.List (List, (:))
import Data.List as List
import Data.Maybe (Maybe(..), maybe)
import Data.Newtype (class Newtype, unwrap)
import Data.Show.Generic (genericShow)
import Data.Traversable (sequence)
import Data.Tuple.Nested (type (/\))
import Effect (Effect)
import Effect.Class.Console as Console
import Partial.Unsafe (unsafeCrashWith)

--------------------------------------------------------------------------------

main :: Effect Unit
main = do
  Console.log "Experiment1.main"

--------------------------------------------------------------------------------

data Term
  = VarTerm Var
  | AppTerm Term Term
  | LamTerm Term
  | PiTerm Term Term
  | UniTerm

derive instance Generic Term _

instance Show Term where
  show x = genericShow x

instance Eq Term where
  eq x = genericEq x

--------------------------------------------------------------------------------

data Drv
  = VarDrv { gamma :: Ctx, ty :: Term } Var
  | AppDrv { gamma :: Ctx, dom :: Term, cod :: Term } Drv Drv
  | LamDrv { gamma :: Ctx, dom :: Term, cod :: Term } Drv
  | PiDrv { gamma :: Ctx } Drv Drv
  | UniDrv { gamma :: Ctx }
  | HoleDrv { gamma :: Ctx, label :: String }
  | TacticDrv { gamma :: Ctx, ty :: Term } Tactic Drv

instance Show Drv where
  show (VarDrv _r x) = show x
  show (AppDrv _r f a) = "(" <> show f <> " " <> show a <> ")"
  show (LamDrv _r b) = "(λ " <> show b <> ")"
  show (PiDrv _r dom cod) = "(Π " <> show dom <> " . " <> show cod <> ")"
  show (UniDrv _r) = "𝒰"
  show (HoleDrv r) = "?" <> r.label
  show (TacticDrv _r (Tactic t) _args) = "($" <> show t.name <> " ...)"

extractTerm :: Drv -> Maybe Term
extractTerm = go
  where
  go :: Drv -> Maybe Term
  go (VarDrv _r x) = pure $ VarTerm x
  go (AppDrv _r f a) = AppTerm <$> go f <*> (go a)
  go (LamDrv _r b) = LamTerm <$> go b
  go (PiDrv _r dom cod) = PiTerm <$> go dom <*> go cod
  go (UniDrv _r) = pure UniTerm
  go (HoleDrv _r) = Nothing
  go (TacticDrv _r _t _mb_args) = Nothing

extractType :: Drv -> Maybe Term
extractType = go
  where
  go :: Drv -> Maybe Term
  go (VarDrv r _x) = pure r.ty
  go (AppDrv r _f _a) = pure r.cod
  go (LamDrv r _b) = pure $ PiTerm r.dom r.cod
  go (PiDrv _r _dom _cod) = pure $ UniTerm
  go (UniDrv _r) = pure $ UniTerm
  go (HoleDrv _r) = Nothing
  go (TacticDrv _r _t _mb_args) = Nothing

--------------------------------------------------------------------------------

type BuildM a = ExceptT BuildErr (ReaderT BuildCtx (WriterT (Array BuildLog) (StateT BuildEnv Identity))) a

type BuildDrv = BuildM Drv

runBuildM
  :: forall a
   . BuildM a
  -> ((BuildErr \/ a) /\ Array BuildLog) /\ BuildEnv
runBuildM m = m
  # runExceptT
  # flip runReaderT
      { gamma: Ctx mempty
      , goal: empty
      }
  # runWriterT
  # flip runStateT {}
  # unwrap

type BuildCtx =
  { gamma :: Ctx
  , goal :: Maybe Term
  }

type BuildEnv =
  {
  }

type BuildErr =
  { ctx :: BuildCtx
  , env :: BuildEnv
  , msg :: String
  }

throwError_BuildM :: forall a. String -> BuildM a
throwError_BuildM msg = do
  ctx <- ask
  env <- get
  throwError { msg, env, ctx }

type BuildLog =
  { label :: String
  , msg :: String
  }

extractTermM :: Drv -> BuildM Term
extractTermM d = extractTerm d # flip maybe pure do
  throwError_BuildM $ "failed to extract term of " <> show d

extractTypeM :: Drv -> BuildM Term
extractTypeM d = extractType d # flip maybe pure do
  throwError_BuildM $ "failed to extract type of " <> show d

var :: Var -> BuildDrv
var x = do
  ctx <- ask
  ty <- lookup_Ctx x ctx.gamma # flip maybe (_.ty >>> pure) do
    throwError_BuildM $ "variable " <> show x <> " is out-of-bounds"
  pure $ VarDrv { gamma: ctx.gamma, ty } x

app :: BuildDrv -> BuildDrv -> BuildDrv
app m_func m_arg = do
  ctx <- ask
  func <- m_func
  { dom, cod } <- extractTypeM func >>= case _ of
    PiTerm dom cod -> pure { dom, cod }
    _ -> throwError_BuildM $ "cannot apply " <> show func <> " since it's not a function"
  arg <- m_arg
  ty_arg <- extractTypeM arg
  unless (dom == ty_arg) do
    throwError_BuildM $ "maltyped application of " <> show func <> " to argument " <> show arg <> " since the argument is expected to have type " <> show dom <> " but it actually has type " <> show ty_arg
  pure $ AppDrv { gamma: ctx.gamma, dom, cod } func arg

lam :: BuildDrv -> BuildDrv -> BuildDrv
lam m_doBuildDrv m_b = do
  ctx <- ask
  doBuildDrv <- m_doBuildDrv
  dom <- extractTermM doBuildDrv
  b <- local (_ { gamma = cons_Ctx dom ctx.gamma }) m_b
  cod <- extractTypeM b
  pure $ LamDrv { gamma: ctx.gamma, dom, cod } b

pi :: BuildDrv -> BuildDrv -> BuildDrv
pi m_dom m_cod = do
  ctx <- ask
  dom <- m_dom
  cod <- m_cod
  pure $ PiDrv { gamma: ctx.gamma } dom cod

uni :: BuildDrv
uni = do
  ctx <- ask
  pure $ UniDrv { gamma: ctx.gamma }

hole :: String -> BuildDrv
hole label = do
  ctx <- ask
  pure $ HoleDrv { gamma: ctx.gamma, label }

tactic :: Tactic -> List BuildDrv -> BuildDrv
tactic (Tactic t) args = do
  ctx <- ask
  drv <- t.call { gamma: ctx.gamma, goal: ctx.goal, args }
  ty <- extractTypeM drv
  pure $ TacticDrv { gamma: ctx.gamma, ty } (Tactic t) drv

--------------------------------------------------------------------------------

newtype Ctx = Ctx (List CtxItem)
type CtxItem = { tm :: Maybe Term, ty :: Term }

derive instance Newtype Ctx _

instance Show Ctx where
  show (Ctx ctx) = ctx # mapWithIndex f # List.intercalate ", "
    where
    f i x =
      show (Var i) <>
        case x.tm of
          Nothing -> " : " <> show x.ty
          Just tm -> " = " <> show tm <> " : " <> show x.ty

cons_Ctx :: Term -> Ctx -> Ctx
cons_Ctx ty (Ctx xs) = Ctx ({ tm: empty, ty } : xs)

lookup_Ctx :: Var -> Ctx -> Maybe CtxItem
lookup_Ctx (Var i) (Ctx xs) = xs List.!! i

--------------------------------------------------------------------------------

newtype Var = Var Int

derive instance Newtype Var _

instance Show Var where
  show (Var i) = "#" <> show i

derive newtype instance Eq Var

--------------------------------------------------------------------------------

newtype Tactic = Tactic
  { name :: String
  , call ::
      { gamma :: Ctx
      , goal :: Maybe Term
      , args :: List BuildDrv
      }
      -> BuildDrv
  }

derive instance Generic Tactic _

derive instance Newtype Tactic _

