module Experiment1.Main where

import Prelude

import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Reader (ReaderT, ask, local, runReaderT)
import Control.Monad.State (StateT, get, runStateT)
import Control.Monad.Writer (WriterT, runWriterT)
import Control.Plus (empty)
import Data.Either.Nested (type (\/))
import Data.Eq.Generic (genericEq)
import Data.FoldableWithIndex (foldMapWithIndex)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Generic.Rep (class Generic)
import Data.Identity (Identity)
import Data.List (List(..), (:))
import Data.List as List
import Data.Maybe (Maybe(..), maybe)
import Data.Newtype (class Newtype, unwrap)
import Data.Tuple.Nested (type (/\))
import Effect (Effect)
import Effect.Class.Console as Console
import Partial.Unsafe (unsafeCrashWith)
import Utility (fromMaybeM)

--------------------------------------------------------------------------------
-- main
--------------------------------------------------------------------------------

main :: Effect Unit
main = do
  Console.log "Experiment1.main"

--------------------------------------------------------------------------------
-- Term
--------------------------------------------------------------------------------

data Term
  = VarTerm Var
  | AppTerm Term Term
  | LamTerm Term
  | PiTerm Term Term
  | UniTerm

derive instance Generic Term _

instance Show Term where
  show (VarTerm x) = show x
  show (AppTerm f a) = "(" <> show f <> " " <> show a <> ")"
  show (LamTerm b) = "(λ " <> show b <> ")"
  show (PiTerm a b) = "(Π " <> show a <> " " <> show b <> ")"
  show UniTerm = "𝒰"

instance Eq Term where
  eq x = genericEq x

varT i = VarTerm (Var i)
appT f a = AppTerm f a
lamT b = LamTerm b
piT a b = PiTerm a b
uniT = UniTerm

--------------------------------------------------------------------------------
-- Drv
--------------------------------------------------------------------------------

data Drv
  = VarDrv { gamma :: Ctx, ty :: Term } Var
  | AppDrv { gamma :: Ctx, dom :: Term, cod :: Term } Drv Drv
  | LamDrv { gamma :: Ctx, dom :: Term, cod :: Term } Drv
  | PiDrv { gamma :: Ctx } Drv Drv
  | UniDrv { gamma :: Ctx }
  | AnnDrv { gamma :: Ctx, ty :: Term } Drv
  | HoleDrv { gamma :: Ctx, goal :: Maybe Goal, label :: String }
  | TacticDrv { gamma :: Ctx, ty :: Term } Tactic Drv

derive instance Generic Drv _

_ShowDrv_show_extra_info = false

instance Show Drv where
  show (VarDrv r x) = (if _ShowDrv_show_extra_info then show r else "") <> show x
  show (AppDrv r f a) = (if _ShowDrv_show_extra_info then show r else "") <> "(" <> show f <> " " <> show a <> ")"
  show (LamDrv r b) = (if _ShowDrv_show_extra_info then show r else "") <> "(λ " <> show b <> ")"
  show (PiDrv r dom cod) = (if _ShowDrv_show_extra_info then show r else "") <> "(Π " <> show dom <> " . " <> show cod <> ")"
  show (UniDrv r) = (if _ShowDrv_show_extra_info then show r else "") <> "𝒰"
  show (AnnDrv r a) = (if _ShowDrv_show_extra_info then show r else "") <> "(" <> show a <> " :: " <> show r.ty <> ")"
  show (HoleDrv r) = (if _ShowDrv_show_extra_info then show r else "") <> "?" <> r.label
  show (TacticDrv r (Tactic t) a) = (if _ShowDrv_show_extra_info then show r else "") <> "($" <> t.name <> " ==> " <> show a <> ")"

instance Eq Drv where
  eq x = genericEq x

data Goal
  = TermGoal Term
  | PiGoal

derive instance Generic Goal _

instance Show Goal where
  show (TermGoal t) = show t
  show PiGoal = "(Π _ _)"

instance Eq Goal where
  eq x = genericEq x

extractTerm :: Drv -> Maybe Term
extractTerm = go
  where
  go :: Drv -> Maybe Term
  go (VarDrv _r x) = pure $ VarTerm x
  go (AppDrv _r f a) = AppTerm <$> go f <*> (go a)
  go (LamDrv _r b) = LamTerm <$> go b
  go (PiDrv _r dom cod) = PiTerm <$> go dom <*> go cod
  go (UniDrv _r) = pure UniTerm
  go (AnnDrv _r a) = go a
  go (HoleDrv _r) = Nothing
  go (TacticDrv _r _t a) = extractTerm a

extractType :: Drv -> Maybe Term
extractType = go
  where
  go :: Drv -> Maybe Term
  go (VarDrv r _x) = pure r.ty
  go (AppDrv r _f _a) = pure r.cod
  go (LamDrv r _b) = pure $ PiTerm r.dom r.cod
  go (PiDrv _r _dom _cod) = pure $ UniTerm
  go (UniDrv _r) = pure $ UniTerm
  go (AnnDrv r _a) = pure r.ty
  go (HoleDrv _r) = Nothing
  go (TacticDrv _r _t a) = extractType a

--------------------------------------------------------------------------------
-- BuildM
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
      { gamma: mempty
      , mb_goal: empty
      }
  # runWriterT
  # flip runStateT {}
  # unwrap

type BuildCtx =
  { gamma :: Ctx
  , mb_goal :: Maybe Goal
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
extractTermM d = extractTerm d # fromMaybeM do
  throwError_BuildM $ "failed to extract term of " <> show d

extractTypeM :: Drv -> BuildM Term
extractTypeM d = extractType d # fromMaybeM do
  throwError_BuildM $ "failed to extract type of " <> show d

--------------------------------------------------------------------------------
-- BuildDrv
--------------------------------------------------------------------------------

var :: Var -> BuildDrv
var x = do
  ctx <- ask
  ty <- lookup_Ctx x ctx.gamma # flip maybe (_.ty >>> pure) do
    throwError_BuildM $ "scope error: variable " <> show x <> " is out-of-bounds"
  ctx.mb_goal # maybe (pure unit) \goal -> unless (goal == TermGoal ty) do
    throwError_BuildM $ "type error: variable " <> show x <> " is expected to have type " <> show goal <> " but actually has type " <> show ty
  pure $ VarDrv { gamma: ctx.gamma, ty } x

app :: BuildDrv -> BuildDrv -> BuildDrv
app m_func m_arg = do
  ctx <- ask
  func <- local (_ { mb_goal = pure $ PiGoal }) m_func
  { dom, cod } <- extractTypeM func >>= case _ of
    PiTerm dom cod -> pure { dom, cod }
    _ -> throwError_BuildM $ "type error: cannot apply " <> show func <> " since it's not a function"
  arg <- local (_ { mb_goal = pure $ TermGoal dom }) m_arg
  ty_arg <- local (_ { mb_goal = pure $ TermGoal dom }) do extractTypeM arg
  unless (dom == ty_arg) do
    throwError_BuildM $ "type error: application of " <> show func <> " to argument " <> show arg <> " since the argument is expected to have type " <> show dom <> " but it actually has type " <> show ty_arg
  cod' <- unsafeCrashWith "TODO: substitute value of arg into cod" cod
  ctx.mb_goal # maybe (pure unit) \goal -> unless (goal == TermGoal cod') do
    throwError_BuildM $ "type error: application of " <> show func <> " to an argument is expected to have type " <> show goal <> " but the function has codomain " <> show cod'
  pure $ AppDrv { gamma: ctx.gamma, dom, cod: cod' } func arg

lam :: BuildDrv -> BuildDrv -> BuildDrv
lam m_dom m_b = do
  ctx <- ask
  domDrv <- local (_ { mb_goal = pure $ TermGoal UniTerm }) m_dom
  dom <- extractTermM domDrv
  goal_b <- case ctx.mb_goal of
    Just PiGoal -> pure Nothing
    Just (TermGoal (PiTerm a _b)) -> pure $ Just $ TermGoal a
    Just (TermGoal _) -> throwError_BuildM "type error: lam is expected to have non-pi type"
    _ -> pure Nothing
  b <- local (_ { gamma = dom ▹ ctx.gamma, mb_goal = goal_b }) m_b
  cod <- extractTypeM b
  case ctx.mb_goal of
    Just (TermGoal (PiTerm cod' dom')) -> do
      unless (dom == dom') do throwError_BuildM $ "type error: lam's dom is expected to be " <> show dom' <> " but it's actually " <> show dom
      unless (cod == cod') do throwError_BuildM $ "type error: lam's cod is expected to be " <> show cod' <> " but it's actually " <> show cod
    Just (TermGoal goal) -> throwError_BuildM $ "type error: lam is expected to have non-pi type: " <> show goal
    _ -> pure unit
  pure $ LamDrv { gamma: ctx.gamma, dom, cod } b

pi :: BuildDrv -> BuildDrv -> BuildDrv
pi m_dom m_cod = do
  ctx <- ask
  let ty = UniTerm
  ctx.mb_goal # maybe (pure unit) \goal -> unless (goal == TermGoal ty) do
    throwError_BuildM $ "type error: pi is expected to have type " <> show goal <> " but actually has type " <> show ty
  dom <- local (_ { mb_goal = pure $ TermGoal UniTerm }) m_dom
  cod <- local (_ { gamma = UniTerm ▹ ctx.gamma, mb_goal = pure $ TermGoal UniTerm }) m_cod
  pure $ PiDrv { gamma: ctx.gamma } dom cod

uni :: BuildDrv
uni = do
  ctx <- ask
  let ty = UniTerm
  ctx.mb_goal # maybe (pure unit) \goal -> unless (goal == TermGoal ty) do
    throwError_BuildM $ "type error: uni is expected to have type " <> show goal <> " but actually has type " <> show ty
  pure $ UniDrv { gamma: ctx.gamma }

ann :: Term -> BuildDrv -> BuildDrv
ann ty m_a = do
  ctx <- ask
  ctx.mb_goal # maybe (pure unit) case _ of
    PiGoal | PiTerm _ _ <- ty -> throwError_BuildM $ "type error: ann is expected to have a pi type but actually has type " <> show ty
    TermGoal goal | goal /= ty -> throwError_BuildM $ "type error: ann is expected to have type " <> show goal <> " but actually has type " <> show ty
    _ -> pure unit
  local (_ { mb_goal = pure $ TermGoal ty }) m_a

hole :: String -> BuildDrv
hole label = do
  ctx <- ask
  pure $ HoleDrv { gamma: ctx.gamma, goal: ctx.mb_goal, label }

tactic :: Tactic -> Array BuildDrv -> BuildDrv
tactic (Tactic t) args = do
  ctx <- ask
  drv <- t.call { gamma: ctx.gamma, mb_goal: ctx.mb_goal, args }
  ty <- extractTypeM drv
  pure $ TacticDrv { gamma: ctx.gamma, ty } (Tactic t) drv

--------------------------------------------------------------------------------
-- Ctx
--------------------------------------------------------------------------------

newtype Ctx = Ctx (List CtxItem)
type CtxItem = { tm :: Maybe Term, ty :: Term }

derive instance Newtype Ctx _

instance Show Ctx where
  show (Ctx Nil) = "∅"
  show (Ctx ctx) = ctx # mapWithIndex f # List.intercalate ", "
    where
    f i x =
      "(" <> show (Var i)
        <>
          ( case x.tm of
              Nothing -> " : " <> show x.ty
              Just tm -> " = " <> show tm <> " : " <> show x.ty
          )
        <> ")"

derive newtype instance Eq Ctx

derive newtype instance Semigroup Ctx

derive newtype instance Monoid Ctx

cons_Ctx :: Term -> Ctx -> Ctx
cons_Ctx ty (Ctx xs) = Ctx ({ tm: empty, ty } : xs)

infixr 6 cons_Ctx as ▹

lookup_Ctx :: Var -> Ctx -> Maybe CtxItem
lookup_Ctx (Var i) (Ctx xs) = xs List.!! i

--------------------------------------------------------------------------------
-- Var
--------------------------------------------------------------------------------

newtype Var = Var Int

derive instance Newtype Var _

instance Show Var where
  show (Var i) = "#" <> show i

derive newtype instance Eq Var

--------------------------------------------------------------------------------
-- Tactic
--------------------------------------------------------------------------------

newtype Tactic = Tactic
  { name :: String
  , call ::
      { gamma :: Ctx
      , mb_goal :: Maybe Goal
      , args :: Array BuildDrv
      }
      -> BuildDrv
  }

derive instance Generic Tactic _

derive instance Newtype Tactic _

instance Eq Tactic where
  eq (Tactic t1) (Tactic t2) = t1.name == t2.name

--------------------------------------------------------------------------------
-- Tactic Examples
--------------------------------------------------------------------------------

-- | Finds the first thing in context that satisfies the goal.
assumption :: Tactic
assumption = Tactic
  { name: "assumption"
  , call: \{ gamma, mb_goal, args: _ } -> do
      ty_goal <- case mb_goal of
        Just (TermGoal ty) -> pure ty
        _ -> throwError_BuildM $ "assumption: invalid goal: " <> show mb_goal
      let
        candidates = unwrap gamma # foldMapWithIndex \i x ->
          if x.ty == ty_goal then pure (Var i) else mempty
      x <- case List.head candidates of
        Nothing -> throwError_BuildM $ "assumption: no candidates"
        Just x -> pure x
      pure $ VarDrv { gamma, ty: ty_goal } x
  }

