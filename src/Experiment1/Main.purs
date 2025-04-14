module Experiment1.Main where

import Prelude

import Control.Monad.Except (throwError)
import Control.Monad.Process (Process, runProcess)
import Control.Monad.Process as Process
import Data.Either.Nested (type (\/))
import Data.Eq.Generic (genericEq)
import Data.FoldableWithIndex (foldMapWithIndex)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Generic.Rep (class Generic)
import Data.List (List(..), (:))
import Data.List as List
import Data.Maybe (Maybe(..), maybe)
import Data.Newtype (class Newtype, unwrap)
import Data.Newtype as Newtype
import Data.Unfoldable (none)
import Effect (Effect)
import Effect.Class.Console as Console
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

subst :: Var -> Term -> Term -> Term
subst x t (VarTerm y) | x == y = t
subst _ _ (VarTerm y) | otherwise = VarTerm y
subst x t (AppTerm f a) = AppTerm (subst x t f) (subst x t a)
subst x t (LamTerm b) = LamTerm (subst (Newtype.modify (_ + 1) x) t b)
subst x t (PiTerm a b) = PiTerm (subst x t a) (subst (Newtype.modify (_ + 1) x) t b)
subst _ _ UniTerm = UniTerm

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

type BuildM = Process BuildErr (Array BuildLog) BuildCtx BuildEnv

type BuildDrv = Ctx -> Maybe Goal -> BuildM Drv

runBuildM :: forall a. BuildM a -> Process.Error BuildErr (Array BuildLog) BuildEnv \/ a
runBuildM m = m # runProcess ctx env
  where
  ctx = {}
  env = {}

type BuildCtx = {}

type BuildEnv = {}

-- type BuildErr = Process.Error String (Array BuildLog) BuildEnv
type BuildErr = String

type BuildLog =
  { label :: String
  , msg :: String
  }

extractTermM :: Drv -> BuildM Term
extractTermM d = extractTerm d # fromMaybeM do
  throwError $ "failed to extract term of " <> show d

extractTypeM :: Drv -> BuildM Term
extractTypeM d = extractType d # fromMaybeM do
  throwError $ "failed to extract type of " <> show d

--------------------------------------------------------------------------------
-- BuildDrv
--------------------------------------------------------------------------------

var :: Var -> BuildDrv
var x gamma mb_goal = do
  ty <- lookup_Ctx x gamma # flip maybe (_.ty >>> pure) do
    throwError $ "scope error: variable " <> show x <> " is out-of-bounds"
  mb_goal # maybe (pure unit) \goal -> unless (goal == TermGoal ty) do
    throwError $ "type error: variable " <> show x <> " is expected to have type " <> show goal <> " but actually has type " <> show ty
  pure $ VarDrv { gamma: gamma, ty } x

app :: BuildDrv -> BuildDrv -> BuildDrv
app build_func build_arg gamma mb_goal = do
  func <- build_func gamma (pure PiGoal)
  { dom, cod } <- extractTypeM func >>= case _ of
    PiTerm dom cod -> pure { dom, cod }
    _ -> throwError $ "type error: cannot apply " <> show func <> " since it's not a function"
  arg <- build_arg gamma (pure $ TermGoal dom)
  tbuild_arg <- extractTermM arg
  ty_arg <- extractTypeM arg
  unless (dom == ty_arg) do
    throwError $ "type error: application of " <> show func <> " to argument " <> show arg <> " since the argument is expected to have type " <> show dom <> " but it actually has type " <> show ty_arg
  let cod' = subst (Var 0) tbuild_arg cod
  mb_goal # maybe (pure unit) \goal -> unless (goal == TermGoal cod') do
    throwError $ "type error: application of " <> show func <> " to an argument is expected to have type " <> show goal <> " but the function has codomain " <> show cod'
  pure $ AppDrv { gamma: gamma, dom, cod: cod' } func arg

lam :: BuildDrv -> BuildDrv -> BuildDrv
lam build_dom build_b gamma mb_goal = do
  -- ctx <- ask
  domDrv <- build_dom gamma (pure $ TermGoal UniTerm)
  dom <- extractTermM domDrv
  goal_b <- case mb_goal of
    Just PiGoal -> pure Nothing
    Just (TermGoal (PiTerm a _b)) -> pure $ Just $ TermGoal a
    Just (TermGoal _) -> throwError "type error: lam is expected to have non-pi type"
    _ -> pure Nothing
  b <- build_b (dom ▹ gamma) goal_b
  cod <- extractTypeM b
  case mb_goal of
    Just (TermGoal (PiTerm cod' dom')) -> do
      unless (dom == dom') do throwError $ "type error: lam's dom is expected to be " <> show dom' <> " but it's actually " <> show dom
      unless (cod == cod') do throwError $ "type error: lam's cod is expected to be " <> show cod' <> " but it's actually " <> show cod
    Just (TermGoal goal) -> throwError $ "type error: lam is expected to have non-pi type: " <> show goal
    _ -> pure unit
  pure $ LamDrv { gamma: gamma, dom, cod } b

pi :: BuildDrv -> BuildDrv -> BuildDrv
pi build_dom build_cod gamma mb_goal = do
  let ty = UniTerm
  mb_goal # maybe (pure unit) \goal -> unless (goal == TermGoal ty) do
    throwError $ "type error: pi is expected to have type " <> show goal <> " but actually has type " <> show ty
  dom <- build_dom gamma (pure $ TermGoal UniTerm)
  cod <- build_cod (UniTerm ▹ gamma) (pure $ TermGoal UniTerm)
  pure $ PiDrv { gamma: gamma } dom cod

uni :: BuildDrv
uni gamma mb_goal = do
  let ty = UniTerm
  mb_goal # maybe (pure unit) \goal -> unless (goal == TermGoal ty) do
    throwError $ "type error: uni is expected to have type " <> show goal <> " but actually has type " <> show ty
  pure $ UniDrv { gamma: gamma }

ann :: Term -> BuildDrv -> BuildDrv
ann ty build_a gamma mb_goal = do
  mb_goal # maybe (pure unit) case _ of
    PiGoal | PiTerm _ _ <- ty -> throwError $ "type error: ann is expected to have a pi type but actually has type " <> show ty
    TermGoal goal | goal /= ty -> throwError $ "type error: ann is expected to have type " <> show goal <> " but actually has type " <> show ty
    _ -> pure unit
  build_a gamma (pure $ TermGoal ty)

hole :: String -> BuildDrv
hole label gamma mb_goal = do
  pure $ HoleDrv { gamma: gamma, goal: mb_goal, label }

tactic :: Tactic -> Array BuildDrv -> BuildDrv
tactic (Tactic t) args gamma mb_goal = do
  drv <- t.build args gamma mb_goal
  ty <- extractTypeM drv
  pure $ TacticDrv { gamma: gamma, ty } (Tactic t) drv

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
cons_Ctx ty (Ctx xs) = Ctx ({ tm: none, ty } : xs)

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
  , build :: Array BuildDrv -> BuildDrv
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
  , build: \_args gamma mb_goal -> do
      ty_goal <- case mb_goal of
        Just (TermGoal ty) -> pure ty
        _ -> throwError $ "assumption: invalid goal: " <> show mb_goal
      let
        candidates = unwrap gamma # foldMapWithIndex \i x ->
          if x.ty == ty_goal then pure (Var i) else mempty
      x <- case List.head candidates of
        Nothing -> throwError $ "assumption: no candidates"
        Just x -> pure x
      pure $ VarDrv { gamma, ty: ty_goal } x
  }

