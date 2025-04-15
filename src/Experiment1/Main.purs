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
import Data.Newtype (class Newtype, unwrap, wrap)
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
  = VarT Var
  | AppT Term Term
  | LamT Term
  | PiT Term Term
  | UniT
  | EqT Term Term
  | ReflT
  | AnyT

derive instance Generic Term _

instance Show Term where
  show (VarT x) = show x
  show (AppT f a) = "(" <> show f <> " " <> show a <> ")"
  show (LamT b) = "(λ " <> show b <> ")"
  show (PiT a b) = "(Π " <> show a <> " " <> show b <> ")"
  show UniT = "𝒰"
  show (EqT a b) = "(" <> show a <> " = " <> show b <> ")"
  show ReflT = "refl"
  show AnyT = "_"

instance Eq Term where
  eq x = genericEq x

varT i = VarT (wrap i)
appT f a = AppT f a
lamT b = LamT b
piT a b = PiT a b
uniT = UniT
eqT a b = EqT a b
reflT = ReflT
anyT = AnyT

subst :: Var -> Term -> Term -> Term
subst x t (VarT y) | x == y = t
subst _ _ (VarT y) | otherwise = VarT y
subst x t (AppT f a) = AppT (subst x t f) (subst x t a)
subst x t (LamT b) = LamT (subst (Newtype.modify (_ + 1) x) t b)
subst x t (PiT a b) = PiT (subst x t a) (subst (Newtype.modify (_ + 1) x) t b)
subst x t (EqT a b) = EqT (subst x t a) (subst x t b)
subst _ _ ReflT = ReflT
subst _ _ UniT = UniT
subst _ _ AnyT = AnyT

satisfies :: Term -> Term -> Boolean

satisfies AnyT _ = false

satisfies (VarT x) (VarT y) = x == y
satisfies _ (VarT _) = false

satisfies (AppT f a) (AppT f' a') = f `satisfies` f' && a `satisfies` a'
satisfies _ (AppT _ _) = false

satisfies (LamT b) (LamT b') = b `satisfies` b'
satisfies _ (LamT _) = false

satisfies (PiT a b) (PiT a' b') = a `satisfies` a' && b `satisfies` b'
satisfies _ (PiT _ _) = false

satisfies UniT UniT = true
satisfies _ UniT = false

satisfies (EqT a b) (EqT a' b') = a `satisfies` a' && b `satisfies` b'
satisfies _ (EqT _ _) = false

satisfies ReflT ReflT = true
satisfies _ ReflT = false

satisfies _ AnyT = true

--------------------------------------------------------------------------------
-- Drv
--------------------------------------------------------------------------------

data Drv
  = Var { gamma :: Ctx, ty :: Term } Var
  | App { gamma :: Ctx, dom :: Term, cod :: Term } Drv Drv
  | Lam { gamma :: Ctx, dom :: Term, cod :: Term } Drv
  | Pi { gamma :: Ctx } Drv Drv
  | Uni { gamma :: Ctx }
  | Eq { gamma :: Ctx } Drv Drv
  | Refl { gamma :: Ctx, ty :: Term }
  | Trans { gamma :: Ctx, ty0 :: Term, ty1 :: Term } Drv Drv
  | Ann { gamma :: Ctx, ty :: Term } Drv
  | Hole { gamma :: Ctx, goal :: Term, label :: String }
  | Tactic { gamma :: Ctx, ty :: Term } Tactic Drv

derive instance Generic Drv _

_ShowDrv_show_extra_info = false

instance Show Drv where
  show (Var r x) = (if _ShowDrv_show_extra_info then show r else "") <> show x
  show (App r f a) = (if _ShowDrv_show_extra_info then show r else "") <> "(" <> show f <> " " <> show a <> ")"
  show (Lam r b) = (if _ShowDrv_show_extra_info then show r else "") <> "(λ " <> show b <> ")"
  show (Pi r dom cod) = (if _ShowDrv_show_extra_info then show r else "") <> "(Π " <> show dom <> " . " <> show cod <> ")"
  show (Uni r) = (if _ShowDrv_show_extra_info then show r else "") <> "𝒰"
  show (Eq r a b) = (if _ShowDrv_show_extra_info then show r else "") <> "(" <> show a <> " = " <> show b <> ")"
  show (Refl r) = (if _ShowDrv_show_extra_info then show r else "") <> "refl"
  show (Trans r pf a) = (if _ShowDrv_show_extra_info then show r else "") <> "(trans " <> show pf <> " " <> show a <> ")"
  show (Ann r a) = (if _ShowDrv_show_extra_info then show r else "") <> "(" <> show a <> " :: " <> show r.ty <> ")"
  show (Hole r) = (if _ShowDrv_show_extra_info then show r else "") <> "?" <> r.label
  show (Tactic r (MkTactic t) a) = (if _ShowDrv_show_extra_info then show r else "") <> "($" <> t.name <> " ==> " <> show a <> ")"

instance Eq Drv where
  eq x = genericEq x

extractTerm :: Drv -> Maybe Term
extractTerm = go
  where
  go :: Drv -> Maybe Term
  go (Var _r x) = pure $ VarT x
  go (App _r f a) = AppT <$> go f <*> (go a)
  go (Lam _r b) = LamT <$> go b
  go (Pi _r dom cod) = PiT <$> go dom <*> go cod
  go (Uni _r) = pure UniT
  go (Eq _r a b) = EqT <$> go a <*> go b
  go (Refl _r) = pure UniT
  go (Trans _r _pf a) = extractTerm a
  go (Ann _r a) = go a
  go (Hole _r) = Nothing
  go (Tactic _r _t a) = extractTerm a

extractType :: Drv -> Maybe Term
extractType = go
  where
  go :: Drv -> Maybe Term
  go (Var r _x) = pure r.ty
  go (App r _f _a) = pure r.cod
  go (Lam r _b) = pure $ piT r.dom r.cod
  go (Pi _r _dom _cod) = pure uniT
  go (Uni _r) = pure uniT
  go (Eq _r _a _b) = pure uniT
  go (Refl r) = pure $ eqT r.ty r.ty
  go (Trans r _pf _a) = pure r.ty1
  go (Ann r _a) = pure r.ty
  go (Hole _r) = Nothing
  go (Tactic _r _t a) = extractType a

--------------------------------------------------------------------------------
-- BuildM
--------------------------------------------------------------------------------

type BuildM = Process BuildErr (Array BuildLog) BuildCtx BuildEnv

type BuildDrv = Ctx -> Term -> BuildM Drv

runBuildM :: forall a. BuildM a -> Process.Error BuildErr (Array BuildLog) BuildEnv \/ a
runBuildM m = m # runProcess ctx env
  where
  ctx = {}
  env = {}

type BuildCtx = {}

type BuildEnv = {}

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
var x gamma goal = do
  ty <- lookup_Ctx x gamma # flip maybe (_.ty >>> pure) do
    throwError $ "scope error: variable " <> show x <> " is out-of-bounds"
  unless (ty `satisfies` goal) do
    throwError $ "type error: variable " <> show x <> " is expected to have type " <> show goal <> " but actually has type " <> show ty
  pure $ Var { gamma: gamma, ty } x

app :: BuildDrv -> BuildDrv -> BuildDrv
app build_func build_arg gamma goal = do
  func <- build_func gamma (piT anyT anyT)
  { dom, cod } <- extractTypeM func >>= case _ of
    PiT dom cod -> pure { dom, cod }
    _ -> throwError $ "type error: cannot apply " <> show func <> " since it's not a function"
  arg <- build_arg gamma dom
  t_arg <- extractTermM arg
  ty_arg <- extractTypeM arg
  unless (dom == ty_arg) do
    throwError $ "type error: application of " <> show func <> " to argument " <> show arg <> " since the argument is expected to have type " <> show dom <> " but it actually has type " <> show ty_arg
  let cod' = subst (wrap 0) t_arg cod
  unless (cod' `satisfies` goal) do
    throwError $ "type error: application of " <> show func <> " to an argument is expected to have type " <> show goal <> " but the function has codomain " <> show cod'
  pure $ App { gamma: gamma, dom, cod: cod' } func arg

lam :: BuildDrv -> BuildDrv -> BuildDrv
lam build_dom build_b gamma goal = do
  domDrv <- build_dom gamma uniT
  dom <- extractTermM domDrv
  goal_b <- case goal of
    PiT a _b -> pure a
    AnyT -> pure AnyT
    _ -> throwError $ "type error: " <> show (lamT anyT) <> " cannot have type " <> show goal
  b <- build_b (dom ▹ gamma) goal_b
  cod <- extractTypeM b
  let ty = PiT cod dom
  unless (ty `satisfies` goal) do
    throwError $ "type error: " <> show (lamT anyT) <> " is expected to type " <> show goal <> " but actually has type " <> show ty
  pure $ Lam { gamma: gamma, dom, cod } b

pi :: BuildDrv -> BuildDrv -> BuildDrv
pi build_dom build_cod gamma goal = do
  let ty = UniT
  unless (ty `satisfies` goal) do
    throwError $ "type error: " <> show (piT anyT anyT) <> " is expected to have type " <> show goal <> " but actually has type " <> show ty
  dom <- build_dom gamma uniT
  cod <- build_cod (uniT ▹ gamma) uniT
  pure $ Pi { gamma: gamma } dom cod

uni :: BuildDrv
uni gamma goal = do
  let ty = UniT
  unless (uniT `satisfies` goal) do
    throwError $ "type error: " <> show uniT <> " is expected to have type " <> show goal <> " but actually has type " <> show ty
  pure $ Uni { gamma: gamma }

eq :: BuildDrv -> BuildDrv -> BuildDrv
eq build_a build_b gamma goal = do
  let ty = uniT
  unless (ty `satisfies` goal) do
    throwError $ "type error: " <> show (eqT anyT anyT) <> " is expected to have type " <> show goal <> " but actually has type " <> show ty
  a <- build_a gamma anyT
  b <- build_b gamma anyT
  pure $ Eq { gamma } a b

refl :: BuildDrv
refl gamma goal = do
  a <- case goal of
    EqT a b -> do
      unless (a == b) do
        throwError $ "type error: " <> show reflT <> " is expected to have type " <> show goal <> ", but " <> show a <> " /= " <> show b
      pure a
    _ -> throwError $ "type errro: " <> show reflT <> " is expected to have non-equality type " <> show goal
  pure $ Refl { gamma, ty: a }

trans :: BuildDrv -> BuildDrv -> BuildDrv
trans build_pf build_a gamma goal = do
  a <- build_a gamma anyT
  ty_a <- extractTypeM a
  pf <- build_pf gamma (eqT ty_a goal)
  pure $ Trans { gamma, ty0: ty_a, ty1: goal } pf a

ann :: BuildDrv -> Term -> BuildDrv
ann build_a ty gamma goal = do
  unless (ty `satisfies` goal) do
    throwError $ "type error: a term is expected have type " <> show goal <> " but is annotated to have type " <> show ty
  a <- build_a gamma ty
  pure $ Ann { gamma, ty } a

hole :: String -> BuildDrv
hole label gamma goal = do
  pure $ Hole { gamma: gamma, goal: goal, label }

tactic :: Tactic -> Array BuildDrv -> BuildDrv
tactic (MkTactic t) args gamma goal = do
  drv <- t.build args gamma goal
  ty <- extractTypeM drv
  pure $ Tactic { gamma: gamma, ty } (wrap t) drv

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
      "(" <> show (wrap i :: Var)
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
lookup_Ctx (MkVar i) (Ctx xs) = xs List.!! i

--------------------------------------------------------------------------------
-- Var
--------------------------------------------------------------------------------

newtype Var = MkVar Int

derive instance Newtype Var _

instance Show Var where
  show (MkVar i) = "#" <> show i

derive newtype instance Eq Var

--------------------------------------------------------------------------------
-- Tactic
--------------------------------------------------------------------------------

newtype Tactic = MkTactic
  { name :: String
  , build :: Array BuildDrv -> BuildDrv
  }

derive instance Generic Tactic _

derive instance Newtype Tactic _

instance Eq Tactic where
  eq (MkTactic t1) (MkTactic t2) = t1.name == t2.name

--------------------------------------------------------------------------------
-- Tactic Examples
--------------------------------------------------------------------------------

-- | Finds the first thing in context that satisfies the goal.
assumption :: Tactic
assumption = wrap
  { name: "assumption"
  , build: \_args gamma goal -> do
      let
        candidates = unwrap gamma # foldMapWithIndex \i -> case _ of
          x | x.ty `satisfies` goal -> pure { var: wrap i, ty: x.ty }
          _ -> mempty
      x <- case List.head candidates of
        Nothing -> throwError $ "assumption: no candidates"
        Just x -> pure x
      pure $ Var { gamma, ty: x.ty } x.var
  }

