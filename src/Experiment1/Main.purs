module Experiment1.Main where

import Prelude

import Data.Eq.Generic (genericEq)
import Data.Generic.Rep (class Generic)
import Data.List (List)
import Data.List as List
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.Show.Generic (genericShow)
import Effect (Effect)
import Effect.Class.Console as Console

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
  = VarDrv VarDrv
  | AppDrv Drv Drv
  | LamDrv Drv
  | PiDrv Drv Drv
  | UniDrv
  | TacticDrv Tactic (Maybe (List Drv))

instance Show Drv where
  show (VarDrv x) = show x
  show (AppDrv f a) = "(" <> show f <> " " <> show a <> ")"
  show (LamDrv b) = "(λ " <> show b <> ")"
  show (PiDrv alpha beta) = "(Π " <> show alpha <> " . " <> show beta <> ")"
  show UniDrv = "𝒰"
  show (TacticDrv (Tactic t) mb_kids) = "($" <> show t.name <> " " <> str_kids <> ")"
    where
    str_kids = case mb_kids of
      Nothing -> "..."
      Just kids -> kids # map show # List.intercalate " "

--------------------------------------------------------------------------------

data VarDrv
  = ZeroVarDrv
  | SucVarDrv VarDrv

instance Show VarDrv where
  show ZeroVarDrv = "O"
  show (SucVarDrv x) = "S" <> show x

--------------------------------------------------------------------------------

type Env = List Term

--------------------------------------------------------------------------------

type Ctx = List Term

--------------------------------------------------------------------------------

type Var = Int

--------------------------------------------------------------------------------

newtype Tactic = Tactic
  { name :: String
  , call ::
      { ctx :: Ctx
      , env :: Env
      , goal :: Term
      , kids :: Maybe (List Drv)
      }
      -> Maybe
           { drv :: Drv
           , kids :: List Drv
           }
  }

derive instance Generic Tactic _

derive instance Newtype Tactic _

