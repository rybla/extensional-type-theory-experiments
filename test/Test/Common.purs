module Test.Common where

import Prelude

import Control.Monad.Error.Class (class MonadThrow)
import Effect.Exception (Error)
import Test.Spec.Assertions as SA

shouldEqual ∷ ∀ (m ∷ Type -> Type) (t ∷ Type). MonadThrow Error m ⇒ Show t ⇒ Eq t ⇒ t → t → m Unit
shouldEqual x y = unless (x == y) $ SA.fail $
  show x <> " ≠\n  " <> show y <> "\n"