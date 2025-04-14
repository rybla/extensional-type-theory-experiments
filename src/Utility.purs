module Utility where

import Prelude

import Data.Maybe (Maybe, maybe)
import Partial.Unsafe (unsafeCrashWith)

fromMaybeM ∷ ∀ m a. Applicative m ⇒ m a → Maybe a -> m a
fromMaybeM = flip maybe pure

todo ∷ ∀ (a ∷ Type). String → a
todo msg = unsafeCrashWith $ "TODO: " <> msg

