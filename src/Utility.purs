module Utility where

import Prelude

import Data.Maybe (Maybe, maybe)

fromMaybeM ∷ ∀ m a. Applicative m ⇒ m a → Maybe a -> m a
fromMaybeM = flip maybe pure

