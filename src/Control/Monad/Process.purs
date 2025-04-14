-- | The `Process` monad combines the `Except`, `Reader`, `Writer`, and `State`
-- | monads into one big monad.
module Control.Monad.Process where

import Prelude

import Control.Monad.Error.Class (class MonadError, class MonadThrow)
import Control.Monad.Except (class MonadTrans, ExceptT, runExceptT)
import Control.Monad.Reader (class MonadAsk, class MonadReader, ReaderT, runReaderT)
import Control.Monad.State (class MonadState, StateT, runStateT)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Writer (class MonadTell, class MonadWriter, WriterT, runWriterT)
import Data.Bifunctor (lmap)
import Data.Either.Nested (type (\/))
import Data.Identity (Identity)
import Data.Newtype (class Newtype, unwrap)
import Data.Tuple.Nested (type (/\), (/\))

newtype ProcessT e w r s m a = ProcessT (ExceptT e (WriterT w (ReaderT r (StateT s m))) a)

type Error e w s = s /\ w /\ e

derive instance Newtype (ProcessT e w r s m a) _

derive newtype instance (Monad m, Monoid w) => Functor (ProcessT e w r s m)
derive newtype instance (Monad m, Monoid w) => Apply (ProcessT e w r s m)
derive newtype instance (Monad m, Monoid w) => Bind (ProcessT e w r s m)
derive newtype instance (Monad m, Monoid w) => Applicative (ProcessT e w r s m)
derive newtype instance (Monad m, Monoid w) => Monad (ProcessT e w r s m)

instance (Monad m, Monoid w) => MonadTrans (ProcessT e w r s) where
  lift m = ProcessT $ lift $ lift $ lift $ lift m

derive newtype instance (Monad m, Monoid w) => MonadThrow e (ProcessT e w r s m)
derive newtype instance (Monad m, Monoid w) => MonadError e (ProcessT e w r s m)

derive newtype instance (Monad m, Monoid w) => MonadTell w (ProcessT e w r s m)
derive newtype instance (Monad m, Monoid w) => MonadWriter w (ProcessT e w r s m)

derive newtype instance (Monad m, Monoid w) => MonadAsk r (ProcessT e w r s m)
derive newtype instance (Monad m, Monoid w) => MonadReader r (ProcessT e w r s m)

derive newtype instance (Monad m, Monoid w) => MonadState s (ProcessT e w r s m)

runProcessT
  ∷ ∀ e a w r s m
   . Monad m
  => r
  → s
  → ProcessT e w r s m a
  → m (Error e w s \/ a)
runProcessT r s (ProcessT m) = m
  # runExceptT
  # runWriterT
  # flip runReaderT r
  # flip runStateT s
  # map (\((e_a /\ w) /\ s') -> e_a # lmap \e -> s' /\ w /\ e)

type Process e w r s = ProcessT e w r s Identity

runProcess
  ∷ ∀ e a w r s
  . r
  → s
  → Process e w r s a
  → Error e w s \/ a
runProcess r s m = m
  # runProcessT r s
  # unwrap

