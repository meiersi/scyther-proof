{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances, MultiParamTypeClasses #-}
--
-- | A monad supporting labeling of values and a monad transformer supporting
-- the consistent labeling of keys.
--
-- TODO: Split module into transformer part and type class instance part along
-- the lines of the transformers package.
module Control.Monad.Label where

import qualified Data.Map as M

import Control.Applicative hiding (empty)
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Reader


------------------------------------------------------------------------------
-- MonadLabel typeclass
------------------------------------------------------------------------------

-- | A monad allowing for labelling keys.
class (Applicative m, Monad m) => MonadLabel k l m where
  label :: k -> m l

-- Instances for other monad tranforerms
-- TODO: Add more

instance (MonadLabel k l m) => MonadLabel k l (StateT s m) where
    label = lift . label

instance (MonadLabel k l m) => MonadLabel k l (ReaderT r m) where
    label = lift . label


------------------------------------------------------------------------------
-- ConsistentLabelsT: Monad transformer for consistent labeling.
------------------------------------------------------------------------------

-- | A monad transformer implementing consistent (equal keys get equal labels)
-- labeling of keys with a sequence of labels.
newtype ConsistentLabelsT k l m a = ConsistentLabelsT {
    unConsistentLabelsT :: StateT ([l], M.Map k l) m a
  }
  deriving( Functor, Applicative, Monad, MonadTrans )

instance (Ord k, Applicative m, Monad m) => MonadLabel k l (ConsistentLabelsT k l m) where
  label k = ConsistentLabelsT $ do
    (ls, labelMap) <- get
    case M.lookup k labelMap of
      Just i  -> return i
      Nothing -> case ls of
        []      -> error "ConsistentLabelsT: label: no more labels left."
        (l:ls') -> do put (ls', M.insert k l labelMap)
                      return l

-- | Run a computation requiring consistent labels.
runConsistentLabelsT :: ConsistentLabelsT k l m a -> [l] -> m (a, ([l], M.Map k l))
runConsistentLabelsT m labels = runStateT (unConsistentLabelsT m) (labels, M.empty)

-- | Evaluate a computation requiring consistent labels.
evalConsistentLabelsT :: Functor m => ConsistentLabelsT k l m a -> [l] -> m a
evalConsistentLabelsT m labels = fst <$> runConsistentLabelsT m labels

-- | Execute a computation requiring consistent labels.
execConsistentLabelsT :: Functor m => ConsistentLabelsT k l m a -> [l] -> m ([l], M.Map k l)
execConsistentLabelsT m labels = snd <$> runConsistentLabelsT m labels


-- Default instance
-------------------

type ConsistentLabels k l = ConsistentLabelsT k l Identity

-- | Run a computation requiring consistent labels.
runConsistentLabels :: ConsistentLabels k l a -> [l] -> (a, ([l], M.Map k l))
runConsistentLabels m = runIdentity . runConsistentLabelsT m

-- | Evaluate a computation requiring consistent labels.
evalConsistentLabels :: ConsistentLabels k l a -> [l] -> a
evalConsistentLabels m = fst . runConsistentLabels m

-- | Execute a computation requiring consistent labels.
execConsistentLabels :: ConsistentLabels k l a -> [l] -> ([l], M.Map k l)
execConsistentLabels m = snd . runConsistentLabels m 





