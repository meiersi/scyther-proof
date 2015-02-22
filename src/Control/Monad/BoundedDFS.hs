{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, 
             FunctionalDependencies, GeneralizedNewtypeDeriving #-}
-- | A monad for implemented bounded depth-first-search and branch-and-bound
-- search.
module Control.Monad.BoundedDFS (
  -- * Costful operations
    MonadCost(..)

  -- * Unbounded depth-first-search 
  , UnboundedDFS(..)

  -- * Bounded depth-first-search
  , BoundedDFS(..)
  , runBoundedDFS
  , evalBoundedDFS
  , execBoundedDFS

  -- * Branch-and-bound search
  , BranchAndBound(..)
  , runBranchAndBound
  , evalBranchAndBound
  , execBranchAndBound
) where


import Control.Applicative
import Control.Monad
import Control.Monad.State
import Control.Monad.Reader




-- A typeclass for costful operations
------------------------------------------------------------------------------

-- | A monad with integer operation cost recording.
class Monad m => MonadCost c m | m -> c where
  -- | Mark the cost of the current operation.
  updateCost :: (c -> c) -> m ()

-- | An unbounded depth-first search monad for searches formulated using
-- MonadPlus.
newtype UnboundedDFS c a = UnboundedDFS { runUnboundedDFS :: Maybe a }
  deriving( Functor, Applicative, Monad )

instance MonadCost c (UnboundedDFS c) where
  updateCost _ = return ()

instance Alternative (UnboundedDFS c) where
  empty = mzero
  (<|>) = mplus

instance MonadPlus (UnboundedDFS c) where
  mzero                                       = UnboundedDFS $ mzero
  (UnboundedDFS m1) `mplus` (UnboundedDFS m2) = UnboundedDFS $ m1 `mplus` m2

-- | A cost bounded depth-first search monad.
--
-- All choices are handled committing and there is no differentiation between
-- failure due to cost overrun and other failures.
newtype BoundedDFS c a = BoundedDFS { unBoundedDFS :: ReaderT (c -> Bool) (StateT c Maybe) a }
  deriving( Functor, Applicative, Monad )

instance MonadCost c (BoundedDFS c) where
  updateCost f = BoundedDFS $ do
    cond <- ask
    b <- get
    let b' = f b
    guard (cond b')
    put b'

instance Alternative (BoundedDFS c) where
  empty = mzero
  (<|>) = mplus

instance MonadPlus (BoundedDFS c) where
  mzero = BoundedDFS mzero
  m `mplus` _ = m

-- | Run a cost bounded depth-first search.
runBoundedDFS :: BoundedDFS c a -> (c -> Bool) -> c -> Maybe (a, c)
runBoundedDFS m cond = runStateT (runReaderT (unBoundedDFS m) cond)

-- | Evaluate a cost bounded depth-first search.
evalBoundedDFS :: BoundedDFS c a -> (c -> Bool) -> c -> Maybe a
evalBoundedDFS m cond = fmap fst . runBoundedDFS m cond

-- | Execute a cost bounded depth-first search.
execBoundedDFS :: BoundedDFS c a -> (c -> Bool) -> c -> Maybe c
execBoundedDFS m cond = fmap snd . runBoundedDFS m cond

-- | A branch and bound monad for finding results with the smallest costs.
newtype BranchAndBound c a = 
  BranchAndBound { 
    unBranchAndBound :: ReaderT (c -> Bool) (StateT c Maybe) a 
  }
  deriving( Functor, Applicative, Monad )

-- | Run a branch and bound search.
runBranchAndBound :: Cost c => BranchAndBound c a -> c -> Maybe (a, c)
runBranchAndBound m bound 
  | zeroCost `lessEqCost` bound = 
      runStateT (runReaderT (unBranchAndBound m) (`lessEqCost` bound)) zeroCost
  | otherwise = mzero

-- | Evaluate a branch and bound search.
evalBranchAndBound :: Cost c => BranchAndBound c a -> c -> Maybe a
evalBranchAndBound m = fmap fst . runBranchAndBound m

-- | Execute a branch and bound search.
execBranchAndBound :: Cost c => BranchAndBound c a -> c -> Maybe c
execBranchAndBound m = fmap snd . runBranchAndBound m

instance MonadCost c (BranchAndBound c) where
  updateCost f = BranchAndBound $ do
    cond <- ask
    b <- get
    let b' = f b
    guard (cond b')
    put b'

class Eq c => Cost c where
  zeroCost      :: c
  addCosts      :: c -> c -> c
  subtractCosts :: c -> c -> c
  lessCost      :: c -> c -> Bool
  lessEqCost    :: c -> c -> Bool

  lessCost c1 c2   = lessEqCost c1 c2 && c1 /= c2
  lessEqCost c1 c2 = lessCost   c1 c2 || c1 == c2

instance (Ord a, Num a) => Cost (Maybe a) where
  zeroCost      = return 0
  addCosts      = liftM2 (+)
  subtractCosts Nothing  Nothing  = error "Cost (Maybe a): subtractCosts: cannot subtract infinity from infinity"
  subtractCosts Nothing  _        = Nothing
  subtractCosts (Just x) (Just y) = Just (x - y)
  subtractCosts _        Nothing  = error "Cost (Maybe a): subtractCosts: cannot subtract infinity"
  lessCost   Nothing  Nothing  = error "Cost (Maybe a): lessCost: cannot compare infinity with infinity"
  lessCost   _        Nothing  = True
  lessCost   (Just x) (Just y) = x < y
  lessCost   _        _        = error "Cost (Maybe a): lessCost: does this make sense?"
  lessEqCost Nothing  Nothing  = error "Cost (Maybe a): lessEqCost: cannot compare infinity with infinity"
  lessEqCost _        Nothing  = True
  lessEqCost (Just x) (Just y) = x <= y
  lessEqCost _        _        = error "Cost (Maybe a): lessEqcost: does this make sense?"

instance Cost c => MonadPlus (BranchAndBound c) where
  mzero = BranchAndBound $ mzero
  m1 `mplus` m2 = BranchAndBound $ 
    (do -- see if m1 get's through
        used <- get
        x1 <- unBranchAndBound m1
        m1Used <- get
        -- m1 did it, check if m2 gets through with new bound
        (local (const (`lessCost` (m1Used `subtractCosts` used))) $ do
           put zeroCost
           x2 <- unBranchAndBound m2
           modify (used `addCosts`)
           return x2
         `mplus`
         -- m2 didn't do it, return result of m1
         return x1)
     `mplus`
     -- m1 didn't do it, try m2
     unBranchAndBound m2)

instance Cost c => Alternative (BranchAndBound c) where
  empty = mzero
  (<|>) = mplus

