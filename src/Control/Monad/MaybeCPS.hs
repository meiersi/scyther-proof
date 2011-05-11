{-# LANGUAGE RankNTypes #-}
module Control.Monad.MaybeCPS where

-- IDEA: Use continuation passing style to get rid of pattern matching in
-- successful cases.
--
-- Didn't really work for the entailment check.
--
-- cf. http://www.haskell.org/haskellwiki/Performance/Monads

import Control.Monad

newtype MaybeCPS a = MaybeCPS { unMaybeCPS :: forall r. (a -> Maybe r) -> Maybe r }
 
runMaybeCPS m = unMaybeCPS m return
 
-- The Cont definitions of return and (>>=)
instance Monad MaybeCPS where
    return a = MaybeCPS (\k -> k a)
    MaybeCPS m >>= f = MaybeCPS (\k -> m (\a -> unMaybeCPS (f a) k))

instance MonadPlus MaybeCPS where
    mzero = MaybeCPS (\_ -> Nothing) -- equivalent to MaybeCPS (Nothing >>=)
    m `mplus` n = case runMaybeCPS m of
                      Nothing -> n
                      Just a  -> return a
