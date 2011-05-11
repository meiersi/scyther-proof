-- | Extends Control.Function with some direct implementations of
-- Control.Monad together with Control.Monad.Identity

module Extension.Data.Function where


-- | Chain the functions from right to left.
-- NOTE: This is exactly opposite as Control.Monad.sequence
sequenceI :: [a -> a] -> (a -> a)
sequenceI = foldr (.) id


-- | Only applies the function, if the condition is true.
whenI :: Bool -> (a -> a) -> (a -> a)
whenI p f   = if p then f else id

-- | Only applies the function, if the condition is false
unlessI :: Bool -> (a -> a) -> (a -> a)
unlessI p f = if p then id else f


