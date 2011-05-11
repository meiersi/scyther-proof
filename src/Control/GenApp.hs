{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, TypeFamilies, UndecidableInstances #-}
module Control.GenApp where

import Control.Applicative

infixl 9 #

newtype Fun a b = Fun {apply :: a -> b}

class Ap a b where
  type Res a b
  (#) :: a -> b -> Res a b

{- Missing equality constraint between second argument and first argument -}
instance Ap (a -> b) a where
  type Res (a -> b) a = b
  (#) = ($)

instance Applicative f => Ap (f (a -> b)) (f a) where
  type Res (f (a -> b)) (f a) = f b
  (#) = (<*>)

{- Interesting case: overlaps with case below: Either arguments or functions get auto-lifted
 
instance Applicative f => Ap (f (a -> b)) (a) where
  type Res (f (a -> b)) a = f b
  f # a = f <*> pure a

instance Functor f => Ap (a -> b) (f a) where
  type Res (a -> b) (f a) = f b
  (#) = fmap
-}

{- Auto-lifting conflicts generalization over functors:
 -
 - Problem:
    Conflicting family instance declarations:
      type instance Res (f (Fun a b)) (f a)
      type instance Res (Fun a b) (f a)
   
   Due to:
      type instance Res (f1 (Fun a1 b1)) (f1 a1)
    ==
      type instance Res (Fun a2 b2) (f2 a2)
 
    for
      f1 = Fun a2
      a1 = a2
      b2 = Fun a2 b1

     Res (Fun a2 (Fun a2 b1)) (Fun a2 a2) == (Fun a2 b1)
                                          /= (Fun a2 (Fun a2 b1))

   The first argument can be interpreted both as function in the functor 'Fun
   a2' or as an unlifted function mapping from 'a2' to 'Fun a2 b1'.
     
instance Functor f => Ap (Fun a b) (f a) where
  type Res (Fun a b) (f a) = f b
  f # a = fmap (apply f) a

-- | Here the class constraint should be: Pointed Functor
instance Applicative f => Ap (a -> b) (a) (f b) where
  f # a = pure (f a)

-}

-- head' :: Applicative f => f [a] -> f a
-- head' = liftA head

map' _ [] = []
map' f (x:xs) = (f # x) : map' f xs

test = map' (+(1)) [1..3]
