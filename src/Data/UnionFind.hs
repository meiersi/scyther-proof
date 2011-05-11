{-# LANGUAGE DeriveDataTypeable #-}
-- | A persistent, but not so efficient union-find structure.
module Data.UnionFind where

import Prelude hiding (map)

import Control.Arrow
import Control.Applicative hiding (empty)

import Data.Maybe
import Data.Monoid
import qualified Data.List as L
import qualified Data.Map as M
import Data.Data


--  We store a map from every element to the representative of its equivalence
--  class which is the minimal element of the class.
newtype UnionFind a = UnionFind { unUnionFind :: M.Map a a }
  deriving( Eq, Ord, Show, Typeable )

instance Ord a => Monoid (UnionFind a) where
    mempty  = empty
    mappend = union

instance (Data a, Ord a) => Data (UnionFind a) where
     gfoldl k z (UnionFind a) = z (unionFind) `k` a

     gunfold k z c = case constrIndex c of
                         1 -> k (z (unionFind))
                         _ -> error "Data (UnionFind a): impossible"

     toConstr (UnionFind _) = con_UnionFind

     dataTypeOf _ = ty_T

con_UnionFind :: Constr
con_UnionFind = mkConstr ty_T "UnionFind" [] Prefix

ty_T :: DataType
ty_T = mkDataType "Data.UnionFind.UnionFind" [con_UnionFind]

-- | Smart constructor from a 'M.Map' to a union-find structure.
unionFind :: Ord a => M.Map a a -> UnionFind a
unionFind = fromList . M.toList

map :: (Ord a, Ord b) => (a -> b) -> UnionFind a -> UnionFind b
map f = fromList . fmap (f *** f) . toList

-- | @empty@ is the syntactic identity equivalence relation.
empty :: UnionFind a
empty = UnionFind M.empty

-- | @size uf@ returns the number of stored equalities.
size :: UnionFind a -> Int
size = M.size . unUnionFind

-- | @equate x y uf@ inserts the equality @x = y@ into @uf@.
equate :: Ord a => a -> a -> UnionFind a -> UnionFind a
equate x y (UnionFind uf) 
  | x == y    = UnionFind uf
  | otherwise = UnionFind $ 
      case (M.lookup x uf, M.lookup y uf) of
         (Nothing, Nothing)
           | x <= y    -> M.insert y x uf
           | otherwise -> M.insert x y uf
         
         (Just xr, Nothing)
           | xr <= x   -> M.insert y xr uf
           | otherwise -> M.insert y x $ update xr x uf
         
         (Nothing, Just yr)
           | yr <= y   -> M.insert x yr uf
           | otherwise -> M.insert x y $ update yr y uf

         (Just xr, Just yr)
           | xr <= yr  -> update yr xr uf
           | otherwise -> update xr yr uf
  where
    update old_rep new_rep = M.map upd
      where
        upd rep | rep == old_rep = new_rep
                | otherwise      = rep

fromList :: Ord a => [(a,a)] -> UnionFind a 
fromList = equateList empty

equateList :: Ord a => UnionFind a -> [(a,a)] -> UnionFind a
equateList = L.foldl' (flip $ uncurry equate)

toList :: UnionFind a -> [(a,a)]
toList = M.toList . unUnionFind

union :: Ord a => UnionFind a -> UnionFind a -> UnionFind a
union uf1 uf2 
  | size uf1 < size uf2 = equateList uf2 $ toList uf1
  | otherwise           = equateList uf1 $ toList uf2

-- | @find x uf@ returns the representative of the equivalence class that @x@
-- belongs to in @uf@, if there is any.
find :: Ord a => a -> UnionFind a -> Maybe a
find x = M.lookup x . unUnionFind

-- | @findWithDefault def x uf@ returns the representative of the equivalence
-- class that @x@ belongs to in @uf@ or @def@, if there is no representative.
findWithDefault :: Ord a => a -> a -> UnionFind a -> a
findWithDefault def x = M.findWithDefault def x . unUnionFind

-- | @(x,y) `equiv` uf@ iff @x@ and @y@ are in the same equivalence class with
-- respect to @uf@.
equiv :: Ord a => (a,a) -> UnionFind a -> Bool
equiv (x, y) uf =
    x == y || (fromMaybe False $ (==) <$> find x uf <*> find y uf)


