{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- | A simple abstract article type.
module Text.Article where

import Data.Monoid

data Sectioned a =
    Section Int String
  | Text String
  | Math a
  deriving( Eq, Ord, Show )

instance Functor Sectioned where
  fmap f (Section i s) = Section i s
  fmap f (Text s)      = Text s
  fmap f (Math x)      = Math (f x)

newtype Article a = Article { getArticle :: [Sectioned a] }
  deriving( Eq, Ord, Show, Monoid )

instance Functor Article where
  fmap f = Article . fmap (fmap f) . getArticle

mapIndent :: (Int -> Int) -> Sectioned a -> Sectioned a
mapIndent f (Section i title) = Section (f i) title
mapIndent f x                 = x

-- | Make the given article a sub-article with a given heading. All its
-- sections are indented accordingly.
subArticle :: String -> Article a -> Article a
subArticle header = 
  Article . (Section 0 header:) . map (mapIndent succ) . getArticle

prependMath :: a -> Article a -> Article a
prependMath x = Article . (Math x :) . getArticle

prependText :: String -> Article a -> Article a
prependText t = Article . (Text t :) . getArticle

appendMath :: a -> Article a -> Article a
appendMath x = Article . (++[Math x]) . getArticle

appendText :: String -> Article a -> Article a
appendText t = Article . (++[Text t]) . getArticle
