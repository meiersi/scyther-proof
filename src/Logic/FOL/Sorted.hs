-- | Many-sorted first-order logic with equality.
module Logic.FOL.Sorted where

import Data.Maybe
import Data.List

import Control.Basics
import Text.PrettyPrint.Applicative

infixl 3 .&&
infixl 2 .||
infixr 1 .==>
infixl 1 .<==
infix  1 .<=>
infix  4 .==
infix  4 ./=

-- Utilities
------------

-- | Apply a function to the last element, if it exists.
mapLast :: (a -> a) -> [a] -> [a]
mapLast f = go
  where go [] = []
        go [x] = [f x]
        go (x:xs) = x : go xs


-- Types
--------

newtype Sort = Sort { getSort :: String }
  deriving(Eq, Ord)

instance Show Sort where
  show = getSort

newtype Id   = Id   { getId   :: String }
  deriving(Eq, Ord)

instance Show Id where
  show = getId

type SortedId = (Id, Sort)

data Fun = Fun SortedId [Sort]
  deriving(Eq, Ord, Show)

data Rel = Rel Id       [Sort]
  deriving(Eq, Ord, Show)

data Term = 
    Var SortedId
  | App Fun [Term]
  deriving(Eq, Ord, Show)

data BinOp = Conj | Disj | Imp | Equiv
  deriving(Eq, Ord, Show)

data Quant = All | Ex
  deriving(Eq, Ord, Show)

data Formula = 
    Top
  | Bot
  | In Rel [Term]
  | Neg Formula
  | BinOp BinOp Formula Formula
  | Quant Quant SortedId Formula
  deriving(Eq, Ord, Show)

idSort :: SortedId -> Sort
idSort = snd

funSort :: Fun-> Sort
funSort (Fun si _) = idSort si

termSort :: Term -> Sort
termSort (Var si)  = idSort si
termSort (App f _) = funSort f

sid :: String -> String -> SortedId
sid i s = (Id i, Sort s)

var :: String -> String -> Term
var = (Var.) . sid

apply :: Fun -> [Term] -> Term
apply f@(Fun _ ss) ts
  | ss == map termSort ts = App f ts
  | otherwise = 
      error $ "apply: '"++show f++"' to '"++show ts++"' - sorts don't agree"
  

const = flip apply []

neg = Neg
(.==) = eq
(./=) = (neg.) . eq
(.&&) = BinOp Conj
(.||) = BinOp Disj
(.<=>) = BinOp Equiv
(.==>) = BinOp Imp
(.<==) = flip (BinOp Imp)

univ :: SortedId -> Formula -> Formula
univ = Quant All

ex :: SortedId -> Formula -> Formula
ex = Quant Ex

eq :: Term -> Term -> Formula
eq x y 
  | sx == sy  = In (Rel (Id "=") [sx,sx]) [x,y]
  | otherwise = error $ "eq: sorts '"++show sx++"' and '"++show sy++"' do not agree."
  where
  sx = termSort x
  sy = termSort y

inRel :: Rel -> [Term] -> Formula
inRel r@(Rel _ sorts)  ts 
  | tss == sorts = In r ts
  | otherwise    = error $ "inRel: sorts '"++show tss++"' disagree with expected sorts '"++show sorts++"'"
  where
  tss = map termSort ts



conj :: [Formula] -> Formula
conj [] = Top
conj as = foldr1 (.&&) as

disj :: [Formula] -> Formula
disj [] = Bot
disj as = foldr1 (.||) as


-- Free algebra axioms
----------------------

indexedIds :: String -> [Id]
indexedIds v = [ Id (v ++ show i) | i <- [0..] ]

sortedSids :: String -> [Sort] -> [SortedId]
sortedSids v = zipWith (,) (indexedIds v)

sortedVars :: String -> [Sort] -> ([SortedId],[Term])
sortedVars v sorts = (sids, map Var sids)
  where sids = sortedSids v sorts

allArguments :: String -> Fun -> (Formula -> Formula, Term, [Term])
allArguments v f@(Fun _ sorts) = 
  (\t -> foldr univ t is, App f ts, ts)
  where 
  (is, ts) = sortedVars v sorts

injective :: MonadPlus m => Fun -> m Formula
injective f@(Fun _ [])    = mzero
injective f@(Fun _ sorts) = return . xquant . yquant $
  (fxs .== fys) .==> (conj $ zipWith (.==) xs ys)
  where
  (xquant, fxs, xs) = allArguments "X" f
  (yquant, fys, ys) = allArguments "Y" f
    
free :: Fun -> [Fun] -> [Formula]
free f@(Fun _ sorts) fs = do
  f'@(Fun _ sorts') <- fs
  let (ys, yvs) = sortedVars "Y" sorts'
  return $ foldr univ
    (App f xvs ./= App f' yvs)
    (xs ++ ys)
  where
  (xs, xvs) = sortedVars "X" sorts


freeAlgebra :: [Fun] -> [Formula]
freeAlgebra fs = 
  (fs >>= injective) <|>
  (zip fs (tail (tails fs)) >>= uncurry free)


-- Pretty Printing
------------------

ppId :: Document d => Id -> d
ppId = text . getId

ppSort :: Document d => Sort -> d
ppSort = text . getSort

ppSortedId :: Document d => SortedId -> d
ppSortedId (i, s) = ppId i <> colon <> ppSort s

ppTerm :: Document d => Term -> d
ppTerm (Var (i,_)) = ppId i
ppTerm (App (Fun (i,_) _) []) = ppId i
ppTerm (App (Fun (i,_) _) ts) = 
  sep (ppId i <> lparen <> arg : args)
  where
  (arg:args) = map (nest 1) . mapLast (<> rparen) . punctuate comma $ map ppTerm ts

ppFormula :: Document d => Formula -> d
ppFormula Top = text "true"
ppFormula Bot = text "false"
ppFormula (In (Rel i _) ts) = case getId i of
  [] -> error "ppFormula: empty identifier encountered"
  op | head op `elem` "=!<>" && length ts == 2 ->
    sep [ppTerm (ts !! 0) <-> text op, ppTerm (ts !! 1)]
  _ ->
    ppId i <> sep (lparen <> arg : map (nest 1) args)
  where
  (arg:args) = mapLast (<> rparen) . punctuate comma $ map ppTerm ts
ppFormula (Neg a) = text "not" <> parens (ppFormula a)
ppFormula (BinOp op a b) = 
  sep [parens (ppFormula a) <-> text (ppOp op), parens (ppFormula b)]
  where
  ppOp Conj  = "&"
  ppOp Disj  = "|"
  ppOp Imp   = "==>"
  ppOp Equiv = "<=>"
ppFormula (Quant q si a) = 
  sep [text (ppQuant q) <-> ppSortedId si <> text ".", nest 1 $ ppFormula a]
  where
  ppQuant All = "!"
  ppQuant Ex  = "?"

