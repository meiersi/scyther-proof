-- | Interacting with a first-order logic theorem prover using the TPTP format.
--
-- NOTE: Sort information is currently ignored.
module Logic.FOL.Sorted.TPTP where

import Data.Char
import Data.List
import Control.Basics

import Logic.FOL.Sorted

import Text.Article
import Text.PrettyPrint.Applicative

import Extension.Prelude

type Labeled a = (String,a)

data Problem = Problem {
    probIdent  :: String
  , probDesc   :: Description
  , probSign   :: Signature
  , probAxioms :: Article (Labeled Formula)
  , probProps  :: Article (Labeled Formula)
  }
  deriving( Eq, Ord, Show )

data Description = Description {
    descName   :: String
  , descLong   :: String
  , descStatus :: Status
  }
  deriving( Eq, Ord, Show )

data Status = Unsatisfiable | Satisfiable | Unknown
  deriving( Eq, Ord, Show )

data Signature = Signature {
    sigSorts :: [Sort]
  , sigFuns  :: [Fun]
  , sigRels  :: [Rel]
  }
  deriving( Eq, Ord, Show )


-- | MOVE
funId :: Fun -> Id
funId (Fun (i,_) _) = i

-- | MOVE
relId :: Rel -> Id
relId (Rel i _) = i

relSorts (Rel _ sorts) = sorts
funSorts (Fun _ sorts) = sorts

-- | MOVE
emptyLine :: Document d => d
emptyLine = text ""

tptpList :: String -> [Doc] -> Doc
tptpList name = vcat

tptpSeparator :: Doc
tptpSeparator = text $ "%" ++ replicate 79 '-'

tptpProblem :: Problem -> Doc
tptpProblem prob =
  vcat . intersperse emptyLine $
    [ text $ "% begin_problem(" ++ probIdent prob ++ ")."
    , tptpDescription $ probDesc   prob
    , tptpSignature   $ probSign   prob
    , tptpAxioms      $ probAxioms prob
    , tptpProperties  $ probProps  prob
    , text "% end_problem."
    ]

tptpDescription :: Description -> Doc
tptpDescription desc = emptyDoc
{-
  tptpList "descriptions"
    [ text $ "name( {*" ++ descName desc ++ "*} )."
    , text $ "author( {* scytherP -- a proof generating security protocol verifier *} )."
    , text $ "logic( {* Decryption-chain reasoning axiomatized in many-sorted FOL with equality *} )."
    , text "status(" <> tptpStatus (descStatus desc) <> text ")."
    , sep [ text "description( {*"
          , nest 2 . fsep . map text . words $ descLong desc
          , text "*} )."]
    ]
-}

tptpStatus :: Status -> Doc
tptpStatus Unsatisfiable = text "unsatisfiable"
tptpStatus Satisfiable   = text "satisfiable"
tptpStatus Unknown       = text "unknown"

tptpSignature :: Signature -> Doc
tptpSignature sig = emptyDoc
   {-
   tptpList "symbols"
     [ warning
     , mkList "functions"  (tptpSym funId funSorts) funs
     , mkList "predicates" (tptpSym relId relSorts) rels
     , mkList "sorts"      tptpSort                 sorts
     ]
   $-$ emptyLine $-$
   tptpList "declarations" (map declPred rels ++ map declFun funs)
   where
   sorts = nub $ sigSorts sig
   funs  = nub $ sigFuns  sig
   rels  = nub $ sigRels  sig
   tptpSym selId selSorts sym =
     parens $ tptpId (selId sym) <> comma <-> int (length (selSorts sym))
   mkList name tptp list =
     sep [text name <> lbrack, nest 2 . fsep . punctuate comma $ map tptp list, text "]."]
   warning
     | nubOn funId funs /= funs || nubOn relId rels /= rels =
         text "% WARNING: equal function or relation identifiers with differents sort used!"
     | otherwise = emptyDoc
   declPred r =
     text "predicate(" <>
     (text . getId . relId $ r) <>
     (hcat . map (\s -> comma <-> text (getSort s)) $ relSorts r) <>
     text ")."
   declFun f@(Fun (_,sort) _) =
     (tptpFormula $ quant $ In (Rel (Id (getSort sort)) (error "declFun: don't inspect")) [t]) <>
     text "."
     where
     (quant, t, _) = allArguments "x" f
   -}

tptpAxioms :: Article (Labeled Formula) -> Doc
tptpAxioms = tptpFormulaArticle "axiom"

tptpProperties :: Article (Labeled Formula) -> Doc
tptpProperties = tptpFormulaArticle "conjecture"

tptpFormulaArticle :: String -> Article (Labeled Formula) -> Doc
tptpFormulaArticle origin article =
  tptpList ("formulae(" ++ origin ++ ")") (map tptpSectioned $ getArticle article)
  where
  tptpSectioned (Math (lbl,a)) =
    sep [text $ "fof("++lbl++","++origin++",(", nest 1 (tptpFormula a) <-> text ") )."]
    $-$ emptyLine
  tptpSectioned (Text t) = text $ "% " ++ t
  tptpSectioned (Section i header) =
    (case i of
       0 -> emptyLines 1 $-$
            (linesToDoc . overline "%". underline "%" $ "%% " ++ header ++ " %%")
       1 -> emptyLines 1 $-$
            (linesToDoc . overline "%". underline "%" $ "% " ++ header)
       2 -> (linesToDoc . underline "%" $ "% " ++ header)
       _ -> text $ "% " ++ header)
    $-$ emptyLines 1




-- | Overline using the given linestyle the first line of the given string.
overline :: String -> String -> String
overline _ "" = ""
overline style t = unlines [take (length . head $ lines t) (cycle style), t]

-- | Underline using the given linestyle the last line of the given string.
underline :: String -> String -> String
underline _ "" = ""
underline style t = unlines [t, take (length . last $ lines t) (cycle style)]

-- | Convert string line breaks to document line breaks.
linesToDoc :: Document d => String -> d
linesToDoc = vcat . map text . lines

-- | n empty lines.
emptyLines :: Document d => Int -> d
emptyLines n = vcat . replicate n $ text ""


tptpId :: Document d => Id -> d
tptpId = text . getId

tptpLowerId (Id []) = error $ "tptpLowerId: empty identifier"
tptpLowerId (Id i)
  | isUpper (head i) = text $ "ss" ++ i
  | otherwise        = text i

tptpSort :: Document d => Sort -> d
tptpSort = text . getSort

tptpSortedId :: Document d => SortedId -> d
tptpSortedId = tptpId . fst

tptpTerm :: Document d => Term -> d
tptpTerm (Var (i,_)) = tptpId i
tptpTerm (App (Fun (i,_) _) []) = tptpLowerId i
tptpTerm (App (Fun (i,_) _) ts) =
  sep (tptpLowerId i <> lparen <> arg : args)
  where
  (arg:args) = map (nest 1) . mapLast (<> rparen) . punctuate comma $ map tptpTerm ts

tptpFormula :: Document d => Formula -> d
tptpFormula Top = text "$true"
tptpFormula Bot = text "$false"
tptpFormula (In (Rel i _) ts) =
  case getId i of
    []  -> error "tptpFormula: empty identifier encountered"
    op | head op `elem` "=!<>" && length ts == 2 ->
      sep [tptpTerm (ts !! 0) <-> text op, tptpTerm (ts !! 1)]
    _ -> tptpLowerId i <>
         sep (lparen <> arg : map (nest 1) args)
  where
  (arg:args) = mapLast (<> rparen) . punctuate comma $ map tptpTerm ts
tptpFormula (Neg a) = text "~" <> parens (tptpFormula a)
tptpFormula (BinOp op a b) =
  sep [ parens (tptpFormula a) <-> text (tptpOp op)
      , nest 1 . parens $ tptpFormula b]
  where
  tptpOp Conj  = "&"
  tptpOp Disj  = "|"
  tptpOp Imp   = "=>"
  tptpOp Equiv = "<=>"
tptpFormula fo0@(Quant q _ _)
  | any (isLower.head.getId.fst) sis =
      error $ "tptpFormula: lowercase variables '"++show sis++"' encountered."
  | otherwise =
      sep [ text (tptpQuant q) <-> brackets sis' <-> colon
          , nest 1 . parens $ tptpFormula fo]
  where
  (sis, fo) = gatherQuants q fo0
  sis' = hcat . punctuate comma $ map tptpSortedId sis
  tptpQuant All = "!"
  tptpQuant Ex  = "?"

-- | MOVE
gatherQuants :: Quant -> Formula -> ([SortedId], Formula)
gatherQuants q = go []
  where
  go sis fo0@(Quant q' si fo)
    | q' == q   = go (si:sis) fo
    | otherwise = (reverse sis, fo0)
  go sis fo0 = (reverse sis, fo0)


