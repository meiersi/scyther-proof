-- | Interacting with the SPASS theorem prover for sorted FOL with equality.
module Logic.FOL.Sorted.SPASS where

import Data.List
import Control.Basics

import Logic.FOL.Sorted

import Text.Article
import Text.PrettyPrint.Applicative

import Extension.Prelude


data Problem = Problem {
    probIdent  :: String
  , probDesc   :: Description
  , probSign   :: Signature
  , probAxioms :: Article Formula
  , probProps  :: Article Formula
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

dfgProblem :: Problem -> Doc
dfgProblem prob = 
  vcat . intersperse emptyLine $
    [ text $ "begin_problem(" ++ probIdent prob ++ ")."
    , dfgDescription $ probDesc   prob
    , dfgSignature   $ probSign   prob
    , dfgAxioms      $ probAxioms prob
    , dfgProperties  $ probProps  prob
    , text "end_problem."
    ]

dfgDescription :: Description -> Doc
dfgDescription desc =
  dfgList "descriptions"
    [ text $ "name( {*" ++ descName desc ++ "*} )."
    , text $ "author( {* scytherP -- a proof generating security protocol verifier *} )."
    , text $ "logic( {* Decryption-chain reasoning axiomatized in many-sorted FOL with equality *} )."
    , text "status(" <> dfgStatus (descStatus desc) <> text ")."
    , sep [ text "description( {*"
          , nest 2 . fsep . map text . words $ descLong desc
          , text "*} )."]
    ]

dfgStatus :: Status -> Doc
dfgStatus Unsatisfiable = text "unsatisfiable"
dfgStatus Satisfiable   = text "satisfiable"
dfgStatus Unknown       = text "unknown"

dfgList :: String -> [Doc] -> Doc
dfgList name ds = vcat $ text ("list_of_"++name++".") : map (nest 2) ds ++ [text "end_of_list."]

dfgSignature :: Signature -> Doc
dfgSignature sig =
   dfgList "symbols"
     [ warning
     , mkList "functions"  (dfgSym funId funSorts) funs
     , mkList "predicates" (dfgSym relId relSorts) rels
     , mkList "sorts"      dfgSort                 sorts
     ] 
   $-$ emptyLine $-$
   dfgList "declarations" (map declPred rels ++ map declFun funs)
   where
   sorts = nub $ sigSorts sig
   funs  = nub $ sigFuns  sig
   rels  = nub $ sigRels  sig
   dfgSym selId selSorts sym = 
     parens $ dfgId (selId sym) <> comma <-> int (length (selSorts sym))
   mkList name dfg list = 
     sep [text name <> lbrack, nest 2 . fsep . punctuate comma $ map dfg list, text "]."]
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
     (dfgFormula $ quant $ In (Rel (Id (getSort sort)) (error "declFun: don't inspect")) [t]) <>
     text "."
     where
     (quant, t, _) = allArguments "x" f

dfgAxioms :: Article Formula -> Doc
dfgAxioms = dfgFormulaArticle "axioms"

dfgProperties :: Article Formula -> Doc
dfgProperties = dfgFormulaArticle "conjectures"

dfgFormulaArticle :: String -> Article Formula -> Doc
dfgFormulaArticle origin article = 
  dfgList ("formulae(" ++ origin ++ ")") (map dfgSectioned $ getArticle article)
  where
  dfgSectioned :: Sectioned Formula -> Doc
  dfgSectioned (Math a) = 
    sep [text "formula(", nest 1 (dfgFormula a) <-> text ")."] $-$ emptyLine
  dfgSectioned (Text t) = text $ "% " ++ t
  dfgSectioned (Section i header) = 
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


dfgId :: Document d => Id -> d
dfgId = text . getId

dfgSort :: Document d => Sort -> d
dfgSort = text . getSort

dfgSortedId :: Document d => SortedId -> d
dfgSortedId (i, s) = dfgSort s <> parens (dfgId i)

dfgTerm :: Document d => Term -> d
dfgTerm (Var (i,_)) = dfgId i
dfgTerm (App (Fun (i,_) _) []) = dfgId i
dfgTerm (App (Fun (i,_) _) ts) = 
  sep (dfgId i <> lparen <> arg : args)
  where
  (arg:args) = map (nest 1) . mapLast (<> rparen) . punctuate comma $ map dfgTerm ts

dfgFormula :: Document d => Formula -> d
dfgFormula Top = text "true"
dfgFormula Bot = text "false"
dfgFormula (In (Rel i _) ts) =     
  text istr <> sep (lparen <> arg : map (nest 1) args)
  where
  (arg:args) = mapLast (<> rparen) . punctuate comma $ map dfgTerm ts
  istr = case getId i of
    []  -> error "dfgFormula: empty identifier encountered"
    "=" -> "equal"
    str -> str
dfgFormula (Neg a) = text "not" <> parens (dfgFormula a)
dfgFormula (BinOp op a b) = 
  sep [text (dfgOp op) <> lparen <> dfgFormula a <> comma, nest 1 $ dfgFormula b <> rparen]
  where
  dfgOp Conj  = "and"
  dfgOp Disj  = "or"
  dfgOp Imp   = "implies"
  dfgOp Equiv = "equiv"
dfgFormula fo0@(Quant q _ _) = 
  sep [ text (dfgQuant q) <> lparen <> brackets sis' <> comma
      , nest 1 $ dfgFormula fo <> rparen]
  where
  (sis, fo) = gatherQuants q fo0
  sis' = hcat . punctuate comma $ map dfgSortedId sis
  dfgQuant All = "forall"
  dfgQuant Ex  = "exists"

-- | MOVE 
gatherQuants :: Quant -> Formula -> ([SortedId], Formula)
gatherQuants q = go []
  where
  go sis fo0@(Quant q' si fo)
    | q' == q   = go (si:sis) fo
    | otherwise = (reverse sis, fo0)
  go sis fo0 = (reverse sis, fo0)


