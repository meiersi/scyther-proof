{-# LANGUAGE DeriveDataTypeable #-}
module Scyther.Formula (
-- * Data Types
    Atom(..)
  , Formula(..)

-- ** Construction
  , substAtom
  , relabelTIDs

-- ** Queries
  , hasQuantifiers
  , conjunctionToAtoms
  , distributeOverDisj
  , isTypingFormula
  , destTypingFormula
  , atomTIDs
  , formulaTIDs
  , findRole

-- * Pretty Printing
  , isaCompr
  , isaUncompr
  , sptAtom
  , isaAtom
  , isaFormula
  , sptFormula
) where

import Data.Maybe
import Data.Data

import Control.Applicative as App
import Control.Monad
import Control.Monad.State
import Control.Monad.Reader

import Text.Isar

import Scyther.Protocol
import Scyther.Message
import Scyther.Equalities as E
import Scyther.Event
import Scyther.Typing

------------------------------------------------------------------------------
-- Data Types
------------------------------------------------------------------------------

-- | A representable logical atom.
data Atom =
    ABool Bool              -- ^ 'False' and 'True' in Isabelle.
  | AEq AnyEq               -- ^ An equality
  | AIneq Inequality        -- ^ An inequality
  | AEv Event               -- ^ An event must have happened.
  | AEvOrd (Event, Event)   -- ^ An event order.
  | ACompr Message          -- ^ A compromised agent variable.
  | AUncompr Message        -- ^ An uncompromised agent variable.
  | AHasType TypeAnn        -- ^ A type annotation on a message.
  | ATyping Typing          -- ^ A claim that the current state of a protocol is
                            --   approximated by the given typing.
  | AReachable Protocol     -- ^ A claim that the current state is reachable.
  deriving( Eq, Show, Ord, Data, Typeable )

-- | A representable logical formula. Currently these are monotonic formula.
data Formula =
    FAtom Atom
  | FConj Formula Formula
  | FDisj Formula Formula
  | FExists (Either TID ArbMsgId) Formula
  deriving( Eq, Show, Ord, Data, Typeable )

-- Queries on the structure of the formula
------------------------------------------

-- | A formula is a single atom claiming well-typedness.
isTypingFormula :: Formula -> Bool
isTypingFormula = isJust . destTypingFormula

-- | Extract the typing from a singleton well-typedness formula.
destTypingFormula :: Formula -> Maybe Typing
destTypingFormula (FAtom (ATyping typ)) = return typ
destTypingFormula _                     = mzero

-- | Relabel quantified TIDs according to the given list of labels.
relabelTIDs :: [TID] -> Formula -> Formula
relabelTIDs tids0 formula =
  runReader (evalStateT (go formula) tids0) (Mapping E.empty)
  where
  go (FAtom atom) = FAtom <$> ((substAtom . getMappingEqs) <$> ask <*> pure atom)
  go (FConj l r)  = FConj <$> go l <*> go r
  go (FDisj l r)  = FDisj <$> go l <*> go r
  go (FExists (Left tid) inner) = do
    tids <- get
    case tids of
      []         -> error "relabelTIDs: out of labels"
      tid':tids' -> do
         put tids'
         FExists (Left tid') <$> local (addTIDMapping tid tid') (go inner)
  go (FExists q@(Right _) inner) = FExists q <$> go inner


-- | Compute the threads associated to the given atom.
atomTIDs :: Atom -> [TID]
atomTIDs (ABool _)      = mzero
atomTIDs (ATyping _)    = mzero
atomTIDs (AReachable _) = mzero
atomTIDs (AEv    e)     = evTIDs e
atomTIDs (AEvOrd ord)   = evOrdTIDs ord
atomTIDs (ACompr m)     = msgTIDs m
atomTIDs (AUncompr m)   = msgTIDs m
atomTIDs (AHasType tya) = typeAnnTIDs tya
atomTIDs (AEq eq)       = anyEqTIDs eq
atomTIDs (AIneq eq)     = inequalityTIDs eq

-- | Compute the free thread variables of the given formula.
formulaTIDs :: Formula -> [TID]
formulaTIDs (FAtom atom)           = atomTIDs atom
formulaTIDs (FConj f1 f2)          = formulaTIDs f1 ++ formulaTIDs f2
formulaTIDs (FDisj f1 f2)          = formulaTIDs f1 ++ formulaTIDs f2
formulaTIDs (FExists (Left tid) f) = filter (tid /=) $ formulaTIDs f
formulaTIDs (FExists (Right _)  f) =                   formulaTIDs f


-- Substitution
---------------

-- | Substitute all variables in an atom.
--
-- NOTE: A 'HasType' atom will only have its thread identifier substituted, but
-- not the whole message variable.
substAtom :: Equalities -> Atom -> Atom
substAtom eqs atom = case atom of
  ABool _      -> atom
  AEq eq       -> AEq      $ substAnyEq      eqs eq
  AIneq eq     -> AIneq    $ substInequality eqs eq
  AEv ev       -> AEv      $ substEv         eqs ev
  AEvOrd ord   -> AEvOrd   $ substEvOrd      eqs ord
  ACompr m     -> ACompr   $ substMsg        eqs m
  AUncompr m   -> AUncompr $ substMsg        eqs m
  AHasType tya -> AHasType $ substTypeAnn    eqs tya
  ATyping _    -> atom
  AReachable _ -> atom


-- Queries
----------

-- | True iff the formula does contain an existential quantifier.
hasQuantifiers :: Formula -> Bool
hasQuantifiers (FAtom _)     = False
hasQuantifiers (FConj f1 f2) = hasQuantifiers f1 || hasQuantifiers f2
hasQuantifiers (FDisj f1 f2) = hasQuantifiers f1 || hasQuantifiers f2
hasQuantifiers (FExists _ _) = True

-- | Convert a formula consisting of conjunctions only to a list of atoms. Uses
-- 'fail' for error reporting.
conjunctionToAtoms :: MonadPlus m => Formula -> m [Atom]
conjunctionToAtoms (FAtom a)     = return [a]
conjunctionToAtoms (FConj f1 f2) =
  (++) `liftM` conjunctionToAtoms f1 `ap` conjunctionToAtoms f2
conjunctionToAtoms _             =
  fail "conjunctionToAtoms: existential quantifier or disjunction encountered."

-- | Produce a logically equivalent formula by pushing conjunctions and
-- quantifiers inside, i.e., apply their respective distributive laws over
-- disjunction. Obvious danger of exponential explosion!
distributeOverDisj :: Formula -> Formula
distributeOverDisj = go
  where
    go (FConj f1 f2) = distribConj (go f1) (go f2)
    go (FDisj f1 f2) = FDisj (go f1) (go f2)
    go (FExists v f) = distribEx v (go f)
    go f             = f

    distribConj f (FDisj f1 f2) = FDisj (distribConj f f1) (distribConj f f2)
    distribConj (FDisj f1 f2) f = FDisj (distribConj f1 f) (distribConj f2 f)
    distribConj f1 f2           = FConj f1 f2

    distribEx v (FDisj f1 f2) = FDisj (distribEx v f1) (distribEx v f2)
    distribEx v f             = FExists v f

-- | Find the first conjoined thread to role equality for this thread, if there
-- is any.
findRole :: TID -> Formula -> Maybe Role
findRole tid = go
  where
    go (FAtom (AEq (TIDRoleEq (tid', role))))
        | tid == tid' = return role
        | otherwise   = mzero
    go (FAtom _)     = mzero
    go (FConj f1 f2) = go f1 `mplus` go f2
    go (FDisj f1 f2) = do
        r1 <- go f1
        r2 <- go f2
        guard (r1 == r2)
        return r1
    go (FExists v f)
        | Left tid == v = mzero
        | otherwise     = go f

-- | Add all thread to role equalities which are (immediate) conjuncts of a
-- formula to a mapping.
addRoles :: Formula -> Mapping -> Mapping
addRoles (FAtom (AEq (TIDRoleEq (tid, role)))) = addTIDRoleMapping tid role
addRoles (FConj f1 f2) = addRoles f1 . addRoles f2
addRoles _             = id


------------------------------------------------------------------------------
-- Pretty Printing
------------------------------------------------------------------------------

-- | A compromised agent variable in Isar format.
isaCompr :: IsarConf -> Message -> Doc
isaCompr conf m = text "RLKR" <> parens (isar conf m) <-> isaIn conf <-> text "reveals t"

-- | An uncompromised agent variable in Isar format.
isaUncompr :: IsarConf -> Message -> Doc
isaUncompr conf m = text "RLKR" <> parens (isar conf m) <-> isaNotIn conf <-> text "reveals t"

-- | A compromised agent variable in security protocol theory format.
sptCompr :: Message -> Doc
sptCompr m = text "compromised" <> parens (sptMessage m)

-- | An uncompromised agent variable in security protocol theory format.
sptUncompr :: Message -> Doc
sptUncompr m = text "uncompromised" <> parens (sptMessage m)

-- | Pretty print an atom in Isar format.
isaAtom :: IsarConf -> Mapping -> Atom -> Doc
isaAtom conf mapping atom = case atom of
    ABool False       -> text "False"
    ABool True        -> text "True"
    AEq eq            -> ppIsar eq
    AIneq eq          -> ppIsar eq
    AEv ev            -> isaEvent    conf mapping ev
    AEvOrd ord        -> isaEventOrd conf mapping ord
    ACompr av         -> isaCompr   conf av
    AUncompr av       -> isaUncompr conf av
    AHasType (m,ty,i) -> ppIsar m <-> isaIn conf <->
                         isar conf ty <-> ppIsar i <->
                         isaExecutionSystemState conf
    ATyping _         -> text "well-typed"
    AReachable p      ->
      text "(t,r,s)" <-> isaIn conf <-> text "reachable" <-> text (protoName p)
  where
    ppIsar :: Isar a => a -> Doc
    ppIsar = isar conf


-- | Pretty print an atom in security protocol theory format.
sptAtom :: Mapping -> Atom -> Doc
sptAtom mapping atom = case atom of
    ABool False    -> text "False"
    ABool True     -> text "True"
    AEq eq         -> sptAnyEq eq
    AIneq eq       -> sptInequality eq
    AEv ev         -> sptEvent    mapping ev
    AEvOrd (e1,e2) -> sptEventOrd mapping [e1,e2]
    ACompr av      -> sptCompr   av
    AUncompr av    -> sptUncompr av
    AHasType tya   -> sptTypeAnn (const Nothing) tya
    ATyping typ    -> sptTyping typ
    AReachable p   -> text "reachable" <-> text (protoName p)


-- | A formula in Isar format.
isaFormula :: IsarConf -> Mapping -> Formula -> Doc
isaFormula conf = pp
  where
    ppIsar :: Isar a => a -> Doc
    ppIsar = isar conf

    pp m (FAtom atom)  = isaAtom conf m atom
    pp m (FConj f1 f2) = sep [ppConjunct m f1 <-> isaAnd conf, ppConjunct m f2]
    pp m (FDisj f1 f2) =
        sep [ppDisjunct (addRoles f1 m) f1 <-> isaOr conf, ppDisjunct (addRoles f2 m) f2]
    pp m (FExists v f) = parens $
        sep [ isaExists conf <-> (either ppIsar ppIsar v) <> char '.'
            , nest 2 $ pp (addRoles f m) f
            ]

    ppConjunct m f@(FDisj _ _) = parens $ pp m f
    ppConjunct m f             = pp m f
    ppDisjunct m f@(FConj _ _) = parens $ pp m f
    ppDisjunct m f             = pp m f


-- | A formula in security protocol theory format.
sptFormula :: Mapping -> Formula -> Doc
sptFormula = pp
  where
    pp m (FAtom atom)  = sptAtom m atom
    pp m (FConj f1 f2) = sep [ppConjunct m f1 <-> char '&', ppConjunct m f2]
    pp m (FDisj f1 f2) =
        sep [ppDisjunct (addRoles f1 m) f1 <-> char '|', ppDisjunct (addRoles f2 m) f2]
    pp m (FExists v f) = parens $
        sep [ char '?' <-> (either sptTID sptArbMsgId v) <> char '.'
            , nest 2 $ pp (addRoles f m) f
            ]

    ppConjunct m f@(FDisj _ _) = parens $ pp m f
    ppConjunct m f             = pp m f
    ppDisjunct m f@(FConj _ _) = parens $ pp m f
    ppDisjunct m f             = pp m f
