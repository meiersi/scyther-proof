{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveDataTypeable #-}
-- | A representation for proofs constructed using our security protocol
-- verification theory.
module Scyther.Proof (
  -- * Datatypes
    Proof(..)
  , TrivReason(..)
  , Rule(..)

  -- ** Proof construction
  , dfsProof
  , shortestProof
  , minimizeProof
  , mapProofSequents

  -- ** Queries
  , prfSequent
  , prfProto
  , isAxiomProof
  , isTrivialProof
  , complete
  , sound
  , depends
  , extractTypeInvariant

  -- *** Proof sizes
  , ProofSize
  , getProofSize
  , missingProofSize
  , proofSize

  -- * Special "Proofs"
  , existsPossibleAttack
  , displayChainRule

) where

import Data.Function
import Data.Maybe
import Data.List
import Data.Monoid
import qualified Data.Set as S
import Data.Data

import Control.Applicative
import Control.Monad
import Control.Monad.State
import Control.Monad.BoundedDFS

import Extension.Prelude

import Scyther.Facts
import qualified Scyther.Equalities as E
import Scyther.Sequent

------------------------------------------------------------------------------
-- Data Types
------------------------------------------------------------------------------

-- | A proof of a sequent.
data Proof =
    Axiom   Sequent                 -- ^ Assumed as an axiom.
  | PossibleAttack Sequent Sequent  -- ^ A possible attack on the given sequent.
  | Missing Sequent String Bool     -- ^ A missing proof and the reason why it is
                                    --   missing plus a flag for displaying the sequent.
  | Trivial Sequent TrivReason      -- ^ A trivial proof for the sequent and the
                                    --   reason why it is trivial.
  | RuleApp Sequent Rule [Proof]    -- ^ An application of a rule/theorem and the
                                    --   proofs for all the resulting sequents.
  deriving( Eq, Show, Data, Typeable {-! NFData !-} )

-- | Triviality reasons.
data TrivReason =
    TrivContradictoryPremises
  | TrivPremisesImplyConclusion
  | TrivLongTermKeySecrecy Message
  deriving( Eq, Show, Data, Typeable {-! NFData !-} )

-- | Supported rules.
data Rule =
    Saturate
  | ForwardResolution (Named Sequent) E.Mapping
  | ChainRule Message [(String, [Either TID ArbMsgId])]
  | SplitEq  E.MsgEq [Bool]  -- True, if sub-proof for this case is present.
  | TypingCases [String]
  deriving( Eq, Show, Data, Typeable {-! NFData !-} )

------------------------------------------------------------------------------
-- Simple Queries
------------------------------------------------------------------------------

-- | True iff the proof is trivial.
isTrivialProof :: Proof -> Bool
isTrivialProof (Trivial _ _) = True
isTrivialProof _             = False

-- | True iff the proof is an axiom definition.
--
-- NOTE: This checks only if the proof is directly by axiom.
isAxiomProof :: Proof -> Bool
isAxiomProof (Axiom _) = True
isAxiomProof _         = False

-- | Extract the proven sequent from a proof.
prfSequent :: Proof -> Sequent
prfSequent (Axiom   se)          = se
prfSequent (PossibleAttack se _) = se
prfSequent (Missing se _ _)      = se
prfSequent (Trivial se _)        = se
prfSequent (RuleApp se _ _)      = se

-- | Extract the protocol concerned by a proof.
prfProto :: Proof -> Protocol
prfProto = seProto . prfSequent


------------------------------------------------------------------------------
-- Proof Construction
------------------------------------------------------------------------------

-- | Try proving a sequent by assumption; i.e. by showing that the premises
-- directly imply the conclusion.
byAssumption :: Monad m => Sequent -> m Proof
byAssumption se@(Sequent prem concl Standard)
  | proveFalse prem         = return $ Trivial se TrivContradictoryPremises
  | proveFormula prem concl = return $ Trivial se TrivPremisesImplyConclusion
  | otherwise = case exploitLongTermKeySecrecy prem of
      Just key -> return $ Trivial se (TrivLongTermKeySecrecy key)
      Nothing  -> fail $ "byAssumption: cannot prove conclusion from premises"
byAssumption _ = fail $ "byAssumption: only work for standard sequents"


-- | An order preferring typing conclusions and then false conclusions.
reuseOrder :: Formula -> Formula -> Ordering
reuseOrder (FAtom (ATyping typ1)) (FAtom (ATyping typ2)) = compare typ1 typ2
reuseOrder (FAtom (ATyping _))    _                      = LT
reuseOrder _                      (FAtom (ATyping _))    = GT
reuseOrder (FAtom AFalse)         (FAtom AFalse)         = EQ
reuseOrder (FAtom AFalse)         _                      = LT
reuseOrder _                      (FAtom AFalse)         = GT
reuseOrder f1                     f2                     = compare f1 f2


-- | A generic proof strategy for proving sequents. Eagerly reuses lemmas in
-- the order they were given using forward resolution.
genericProof :: MonadPlus m
             => m ()                  -- ^ A marker for usages of the chain rule.
             -> (Facts -> [Message])  -- ^ A heuristic for the order of
                                      --   messages to be tried using the chain rule.
             -> [Named Sequent]       -- ^ Rules that should be reused in this proof.
             -> Sequent               -- ^ The sequent to be proven
             -> m Proof
genericProof chainRuleMarker goals rawRules se0 =
  case saturate se0 of
    Just se1 -> (RuleApp se0 Saturate . return) `liftM` prove se1
    Nothing  ->                                         prove se0
  where
  -- the theorems for reuse: prefer false conclusions over arbitrary conclusions
  reusableRules :: [Named Sequent]
  reusableRules = sortBy (reuseOrder `on` (seConcl . snd)) rawRules

  -- build a proof step corresponding to the reuse of a rule.
  reuseRule se rule = do
    (mapping, optSequent) <- frule (snd rule) se
    let mkProof = RuleApp se (ForwardResolution rule mapping)
    case optSequent of
      Nothing      -> return $ return $ mkProof []
      Just sequent -> return $ (mkProof . return) `liftM` prove sequent

  -- use the chain rule
  useChainRule se m = do
    chainRuleMarker
    case chainRule se m of
      Just cases -> do
        let (info, sequents) = unzip cases
        (RuleApp se (ChainRule m info)) `liftM` mapM prove sequents
      Nothing    -> return $ Missing se "prover stuck => no type invariant available" True

  -- prove a sequent
  prove se =
    case byAssumption se of
      Just prf -> return prf  -- proven by assumption
      Nothing  ->
        case wellTypedCases se of
          Just cases -> do    -- try to prove well-typedness cases
            let (names, sequents) = unzip cases
            RuleApp se (TypingCases names) `liftM` mapM prove sequents
          Nothing ->
            case msum (map (reuseRule se) reusableRules) of
              Just mkPrf -> mkPrf -- could reuse a proven sequent
              Nothing    ->       -- try to use the chain rule
                case splittableEqs (sePrem se) of
                  -- split the first available equality
                  eq:_ -> do
                    let sequents = splitEq eq se
                    RuleApp se (SplitEq eq (map isJust sequents)) `liftM`
                      mapM prove (catMaybes sequents)

                  -- there is none => chain rule is our last resort
                  [] ->
                    case goals (sePrem se) of
                      [] -> return $ PossibleAttack se se
                      ms -> msum $ map (useChainRule se) ms



-- | Use a (possibly bounded) depth-first search for finding the proof.
-- TODO: Make error handling explicit.
dfsProof :: Maybe Int -> (Facts -> [Message]) -> [Named Sequent] -> Sequent -> Maybe Proof
dfsProof Nothing heuristic rules se =
  runUnboundedDFS $ genericProof (return ()) heuristic rules se
dfsProof (Just bound) heuristic rules se =
  evalBoundedDFS (genericProof (updateCost succ) heuristic rules se) (<= bound) 0

-- | Use branch-and-bound search to find the shortest proof.
-- TODO: Make error handling explicit.
shortestProof :: Maybe Int -> (Facts -> [Message]) -> [Named Sequent] -> Sequent -> Maybe Proof
shortestProof optBound heuristic rules se =
  evalBranchAndBound
    (genericProof (updateCost (fmap succ)) heuristic rules se)
    optBound

-- | Check if there exists a case where the prover gets stuck using unbounded DFS
-- and the given heuristic and theorems to reuse.
existsPossibleAttack :: (Facts -> [Message]) -> [Named Sequent] -> Sequent -> Maybe Proof
existsPossibleAttack heuristic rules se =
  findAttack =<< (runUnboundedDFS $ genericProof (return ()) heuristic rules se)

------------------------------------------------------------------------------
-- Proof Checking and Minimization
------------------------------------------------------------------------------

-- | A proof is locally sound iff each rule application is sound.
checkProof :: Sequent -> Proof -> Maybe Proof
checkProof se0 prf0 = evalStateT (go prf0) se0
  where
  mkSubproof se prf = put se >> go prf

  go :: Proof -> StateT Sequent Maybe Proof
  go (Missing _ reason showSequent) =
    Missing <$> get <*> pure reason <*> pure showSequent
  go prf@(Axiom seAxiom) = do
    se <- get
    guard (se == seAxiom)
    return prf
  go prf@(PossibleAttack seAttacked _) = do
    se <- get
    guard (se == seAttacked)
    return prf
  go (Trivial _ reason@TrivContradictoryPremises) = do
    prem <- gets sePrem
    guard (proveFalse prem)
    Trivial <$> get <*> pure reason
  go (Trivial _ reason@TrivPremisesImplyConclusion) = do
    se <- get
    guard (proveFormula (sePrem se) (seConcl se))
    Trivial <$> get <*> pure reason
  go (Trivial _ reason@(TrivLongTermKeySecrecy key)) = do
    se <- get
    case exploitLongTermKeySecrecy (sePrem se) of
      Just key' -> do guard (key == key')
                      Trivial <$> get <*> pure reason
      Nothing   -> mzero
  go (RuleApp _ Saturate [prf]) = do
    se <- get
    case saturate se of
      Just se' -> (RuleApp se Saturate . return) <$> (put se' >> go prf)
      Nothing  -> go prf
  go (RuleApp _ rule@(ForwardResolution thm mapping) prfs) = do
    se <- get
    let statePrem = sePrem se
    guard (proveFacts statePrem (sePrem $ snd thm) mapping)
    optSequent <- fruleInst (snd thm) mapping se
    case optSequent of
      Nothing -> do guard (null prfs)
                    return $ RuleApp se rule prfs
      Just sequent -> case prfs of
        [prf] -> (RuleApp se rule . return) `liftM` mkSubproof sequent prf
        _     -> mzero
  go (RuleApp _ rule@(ChainRule m info) prfs) = do
    se <- get
    -- FIXME: Here we could get a problem if the atom can no longer be
    -- certified.  This will probably not occur in our current setting, as
    -- proof minimization does not change the quantifiers because only
    -- non-existentially quantified conclusions are reused.
    guard (proveAtom (sePrem se) (AEv (Learn m)))
    (info', sequents') <- unzip `liftM` chainRule se m
    guard (info == info')
    RuleApp <$> get <*> pure rule <*> zipWithM mkSubproof sequents' prfs

  go (RuleApp _ rule@(SplitEq eq info) prfs) = do
    se <- get
    guard (eq `elem` splittableEqs (sePrem se))
    let optSequents' = splitEq eq se
        info'        = map isJust optSequents'
        sequents'    = catMaybes optSequents'
    guard (info == info')
    RuleApp <$> get <*> pure rule <*> zipWithM mkSubproof sequents' prfs

  go (RuleApp _ rule@(TypingCases info) prfs) = do
    se <- get
    (info', sequents') <- unzip `liftM` wellTypedCases se
    guard (info == info')
    RuleApp <$> get <*> pure rule <*> zipWithM mkSubproof sequents' prfs
  go _ = mzero

-- | Find the first 'PossibleAttack' proof state and replace all other proof
-- steps on the way to this state by missing steps.
findAttack :: Proof -> Maybe Proof
findAttack = fmap head . go . return
  where
    unvisited prf = Missing (prfSequent prf) "not yet investigated" False

    go :: [Proof] -> Maybe [Proof]
    go []           = Nothing
    go (prf : prfs) = case prf of
        RuleApp se rule subprfs ->
            -- look for an attack in the subproofs of the given rule
            (do subprfs' <- go subprfs
                return $ RuleApp se rule subprfs' : map unvisited prfs
            ) `mplus`
            -- look for an attack in the remaining proofs
            ((unvisited prf :) `liftM` go prfs)
        -- attack found: return it together with the unvisited siblings
        PossibleAttack _ _  -> return $ prf : map unvisited prfs
        -- look for an attack in the siblings and prepend ourselves unvisited
        _                   -> (unvisited prf :) `liftM` go prfs

-- | A proof is complete iff no 'Missing' proof or 'PossibleAttack' is part of it.
complete :: Proof -> Bool
complete (Missing _ _ _)      = False
complete (PossibleAttack _ _) = False
complete (RuleApp _ _ prfs)   = all complete prfs
complete _                    = True

-- | A proof is sound iff it is complete and each inference step is sound.
sound :: Proof -> Bool
sound prf = complete prf && isJust (checkProof (prfSequent prf) prf)

-- | Minimize a proof by removing all unnecesary forward resolutions.
minimizeProof :: Proof -> Proof
minimizeProof prf0 = fromMaybe prf0 $ do
  prf <- go prf0
  checkProof (prfSequent prf) prf
  where
  go (RuleApp se rule@(ForwardResolution _ _) [prf]) = do
    prf' <- go prf
    (checkProof se prf' <|> pure (RuleApp se rule [prf']))
  go (RuleApp se rule prfs) =
    RuleApp se rule <$> mapM go prfs
  go prf = return prf

-- | Output the set of theorems a proof depends on.
depends :: Proof -> S.Set (String, Protocol)
depends (RuleApp _ (ForwardResolution (name, se) _) prfs) =
  S.insert (name, seProto se) $ S.unions $ map depends prfs
depends (RuleApp _ _ prfs) = S.unions $ map depends prfs
depends _ = S.empty

-- | Extracts the first type invariant occurring in a forward resolution. This
-- is required because in Isabelle type invariants are handled using locales,
-- while we are handling them using forward resolution.
--
-- Note that our system here is more general, but for the current setup, we do
-- not see this generality.
extractTypeInvariant :: Proof -> Maybe (Named Typing)
extractTypeInvariant (RuleApp _ (ForwardResolution (name, se) _) prfs) =
  case destTypingFormula (seConcl se) of
    Just typ -> return (name, typ)
    Nothing  -> msum $ map extractTypeInvariant prfs
extractTypeInvariant (RuleApp _ _ prfs) = msum $ map extractTypeInvariant prfs
extractTypeInvariant _ = mzero

------------------------------------------------------------------------------
-- Proof Sizes
------------------------------------------------------------------------------

-- | Proof size datatype counting number of chain rule applications and the
-- number of forward resolutions. The 'Monoid' instance corresponds to adding
-- proof sizes.
newtype ProofSize = ProofSize (Sum Int, Sum Int, Sum Int)
  deriving( Eq, Ord, Monoid )

instance Show ProofSize where
  show s =
    concat ["C:", show nChain, " F:", show nForward, " M:", show nMissing]
    where
    (nChain, nForward, nMissing) = getProofSize s

-- | Extract the raw proof size information.
getProofSize :: ProofSize -> (Int, Int, Int)
getProofSize (ProofSize (nChain, nForward, nMissing)) =
  (getSum nChain, getSum nForward, getSum nMissing)

-- | The size of a missing proof.
missingProofSize :: ProofSize
missingProofSize = ProofSize (mempty, mempty, Sum 1)

-- | Compute the size of a proof.
proofSize :: Proof -> ProofSize
proofSize (Axiom _)             = mempty
proofSize (PossibleAttack _ _)  = mempty
proofSize (Trivial _ _)         = mempty
proofSize (Missing _ _ _)       = missingProofSize
proofSize (RuleApp _ rule prfs) = mconcat $
  (case rule of
     ChainRule _ _         -> pure $ ProofSize (Sum 1, mempty, mempty)
     ForwardResolution _ _ -> pure $ ProofSize (mempty, Sum 1, mempty)
     _                     -> mempty
  ) ++ map proofSize prfs

-- | Map the sequents of the proof.
mapProofSequents :: (Sequent -> Sequent) -> Proof -> Proof
mapProofSequents f  = go
  where
  go (Axiom se)               = Axiom (f se)
  go (PossibleAttack se se')  = PossibleAttack (f se) (f se')
  go (Trivial se reason)      = Trivial (f se) reason
  go (Missing se reason hide) = Missing (f se) reason hide
  go (RuleApp se rule prfs)   = RuleApp (f se) rule (map go prfs)


-- Chain Rule Display
------------------------------------------------------------------------------

displayChainRule :: Protocol -> Maybe Typing -> Proof
displayChainRule _ _ = error "displayChainRule: not yet upgraded"
{-
displayChainRule proto optTyp =
  RuleApp se (ChainRule optTyp m (map fst cases)) (map mkPrf cases)
  where
  tid   = 0
  m     = (MMVar (LocalId (Id "m", tid)))
  prem  = insertEv (Learn m) $ insertThread tid $ emptyFacts
  se    = Sequent proto (FFacts prem) FFalse
  cases = chainRule proto optTyp m prem
  mkPrf c = Missing (Sequent proto (FFacts (snd c)) FFalse) "chain rule case:"

-}
