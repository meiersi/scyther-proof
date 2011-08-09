{-# LANGUAGE DeriveDataTypeable #-}
module Scyther.Theory (

  -- * Theorems
    Theorem
  , thmProto
  , thmName
  , thmSequent
  , thmProof
  , isAxiom

  -- * Theory items
  , ThyItem(..)

  -- * Theory Datatypes
  , Theory(..)

  -- ** Construction
  , adaptTheoryName
  , insertItem
  , shrinkTheory
  , proveSequents
  , mapTheorySequents
  , addMissingTypingInvariants
  , ensureUniqueRoleNames
  , composeParallel

  -- ** Queries
  , lookupProtocol
  , unsoundTheorems
  , theoryProofSize
  , theoryOverview
  , classifyProperties
  -- , wfTheory       -- TODO: Implement type wellformedness check. 
                      --       Currently, we rely on Isabelle for the last soundness check.

) where

import Safe
import Data.Either (partitionEithers)
import Data.Monoid
import Data.List (isPrefixOf)
import qualified Data.Set as S
import qualified Data.Map as M
import Data.DAG.Simple
import Data.Data
import Data.Generics.Uniplate.Data

import Control.Monad
import Control.Monad.State

import System.FilePath

import Extension.Prelude

import Scyther.Facts
import Scyther.Sequent
import Scyther.Proof

------------------------------------------------------------------------------
-- Theorems
------------------------------------------------------------------------------

-- | A theorem is just a named proof.
type Theorem = Named Proof

-- | The name of a theorem.
thmName :: Theorem -> String
thmName = fst

-- | The proof of a theorem.
thmProof :: Theorem -> Proof
thmProof = snd

-- | The sequent of a theorem.
thmSequent :: Theorem -> Sequent
thmSequent = prfSequent . thmProof

-- | The protocol of a theorem.
thmProto :: Theorem -> Protocol
thmProto = prfProto . thmProof

-- | Check if a theorem is an axiom.
isAxiom :: Theorem -> Bool
isAxiom = isAxiomProof . snd


------------------------------------------------------------------------------
-- Theory Items
------------------------------------------------------------------------------


-- | A theory item is a (meta-)logical fact representable by our security
-- protocol theory.
data ThyItem =
    ThyProtocol Protocol
  | ThySequent (Named Sequent)
  | ThyTheorem (Named Proof)
  | ThyText String String  -- ^ Type of text and content.
  deriving( Eq, Show, Data, Typeable {-! NFData !-} )


------------------------------------------------------------------------------
-- Theories
------------------------------------------------------------------------------

data Theory = Theory {
    thyName  :: String
  , thyItems :: [ThyItem]
  }
  deriving( Eq, Show, Data, Typeable {-! NFData !-} )


-- Construction
---------------

-- | Map the items of a theory.
mapTheoryItems :: ([ThyItem] -> [ThyItem]) -> Theory -> Theory
mapTheoryItems f (Theory name items) = Theory name (f items)

-- | Map the sequents of a theory.
mapTheorySequents :: (Sequent -> Sequent) -> Theory -> Theory
mapTheorySequents f = mapTheoryItems (map mapThyItemSequents)
  where
  mapThyItemSequents item = case item of
    ThySequent (name, se)  -> ThySequent (name, f se)
    ThyTheorem (name, prf) -> ThyTheorem (name, mapProofSequents f prf)
    ThyProtocol _          -> item
    ThyText _ _            -> item

-- | Insert a theory item into a theory.
insertItem :: ThyItem -> Theory -> Theory
insertItem item thy = thy { thyItems = thyItems thy ++ [item] }

-- | Most proofs require a typing invariant to be present for the protocol
-- under investigation. We try to derive one from the protcol specification
-- for every protocol that has none.
addMissingTypingInvariants :: Theory -> Theory
addMissingTypingInvariants thy =
    Theory (thyName thy) (concatMap add $ thyItems thy)
  where
    mkTypingSequent p = case mscTyping p of
        Just typ -> return $ ThySequent ( protoName p ++ "_msc_typing"
                                        , Sequent (empty p) (FAtom (ATyping typ)))
        Nothing  -> mzero

    add item = case item of
        ThyProtocol p 
          | noTypingInvariant p -> [item] ++ mkTypingSequent p
        _                       -> [item]

    noTypingInvariant p = and $ do
        item <- thyItems thy
        se <- case item of
                ThySequent (_, se)  -> return se
                ThyTheorem (_, prf) -> return (prfSequent prf)
                _                   -> mzero
        guard (isTypingFormula $ seConcl se)
        return (p /= seProto se)

-- | Prove all claims with the given heuristic optionally using the given
-- bound.
proveSequents :: (Sequent -> Theorem -> Bool) 
                 -- ^ Predicate determining theorems for reuse for proving the
                 -- given sequent.
              -> ([Named Sequent] -> Sequent -> Maybe Proof) 
                 -- ^ Proof construction function.
              -> Theory -> Theory
proveSequents reuse prover thy =
  Theory (thyName thy) (flip execState [] . mapM_ prove $ thyItems thy)
  where
  prove (item@(ThySequent (name, se))) = do
    prevItems <- get
    let reusableThms = [ (thmName th, thmSequent th) 
                       | ThyTheorem th <- prevItems, reuse se th, thmProto th == seProto se]

    case prover reusableThms se of
      Just prf -> modify (++[ThyTheorem (name, prf)])
      Nothing  -> modify (++[item])

  prove item = modify (++[item])

-- | Only keep theorems for which the given predicate is true or which are
-- referenced by some kept theorem.
shrinkTheory :: (String -> Bool) -> Theory -> Theory
shrinkTheory mustKeep (Theory name items) =
  Theory name (filter keep items)
  where
  thmInfo thm = (thmName thm, thmProto thm)
  kept = [ thmInfo thm | ThyTheorem thm <- items, mustKeep $ thmName thm ]
  dependencies =
    [ (thmInfo thm, dep) 
    | ThyTheorem thm <- items, dep <- S.toList . depends $ thmProof thm ]
  toKeep = reachableSet kept dependencies
  keep :: ThyItem -> Bool
  keep (ThyTheorem thm) = (thmInfo thm `S.member` toKeep)
  keep (ThySequent se)  = mustKeep $ fst se
  keep _                = True

-- | Adapt the theory name to the base name of the given file.
adaptTheoryName :: FilePath -> Theory -> Theory
adaptTheoryName file thy = thy { thyName = takeBaseName file }

-- | Ensures that all roles are globally uniquely named by prefixing all role
-- names with their corresponding protocol name, if two roles have equal names.
ensureUniqueRoleNames :: Theory -> Theory
ensureUniqueRoleNames thy
  | unique rs = thy
  | otherwise = mapTheoryItems (map addPrefix) thy
  where
    rs = [roleName r | ThyProtocol p <- thyItems thy, r <- protoRoles p]

    prefixRoleName p r = r {roleName = protoName p ++ "_" ++ roleName r}

    getProtocol (ThyProtocol p) = return p
    getProtocol (ThySequent s)  = return (seProto $ snd s)
    getProtocol (ThyTheorem p)  = return (thmProto p)
    getProtocol (ThyText _ _)   = mzero

    addPrefix item = case getProtocol item of
        Just p  -> transformBi (prefixRoleName p) item
        Nothing -> item

-- | Compose all protocol in the theory in parallel. Assumes that both protocol
-- names as well as role names are /globally/ unique.
composeParallel :: Theory -> Theory
composeParallel thy 
    | length ps <= 1 = thy
    | otherwise      = thy { thyItems = [ThyProtocol pc, ThySequent sec] ++ items3 }
  where
    (ps,  items1) = partitionEithers $ do
        item <- thyItems thy
        case item of 
            ThyProtocol p -> return $ Left p
            _             -> return $ Right item

    (typs, items2) = partitionEithers $ do
        item <- items1 
        case item of
            ThySequent (_, Sequent _ (FAtom (ATyping typ)))
              -> return $ Left typ
            ThySequent x -> return $ Right $ ThySequent $ prefixProtoName (seProto $ snd x) x
            ThyTheorem x -> return $ Right $ ThyTheorem $ prefixProtoName (thmProto x) x
            _            -> return $ Right item


    prefixProtoName :: Protocol -> (String, a) -> (String, a)
    prefixProtoName p x@(n, v)
      | protoName p `isPrefixOf` n = x
      | otherwise                  = (protoName p ++ "_" ++ n, v)
     
    namec = thyName thy
    pc    = Protocol namec (concatMap protoRoles ps)
    sec   = ( namec ++ "_composed_typing"
            , Sequent (empty pc) (FAtom (ATyping (M.unions typs)))
            )

    replaceProtocol :: Protocol -> Protocol
    replaceProtocol = const pc

    items3 = transformBi replaceProtocol items2


-- Queries
----------

-- | Find a protocol in the theory according to its name.
lookupProtocol :: String -> Theory -> Maybe Protocol
lookupProtocol name thy = 
  headMay [proto | ThyProtocol proto <- thyItems thy, protoName proto == name]

-- | Find all unsound theorems of the theory.
unsoundTheorems :: Theory -> [(Protocol, String)]
unsoundTheorems (Theory _ items) = 
  [ (prfProto prf, name) 
  | ThyTheorem (name, prf) <- items, not (sound prf) 
  ] ++
  [ (seProto se, name) 
  | ThySequent (name, se) <- items
  ]

-- | Total proof size.
theoryProofSize :: Theory -> ProofSize
theoryProofSize (Theory _ items) = mconcat $
  [ proofSize (thmProof th) | ThyTheorem th <- items ] ++
  [ missingProofSize        | ThySequent _  <- items ]

-- | Count and classify the properties selected by the given predicate into
-- secrecy properties, authentication properties, and other properties.
classifyProperties :: (String -> Bool) -> Theory -> (Int, Int, Int)
classifyProperties toClassify = foldl classify (0,0,0) . thyItems
  where
  getSequent (ThyTheorem thm) = do
    guard (toClassify $ thmName thm) 
    return $ thmSequent thm
  getSequent (ThySequent se)  = do
    guard (toClassify (fst se))
    return (snd se)
  getSequent _                = mzero

  classify counts@(nSec, nAuth, nOther) item = case getSequent item of
    Just se | isContradictionProp se   -> (succ nSec,      nAuth,      nOther)
    Just se | isExistsStructureProp se -> (     nSec, succ nAuth,      nOther)
    Just _                             -> (     nSec,      nAuth, succ nOther)
    Nothing                            -> counts

  -- | True, if the sequent implies 'FFalse'.
  isContradictionProp :: Sequent -> Bool
  isContradictionProp = (FAtom AFalse ==) . seConcl

  -- | True, if the sequents conclusion contains an existentially quantified
  -- thread.
  isExistsStructureProp :: Sequent -> Bool
  isExistsStructureProp = hasQuantifiers . seConcl

-------------------------------------------------------------------------------
-- Overview generation
-------------------------------------------------------------------------------

theoryOverview :: Theory -> Theory
theoryOverview = error "theoryOverview: upgrade to new infrastructure"

{-
lookupTypeInvariants :: Protocol -> Theory -> [(ThyItem, Maybe Typing)]
lookupTypeInvariants proto thy = do
  item <- thyItems thy
  se <- case item of
    ThySequent _ se -> return se
    ThyTheorem th   -> return $ thmSequent th
    _               -> mzero
  guard (seProto se == proto)
  case seConcl se of
    FTyping typ -> return (item, typ)
    _           -> mzero

-- | The overview of a theory lists for each protocol its associated typings
-- together with the corresponding chain rule. If no typing is given, then it
-- tries to infer it from the message sequence chart.
theoryOverview :: Theory -> Theory
theoryOverview thy@(Theory name items) = 
  Theory name $ concat [ protoOverview proto | ThyProtocol proto <- items]
  where
  protoOverview proto = 
    (ThyText "section" $ "Overview of protocol '"++protoName proto++"'") : 
    ThyProtocol proto : typInvs
    where
    typInvs = case lookupTypeInvariants proto thy of
      [] -> case mscTyping proto of
        Just typing -> addChainRule
          ( ThySequent "auto_msc_typing" $
               Sequent proto (FFacts emptyFacts) (FTyping (Just typing))
          , Just typing )
        Nothing   -> return $
          ThyText "text" "failed to infer typing from protocol specification\n\
                  \(maybe some message patterns are not unifiable)"
      xs -> concatMap addChainRule xs

    addChainRule (item, typ) = 
      [ item
      , ThyText "text" $ unlines
          [ "Note that the chain rule below is only an informal representation of the"
          , "actual chain rule, which you can find in the Isabelle theories. In particular,"
          , "it is missing the cases for the initial intruder knowledge and uses a dummy"
          , "conclusion 'False'." ]
      , ThyTheorem $ Theorem ("chain_rule_OF_" ++ name) (displayChainRule proto typ)
      ]
      where
      name = case item of
        ThySequent n _ -> n
        ThyTheorem th  -> thmName th
        _              -> error $ "theoryOverview: expected sequent or theorem item"


-}
