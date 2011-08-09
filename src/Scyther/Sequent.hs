{-# LANGUAGE DeriveDataTypeable #-}
module Scyther.Sequent (

  -- * Datatype
    Sequent(..)
  , seProto

  -- ** Logically safe construction
  , wellTypedCases
  , saturate
  , frule
  , fruleInst
  , chainRule
  , splitEq
  , exploitTyping
  , uniqueTIDQuantifiers
) where

import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Data

import Control.Arrow
import Control.Monad

import qualified Scyther.Equalities as E
import Scyther.Facts
import Scyther.Formula


------------------------------------------------------------------------------
-- Sequents
------------------------------------------------------------------------------

-- | A sequent with a conjunction of a set of facts as the premise and a single
-- formula as the conclusion denoting a statement about a reachable state of
-- a protocol.
data Sequent = Sequent {
    sePrem  :: Facts
  , seConcl :: Formula
  }
  deriving( Eq, Show, Ord, Data, Typeable )

-- | The protocol of a sequent.
seProto :: Sequent -> Protocol
seProto = protocol . sePrem


-- Construction
---------------

-- | Make all thread identifiers occurring in the sequent unique by
-- consistently relabeling the thread identifiers in the conclusion.
uniqueTIDQuantifiers :: Sequent -> Sequent
uniqueTIDQuantifiers (Sequent prem concl) = 
  Sequent prem (relabelTIDs [nextTID prem..] concl)

-- | Apply a function to the premise, but return only the updated sequent if
-- the premise was changed.
changePrem :: MonadPlus m => (Facts -> m Facts) -> Sequent -> m Sequent
changePrem f se = do
  let prem0 = sePrem se
  prem1 <- f prem0
  guard (prem0 /= prem1)
  return $ se { sePrem = prem1 }


-- | The named list of sequents which need to be proven in order to prove that
-- the given protocol is well typed
--
-- PRE: The conclusion of the sequent must be typing atom.
--
-- Uses 'fail' for error reporting.
wellTypedCases :: MonadPlus m => Sequent -> m [(String, Sequent)]
wellTypedCases se = case seConcl se of
  FAtom (ATyping typ) -> 
      return $ protoRoles (seProto se) >>= roleProofs typ
  _ -> mzero
  where
  roleProofs typ role = proveRecvs S.empty (roleSteps role)
    where
    proveRecvs _ [] = []
    proveRecvs recv (      Send _ _       : steps) = proveRecvs recv steps
    proveRecvs recv ((Recv _ (PMVar lid)) : steps) = 
      -- don't prove single reiceves as they are handled directly by the tactic
      -- on the Isabelle side.
      proveRecvs (S.insert lid recv) steps
    proveRecvs recv (step@(Recv _ pt)     : steps) = 
      let mvars = patFMV pt
      in (S.toList mvars >>= proveVar) `mplus` 
         (proveRecvs (recv `S.union` mvars) steps)
      where
      proveVar v
        | v `S.member` recv = fail "proveVar: not first receive"
        | otherwise = do
            return (name, Sequent prem concl)
        where
        name = roleName role ++ "_" ++ stepLabel step ++ "_" ++ getId v
        (tid, prem0) = freshTID (sePrem se)
        mv = MVar (LocalId (v, tid))
        premErr = error $ "wellTypedCases: could not add thread " ++ show tid ++ ". This should not happen."
        prem1 = maybe premErr saturateFacts . join $ 
          conjoinAtoms [AEv (Step tid step), AEq (E.TIDRoleEq (tid, role))] prem0
        prem = fromMaybe (error "failed to set typing") $ setTyping typ prem1
        concl = FAtom $ 
            case M.lookup (v, role) typ of
              Just ty -> AHasType (MMVar mv, ty, tid)
              Nothing -> error $ 
                "wellTypedCases: no type given for '"++show v++"' in role '"++roleName role++"'"


-- | Emulate a variant Isabelle's 'frule' tactic. It works only if the given
-- maping of free variables of the rule makes the premise of the rule provable
-- under the given proof state. Then, the conclusion of the rule with free
-- variables mapped accordingly is added to premises of the proof state. The
-- last step works currently only for conclusions being false of pure
-- conclusions.
--
-- NOTE that 'frule' works only for rules that contain no existential
-- quantifiers in the conclusion.
fruleInst :: MonadPlus m
      => Sequent -- ^ rule 
      -> E.Mapping -- ^ mapping of free variables of rule to proof state
      -> Sequent -- ^ proof state
      -> m (Maybe Sequent) -- ^ some result if resolution worked. Nothing
                           -- denotes that False was derived. Just means that
                           -- premises of proof state were extended.
                           --
                           -- mzero if rule could not be applied
fruleInst rule mapping state = do
  atoms <- conjunctionToAtoms $ seConcl rule
  let statePrem = sePrem state
  guard (proveFacts statePrem (sePrem rule) mapping)
  optStatePrem' <- conjoinAtoms (map (substAtom (E.getMappingEqs mapping)) atoms) statePrem
  case optStatePrem' of
    Nothing         -> do return Nothing
    Just statePrem' -> do guard (statePrem /= statePrem')
                          return . Just $ Sequent statePrem' (seConcl state)

-- | Like 'fruleInst' but tries all mappings.
frule :: MonadPlus m
      => Sequent -- ^ rule 
      -> Sequent -- ^ proof state
      -> m (E.Mapping, Maybe Sequent) 
         -- ^ some result if resolution worked. Nothing denotes that False was
         -- derived. Just means that premises of proof state were extended.
         --
         -- mzero if rule could not be applied
frule rule state = case resolutions of
  []      -> mzero
  res : _ -> return res
  where
  resolutions = do
    mapping <- freeVariableMappings (sePrem rule) (sePrem state)
    ((,) mapping) `liftM` fruleInst rule mapping state


{-
-- | Emulate Isabelle's 'frule' tactic; i.e. the first sequent is the rule that
-- is used for resolution.
--
-- NOTE that 'frule' works only for rules that contain no existential
-- quantifiers in the conclusion.
frule :: Sequent   -- ^ Rule to use for resolution.
      -> Sequent   -- ^ Proof state that this rule is resolved against.
      -> [(Mapping, Maybe Sequent)]
                   -- ^ The mapping and no resulting proof state
                   -- if the resolution solved this subgoal;
                   -- otherwise the new subgoal provided it is
                   -- differnt from the old one.
frule rule state = do
  atoms <- conjunctionToAtoms $ seConcl rule
  let prem0 = sePrem state
  mapping <- resolve (sePrem rule) prem0
  optPrem1 <- conjoinAtoms (map (substAtom (getMappingEqs mapping)) atoms) prem0
  case optPrem1 of
    Nothing    -> do return (mapping, Nothing)
    Just prem1 -> do guard (prem1 /= prem0)
                     return (mapping, Just $ Sequent prem1 (seConcl state))
-}

-- | Try to saturate a sequent, if possible and leading to new facts.
saturate :: MonadPlus m => Sequent -> m Sequent
saturate = changePrem (return . saturateFacts)

-- | Try to use the chain rule. 
--
-- MonadPlus is used to report a failure to apply the rule.
--
chainRule :: MonadPlus m 
          => Sequent -> Message 
          -> m [((String, [Either TID ArbMsgId]), Sequent)]
chainRule se m = 
    map (second mkSequent) `liftM` chainRuleFacts m (sePrem se)
  where 
    mkSequent prem = Sequent prem (seConcl se)

-- | Try to exploit the typing. Fails if no new facts could be derived.
exploitTyping :: MonadPlus m => Sequent -> m Sequent
exploitTyping = changePrem exploitTypingFacts

-- | Split a splittable equality.
-- splitting can be done.
splitEq :: E.MsgEq -> Sequent -> [Maybe Sequent]
splitEq eq se 
  | eq `elem` splittableEqs prems = map (fmap updPrem) $ splitEqFacts eq prems
  | otherwise                     = error $ "splitEq: equality not present"
  where
    prems = sePrem se
    updPrem prem' = se {sePrem = prem'}

  




