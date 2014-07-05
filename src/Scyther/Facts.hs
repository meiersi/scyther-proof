{-# LANGUAGE CPP, FlexibleContexts, DeriveDataTypeable #-}
-- | Conjunctions of the logical facts needed during a proof using decryption chain reasoning.
module Scyther.Facts (

    module Scyther.Protocol
  , module Scyther.Typing
  , module Scyther.Message
  , module Scyther.Event
  , module Scyther.Formula

-- * Facts
  , Facts
  , protocol

  -- ** Construction
  , empty
  , freshTID
  , freshArbMsgId
  , quantifyTID
  , quantifyArbMsgId
  , conjoinAtoms
  , setTyping

  -- ** Queries
  , nullFacts
  , freeVariableMappings
  , proveFacts
  , proveFalse
  , proveAtom
  , proveFormula
  , toAtoms
  , toFormula
  , nextTID
  , nextArbMsgId
  , quantifiedTIDs

  -- ** Substitution under the equalities of the facts
  , substEv
  , threadRole
  , eqsToMapping
  , applyMapping

  -- ** Rule applications
  , oldestOpenMessages
  , chainRuleFacts
  , saturateFacts
  , exploitTypingFacts
  , exploitLongTermKeySecrecy

  , splittableEqs
  , splitEqFacts

-- * Output
  , isaFacts
  , sptFacts

) where

import Debug.Trace
import Extension.Prelude

import Safe
import Data.List
import Data.Maybe

-- workaround new Monoid operator <>
#if __GLASGOW_HASKELL__ < 704
import Data.Monoid
#else
import Data.Monoid hiding ((<>))
#endif

import Data.Foldable (foldMap)
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Data

import Control.Arrow ( second, (***) )
import Control.Applicative hiding (empty)
import Control.Monad
import Control.Monad.State

import Text.Isar

import Scyther.Protocol
import Scyther.Message
import qualified Scyther.Typing     as T
import           Scyther.Typing          hiding (substTypeAnn)
import qualified Scyther.Equalities as E
import           Scyther.Equalities      hiding (solve, substTID, threadRole, substMVar, substAVar, substMsg, substAnyEq, substInequality, substAMID, empty, null)
import           Scyther.Event           hiding (substEv, substEvOrd)
import qualified Scyther.Event      as E
import           Scyther.Formula         hiding (substAtom)
import qualified Scyther.Formula    as F


-- | A convenient abbreviation for `mappend`.
(><) :: Monoid m => m -> m -> m
(><) = mappend


------------------------------------------------------------------------------
-- Facts
------------------------------------------------------------------------------

-- | A conjunction of logical facts.
--
-- Invariants that hold for a value @facts = Facts _ evs evord co uc eqs@:
--
--   1. All facts are invariant under their corresponding substitution. This
--      excludes the quantifiers, as they are no facts.
--
--   2. All trivial learn events are removed (or split in case of a pair).
--
--   3. All arbitrary messages are annotated with a type.
--
-- We assume that all thread identifiers that are assigned to a role are
-- locally quantified. The kind of quantification depends on the context. If
-- the set of facts models the premises of a proof state then this would be
-- universal quantification. If the set of facts models an authentication
-- conclusion this would be existential quantification.
--
data Facts = Facts {
    events         :: S.Set Event    -- ^ Statements about events that must have happened.
  , eventOrd       :: EventOrder     -- ^ Statements about the order of events that happened.
  , compromised    :: S.Set Message  -- ^ Statements about agents being compromised.
  , uncompromised  :: S.Set Message  -- ^ Statements about agents being uncompromised.
  , equalities     :: E.Equalities   -- ^ All equalities that must hold.
  , inequalities   :: S.Set Inequality -- ^ All inequalities that must hold.
  , tidQuantifiers :: S.Set TID      -- ^ All thread IDs occurring in the facts.
  , amQuantifiers  :: S.Set ArbMsgId  -- ^ All arbitrary-message IDs ocurring in the facts.
  , optTyping      :: Maybe Typing   -- ^ The typing if there is any that the
                                     --   current state satisfies.
   -- NOTE: The Maybe is used for facts that don't have a typing.
  , typeAnns       :: S.Set TypeAnn  -- ^ Type annotations on messages.

  , covered        :: S.Set Message  -- ^ The messages that have already been used in a
                                     --   case distinction.
  , failedEqs      :: S.Set AnyEq    -- ^ All equalities which could not be solved.
                                     --   A non-empty set implies false.
  , protocol       :: Protocol       -- ^ The protocol that the current state
                                     --   is a reachable state of.
  }
  deriving( Eq, Ord, Show, Data, Typeable )

------------------------------------------------------------------------------
-- Queries
------------------------------------------------------------------------------

-- | True if no premises apart from state reachability and the optional
-- well-typedness claim are present. Note that there may be quantifiers and
-- covered goals.
nullFacts :: Facts -> Bool
nullFacts facts =
  S.null (events facts) &&
  S.null (eventOrd facts) &&
  S.null (compromised facts) &&
  S.null (uncompromised facts) &&
  S.null (typeAnns facts) &&
  E.null (equalities facts) &&
  S.null (inequalities facts) &&
  S.null (failedEqs facts)

------------------------------------------------------------------------------
-- Construction
------------------------------------------------------------------------------

-- | Empty set of facts; logically equivalent to true.
empty :: Protocol -> Facts
empty = Facts
    S.empty S.empty S.empty S.empty E.empty S.empty S.empty S.empty Nothing S.empty S.empty S.empty

-- | Set the protocol.
--
-- PRE: Setting a protocol is the identity iff the new protocol agrees with the
-- existing one.
--
-- Uses 'fail' for error reporting.
setProtocol :: Monad m => Protocol -> Facts -> m Facts
setProtocol proto facts
  | proto == protocol facts = return facts
  | otherwise = fail $ "setProtocol: '" ++ show proto ++ "' /= '"
                                        ++ show (protocol facts) ++ "'"

-- | Set the typing.
--
-- PRE: There mustn't be a different existing typing.
--
-- Uses 'fail' for error reporting.
setTyping :: Monad m => Typing -> Facts -> m Facts
setTyping typ facts = case optTyping facts of
  Just typ' | typ /= typ' -> fail $ "setTyping: '" ++ show typ ++ "' /= '"
                                                   ++ show typ' ++ "'"
  _                       -> return $ facts { optTyping = Just typ }


-- | Create a mapping from the equalities of the facts.
eqsToMapping :: Facts -> Mapping
eqsToMapping = Mapping . equalities

-- Quantifiers
--------------

-- | Tries to quantify the given thread identifier. If it is already quantified
-- `fail` is called in the given monad.
quantifyTID :: Monad m => TID -> Facts -> m Facts
quantifyTID tid facts
  | null (tidQuantified facts tid) =
      fail $ "quantifyTID: " ++ show tid ++ " already quantified."
  | otherwise               =
      return $ facts { tidQuantifiers = S.insert tid $ tidQuantifiers facts }

-- | Tries to quantify the given agent identifier. If it is already quantified
-- `fail` is called in the given monad.
quantifyArbMsgId :: Monad m => ArbMsgId -> Facts -> m Facts
quantifyArbMsgId aid facts
  | null (arbMsgIdQuantified facts aid) =
      fail $ "quantifyArbMsgId: " ++ show aid ++ " already quantified."
  | otherwise                   =
      return $ facts { amQuantifiers = S.insert aid $ amQuantifiers facts }

-- | Get a fresh TID and the updated set of facts.
freshTID ::  Facts -> (TID, Facts)
freshTID facts =
  (tid, facts { tidQuantifiers = S.insert tid $ tidQuantifiers facts })
  where tid = nextTID facts

-- | Get a fresh ArbMsgId and the updated set of facts.
freshArbMsgId :: Facts -> (ArbMsgId, Facts)
freshArbMsgId facts =
  (aid, facts { amQuantifiers = S.insert aid $ amQuantifiers facts })
  where aid = nextArbMsgId facts

-- | The list of thread ids that are quantified.
quantifiedTIDs :: Facts -> [TID]
quantifiedTIDs = S.toList . tidQuantifiers

-- Certification
----------------

-- | A value certified to be satisfy. This is a type level construct
-- helping the implementor to discern between values from the outside and
-- values with their invariants checked.
--
-- What is missing is the binding between the context and the checked value. It
-- is up to the user to not mix this up.
newtype Cert a = Cert { certified :: a }
  deriving( Eq, Ord, Show )

-- | The results denotes the list of certification errors. If it is empty, then
-- certification succeeded.
type CertResult = [String]

-- | The successful certification result.
certSuccess :: CertResult
certSuccess = []

-- | Conditionally return a certification error.
certErrorIf :: Bool -> String -> CertResult
certErrorIf True  msg = [msg]
certErrorIf False _   = certSuccess

-- | Changed the certified value. Note that you have to guarantee that the
-- required invariants are not violated.
mapCertified :: (a -> b) -> Cert a -> Cert b
mapCertified f (Cert x) = Cert (f x)

-- | Check if a TID is quantified in these facts
tidQuantified :: Facts -> TID -> CertResult
tidQuantified facts tid =
    certErrorIf (tid `S.notMember` tidQuantifiers facts) $
        "unquantified tid: " ++ show tid

-- | Check if a agent id is quantified in these facts
arbMsgIdQuantified :: Facts -> ArbMsgId -> CertResult
arbMsgIdQuantified facts aid =
    certErrorIf (aid `S.notMember` amQuantifiers facts) $
        "unquantified aid: " ++ show aid

-- | Check if all logical variables in an local id are quantified.
lidQuantified :: Facts -> LocalId -> CertResult
lidQuantified facts = tidQuantified facts . lidTID

-- | Check if all logical variables in an agent variable are quantified.
avarQuantified :: Facts -> AVar -> CertResult
avarQuantified facts = lidQuantified facts . getAVar

-- | Check if all logical variables in an message variable are quantified.
mvarQuantified :: Facts -> MVar -> CertResult
mvarQuantified facts = lidQuantified facts . getMVar

-- | Check if all logical variables in an message are quantified.
msgQuantified :: Facts -> Message -> CertResult
msgQuantified facts m =
    foldMap (tidQuantified     facts) (msgTIDs m)     ><
    foldMap (arbMsgIdQuantified facts) (msgAMIDs m)

-- | Check if all logical variables in an event are quantified.
evQuantified :: Facts -> Event -> CertResult
evQuantified facts (Learn m)    = msgQuantified facts m
evQuantified facts (Step tid _) = tidQuantified facts tid

-- | Check if all logical variables in an event order are quantified.
evOrdQuantified :: Facts -> (Event, Event) -> CertResult
evOrdQuantified facts (e1, e2) = evQuantified facts e1 >< evQuantified facts e2

-- | Check if all logical variables in a type annotation are quantified.
typeAnnQuantified :: Facts -> TypeAnn -> CertResult
typeAnnQuantified facts (m, _, tid) =
    msgQuantified facts m >< tidQuantified facts tid

-- | Check if an equality contains only quantified logical variables.
anyEqQuantified :: Facts -> E.AnyEq -> CertResult
anyEqQuantified facts eq = case eq of
    E.TIDEq  (tid1, tid2) -> tidQuantified facts tid1 >< tidQuantified facts tid2
    E.TIDRoleEq (tid, _)  -> tidQuantified facts tid
    E.RoleEq _            -> certSuccess
    E.ArbMsgEq (aid, rhs) -> arbMsgIdQuantified facts aid >< msgQuantified facts rhs
    E.AVarEq (av1, av2)   -> avarQuantified facts av1 >< avarQuantified facts av2
    E.MVarEq (mv, m)      -> mvarQuantified facts mv >< msgQuantified facts m
    E.MsgEq (m1, m2)      -> msgQuantified facts m1 >< msgQuantified facts m2

-- | Check if an inequality contains only quantified logical variables.
ineqQuantified :: Facts -> E.Inequality -> CertResult
ineqQuantified facts = anyEqQuantified facts . getInequality

-- | Check if an atom contains only quantified logical variables.
atomQuantified :: Facts -> Atom -> CertResult
atomQuantified facts atom = case atom of
  ABool _      -> certSuccess
  AEq eq       -> anyEqQuantified facts eq
  AIneq eq     -> ineqQuantified  facts eq
  AEv ev       -> evQuantified    facts ev
  AEvOrd ord   -> evOrdQuantified facts ord
  ACompr m     -> msgQuantified   facts m
  AUncompr m   -> msgQuantified   facts m
  AHasType tya -> typeAnnQuantified facts tya
  ATyping _    -> certSuccess
  AReachable _ -> certSuccess


-- | Certification of a value with respect to a check and a morphism required
-- to establish the required invariants in the context of a set of facts.
certify :: Show a => (Facts -> a -> CertResult) -> (Facts -> a -> b)
        -> Facts -> a -> Cert b
certify check conv facts x =
    case check facts x of
        []   -> x'
        -- FIXME: Somehow bidirectional shared keys lead in some cases to an
        -- unquantified thread identifier error. However, all of these cases
        -- dealt with proofs that failed (i.e., attackable security
        -- properties). Therfore, we have not yet debugged this to its full
        -- extent.
        errs -> trace
            (unlines $
                ("warning: internal check failed for '" ++ show x ++ "' because of") :
                (map ("  "++) $ errs)
             )
             x'
  where
    x' = Cert $ conv facts x

-- | Certify a message.
certMsg :: Facts -> Message -> Cert Message
certMsg = certify msgQuantified substMsg

-- | Certify an event.
-- certEv :: Facts -> Event -> Cert Event
-- certEv = certify evQuantified substEv

-- | Certify an event order.
certEvOrd :: Facts -> (Event, Event) -> Cert (Event, Event)
certEvOrd = certify evOrdQuantified substEvOrd

-- | Certify an equality.
certAnyEq :: Facts -> E.AnyEq -> Cert E.AnyEq
certAnyEq = certify anyEqQuantified substAnyEq

-- | Certify an inequality.
certInequality :: Facts -> Inequality -> Cert Inequality
certInequality = certify ineqQuantified substInequality

-- | Certify an atom: All logical variables are quantified under the given
-- facts and all values are invariant under the equalities associated with the
-- facts.
certAtom :: Facts -> Atom -> Cert Atom
certAtom = certify atomQuantified substAtom

-- | Certify an a type annotation.
certTypeAnn :: Facts -> TypeAnn -> Cert TypeAnn
certTypeAnn = certify typeAnnQuantified substTypeAnn


-- Equalities
-------------

-- | Lift a substitutition.
liftSubst :: (E.Equalities -> a -> b) -> Facts -> a -> b
liftSubst subst facts = subst (equalities facts)

-- | Substitute a TID.
substTID :: Facts -> TID -> TID
substTID = liftSubst E.substTID

-- TODO: Remove if not used anymore.

-- | Substitute an agent variale.
-- substAVar :: Facts -> AVar -> AVar
-- substAVar = liftSubst E.substAVar

-- | Substitute an message variale.
-- substMVar :: Facts -> MVar -> Message
-- substMVar = liftSubst E.substMVar

-- | Substitute an message variale.
substAMID :: Facts -> ArbMsgId -> Message
substAMID = liftSubst E.substAMID

-- | Substitute an message variale.
-- substArbMsgEqRHS :: Facts -> E.ArbMsgEqRHS -> E.ArbMsgEqRHS
-- substArbMsgEqRHS = liftSubst E.substArbMsgEqRHS

-- | Substitute a message.
substMsg :: Facts -> Message -> Message
substMsg = liftSubst E.substMsg

-- | Substitute an equality.
substAnyEq :: Facts -> E.AnyEq -> E.AnyEq
substAnyEq = liftSubst E.substAnyEq

-- | Substitute an inequality.
substInequality :: Facts -> Inequality -> Inequality
substInequality = liftSubst E.substInequality

-- | Substitute an atom.
substAtom :: Facts -> Atom -> Atom
substAtom = liftSubst F.substAtom

-- | Substitute an event.
substEv :: Facts -> Event -> Event
substEv = liftSubst E.substEv

-- | Substitute an event order.
substEvOrd :: Facts -> (Event, Event) -> (Event, Event)
substEvOrd = liftSubst E.substEvOrd

-- | Substitute a type annotation.
substTypeAnn :: Facts -> TypeAnn -> TypeAnn
substTypeAnn = liftSubst T.substTypeAnn

-- | The role assigned to a thread.
threadRole :: TID -> Facts -> Maybe Role
threadRole tid = E.threadRole tid . equalities

-- | Remove thread identifier and agent identifiers equalities and the
-- quantifiers that were mapped by them.
--
-- This operation is logically safe iff there are no references to the mapped
-- logical variables outside the facts.
trimQuantifiers :: Facts -> Facts
trimQuantifiers facts = facts {
    equalities = eqs'
  , tidQuantifiers = S.filter (`notElem` tids) $ tidQuantifiers facts
  , amQuantifiers = S.filter (`notElem` aids) $ amQuantifiers facts
  }
  where
  (tids, (aids, eqs')) = second E.trimArbMsgEqs . E.trimTIDEqs $ equalities facts

-- | Solve the equations in the context of the given facts and update all facts
-- accordingly.
solve :: Monad m => [Cert E.AnyEq] -> Facts -> m Facts
solve ueqs facts = do
  eqs <- E.solve (map certified ueqs) $ equalities facts
  return . removeTrivialFacts $ facts {
      events         = S.map (E.substEv eqs)    (events        facts)
    , eventOrd       = S.map (E.substEvOrd eqs) (eventOrd      facts)
    , compromised    = S.map (E.substMsg eqs)   (compromised   facts)
    , uncompromised  = S.map (E.substMsg eqs)   (uncompromised facts)
    , equalities     = eqs
    , inequalities   = S.map (E.substInequality eqs) (inequalities facts)
    , tidQuantifiers = tidQuantifiers facts
    , amQuantifiers  = amQuantifiers facts
    , typeAnns       = S.map (T.substTypeAnn eqs) (typeAnns facts)
    , covered        = S.map (E.substMsg eqs)     (covered facts)
    , failedEqs      = S.map (E.substAnyEq eqs)   (failedEqs facts)
    }


-- Compromised agents
---------------------

-- | Mark an message as being a compromised agent name.
compromise :: Message -> Facts -> Facts
compromise m facts =
  facts { compromised = S.insert (certified m') (compromised facts) }
  where m' = certMsg facts m

-- | Mark an message as not being a compromised agent name.
uncompromise :: Message -> Facts -> Facts
uncompromise m facts =
  facts { uncompromised = S.insert (certified m') (uncompromised facts) }
  where m' = certMsg facts m


-- Incremental construction
---------------------------

-- | Inserts an event fact.
insertEv :: Cert Event -> Facts -> Facts
insertEv ev prems = prems { events = S.insert (certified ev) (events prems) }

-- | Delete an event fact.
deleteEv :: Cert Event -> Facts -> Facts
deleteEv ev prems = prems { events = S.delete (certified ev) (events prems) }

-- | Insert a learn event fact.
insertLearn :: Cert Message -> Facts -> Facts
insertLearn m = insertEv (mapCertified Learn m)

-- | Inserts an event order fact.
insertEvOrd :: Cert (Event, Event) -> Facts -> Facts
insertEvOrd ord prems =
  prems { eventOrd = S.insert (certified ord) (eventOrd prems) }

-- | Delete an event order fact.
deleteEvOrd :: Cert (Event, Event) -> Facts -> Facts
deleteEvOrd ord prems =
  prems { eventOrd = S.delete (certified ord) (eventOrd prems) }

-- | Insert a thread identifier to role assignment. This will fail with
-- an error iff this assignment conflicts with an existing assignment of
-- the same thread identifier to a different role.
insertRole :: TID -> Role -> Facts -> Facts
insertRole tid role facts = maybe err id $
  solve [certAnyEq facts $ E.TIDRoleEq (tid, role)] facts
  where
  err = error $ "insertRole: failed to insert role"

-- | Annotate a message with a type interpreted with respect to a specific
-- thread.
insertTypeAnn:: Cert TypeAnn -> Facts -> Facts
insertTypeAnn tya prems =
  prems { typeAnns = S.insert (certified tya) (typeAnns prems) }

-- | Insert an inequality.
insertInequality :: Cert Inequality -> Facts -> Facts
insertInequality ineq facts =
  facts { inequalities = S.insert (certified ineq) (inequalities facts) }

-- | Insert a failed equation.
insertFailedEq :: Cert E.AnyEq -> Facts -> Facts
insertFailedEq eq facts =
  facts { failedEqs = S.insert (certified eq) (failedEqs facts) }

-- | Build the conjunction of the atoms and the facts; a result of 'Nothing'
-- means that the conjunction is logically equivalent to False. This will occur
-- in case 'AFalse' is conjoined or an equality that cannot be unified.
--
-- PRE: The atom must pass certification under the given facts.
--
conjoinAtoms :: Monad m => [Atom] -> Facts -> m (Maybe Facts)
conjoinAtoms atoms facts0 =
    foldM conjoinAtom (Just facts0) atoms
  where
    conjoinAtom Nothing      _    = return Nothing
    conjoinAtom (Just facts) atom = case certified $ certAtom facts atom of
      ABool False  -> return Nothing
      ABool True   -> return (Just facts)
      -- FIXME: repeated calls to solve may be a bit expensive due to duplicated
      -- work of 'removeTrivialFacts'.
      AEq eq       -> return        $ solve [Cert eq] facts
      AIneq eq     -> return . Just $ insertInequality (Cert eq) facts
      AEv ev       -> return . Just $ insertEvNonTrivial (Cert ev) facts
      AEvOrd ord   -> return . Just $ insertEvOrdNonTrivial (Cert ord) facts
      ACompr m     -> return . Just $ compromise m facts
      AUncompr m   -> return . Just $ uncompromise m facts
      AReachable p -> Just `liftM` setProtocol p facts
      ATyping typ  -> Just `liftM` setTyping typ facts
      AHasType tya -> return . Just $ insertTypeAnn (Cert tya) facts


-- Combined construction and application of inference rules
-----------------------------------------------------------

-- | Inserts an event order fact and both event facts implied by the presence
-- of this event oder fact.
insertEvOrdAndEvs :: Cert (Event, Event) -> Facts -> Facts
insertEvOrdAndEvs ord =
  insertEv (mapCertified fst ord) .
  insertEv (mapCertified snd ord) . insertEvOrd ord

-- | Insert all non-trivial events implied by the given event.
insertEvNonTrivial :: Cert Event -> Facts -> Facts
insertEvNonTrivial ev prems = case certified ev of
  Learn m  -> foldl' (flip (insertLearn . Cert)) prems (splitNonTrivial m)
  Step _ _ -> insertEv ev prems

-- | Insert all event orders which are non-trivial in their first argument
-- implied by the given event order.
insertEvOrdNonTrivial :: Cert (Event, Event) -> Facts -> Facts
insertEvOrdNonTrivial ord prems = case certified ord of
  (Learn m, to) -> foldl' (insertLearnBefore to) prems (splitNonTrivial m)
  _             -> insertEvOrdAndEvs ord prems
  where
  insertLearnBefore to p m = insertEvOrdAndEvs (Cert (Learn m, to)) p

-- | Insert an executed role step and all non-trivial facts implied by the
-- Input, MatchEq, and NotMatch rules.
--
-- TODO: Update name to include MatchEq/NotMatch rule.
insertStepInputClosed :: Cert (TID, RoleStep) -> Facts -> Facts
insertStepInputClosed s prems = case certified s of
  (tid, step@(Recv _ pt))         ->
    let m = substMsg prems (inst tid pt)
    in  insertEvOrdNonTrivial (Cert (Learn m, Step tid step)) prems
  (tid, step@(Match _ True v pt)) ->
    let eq  = certAnyEq prems . mkEquality tid v $ substMsg prems (inst tid pt)
    in  insertEv (Cert (Step tid step)) . maybe (insertFailedEq eq prems) id $ solve [eq] prems
  (tid, step@(Match _ False v pt)) ->
    let ineq = certInequality prems . Inequality . mkEquality tid v $ substMsg prems (inst tid pt)
    in  insertEv (Cert (Step tid step)) $ insertInequality ineq prems
  (tid, step)                     -> insertEv (Cert (Step tid step)) prems
  where
    mkEquality tid var msg = case var of
        SAVar i -> case msg of
            MAVar av -> AVarEq (AVar $ LocalId (i, tid), av)
            MMVar mv -> MVarEq (mv, MAVar $ AVar $ LocalId (i, tid))
            _        -> MsgEq (msg, MAVar $ AVar $ LocalId (i, tid))
        SMVar i -> MVarEq (MVar $ LocalId (i, tid), msg)

-- | Insert an executed role step and all non-trivial facts implied by the
-- Input, MatchEq, NotMatch, and Role rules.
insertStepPrefixClosed :: Cert (TID, RoleStep) -> Facts -> Facts
insertStepPrefixClosed s = case certified s of
  (tid, step) -> execState $ do
    let err = error $ "insertStepPrefixClosed: no role assigned to thread " ++ show tid
    role <- gets (fromMaybe err . threadRole tid)
    let prefix        = takeWhile (/= step) (roleSteps role) ++ [step]
        insertStepOrd = modify . insertEvOrdAndEvs . Cert . (Step tid *** Step tid)
    mapM_ (modify . insertStepInputClosed . (Cert . ((,) tid))) prefix
    mapM_ insertStepOrd $ zip prefix (tail prefix)

-- | Insert an event an all non-trivial facts implied by the Input, MatchEq,
-- and Role rules.
insertEvSaturated :: Cert Event -> Facts -> Facts
insertEvSaturated ev = case certified ev of
  (Learn _      ) -> insertEvNonTrivial ev
  (Step tid step) -> insertStepPrefixClosed (Cert (tid, step))

-- | Derive all non-trivial facts implied by the splitting rules and remove
-- trivial facts.
removeTrivialFacts :: Facts -> Facts
removeTrivialFacts = execState $ do
  evs <- S.toList <$> gets events
  mapM_ checkEv evs
  evord <- S.toList <$> gets eventOrd
  mapM_ checkEvOrd evord
  where
  checkEv ev@(Learn m)
    | trivial m = modify (insertEvNonTrivial (Cert ev) . deleteEv (Cert ev))
    | otherwise = return ()
  checkEv _ = return ()
  checkEvOrd ord@(Learn m, _)
    | trivial m = modify (insertEvOrdNonTrivial (Cert ord) . deleteEvOrd (Cert ord))
    | otherwise = return ()
  checkEvOrd _ = return ()

-- | Saturate facts modulo removal of trivial facts; i.e. apply all rules
-- except the chain rule eagerly and remove trivial facts.
saturateFacts :: Facts -> Facts
saturateFacts = execState $ do
  modify removeTrivialFacts
  evs <- gets events
  evord <- gets eventOrd
  let evs' = (evs `S.union` S.map fst evord) `S.union` S.map snd evord
  mapM_ (modify . insertEvSaturated . Cert) (S.toList evs')

-- | Make use of the typing assumption by checking for instantiated message variables
-- if their instantiation does not agree with the structural type and hence they must
-- be known before the given step.
--
-- Is equal to 'mzero' in case the facts don't contain a typing.
exploitTypingFacts :: MonadPlus m => Facts -> m Facts
exploitTypingFacts facts0 = return facts0 -- TODO: implement this check.
  {- cf. the one for weak atomicity below:
  do
    -- WeaklyAtomic -> foldl' weaklyAtomic facts0 . E.getMVarEqs . equalities $ facts0
  where
    weaklyAtomic :: Facts -> (MVar, Message) -> Facts
    weaklyAtomic facts (_,                       MMVar _ ) = facts
    weaklyAtomic facts (_,                       MFresh _) = facts
    weaklyAtomic facts (MVar (LocalId (i, tid)), m       ) =
      case threadRole tid facts of
        Nothing -> error $ "exploitTypingFacts: no role assigned to '"++show tid++"'"
        Just role ->
          case find (S.member i . stepFMV) (roleSteps role) of
            Nothing   ->
              error $ "exploitTypingFacts: variable '"++show i++"' does not occur in role."
            Just step ->
              insertEvOrdNonTrivial (Cert (Learn m, Step tid step)) facts
  -}

------------------------------------------------------------------------------
-- Queries
------------------------------------------------------------------------------

-- | The next free thread identifier
nextTID :: Facts -> TID
nextTID = maybe 0 (succ . fst) . S.maxView . tidQuantifiers

-- | The next free agent identifier
nextArbMsgId :: Facts -> ArbMsgId
nextArbMsgId = maybe 0 (succ . fst) . S.maxView . amQuantifiers

-- | Try to retrieve the typing; equal to 'mzero' if there is none.
getTyping :: MonadPlus m => Facts -> m Typing
getTyping = maybe mzero return . optTyping

-- | Check if a set of facts is trivially contradictory.
--
-- NOTE: This is not the same as trying to prove the atom AFalse under these
-- premises. The checks are separated due to efficiency reasons.
proveFalse :: Facts -> Bool
proveFalse prems =
    not (S.null (failedEqs prems)) ||
    not (S.null (compromised prems `S.intersection` uncompromised prems)) ||
    any noAgent (S.toList (compromised prems)) ||
    cyclic (eventOrd prems) ||
    any reflexiveIneq (S.toList (inequalities prems))
  where
    noAgent (MMVar _)  = False
    noAgent (MAVar _)  = False
    noAgent (MArbMsg _) = False
    noAgent _          = True

-- | True iff the facts imply the validity of the given atom. Note that this check
-- is incomplete; i.e. there may be atoms that would be true under these facts,
-- but are not detected as such.
--
-- PRE: Trivial learn events must be split. You may achieve this using
-- 'removeTrivialFacts'.
proveAtom :: Facts -> Atom -> Bool
proveAtom facts = checkAtom . certified . certAtom facts
  where
  -- PRE: atom is fully substituted
  checkAtom atom = case atom of
    ABool b              -> b
    AEq eq               -> E.reflexive eq
    AIneq eq             -> False
    AEv (Learn m)        -> all checkLearn (splitNonTrivial m)
    AEv ev               -> ev `S.member` events facts
    AEvOrd (Learn m, e2) -> all (checkLearnBefore e2) (splitNonTrivial m)
    AEvOrd (e1, e2)      -> before (eventOrd facts) e1 e2
    ACompr m             -> m `S.member` compromised facts
    AUncompr m           -> m `S.member` uncompromised facts
    AHasType tya         -> hasType tya
    ATyping typ          -> Just typ == optTyping facts
    AReachable proto     -> proto == protocol facts

  checkLearn m          = Learn m `S.member` events facts
  checkLearnBefore to m = before (eventOrd facts) (Learn m) to

  hasType (m0, ty0, tid0) =
      go m0 ty0
    where
      go (MAVar _)     (AgentT)        = True
      go (MConst i)    (ConstT i')     = i == i'
      go (MFresh (Fresh (LocalId (i, tid)))) (NonceT role i') =
          i == i' && threadRole tid facts == Just role
      go (MHash m)     (HashT ty)      = go m ty
      go (MEnc m1 m2)  (EncT ty1 ty2)  = go m1 ty1 && go m2 ty2
      go (MTup m1 m2)  (TupT ty1 ty2)  = go m1 ty1 && go m2 ty2
      go (MSymK m1 m2) (SymKT ty1 ty2) = go m1 ty1 && go m2 ty2
      go (MAsymPK m)   (AsymPKT ty)    = go m ty
      go (MAsymSK m)   (AsymSKT ty)    = go m ty
      go  m            (KnownT step)   = checkAtom (AEvOrd (Learn m, Step tid0 step))
      go  m            (SumT ty1 ty2)  = go m ty1 || go m ty2
      go  m            ty              = or $ do
          (m', ty', tid') <- S.toList $ typeAnns facts
          guard (m == m')
          return $ (ty', tid') `subType` (ty, tid0)

  -- ty `subType` ty' holds iff every instance of ty is also an instance of ty'.
  subType (ty0, tid) (ty'0, tid') =
      go ty0 ty'0
    where
      go (EncT ty1 ty2)  (EncT ty'1 ty'2)  = go ty1 ty'1 && go ty2 ty'2
      go (TupT ty1 ty2)  (TupT ty'1 ty'2)  = go ty1 ty'1 && go ty2 ty'2
      go (SymKT ty1 ty2) (SymKT ty'1 ty'2) = go ty1 ty'1 && go ty2 ty'2
      go (AsymPKT ty)    (AsymPKT ty')     = go ty ty'
      go (AsymSKT ty)    (AsymSKT ty')     = go ty ty'
      -- NOTE: SumT handling results in an under-approximation for nested
      -- SumTs. The left-hand SumTs should be pushed outwards first; such
      -- that they are taken apart before the right-hand SumTs.
      go (SumT ty1 ty2)  ty'               = go ty1 ty' && go ty2 ty'
      go ty              (SumT ty'1 ty'2)  = go ty ty'1 || go ty ty'2
      go (KnownT step)   (KnownT step')    =
          -- every message before step is also before step'
          checkAtom (AEvOrd (Step tid step, Step tid' step'))
      go ty              ty'               = ty == ty'


-- | Try to prove that the formula holds under these facts.
proveFormula :: Facts -> Formula -> Bool
proveFormula facts = prove (Mapping E.empty)
  where
  prove mapping (FAtom atom)  = proveAtom facts (F.substAtom (getMappingEqs mapping) atom)
  prove mapping (FConj f1 f2) = prove mapping f1 && prove mapping f2
  prove mapping (FDisj f1 f2) = prove mapping f1 || prove mapping f2
  prove mapping (FExists v f) = any (\mk -> prove (mk mapping) f) (mkMappings v)
  -- the mappings assign witnesses to the existentially quantified variables.
  mkMappings (Left  tid) = map (E.addTIDMapping tid)     (S.toList $ tidQuantifiers facts)
  mkMappings (Right aid) = map (E.addArbMsgIdMapping aid) (S.toList $ amQuantifiers facts)

-- | Try to find a long-term-key that must be secret due to the
-- uncompromisedness assumptions, but is claimed to be known to the intruder;
-- i.e. if this method returns a message, then the premises are contradictory.
exploitLongTermKeySecrecy :: Facts -> Maybe Message
exploitLongTermKeySecrecy facts = msum . map check . S.toList $ events facts
  where
    check (Learn key@(MSymK m1 m2)) = do
      guard (all (`S.member` uncompromised facts) [m1, m2])
      return key
    check (Learn key@(MShrK m1 m2)) = do
      guard (all (`S.member` uncompromised facts) [m1, m2])
      return key
    check (Learn key@(MAsymSK m)) = do
      guard (m `S.member` uncompromised facts)
      return key
    check _ = mzero


-- Deconstruction
-----------------

-- | Represent the facts as a set of atoms.
--
-- TODO: non-empty failedEqs imply False?
toAtoms :: Facts -> [Atom]
toAtoms facts = mconcat [
    AEq      <$> E.toAnyEqs (equalities    facts)
  , AIneq    <$> S.toList   (inequalities  facts)
  , AUncompr <$> S.toList   (uncompromised facts)
  , ACompr   <$> S.toList   (compromised   facts)
  , AEv      <$> S.toList   (events        facts)
  , AEvOrd   <$> S.toList   (eventOrd      facts)
  , AHasType <$> S.toList   (typeAnns      facts)
  ]

-- | Represent the facts as a formula.
toFormula :: Facts -> Formula
toFormula facts = case toAtoms facts of
    []    -> FAtom (ABool True)
    atoms -> foldr1 FConj (map FAtom atoms)


------------------------------------------------------------------------------
-- Chain Rule Application
------------------------------------------------------------------------------

-- | Compute the set of messages that have no given previous event.
--
-- PRE: Assumes all events in the event order are also part of the
--      set of events.
openMessages :: Facts -> [Message]
openMessages prems = nub $ filter okGoal $ catMaybes
  [ case e of Learn m -> Just m; _ -> Nothing
  | e <- S.toList $ events prems `S.difference` S.map snd (eventOrd prems) ]
  where
  okGoal (MMVar _)   = False
  okGoal (MArbMsg _) = False
  okGoal (MAsymPK _) = False
  okGoal (MInvKey _) = False
  okGoal m           = not (trivial m) && (m `S.notMember` covered prems)

-- | Sort open messages ascending with respect to the maximal thread id.
oldestOpenMessages :: Facts -> [Message]
oldestOpenMessages prems =
  map fst . sortOn snd . mapMaybe score $ ms
  where
  ms = openMessages prems
  co = compromised prems
  ltkLocalIds (MAsymSK m@(MAVar a))
    | m `S.member` co                      = []
    | otherwise                            = [getAVar a]
  ltkLocalIds (MSymK ma@(MAVar a) mb@(MAVar b))
    | ma `S.member` co || mb `S.member` co = []
    | otherwise                            = [getAVar a, getAVar b]
  ltkLocalIds (MShrK ma@(MAVar a) mb@(MAVar b))
    | ma `S.member` co || mb `S.member` co = []
    | otherwise                            = [getAVar a, getAVar b]
  ltkLocalIds _                            = []
  score m = fmap (\x->(m,x)) . maximumMay $
    [ tid | MVar (LocalId (_,tid)) <- msgFMV m ] ++
    [ tid | Fresh (LocalId (_,tid)) <- msgFresh m ] ++
    [ tid | LocalId (_,tid) <- ltkLocalIds m ]

-- | A data type to represent the state of the chain rule computation.
data ChainRuleState = ChainRuleState
  { crsCaseName :: [String]
  , crsNewVars  :: [Either TID ArbMsgId]
  , crsFacts    :: Facts
  , crsFinalEq  :: Maybe E.MsgEq
  }

type ChainRuleM = StateT ChainRuleState []

-- | Add a fragment of the case name.
addCaseFragment :: String -> ChainRuleM ()
addCaseFragment name = modify $ \crs -> crs { crsCaseName = crsCaseName crs ++ [name] }

-- | Add a newly quantified variable.
addNewVar :: Either TID ArbMsgId -> ChainRuleM ()
addNewVar v = modify $ \crs -> crs { crsNewVars = crsNewVars crs ++ [v] }

-- | Change the facts of the chain rule computation state.
modifyFacts :: (Facts -> Facts) -> ChainRuleM ()
modifyFacts f = modify $ \crs -> crs { crsFacts = f $ crsFacts crs }

-- | Gets a component of the facts.
getsFacts :: (Facts -> a) -> ChainRuleM a
getsFacts f = gets (f . crsFacts)

-- | Set the equality that has to be solved for the case to be complete.
setFinalEq :: E.MsgEq -> ChainRuleM ()
setFinalEq eq = modify $ \crs -> crs { crsFinalEq = Just eq }

-- try to unify the two messages in the context of the current facts;
-- this function will always succeed, but the facts may be Nothing
unify :: Message -> Message -> ChainRuleM ()
unify m m'
  | m == m'   = return () -- performance optimization
  | otherwise = do
      crs <- get
      maybe mzero (modifyFacts . const) $
        solve [certAnyEq (crsFacts crs) $ E.MsgEq (m', m)] (crsFacts crs)

-- | Get a fresh thread identifier and update the facts accordingly
getFreshTID :: ChainRuleM TID
getFreshTID = do
  (tid, facts) <- getsFacts freshTID
  modifyFacts (const facts)
  addNewVar (Left tid)
  return tid

-- | Get a fresh thread arbitrary-message id and update the facts accordingly
getFreshAMID :: ChainRuleM ArbMsgId
getFreshAMID = do
  (aid, facts) <- getsFacts freshArbMsgId
  modifyFacts (const facts)
  addNewVar (Right aid)
  return aid

-- | Add a type annotation.
addTypeAnn :: TypeAnn -> ChainRuleM ()
addTypeAnn tya = modifyFacts $
    \facts -> insertTypeAnn (certTypeAnn facts tya) facts

-- | Delete the given type annotation. Logically, this means forgetting
-- the corresponding assumption.
deleteTypeAnn :: TypeAnn -> ChainRuleM ()
deleteTypeAnn tya = modifyFacts $
    \facts -> facts { typeAnns = S.delete tya (typeAnns facts) }

-- | Add a type annotation in expanded form. Expansion stops at SumT types
-- to avoid introducing unnecessary case distionctions.
addExpandedTypeAnn :: TypeAnn -> ChainRuleM ()
addExpandedTypeAnn (m, ty0, tid) = do
    m' <- expand (return m) ty0
    unify m m'
  where
    -- The first argument allows us to be lazy for creating new
    -- message-variables
    expand :: ChainRuleM Message -> Type -> ChainRuleM Message
    expand mkV AgentT          = do
        v <- mkV
        addTypeAnn (v, AgentT, tid)
        return v
    expand _ (NonceT role n) = do
        nTid <- getFreshTID
        modifyFacts $ insertRole nTid role
        return $ MFresh (Fresh (LocalId (n, nTid)))

    expand mkV ty@(SumT _ _) = do
        v <- mkV
        addTypeAnn (v, ty, tid)
        return v

    expand mkV ty@(KnownT _) = do
        v <- mkV
        addTypeAnn (v, ty, tid)
        return v

    expand _ (ConstT c)      = return (MConst c)
    expand _ (HashT ty)      = MHash   <$> expand arb ty
    expand _ (EncT ty1 ty2)  = MEnc    <$> expand arb ty1 <*> expand arb ty2
    expand _ (TupT ty1 ty2)  = MTup    <$> expand arb ty1 <*> expand arb ty2
    expand _ (SymKT ty1 ty2) = MSymK   <$> expand arb ty1 <*> expand arb ty2
    expand _ (AsymPKT ty)    = MAsymPK <$> expand arb ty
    expand _ (AsymSKT ty)    = MAsymSK <$> expand arb ty

    arb :: ChainRuleM Message
    arb = MArbMsg <$> getFreshAMID

-- | Get the type annotation of a message.
--
-- PRE: The message must be normalized with respect to the current facts.
getTypeAnn :: Message -> ChainRuleM TypeAnn
getTypeAnn m = do
  tyas <- gets (typeAnns . crsFacts)
  return $ headNote ("getTypeAnn: unannotated message '" ++ show m ++ "'")
                    [ tya | tya@(m', _, _) <- S.toList tyas, m == m' ]


-- number cases such that duplicates get numbered individually
numberCases :: [ChainRuleState] -> [ChainRuleState]
numberCases cases = (`evalState` M.empty) . forM cases $ \ crs -> do
  let name = concat . intersperse "_" . map head . group $ crsCaseName crs
  counter <- get
  let i = M.findWithDefault (0::Int) name counter
  put $ M.insert name (succ i) counter
  return $ crs {crsCaseName = return $ if i == 0 then name else name ++ "_" ++ show i}
  -- TODO: Remove this magic number (0) hack

-- | Extract the actual cases that result in new facts the other cases were
-- just there to compute the name
extractCase :: [E.AnyEq] -> ChainRuleState -> Maybe ((String, [Either TID ArbMsgId]), Facts)
extractCase delayedEqs0 crs = do
  let facts0 = crsFacts crs
      unmappedTID tid
        | substTID facts0 tid == tid = return (Left tid)
        | otherwise                  = mzero
      unmappedAMID aid
        | substAMID facts0 aid == MArbMsg aid = return (Right aid)
        | otherwise                           = mzero

      newVars = concatMap (either unmappedTID unmappedAMID) $ crsNewVars crs
      delayedEqs = maybe [] (return . E.MsgEq) (crsFinalEq crs) ++ delayedEqs0
  -- NOTE we are careful here to certify the equalities again. This should be a
  -- no-op, but we'll leave it in for debugging purposes.
  facts <- solve (map (certAnyEq facts0) delayedEqs) facts0
  -- NOTE that at this point the case name is stored in complete form in the
  -- head fragment. Trivial facts need to be removed as they could have been
  -- introduced due to unification.
  return ( (head $ crsCaseName crs, newVars)
         , removeTrivialFacts . trimQuantifiers $ facts)

-- | Cases stemming from the initial intruder knowledge
initialIntruderKnowledge :: Message -> ChainRuleM ()
initialIntruderKnowledge m = do
  facts <- getsFacts id
  case m of
    MSymK a b -> do
      addCaseFragment "ik0"
      ( (modifyFacts $ compromise a) `mplus` (modifyFacts $ compromise b) )
    MShrK a b -> do
      addCaseFragment "ik0"
      ( (modifyFacts $ compromise a) `mplus` (modifyFacts $ compromise b) )
    MAsymSK a             -> do
      addCaseFragment "ik0"
      modifyFacts $ compromise a
    -- fake
    MHash m1   -> do
      addCaseFragment "fake"
      modifyFacts $ insertEvOrdNonTrivial (certEvOrd facts (Learn m1, Learn m))
    MEnc m1 m2 -> do
      addCaseFragment "fake"
      modifyFacts
        ( insertEvOrdNonTrivial (certEvOrd facts (Learn m1, Learn m))
        . insertEvOrdNonTrivial (certEvOrd facts (Learn m2, Learn m)))
    MTup m1 m2 -> do
      addCaseFragment "fake"
      modifyFacts
        ( insertEvOrdNonTrivial (certEvOrd facts (Learn m1, Learn m))
        . insertEvOrdNonTrivial (certEvOrd facts (Learn m2, Learn m)))
    MFresh _ -> mzero
    _        -> error $ "initialIntruderKnowledge: message not supported '" ++ show m ++ "'"


-- | Apply the chain rule to a message in the context of a protocol and a set
-- of established facts. Returns the list of facts corresponding to the
-- disjunctions in the conclusion of the chain rule, which are not trivially
-- false due to syntactic inequality.
chainRuleFacts :: MonadPlus m => Message -> Facts -> m [((String, [Either TID ArbMsgId]), Facts)]
chainRuleFacts (MAVar _ )  _ = error $ "chainRuleFacts: application to agent variables not supported."
chainRuleFacts (MConst _)  _ = error $ "chainRuleFacts: application to global constants not supported."
chainRuleFacts (MInvKey _) _ = error $ "chainRuleFacts: application to symbolically inverted keys not supported."
chainRuleFacts (MAsymPK _) _ = error $ "chainRuleFacts: no support for public keys."
chainRuleFacts (MTup _ _)  _ = error $ "chainRuleFacts: no support for tuples."
chainRuleFacts m      facts0
  | proveAtom facts0 (F.AEv (Learn m)) = assembleCases `liftM` getTyping facts0
  | otherwise = error $ "chainRuleFacts: could not prove that '" ++ show m ++ "' is known to the intruder."
  where
  assembleCases typ =
      mapMaybe (extractCase delayedEqs) . numberCases .
      flip execStateT (ChainRuleState [] [] facts1 Nothing) $ (
        initialIntruderKnowledge m
        `mplus`
        -- send steps
        do tid <- getFreshTID
           proto <- getsFacts protocol
           msum $ map (roleChains typ tid) $ protoRoles proto
           -- don't output cases where the facts are already contradictory without
           -- the context. This caters for messages that are received and sent in
           -- exactly the same form.
           finalFacts <- gets crsFacts
           guard (not $ proveFalse finalFacts)
      )
    where
      facts1     = facts0 { equalities = E.empty
                          , covered = S.insert m $ covered facts0 }
      delayedEqs = E.toAnyEqs $ equalities facts0

  -- insert a list of previous events
  insertPrevious :: [Event] -> Event -> ChainRuleM ()
  insertPrevious prev ev = modifyFacts $
      \facts -> foldl' insertSingle facts prev
    where
      insertSingle p prevEv = insertEvOrdNonTrivial (certEvOrd p (prevEv, ev)) p

  -- enumerate chainRuleFacts starting from the given role
  roleChains :: Typing -> TID -> Role -> ChainRuleM ()
  roleChains typ tid role = do
      modifyFacts $ insertRole tid role
      addCaseFragment $ roleName role
      msum . map stepChains $ roleSteps role
    where
      stepChains :: RoleStep -> ChainRuleM ()
      stepChains (Recv _ _)       = mzero
      stepChains (Match _ _ _ _)  = mzero
      stepChains step@(Send _ pt) = do
          -- trace ("stepChains: " ++ roleName role ++"_"++getLabel l) (return ())
          modifyFacts $ insertStepPrefixClosed (Cert (tid, step))
          addCaseFragment $ stepLabel step
          mapM_ annotateMVarType $ S.toList $ patFMV pt
          msgChains [(Step tid step)] (inst tid pt)
        where
          -- annotating message variables with their type
          annotateMVarType mv =
              case M.lookup (mv, role) typ of
                Nothing -> error $ "stepChains: no type provided for '"++show v++"'"
                Just ty -> addExpandedTypeAnn (v, ty, tid)
            where
              v = MMVar (MVar (LocalId (mv, tid)))

          -- case naming
          msgName (MConst i)   = getId i
          msgName (MFresh fr)  = lidName . getFresh $ fr
          msgName (MAVar av)   = lidName . getAVar  $ av
          msgName (MMVar mv)   = lidName . getMVar  $ mv
          msgName (MHash _)    = "hash"
          msgName (MEnc _ _)   = "enc"
          msgName (MTup _ _)   = "tup"
          msgName (MSymK _ _)  = "K_ud"
          msgName (MShrK _ _)  = "K_bd"
          msgName (MAsymPK _)  = "pk"
          msgName (MAsymSK _)  = "sk"
          msgName (MArbMsg _)   = "someAgent"
          msgName (MInvKey _)  = "invKey"

          lidName = getId . fst . getLocalId

          -- chain enumeration
          msgChains :: [Event] -> Message -> ChainRuleM ()
          msgChains _ (MAVar _)        = mzero
          msgChains _ (MConst _)       = mzero
          msgChains prev v@(MArbMsg _) = typChains prev v
          msgChains prev v@(MMVar _)   = do
            addCaseFragment (msgName v)
            typChains prev v

          msgChains prev m'@(MEnc m1 m2) =
            do insertPrevious prev (Learn m')
               ( do -- trace ("msgChains: unify " ++ show m' ++ " =?= " ++ show m) (return ())
                    addCaseFragment $ msgName m'
                    setFinalEq (m', m)
                 `mplus`
                 msgChains [Learn m', Learn (MInvKey m2)] m1 )

          msgChains prev (MTup m1 m2) = msgChains prev m1 `mplus` msgChains prev m2

          msgChains prev m'@(MFresh _) = do
            insertPrevious prev (Learn m')
            addCaseFragment $ msgName m'
            -- here we have to unify, as Isabelle is also doing it early
            unify m' m

          -- the m' is an atomic message: just unify and be done with it.
          msgChains prev m' = do
            insertPrevious prev (Learn m')
            addCaseFragment $ msgName m'
            setFinalEq (m', m)

          -- exploiting type annotations.
          typChains :: [Event] -> Message -> ChainRuleM ()
          typChains prev v = do
            v' <- getsFacts (`substMsg` v)
            if v /= v'
              then msgChains prev v'
              else do
                tya <- getTypeAnn v
                case tya of
                  (_,tyaTy,tyaTid) -> case tyaTy of
                    KnownT _     -> mzero -- protocol wellformedness checks that KnownT implies cyclicity
                    AgentT       -> mzero -- we already know the agent names
                    SumT ty1 ty2 -> do
                        deleteTypeAnn tya
                        (addFastExpandedTypeAnn (v, ty1, tyaTid) <|>
                         addFastExpandedTypeAnn (v, ty2, tyaTid))
                        msgChains prev v
                    -- all other type annotations should have been expanded already.
                    _ -> error $ "msgChains: unexpanded type annotation: " ++ show tya

          -- fast expansion of type annotations: exploits that KnownT _ is guaranteed to be cyclic
          addFastExpandedTypeAnn (_, KnownT _, _) = mzero
          addFastExpandedTypeAnn tya              = addExpandedTypeAnn tya

------------------------------------------------------------------------------
-- Message Equality Splitting to deal with 'MShrK a b = MShrK x y' eqs
------------------------------------------------------------------------------

-- | Equalities that can be splitted.
splittableEqs :: Facts -> [MsgEq]
splittableEqs facts =
    do eq@(MShrK _ _, MShrK _ _) <- getPostEqs $ equalities facts
       guard (not $ uncurry (==) eq)
       return eq

-- | Split an equality between bi-directional symmetric shared keys.
splitEqFacts :: MsgEq -> Facts -> [Maybe Facts]
splitEqFacts (MShrK a b, MShrK x y) facts =
    [ addEqs [MsgEq (a,x), MsgEq (b,y)]
    , addEqs [MsgEq (b,x), MsgEq (a,y)]
    ]
  where
    addEqs eqs = solve (map (certAnyEq facts) eqs) facts

splitEqFacts eq _ =
    error $ "splitEqFacts: cannot split equality '" ++ show eq ++ "'"


------------------------------------------------------------------------------
-- Resolution
------------------------------------------------------------------------------

proveFacts :: Facts -- ^ From these premises
           -> Facts -- ^ Show the these conclusion
           -> Mapping -- ^ Mapping the free variables of the conclusion to the premises.
           -> Bool
proveFacts prems concl mapping =
  all (proveAtom prems . F.substAtom (getMappingEqs mapping)) (toAtoms concl)

-- | Possible unifiers making the first set of facts provable under the second
-- set of facts.  resulting equalities describe the mapping from all logical
-- variables of the first set of facts logical variables of the second set of
-- facts.
--
-- NOTE: You may want to use 'trimQuantifiers' before using this function to
-- avoid getting superfluous unifiers.
freeVariableMappings :: Facts -> Facts -> [Mapping]
freeVariableMappings from to = do
  mapping <- quantifierMappings
  return mapping
  where
  quantifierMappings = do
    tideqs  <- foldM mkTIDMapping     M.empty . S.toList $ tidQuantifiers from
    agnteqs <- foldM mkArbMsgIdMapping M.empty . S.toList $ amQuantifiers from
    return $ E.mkMapping tideqs agnteqs

  mkTIDMapping eqs tidF = do
    tidT <- msum . map return . S.toList $ tidQuantifiers to
    return $ M.insert tidF tidT eqs

  mkArbMsgIdMapping eqs aidF = do
    aidT <- msum . map return . S.toList $ amQuantifiers to
    return $ M.insert aidF aidT eqs


-- | Apply the mapping of agent and thread equalities to the facts.
--
-- TODO: Improve error handling. Currently, 'error' is called if the facts
-- are contradictory after the substitution.
applyMapping :: Mapping -> Facts -> Facts
applyMapping mapping facts0 = case newFacts of
     Just (Just facts) -> facts
     _ -> error "applyMapping: failed to reconstruct facts after mapping"
   where
     p = protocol facts0

     newFacts = addAtoms =<< quantifyAIDs =<< quantifyTIDs (empty p)

     eqs = getMappingEqs mapping
     qTID = flip (quantifyTID     . E.substTID eqs)
     qAID = flip (quantifyArbMsgId . extractArbMsgId . E.substAMID eqs)
     quantifyTIDs facts = foldM qTID facts $ S.toList $ tidQuantifiers facts0
     quantifyAIDs facts = foldM qAID facts $ S.toList $ amQuantifiers facts0

     addAtoms = conjoinAtoms atoms
     atoms = map (F.substAtom (getMappingEqs mapping)) . toAtoms $ facts0

     extractArbMsgId (MArbMsg aid) = aid
     extractArbMsgId m             = error $
        "applyMapping: arbitrary-message id mapped to '" ++ show m ++ "'"


------------------------------------------------------------------------------
-- Pretty Printing
------------------------------------------------------------------------------

-- Helper functions
-------------------

isReprEq :: E.AnyEq -> Bool
isReprEq (TIDEq _)   = False
isReprEq (ArbMsgEq _) = False
isReprEq _           = True

ppSet :: (a -> b) -> S.Set a -> [b]
ppSet ppElem = map ppElem . S.toList


-- To Isar
----------

-- | Pretty print the facts in Isar format.
isaFacts :: IsarConf -> Facts
         -> ([Doc],[Doc],[Doc]) -- ^ Quantified variables, representable facts, and non-representable facts
isaFacts conf facts =
    ( ppSet (isar conf) (tidQuantifiers facts) ++
      ppSet (isar conf) (amQuantifiers facts)
    , map (isar conf) reprEqs ++
      ppSet (isar conf)       (inequalities facts) ++
      ppSet (isaUncompr conf) (uncompromised facts) ++
      ppSet (isaCompr   conf) (compromised facts) ++
      ppSet (isaEventOrd conf (Mapping eqs)) (eventOrd facts) ++
      ppSet (isaEvent    conf (Mapping eqs)) (events facts)
    , map (isar conf) nonReprEqs
    )
    where
    eqs = equalities facts
    (reprEqs, nonReprEqs) = partition isReprEq $ E.toAnyEqs eqs


-- To a security protocol theory
--------------------------------


-- | Pretty print the facts in security protocol theory format.
sptFacts :: Facts
         -> ([Doc],[Doc],[Doc]) -- ^ Quantified variables, representable facts, and non-representable facts
sptFacts facts =
    ( ppSet sptTID     (tidQuantifiers facts) ++
      ppSet sptArbMsgId (amQuantifiers facts)
    , map sptAnyEq reprEqs ++
      ppSet sptInequality (inequalities facts) ++
      ppComprInfo "uncompromised" (uncompromised facts) ++
      ppComprInfo "compromised"   (compromised facts) ++
      (map (sptEventOrd (Mapping eqs)) $ transitiveChains $ S.toList $ eventOrd facts) ++
      ppSet (sptEvent (Mapping eqs)) (events facts)
    , (map (sptTypeAnn (`threadRole` facts)) $ S.toList $ typeAnns facts) ++
      map sptAnyEq nonReprEqs ++
      (map ppCovered $ S.toList $ covered facts)
    )
    where
    eqs = equalities facts
    (reprEqs, nonReprEqs) = partition isReprEq $ E.toAnyEqs eqs

    ppCovered m = text "covered" <> parens (sptMessage m)
    ppComprInfo setName set
      | S.null set = mzero
      | otherwise  = return . fsep $
          (text setName <> lparen : (map (nest 2) . punctuate comma)
            (ppSet sptMessage set)) ++ [rparen]

{-
sptSimpleFacts :: Facts -> Doc
sptSimpleFacts facts = case sptFacts facts of
    (ds1, ds2, ds3) -> vcat $ map vcat [ds1, [text ""], ds2, [text ""], ds3]
-}

-- | Compute a list of transitive chains representing an abbreviated version of
-- the given binary relation.
transitiveChains :: Ord a => [(a,a)] -> [[a]]
transitiveChains = sortOn head . foldl' insertEdge []
  where
  findChain sel x cs = case break ((x ==) . sel) cs of
      (_,[])                   -> (cs, [x])
      (cs1, c:cs2) -> (cs1 ++ cs2, c)
  insertEdge chains0 (from,to) =
    let (chains1, prefix) = findChain last from chains0
        (chains2, suffix) = findChain head to   chains1
    in (prefix ++ suffix) : chains2

