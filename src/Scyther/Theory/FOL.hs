-- | First-order logic encoding of a security protocol theory
module Scyther.Theory.FOL where

import Data.Maybe
import Data.Either
import Data.List
import Data.Monoid
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Traversable (sequenceA)

import Control.Basics
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.List

import Text.PrettyPrint.Applicative
import Text.Article

import qualified Logic.FOL.Sorted as F
import Logic.FOL.Sorted.TPTP

import Scyther.Protocol
import Scyther.Message
import Scyther.Facts
import Scyther.Theorem
import Scyther.Theory


-- Operators
------------

infix 4 .<.


-- Utilities
------------

type Accessor r a = (r -> a, a -> r -> r)

-- Sorts
--------

msgS      = F.Sort "Msg"
freshS    = F.Sort "Fresh"
tidS      = F.Sort "TID"
varS      = F.Sort "Var"
eventS    = F.Sort "Event"
rolestepS = F.Sort "RoleStep"
roleS     = F.Sort "Role"

theSorts = [msgS, freshS, tidS, varS, eventS, rolestepS, roleS]

-- Functions
------------


substF = F.Fun (F.Id "s", msgS) [varS, tidS]
invF   = F.Fun (F.Id "inv", msgS) [msgS]

localF  = F.Fun (F.Id "new",    msgS) [freshS, tidS]
tupF    = F.Fun (F.Id "tup",    msgS) [msgS, msgS]
encF    = F.Fun (F.Id "enc",    msgS) [msgS, msgS]
symKF   = F.Fun (F.Id "k",   msgS) [msgS, msgS]
hashF   = F.Fun (F.Id "hash",   msgS) [msgS]
asymPKF = F.Fun (F.Id "pk", msgS) [msgS]
asymSKF = F.Fun (F.Id "sk", msgS) [msgS]

learnF = F.Fun (F.Id "ln", eventS) [msgS]
stepF  = F.Fun (F.Id "st", eventS) [tidS, rolestepS]

runsF  = F.Fun (F.Id "runs", roleS) [tidS]

theFuns = [substF, invF, runsF] ++ msgCo ++ stepCo

msgCo    = [localF, tupF, encF, symKF, hashF, asymPKF, asymSKF]
symKeyCo = [localF, tupF, encF, symKF, hashF]
stepCo   = [learnF, stepF]

invAp = F.apply invF . return
asymPKAp = F.apply asymPKF . return
asymSKAp = F.apply asymSKF . return
substAp v tid = F.apply substF [v,tid]

-- Relations
------------

knowsR, beforeR :: F.Rel
knowsR  = F.Rel (F.Id "knows")  [msgS]
stepsR  = F.Rel (F.Id "steps")  [tidS, rolestepS]
beforeR = F.Rel (F.Id "prec") [eventS, eventS]
ik0R    = F.Rel (F.Id "ik0")    [msgS]
agentR  = F.Rel (F.Id "agent")  [msgS]
comprR  = F.Rel (F.Id "compr")  [msgS]

theRels = [knowsR, stepsR, beforeR, ik0R, agentR, comprR]



inKnows :: F.Term -> F.Formula
inKnows = F.inRel knowsR . return

inSteps :: TID -> F.Term -> F.Formula
inSteps tid step = F.inRel stepsR [tidVar tid, step]

(.<.) x y = F.In beforeR [x,y]

runsRole :: TID -> F.Term -> F.Formula
runsRole tid role = F.eq (F.apply runsF [tidVar tid]) role

inIK0 :: F.Term -> F.Formula
inIK0 = F.inRel ik0R . return

inCompr :: F.Term -> F.Formula
inCompr = F.inRel comprR . return

agentName :: F.Term -> F.Formula
agentName = F.inRel agentR . return

-- Encoder
----------

data EncoderState = EncoderState {
    esIds      :: S.Set String
  , esConst    :: M.Map Id F.Fun
  , esFresh    :: M.Map Id F.Fun
  , esAVar     :: M.Map Id F.Fun
  , esMVar     :: M.Map Id F.Fun
  , esRoleStep :: M.Map RoleStep F.Fun
  , esRole     :: M.Map Role F.Fun
  }
  deriving(Eq, Ord, Show)

type Encoder = State EncoderState

-- | Aquire the next free identifier with the given prefix. The
-- sequence of prefix_id<n> for n = eps, 1, 2, ... is tested.
aquireId :: String -> Id -> Encoder F.Id
aquireId prefix = aquire modifiers . addPrefix . getId
  where 
  addPrefix = ((prefix++"_") ++)
  modifiers = id : map (flip (++) . show) [1..]
  aquire (mod:mods) i0 = do
     s <- get
     let i = mod i0
     if i `S.member` esIds s
       then aquire mods i
       else do
         put (s {esIds = S.insert i (esIds s)})
         return (F.Id i)
       

    

-- | Get the sorted id corresponding to a thread identifier.
tidSid :: TID -> F.SortedId
tidSid 0   = (F.Id   "I",                      tidS)
tidSid tid = (F.Id $ "I" ++ show (getTID tid), tidS)

-- | Encode a thread identifier variable.
tidVar :: TID -> F.Term
tidVar = F.Var . tidSid

-- | Encode an universal quantification over a thread identifier.
allTID :: TID -> F.Formula -> F.Formula
allTID = F.univ . tidSid

-- | Encode an existential quantification over a thread identifier.
exTID :: TID -> F.Formula -> F.Formula
exTID = F.ex . tidSid

-- | Encode a constant as a first-order constant and register the conversion in
-- the encoder state.
encFOConst :: Ord a => Accessor EncoderState (M.Map a F.Fun) -> (a -> Id) ->
              F.Sort -> String -> a -> Encoder F.Fun
encFOConst (getter, setter) extract sort prefix c = do
  s <- get
  case M.lookup c (getter s) of
    Just c' -> return c'
    Nothing -> do
      i <- aquireId prefix (extract c)
      let c' = F.Fun (i, sort) []
      put (setter (M.insert c c' (getter s)) s)
      return c'

-- | Encode a symbolically instantiated agent variable.
encAVar :: LocalId -> Encoder F.Term
encAVar (LocalId (v, tid)) = do
  v' <- F.const <$> encFOConst (esAVar, \m s -> s {esAVar = m}) id varS "av" v
  return $ substAp v' (tidVar tid)

-- | Encode a symbolically instantiated message variable.
encMVar :: LocalId -> Encoder F.Term
encMVar (LocalId (v, tid)) = do
  v' <- F.const <$> encFOConst (esMVar, \m s -> s {esMVar = m}) id varS "mv" v
  return $ substAp v' (tidVar tid)


-- | Encode a symbolically instantiated message.
encMsg :: Message -> Encoder F.Term
encMsg (MConst c) = 
  F.const <$> encFOConst (esConst, \m s -> s {esConst = m}) id msgS "c" c
encMsg (MFresh (LocalId (f, tid))) = do
  f' <- F.const <$> encFOConst (esFresh, \m s -> s {esFresh = m}) id freshS "f" f
  return $ F.apply localF [f', tidVar tid]
encMsg (MAVar av) = encAVar av
encMsg (MMVar mv) = encMVar mv

encMsg (MTup x y)  = F.apply tupF  <$> sequenceA [encMsg x, encMsg y]
encMsg (MEnc m k)  = F.apply encF  <$> sequenceA [encMsg m, encMsg k]
encMsg (MSymK a b) = F.apply symKF <$> sequenceA [encMsg a, encMsg b]

encMsg (MHash x)   = F.apply hashF   <$> sequenceA [encMsg x]
encMsg (MAsymPK x) = F.apply asymPKF <$> sequenceA [encMsg x]
encMsg (MAsymSK x) = F.apply asymSKF <$> sequenceA [encMsg x]
encMsg (MInvKey x) = F.apply invF    <$> sequenceA [encMsg x]

encRoleStep :: Maybe Role -> RoleStep -> Encoder F.Term
encRoleStep role s = do
  let name = Id . ((maybe "" roleName role ++ "_") ++) . stepLabel
  s' <- encFOConst (esRoleStep, \x s -> s {esRoleStep = x}) name rolestepS "rs" s
  return $ F.const s'


-- | Encode an event
encEvent :: (TID -> Maybe Role) -> Event -> Encoder F.Term
encEvent _ (Learn m) = F.apply learnF <$> sequenceA [encMsg m]
encEvent role (Step tid s) = do
  s' <- encRoleStep (role tid) s
  return $ F.apply stepF [tidVar tid, s']

encRole :: Role -> Encoder F.Term
encRole role =
  F.const <$> encFOConst (esRole, \x s -> s {esRole = x}) (Id . roleName) roleS "r" role

showRoleStep :: RoleStep -> String
showRoleStep = renderStyle (style {mode = OneLineMode}) . sptRoleStep

inputAxiom :: Role -> RoleStep -> Encoder (Maybe (Article F.Formula))
inputAxiom role (Send _ _) = return Nothing
inputAxiom role s@(Recv l pt) = do
  let tid = 0
      mkArticle = flip appendMath . Article . return . Text . concat $
        ["Input rule for step '", showRoleStep s, "' of role '", roleName role, "'"]
  s' <- encRoleStep (Just role) s
  step' <- encEvent (const $ Just role) (Step tid s)
  m' <- encMsg (inst tid pt)
  return . Just . mkArticle . allTID tid $ (inSteps tid s') F..==> (m' .<. step')

roleOrdAxiom :: Role -> (RoleStep, RoleStep) -> Encoder (Article F.Formula)
roleOrdAxiom role (s1, s2) = do
  let tid = 0
      encEv = encEvent (const $ Just role) . Step tid
      mkArticle = flip appendMath . Article . return . Text . concat $
        [ "In role '", roleName role, "' step '", showRoleStep s1
        , "' happens before step '", showRoleStep s2, "'"]
  s2' <- encRoleStep (Just role) s2
  step1' <- encEv s1
  step2' <- encEv s2
  role'  <- encRole role
  return . mkArticle . allTID tid $ 
    (runsRole tid role' F..&& inSteps tid s2') F..==> (step1' .<. step2')

roleAxioms :: Role -> Encoder (Article F.Formula)
roleAxioms role = do
  let steps = roleSteps role
  input <- catMaybes <$> mapM (inputAxiom role) steps
  ords  <- case steps of
    [] -> return []
    _  -> mapM (roleOrdAxiom role) (zip steps (tail steps))
  return . subArticle ("Role '"++roleName role++"'") . mconcat $ input ++ ords

-- | Generate a variable with the given name and sort: once as a sorted
-- identifier and once as the corresponding variable term.
--
-- NOTE: This currently not protected in any way; i.e. name clashes must be
-- avoided by choosing the right input.
sortedVar :: F.Sort -> String -> (F.SortedId, F.Term)
sortedVar sort v = let si = (F.Id v, sort) in (si, F.Var si)

-- | Generate a message variable with the given name: once as a sorted
-- identifier and once as the corresponding variable term.
--
-- NOTE: This currently not protected in any way; i.e. name clashes must be
-- avoided by choosing the right input.
msgVar :: String -> (F.SortedId, F.Term)
msgVar = sortedVar msgS

atomicChainAxioms :: Protocol -> Encoder (Article F.Formula)
atomicChainAxioms proto = do
  -- F.univ mv <$> genChainAxiom proto (m, True, const True)
  formulas <- sequenceA 
    [ encQuant <$> genChainAxiom proto (enc, False, isEnc)
    , hashQuant <$> genChainAxiom proto (hash, False, isHash)
    , symQuant <$> genChainAxiom proto (sym, True, isSym)
    , asymQuant <$> genChainAxiom proto (asym, True, isAsym)
    , nonceQuant <$> genChainAxiom proto (nonce, False, isNonce)
    ]
  return . subArticle "Spezialized instances of the decryption chain rule" .
    mconcat . zipWith addComment formulas $
      [ "encryptions"
      , "hashes"
      , "symmetric long-term keys"
      , "asymmetric long-term keys"
      , "nonces"
      ]
  where
  addComment f info = 
    Article [Text $ "Chain rule for " ++ info ++ ".", Math f]

  (av, a) = msgVar "A0"
  (bv, b) = msgVar "B0"
  (mv, m) = msgVar "M0"
  (kv, k) = msgVar "K0"
  (nv, n) = sortedVar freshS "N0"
  (tidv, tid) = sortedVar tidS "I0"

  (encQuant, enc) = (F.univ mv . F.univ kv, F.apply encF [m,k])
  isEnc (MEnc _ _) = True
  isEnc _          = False

  (hashQuant, hash) = (F.univ mv, F.apply hashF [m])
  isHash (MHash _) = True
  isHash _         = False

  (nonceQuant, nonce) = (F.univ nv . F.univ tidv, F.apply localF [n,tid])
  isNonce (MFresh _) = True
  isNonce (MMVar _)  = True
  isNonce _          = False

  (symQuant, sym) = (F.univ av . F.univ bv, F.apply symKF [a,b])
  isSym (MSymK _ _) = True
  isSym _           = False

  (asymQuant, asym) = (F.univ av, F.apply asymSKF [a])
  isAsym (MAsymSK _) = True
  isAsym _           = False


-- | Build a final disjunction by evaluationg the ListT transformed monadic
-- computation of a formula.
--
-- TODO: Move
finalDisjM :: Monad m => ListT m F.Formula -> m F.Formula
finalDisjM = liftM F.disj . runListT

-- | Build an intermediate disjunction by evaluationg the ListT transformed
-- monadic computation of a formula and returning it as a single disjunctive
-- formula.
--
-- TODO: Move
interDisjM :: Monad m => ListT m F.Formula -> ListT m F.Formula
interDisjM f = do
  formulas <- lift $ runListT f
  case formulas of
    [] -> mzero
    _  -> return $ F.disj formulas

genChainAxiom :: Protocol -> (F.Term, Bool, Message -> Bool) -> Encoder F.Formula
genChainAxiom proto (m, maybeInIK0, approxEq) = do
  cases <- finalDisjM $ msum [ik0, hash, enc, tup, send]
  return (inKnows m F..==> cases)
  where
  (xv, x) = msgVar "X"
  (kv, k) = msgVar "K"
  (yv, y) = msgVar "Y"

  ik0 = guard maybeInIK0 *> pure (inIK0 m)

  hash = do
    guard (approxEq (MHash err)) 
    return $ F.ex xv $ F.conj [F.eq m h, x .<. h]
    where
    err = error $ "chainAxiom: fake hash - unknown inner structure"
    h = F.apply hashF [x]

  enc = do
    guard (approxEq (MEnc err err))
    return $ F.ex xv $ F.ex kv $ F.conj [F.eq m e, x .<. e, k .<. e]
    where
    err = error $ "chainAxiom: fake enc - unknown inner structure"
    e = F.apply encF [x,k]

  tup = do
    guard (approxEq (MTup err err))
    return $ F.ex xv $ F.ex yv $ F.conj [F.eq m t, x .<. t, y .<. t]
    where
    err = error $ "chainAxiom: fake tup - unknown inner structure"
    t = F.apply tupF [x,y]

  send = msum . map roleChains $ protoRoles proto
    where
    roleChains role = 
      msum . map stepChains $ roleSteps role
      where
      stepChains      (Recv _ _)  = mzero
      stepChains step@(Send l pt) = do
        let tid = 0
        role' <- lift $ encRole role
        step' <- lift $ encEvent (const $ Just role) (Step tid step)
        chain <- interDisjM $ msgChains [step'] (inst tid pt)
        return . exTID tid $
          runsRole tid role' F..&& chain
        where
        msgChains :: [F.Term] -> Message -> 
                     ListT (StateT EncoderState Identity) F.Formula
        msgChains from msg = 
          do guard (approxEq msg)
             msg' <- lift $ encMsg msg
             return . F.conj $ (map (.<. msg') from) ++ [msg' F..== m]
          `mplus`
          case msg of
            MTup x y ->
              interDisjM $ msgChains from x `mplus` msgChains from y
            MEnc x k -> do
              msg'  <- lift $ encMsg msg
              invk' <- lift $ encMsg (normMsg (MInvKey k))
              innerchain <- interDisjM $ msgChains [msg', invk'] x
              return . F.conj $ (map (.<. msg') from) ++ [innerchain]
            _       -> mzero

protocolAxioms :: Protocol -> Encoder (Article F.Formula)
protocolAxioms proto = do
  roleAxs <- mconcat <$> mapM roleAxioms (protoRoles proto)
  chains <- atomicChainAxioms proto
  let header = "Axiomatization of protocol '"++protoName proto++"'"
  return . subArticle header $ roleAxs `mappend` chains
  
-- | Encode a set of equalities.
encEqualities :: Equalities -> Encoder [F.Formula]
encEqualities (Equalities tideqs roleqs avareqs mvareqs agnteqs) =
  concat <$> sequenceA
    [ conv encTIDEq tideqs
    , mapM encRoleEq [(k, v) | (k, Just v) <- M.toList roleqs]
    , conv encAVarEq avareqs 
    , conv encMVarEq mvareqs
    , conv encAgntEq agnteqs
    ]
  where
  conv :: ((k,v) -> Encoder a) -> M.Map k v -> Encoder [a]
  conv f = mapM f . M.toList
  encTIDEq (tid1, tid2) = return $ tidVar tid1 F..== tidVar tid2
  encRoleEq (tid, role) = runsRole tid <$> encRole role
  encAVarEq (v1, v2) = (F..==) <$> encAVar v1 <*> encAVar v2
  encMVarEq (v, m)   = (F..==) <$> encMVar v  <*> encMsg m
  encAgntEq _ = error "encEqualities: implement agent equalities encoder"


-- | Encode a set of facts.
encFacts :: Facts -> Encoder F.Formula
encFacts (Facts evs evord co uc eqs) = do
  F.conj . concat <$> sequenceA
    [ encEqualities eqs
    , conv encEv evs
    , conv encEvOrd evord
    , conv encCo co
    , conv encUc uc
    ]
  where
  conv :: (a -> Encoder b) -> S.Set a -> Encoder [b]
  conv f = mapM f . S.toList

  findRole = (`threadRole` roleEqs eqs)

  encEv (Learn m) = inKnows <$> encMsg m
  encEv (Step tid s) = inSteps tid <$> encRoleStep (findRole tid) s
  encEvOrd (e1,e2) = (.<.) <$> encEvent findRole e1 <*> encEvent findRole e2
  encCo av =         inCompr <$> encAVar av
  encUc av = F.neg . inCompr <$> encAVar av

-- | TODO: Make translation errors bubble up to the user instead of silently
-- ignoring them.
encFormula :: Formula -> Encoder [F.Formula]
encFormula FFalse         = return [F.Bot]
encFormula (FFacts facts) = return <$> encFacts facts
encFormula _              = return []

-- | Encode a sequent.
encSequent :: Sequent -> Encoder [F.Formula]
encSequent se = do
  prems' <- encFormula $ sePrem se
  concls' <- encFormula $ seConcl se
  let quantTids f quant body = foldr quant body tids
        where
        tids = maybe [] (M.keys . roleEqs . equalities) $ formulaFacts f
      premQuant = quantTids (sePrem se) allTID
      conclQuant = quantTids (seConcl se) exTID
  return [ premQuant $ prem' F..==> conclQuant concl'
         | prem' <- prems', concl' <- concls' ]


-- | TODO: Move
mathArticle :: a -> Article a
mathArticle = Article . return . Math

-- | TODO: Move
textArticle :: String -> Article a
textArticle = Article . return . Text

-- | The axioms underlying the model.
modelAxioms :: Article F.Formula
modelAxioms = 
  mconcat . map (uncurry subArticle) $ 
    [ ("Initial intruder knowledge", ik0)
    , ("Event order", evord)
    , ("Splitting tuples", unpair)
    , ("Agent names", agent)
    , ("Free event constructors", eventConstrs)
    , ("Key inversion", invkey)
    ]
  where
  -- convert a list of commented math to an article
  commentedMath :: [(String,a)] -> Article a
  commentedMath = mconcat . map (uncurry mappend . (textArticle *** mathArticle))

  eventConstrs = 
    mconcat . map mathArticle $ F.freeAlgebra [learnF, stepF]

  ik0 = mconcat . map mathArticle $
    [ kquant  $ inIK0 k F..==> F.disj [inCompr ka, inCompr kb]
    , skquant $ inIK0 sk F..==> inCompr ska
    ]
    where
    (kquant,  k,  [ka, kb]) = F.allArguments "X" symKF
    (skquant, sk, [ska])    = F.allArguments "X" asymSKF

  evord = commentedMath
    [ ( "irreflexivity"
      , F.univ e0v $ F.neg $ e0 .<. e0)
    , ( "transitivity"
      , foldr F.univ (e0 .<. e1 F..&& e1 .<. e2 F..==> e0 .<. e2) [e0v, e1v, e2v])
    , ( "step before: executed"
      , foldr F.univ (step .<. e0 F..==> inSteps tid0 rs) [tidv, rsv, e0v])
    , ( "knows before: known"
      , foldr F.univ (learned .<. e0 F..==> inKnows m) [mv, e0v])
    ]
    where
    (e0v, e0) = sortedVar eventS "E0"
    (e1v, e1) = sortedVar eventS "E1"
    (e2v, e2) = sortedVar eventS "E2"
    tid0 = 0
    (tidv, tid) = (tidSid tid0, tidVar tid0)
    (rsv, rs)   = sortedVar rolestepS "RS"
    step = F.apply stepF [tid,rs]
    (mv, m) = msgVar "M"
    learned = F.apply learnF [m]

  unpair = mconcat . map mathArticle $
    [ foldr F.univ (learn tup .<. e F..==> learn x .<. e) [xv, yv, ev]
    , foldr F.univ (learn tup .<. e F..==> learn y .<. e) [xv, yv, ev]
    , foldr F.univ (inKnows tup F..==> inKnows y) [xv, yv, ev]
    , foldr F.univ (inKnows tup F..==> inKnows x) [xv, yv, ev]
    ]
    where
    (ev, e) = sortedVar eventS "E"
    (xv, x) = msgVar "X"
    (yv, y) = msgVar "Y"
    tup = F.apply tupF [x,y]
    learn = F.apply learnF . return

  agent = mconcat . map mathArticle $
    (F.univ xv (inCompr x F..==> agentName x)) :
    map notAnAgent [ tupF, encF, symKF, hashF, asymPKF, asymSKF]
    where
    (xv, x) = msgVar "X"

  invkey = mconcat . map mathArticle $
    [ F.univ av $ F.eq (invAp pk) sk
    , F.univ av $ F.eq (invAp sk) pk
    ] ++
    map symkey symKeyCo
    -- ++
    -- [ F.univ av $ agentName a F..==> invAp a F..== a ]
    ++
    [ F.univ xv . F.univ av $ (invAp x F..== pk) F..==> x F..== sk 
    , F.univ xv . F.univ av $ (invAp x F..== sk) F..==> x F..== pk 
    ] ++
    map invsymkey symKeyCo
    ++
    [ F.univ xv . F.univ yv $ invAp x F..== invAp y F..==> x F..== y]
    where
    (av, a) = msgVar "A"
    (xv, x) = msgVar "X"
    (yv, y) = msgVar "Y"
    pk = asymPKAp a
    sk = asymSKAp a
    symkey f = quant $ invAp f' F..== f'
      where
      (quant, f', _) = F.allArguments "X" f
    invsymkey f = F.univ xv . quant $ invAp x F..== f' F..==> x F..== f'
      where
      (quant, f', _) = F.allArguments "Y" f

-- | The formula that the given function will never result in an agent name.
notAnAgent :: F.Fun -> F.Formula
notAnAgent f = quant $ F.neg $ agentName f'
  where
  (quant, f', _) = F.allArguments "X" f

freeAlgebra = mconcat . map mathArticle . F.freeAlgebra

encodingAxioms :: EncoderState -> Article F.Formula
encodingAxioms state =
  mconcat . map (uncurry subArticle) $ 
    [ ("Free message algebra", msgAlg)
    , ("Global constants", consts)
    , ("Agent variables", avars)
    -- , ("Variable Identifiers", varids)
    , ("Fresh message identifiers", freshids)
    , ("Rolestep identifiers", rolestepids)
    , ("Role identifiers", roleids)
    ]
  where
  msgAlg      = freeAlgebra $ M.elems (esConst state) ++ msgCo
  freshids    = freeAlgebra $ M.elems (esFresh state)
  varids      = freeAlgebra $ M.elems (esAVar state) ++ M.elems (esMVar state)
  rolestepids = freeAlgebra $ M.elems (esRoleStep state)
  roleids     = freeAlgebra $ M.elems (esRole state)
  consts = 
    mconcat . map (mathArticle . F.neg . agentName . F.const) $ 
      M.elems (esConst state)
  avars = 
    mconcat . map (mathArticle . agent) $ M.elems (esAVar state)
    where
    tid = 0
    agent av = allTID tid . agentName $ F.apply substF [F.const av, tidVar tid]


runEncoder :: Encoder a -> (a, EncoderState)
runEncoder m = runState m emptyEncoderState

emptyEncoderState :: EncoderState
emptyEncoderState = EncoderState S.empty M.empty M.empty M.empty M.empty M.empty M.empty

test = runEncoder $ encMsg (MTup (MFresh (LocalId (Id "ni", TID 1))) (MConst (Id "1")))

-- | Encode a security protocol theory into a list of axioms and a list of
-- formulas corresponding to the expected security properties.
encTheory :: Theory -> (Signature, Article F.Formula, [Article F.Formula])
encTheory thy = 
  ( Signature 
      theSorts
      (theFuns ++ concatMap M.elems [esConst s, esFresh s, esAVar s, esMVar s]
               ++ M.elems (esRoleStep s) ++ M.elems (esRole s)
      )
      theRels
  , mconcat 
    [ subArticle "Model Axiomatization" modelAxioms 
    , mconcat protos
    , subArticle "Encoding Axiomatization" (encodingAxioms s)
    ]
  , properties )
  where
  (protos, properties) = partitionEithers fs
  (fs, s) = runEncoder (mapM encThyItem $ thyItems thy)
  encThyItem (ThyProtocol proto) =
    Left <$> protocolAxioms proto
  encThyItem (ThySequent name se) = do
    se' <- F.conj <$> encSequent se
    return . Right . Article $
      [ Text $ "Sequent '"++name++"'"
      , Math se' 
      ]
  encThyItem (ThyTheorem _) = 
    return $ Left mempty

prettyFOLTheory :: Theory -> Doc
prettyFOLTheory thy =
  vcat . map ppContent . getArticle $ theory
  where
  (_, axioms, props) = encTheory thy
  theory = 
    subArticle "Axiomatization" axioms `mappend`
    subArticle "Properties" (mconcat props)
  ppContent :: Sectioned F.Formula -> Doc
  ppContent (Math a) = F.ppFormula a $-$ text ""
  ppContent (Text t) = text $ "% " ++ t
  ppContent (Section i header) = 
    (case i of
       0 -> emptyLines 1 $-$ 
            (linesToDoc . overline "%". underline "%" $ "%% " ++ header ++ " %%")
       1 -> emptyLines 1 $-$ 
            (linesToDoc . overline "%". underline "%" $ "% " ++ header)
       2 -> (linesToDoc . underline "%" $ "% " ++ header)
       _ -> text $ "% " ++ header)
    $-$ emptyLines 1


toTPTP :: Theory -> Problem
toTPTP thy = 
  Problem (thyName thy) desc sign 
    (labelMath axLbls axioms) 
    (mathArticle . ((,) "properties") . F.conj . getMath $ mconcat conjectures)
  where
  desc = Description 
    "scytherP - FOL backend" 
    "auto-generated security protocol verification problem" 
    Satisfiable
  (sign, axioms, conjectures) = encTheory thy
  axLbls = map (("ax"++) . show) [1..]
  coLbls = map (("co"++) . show) [1..]

labelMath :: [b] -> Article a -> Article (b,a)
labelMath labels = 
  Article . (`evalState` labels) . mapM label . getArticle
  where
  label (Math a) = do
    l:ls <- get
    put ls
    return (Math (l,a))
  label (Text t)           = return $ Text t
  label (Section i header) = return $ Section i header


getMath :: Article a -> [a]
getMath a = [ x | Math x <- getArticle a ]


