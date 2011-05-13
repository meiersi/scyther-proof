-- | .dot file generation for elements of a security protocol theory.
module Scyther.Theory.Dot (
    dotSequentMarked
  , dotProtocol
  , graphvizDotToPng
) where

import Safe
import Data.Maybe
import Data.List (find)
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Color

import Control.Basics
import Control.Monad.State
import Control.Monad.Reader
import Control.Concurrent.Chan

import Text.Dot as Dot
import Text.Isar hiding (hcat)

import System.Process (waitForProcess, runCommand)

import qualified Scyther.Equalities as E
import Scyther.Facts
import Scyther.Sequent

-----------------------------------------------------------------------------
-- Utility Functions
-----------------------------------------------------------------------------

-- | Find a value in a map and display an error if it cannot be found.
findWithError :: Ord k => String -> k -> M.Map k v -> v
findWithError msg k = fromMaybe (error msg) . M.lookup k

-- | Find a value and display the key in case it cannot be found.
findShowError :: (Ord k, Show k) => k -> M.Map k v -> v
findShowError k = 
  findWithError ("findShowError: key '"++show k++"' not in map.") k

-- | The style of an edge between two nodes of the same thread.
threadEdgeStyle :: [(String, String)]
threadEdgeStyle = [("style","bold"),("weight","10.0")]

-- | Set default attributes for nodes and edges.
setDefaultAttributes :: Dot ()
setDefaultAttributes = do
  attribute ("nodesep","0.3")
  attribute ("ranksep","0.3")
  nodeAttributes [("fontsize","10"),("fontname","Helvetica"),("width","0.3"),("height","0.2")]
  edgeAttributes [("fontsize","10"),("fontname","Helvetica")]

-- | Find the color; default to the color for Nothing, if no color can be
-- found.
getColorWithDefault :: TID -> M.Map (Maybe TID) v -> v
getColorWithDefault tid m = M.findWithDefault (m M.! Nothing) (Just tid) m

-----------------------------------------------------------------------------
-- DOT Graph Generation
-----------------------------------------------------------------------------

-- Grouping different thread identifiers according to their role
----------------------------------------------------------------

type TIDMap = M.Map TID (Maybe Role)

extractTIDMap :: Sequent -> TIDMap
extractTIDMap se = formulaMap (seConcl se) (M.fromList fromPrem)
  where
  prem     = sePrem se
  fromPrem = [ (tid, threadRole tid prem) | tid <- quantifiedTIDs prem ]

  formulaMap :: Formula -> TIDMap -> TIDMap
  formulaMap formula = case formula of
    (FExists (Left tid)  prop)              -> formulaMap prop . M.insert tid Nothing
    (FExists (Right _ ) prop)               -> formulaMap prop
    (FConj lprop rprop)                     -> formulaMap lprop . formulaMap rprop
    (FAtom (AEq (E.TIDRoleEq (tid, role)))) -> M.insert tid (Just role)
    _                                       -> id


-- Color map
------------

type ColorMap = M.Map (Maybe TID) String

-- | A map from thread identifiers to strings identifying their color.
-- type ColorMap = M.Map SequentTID String

-- | A reserved thread identifier for the intruder
intruderTID :: TID
intruderTID = -1

-- | The hue of the intruder events
intruderHue :: Double
intruderHue = 18 / 360

-- | Generate a color map mapping every thread to it's specific color. The
-- intruder gets one color accessible under the thread identifier @intrSID@
threadColors :: Sequent -> ColorMap
threadColors se = M.fromList $ assocs
  where
  optRoles = (1, Nothing) : (zip [2..] . map Just . protoRoles $ seProto se)

  roleeqs               = M.toList $ extractTIDMap se
  threadsOfRole optRole = [ tid | (tid, optRole') <- roleeqs, optRole == optRole' ]

  tidGroupEqs :: [[(TID, (Int, Int))]]
  tidGroupEqs = 
    [(intruderTID, (0,0))] : 
    [  [ (tid, (roleIdx, tidIdx)) 
       | (tidIdx, tid) <- zip [0..] $ threadsOfRole optRole ]
    | (roleIdx, optRole) <- optRoles ]

  getColor idx = 
      maybe (error $ "color of " ++ show idx ++ " not found") snd $
      find ((idx ==) . fst) $ colors

  colors = colorGroups intruderHue (map length tidGroupEqs)

  assocs = (Nothing, "#eeeeee") :
    [ (Just tid, hsvToHex $ getColor idx) | (tid, idx) <- concat tidGroupEqs ]


-- Custom Monad for transporting the relevant information
---------------------------------------------------------

type NodeMap = M.Map Event NodeId

data DotEnv   = DotEnv {
    colorMap      :: ColorMap    -- ^ Assigns colors to threads
  , threadMapping :: E.Mapping   -- ^ Assigns threads to roles
  , marked        :: S.Set Event -- ^ Events to be marked
  }

data DotState = DotState {
    nodeMap     :: M.Map Event NodeId
    -- ^ Mapping events to Dot node-ids.
  , threadAtoms :: M.Map (Maybe TID) [Atom]
    -- ^ Gather the atoms that do not have their own graphical representation
    -- according to the thread they belong to.
  }

-- | Modify the node map of a state.
mapNodeMap :: (NodeMap -> NodeMap) -> DotState -> DotState
mapNodeMap f s = s { nodeMap = f (nodeMap s) }

-- | A custom dot monad.
type MyDot = ReaderT DotEnv (StateT DotState Dot)

runMyDot :: ColorMap -> E.Mapping -> S.Set Event -> MyDot a -> Dot a
runMyDot cm tm ma m = evalStateT (runReaderT m env0) s0
  where
  env0 = DotEnv { colorMap = cm, threadMapping = tm, marked = ma }
  s0   = DotState { nodeMap = M.empty, threadAtoms = M.empty }

-- | Lift a nullary operation to our custom dot monad.
liftDot :: Dot a -> MyDot a
liftDot = lift . lift

-- | Lift a unary operation to our custom dot monad.
liftDot1 :: (Dot (a, DotState) -> Dot (b, DotState)) -> (MyDot a -> MyDot b)
liftDot1 f m = ReaderT $ \env -> StateT $ \s -> 
  f (runStateT (runReaderT m env) s)

-- | A lifted version of the @cluster@ method for constructing a graph cluster.
myCluster :: MyDot a -> MyDot (NodeId, a)
myCluster = liftDot1 (liftM adapt . cluster)
  where adapt (nid, (x, s)) = ((nid, x), s)

-- | Ensure that the given event is dotted and return its node id.
dotEvent :: Event -> MyDot NodeId
dotEvent ev = do
  optId <- gets $ M.lookup ev . nodeMap
  case optId of
    Just nid -> return nid
    Nothing  -> do
      mapping <- asks threadMapping
      mark <- asks $ S.member ev . marked
      let peripheries | mark      = "2"
                      | otherwise = "1"
          label = render $ sptRawEvent mapping ev
          shape = case ev of
            Learn _  -> "ellipse"
            Step _ _ -> "box"
      color <- case ev of
        Learn _    -> asks $ getColorWithDefault intruderTID . colorMap
        Step tid _ -> asks $ getColorWithDefault tid         . colorMap
      nid <- liftDot $ node 
        [ ("label", label)
        , ("shape", shape)
        , ("style", "filled")
        , ("fillcolor", color)
        , ("peripheries", peripheries)
        ]
      modify . mapNodeMap $ M.insert ev nid
      return nid

-- | Produce the Dot code and the updated dot state for a single atom.
dotAtom :: Atom -> MyDot ()
dotAtom (AEv ev)                  = dotEvent ev >> return ()
dotAtom (AEvOrd evord@(from, to)) = do
  fromId <- dotEvent from
  toId   <- dotEvent to
  liftDot $ edge fromId toId edgestyle
  where
  edgestyle = case evord of
    (Step tid1 _, Step tid2 _) | tid1 == tid2 -> threadEdgeStyle
    _                                         -> []
dotAtom atom = addThreadAtom atom

-- | Reset the thread atoms to the given default thread/role information.
resetThreadAtoms :: [(Maybe TID, Maybe Role)] -> MyDot ()
resetThreadAtoms info = do
  s <- get
  put $ s { threadAtoms = M.fromList $ mapMaybe prepare info }
  where
  prepare (optTid, optRole) = do 
    role <- optRole
    tid  <- optTid
    return (optTid, [AEq (E.TIDRoleEq (tid, role))])

-- | Add to given atom to its associated thread.
addThreadAtom :: Atom -> MyDot ()
addThreadAtom atom = do
  s <- get
  let ins = M.insertWith (++) (headMay $ atomTIDs atom) [atom]
  put $ s { threadAtoms = ins $ threadAtoms s }

-- | Produce the graphical information describing the atoms that have been
-- added to some thread using @addThreadAtom@.
dotThreads :: Bool  -- ^ True iff the threads are quantified here.
           -> MyDot ()
dotThreads quantified = do
  threadInfo <- gets $ M.toList . threadAtoms
  mapM_ (uncurry (dotThread quantified)) threadInfo
  
-- | Produce the dot code to for a single thread described by the list of
-- atoms.
dotThread :: Bool                             -- ^ True iff the thread is quantified
          -> Maybe TID -> [Atom] -> MyDot ()
dotThread quantified optTid atoms = do
  mapping <- asks $ threadMapping
  let -- combine the thread info
      infoContent = filter (not.null)
        [ threadinfo
        , ppLidList "compromised: "   compr
        , ppLidList "uncompromised: " uncompr
        , ppAtomList avareqs
        , ppAtomList other
        ]
      optRole = headMay [ role | AEq (E.TIDRoleEq (_, role)) <- atoms ]
                `mplus` (do tid <- optTid
                            E.threadRole tid (E.getMappingEqs mapping))
      quantifier | quantified = "some"
                 | otherwise  = "thread"
      threadinfo = case (fmap show optTid, fmap roleName optRole) of
        (Nothing, Nothing)    -> ""
        (Nothing, Just role)  -> "running " ++ role
        (Just tid, Nothing)   -> quantifier ++ " " ++ tid
        (Just tid, Just role) -> quantifier ++ " " ++ tid ++ " running " ++ role

      compr    = [ a | ACompr a <- atoms ]
      uncompr  = [ a | AUncompr a <- atoms ]
      avareqs  = [ atom | atom@(AEq (E.AVarEq _)) <- atoms ]
      other = do
        atom <- atoms
        guard $ case atom of
          AEq eq   -> case eq of
            E.TIDRoleEq _ -> False
            E.RoleEq _    -> False
            E.TIDEq _     -> False
            E.AVarEq _    -> False
            _             -> True
          AEv _      -> False
          AEvOrd _   -> False
          ACompr _   -> False
          AUncompr _ -> False
          _          -> True
        return atom

      ppAtomList [] = mzero
      ppAtomList as = unlines $ map (render . sptAtom mapping) as

      ppLidList _      []   = mzero
      ppLidList prefix lids =
        render . (text prefix <->) . fsep . punctuate comma $ map sptMessage lids
  unless (null infoContent) $ do
    color <- asks $ maybe (M.! Nothing) getColorWithDefault optTid . colorMap
    -- create the record node
    info <- liftDot $ record_
      (Dot.vcat' infoContent)
      [ ("style",     "filled")
      , ("fillcolor", color   )
      ]
    -- add an edge between the thread info node and the first node of
    -- this role that is present in the graph
    evMap <- gets nodeMap
    fromMaybe (return ()) $ do
      tid  <- optTid
      role <- optRole
      let findStep step = M.lookup (Step tid step) evMap
      stepId <- msum . map findStep $ roleSteps role
      return $ liftDot $ edge info stepId threadEdgeStyle


-- | Produce the dot code of the facts.
dotFacts :: Facts -> MyDot ()
dotFacts facts = do
  resetThreadAtoms $ 
    map (\tid -> (Just tid, threadRole tid facts)) (quantifiedTIDs facts) 
  mapM_ dotAtom $ toAtoms facts
  dotThreads True

-- | Hide all information belonging to the given thread id during the execution
-- of the local action.
localThreadInfo :: TID -> Maybe Role -> MyDot a -> MyDot a
localThreadInfo tid optRole m = do
  s <- get
  -- execute local action with the new role assignment noted
  x <- local (tryNoteRole tid optRole) $ m
  -- restore thread atoms
  let optTid       = Just tid
      restoreAtoms = maybe (M.delete optTid) (M.insert optTid) 
                           (M.lookup optTid (threadAtoms s))
  modify $ \s' -> s' { threadAtoms = restoreAtoms $ threadAtoms s' }
  -- return the result
  return x

-- | Modify the thread to role assignment.
tryNoteRole :: TID -> Maybe Role -> DotEnv -> DotEnv
tryNoteRole _   Nothing     env = env
tryNoteRole tid (Just role) env = 
  env { threadMapping = E.addTIDRoleMapping tid role (threadMapping env) }

-- | Produce the dot code of the formula.
dotFormula :: Formula -> MyDot ()
dotFormula (FAtom atom) = dotAtom atom
dotFormula (FConj f1 f2) = dotFormula f1 >> dotFormula f2
dotFormula (FExists (Left tid) inner) = do
  localThreadInfo tid (findRole tid inner) $ do
    dotFormula inner
    optAtoms <- gets $ M.lookup (Just tid) . threadAtoms 
    maybe (return ()) (dotThread True (Just tid)) optAtoms 
dotFormula (FExists (Right aid) inner) = do
  _ <- liftDot $ node [("label", "some agent " ++ show aid)]
  dotFormula inner

-- | Produce the dot code for a formula that is a conclusion of a sequent. This
-- takes care of handling the quantifiers stemming from the premises.
dotConclusion :: Formula -> MyDot ()
dotConclusion formula = do
  resetThreadAtoms []
  dotFormula formula
  dotThreads False

-- | Dot a sequent with two separate clusters for premise and conclusion.
dotSequent :: Sequent -> MyDot ()
dotSequent se = do
  s <- get
  liftDot setDefaultAttributes
  _ <- myCluster $ do
    liftDot $ attribute ("label","premise")
    dotFacts $ sePrem se
  -- restore state before premise dotting because premise and conclusion should
  -- not share nodes
  put s 
  _ <- myCluster $ do
    liftDot $ attribute ("label","conclusion")
    dotConclusion $ seConcl se
  return ()

-- | Dot a sequent with some marked events.
dotSequentMarked :: S.Set Event -> Sequent -> Dot ()
dotSequentMarked markedEvs se = 
  runMyDot (threadColors se) (eqsToMapping $ sePrem se) markedEvs $ dotSequent se

-- | Convert a protocol to a dot graph.
dotProtocol :: Protocol -> Dot ()
dotProtocol proto = do
  return ()
  setDefaultAttributes
  ids <- mapM dotStep steps
  let stepMap = M.fromList $ zip steps ids
  mapM_ (dotSend stepMap) steps
  mapM_ (dotRole stepMap) roles
  where
  roles = protoRoles proto
  steps = concatMap extractSteps roles
  extractSteps role = zip (repeat $ roleName role) (roleSteps role)

  rMap = M.fromList $ zip (map roleName roles) [2..]
  cMap = colorGroups intruderHue (replicate (length roles + 2) 1)
  getColor gIdx eIdx = 
     maybe (error "color not found") snd $ find (((gIdx, eIdx) == ) . fst) cMap
  getRoleColor role = hsvToHex $ getColor (findShowError role rMap) 0

  mkNode label color attrs = node $ [
        ("label",label)
      , ("shape","box")
      , ("style","filled")
      , ("fillcolor",color)
      ] ++ attrs

  dotStep (role, step) = 
    mkNode (render $ sptRoleStep Nothing step) (getRoleColor role) []

  dotSend _            (_, Recv _ _) = return ()
  dotSend stepMap send@(_, Send l _) = sequence_
    [ edge (findShowError send stepMap) (findShowError recv stepMap) []
    | recv@(_, Recv l' _) <- steps, l == l' ]

  dotRole stepMap role = do
    roleId <- mkNode ("role "++roleName role) (getRoleColor $ roleName role) [("peripheries","2")]
    let getStepId = (`findShowError` stepMap) . ((,) (roleName role))
        ids = roleId : map getStepId (roleSteps role)
        mkEdge (from, to) = edge from to threadEdgeStyle
    mapM_ mkEdge (zip ids (tail ids))
    

------------------------------------------------------------------------------
-- Calling Graphviz' dot tool
------------------------------------------------------------------------------

-- | Convert a .dot file to a .png file using the dot tool.
graphvizDotToPng :: FilePath    -- ^ Path to dot tool.
                 -> FilePath    -- ^ Dot file to convert
                 -> FilePath    -- ^ Png file to output
                 -> Chan String -- ^ Message channel
                 -> IO ()
graphvizDotToPng dotTool dotFile pngFile msgChan = do
  let cmd = dotTool ++ " -Tpng -o " ++ pngFile ++ " " ++ dotFile
  writeChan msgChan cmd
  hProc <- runCommand cmd 
  _ <- waitForProcess hProc
  return ()
