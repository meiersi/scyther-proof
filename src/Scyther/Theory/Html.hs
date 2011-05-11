{-# LANGUAGE GeneralizedNewtypeDeriving, MultiParamTypeClasses #-}

-- remove the two warnings from tagsoup
{-# OPTIONS_GHC -fno-warn-warnings-deprecations #-}

-- | Converting security protocol theories to a bunch of HTML files and images.
module Scyther.Theory.Html (
    GenerationInput(..)
  , theoryToHtml
  , evalHtmlMarkup
) where

import Data.Char
import Data.Maybe
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Time.Clock
import Data.Time.Format ()
import Data.Traversable (sequenceA)

import Control.Basics
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Label
import Control.Concurrent.ManagedThreads

import Text.Isar
import Text.Dot
import Text.HTML.TagSoup
import Text.JSON

import System.IO
import System.Directory
import System.FilePath
import System.Timing

import Extension.Prelude

import Scyther.Protocol
import Scyther.Sequent
import Scyther.Theory
import Scyther.Theory.Dot
import Scyther.Theory.Pretty


-- | Converts an indented string to the corresponding Html element.
indentedToHtmlString :: String -> String
indentedToHtmlString = unlines . map (addBreak . indent) . lines
  where
  addBreak  = (++"<br />")
  indent = uncurry (++) . (concatMap (const "&nbsp;") *** escapeText) . span isSpace
  escapeText = renderTags . parseTags

------------------------------------------------------------------------------
-- Html file generation
------------------------------------------------------------------------------

-- | Input for generation process that needs to be supplied from a caller of
-- @theoryToHtml@.
data GenerationInput = GenerationInput {
    giHeader      :: String    -- ^ Arbitrary html for the header
  , giTime        :: UTCTime   -- ^ Generation time.
  , giSystem      :: String    -- ^ Description of the system we run on.
  , giInputFile   :: FilePath  -- ^ Path to input file.
  , giTemplate    :: FilePath  -- ^ Path to template index.
  , giOutDir      :: FilePath  -- ^ Path to the output directory.
  , giMarkup      :: HtmlMarkup Doc -- ^ Document representing theory to output.
  , giProofScript :: FilePath -> String    
                               -- ^ A function mapping the output file name to a
                               --   string representation of Isabelle/HOL
                               --   certificate. The generation time will be
                               --   measured as the time it takes to write
                               --   this string to the output file.
  , giCmdLine     :: String    -- ^ The command line that was used in this call to
                               --   scyther-proof.
  , giIsabelle    :: Maybe (FilePath -> IO (IO String, Maybe String))
                               -- ^ A checking function calling isabelle with
                               -- the right parameters and returning an IO function
                               -- for retrieving the logfile contents and an error
                               -- message in case the check didn't succeed.
  }

-- | Information about various paths relevant for generating the HTML output.
data PathInfo = PathInfo {
    inputFileCopy   :: FilePath  -- ^ Path of input file copy.
  , proofScriptFile :: FilePath  -- ^ Path of generated Isabelle proof script.
  , logFileCopy     :: FilePath  -- ^ Path of the copy of the logFile
  , outDir          :: FilePath  -- ^ Output directory.
  , imageDir        :: FilePath  -- ^ Relative directory for graphs.
  , filesDir        :: FilePath  -- ^ Relative directory for input and output files.
  }

-- | Compute the path info from the generation input.
pathInfo :: GenerationInput -> PathInfo
pathInfo input = info
  where
    info = PathInfo
      { inputFileCopy   = filesDir info </> takeFileName (giInputFile input)
      , proofScriptFile = filesDir info </> 
          addExtension (takeBaseName (giInputFile input) ++ "_cert_auto") "thy"
      , logFileCopy     = filesDir info </> "logfile"
      , outDir          = giOutDir input
      , imageDir        = "img"
      , filesDir        = "files"
      }


-- | Make a path that is specified relative to the output directory absolute.
mkAbsolute :: PathInfo -> FilePath -> FilePath
mkAbsolute info = (outDir info </>)

-- | Compute the list of absolute paths to directories required for generating
-- this HTML output.
requiredDirs :: PathInfo -> [FilePath]
requiredDirs info = map (mkAbsolute info) [".", imageDir info, filesDir info]

-- | Prepare information gathered during the generation of the resulting
-- theories for exporting as JSON.
jsGenerationInfo :: GenerationInput
                 -> NominalDiffTime  -- ^ Proof script generation time.
                 -> Maybe (Bool, NominalDiffTime, FilePath) 
                                     -- ^ Proof checking time and relative logfile path.
                 -> JSObject JSValue
jsGenerationInfo input genTime optCheckInfo = toJSObject $
    [ ("header",      showJSON . toJSString $ giHeader input)
    , ("time",        showJSON . toJSString . show $ giTime input)
    , ("system",      showJSON . toJSString $ giSystem input)
    , ("inputFile",   showJSON . fileLink   $ inputFileCopy paths)
    , ("proofScript", showJSON . fileLink   $ proofScriptFile paths)
    , ("commandLine", showJSON . toJSString $ giCmdLine input)
    ] ++
    checkInfo optCheckInfo
  where
    paths = pathInfo input
    fileLink file = (toJSString (takeFileName file), toJSString file)
    genTimeString = "generated in " ++ show genTime

    checkInfo Nothing                              = 
        [ ("certificateStatus", showJSON . toJSString $ genTimeString) ]
    checkInfo (Just (success, checkTime, logFile)) =
        [ ( "certificateStatus", showJSON . toJSString $ genTimeString ++ status)
        , ( "logFile", showJSON (toJSString "logfile", toJSString logFile))
        ]
      where
        status | success   = ", successfully checked in " ++ show checkTime
               | otherwise = ", CHECK FAILED after " ++ show checkTime

-- | Convert a security protocol theory to a HTML file visualizing it.
theoryToHtml :: GenerationInput -> IO ()
theoryToHtml input = do
  putStrLn ""
  putStrLn $ " copying template to output directory: " ++ outDir paths
  mapM_ (createDirectoryIfMissing True) $ requiredDirs paths
  copyTemplate (giTemplate input) $ outDir paths
  copyFile (giInputFile input) (mkAbsolute paths $ inputFileCopy paths)
  -- timed proof script generation
  putStr " generating proof script: " >> hFlush stdout
  genTime <- timed_ $ writeAbsolute (proofScriptFile paths) 
                        (giProofScript input $ proofScriptFile paths)
  putStrLn $ show genTime
  -- timed isabelle check
  optCheckInfo <- case giIsabelle input of
    Nothing           -> return Nothing
    Just machineCheck -> do
      putStr " checking proof script: " >> hFlush stdout
      ((logFileContents, optErrMsg), checkTime) <- timed $ 
        machineCheck (mkAbsolute paths $ proofScriptFile paths)
      putStrLn $ show checkTime
      -- write log file copy
      contents <- logFileContents
      writeAbsolute (logFileCopy paths) contents
      return $ Just (isNothing optErrMsg, checkTime, logFileCopy paths)
  -- json output
  let thyJSON = mkThyJSON (jsGenerationInfo input genTime optCheckInfo)
  writeAbsolute "theory.js"
    (("scytherP_theory_JSON = "++) . show $ showJSObject thyJSON "")
  -- graph generation
  putStrLn " generating visualizations using GraphViz:"
  parMkGraphs . sortOn snd $ M.toList graphs
  where
  paths = pathInfo input
  writeAbsolute = writeFile . mkAbsolute paths

  (ppThy, (st, graphs)) = runHtmlMarkup $ giMarkup input
  thyStr  = indentedToHtmlString (render ppThy)
  mkThyJSON :: JSObject JSValue -> JSObject JSValue
  mkThyJSON genInfo = toJSObject
    [ ("theory",         showJSON $ toJSString thyStr)
    , ("generationInfo", showJSON $ genInfo          )
    , ("theoremDefs",    showJSON $ htmlThmDefs   st )
    , ("theoremRefs",    showJSON $ htmlThmRefs   st )
    , ("cases",          showJSON $ htmlCases     st )
    , ("proofstates",    showJSON $ htmlGraphRefs st )
    , ("explanations",   showJSON $ swapKeyValue $ htmlExpls st)
    ]
  swapKeyValue m = M.fromList [(y, x) | (x, y) <- M.toList m]

  -- create the graph corresponding to the given formula
  mkGraph (dotStr,idx) msgChan = do
    let outFile = mkAbsolute paths (imageDir paths </> ("graph_" ++ show idx))
        dotFile = addExtension outFile "dot"
        pngFile = addExtension outFile "png"
    writeFile dotFile dotStr
    graphvizDotToPng dotFile pngFile msgChan
    removeFile dotFile

  -- | Convert a list of dot strings in parallel to png files, using the number of
  -- cores+1 parallel executions of the dot tool.
  parMkGraphs = parCmd_ display . map mkGraph
    where
    display n i msg = hPutStrLn stdout $ "  ["++showPadded i++" of "++show n++"] "++msg
      where showPadded x = flushRight (length (show n)) (show x)

-- | Copy all the files referenced in the template index file to the output
-- directory.
copyTemplate :: FilePath -- ^ Path of template index file.
             -> FilePath -- ^ Output directory.
             -> IO ()
copyTemplate templateFile targetDir = do
  let templateDir = takeDirectory templateFile
  template <- readFile templateFile
  let files = filter (not.null) $ lines template
      copy file = do
        let outPath = targetDir </> file
        createDirectoryIfMissing True (takeDirectory outPath)
        copyFile (templateDir </> file) outPath
  mapM_ copy files

------------------------------------------------------------------------------
-- Html Markup Output
------------------------------------------------------------------------------

-- Helper functions
-------------------

-- | Name value pairs for attributes.
type Attributes = [(String,String)]

-- | Output a document surrounded by a tag.
withTag :: Document d => 
           String      -- ^ Tag name
        -> Attributes  -- ^ Name, value pairs for attributes (no escaping done!)
        -> d           -- ^ Inner document
        -> d
withTag tag atts d = 
  zeroWidthText ("<" ++ tag ++ attsStr ++ ">") <> d <> zeroWidthText ("</" ++ tag ++ ">")
  where
  attsStr | null atts = ""
          | otherwise = concat [ " "++a++"=\""++v++"\"" | (a,v) <- atts ]

-- | Output a document surrounded by a span tag.
withSpan :: Document d => Attributes -> d -> d
withSpan = withTag "span"


-- Html Markup Monad
--------------------

newtype GraphIdx = GraphIdx { getGraphIdx :: Int }
  deriving( Eq, Ord, Num, Enum, JSON )

instance Show GraphIdx where
  show = show . getGraphIdx

type HtmlCase = (GraphIdx, [((String, Bool), GraphIdx)])
type HtmlSequent = GraphIdx
-- type HtmlSequent = (GraphIdx, GraphIdx)

data HtmlMarkupState = HtmlMarkupState {
    htmlCases       :: M.Map Int HtmlCase
  , htmlThmDefs     :: M.Map (String, String) HtmlSequent
  , htmlThmRefs     :: M.Map Int HtmlSequent
  , htmlGraphRefs   :: M.Map Int HtmlSequent
  , htmlExpls       :: M.Map String Int 
  , htmlNextExplRef :: Int
  }

type GraphDesc = String

newtype HtmlMarkup a = HtmlMarkup {
    unHtmlMarkup :: StateT HtmlMarkupState 
                      (ConsistentLabelsT GraphDesc GraphIdx Identity) a
  }
  deriving( Functor, Applicative, Monad )

instance MonadState HtmlMarkupState HtmlMarkup where
  get = HtmlMarkup get
  put = HtmlMarkup . put

-- | Get a uniquely numbered reference to a graph given as a 'Dot' action.
referenceGraph :: Dot a -> HtmlMarkup GraphIdx
referenceGraph = HtmlMarkup . lift . label . showDot

-- | Compute the next free index of a map of keys: 0 for the empty map and the
-- maximal index plus 1 otherwise.
nextIndex :: (Num k, Enum k) => M.Map k v -> k
nextIndex = maybe 0 (succ.fst.fst) . M.maxViewWithKey

-- | Insert the value at the 'nextIndex' of one of the maps underlying the
-- 'HtmlMarkupState'.
insertAtNextIndex :: (Ord k, Enum k, Num k) =>
                     (HtmlMarkupState -> M.Map k v)                    -- ^ Get the map.
                  -> (M.Map k v -> HtmlMarkupState -> HtmlMarkupState) -- ^ Set the map.
                  -> v -> HtmlMarkup k
insertAtNextIndex getter setter c = HtmlMarkup $ do
  s <- get
  let cases = getter s
      next  = nextIndex cases
  put (setter (M.insert next c cases) s)
  return next

insertHtmlCase :: HtmlCase -> HtmlMarkup Int
insertHtmlCase = insertAtNextIndex htmlCases (\x s->s {htmlCases = x})

insertGraphRef :: GraphIdx -> HtmlMarkup Int
insertGraphRef = insertAtNextIndex htmlGraphRefs (\x s->s {htmlGraphRefs = x})

insertThmRef :: HtmlSequent -> HtmlMarkup Int
insertThmRef = insertAtNextIndex htmlThmRefs (\x s->s {htmlThmRefs = x})

insertThmDef :: Theorem -> HtmlSequent -> HtmlMarkup (String, String)
insertThmDef thm se = do
  let name = (protoName . seProto $ thmSequent thm, thmName thm)
  modify (\s -> s { htmlThmDefs = M.insert name se (htmlThmDefs s) })
  return name

insertExplanation :: String -> HtmlMarkup Int
insertExplanation e = do
  expls <- gets htmlExpls
  case M.lookup e expls of
    Just ref -> return ref
    Nothing  -> do
      st <- get
      let ref = htmlNextExplRef st
      put $ st { htmlNextExplRef = succ ref, htmlExpls = M.insert e ref expls }
      return ref

htmlSequent :: Sequent -> HtmlMarkup HtmlSequent
htmlSequent = referenceGraph . dotSequentMarked S.empty
  -- (,) <$> referenceGraph (dotPremise se) <*> referenceGraph (dotConclusion se)

htmlCase :: Dot a -> [((String,Bool),Dot b)] -> HtmlMarkup HtmlCase
htmlCase c scs =
  (,) <$> referenceGraph c <*>
          sequenceA [ (,) info <$> referenceGraph dot | (info, dot) <- scs ]

emptyHtmlMarkupState :: HtmlMarkupState
emptyHtmlMarkupState = HtmlMarkupState M.empty M.empty M.empty M.empty M.empty 0

runHtmlMarkup :: HtmlMarkup a -> (a, (HtmlMarkupState, M.Map GraphDesc GraphIdx))
runHtmlMarkup m = 
  case runIdentity . flip runConsistentLabelsT [1..] .
       flip runStateT emptyHtmlMarkupState . unHtmlMarkup $ m of
    ((res, st), (_, sequentIdxs)) -> (res, (st, sequentIdxs))

evalHtmlMarkup :: HtmlMarkup a -> a
evalHtmlMarkup = fst . runHtmlMarkup

instance MarkupMonad HtmlMarkup where
  withGraph dot d = do
    ref <- insertGraphRef =<< referenceGraph dot
    withSpan [("id", "graphRef_"++show ref)] d

  withExplanation expl d = do
    ref <- insertExplanation expl
    withSpan [("name", "explRef_"++show ref)] d

  noteCases c ntcs tcs d = do
    let addTag isTrivial (name, dot) = ((name, isTrivial), dot)
        cases = map (addTag False) ntcs ++ map (addTag True) tcs
    ref <- insertHtmlCase =<< htmlCase c cases
    withSpan [("id", "caseRef_"++show ref)] d

  theoremRef proto thmname = do
    let pname = protoName proto
    defs <- gets htmlThmDefs
    case M.lookup (pname, thmname) defs of
      Just se -> do
        ref <- insertThmRef se
        withSpan [("id","thmRef_"++show ref)] (text thmname)
      Nothing ->
        text thmname

  theoremDef thm d = do
    (pname, thname) <- insertThmDef thm =<< htmlSequent (thmSequent thm)
    let anchor = pname ++ "_" ++ thname
    withTag "a" [("name",anchor)] d

  keyword tag d = withSpan [("class","kw-"++tag)] d

  

