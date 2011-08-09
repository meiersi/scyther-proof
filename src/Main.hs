{-# LANGUAGE DeriveDataTypeable #-}
module Main (main) where

import Data.Maybe
import Data.Char
import Data.List
import Data.Time.Clock
import Data.Time.Format ()
import qualified Data.Table as T
import Data.Version (showVersion)
import Data.Typeable (Typeable)

import Control.Basics
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Exception as E
import Control.Concurrent.MVar

import qualified Text.Isar as Isar

import System.Exit
import System.IO
import System.FilePath
import System.Directory
import System.Isabelle
import System.Info
import System.Timeout
import System.Timing
import System.Environment
import System.Process

import System.Console.CmdArgs.Explicit
import System.Console.CmdArgs.Text

import Extension.Prelude

-- import Logic.FOL.Sorted.TPTP
-- import Scyther.Theory.FOL

import Scyther.Facts hiding (MVar, empty)
import Scyther.Sequent
import Scyther.Proof
import Scyther.Theory
import Scyther.Theory.Parser
import Scyther.Theory.Pretty
import Scyther.Theory.Html

import Scyther.GoalFlow

import Paths_scyther_proof

------------------------------------------------------------------------------
-- Version information and global constants
------------------------------------------------------------------------------

-- | Program name
programName :: String
programName = "scyther-proof"

-- | Version string
versionStr :: String
versionStr = concat
  [ programName
  , " "
  , showVersion version
  , ", (C) Simon Meier, ETH Zurich, 2009-2011"
  ]

-- | Version string with HTML markup.
htmlVersionStr :: String
htmlVersionStr = concat
    [ link "http://people.inf.ethz.ch/meiersi/espl" programName
    , " "
    , showVersion version
    , ", &copy; "
    , link "http://people.inf.ethz.ch/meiersi" "Simon Meier"
    , ", ETH Zurich, 2009-2011"
    ]
  where
    link href name = 
        "<a href=\"" ++ href ++ "\" target=\"new\">" ++ name ++ "</a>"

-- | Line width to use.
lineWidth :: Int
lineWidth = 110

-- | ESPL Theory directory.
esplTheoryDir :: IO String
esplTheoryDir = getDataFileName "isabelle"


------------------------------------------------------------------------------
-- Argument parsing helpers
------------------------------------------------------------------------------

type Arguments = [(String,String)]

argExists :: String -> Arguments -> Bool
argExists a = isJust . findArg a

findArg :: MonadPlus m => String -> Arguments -> m String
findArg a' as = msum [ return v | (a,v) <- as, a == a' ]

findCheckedArg :: (Read a, MonadPlus m) => (a -> Bool) -> String -> Arguments -> m a
findCheckedArg p a as = do
    x <- read `liftM` findArg a as
    guard (p x)
    return x

addArg :: String -> String -> Arguments -> Arguments
addArg a v = ((a,v):)

withArguments :: Mode Arguments -> (Arguments -> IO ()) -> IO ()
withArguments argMode io = do
    processArgs argMode >>= run
  where
    run as
      | argExists "help"    as = print $ helpText HelpFormatAll argMode
      | argExists "version" as = putStrLn versionStr
      | otherwise              = io as

    
------------------------------------------------------------------------------
-- Argument Parsing
------------------------------------------------------------------------------
 
data PrintMode =
    SPTheory       -- ^ Output as a security protocol theory.
  | IsarXSymbol    -- ^ Output as an Isabelle theory using XSymbol symbols.
  | IsarASCII      -- ^ Output as an Isabelle theory using ASCII symbols.
  deriving( Show, Eq )

-- | Main mode.
setupMainMode :: IO (Mode [(String,String)])
setupMainMode = do
    examplePath  <- getDataFileName "examples"
    readmePath   <- getDataFileName "isabelle/README"
    isabellePath <- esplTheoryDir
    return $ 
      ( defaultMode programName
          "Automatic generation of machine-checked proofs for security protocols."
          [ "Additional information:"
          , "  Path to example protocol models: '" ++ examplePath ++ "'"
          , "  Path to Isabelle/HOL security protocol theory: '" ++ isabellePath ++ "'"
          , "  "
          , "  The '--html' flag requires the 'dot' tool from GraphViz available at:"
          , "    " ++ "http://www.graphviz.org/"
          , "  "
          , "  The '--isabelle' flag requires the 'Isabelle-2009-1' release of Isabelle/HOL:"
          , "    " ++ "http://isabelle.in.tum.de/website-Isabelle2009-1/download_x86-linux.html"
          , ""
          , "  Check the '" ++ readmePath ++ "' file for instructions on how to load the generated theory files in Isabelle's interactive mode."
          ]
      )
      { modeCheck      = upd "mode" "translate"
      , modeArgs       = Just $ flagArg (upd "inFile") "FILES"
      , modeGroupFlags = Group 
          { groupUnnamed =
              [ flagNone ["first", "f"] (addArg "strategy" "first")
                  "Return the first found proof."

              , flagNone ["shortest", "s"] (addArg "strategy" "shortest")
                  "Return the shortest proof w.r.t number of chain rule applications."

              , flagOpt "5" ["bound", "b"]   (upd "bound") "INT"
                  "Bound the depth of the proofs (0 for no bound)."

              , flagNone ["no-reuse"] (addArg "reuse" "none")
                  "Do not reuse any previously proven properties."

              , flagNone ["secrecy-reuse"] (addArg "reuse" "secrecy")
                  "Reuse serecy properties only."

              , flagNone ["no-minimize"] (addEmpty "noMinimize")
                  "Do not minimize the number of forward resolutions."

              , flagNone ["no-soundness-check"] (addEmpty "noSoundness")
                  "Do not output a list of properties with unsound proofs."

              , flagNone ["no-attack-search"] (addEmpty "noAttackSearch")
                  "Do not search for attacks before attempting a proof."

              , flagNone ["overview"] (addEmpty "overview")
                  "Generate a protocol overview."

              , flagNone ["compose-parallel"] (addEmpty "composeParallel")
                  "Compose all security protocols in the theory in parallel."

              , flagOpt "isabelle" ["isabelle","i"] (upd "isabelle") "PATH"
                  "Check resulting proof script using the 'isabelle' tool from Isabelle/HOL."

              , flagOpt "0" ["isabelle-threads"]   (upd "isabelleThreads") "INT"
                  "Number of parellel threads to be used for proof checking. \
                  \(The default is to use as many threads as there are cores.)"

              , flagNone ["rebuild-logic"] (addEmpty "rebuildLogic")
                  "Rebuild the ESPL logic image (required after updating its source)"

              , flagNone ["no-generation"] (addEmpty "noGeneration")
                  "Do not generate the theory files, but check the results using Isabelle."

              , flagOpt "0" ["timeout"]   (upd "timeout") "SECONDS"
                  "Timeout in seconds for proof generation and checking."

              , flagOpt "" ["hide-prefix"]   (upd "hidePrefix") "VALUE"
                  "Hide non-referenced properties with this prefix (default=auto)."

              , flagOpt "dot" ["html"] (upd "html") "PATH"
                  "Output Html files visualizing the theory and its proofs using the 'dot' tool from Graphviz. This flag requires an output directory to be set."

              , flagOpt "100" ["chars-per-line"]   (upd "charsPerLine") "INT"
                  "Characters per line (default=100)."

              , flagNone ["XSymbol", "X"] (addArg "printMode" "XSymbol")
                  "Output as an Isabelle theory using XSymbol symbols."

              , flagNone ["ASCII", "A"] (addArg "printMode" "ASCII")
                  "Output as an Isabelle theory using ASCII symbols."

              , flagOpt "-" ["report"]   (upd "report") "FILE"
                  "Write a report file (use - for stdout)."

              ] ++
              outputFlags
          , groupHidden = []
          , groupNamed =
              [ ("About"
                , [ flagHelpSimple (addEmpty "help")
                  , flagVersion (addEmpty "version")
                  ] )
              ]
          }
      }
  where 
    upd a v = Right . addArg a v
    addEmpty a = addArg a ""

    defaultMode name help helpSuffix = Mode
        { modeGroupModes = toGroup []
        , modeNames      = [name] 
        , modeValue      = [] 
        , modeCheck      = upd "mode" name
        , modeReform     = const Nothing-- no reform possibility
        , modeHelp       = help
        , modeHelpSuffix = helpSuffix
        , modeArgs       = Nothing    -- no positional arguments
        , modeGroupFlags = toGroup [] -- no flags
        }

    outputFlags = 
      [ flagOpt "" ["output","o"] (upd "outFile") "FILE" "Output file"
      , flagOpt "" ["Output","O"] (upd "outDir") "DIR"  "Output directory"
      ]


-- | Disply help message and exit.
errHelpExit :: String -> IO ()
errHelpExit msg = do
  mainMode <- setupMainMode
  putStrLn $ "error: " ++ msg
  putStrLn $ ""
  putStrLn $ showText (Wrap 100) 
           $ helpText HelpFormatDefault mainMode
  exitFailure


-- | Main function.
main :: IO ()
main = do
    mainMode <- setupMainMode
    withArguments mainMode selectMode
  where
    selectMode as = case findArg "mode" as of
      Just "translate" -> translate as
      Just m           -> error $ "main: unknown mode '" ++ m ++ "'"
      Nothing          -> error $ "main: no mode given"


------------------------------------------------------------------------------
-- Translate mode execution
------------------------------------------------------------------------------

-- | Entry point fro executing a translation.
translate :: Arguments -> IO ()
translate as = do
    templateFile <- getDataFileName "HTML_TEMPLATE"
    reportVar <- newMVar T.empty
    translateWorker as templateFile reportVar


-- | Execute a translation.
translateWorker :: Arguments 
                -> FilePath     -- ^ Path to HTML template file.
                -> MVar (T.Table String) -- ^ Empty MVar for building the report.
                -> IO ()
translateWorker as templateFile reportVar
  | null inFiles && not rebuildLogic = errHelpExit "no input iles given"
  | otherwise                        = do
      -- check required tools
      when (not dryRun && html)     (ensureGraphVizDot dotTool)
      when (rebuildLogic || (not dryRun && isabelle)) 
          (ensureIsabelleESPL rebuildLogic isabelleTool)
      
      -- translate all input files and ensure report is written with a special
      -- interrupted marker when an exception like Ctrl-C happened
      unless (n <= 1)  (putInfoLn $ "processing "++show n++" files:")
      bracket_ (return ()) writeReport $
        bracketOnError_ (return ())
          (updateReport (T.appendCell "interrupted"))
          (sequence_ . intersperse reportNewRow $ map translateOneFile inFiles )
      putInfoLn ""
  where
    -- Tool paths and flags
    -----------------------
    rebuildLogic = argExists "rebuildLogic" as
    isabelleTool = fromMaybe "isabelle" $ findArg "isabelle" as
    dotTool      = fromMaybe "dot"      $ findArg "html" as

    -- Input files
    -----------------------
    inFiles = findArg "inFile" as
    n       = length inFiles

    maxFileNameLength :: Int
    maxFileNameLength = maximum $ map length inFiles

    -- Output files
    ---------------
    dryRun     = outFile == "" && outDir == ""
    reportFile = fromMaybe "" $ findArg "report"  as
    outFile    = fromMaybe "" $ findArg "outFile" as 
    outDir     = fromMaybe "" $ findArg "outDir"  as 
    

    -- automatically generate the filename for output
    mkAutoPath :: FilePath -> String -> FilePath
    mkAutoPath dir name
      | html      = dir </> name
      | otherwise = dir </> addExtension (name ++ "_cert_auto") "thy"

    mkOutPath :: FilePath  -- ^ Input file name.
              -> FilePath  -- ^ Output file name.
    mkOutPath inFile = 
      case outFile of
        ""   -> case outDir of
                  ""  -> error "outPath: undefined in dry-run mode"
                  dir -> mkAutoPath dir (takeBaseName inFile)
        path -> path



    -- hidden security properties
    ----------------------
    hide = fromMaybe "auto" $ findArg "hidePrefix" as

    isHidden :: String -> Bool
    isHidden | hide == "" = const False
             | otherwise  = (hide `isPrefixOf`)

    removeHiddenItems :: Theory -> Theory
    removeHiddenItems = shrinkTheory (not . isHidden)

    -- protocol composition
    -----------------------
    composeProtos :: Theory -> Theory
    composeProtos 
      | argExists "composeParallel" as = composeParallel
      | otherwise                      = id

    -- timeout handling
    -------------------
    maxTime :: Maybe Int
    maxTime = findCheckedArg (0 <) "timeout" as

    execWithTimeout :: IO a -> IO a
    execWithTimeout io = case maxTime of
        Nothing -> io
        Just t  -> do
            res <- timeout (t * 1000000) io
            case res of 
              Nothing -> do
                updateReport (T.appendCell $ "timeout: "++show maxTime++"s")
                throw CustomTimeout
              Just x -> return x

    ignoringTimeout :: IO () -> IO ()
    ignoringTimeout io = E.catch io handler
      where
      handler :: CustomTimeout -> IO ()
      handler _ = return ()

    -- progress output for batch mode
    ---------------------------------
    putInfo   msg = unless dryRun (putStr   msg >> hFlush stdout)
    putInfoLn msg = unless dryRun (putStrLn msg >> hFlush stdout)

    -- report generation
    --------------------
    reportNewRow :: IO ()
    reportNewRow = updateReport T.newRow >> putInfoLn ""

    reportNumber :: Show a => String -> a -> IO ()
    reportNumber header x = 
      updateReport (T.headerLastCell header . T.alignLastCell T.AlignRight. T.appendCell (show x))

    reportString :: String -> String -> IO ()
    reportString header msg = 
      updateReport (T.headerLastCell header . T.appendCell msg)
  
    updateReport :: (T.Table String -> T.Table String) -> IO ()
    updateReport 
      | null reportFile = const $ return () -- no report will be produced => don't update it
      | otherwise       = modifyMVar_ reportVar . (return .)

    reportProofSize :: ProofSize -> IO ()
    reportProofSize s = do
      reportNumber "#chain rules"         nChains
      reportNumber "#forward resolutions" nForward
      reportNumber "#missing proofs"      nMissing
      where 
      (nChains, nForward, nMissing) = getProofSize s

    reportProperties :: Theory -> IO ()
    reportProperties thy = do
      reportNumber "#sec."  nSec
      reportNumber "#auth." nAuth
      reportNumber "#other" nOther
      where
      (nSec, nAuth, nOther) = classifyProperties (not . isHidden) thy

    mkReport :: IO String
    mkReport = do
      table <- readMVar reportVar
      time  <- getCurrentTime
      cmdLine <- getCommandLine
      revisions <- (concat . intersperse ", " . nub)
                   `liftM` mapM getSvnRevision inFiles
      let header = unlines $ map ("% "++) [
              "generator:   " ++ versionStr
            , "command:     " ++ cmdLine
            , "date:        " ++ show time
            , "system:      " ++ arch ++ "/" ++ os
            , "input revs.: " ++ revisions
            ]
      return . concat $ [
          "\n\n"
        , header 
        , "\n"
        , T.toLaTeX (filter (/='\t')) table
        ]

    writeReport :: IO ()
    writeReport = case reportFile of
      ""  -> return ()
      "-" -> mkReport >>= putStrLn
      _   -> mkReport >>= appendFile reportFile
    
    -- HTML generation
    ------------------
    generateHtml :: FilePath -- ^ Input file
                 -> Theory   -- ^ Theory to pretty print
                 -> IO ()
    generateHtml inFile thy = do
      cmdLine <- getCommandLine
      time    <- getCurrentTime
      cpu     <- getCpuModel
      theoryToHtml $ GenerationInput {
          giHeader      = "Generated by " ++ htmlVersionStr
        , giTime        = time
        , giSystem      = cpu
        , giInputFile   = inFile
        , giTemplate    = templateFile
        , giOutDir      = mkOutPath inFile
        , giMarkup      = thyToDoc printMode thy
        , giProofScript = 
            \outPath -> renderDoc . runIdentity . 
                        thyToDoc (ensureIsabellePrintMode printMode) $
                        adaptTheoryName outPath thy
        , giCmdLine     = cmdLine
        , giDotTool     = dotTool
        , giIsabelle    = 
            if isabelle  
              then Just $ checkTheoryFile isabelleTool isabelleThreads 0 "ESPL"
              else Nothing
        }

    -- Theory input
    ---------------
    overview       = argExists "overview" as

    makeOverview :: Theory -> Theory
    makeOverview | overview  = protocolsOnly -- theoryOverview
                 | otherwise = id
      where
      protocolsOnly (Theory name items) = 
        Theory name [x | x@(ThyProtocol _) <- items ]

    thyToOverviewDoc :: Theory -> Isar.Doc
    thyToOverviewDoc = goalFlowAnalysis

    readThy :: FilePath -> IO Theory
    readThy inFile = do
        putInfo (flushLeft maxFileNameLength inFile)
        reportString "Protocol" (takeBaseName inFile)
        reportString "Revision" =<< getSvnRevision inFile
        thy <- (makeOverview . ensureUniqueRoleNames) `liftM` parseTheory inFile
        reportProperties thy
        return . 
          removeHiddenItems .
          proveThy . 
          composeProtos .
          addMissingTypingInvariants .
          -- if no reuse is done, then remove the hidden items before proving
          -- (but still add missing typing invariants afterwards)
          (if noReuse then removeHiddenItems else id) $
          thy

    -- proving
    ----------
    bound   :: Maybe Int
    bound   = findCheckedArg (0 <) "bound" as

    noMinimize     = argExists "noMinimize" as
    noSoundness    = argExists "noSoundness" as
    noAttackSearch = argExists "noAttackSearch" as
    noReuse        = Just "noReuse" == findArg "reuse" as

    reuseSelector :: Sequent -> Named Proof -> Bool
    reuseSelector = case findArg "reuse" as of
      Just "noReuse"      -> mkReuse $ const False
      Just "secrecyReuse" -> mkReuse $ \th ->
        (complete $ thmProof th) && (FAtom AFalse == seConcl (thmSequent th))
      _                   -> mkReuse $ (complete . thmProof)
      where
      mkReuse thmSel se th
        | isTypingFormula $ seConcl se = 
            -- we do not support reusing in typing proofs
            -- because the ISAR pretty printer cannot handle it yet correctly.
            False
        | otherwise                    = 
            -- type invariants and axioms are always reused
            isAxiom th || (isTypingFormula . seConcl $ thmSequent th) || thmSel th
    
    minimizer :: Proof -> Proof
    minimizer | noMinimize = id
              | otherwise  = minimizeProof

    proveThy :: Theory -> Theory
    proveThy = case findArg "strategy" as of
        Just "first"    -> allClaims $ dfsProof bound oldestOpenMessages
        Just "shortest" -> allClaims $ shortestProof bound oldestOpenMessages
        _               -> id
      where
        allClaims prover0 = 
            proveSequents reuseSelector prover
          where
            prover toReuse se = fmap minimizer $
               (do guard (not noAttackSearch && bound == Nothing) 
                   -- TODO: Make attack search respect bound.
                   existsPossibleAttack oldestOpenMessages toReuse se
               `mplus` 
               prover0 toReuse se)
       

    -- Theory output
    ----------------
    noGeneration = argExists "noGeneration" as
    html         = argExists "html"         as
    isabelle     = argExists "isabelle"     as 
    width        = maybe lineWidth read $ findArg "charsPerLine" as

    isabelleThreads :: Maybe Int
    isabelleThreads = findCheckedArg (0 <) "isabelleThreads" as

    ensureIsabellePrintMode SPTheory = IsarASCII
    ensureIsabellePrintMode pmode    = pmode

    printMode = case findArg "printMode" as of
      Just "ASCII"   -> IsarASCII
      Just "XSymbol" -> IsarXSymbol
      Just other     -> error $ "internal: unknown printmode '" ++ other ++ "'"
      Nothing | isabelle && not html -> IsarASCII
              | otherwise            -> SPTheory

    thyToDoc :: MarkupMonad m => PrintMode -> Theory -> m Isar.Doc
    thyToDoc pmode thy0 = case pmode of
      SPTheory    -> runTaggedIdentityT SlimOutput thyDoc 
      IsarXSymbol -> runReaderT thyDoc (Isar.defaultIsarConf { Isar.isarStyle = Isar.XSymbol })
      IsarASCII   -> runReaderT thyDoc Isar.defaultIsarConf
      where
      -- for html output we rename the TID quantifiers in the conclusion
      -- to be clash-free
      thy | html      = mapTheorySequents uniqueTIDQuantifiers thy0
          | otherwise = thy0

      thyDoc :: PrettyMonad m => m Isar.Doc
      thyDoc | noSoundness = prettyTheory thy
             | otherwise   = prettyTheory thy Isar.$-$ prettySoundness thy

    renderDoc = Isar.renderStyle (Isar.style { Isar.lineLength = width })

    thyToString :: Theory -> String
    thyToString 
      | html      = renderDoc . evalHtmlMarkup . thyToDoc printMode
      -- | fol       = render . tptpProblem . toTPTP
      | overview  = renderDoc . thyToOverviewDoc
      | otherwise = renderDoc . runIdentity . thyToDoc printMode
      where

    writeThyFile :: FilePath -> Theory -> IO ()
    writeThyFile outPath thy = do
      if not noGeneration 
        then do
          tGen <- execWithTimeout . timed_ . writeFile outPath .
                  thyToString $ adaptTheoryName outPath thy
          let prfSize = theoryProofSize thy
          reportNumber "Generation Time" tGen
          reportProofSize prfSize
          putInfo ('\t' : (flushLeft 9 . show $ prfSize))
          putInfo ('\t' : show tGen)
        else do
          -- ensure columns of report are in line with generatin branch
          reportString "Generation Time" "--no-generation"
          sequence_ . replicate 3 $ reportString "-" "--n"
      if isabelle
        then do
          -- let isabelleTimeout = maxTime * 10^6 -- in microseconds
          let isabelleTimeout = 0 -- because timeout construction for Isabelle is buggy currently
          ((_, result), tCheck) <- timed $ checkTheoryFile isabelleTool isabelleThreads isabelleTimeout "ESPL" outPath
          reportNumber "Checking Time" tCheck
          case result of
            Nothing -> do
              mapM_ (putInfo . ('\t':)) ["successfully checked", show tCheck, ""]
              reportString "Isabelle Status" "checked"
              reportString "Isabelle Message" ""
            Just msg -> do
              mapM_ (putInfo . ('\t':)) ["CHECK FAILED", show tCheck, show msg]
              reportString "Isabelle Status" "check failed"
              reportString "Isabelle Message" (show msg)
        else 
          return ()

    -- Translate one theory file
    ----------------------------
    -- NOTE: For the timeout mechanism to work you have to take care that
    -- all IO actions forcing this theory are done under the timeout in
    -- writeThyFile. I didn't do this once, which cost me quite some
    -- debugging time.
    processThy :: FilePath -> Theory -> IO ()
    processThy inFile thy 
      | dryRun    = putStrLn (thyToString thy)
      | html      = do
          generateHtml inFile thy
      | otherwise = do
          handle (\(ErrorCall errMsg) -> putInfo $ "error: "++errMsg) $
            handle (\(PatternMatchFail errMsg) -> putInfo $ "error: "++errMsg) $ do
              createDirectoryIfMissing True (takeDirectory outPath)
              writeThyFile outPath thy
      where
      outPath = mkOutPath inFile

    translateOneFile :: FilePath -> IO ()
    translateOneFile inFile = ignoringTimeout (readThy inFile >>= processThy inFile)


------------------------------------------------------------------------------
-- Utility Functions
------------------------------------------------------------------------------

-- | Version of bracket on error with constant error handler and inner IO
-- function.
bracketOnError_ :: IO a -> IO b -> IO c -> IO c
bracketOnError_ aquire onError io = bracketOnError aquire (const onError) (const io)

-- | Custom timeout exception for the use with execWithTimeout
data CustomTimeout = CustomTimeout
     deriving (Show, Typeable)

instance Exception CustomTimeout

-- | Get the string constituting the command line.
getCommandLine :: IO String
getCommandLine = commandLine programName <$> getArgs

-- | Build the command line corresponding to a program arguments tuple.
commandLine :: String -> [String] -> String
commandLine prog args = concat $ intersperse " " $ prog : args

-- | Read the SVN revision of the given file using the SVN command.
getSvnRevision :: FilePath -> IO String
getSvnRevision file = 
  handle handler $ do
    (_, info, _) <- readProcessWithExitCode "svn" ["info",file] []
    return $ maybe "unversioned"
               (takeWhile isNumber . dropWhile (not.isNumber))
               (find ("Revision:" `isPrefixOf`) $ lines info)
  where
  handler :: IOException -> IO String
  handler _ = return "svn error"

-- | Read the cpu info using a call to cat /proc/cpuinfo
getCpuModel :: IO String
getCpuModel = 
  handle handler $ do
    (_, info, _) <- readProcessWithExitCode "cat" ["/proc/cpuinfo"] []
    return $ maybe errMsg
               (("Linux running on an "++) . drop 2 . dropWhile (/=':'))
               (find (isPrefixOf "model name") $ lines info)
  where
  errMsg = "could not extract CPU model"
  handler :: IOException -> IO String
  handler _ = return errMsg


-- | Test if a process is executable and check its response. This is used to
-- determine the versions and capabilities of tools that we depend on.
testProcess :: (String -> String -> Either String String) 
                              -- ^ Analysis of stdout, stderr. Use 'Left' to report error.
            -> String         -- ^ Test description to display.
            -> FilePath       -- ^ Process to start
            -> [String]       -- ^ Arguments
            -> String         -- ^ Stdin
            -> IO Bool        -- ^ True, if test was successful
testProcess check testName prog args inp = do
    putStr testName
    hFlush stdout
    handle handler $ do
        (exitCode, out, err) <- readProcessWithExitCode prog args inp
        let errMsg reason = do
                putStrLn reason
                putStrLn $ "command: " ++ commandLine prog args
                putStrLn $ "stdin:   " ++ inp
                putStrLn $ "stdout:  " ++ out
                putStrLn $ "stderr:  " ++ err
                return False

        case exitCode of
            ExitFailure code -> errMsg $ "failed with exit code " ++ show code
            ExitSuccess      -> 
              case check out err of
                Left msg     -> errMsg msg
                Right msg    -> do putStrLn msg
                                   return True
  where
    handler :: IOException -> IO Bool
    handler _ = do putStrLn "caught exception while executing:"
                   putStrLn $ commandLine prog args
                   putStrLn $ "with input: " ++ inp
                   return False

-- | Ensure a suitable version of the Graphviz dot tool is installed.
ensureGraphVizDot :: FilePath -- ^ Path to the 'dot' tool.
                  -> IO ()
ensureGraphVizDot dot = do
    putStrLn $ "checking suitability of GraphViz tool: '" ++ dot ++ "'"
    _ <- testProcess check " checking version: " dot ["-V"] ""
    putStrLn ""
  where
    check _ err
      | "Graphviz" `isInfixOf` err = Right $ init err ++ ". OK."
      | otherwise                  = Left  $ unlines $
          [ "WARNING:"
          , ""
          , " The dot tool seems not to be provided by Graphviz."
          , " Graph generation might not work."
          , " Please download an official version from:"
          , "         http://www.graphviz.org/"
          ]


-- | Ensure a suitable version of the Isabelle/HOL 'isabelle' tool is installed
-- and the 'ESPL' head is compiled.
ensureIsabelleESPL :: Bool     -- ^ True if logic must rebuilt anyways.
                   -> FilePath -- ^ Path to the 'isabelle' tool.
                   -> IO ()
ensureIsabelleESPL rebuild isabelle = do
    putStrLn $ "checking suitability of Isabelle tool: '" ++ isabelle ++ "'"
    _ <- testProcess checkVersion " version: " isabelle ["version"] ""
    success <- testProcess checkLogics " installed logics: " isabelle ["findlogics"] ""
    if success && not rebuild
      then putStrLn " (use the flag --rebuild-logic if your image of ESPL is outdated)"
      else buildESPL
    putStrLn ""
  where
    checkVersion out _
      | "Isabelle2009-1" `isInfixOf` out = Right $ init out ++ ". OK."
      | otherwise                        = Left  $ unlines $
          [ "WARNING:"
          , ""
          , " " ++ programName ++ " requires Isabelle2009-1."
          , " Proof checking is likely not to work."
          , " Please download Isabelle2009-1 from:"
          , "   http://isabelle.in.tum.de/website-Isabelle2009-1/download_x86-linux.html"
          ]

    checkLogics out _
      | "ESPL" `isInfixOf` out = Right $ init out ++ ". OK."
      | otherwise              = Left  $ init out ++ ". WARNING: ESPL logic not installed."


    buildESPL = do
      putStrLn "---"
      putStrLn "Attempting to build ESPL logic (this may take several minutes):"
      theoryDir <- esplTheoryDir
      let isamake args = 
            runProcess isabelle ("make" :args) (Just theoryDir) Nothing Nothing Nothing Nothing
              >>= waitForProcess
      exitCode <- isamake ["clean"] >> isamake []
      case exitCode of
        ExitSuccess -> putStrLn "Sucess! :-)\n---"
        ExitFailure code -> putStrLn $ unlines 
            [ "  Logic building failed with code: " ++ show code
            , "  Proof checking is likely not to work."
            , "  To investigate the problem try manually loading/building the theories in"
            , "    '" ++ theoryDir ++ "'"
            ]
      
