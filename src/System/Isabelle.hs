-- | Using Isabelle to check theory files.
--
-- Requirements:
--
--   1. A working installation of Isabelle2009-1 (http://isabelle.in.tum.de/)
--   2. The \'isabelle\' command must be on the PATH.
--
module System.Isabelle (
  checkTheoryFile
) where

import Data.Maybe
import Data.List

import System.FilePath
import System.Directory
import System.Process
import System.IO

import Control.Concurrent
import Control.Monad
import Control.Exception

------------------------------------------------------------------------------
-- Utilities: TODO MOVE INTO GENERAL FILE
------------------------------------------------------------------------------

-- | Create and use a temporary file ensuring that it is closed if the
-- computation fails.
--
-- See 'openTempFile' for more information on the parameters.
withTempFile :: FilePath -> String -> ((FilePath, Handle) -> IO a) -> IO (a, FilePath)
withTempFile dir nameTemplate io = 
  bracket (openTempFile dir nameTemplate) (hClose . snd) 
          (\args@(file,_) -> do{ x <- io args; return (x, file) })

-- | Like 'withTempFile' buth without returning the results of the inner
-- computation.
withTempFile_ :: FilePath -> String -> ((FilePath, Handle) -> IO a) -> IO FilePath
withTempFile_ dir nameTemplate io = snd `liftM` withTempFile dir nameTemplate io

-- | Waits the given amount of microseconds before trying to terminate the
-- process using 'terminateProcess'.
waitForProcessTimeout :: Int -> ProcessHandle -> IO Bool
waitForProcessTimeout maxTime hProc
  | maxTime <= 0 = do _<- waitForProcess hProc; return False
  | otherwise    = do
      timeout <- newMVar False
      _ <- forkIO $ do
        threadDelay maxTime
        modifyMVar_ timeout (return . const True)
        terminateProcess hProc
      _ <- waitForProcess hProc
      readMVar timeout
    

------------------------------------------------------------------------------
-- Isabelle commands
------------------------------------------------------------------------------

-- | Use Isabelle to check the correctness of a theory file.
checkTheoryFile :: FilePath            -- ^ Path to 'isabelle' binary.
                -> Maybe Int           -- ^ Number of parallel thread to use while checking.
                -> Int                 -- ^ Maximal available time in micro-seconds
                -> String              -- ^ Logic Image to use
                -> FilePath            -- ^ Path to file to be checked
                -> IO (IO String, Maybe String)
                   -- ^ If the check went through, log-file content only, otherwise
                   -- also an error message.
checkTheoryFile isabelleTool threads maxTime logic thyFile = do
  let thyName     = takeBaseName thyFile
      rootName    = "ROOT-" ++ thyName ++ ".ML"
      sessionName = "scyther-proof-" ++ thyName
  -- create ROOT.ML file
  tmpDir <- getTemporaryDirectory
  rootFile <- withTempFile_ tmpDir rootName 
    (\(_, hRootFile) -> 
      hPutStrLn hRootFile $ "use_thy \"" ++ dropExtension thyFile ++ "\""
    )
  -- call "isabelle usedir"
  finally 
    (do let cmd = isabelleTool ++ 
                     " usedir -f " ++ rootFile ++ 
                     " -s " ++ sessionName ++ 
                     " -M " ++ maybe "0" show threads ++
                        " " ++ logic ++ " ."
        (_,   _,    hErr, hProc) <- runInteractiveCommand cmd
        isaOutVar <- newEmptyMVar
        _ <-forkIO $ redirect hErr isaOutVar
        timeout <- waitForProcessTimeout maxTime hProc
        isaOut <- takeMVar isaOutVar
        if timeout
          then do return (return $ isaOut ++ "Interrupted due to timeout!"
                         , Just $ "timeout: " ++ 
                              show ((fromIntegral maxTime / 10E6)::Double) ++ "s")
          else do return $ parseIsaOutput sessionName isaOut
    )
    (do removeFile rootFile)
  where
  -- | Redirect the contents of a the given handle into the message variable.
  redirect hIn mvar = hGetContents hIn >>= putMVar mvar

  -- | extract the log file name from the isabelle output
  logFileName str = fromMaybe "no log file" $ do
    let logIndicator = "(see also "
    line <- find (logIndicator `isPrefixOf`) (lines str) 
    init `liftM` stripPrefix logIndicator line
  
  -- | Extract the error message from the isabelle output
  errMsg str = case break ("***" `isPrefixOf`) (lines str) of
    (_,[]) -> str
    (_,first:ls) -> case break ("***" `isPrefixOf`) ls of
      (_,[]) -> unlines (first : ls)
      (ls',(fin:_)) -> unlines (first : ls'++[fin])

  -- | Parse the Isabelle output.
  parseIsaOutput sessionName str
    | ("Finished "++logic++"-"++sessionName) `isInfixOf` str = (return str, Nothing)
    | otherwise = (readFile (logFileName str), Just (errMsg str))

        
