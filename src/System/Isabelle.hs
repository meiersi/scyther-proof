-- | Using Isabelle to check theory files.
--
-- Requirements:
--
--   1. A working installation of Isabelle2013 (http://isabelle.in.tum.de/)
--   2. The \'isabelle\' command must be on the PATH.
--
module System.Isabelle (
  checkTheoryFile
) where

import Data.List

import System.FilePath
import System.Directory
import System.Process
import System.IO
import System.Exit

------------------------------------------------------------------------------
-- Isabelle commands
------------------------------------------------------------------------------

-- | Use Isabelle to check the correctness of a theory file.
checkTheoryFile :: FilePath            -- ^ Path to 'isabelle' binary.
                -> Maybe Int           -- ^ Number of parallel thread to use while checking.
                -> FilePath            -- ^ Path to ESPL sources
                -> FilePath            -- ^ Path to file to be checked
                -> IO (Maybe String)
                   -- ^ If the check went through, log-file content only, otherwise
                   -- also an error message.
checkTheoryFile isabelleTool threads esplSrc thyFile = do
  let thyName     = takeBaseName thyFile
      rootName    = "ROOT"
      sessionName = "scyther-proof-" ++ thyName
  
  -- setup temporary directory
  tmpDir <- createTempDirectory
  copyFile thyFile (tmpDir </> addExtension thyName "thy")
  writeFile (tmpDir </> rootName) ("session \"" ++ sessionName ++ "\" = ESPL + theories \"" ++ thyName ++ "\"")
  -- call "isabelle usedir"
  (code, out, _err) <- readProcessWithExitCode isabelleTool
     ["build", "-d", esplSrc, "-D", tmpDir, "-j", maybe "0" show threads]
     ""
  if code == ExitSuccess
    then do
      removeDirectoryRecursive tmpDir
      return Nothing
    else
      return (Just (errMsg out))        
  where
  -- | Extract the error message from the isabelle output
  errMsg str = case break ("***" `isPrefixOf`) (lines str) of
    (_,[]) -> str
    (_,first:ls) -> case break ("***" `isPrefixOf`) ls of
      (_,[]) -> unlines (first : ls)
      (ls',(fin:_)) -> unlines (first : ls'++[fin])

  createTempDirectory :: IO FilePath
  createTempDirectory = do
      tmpBase <- getTemporaryDirectory
      -- hack to create a unique temporary directory
      (tmpDir, handle) <- openTempFile tmpBase "scyther-proof_tmp"
      hClose handle
      removeFile tmpDir
      createDirectory tmpDir
      return tmpDir
