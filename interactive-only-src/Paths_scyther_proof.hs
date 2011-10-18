module Paths_scyther_proof (
    version,
    getBinDir, getLibDir, getDataDir, getLibexecDir,
    getDataFileName
  ) where

import Data.Version (Version(..))
import System.Environment (getEnv)

version :: Version
version = Version {versionBranch = [0,3,1], versionTags = []}

bindir, libdir, datadir, libexecdir :: FilePath

bindir     = "."
libdir     = "."
datadir    = "data"
libexecdir = "."

getBinDir, getLibDir, getDataDir, getLibexecDir :: IO FilePath
getBinDir = catch (getEnv "scyther_proof_bindir") (\_ -> return bindir)
getLibDir = catch (getEnv "scyther_proof_libdir") (\_ -> return libdir)
getDataDir = catch (getEnv "scyther_proof_datadir") (\_ -> return datadir)
getLibexecDir = catch (getEnv "scyther_proof_libexecdir") (\_ -> return libexecdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
