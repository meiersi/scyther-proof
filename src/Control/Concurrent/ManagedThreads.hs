-- NOTE: The first part of this module is based on Chapter 24 from 
-- "Real World Haskell Programming" cf:
-- (http://book.realworldhaskell.org/read/concurrent-and-multicore-programming.html)

module Control.Concurrent.ManagedThreads (
    ThreadManager
  , newManager
  , forkManaged
  , getStatus
  , waitFor
  , waitAll

  , nParSequenceIO
  , nParSequenceIO_
  , nParMapIO
  , nParMapIO_
  , nParCmd_
  , parCmd_
) where

import Data.Ord      (comparing)
import Data.List     (sortBy)
import qualified Data.Map as M

import Control.Monad

import Control.Concurrent
import Control.Exception (IOException, try)

import GHC.Conc (numCapabilities)


------------------------------------------------------------------------------
-- Thread Manager
------------------------------------------------------------------------------

data ThreadStatus = Running
                  | Finished         -- terminated normally
                  | Threw IOException  -- killed by uncaught exception
                    deriving (Show)

newtype ThreadManager =
    Mgr (MVar (M.Map ThreadId (MVar ThreadStatus)))
    deriving (Eq)

-- | Create a new thread manager.
newManager :: IO ThreadManager
newManager = Mgr `fmap` newMVar M.empty

-- | Create a new managed thread.
forkManaged :: ThreadManager -> IO () -> IO ThreadId
forkManaged (Mgr mgr) body =
    modifyMVar mgr $ \m -> do
      state <- newEmptyMVar
      tid <- forkIO $ do
        result <- try body
        putMVar state (either Threw (const Finished) result)
      return (M.insert tid state m, tid)

-- | Immediately return the status of a managed thread.
getStatus :: ThreadManager -> ThreadId -> IO (Maybe ThreadStatus)
getStatus (Mgr mgr) tid =
  modifyMVar mgr $ \m ->
    case M.lookup tid m of
      Nothing -> return (m, Nothing)
      Just st -> tryTakeMVar st >>= \mst -> case mst of
                   Nothing -> return (m, Just Running)
                   Just sth -> return (M.delete tid m, Just sth)

-- | Block until a specific managed thread terminates.
waitFor :: ThreadManager -> ThreadId -> IO (Maybe ThreadStatus)
waitFor (Mgr mgr) tid =
  join . modifyMVar mgr $ \m ->
    return $ case M.updateLookupWithKey (\_ _ -> Nothing) tid m of
      (Nothing, _) -> (m, return Nothing)
      (Just st, m') -> (m', Just `fmap` takeMVar st)

-- | Block until all managed threads terminate.
waitAll :: ThreadManager -> IO ()
waitAll (Mgr mgr) = modifyMVar mgr elems >>= mapM_ takeMVar
    where elems m = return (M.empty, M.elems m)


------------------------------------------------------------------------------
-- Parallel Sequence
------------------------------------------------------------------------------

-- | Extract the head of the list in the MVar if possible.
takeHead :: MVar [a] -> IO (Maybe a)
takeHead v = 
    modifyMVar v (return . extract)
  where
    extract []     = ([], Nothing)
    extract (x:xs) = (xs, Just x)

-- | Do a parallel sequencing of a list of IO commands using n worker threads
-- and gather their results in a list again.
nParSequenceIO :: Int -> [IO a] -> IO [a] 
nParSequenceIO n ios = do
    inMv <- newMVar $ zip [(1::Int)..] ios
    resMv <- newMVar []
    mgr <- newManager
    mapM_ (forkManaged mgr) (replicate (max 1 n) $ worker inMv resMv)
    waitAll mgr
    (map snd . sortBy (comparing fst)) `liftM` takeMVar resMv
  where
    worker inMv resMv = do
        nextJob <- takeHead inMv
        case nextJob of
          Nothing      -> return ()
          Just (i, io) -> do
              out <- io
              modifyMVar_ resMv (\res -> return $ (i,out) : res)
              worker inMv resMv

-- | Do a parallel sequencing of a list of IO commands using n worker threads.
nParSequenceIO_ :: Int -> [IO a] -> IO ()
nParSequenceIO_ n ios = do
    inMv <- newMVar ios
    mgr <- newManager
    mapM_ (forkManaged mgr) (replicate n $ worker inMv)
    waitAll mgr
  where
    worker inMv = do
        nextJob <- takeHead inMv
        case nextJob of
          Nothing -> return ()
          Just io -> io >> worker inMv

-- | Do a parallel map of an IO cmd over a list using n worker threads.
nParMapIO :: Int -> (a -> IO b) -> [a] -> IO [b]
nParMapIO n f = nParSequenceIO n . map f

-- | Do a parallel map of an IO cmd over a list using n worker threads while
-- ignoring the results.
nParMapIO_ :: Int -> (a -> IO b) -> [a] -> IO ()
nParMapIO_ n f = nParSequenceIO_ n . map f

-- | Parallel execution of a command using n worker threads. The channel
-- argument can be used to report exactly one (!) progress value to the display
-- function.
-- NOTE: If the executed command is blocking, then you need to use the threaded
-- runtime
nParCmd_ :: Int -> (Int -> Int -> b -> IO ()) -> [Chan b -> IO a] -> IO ()
nParCmd_ nThreads display cmds = do
    chan <- newChan
    mgr <- newManager
    _ <- forkManaged mgr (displayThread chan 1)
    _ <- forkManaged mgr (nParMapIO_ nThreads (\cmd -> cmd chan) cmds)
    waitAll mgr
  where
    nCmds = length cmds
    displayThread ch i 
      | nCmds < i = do return ()
      | otherwise = do msg <- readChan ch
                       display nCmds i msg
                       displayThread ch (succ i)

-- | Like @nParCmd_@ but uses the number of processing cores+1 as a default for
-- the number of worker treads. You can change their number by adding to the
-- command line of a program linked with the threaded library: 
--    +RTS -N<no-of-cores> -RTS
parCmd_ :: (Int -> Int -> b -> IO ()) -> [Chan b -> IO a] -> IO ()
parCmd_ display cmds = nParCmd_ (numCapabilities+1) display cmds

