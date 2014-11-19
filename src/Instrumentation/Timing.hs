{-# LANGUAGE ForeignFunctionInterface #-}
module Instrumentation.Timing (timingInit, timingBracket, timingReport) where

import           Data.IORef                       (IORef, newIORef, writeIORef, readIORef, modifyIORef)
import qualified Data.HashTable.IO                as HT
import           System.IO.Unsafe                 (unsafePerformIO)
import qualified Text.PrettyPrint.Boxes           as Boxes
import           Text.Printf                      (printf)

import           Prelude.Extended

type Key = String

{-# NOINLINE cumulativeTimes #-}
cumulativeTimes :: HT.CuckooHashTable Key Double
cumulativeTimes = unsafePerformIO HT.new

data StackItem = StackItem
  { siElapsed :: Double
  , siLeftAt  :: Double
  , siKey     :: Key
  }

_dummy :: a
_dummy = error "UNUSED" siElapsed siLeftAt siKey

type Stack = [StackItem]

{-# NOINLINE stackRef #-}
stackRef :: IORef Stack
stackRef = unsafePerformIO $ newIORef []

readStackRef :: IO Stack
readStackRef = readIORef stackRef

writeStackRef :: Stack -> IO ()
writeStackRef x = writeIORef stackRef x

modifyStackRef :: (Stack -> Stack) -> IO ()
modifyStackRef f = modifyIORef stackRef f

timingInit :: IO ()
timingInit = initializeTime

timingPush :: Key -> IO ()
timingPush key = do
  stack <- readStackRef
  t <- getCPUTime
  case stack of
    [] ->
      return ()
    (StackItem elapsed leftAt oldKey : stack') -> do
      let elapsed' = elapsed + (t - leftAt)
      writeStackRef $ StackItem elapsed' t oldKey : stack'
  modifyStackRef (StackItem 0 t key :)

timingPop :: IO ()
timingPop = do
  StackItem elapsed leftAt key : stack <- readStackRef
  t <- getCPUTime
  let elapsed' = elapsed + (t - leftAt)
  existing <- fromMaybe 0 <$> HT.lookup cumulativeTimes key
  HT.insert cumulativeTimes key (existing + elapsed')
  case stack of
    [] ->
      return ()
    StackItem oldElapsed _oldLeftAt oldKey : oldStack -> do
      writeStackRef $ StackItem oldElapsed t oldKey : oldStack

-- TODO sadly we can't use bracket here -- because of MonadIO.  Shall we
-- use lifted-base?
timingBracket :: (MonadIO m) => Key -> m a -> m a
timingBracket label m = do
  liftIO $ timingPush label
  x <- m
  liftIO $ timingPop
  return x

timingReport :: IO ()
timingReport = do
  kvs <- reverse . sortBy (comparing snd) <$> HT.toList cumulativeTimes
  let total  = sum $ map snd kvs
  let fmt n  = printf "%.4f" n :: String
  let perc n = printf "%.4f%%" $ ((n * 100) / total) :: String
  let vcatl  = Boxes.vcat Boxes.left
  let vcatr  = Boxes.vcat Boxes.right
  let (<+>)  = (Boxes.<+>)
  let box    = (\(x, y, z) -> vcatl x <+> vcatr y <+> vcatr z) $ unzip3
               [ (Boxes.text label, Boxes.text (fmt t), Boxes.text (perc t))
               | (label, t) <- kvs
               ]
  putStrLn "------------------------------------------------------------------------"
  putStrLn $ "-- Timing report"
  putStrLn "------------------------------------------------------------------------"
  putStrLn $ Boxes.render box

------------------------------------------------------------------------
-- Timing functions ripped from criterion.

-- | Return the amount of elapsed CPU time, combining user and kernel
-- (system) time into a single measure.
foreign import ccall unsafe "criterion_getcputime" getCPUTime :: IO Double

-- | Set up time measurement.
foreign import ccall unsafe "criterion_inittime" initializeTime :: IO ()
