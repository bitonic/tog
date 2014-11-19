{-# LANGUAGE ForeignFunctionInterface #-}
module Timing (push, pop, report) where

import           Data.IORef                       (IORef, newIORef, writeIORef, readIORef, modifyIORef)
import qualified Data.HashTable.IO                as HT
import           System.IO.Unsafe                 (unsafePerformIO)
import qualified Text.PrettyPrint.Boxes           as Boxes
import           Data.Functor                     ((<$>))
import           Data.Maybe                       (fromMaybe)
import           Data.List                        (sortBy)
import           Data.Ord                         (comparing)
import           Text.Printf                      (printf)
import           Control.Monad.IO.Class           (MonadIO, liftIO)

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

readStackRef :: MonadIO m => m Stack
readStackRef = liftIO $ readIORef stackRef

writeStackRef :: MonadIO m => Stack -> m ()
writeStackRef x = liftIO $ writeIORef stackRef x

modifyStackRef :: MonadIO m => (Stack -> Stack) -> m ()
modifyStackRef f = liftIO $ modifyIORef stackRef f

init :: MonadIO m => m ()
init = liftIO initializeTime

push :: MonadIO m => Key -> m ()
push key = do
  stack <- readStackRef
  t <- liftIO getCPUTime
  case stack of
    [] ->
      return ()
    (StackItem elapsed leftAt oldKey : stack') -> do
      let elapsed' = elapsed + (t - leftAt)
      writeStackRef $ StackItem elapsed' t oldKey : stack'
  modifyStackRef (StackItem 0 t key :)

pop :: MonadIO m => m ()
pop = do
  StackItem elapsed leftAt key : stack <- readStackRef
  t <- liftIO getCPUTime
  let elapsed' = elapsed + (t - leftAt)
  existing <- liftIO (fromMaybe 0 <$> HT.lookup cumulativeTimes key)
  liftIO $ HT.insert cumulativeTimes key (existing + elapsed')
  case stack of
    [] ->
      return ()
    StackItem oldElapsed _oldLeftAt oldKey : oldStack -> do
      writeStackRef $ StackItem oldElapsed t oldKey : oldStack

report :: IO ()
report = do
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
