module Timing (push, pop, report) where

import           Data.IORef                       (IORef, newIORef, writeIORef, readIORef, modifyIORef)
import qualified Data.HashTable.IO                as HT
import           System.IO.Unsafe                 (unsafePerformIO)
import           System.CPUTime                   (getCPUTime)
import qualified Text.PrettyPrint.Boxes           as Boxes
import           Data.Functor                     ((<$>))
import           Data.Maybe                       (fromMaybe)
import           Data.List                        (sortBy)
import           Data.Ord                         (comparing)
import           Data.Ratio                       ((%))
import           Text.Printf                      (printf)
import           Control.Monad.IO.Class           (MonadIO, liftIO)

type Key = String

{-# NOINLINE cumulativeTimes #-}
cumulativeTimes :: HT.CuckooHashTable Key Integer
cumulativeTimes = unsafePerformIO HT.new

data StackItem = StackItem
  { siElapsed :: Integer
  , siLeftAt  :: Integer
  , siKey     :: Key
  }

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

push :: MonadIO m => Key -> m ()
push key = do
  stack <- readStackRef
  t <- liftIO getCPUTime
  case stack of
    [] ->
      return ()
    (StackItem elapsed leftAt oldKey : stack) -> do
      let elapsed' = elapsed + (t - leftAt)
      writeStackRef $ StackItem elapsed' t oldKey : stack
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
    StackItem oldElapsed oldLeftAt oldKey : oldStack -> do
      writeStackRef $ StackItem oldElapsed t oldKey : oldStack

-- section :: String -> IO ()
-- section label = do
--   t <- getCPUTime
--   mbCurrent <- readIORef currentTimer
--   forM_ mbCurrent $ \(oldLabel, t0) -> do
--     existing <- fromMaybe 0 <$> HT.lookup timersTable oldLabel
--     HT.insert timersTable oldLabel (existing + (t - t0))
--   t' <- getCPUTime
--   writeIORef currentTimer $ Just (label, t')

report :: IO ()
report = do
  kvs <- reverse . sortBy (comparing snd) <$> HT.toList cumulativeTimes
  let total  = sum $ map snd kvs
  let perc n = printf "%.4f%%" $ (fromRational ((n * 100) % total) :: Double) :: String
  let vcatl  = Boxes.vcat Boxes.left
  let vcatr  = Boxes.vcat Boxes.right
  let (<+>)  = (Boxes.<+>)
  let box    = (\(x, y, z) -> vcatl x <+> vcatr y <+> vcatr z) $ unzip3
               [ (Boxes.text label, Boxes.text (show t), Boxes.text (perc t))
               | (label, t) <- kvs
               ]
  putStrLn "------------------------------------------------------------------------"
  putStrLn $ "-- Timing report"
  putStrLn "------------------------------------------------------------------------"
  putStrLn $ Boxes.render box
