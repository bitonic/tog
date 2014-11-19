module Timing (section, report) where

import           Data.IORef                       (IORef, newIORef, writeIORef, readIORef)
import qualified Data.HashTable.IO                as HT
import           System.IO.Unsafe                 (unsafePerformIO)
import           System.CPUTime                   (getCPUTime)
import qualified Text.PrettyPrint.Boxes           as Boxes
import           Data.Foldable                    (forM_)
import           Data.Functor                     ((<$>))
import           Data.Maybe                       (fromMaybe)
import           Data.List                        (sortBy)
import           Data.Ord                         (comparing)
import           Data.Ratio                       ((%))
import           Text.Printf                      (printf)

{-# NOINLINE timersTable #-}
timersTable :: HT.CuckooHashTable String Integer
timersTable = unsafePerformIO HT.new

{-# NOINLINE currentTimer #-}
currentTimer :: IORef (Maybe (String, Integer))
currentTimer = unsafePerformIO $ newIORef Nothing

section :: String -> IO ()
section label = do
  t <- getCPUTime
  mbCurrent <- readIORef currentTimer
  forM_ mbCurrent $ \(oldLabel, t0) -> do
    existing <- fromMaybe 0 <$> HT.lookup timersTable oldLabel
    HT.insert timersTable oldLabel (existing + (t - t0))
  t' <- getCPUTime
  writeIORef currentTimer $ Just (label, t')

report :: IO ()
report = do
  kvs <- reverse . sortBy (comparing snd) <$> HT.toList timersTable
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
