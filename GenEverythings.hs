import System.Environment
import System.Directory
import System.Exit
import Control.Monad
import Data.Maybe
import Data.List

stripSuffix :: (Eq a) => [a] -> [a] -> Maybe [a]
stripSuffix sfx = fmap reverse . stripPrefix (reverse sfx) . reverse

splitOn :: Char -> String -> [String]
splitOn d = foldr go []
  where go :: Char -> [String] -> [String]
        go x acc | d == x = []:acc
        go x (a:acc) = (x:a):acc
        go x [] = [[x]]


type SplitFilePath = [String]

showFP :: Char -> SplitFilePath -> String
showFP c fp = intercalate [c] (reverse fp)

addToFP :: SplitFilePath -> String -> SplitFilePath
addToFP fp dir = dir : fp

-- Given a path to a directory, returns a pair containing the list of all its
--  subdirectories and the list of all agda files it contains
getSubDirsFiles :: SplitFilePath -> IO ([String], [String])
getSubDirsFiles fp = do
  ls <- getDirectoryContents ("./" ++ showFP '/' fp)
  let sub_dirs = filter ('.' `notElem`) ls
      files    = mapMaybe (stripSuffix ".agda") ls
  pure (sub_dirs, files)

-- Given a path to an agda file, returns the list of all files it imports
getImported :: SplitFilePath -> IO [SplitFilePath]
getImported fp = do
  ls <- fmap words . lines <$> readFile ("./" ++ showFP '/' fp ++ ".agda")
  pure $ fmap (reverse . splitOn '.') (mapMaybe f ls)
  where f :: [String] -> Maybe String
        f ("open":"import":x:_) = Just x
        f ("import":x:_) = Just x
        f _ = Nothing

-- Given a path to a directory $fp and a path to an agda file $fileToCheck.agda,
--  returns the list of all files in* $fp not imported in $fileToCheck.agda
-- * recursively
getMissingFiles :: SplitFilePath -> Maybe SplitFilePath -> IO [SplitFilePath]
getMissingFiles fp fpToCheck = do
  (sub_dirs, sub_files) <- getSubDirsFiles fp
  -- recursively get all files in $fp/X not imported in $fp/X.agda (if it exists)
  missing_files <- concat <$> forM sub_dirs (\sub_dir ->
    getMissingFiles (addToFP fp sub_dir)
                    (addToFP fp <$> (find (== sub_dir) sub_files)))
  -- return all of these files, plus all agda files in the current directory,
  --  except for those which are imported in $fpToCheck.agda (if it exists) or
  --  which are $fpToCheck.agda itself
  imported <- maybe (pure []) getImported fpToCheck
  pure $ ((addToFP fp <$> sub_files) ++ missing_files)
         \\ (maybeToList fpToCheck ++ imported)


checkEverythings :: [String] -> IO ()
checkEverythings excluded_dirs = do
  all_dirs <- filter ('.' `notElem`) <$> getDirectoryContents "./Cubical"
  let dirs = all_dirs \\ excluded_dirs
  missing_files <- concat <$> forM dirs (\dir ->
    getMissingFiles [dir,"Cubical"] (Just ["Everything",dir,"Cubical"]))
  if null missing_files then pure ()
  else do putStrLn "Found some files which are not imported in any Everything.agda:"
          forM_ missing_files (putStrLn . (" " ++) . showFP '.')
          exitFailure

checkREADME :: IO ()
checkREADME = do
  (sub_dirs, _) <- getSubDirsFiles ["Cubical"]
  imported <- getImported ["README","Cubical"]
  let missing_files = fmap (\dir -> ["Everything",dir,"Cubical"]) sub_dirs \\ imported
  if null missing_files then pure ()
  else do putStrLn "Found some Everything.agda's which are not imported in README.agda:"
          forM_ missing_files (putStrLn . (" " ++) . showFP '.')
          exitFailure

genEverything :: SplitFilePath -> IO ()
genEverything fp = do
  files <- getMissingFiles fp Nothing
  let ls = ["{-# OPTIONS --cubical --safe #-}",
            "module " ++ showFP '.' (addToFP fp "Everything") ++ " where", []]
           ++ sort (fmap (\file -> "import " ++ showFP '.' file)
                         (delete (addToFP fp "Everything") files))
  writeFile ("./" ++ showFP '/' (addToFP fp "Everything") ++ ".agda") (unlines ls)

genEverythings :: [String] -> IO ()
genEverythings excluded_dirs = do
  all_dirs <- filter ('.' `notElem`) <$> getDirectoryContents "./Cubical"
  forM_ (all_dirs \\ excluded_dirs)
        (genEverything . addToFP ["Cubical"])


main :: IO ()
main = do
  args <- getArgs
  case args of
    "check":exs -> checkEverythings exs
    "gen"  :exs -> genEverythings   exs
    ["checkREADME"] -> checkREADME
    ["genOne",dir] -> genEverything (addToFP ["Cubical"] dir)
    _ -> putStrLn "error: run with arguments (check | gen) [list of exclued files]"
