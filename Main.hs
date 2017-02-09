module Main where

import JackCompiler (rootCompile)
import JackParser (parse, parseClass)
import VMCode (toVMFile)
import System.Directory
import System.Environment
import System.Exit
import System.FilePath
import System.IO

failWithMessage :: String -> IO ()
failWithMessage message = do
  hPutStrLn stderr message
  exitFailure

removeEnd :: Eq a => [a] -> [a] -> Maybe [a]
removeEnd ending list =
  if ending == list then
    Just []
  else
    if list == [] then
      Nothing
    else
      let
        first : remaining = list
        removeEndRemaining = removeEnd ending remaining
      in
        fmap (first :) removeEndRemaining

vmExtension :: String
vmExtension = ".vm"
jackExtension :: String
jackExtension = ".jack"

compileJackFile :: String -> IO ()
compileJackFile fileName = do
  contents <- readFile fileName
  if isJackFile fileName then
    case parse parseClass contents of
      Nothing ->
       failWithMessage ("Could not parse " ++ fileName)
      Just (jackClass, _) ->
        let
          vmFile = replaceExtension fileName vmExtension
          vmString = toVMFile (rootCompile jackClass)
        in
          writeFile vmFile vmString
  else
    failWithMessage "File is not a jack file"

isJackFile :: String -> Bool
isJackFile = (jackExtension ==) . takeExtension

main :: IO ()
main = do
  args <- getArgs
  case args of
    [path] -> do
      isFile <- doesFileExist path
      if isFile then
        compileJackFile path
      else do --project directory
        jackFiles <-
          fmap
            (map (path </>) . filter isJackFile)
            (getDirectoryContents path)
        mapM_ compileJackFile jackFiles
    _ ->
     failWithMessage "Syntax: ./Main JackClass.jack OR ./Main JackProjectDir"