

module Main
  ( main
  )
where


import System.Console.Haskeline
import System.Environment
import System.Directory

import Parser
import Evaluator
import TypeChecker
import Language.AbstractSyntax


type Error = String


main :: IO ()
main = do
  args <- getArgs
  if null args
    then runInputT defaultSettings (loop "")
    else do
      bs <- mapM (doesFileExist) args
      if and bs
        then do
          str <- getFiles args
          runInputT defaultSettings (loop str)
        else error "not all files exist"
  where
    loop :: String -> InputT IO ()
    loop pre = do
      minput <- getInputLine "Brandon's Interpreter> "
      case minput of
        Nothing     -> return ()
        Just "quit" -> return ()
        Just txt    ->
          case txt of
            ":exit"         -> return ()
            ':':'t':'y':'p':'e':'o':'f':txt' ->
              case computeVal (pre ++ ' ':txt') of
                Left e      -> do outputStrLn e; loop pre
                Right (t,v) -> do outputStrLn $ show t; loop pre
            _       ->
              case computeVal (pre ++ ' ':txt) of
                Left e      -> do outputStrLn e; loop pre
                Right (t,v) -> do outputStrLn $ show v; loop pre

getFiles :: [String] -> IO String
getFiles [] = return ""
getFiles (f:fs) = do
  s <- readFile f
  ss <- getFiles fs
  return $ s ++ ss

computeVal :: String -> Either Main.Error (TypeChecker.Type, Language.AbstractSyntax.Term)
computeVal txt =
  case Parser.parse txt of
    Left e     -> Left $ "Parsing Error:  " ++ show e
    Right term ->
      case TypeChecker.typeof term of
        Left e   -> Left $ "Type Error:  " ++ show e
        Right ty -> return $ (ty, eval term)
