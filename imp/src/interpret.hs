

module Main
  ( main
  )
where


import System.Console.Haskeline

import Lexer
import Parser
import Evaluator
import TypeChecker
import Language.AbstractSyntax


type Error = String


main :: IO ()
main = runInputT defaultSettings loop
  where
    loop :: InputT IO ()
    loop = do
      minput <- getInputLine "Brandon's Interpreter> "
      case minput of
        Nothing     -> return ()
        Just "quit" -> return ()
        Just txt    ->
          case txt of
            ":exit"         -> return ()
            ':':'t':'y':'p':'e':'o':'f':txt' ->
              case computeVal txt' of
                Left e      -> do outputStrLn e; loop
                Right (t,v) -> do outputStrLn $ show t; loop
            _       ->
              case computeVal txt of
                Left e      -> do outputStrLn e; loop
                Right (t,v) -> do outputStrLn $ show v; loop

computeVal :: String -> Either Main.Error (TypeChecker.Type, Language.AbstractSyntax.Term)
computeVal txt =
  case Lexer.lex txt of
    Left e     -> Left $ "Lexical Error:  " ++ show e
    Right toks ->
      case Parser.parse toks of
        Left e     -> Left $ "Parsing Error:  " ++ show e
        Right term ->
          case TypeChecker.typeof term of
            Left e   -> Left $ "Type Error:  " ++ show e
            Right ty -> return $ (ty, eval term)
