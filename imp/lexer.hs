-- Lexer

module Lexer
  ( Token(..)
  , Error(..)
  , lex
  )
where


import Data.Char (isSpace, isAlphaNum)
import Prelude hiding (lex)
import Language.Tokens


data Error = UnrecognizedToken

instance Show Error where
  show e = "Unrecognized token in input stream"


left :: (a -> c) -> (a, b) -> (c, b)
left f (a, b) = (f a, b)

right :: (b -> c) -> (a, b) -> (a, c)
right f (a, b) = (a, f b)

identifier :: String -> (String, String)
identifier [] = ([], [])
identifier (c:cs)
  | isAlphaNum c = left (c:) $ identifier cs
  | otherwise = ([], (c:cs))

lex :: String -> Either Error [Token]
lex [] = return []
lex (c:cs)
  | isSpace c = lex cs
  | otherwise =
    case c of
      '\\' -> a1 Lambda
      '.'  -> a1 Period
      ':'  -> a1 Colon 
      '('  -> a1 LParen
      ')'  -> a1 RParen
      '0'  -> a1 ZeroT 
      '-'  ->
        case cs of
          '>':cs' -> ap Arr cs'
          _       -> Left UnrecognizedToken
      _    ->
        case name of
          ""       -> Left UnrecognizedToken
          "forall" -> a2 ForallT
          "fix"    -> a2 FixT
          "if"     -> a2 IfT
          "then"   -> a2 Then
          "else"   -> a2 Else
          "iszero" -> a2 IsZeroT
          "succ"   -> a2 SuccT
          "pred"   -> a2 PredT
          "True"   -> a2 TruT
          "False"  -> a2 FlsT
          _        -> a2 (Id name)
        where (name, back) = identifier (c:cs)
              a2 l         = ap l back
    where ap l b = do b' <- lex b; return $ l:b'
          a1 l   = ap l cs
