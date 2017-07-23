-- Lexer

module Lexer
  ( Token(..)
  , Error(..)
  , lex
  )
where


import Data.Char (isSpace, isAlphaNum, isDigit)
import Prelude hiding (lex)
import Language.Tokens


data Error = UnrecognizedToken

instance Show Error where
  show e = "Unrecognized token in input stream"


left :: (a -> c) -> (a, b) -> (c, b)
left f (a, b) = (f a, b)

right :: (b -> c) -> (a, b) -> (a, c)
right f (a, b) = (a, f b)

getWhile :: (Char -> Bool) -> String -> (String, String)
getWhile p [] = ([], [])
getWhile p (c:cs)
  | p c       = left (c:) $ getWhile p cs
  | otherwise = ([], (c:cs))

identifier :: String -> (String, String)
identifier = getWhile isAlphaNum

natural :: String -> (String, String)
natural = getWhile isDigit

convertNat :: Int -> [Token]
convertNat 0 = [ZeroT]
convertNat i = SuccT:LParen:ts ++ [RParen] where ts = convertNat $ i - 1

lex :: String -> Either Error [Token]
lex [] = return []
lex (c:cs)
  | isSpace c = lex cs
  | isDigit c = do
    let (num, back) = natural (c:cs)
    let ts          = LParen:convertNat (read num :: Int) ++ [RParen]
    b <- lex back
    return $ ts ++ b 
  | otherwise =
    case c of
      '\\' -> a1 Lambda
      '.'  -> a1 Period
      ':'  -> a1 Colon 
      '('  -> a1 LParen
      ')'  -> a1 RParen
      '='  -> a1 Equ
      ','  -> a1 Comma
      '-'  ->
        case cs of
          '>':cs' -> ap Arr cs'
          _       -> Left UnrecognizedToken
      _    ->
        case name of
          ""       -> Left UnrecognizedToken
          "forall" -> a2 ForallT
          "let"    -> a2 LetT
          "in"     -> a2 In
          "fix"    -> a2 FixT
          "if"     -> a2 IfT
          "then"   -> a2 Then
          "else"   -> a2 Else
          "fst"    -> a2 FstT
          "snd"    -> a2 SndT
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
