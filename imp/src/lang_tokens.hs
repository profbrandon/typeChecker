-- Lexer

module Language.Tokens
  ( Token(..)
  )
where


data Token = Id      String
           | Lambda
           | Colon
           | Period
           | LParen
           | RParen
           | Comma
           | ForallT
           | Arr
           | LetT
           | In
           | Equ
           | FixT
           | IfT
           | Then
           | Else
           | FstT
           | SndT
           | IsZeroT
           | SuccT
           | PredT
           | TruT
           | FlsT
           | ZeroT
           deriving Show
