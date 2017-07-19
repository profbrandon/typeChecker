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
           | ForallT
           | Arr
           | FixT
           | IfT
           | Then
           | Else
           | IsZeroT
           | SuccT
           | PredT
           | TruT
           | FlsT
           | ZeroT
           deriving Show
