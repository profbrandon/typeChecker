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
           | EOT

instance Show Token where
  show = showToken True

angBrak :: String -> String
angBrak s = "<" ++ s ++ ">"

showToken0 :: Token -> String
showToken0 (Id s)  = s
showToken0 Lambda  = "\\"
showToken0 Colon   = ":"
showToken0 Period  = "."
showToken0 LParen  = "("
showToken0 RParen  = ")"
showToken0 Comma   = ","
showToken0 ForallT = "forall"
showToken0 Arr     = "->"
showToken0 LetT    = "let"
showToken0 In      = "in"
showToken0 Equ     = "="
showToken0 FixT    = "fix"
showToken0 IfT     = "if"
showToken0 Then    = "then"
showToken0 Else    = "else"
showToken0 FstT    = "fst"
showToken0 SndT    = "snd"
showToken0 IsZeroT = "iszero"
showToken0 SuccT   = "succ"
showToken0 PredT   = "pred"
showToken0 TruT    = "True"
showToken0 FlsT    = "False"
showToken0 ZeroT   = "0"
showToken0 EOT     = "End of Text"

showToken :: Bool -> Token -> String
showToken True  = angBrak . showToken0
showToken False = showToken0
