-- Module for the abstract pattern syntax

module Language.Patterns 
  ( Pat(..)
  , countVars )
where

-- Patterns
data Pat = PVar String
         | PPair Pat Pat
         | PRec [(String, Pat)]
         | PLeft Pat
         | PRight Pat
         | PTru
         | PFls
         | PWild
         | PUnit
         | PZero
         | PSucc Pat
         deriving Eq

instance Show Pat where
  show = showPat

showFields :: [(String, Pat)] -> String
showFields []          = ""
showFields [(s, p)]    = show s ++ " = " ++ show p
showFields ((s, p):xs) = show s ++ " = " ++ show p ++ ", " ++ showFields xs

toInt :: Pat -> Int
toInt PZero     = 0
toInt (PSucc p) = 1 + (toInt p)
toInt _         = error "Non-numeric argument supplied to function 'toInt'"

showPat :: Pat -> String
showPat (PVar s)      = s
showPat PTru          = "True"
showPat PFls          = "False"
showPat PWild         = "_"
showPat PUnit         = "()"
showPat PZero         = "0"
showPat (PLeft p)     = "Left " ++ show p
showPat (PRight p)    = "Right " ++ show p 
showPat (PSucc p)
  | countVars p == 0  = show $ 1 + toInt p
  | otherwise         = "succ (" ++ show p ++ ")" 
showPat (PPair p1 p2) = "(" ++ show p1 ++ "," ++ show p2 ++ ")"
showPat (PRec ps)     = "{" ++ showFields ps ++ "}"

countVars :: Pat -> Int 
countVars (PVar _)    = 1
countVars (PPair a b) = countVars a + countVars b
countVars (PRec fs)   = foldl (+) 0 $ map countVars ps where ps = snd (unzip fs)
countVars (PSucc p)   = countVars p
countVars (PLeft p)   = countVars p
countVars (PRight p)  = countVars p
countVars _           = 0
