-- Module for the abstract pattern syntax

module Language.Patterns 
  ( Pat(..)
  , PFields(..)
  , countVars
  )
where

-- Patterns
data Pat = PVar   String      -- a, b, c, ...
         | PRec   PFields     -- {}, {a = b}, ...
         | PPair  Pat     Pat -- (a,b)
         | PSucc  Pat         -- succ a   Can only read numbers. It is used to match objects like 1, 2, 3
         | PLeft  Pat         -- Left a
         | PRight Pat         -- Right a
         | PTru               -- True
         | PFls               -- False
         | PUnit              -- ()
         | PZero              -- 0
         | PWild              -- _
         deriving Eq

type PFields = [(String, Pat)]

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
showPat (PVar   s)     = s
showPat (PLeft  p)     = "Left "  ++ show p
showPat (PRight p)     = "Right " ++ show p 
showPat (PSucc  p)     = show $ 1 + toInt p 
showPat (PPair  p1 p2) = "(" ++ show p1 ++ "," ++ show p2 ++ ")"
showPat (PRec   ps)    = "{" ++ showFields ps ++ "}"
showPat PTru           = "True"
showPat PFls           = "False"
showPat PUnit          = "()"
showPat PZero          = "0"
showPat PWild          = "_"

countVars :: Pat -> Int 
countVars (PVar _)    = 1
countVars (PPair a b) = countVars a + countVars b
countVars (PRec fs)   = foldl (+) 0 $ map countVars ps where ps = snd (unzip fs)
countVars (PSucc p)   = countVars p
countVars (PLeft p)   = countVars p
countVars (PRight p)  = countVars p
countVars _           = 0
