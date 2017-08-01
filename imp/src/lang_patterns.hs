
module Language.Patterns 
  ( Pat(..)
  , countVars)
where

data Pat = PVar String
         | PPair Pat Pat
         | PRec [(String, Pat)]
         | PTru
         | PFls
         deriving Eq

instance Show Pat where
  show = showPat

showFields :: [(String, Pat)] -> String
showFields []          = ""
showFields [(s, p)]    = show s ++ " = " ++ show p
showFields ((s, p):xs) = show s ++ " = " ++ show p ++ ", " ++ showFields xs

showPat :: Pat -> String
showPat (PVar s)      = s
showPat PTru          = "True"
showPat PFls          = "False"
showPat (PPair p1 p2) = "(" ++ show p1 ++ "," ++ show p2 ++ ")"
showPat (PRec ps)     = "{" ++ showFields ps ++ "}"

countVars :: Pat -> Int 
countVars (PVar _) = 1
countVars (PPair a b) = countVars a + countVars b
countVars (PRec fs) = foldl (+) 0 $ map countVars ps where ps = snd (unzip fs)
countVars _ = 0
