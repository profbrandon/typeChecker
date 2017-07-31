
module Language.Patterns 
  (Pat(..))
where

data Pat = PVar String
         | PPair Pat Pat
         | PRec [(String, Pat)]
         deriving Eq

instance Show Pat where
  show = showPat

showFields :: [(String, Pat)] -> String
showFields []          = ""
showFields [(s, p)]    = show s ++ " = " ++ show p
showFields ((s, p):xs) = show s ++ " = " ++ show p ++ ", " ++ showFields xs

showPat :: Pat -> String
showPat (PVar s)      = s
showPat (PPair p1 p2) = "(" ++ show p1 ++ "," ++ show p2 ++ ")"
showPat (PRec ps)     = "{" ++ showFields ps ++ "}"