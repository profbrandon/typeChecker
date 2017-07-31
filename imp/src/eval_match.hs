
module Evaluator.PatternMatching
  (match)
where

import Language.Patterns
import Language.AbstractSyntax

matchRec :: [(String, Pat)] -> [(String, Term)] -> Maybe [(String, Term)]
matchRec [] []                     = return []
matchRec ((s1, p):ps) ((s2, t):fs) = 
  if s1 == s2
    then do
      subs1 <- match p t
      subs2 <- matchRec ps fs
      return $ subs1 `union` subs2
    else Nothing

match :: Pat -> Term -> Maybe [(String, Term)]
match (PVar s)      t              = return [(s, t)]
match (PPair p1 p2) (Pair t1 t2 _) = do
  s1 <- match p1 t1
  s2 <- match p2 t2
  return $ s1 `union` s2
match (PRec ps)     (Record fs _)
  | length ps == length fs = matchRec ps fs
  | otherwise = Nothing
match _             _            = Nothing