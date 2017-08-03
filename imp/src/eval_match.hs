
module Evaluator.PatternMatching
  (match)
where

import Language.Patterns(Pat(..))
import Language.AbstractSyntax(Term(..))

-- Pattern matches record fields
matchRec :: [(String, Pat)] -> [(String, Term)] -> Maybe [(String, Term)]
matchRec [] []                     = return []
matchRec ((s1, p):ps) ((s2, t):fs) = 
  if s1 == s2
    then do
      subs1 <- match p t
      subs2 <- matchRec ps fs
      return $ subs1 ++ subs2
    else Nothing

-- Pattern matches expressions, returning a list of variable substitutions on success
  -- e.g., match (a,b) (1,2) = [("a",1),("b",2)]
match :: Pat -> Term -> Maybe [(String, Term)]
match (PPair p1 p2) (Pair t1 t2 _) = do
  subs1 <- match p1 t1
  subs2 <- match p2 t2
  return $ subs1 ++ subs2
match (PRec ps)     (Record fs _)
  | length ps == length fs         = matchRec ps fs
  | otherwise                      = Nothing
match (PVar   s)    t              = return [(s, t)]
match (PSucc  p)    (Succ   e _)   = match p e
match (PLeft  p)    (ELeft  e _ _) = match p e
match (PRight p)    (ERight e _ _) = match p e
match PTru          (Tru _)        = return []
match PFls          (Fls _)        = return []
match PUnit         (EUnit _)      = return []
match PZero         (Zero  _)      = return []
match PWild         _              = return []
match _             _              = Nothing
