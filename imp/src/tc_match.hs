
module TypeChecker.PatternMatching
  (tmatch)
where

import TypeChecker.Types
import TypeChecker.UniversalQuantifiers.Utils
import Language.Patterns

matchRec :: [(String, Pat)] -> [(String, Type)] -> Maybe [(String, Type)]
matchRec [] [] = return []
matchRec ((s1, p):ps) ((s2, t):ts) =
  if s1 == s2
    then do
      subs1 <- tmatch p t
      subs2 <- matchRec ps ts
      return $ subs1 ++ subs2
    else Nothing

-- Performs pattern matching against types
tmatch :: Pat -> Type -> Maybe [(String, Type)]
tmatch (PVar s)      t             = return [(s, t)]
tmatch (PPair p1 p2) t             = 
  case separate t of
    (_, TPair a b) -> do
      s1 <- tmatch p1 (quantify' (Type a))
      s2 <- tmatch p2 (quantify' (Type b))
      return $ s1 ++ s2
    _ -> Nothing
tmatch (PRec ps)  (Type (TRec ts))
  | length ps == length ts         = matchRec ps ts
  | otherwise                      = Nothing
tmatch PTru       (Type Bool)      = return []
tmatch PFls       (Type Bool)      = return []
tmatch PWild      _                = return []
tmatch PUnit      (Type Unit)      = return []
tmatch PZero      (Type Nat)       = return []
tmatch (PSucc p)  (Type Nat)       = tmatch p (Type Nat)
tmatch (PLeft p)  (Type (Sum t _)) = tmatch p (Type t)
tmatch (PRight p) (Type (Sum _ t)) = tmatch p (Type t)
tmatch _          _                = Nothing
