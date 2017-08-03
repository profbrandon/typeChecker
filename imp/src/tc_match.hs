
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
tmatch (PCons p1 p2) t             =
  case separate t of
    (_, List a) -> do
      s1 <- tmatch p1 (quantify' (Type a)) 
      s2 <- tmatch p2 t
      return $ s1 ++ s2
    _           -> Nothing
tmatch (PRec ps)  (Type (TRec ts))
  | length ps == length ts         = matchRec ps ts
  | otherwise                      = Nothing
tmatch PTru       t                = tmatch0 (Type Bool) t
tmatch PFls       t                = tmatch0 (Type Bool) t
tmatch PWild      _                = return []
tmatch PUnit      t                = tmatch0 (Type Unit) t
tmatch PZero      t                = tmatch0 (Type Nat) t
tmatch PNil       t                =
  case separate t of
    (_, List _) -> return []
    _           -> Nothing
tmatch (PSucc p)  (Type Nat)       = tmatch p (Type Nat)
tmatch (PSucc p)  t                = tmatch0 (Type Nat) t
tmatch (PLeft p)  t                =
  case separate t of
    (_, Sum a _) -> tmatch p $ quantify' (Type a)
    _            -> Nothing
tmatch (PRight p) t                =
  case separate t of
    (_, Sum _ b) -> tmatch p $ quantify' (Type b)
    _            -> Nothing
tmatch _          _                = Nothing

tmatch0 :: Type -> Type -> Maybe [(String, Type)]
tmatch0 ag t = do
  subs <- findSubs [] t ag
  return subs
