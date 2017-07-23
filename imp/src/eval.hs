
module Evaluator
  ( eval
  )
where

import Language.AbstractSyntax


-- Evaluation

shiftnl :: Int -> Int -> Term -> Term
shiftnl d c (Abs s ty t)  = Abs s ty $ shiftnl d (c + 1) t
shiftnl d c (App t1 t2)   = App (shiftnl d c t1) (shiftnl d c t2)
shiftnl d c (Var k)       = Var $ if k < c then k else (k + d)
shiftnl d c (Pair t1 t2)  = Pair (shiftnl d c t1) (shiftnl d c t2)
shiftnl d c (Fix t)       = Fix $ shiftnl d c t
shiftnl d c (Let s t1 t2) = Let s (shiftnl d c t1) $ shiftnl d (c + 1) t2
shiftnl d c (If t1 t2 t3) = If (sh t1) (sh t2) (sh t3) where sh = shiftnl d c
shiftnl d c (Fst t)       = Fst $ shiftnl d c t
shiftnl d c (Snd t)       = Snd $ shiftnl d c t
shiftnl d c (Succ t)      = Succ $ shiftnl d c t
shiftnl d c (Pred t)      = Pred $ shiftnl d c t
shiftnl d c (IsZero t)    = IsZero $ shiftnl d c t
shiftnl _ _ t             = t

sub :: Int -> Term -> Term -> Term
sub j s (Abs ss ty t)  = Abs ss ty t' where t' = sub (j + 1) (shiftnl 1 0 s) t
sub j s (App t1 t2)    = App (sub j s t1) (sub j s t2)
sub j s (Var i)        = if i == j then s else (Var i)
sub j s (Pair t1 t2)   = Pair (sub j s t1) (sub j s t2)
sub j s (Fix t)        = Fix $ sub j s t
sub j s (Let ss t1 t2) = Let ss (sub j s t1) (sub (j + 1) (shiftnl 1 0 s) t2)
sub j s (If t1 t2 t3)  = If (sb t1) (sb t2) (sb t3) where sb = sub j s
sub j s (Fst t)        = Fst $ sub j s t
sub j s (Snd t)        = Snd $ sub j s t
sub j s (Succ t)       = Succ $ sub j s t
sub j s (Pred t)       = Pred $ sub j s t
sub j s (IsZero t)     = IsZero $ sub j s t
sub _ _ t              = t

eval1 :: Term -> Maybe Term
eval1 (Abs s ty t)            = do
  t' <- eval1 t
  return $ Abs s ty t'
eval1 (App (Abs s ty t11) t2) =
  if isValue t2
    then return $ shiftnl (-1) 0 $ sub 0 (shiftnl 1 0 t2) t11
    else do
      t2' <- eval1 t2
      return $ App (Abs s ty t11) t2'
eval1 (App t1 t2)             = do
  t1' <- eval1 t1
  return $ App t1' t2
eval1 (Let s t1 t2)           =
  if isValue t1
    then return $ shiftnl (-1) 0 $ sub 0 (shiftnl 1 0 t1) t2
    else do
      t1' <- eval1 t1
      return $ Let s t1' t2
eval1 (Pair t1 t2)            =
  if isValue t1
    then do
      t2' <- eval1 t2
      return $ Pair t1 t2'
    else do
      t1' <- eval1 t1
      return $ Pair t1' t2
eval1 (Fix (Abs s ty t))      = return $ shiftnl (-1) 0 $ sub 0 (shiftnl 1 0 $ Fix (Abs s ty t)) t
eval1 (Fix t)                 = do
  t' <- eval1 t
  return $ Fix t
eval1 (If Tru t2 t3)          = Just t2
eval1 (If Fls t2 t3)          = Just t3
eval1 (If t1 t2 t3)           = do
  t1' <- eval1 t1
  return $ If t1' t2 t3
eval1 (Fst (Pair t1 t2))      = Just t1
eval1 (Fst t)                 = do
  t' <- eval1 t
  return $ Fst t'
eval1 (Snd (Pair t1 t2))      = Just t2
eval1 (Snd t)                 = do
  t' <- eval1 t
  return $ Snd t'
eval1 (Succ (Pred t))         = Just t
eval1 (Succ t)                = do
  t' <- eval1 t
  return $ Succ t'
eval1 (Pred Zero)             = Just Zero
eval1 (Pred (Succ t))         = Just t
eval1 (Pred t)                = do
  t' <- eval1 t
  return $ Pred t'
eval1 (IsZero Zero)           = Just Tru
eval1 (IsZero (Succ t))       = Just Fls
eval1 (IsZero t)              = do
  t' <- eval1 t
  return $ IsZero t'
eval1 _                       = Nothing

eval :: Term -> Term
eval t =
  let ev = eval1 t
  in case ev of
    Nothing -> t
    Just t' -> eval t'
