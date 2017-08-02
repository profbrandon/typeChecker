
module Evaluator

where

import Language.AbstractSyntax
import Language.Patterns
import Evaluator.PatternMatching
import TypeChecker.Types
import Text.Parsec.Pos


-- Evaluation

-- Shift nameless terms by "d" above cutoff "c" in the term provided
shiftnl :: Int -> Int -> Term -> Term
shiftnl d c (Abs s ty t pos)  = Abs s ty (shiftnl d (c + 1) t) pos
shiftnl d c (App t1 t2 pos)   = App (shiftnl d c t1) (shiftnl d c t2) pos
shiftnl d c (Var k pos)       = Var (if k < c then k else (k + d)) pos
shiftnl d c (Record ts pos)   =
  let sh ts = case ts of
        []     -> []
        ((ss, t):ts) -> (ss, t'):(sh ts) where t' = shiftnl d c t
  in Record (sh ts) pos
shiftnl d c (Proj t s pos)    = Proj (shiftnl d c t) s pos
shiftnl d c (Pair t1 t2 pos)  = Pair (shiftnl d c t1) (shiftnl d c t2) pos
shiftnl d c (Fix t pos)       = Fix (shiftnl d c t) pos
shiftnl d c (Let p t1 t2 pos) = Let p (shiftnl d c t1) (shiftnl d (c + l) t2) pos where l = countVars p
shiftnl d c (Case t bs pos)   = 
  let br bs = case bs of
        [(p, t1)] -> [(p, shiftnl d (c + 1) t1)] where l = countVars p 
        ((p, t1):bs') -> (p, shiftnl d (c + l) t1):br bs' where l = countVars p
  in Case (shiftnl d c t) (br bs) pos
shiftnl d c (If t1 t2 t3 pos) = If (sh t1) (sh t2) (sh t3) pos where sh = shiftnl d c
shiftnl d c (Fst t pos)       = Fst (shiftnl d c t) pos
shiftnl d c (Snd t pos)       = Snd (shiftnl d c t) pos
shiftnl d c (Succ t pos)      = Succ (shiftnl d c t) pos
shiftnl d c (Pred t pos)      = Pred (shiftnl d c t) pos
shiftnl d c (IsZero t pos)    = IsZero (shiftnl d c t) pos
shiftnl _ _ t                 = t

-- Preforms variable substitution in branches
subBranches :: Int -> Term -> Branches -> Branches
subBranches j s [(p, t)] = [(p, sub j s t)]
subBranches j s ((p, t):bs) = (p, sub j s t):bs' where bs' = subBranches j s bs

sub :: Int -> Term -> Term -> Term
sub j s (Abs ss ty t pos)  = Abs ss ty t' pos where t' = sub (j + 1) (shiftnl 1 0 s) t
sub j s (App t1 t2 pos)    = App (sub j s t1) (sub j s t2) pos
sub j s (Var i pos)        = if i == j then s else (Var i) pos
sub j s (Record ts pos)    =
  let su ts = case ts of
        []     -> []
        ((ss, t):ts) -> (ss, t'):(su ts) where t' = sub j s t
  in Record (su ts) pos
sub j s (Proj t ss pos)    = Proj (sub j s t) ss pos
sub j s (Pair t1 t2 pos)   = Pair (sub j s t1) (sub j s t2) pos
sub j s (Fix t pos)        = Fix (sub j s t) pos
sub j s (Let p t1 t2 pos)  = Let p (sub j s t1) (sub (j + l) (shiftnl l 0 s) t2) pos where l = countVars p
sub j s (Case t bs pos)    = Case (sub j s t) (subBranches j s bs) pos
sub j s (If t1 t2 t3 pos)  = If (sb t1) (sb t2) (sb t3) pos where sb = sub j s
sub j s (Fst t pos)        = Fst (sub j s t) pos
sub j s (Snd t pos)        = Snd (sub j s t) pos
sub j s (Succ t pos)       = Succ (sub j s t) pos
sub j s (Pred t pos)       = Pred (sub j s t) pos
sub j s (IsZero t pos)     = IsZero (sub j s t) pos
sub _ _ t                  = t

-- Substitutes patterns
subPats :: [(String, Term)] -> Term -> Term
subPats [] t           = t
subPats ((_, t):xs) te = subPats xs te' where te' = sub (length xs) t te

-- Evaluates branches of case expressions
evalBranches :: Term -> Branches -> SourcePos -> Term
evalBranches t [(p, e)] pos =
  let msubs = match p t
  in case msubs of
    Nothing   -> error $ "non-exhaustive patterns in case expression at " ++ show pos
    Just subs -> subPats subs e
evalBranches t ((p, e):bs) pos =
  let msubs = match p t
  in case msubs of
    Nothing   -> evalBranches t bs pos
    Just subs -> subPats subs e

eval1 :: Term -> Maybe Term
eval1 (Abs s ty t pos)            = do
  t' <- eval1 t
  return $ Abs s ty t' pos
eval1 (App (Abs s ty t11 pos1) t2 pos2) = return $ shiftnl (-1) 0 $ sub 0 (shiftnl 1 0 t2) t11
eval1 (App t1 t2 pos)              = do
  t1' <- eval1 t1
  return $ App t1' t2 pos
eval1 (Let p t1 t2 pos)            =
  if isValue t1
    then let msubs = match p t1
      in case msubs of
        Nothing   -> error $ "error in pattern matching:  " ++ show pos
        Just subs -> return $ subPats subs t2 where l = length subs
    else do
      t1' <- eval1 t1
      return $ Let p t1' t2 pos
eval1 (Case t bs pos)              =
  if isValue t
    then return $ evalBranches t bs pos
    else do
      t' <- eval1 t
      return $ Case t' bs pos
eval1 (Record fs pos)              =
  let fields fs = case fs of
        []      -> Nothing
        ((s, t):fs0) -> do
          let t' = eval t
          fs0' <- fields fs0
          return $ (s, t'):fs0'
  in do
    fs' <- fields fs
    return $ Record fs' pos
eval1 (Proj t s pos)               =
  if isValue t
    then case t of
      Record fs _ ->
        case s `lookup` fs of
          Nothing -> error $ "field \'" ++ s ++ "\' not a member of record:  " ++ show pos
          Just tt -> return tt
      _         -> error $ "record not provided to projection:  " ++ show pos
    else do
      t' <- eval1 t
      return $ Proj t' s pos
eval1 (Pair t1 t2 pos)             = do
  if isValue t1
    then do
      t2' <- eval1 t2
      return $ Pair t1 t2' pos
    else do
      t1' <- eval1 t1
      return $ Pair t1' t2 pos
eval1 (Fix (Abs s ty t pos1) pos2) = return $ shiftnl (-1) 0 $ sub 0 (shiftnl 1 0 $ Fix (Abs s ty t pos1) pos2) t
eval1 (Fix t pos)                  = do
  t' <- eval1 t
  return $ Fix t' pos
eval1 (If (Tru _) t2 t3 _)        = Just t2
eval1 (If (Fls _) t2 t3 _)        = Just t3
eval1 (If t1 t2 t3 pos)           = do
  t1' <- eval1 t1
  return $ If t1' t2 t3 pos
eval1 (Fst (Pair t1 t2 _) _)      = Just t1
eval1 (Fst t pos)                 = do
  t' <- eval1 t
  return $ Fst t' pos
eval1 (Snd (Pair t1 t2 _) _)      = Just t2
eval1 (Snd t pos)                 = do
  t' <- eval1 t
  return $ Snd t' pos
eval1 (Succ (Pred t _) pos)       = Just t
eval1 (Succ t pos)                = do
  t' <- eval1 t
  return $ Succ t' pos
eval1 (Pred (Zero _) pos)         = Just $ Zero pos
eval1 (Pred (Succ t _) pos)       = Just t
eval1 (Pred t pos)                = do
  t' <- eval1 t
  return $ Pred t' pos
eval1 (IsZero (Zero _) pos)       = Just $ Tru pos
eval1 (IsZero (Succ t _) pos)     = Just $ Fls pos
eval1 (IsZero t pos)              = do
  t' <- eval1 t
  return $ IsZero t' pos
eval1 _                           = Nothing

eval :: Term -> Term
eval t =
  let ev = eval1 t
  in case ev of
    Nothing -> t
    Just t' -> eval t'
