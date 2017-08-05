
module Evaluator

where

import Debug.Trace
import Text.Parsec.Pos(SourcePos(..))

import Language.AbstractSyntax(Term(..), Branches(..), VContext(..), pushBinding, isValue)
import Language.Patterns(countVars)
import Evaluator.PatternMatching(match)
import TypeChecker(typeof0)
import TypeChecker.Utils(nilmap)
import TypeChecker.Types(Type(..))
import TypeChecker.UniversalQuantifiers.Utils(findSubs, substituteAll)


-- Evaluation

-- Shift nameless terms by "d" above cutoff "c" in the term provided
shiftnl :: Int -> Int -> Term -> Term
shiftnl d c (Var k        pos) = Var    (if k < c then k else (k + d)) pos
shiftnl d c (App t1 t2    pos) = App    (shiftnl d c t1) (shiftnl d c t2) pos
shiftnl d c (Abs s  ty t  pos) = Abs s ty (shiftnl d (c + 1) t) pos
shiftnl d c (If  t1 t2 t3 pos) = If     (sh t1) (sh t2) (sh t3) pos                 where sh = shiftnl d c
shiftnl d c (Let p  t1 t2 pos) = Let p  (shiftnl d c t1) (shiftnl d (c + l) t2) pos where l = countVars p
shiftnl d c (Case   t  bs pos) = Case   (shiftnl d c t)  (map shift bs)         pos where shift = \(p, e) -> (p, shiftnl d (c + countVars p) e)
shiftnl d c (Proj   t  s  pos) = Proj   (shiftnl d c t) s pos
shiftnl d c (Record fs    pos) = Record (map shift fs) pos                          where shift = \(s, f) -> (s, shiftnl d c f) 
shiftnl d c (Pair   t1 t2 pos) = Pair   (shiftnl d c t1) (shiftnl d c t2) pos
shiftnl d c (ELeft  t  ty pos) = ELeft  (shiftnl d c t) ty pos
shiftnl d c (ERight t  ty pos) = ERight (shiftnl d c t) ty pos
shiftnl d c (Fix    t     pos) = Fix    (shiftnl d c t) pos
shiftnl d c (Fst    t     pos) = Fst    (shiftnl d c t) pos
shiftnl d c (Snd    t     pos) = Snd    (shiftnl d c t) pos
shiftnl d c (Succ   t     pos) = Succ   (shiftnl d c t) pos
shiftnl d c (Pred   t     pos) = Pred   (shiftnl d c t) pos
shiftnl d c (IsZero t     pos) = IsZero (shiftnl d c t) pos
shiftnl d c (Cons   t  ts pos) = Cons   (shiftnl d c t) (shiftnl d c ts) pos
shiftnl _ _ t                  = t

-- Preforms variable substitution in branches
sub :: Int -> Term -> Term -> Term
sub j s (Var  i        pos) = if i == j then s else (Var i) pos
sub j s (App  t1 t2    pos) = App    (sub j s t1) (sub j s t2) pos
sub j s (Abs  n  ty t  pos) = Abs    n ty t' pos                                       where t' = sub (j + 1) (shiftnl 1 0 s) t
sub j s (If   t1 t2 t3 pos) = If     (sb t1) (sb t2) (sb t3) pos                       where sb = sub j s
sub j s (Let  p  t1 t2 pos) = Let p  (sub j s t1) (sub (j + l) (shiftnl l 0 s) t2) pos where l = countVars p
sub j s (Case t  bs    pos) = Case   (sub j s t) (map su bs) pos                       where su = \(p, e) -> let l = countVars p in (p, sub (j + l) (shiftnl l 0 s) e)
sub j s (Proj t  ss    pos) = Proj   (sub j s t) ss pos
sub j s (Record  ts    pos) = Record (map su ts) pos                                   where su = \(n, f) -> (n, sub j s f)
sub j s (Pair t1 t2    pos) = Pair   (sub j s t1) (sub j s t2) pos
sub j s (Cons t  ts    pos) = Cons   (sub j s t) (sub j s ts)  pos
sub j s (ELeft   t ty  pos) = ELeft  (sub j s t) ty pos
sub j s (ERight  t ty  pos) = ERight (sub j s t) ty pos
sub j s (Fix     t     pos) = Fix    (sub j s t) pos
sub j s (Fst     t     pos) = Fst    (sub j s t) pos
sub j s (Snd     t     pos) = Snd    (sub j s t) pos
sub j s (Succ    t     pos) = Succ   (sub j s t) pos
sub j s (Pred    t     pos) = Pred   (sub j s t) pos
sub j s (IsZero  t     pos) = IsZero (sub j s t) pos
sub _ _ t                   = t

-- Performs substitution in type annotations
subType :: [(String, Type)] -> Term -> Term
subType []   t                  = t
subType subs (Abs s  ty t  pos) = Abs s   ty' t'  pos where ty' = substituteAll subs ty; t' = subType subs t
subType subs (ELeft  t  ty pos) = ELeft   t'  ty' pos where ty' = substituteAll subs ty; t' = subType subs t
subType subs (ERight t  ty pos) = ERight  t'  ty' pos where ty' = substituteAll subs ty; t' = subType subs t
subType subs (App t1 t2    pos) = App t1' t2'     pos where t1' = subType subs t1; t2' = subType subs t2
subType subs (If  t1 t2 t3 pos) = If  t1' t2' t3' pos where [t1',t2',t3'] = map (subType subs) [t1,t2,t3]
subType subs (Let p  t1 t2 pos) = Let p   t1' t2' pos where t1' = subType subs t1; t2' = subType subs t2
subType subs (Case   t  bs pos) = Case    t'  (map stb bs) pos where t' = subType subs t; stb = \(p, e) -> (p, subType subs e)
subType subs (Proj   t  s  pos) = Proj    t'  s   pos where t' = subType subs t
subType subs (Pair   t1 t2 pos) = Pair    t1' t2' pos where [t1',t2'] = map (subType subs) [t1,t2]
subType subs (Cons   t  ts pos) = Cons    t'  ts' pos where t' = subType subs t; ts' = subType subs ts
subType subs (Fix    t     pos) = Fix     t'      pos where t' = subType subs t
subType subs (Fst    t     pos) = Fst     t'      pos where t' = subType subs t
subType subs (Snd    t     pos) = Snd     t'      pos where t' = subType subs t
subType subs (Succ   t     pos) = Succ    t'      pos where t' = subType subs t
subType subs (Pred   t     pos) = Succ    t'      pos where t' = subType subs t
subType subs (IsZero t     pos) = IsZero  t'      pos where t' = subType subs t
subType _    t                  = t

-- Substitutes patterns
subPats :: [(String, Term)] -> Term -> Term
subPats [] t           = t
subPats ((_, t):xs) te = subPats xs te' where te' = sub (length xs) t te

-- Evaluates branches of case expressions
evalBranches :: Term -> Branches -> SourcePos -> Term
evalBranches t [(p, e)] pos =
  case match p t of
    Nothing   -> error $ "non-exhaustive patterns in case expression at " ++ show pos
    Just subs -> subPats subs e
evalBranches t ((p, e):bs) pos =
  case match p t of
    Nothing   -> evalBranches t bs pos
    Just subs -> subPats subs e

eval1 :: VContext -> Term -> Maybe Term
eval1 ctx (Abs s ty t pos)            = do
  t' <- eval1 ctx' t
  return $ Abs s ty t' pos
  where ctx' = pushBinding ctx (s, ty)
eval1 ctx (App (Abs s ty t11 pos1) t2 pos2) =
  case typeof0 nilmap ctx t2 of
    Left e    -> error $ "Error in type substitution:  " ++ show e
    Right ty2 -> do
      subs <- findSubs [] ty ty2
      let t11' = subType subs t11
      return $ shiftnl (-1) 0 $ sub 0 (shiftnl 1 0 t2) t11'
eval1 ctx (App t1 t2 pos)              = do
  t1' <- eval1 ctx t1
  return $ App t1' t2 pos
eval1 ctx (Let p t1 t2 pos)            =
  if isValue t1
    then let msubs = match p t1
      in case msubs of
        Nothing   -> error $ "error in matching the pattern " ++ show p ++ " with the term " ++ show t1 ++ " at " ++ show pos
        Just subs -> return $ subPats subs t2 where l = length subs
    else do
      t1' <- eval1 ctx t1
      return $ Let p t1' t2 pos
eval1 ctx (Case t bs pos)              =
  if isValue t
    then return $ evalBranches t bs pos
    else do
      t' <- eval1 ctx t
      return $ Case t' bs pos
eval1 ctx (Record fs pos)              =
  let fields fs = case fs of
        []      -> Nothing
        ((s, t):fs0) ->
          if isValue t
            then do
              fs0' <- fields fs0
              return $ (s, t):fs0'
            else do
              t' <- eval1 ctx t
              return $ (s, t'):fs0
  in do
    fs' <- fields fs
    return $ Record fs' pos
eval1 ctx (Proj t s pos)               =
  if isValue t
    then case t of
      Record fs _ ->
        case s `lookup` fs of
          Nothing -> error $ "field \'" ++ s ++ "\' not a member of record:  " ++ show pos
          Just tt -> return tt
      _         -> error $ "record not provided to projection:  " ++ show pos
    else do
      t' <- eval1 ctx t
      return $ Proj t' s pos
eval1 ctx (Pair t1 t2 pos)             = do
  if isValue t1
    then do
      t2' <- eval1 ctx t2
      return $ Pair t1 t2' pos
    else do
      t1' <- eval1 ctx t1
      return $ Pair t1' t2 pos
eval1 ctx (Fix (Abs s ty t pos1) pos2) = return $ shiftnl (-1) 0 $ sub 0 (shiftnl 1 0 $ Fix (Abs s ty t pos1) pos2) t
eval1 ctx (Fix t pos)                  = do
  t' <- eval1 ctx t
  return $ Fix t' pos
eval1 ctx (If (Tru _) t2 t3 _)        = Just t2
eval1 ctx (If (Fls _) t2 t3 _)        = Just t3
eval1 ctx (If t1 t2 t3 pos)           = do
  t1' <- eval1 ctx t1
  return $ If t1' t2 t3 pos
eval1 ctx (Fst (Pair t1 t2 _) _)      = Just t1
eval1 ctx (Fst t pos)                 = do
  t' <- eval1 ctx t
  return $ Fst t' pos
eval1 ctx (Snd (Pair t1 t2 _) _)      = Just t2
eval1 ctx (Snd t pos)                 = do
  t' <- eval1 ctx t
  return $ Snd t' pos
eval1 ctx (Succ (Pred t _) pos)       = Just t
eval1 ctx (Succ t pos)                = do
  t' <- eval1 ctx t
  return $ Succ t' pos
eval1 ctx (Pred (Zero _) pos)         = Just $ Zero pos
eval1 ctx (Pred (Succ t _) pos)       = Just t
eval1 ctx (Pred t pos)                = do
  t' <- eval1 ctx t
  return $ Pred t' pos
eval1 ctx (IsZero (Zero _) pos)       = Just $ Tru pos
eval1 ctx (IsZero (Succ t _) pos)     = Just $ Fls pos
eval1 ctx (IsZero t pos)              = do
  t' <- eval1 ctx t
  return $ IsZero t' pos
eval1 ctx (ELeft t ty pos)            = do
  t' <- eval1 ctx t
  return $ ELeft t' ty pos
eval1 ctx (ERight t ty pos)           = do
  t' <- eval1 ctx t
  return $ ERight t' ty pos
eval1 ctx (Cons t ts pos)             =
  if isValue t
    then do
      ts' <- eval1 ctx ts
      return $ Cons t ts' pos
    else do
      t' <- eval1 ctx t
      return $ Cons t' ts pos
eval1 ctx _                           = Nothing

eval0 :: VContext -> Term -> Term
eval0 ctx t =
  let ev = eval1 ctx t
  in case ev of
    Nothing -> t
    Just t' -> eval0 ctx t'

eval :: Term -> Term
eval = eval0 nilmap
