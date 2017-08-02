
module TypeChecker
  ( Term(..)
  , Type(..)
  , TExpr(..)
  , TContext(..)
  , VContext(..)
  , nilmap
  , pushBinding
  , typeof
  , typeof0
  , special
  , (!>)
  )
where

import Data.List (union, delete)
import Data.Maybe (isJust, isNothing)
import Text.Parsec (SourcePos)

import TypeChecker.Utils
import TypeChecker.Types
import TypeChecker.UniversalQuantifiers.Utils
import TypeChecker.PatternMatching
import Evaluator.PatternMatching
import Language.AbstractSyntax


data Error = ParamTypeMismatch    Type Type   SourcePos
           | IfBranchMismatch     Type Type   SourcePos
           | CaseBranchMismatch   Type Type   SourcePos
           | ProjectionMismatch   Type String SourcePos
           | ExpectedArrow        Type        SourcePos
           | ExpectedBoolGuard    Type        SourcePos
           | ExpectedPairtoFst    Type        SourcePos
           | ExpectedPairtoSnd    Type        SourcePos
           | ExpectedNattoSucc    Type        SourcePos
           | ExpectedNattoPred    Type        SourcePos
           | ExpectedNattoIsZero  Type        SourcePos
           | ExpectedRecordtoProj Type        SourcePos
           | PatternError                     SourcePos
           | UnboundVar                       SourcePos

instance Show Error where
  show = showError

showError :: Error -> String
showError (ParamTypeMismatch t1 t2 pos) = "parameter type mismatch. Expected type " ++ show t1 ++ ", recieved type " ++ show t2 ++ " at " ++ show pos
showError (IfBranchMismatch t1 t2 pos)  = "type mismatch in branches of conditional. Recieved types " ++ show t1 ++ " and " ++ show t2 ++ " at " ++ show pos
showError (CaseBranchMismatch t1 t2 pos) = "type mismatch in branches of case expression. Recieved types " ++ show t1 ++ " and " ++ show t2 ++ " at " ++ show pos
showError (ProjectionMismatch t s pos)  = "type mismatch in projection.  Recieved field " ++ s ++ ", expected a member of " ++ show t ++ " at " ++ show pos
showError (ExpectedArrow t pos)         = "expected arrow type, recieved type " ++ show t ++ " at " ++ show pos
showError (ExpectedBoolGuard t pos)     = "expected argument of type Bool to guard of conditional, recieved type " ++ show t ++ " at " ++ show pos
showError (ExpectedPairtoFst t pos)     = "expected argument of type (a, b) to \'fst\' function, recieved type " ++ show t ++ " at " ++ show pos
showError (ExpectedPairtoSnd t pos)     = "expected argument of type (a, b) to \'snd\' function, recieved type " ++ show t ++ " at " ++ show pos
showError (ExpectedNattoSucc t pos)     = "expected argument of type Nat to \'succ\' function, recieved type " ++ show t ++ " at " ++ show pos
showError (ExpectedNattoPred t pos)     = "expected argument of type Nat to \'pred\' function, recieved type " ++ show t ++ " at " ++ show pos
showError (ExpectedNattoIsZero t pos)   = "expected argument of type Nat to \'iszero\' function, recieved type " ++ show t ++ " at " ++ show pos
showError (ExpectedRecordtoProj t pos)  = "expected argument of type {a = A,b = B,...} to projection, recieved type " ++ show t ++ " at " ++ show pos
showError (PatternError pos)            = "pattern error at " ++ show pos
showError (UnboundVar pos)              = "unbound variable at " ++ show pos



-- Typing

-- Handles the typing of case expression branches
branches :: TContext -> VContext -> SourcePos -> Type -> Branches -> Either Error Type
branches tctx vctx pos ty [(p, t)] =
  case tmatch p ty of
    Nothing   -> Left $ PatternError pos
    Just subs -> 
      let vctx' = pushAllBindings vctx subs
      in typeof0 tctx vctx' t
branches tctx vctx pos ty ((p, t):bs) =
  case tmatch p ty of
    Nothing -> Left $ PatternError pos
    Just subs ->
      let vctx' = pushAllBindings vctx subs
      in do
        ty1 <- typeof0 tctx vctx' t
        ty2 <- branches tctx vctx pos ty bs
        if ty1 !> ty2
          then return ty2
          else if ty2 !> ty1
            then return ty1
            else Left $ CaseBranchMismatch ty1 ty2 pos

typeof :: Term -> Either Error Type
typeof = typeof0 nilmap nilmap

typeof0 :: TContext -> VContext -> Term -> Either Error Type
typeof0 tctx vctx (Abs s ty1 tm _) = do
  ty2 <- typeof0 tctx' vctx' tm
  return $ buildArrow ty1 ty2 
  where tctx' = addAllBindings (fst $ separate ty1) tctx
        vctx' = pushBinding vctx (s, ty1)
typeof0 tctx vctx (App t1 t2 pos)    = do
  ty1 <- typeof0 tctx vctx t1
  ty2 <- typeof0 tctx vctx t2
  case separate ty1 of
    (_, Arrow _ _) ->
      let (ty11, ty12) = splitArrow ty1
          ty2'         = renameUnique tctx ty2 ty1
          fs           = findSubs [] ty11 ty2'
      in case fs of
        Nothing   -> Left $ ParamTypeMismatch ty11 ty2 pos
        Just subs -> if tctxConflict tctx subs
                       then Left $ ParamTypeMismatch ty11 ty2 pos
                       else return $ quantify (free0 ty12', ty12') where (_, ty12') = separate $ substituteAll subs ty12
    _            ->
      if ty1 == Bottom
        then return Bottom
        else Left $ ExpectedArrow ty1 pos
typeof0 tctx vctx (Let p t1 t2 pos)  = do
  ty1 <- typeof0 tctx vctx t1
  let msubs = tmatch p ty1
  case msubs of
    Nothing   -> Left $ PatternError pos
    Just subs -> do
      let tctx' = addAllBindings (fst $ separate ty1) tctx
          vctx' = pushAllBindings vctx subs
      typeof0 tctx' vctx' t2
typeof0 tctx vctx (Case t bs pos)  = do
  ty <- typeof0 tctx vctx t
  let tctx' = addAllBindings (fst $ separate ty) tctx
  branches tctx' vctx pos ty bs
typeof0 tctx vctx (Record fs _)    =
  let fields fs = case fs of
        []            -> return []
        ((s, te):fs') -> do
          tf <- typeof0 tctx vctx te
          tfs <- fields fs'
          return $ (s, tf):tfs
  in do
    fs' <- fields fs
    return $ Type $ TRec fs'
typeof0 tctx vctx (Proj t s pos)     = do
  ty <- typeof0 tctx vctx t
  case ty of
    Type (TRec fs) ->
      case s `lookup` fs of
        Nothing  -> Left $ ProjectionMismatch ty s pos
        Just tys -> return tys
    _              -> Left $ ExpectedRecordtoProj ty pos
typeof0 tctx vctx (Pair t1 t2 _)   = do
  ty1 <- typeof0 tctx vctx t1
  ty2 <- typeof0 tctx vctx t2
  let (qs1, ty1') = separate ty1
      (qs2, ty2') = separate ty2
  return $ quantify (qs1 ++ qs2, TPair ty1' ty2')
typeof0 tctx vctx (Var v pos)        = 
  case vctx v of
    Nothing     -> Left $ UnboundVar pos
    Just (_, t) -> return t
typeof0 tctx vctx (Fix t pos)        = do
  ty <- typeof0 tctx vctx t
  case separate ty of
    (qs, (Arrow _ _)) -> return $ fst $ splitArrow ty
    _                 -> Left $ ExpectedArrow ty pos
typeof0 tctx vctx (If t1 t2 t3 pos)  = do
  ty1 <- typeof0 tctx vctx t1
  ty2 <- typeof0 tctx vctx t2
  ty3 <- typeof0 tctx vctx t3
  if ty1 == Type Bool
    then if ty2 !> ty3
      then return ty3
      else if ty3 !> ty2
        then return ty2
        else Left $ IfBranchMismatch ty2 ty3 pos
    else Left $ ExpectedBoolGuard ty1 pos
typeof0 tctx vctx (Fst t pos)        = do
  ty <- typeof0 tctx vctx t
  case separate ty of
    (qs, TPair a b) -> return $ quantify (qs, a)
    _               -> Left $ ExpectedPairtoFst ty pos
typeof0 tctx vctx (Snd t pos)        = do
  ty <- typeof0 tctx vctx t
  case separate ty of
    (qs, TPair a b) -> return $ quantify (qs, b)
    _               -> Left $ ExpectedPairtoSnd ty pos
typeof0 tctx vctx (Succ t pos)       = do
  ty <- typeof0 tctx vctx t
  if ty == Type Nat 
    then return $ Type Nat 
    else Left $ ExpectedNattoSucc ty pos
typeof0 tctx vctx (Pred t pos)       = do
  ty <- typeof0 tctx vctx t
  if ty == Type Nat 
    then return $ Type Nat 
    else Left $ ExpectedNattoPred ty pos
typeof0 tctx vctx (IsZero t pos)     = do
  ty <- typeof0 tctx vctx t
  if ty == Type Nat 
    then return $ Type Bool 
    else Left $ ExpectedNattoIsZero ty pos
typeof0 _    _    (Tru _)            = return $ Type Bool
typeof0 _    _    (Fls _)            = return $ Type Bool
typeof0 _    _    (Zero _)           = return $ Type Nat
typeof0 _    _    (EUnit _)          = return $ Type Unit
