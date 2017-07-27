-- Type Checker for an extension to the Lambda Calculus

-- Supported Language Features:

--   Abstractions
--   Application
--   Variables
--   Recursion
--   Conditionals
--   Successor Function
--   Predeccessor Function
--   Zero Test
--   Boolean Values
--   Natural Values
--   Unit Value
--   Errors (Uncaught Exceptions)

-- Supported Typing Features:

--   Universal Quantification (Parametric Polymorphism)
--   Type Variables
--   Top Type
--   Bottom Type
--   Arrow Types (Function Types)
--   Bool Type
--   Nat Type
--   Unit Type
--   Subtyping

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

import TypeChecker.Utils
import TypeChecker.Types
import TypeChecker.UniversalQuantifiers.Utils
import Language.AbstractSyntax


data Error = ParamTypeMismatch   Type Type
           | IfBranchMismatch    Type Type
           | ExpectedArrow       Type
           | ExpectedBoolGuard   Type
           | ExpectedPairtoFst   Type
           | ExpectedPairtoSnd   Type
           | ExpectedNattoSucc   Type
           | ExpectedNattoPred   Type
           | ExpectedNattoIsZero Type
           | UnboundVar

instance Show Error where
  show = showError

showError :: Error -> String
showError (ParamTypeMismatch t1 t2) = "parameter type mismatch. Expected type " ++ show t1 ++ ", recieved type " ++ show t2
showError (IfBranchMismatch t1 t2)  = "type mismatch in branches of conditional. Recieved types " ++ show t1 ++ " and " ++ show t2
showError (ExpectedArrow t)         = "expected arrow type, recieved type " ++ show t
showError (ExpectedBoolGuard t)     = "expected argument of type Bool to guard of conditional, recieved type " ++ show t
showError (ExpectedPairtoFst t)     = "expected argument of type (a, b) to \'fst\' function, recieved type " ++ show t
showError (ExpectedPairtoSnd t)     = "expected argument of type (a, b) to \'snd\' function, recieved type " ++ show t
showError (ExpectedNattoSucc t)     = "expected argument of type Nat to \'succ\' function, recieved type " ++ show t
showError (ExpectedNattoPred t)     = "expected argument of type Nat to \'pred\' function, recieved type " ++ show t
showError (ExpectedNattoIsZero t)   = "expected argument of type Nat to \'iszero\' function, recieved type " ++ show t
showError (UnboundVar)              = "unbound variable"



-- Typing

typeof :: Term -> Either Error Type
typeof = typeof0 nilmap nilmap

typeof0 :: TContext -> VContext -> Term -> Either Error Type
typeof0 tctx vctx (Abs s ty1 tm) = do
  ty2 <- typeof0 tctx' vctx' tm
  return $ buildArrow ty1 ty2 
  where tctx' = addAllBindings (fst $ separate ty1) tctx
        vctx' = pushBinding vctx (s, ty1)
typeof0 tctx vctx (App t1 t2)    = do
  ty1 <- typeof0 tctx vctx t1
  ty2 <- typeof0 tctx vctx t2
  case separate ty1 of
    (_, Arrow _ _) ->
      let (ty11, ty12) = splitArrow ty1
          ty2'         = renameUnique tctx ty2 ty1
          fs           = findSubs [] ty11 ty2'
      in case fs of
        Nothing   -> Left $ ParamTypeMismatch ty11 ty2
        Just subs -> if tctxConflict tctx subs
                       then Left $ ParamTypeMismatch ty11 ty2
                       else return $ quantify (free0 ty12', ty12') where (_, ty12') = separate $ substituteAll subs ty12
    _            ->
      if ty1 == Bottom
        then return Bottom
        else Left $ ExpectedArrow ty1
typeof0 tctx vctx (Let s t1 t2)  = do
  ty1 <- typeof0 tctx vctx t1
  let tctx' = addAllBindings (fst $ separate ty1) tctx
      vctx' = pushBinding vctx (s, ty1)
  typeof0 tctx' vctx' t2
typeof0 tctx vctx (Pair t1 t2)   = do
  ty1 <- typeof0 tctx vctx t1
  ty2 <- typeof0 tctx vctx t2
  let (qs1, ty1') = separate ty1
      (qs2, ty2') = separate ty2
  return $ quantify (qs1 ++ qs2, TPair ty1' ty2')
typeof0 tctx vctx (Var v)        = 
  case vctx v of
    Nothing     -> Left UnboundVar
    Just (_, t) -> return t
typeof0 tctx vctx (Fix t)        = do
  ty <- typeof0 tctx vctx t
  case separate ty of
    (qs, (Arrow _ _)) -> return $ fst $ splitArrow ty
    _                 -> Left $ ExpectedArrow ty
typeof0 tctx vctx (If t1 t2 t3)  = do
  ty1 <- typeof0 tctx vctx t1
  ty2 <- typeof0 tctx vctx t2
  ty3 <- typeof0 tctx vctx t3
  if ty1 == Type Bool
    then if ty2 !> ty3
      then return ty3
      else if ty3 !> ty2
        then return ty2
        else Left $ IfBranchMismatch ty2 ty3
    else Left $ ExpectedBoolGuard ty1
typeof0 tctx vctx (Fst t)        = do
  ty <- typeof0 tctx vctx t
  case separate ty of
    (qs, TPair a b) -> return $ quantify (qs, a)
    _               -> Left $ ExpectedPairtoFst ty
typeof0 tctx vctx (Snd t)        = do
  ty <- typeof0 tctx vctx t
  case separate ty of
    (qs, TPair a b) -> return $ quantify (qs, b)
    _               -> Left $ ExpectedPairtoSnd ty
typeof0 tctx vctx (Succ t)       = do
  ty <- typeof0 tctx vctx t
  if ty == Type Nat 
    then return $ Type Nat 
    else Left $ ExpectedNattoSucc ty 
typeof0 tctx vctx (Pred t)       = do
  ty <- typeof0 tctx vctx t
  if ty == Type Nat 
    then return $ Type Nat 
    else Left $ ExpectedNattoPred ty
typeof0 tctx vctx (IsZero t)     = do
  ty <- typeof0 tctx vctx t
  if ty == Type Nat 
    then return $ Type Bool 
    else Left $ ExpectedNattoIsZero ty
typeof0 _    _    Tru            = return $ Type Bool
typeof0 _    _    Fls            = return $ Type Bool
typeof0 _    _    Zero           = return $ Type Nat
typeof0 _    _    EUnit          = return $ Type Unit
typeof0 _    _    Error          = return $ Bottom
