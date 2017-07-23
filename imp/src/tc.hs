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
  , special
  , (<!)
  )
where

import TypeChecker.Utils
import TypeChecker.Types
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



-- Operations on Universal Quantifiers

-- Condenses Quantifiers
   -- e.g.,  forall a. forall a. t ==> forall a. t
condense :: Type -> Type
condense t = condense2 (\a -> Nothing) t

condense2 :: TContext -> Type -> Type
condense2 ctx (Forall n ty) =
  case ctx n of
    Nothing -> if hasTypeVar n ty then Forall n ty' else ty'
    _       -> ty'
    where ctx' = addBinding n n ctx
          ty'  = condense2 ctx' ty
condense2 ctx ty = ty

-- Separates quantifiers from their type expressions
   -- e.g., forall a. a -> a ==> ("a", a -> a)
separate :: Type -> ([String], TExpr)
separate (Type te)     = ([], te)
separate (Forall n ty) = (n:ns, te) where (ns, te) = separate ty

buildArrow :: Type -> Type -> Type
buildArrow t1 t2 =
  let (n1, te1) = separate t1
      (n2, te2) = separate t2
  in quantify (n1 ++ n2, Arrow te1 te2)

-- Splits an arrow type into the domain and codomain types, keeping quantifiers if needed
   -- e.g., forall a. forall b. a -> b ==> (forall a. a, forall b. b)
splitArrow :: Type -> (Type, Type)
splitArrow t = 
  case te of
    Arrow a b -> (a', b')
      where a' = quantify (ns, a)
            b' = quantify (ns, b)
    where (ns, te) = separate t

isArrow :: Type -> Bool
isArrow (Forall n t)       = isArrow t
isArrow (Type (Arrow _ _)) = True
isArrow _                  = False

-- Inverse of separate (i.e., quantify . separate == id)
quantify :: ([String], TExpr) -> Type
quantify = condense . quantify2

quantify2 :: ([String], TExpr) -> Type
quantify2 ([], te)     = Type te
quantify2 ((n:ns), te) = Forall n ty where ty = quantify2 (ns, te)

hasTypeVar :: String -> Type -> Bool
hasTypeVar s (Forall n ty)      = hasTypeVar s ty
hasTypeVar s (Type (Arrow a b)) = hasTypeVar s (Type a) || hasTypeVar s (Type b)
hasTypeVar s (Type (TVar k))    = s == k
hasTypeVar s _                  = False

substitute :: String -> Type -> Type -> Type
substitute v (Type (TVar v')) t =
  substitute v (Forall v' $ Type $ TVar v') t
substitute v t2 t1 =
  let (qs1, te1) = separate t1
      (qs2, te2) = separate t2
  in quantify (qs1 ++ qs2, substitute0 v te2 te1)

substitute0 :: String -> TExpr -> TExpr -> TExpr
substitute0 v t2 t1 =
  if hasTypeVar v (Type t1)
    then case t1 of
      Arrow a b -> Arrow a' b'
        where a' = substitute0 v t2 a
              b' = substitute0 v t2 b
      TVar n    ->
        if n == v
          then t2
          else TVar n
      te' -> te'
    else t1

rename :: String -> String -> Type -> Type
rename s1 s2 = substitute s1 $ Type $ TVar s2

renameAll :: [(String, String)] -> Type -> Type
renameAll []     t = t
renameAll (x:xs) t = 
  rename s1 s2 t' 
  where (s1, s2) = x
        t'       = renameAll xs t

-- Builds unique type variable names that are not present in the type provided
uniqueNames :: [String] -> Type -> [String]
uniqueNames []     t = []
uniqueNames (x:xs) t =
  if hasTypeVar x t'
    then (x ++ "\'"):back
    else x:back
  where t'   = condense t
        back = uniqueNames xs t'

-- Renames type variables in the second parameter to names, unique from those in the third parameter,
-- unless the type variables are bound in a type context
renameUnique :: TContext -> Type -> Type -> Type
renameUnique ctx t1 observer =
  let (names, _) = separate $ condense t1
      names'     = filter (\n -> case ctx n of
                                   Nothing -> True
                                   _ -> False) names
      names''    = uniqueNames names' observer
      mapping    = zip names' names''
  in renameAll mapping t1

substituteAll :: [(String, Type)] -> Type -> Type
substituteAll [] t    = t
substituteAll subs t1 = 
  let getSub     = toFunction subs
      (qs1, t1') = separate t1
      (qs2, t2)  = substituteAll0 (getSub) t1'
  in quantify (qs1 ++ qs2, t2)

substituteAll0 :: Function String Type -> TExpr -> ([String], TExpr)
substituteAll0 getSub t =
  case t of
    Arrow a b ->
      let (qsa, a') = substituteAll0 (getSub) a
          (qsb, b') = substituteAll0 (getSub) b
      in (qsa ++ qsb, Arrow a' b')
    TVar v    -> 
      case getSub v of
        Nothing -> ([v], TVar v)
        Just ty -> separate ty
    t'        -> ([], t')

quantifier :: Type -> Bool
quantifier (Forall _ _) = True
quantifier (Type _)     = False



-- Typing

infix 4 <!

(<!) :: Type -> Type -> Bool
(<!) = special

--(<:) :: Type -> Type -> Bool
--(<:) = subtype

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
      let (ty11, ty12)  = splitArrow ty1
          ty2'          = renameUnique tctx ty2 ty1
          (subs, isspe) = special0 ty11 ty2'
      in if isspe
        then return $ substituteAll subs ty12
        else Left $ ParamTypeMismatch ty11 ty2
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
    then if ty2 <! ty3
      then return ty2
      else if ty3 <! ty2
        then return ty3
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

-- Specialization relation
-- t1 is a specialization of t2
special :: Type -> Type -> Bool
special t2 t1 = b where (_, b) = special0 t2 t1

special0 :: Type -> Type -> ([(String, Type)], Bool)
special0 t2 t1 =
  let t1' = condense t1
      t2' = condense t2
  in case (isArrow t1', isArrow t2') of
    (False, False) -> 
      case t2' of
        Forall _ (Type (TVar n)) -> ([(n, t1')], True)
        _                        -> ([], t1' == t2')
    (False, True)  -> ([], False)
    (True, False)  -> 
      case t2' of
        Forall _ (Type (TVar n)) -> ([(n, t1')], True)
        _                        -> ([], False)
    (True, True)   ->
      let (t11, t12) = splitArrow t1'
          (t21, t22) = splitArrow t2'
          (subs, b)  = special0 t21 t11
          back       = if b then let (subs', b') = special0 (substituteAll subs t22) t12
                                 in (subs ++ subs', b')
                            else ([], False)
      in case t2' of
        Forall _ (Forall _ (Type (Arrow (TVar n) (TVar m)))) -> ([(n, t11), (m, t12)], True)
        Forall _ (Type (Arrow _ _)) ->
          case t1' of
            Forall _ (Forall _ _)       -> ([], False)
            Forall _ (Type (Arrow _ _)) -> back
            _ -> back 
        _ -> back

-- Subtype Relation
-- subtype :: Type -> Type -> Bool