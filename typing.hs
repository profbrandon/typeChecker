module TypeChecker
  ( Term (..)
  , Type (..)
  , TExpr (..)
  , showTerm
  , showType
  , typeof
  , subtype
  , (<:)
  )
where

data Term = Abs String Type Term
          | App Term Term
          | Var Int
          | If Term Term Term
          | Tru
          | Fls
          | Succ Term
          | Pred Term
          | IsZero Term
          | Zero

data Type = Forall String Type
          | Type TExpr
          | Bottom
          deriving Eq

data TExpr = Arrow TExpr TExpr
           | TVar String
           | Bool
           | Nat
           deriving Eq

type Function a b = a -> Maybe b

instance Show Term where
  show = showTerm (\a -> Nothing)

instance Show Type where
  show = showType (\a -> Nothing)

instance Show TExpr where
  show = showTExpr (\a -> Nothing) 



-- Contexts

type TContext = Function String String
type VContext = Function Int (String, Type)

addBinding :: Eq a => Function a b -> a -> b -> Function a b
addBinding f a b = \x -> if x == a then Just b else f x

pushBinding :: VContext -> (String, Type) -> VContext
pushBinding ctx p = addBinding (shiftBindings ctx) 0 p

shiftBindings :: VContext -> VContext
shiftBindings ctx = \x -> ctx (x - 1)



-- Show Functions

showTerm :: VContext -> Term -> String
showTerm ctx (Abs s ty tm) = 
  "\\" ++ s ++ " : " ++ show ty ++ " -> " ++ showTerm ctx' tm
  where ctx' = pushBinding ctx (s, ty)
showTerm ctx (App t1 t2)   = 
  "(" ++ showTerm ctx t1 ++ ") (" ++ showTerm ctx t2 ++ ")"
showTerm ctx (Var v)       = 
  case ctx v of
    Nothing     -> error "attempted access of unbound variable"
    Just (s, _) -> s
showTerm ctx (If t1 t2 t3) =
  "if " ++ showTerm ctx t1 ++ " then " ++ showTerm ctx t2 ++ " else " ++ showTerm ctx t3
showTerm ctx (Succ t)      = "succ (" ++ showTerm ctx t ++ ")"
showTerm ctx (Pred t)      = "pred (" ++ showTerm ctx t ++ ")"
showTerm ctx (IsZero t)    = "iszero (" ++ showTerm ctx t ++ ")"
showTerm _   Tru           = "True"
showTerm _   Fls           = "False"
showTerm _   Zero          = "0"

showType :: TContext -> Type -> String
showType ctx (Forall n ty) = 
  "forall " ++ n ++ ". (" ++ showType ctx' ty ++ ")"
  where ctx' = addBinding ctx n n
showType ctx (Type te)     = showTExpr ctx te
showType _   Bottom        = "Bottom"

showTExpr :: TContext -> TExpr -> String
showTExpr ctx (Arrow a b) =
  case a of
    Arrow _ _ -> wparen
    _         -> showTExpr ctx a ++ " -> " ++ showTExpr ctx b
    where wparen = "(" ++ showTExpr ctx a ++ ") -> " ++ showTExpr ctx b
showTExpr ctx (TVar s)    =
  case ctx s of
    Nothing -> error $ "attempted access of unbound type variable \'" ++ s ++ "\'"
    _       -> s
showTExpr ctx (Bool)      = "Bool"
showTExpr ctx (Nat)       = "Nat"



-- Operations on Universal Quantifiers

commute :: Type -> Type
commute (Forall n1 (Forall n2 t')) = Forall n2 (Forall n1 t')
commute _ = error "swapUQ requires arguments with two universal quantifiers"

condense :: Type -> Type
condense t = condense2 (\a -> Nothing) t

condense2 :: TContext -> Type -> Type
condense2 ctx (Forall n ty) =
  case ctx n of
    Nothing -> if hasTypeVar n ty then Forall n ty' else ty'
    _       -> ty'
    where ctx' = addBinding ctx n n
          ty'  = condense2 ctx' ty
condense2 ctx ty = ty

separate :: Type -> ([String], TExpr)
separate (Type te)     = ([], te)
separate (Forall n ty) = (n:ns, te) where (ns, te) = separate ty

buildArrow :: Type -> Type -> Type
buildArrow t1 t2 =
  let (n1, te1) = separate t1
      (n2, te2) = separate t2
  in quantify (n1 ++ n2, Arrow te1 te2)

splitArrow :: Type -> (Type, Type)
splitArrow t = 
  case te of
    Arrow a b -> (a', b')
      where a' = quantify (ns, a)
            b' = quantify (ns, b)
    _         -> error "non-arrow type provided to splitArrow"
    where (ns, te) = separate t

isArrow :: Type -> Bool
isArrow (Forall n t)       = isArrow t
isArrow (Type (Arrow _ _)) = True
isArrow _                  = False

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

uniqueNames :: [String] -> Type -> [String]
uniqueNames []     t = []
uniqueNames (x:xs) t =
  if hasTypeVar x t'
    then (x ++ "\'"):back
    else x:back
  where t'   = condense t
        back = uniqueNames xs t'

renameUnique :: Type -> Type -> Type
renameUnique t1 observer = 
  let (names, te1) = separate t1
      names'       = uniqueNames names observer
      mapping      = zip names names'
  in renameAll mapping t1

substituteAll :: [(String, Type)] -> Type -> Type
substituteAll [] t = t
substituteAll subs t1 = 
  let getSub     = toFunct subs
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
        t'      -> ([], t')

toFunct :: Eq a => [(a, b)] -> Function a b
toFunct []     = \a -> Nothing
toFunct (x:xs) = \n -> if n == a then Just b else (toFunct xs) n where (a, b) = x 



-- Typing

infix 4 <:

(<:) :: Type -> Type -> Bool
(<:) = subtype

typeof :: Term -> Type
typeof = typeof0 (toFunct [])

typeof0 :: VContext -> Term -> Type
typeof0 ctx (Abs s ty1 tm) = 
  buildArrow ty1 ty2 
  where ctx' = pushBinding ctx (s, ty1)
        ty2  = typeof0 ctx' tm
typeof0 ctx (App t1 t2)    =
  case separate ty1 of
    (_, (Arrow _ _)) ->
      let (ty11, ty12)  = splitArrow ty1
          ty2'          = renameUnique ty2 ty1
          (subs, issub) = subtype0 ty2' ty11
      in if issub 
        then substituteAll subs ty12
        else error "parameter type mismatch"
    _            -> error "arrow type expected as applicand"
    where ty1 = typeof0 ctx t1
          ty2 = typeof0 ctx t2
typeof0 ctx (Var v)        = 
  case ctx v of
    Nothing     -> error "attempted access of unbound variable in function \'typeof\'"
    Just (_, t) -> t
typeof0 ctx (If t1 t2 t3)  =
  if ty1 == Type Bool
    then if ty2 == ty3
      then ty2
      else error "type mismatch in branches of conditional"
    else error "type \'Bool\' expected in guard of conditional"
  where ty1 = typeof0 ctx t1
        ty2 = typeof0 ctx t2
        ty3 = typeof0 ctx t3
typeof0 ctx (Succ t)       = 
  if ty == Type Nat 
    then Type Nat 
    else error "argument of type \'Nat\' expected to \'succ\'" 
  where ty = typeof0 ctx t
typeof0 ctx (Pred t)       =
  if ty == Type Nat 
    then Type Nat 
    else error "argument of type \'Nat\' expected to \'pred\'" 
  where ty = typeof0 ctx t
typeof0 ctx (IsZero t)     =
  if ty == Type Nat 
    then Type Bool 
    else error "argument of type \'Nat\' expected to \'iszero\'" 
  where ty = typeof0 ctx t
typeof0 _   Tru            = Type Bool
typeof0 _   Fls            = Type Bool
typeof0 _   Zero           = Type Nat

subtype :: Type -> Type -> Bool
subtype Bottom t  = True
subtype t1     t2 = b where (_, b) = subtype0 t1 t2

subtype0 :: Type -> Type -> ([(String, Type)], Bool)
subtype0 t1 t2 =
  let t1' = condense t1
      t2' = condense t2
  in case (isArrow t1', isArrow t2') of
    (False, False) -> 
      case t2' of
        Forall _ (Type (TVar n)) -> ([(n, t1)], True)
        _                        -> ([], t1' == t2')
    (False, True)  -> ([], False)
    (True, False)  -> 
      case t2' of
        Forall _ (Type (TVar n)) -> ([(n, t1)], True)
        _                        -> ([], False)
    (True, True)   ->
      let (t11, t12) = splitArrow t1'
          (t21, t22) = splitArrow t2'
          (subs, b)  = subtype0 t11 t21
          back       = if b then subtype0 t12 $ substituteAll subs t22
                            else ([], False)
      in case t2' of
        Forall _ (Forall _ (Type (Arrow (TVar n) (TVar m)))) -> ([(n, t11), (m, t12)], True)
        Forall _ (Type (Arrow _ _)) ->
          case t1' of
            Forall _ (Forall _ _)       -> ([], False)
            Forall _ (Type (Arrow _ _)) -> back
            _ -> back 
    _ -> back
