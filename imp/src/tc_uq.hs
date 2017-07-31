
module TypeChecker.UniversalQuantifiers.Utils where

import Data.List (union, delete)
import Data.Maybe (isJust, isNothing)

import TypeChecker.Utils
import TypeChecker.Types



-- Operations on Universal Quantifiers

-- Calculates Free Variables of a type based on the definition in typeChecker/imp/doc/uq.txt
free :: Type -> [String]
free (Type t)           = free0 t
free (Forall n t)       = delete n $ free t

free0 :: TExpr -> [String]
free0 (TVar n)    = [n]
free0 (Arrow a b) = free0 a `union` free0 b
free0 (TPair a b) = free0 a `union` free0 b
free0 _           = []

-- Condenses Quantifiers
   -- e.g.,  forall a. forall a. t ==> forall a. t
condense :: Type -> Type
condense (Type t)     = Type t
condense (Forall n t)
  | n `elem` fv = Forall n t'
  | otherwise   = t'
  where fv = free t; t' = condense t

-- Separates quantifiers from their type expressions
   -- Inverse of qunatify
   -- e.g., forall a. a -> a ==> ("a", a -> a)
separate :: Type -> ([String], TExpr)
separate (Type te)     = ([], te)
separate (Forall n ty) = (n:ns, te) where (ns, te) = separate ty

-- Builds an arrow type using domain and codomain types, condensing quantifiers if needed
   -- The inverse of splitArrow.
      -- e.g., (uncurry buildArrow) (splitArrow t) = t
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

-- Combines a type expression with the corresponding quantifiers
   -- Inverse of separate (i.e., quantify . separate = id)
quantify :: ([String], TExpr) -> Type
quantify = condense . quantify2

quantify2 :: ([String], TExpr) -> Type
quantify2 ([], te)     = Type te
quantify2 ((n:ns), te) = Forall n ty where ty = quantify2 (ns, te)

quantify' :: Type -> Type
quantify' t = quantify (free0 te, te) where (_, te) = separate t

hasTypeVar :: String -> Type -> Bool
hasTypeVar s (Forall n ty) = hasTypeVar s ty
hasTypeVar s (Type t)      = s `elem` free0 t

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
      names'     = filter (\n -> isNothing $ ctx n) names
      mapping    = zip names' $ uniqueNames names' observer
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
    TPair a b ->
      let (qsa, a') = substituteAll0 (getSub) a
          (qsb, b') = substituteAll0 (getSub) b
      in (qsa ++ qsb, TPair a' b')
    TVar v    -> 
      case getSub v of
        Nothing -> ([v], TVar v)
        Just ty -> separate ty
    t'        -> ([], t')

-- Checks for a conflict between substitutions and the given context
tctxConflict :: TContext -> [(String, Type)] -> Bool
tctxConflict tctx []     = False
tctxConflict tctx (x:xs) =
  case x of
   (n, Type (TVar m)) ->
     if n == m
       then back
       else not (prop n && prop m) || back
   _                  -> back
  where prop = isNothing . tctx
        back = tctxConflict tctx xs



-- Specialization

infix 4 !>

(!>) :: Type -> Type -> Bool
(!>) = special

-- Specialization relation
-- t1 is a specialization of t2
special :: Type -> Type -> Bool
special t1 t2 = isJust $ findSubs [] t2 t1

-- Finds Substitutions "s" such that s (t2) = t1 (if they exist)
  -- where s (t2) denotes performing all substitutions in s on t2
findSubs :: [(String,Type)] -> Type -> Type -> Maybe [(String, Type)]
findSubs s  (Forall v1 tt1) (Forall v2 tt2) = findSubs s tt1 tt2
findSubs s  (Forall v tt) t = findSubs s tt t
findSubs s0 (Type (Arrow t11 t12)) (Type (Arrow t21 t22)) = do
  s1 <- findSubs s0 (Type t11) (Type t21)
  s2 <- findSubs s1 (Type t12) (Type t22)
  return $ s2
findSubs s0 (Type (TPair t11 t12)) (Type (TPair t21 t22)) = do
  s1 <- findSubs s0 (Type t11) (Type t21)
  s2 <- findSubs s1 (Type t12) (Type t22)
  return $ s2
findSubs s (Type (TVar n)) t1
  | (n, t1) `elem` s      = return s
  | isJust $ n `lookup` s = Nothing
  | otherwise             = return $ (n, t1):s
findSubs s (Type p1) (Type p2)
  | p1 == p2  = return []
  | otherwise = Nothing
findSubs _ _ _ = Nothing
