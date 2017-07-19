-- Type Checker for the Simply-Typed Lambda Calculus

-- Supported Language Features:

--   Abstractions
--   Application
--   Variables
--   Sums
--   Binary Case Expressions

-- Supported Typing Features:

--   Arrow Types (Function Types)
--   Type Variables
--   Sum Types

module STLambdaSum
  ( Term (..)
  , Type (..)
  , Error (..)
  , VContext (..)
  , showTerm
  , showType
  , addBinding
  , pushBinding
  , shiftBindings
  , typeof
  )
where

data Term = Abs String Type Term
          | App Term Term
          | Var Int
          | Lft Term
          | Rit Term
          | Case Term Term Term Term Term

data Type = Arrow Type Type
          | TVar String
          | Sum Type Type
          | Hole
           deriving Eq

data Error = ParamMismatch Type Type
           | MissingArrow Term
           | UnboundVar VContext Int
           | MissingSum Type
           | CaseBranchMismatch Type Type
           | CaseIncGuard Term Term
           | CaseGuardMismatch Type Type

type Function a b = a -> Maybe b

instance Show Term where
  show = showTerm (\a -> Nothing)

instance Show Type where
  show = showType

instance Show Error where
  show = showError


-- Contexts

type VContext = Function Int (String, Type)

addBinding :: Eq a => Function a b -> a -> b -> Function a b
addBinding f a b = \x -> if x == a then Just b else f x

pushBinding :: VContext -> (String, Type) -> VContext
pushBinding ctx p = addBinding (shiftBindings ctx) 0 p

shiftBindings :: VContext -> VContext
shiftBindings ctx = \x -> ctx (x - 1)



-- Show Functions

showTerm :: VContext -> Term -> String
showTerm ctx (Lft t)       = "Left (" ++ showTerm ctx t ++ ")"
showTerm ctx (Rit t)       = "Right (" ++ showTerm ctx t ++ ")"
showTerm ctx (Case t t1 t1' t2 t2') =
  "case " ++ showTerm ctx t ++ " of " ++ showTerm ctx t1 ++ " -> " ++ showTerm ctx t1' ++ " | " ++ showTerm ctx t2 ++ " -> " ++ showTerm ctx t2'
showTerm ctx (Abs s ty tm) = 
  "\\" ++ s ++ " : " ++ show ty ++ ". " ++ showTerm ctx' tm
  where ctx' = pushBinding ctx (s, ty)
showTerm ctx (App t1 t2)   = 
  "(" ++ showTerm ctx t1 ++ ") (" ++ showTerm ctx t2 ++ ")"
showTerm ctx (Var v)       = 
  case ctx v of
    Nothing     -> "(Var " ++ show v ++ ")"
    Just (s, _) -> s

showType :: Type -> String
showType Hole        = "_"
showType (Sum a b)   = "(" ++ showType a ++ " | " ++ showType b ++ ")"
showType (Arrow a b) =
  case a of
    Arrow _ _ -> wparen
    _         -> showType a ++ " -> " ++ showType b
    where wparen = "(" ++ showType a ++ ") -> " ++ showType b
showType (TVar s)    = s

showError :: Error -> String
showError (ParamMismatch t1 t2) = "expected type (" ++ show t1 ++ "), supplied type (" ++ show t2 ++ ")"
showError (MissingArrow t)      = "expected arrow type in the term \'" ++ show t ++ "\'" 
showError (UnboundVar ctx i)    = "variable indexed by \'" ++ show i ++ "\' not in the present context"
showError (MissingSum t)        = "expected sum type, recieved type (" ++ show t ++ ")"
showError (CaseBranchMismatch t1 t2) = "type mismatch in branches of case expression. (" ++ show t1 ++ ") /= (" ++ show t2 ++ ")"
showError (CaseGuardMismatch t1 t2) = "expected type (" ++ show t1 ++ ") in guard, recieved type (" ++ show t2 ++ ")" 
showError (CaseIncGuard t1 t2)  = "expected left or right term to both guards of case, recieved terms \'" ++ show t1 ++ "\', \'" ++ show t2 ++ "\'"



-- toFunct

toFunct :: Eq a => [(a, b)] -> Function a b
toFunct [] = \a -> Nothing
toFunct (x:xs) = \n -> if n == a then Just b else (toFunct xs) n where (a, b) = x



-- Typing

typeof :: Term -> Either Error Type
typeof = typeof0 (toFunct [])

typeof0 :: VContext -> Term -> Either Error Type
typeof0 ctx (Lft a)        = do
  ta <- typeof0 ctx a
  return $ Sum ta Hole
typeof0 ctx (Rit b)        = do
  tb <- typeof0 ctx b
  return $ Sum Hole tb
typeof0 ctx (Abs s ty1 tm) = (Arrow ty1) <$> typeof0 ctx' tm
  where ctx' = pushBinding ctx (s, ty1)
typeof0 ctx (App t1 t2)    = do
  ty1 <- typeof0 ctx t1
  ty2 <- typeof0 ctx t2
  case ty1 of
    Arrow ty11 ty12 ->
      if ty11 == ty2
        then Right ty12
        else Left $ ParamMismatch ty11 ty2
    _            -> Left $ MissingArrow (App t1 t2) 
typeof0 ctx (Var v)        = 
  case ctx v of
    Nothing     -> Left $ UnboundVar ctx v
    Just (_, t) -> Right t
typeof0 ctx (Case t t1 t1' t2 t2') = do
  ty   <- typeof0 ctx t
  ty1' <- typeof0 ctx t1'
  ty2' <- typeof0 ctx t2'
  case ty of
    Sum a b ->
      if ty1' == ty2'
        then case (t1, t2) of
          (Lft a', Rit b') -> do
            ta' <- typeof a'
            tb' <- typeof b'
            case (a, b) of
              (Hole, tb) ->
                if tb == tb'
                  then return ty1'
                  else Left $ CaseGuardMismatch tb tb'
              (ta, Hole) ->
                if ta == ta'
                  then return ty1'
                  else Left $ CaseGuardMismatch ta ta'
          _ -> Left $ CaseIncGuard t1 t2
        else Left $ CaseBranchMismatch ty1' ty2'
    _ -> Left $ MissingSum ty
