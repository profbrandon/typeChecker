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

module STLambda
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
          | Lft Term Type
          | Rit Term Type
          | Case Term Term Term Term Term

data Type = Arrow Type Type
          | TVar String
          | Sum Type Type
           deriving Eq

data Error = ParamMismatch Type Type
           | MissingArrow Term
           | UnboundVar VContext Int
           | MissingSum Type
           | SumMismatch Type Type
           | CaseBranchMismatch Type Type
           | CaseGuardMismatch
           | CaseMissingSum

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
showTerm ctx (Lft e t) = "Left " ++ showTerm ctx e ++ " : " ++ show t
showTerm ctx (Rit e t) = "Right " ++ showTerm ctx e ++ " : " ++ show t
showTerm ctx (Case e1 e2 e2' e3 e3') =
  "case " ++ showTerm ctx e1 ++ " of "
    ++ showTerm ctx e2 ++ " -> " ++ showTerm ctx e2' ++ " | "
    ++ showTerm ctx e3 ++ " -> " ++ showTerm ctx e3'
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
showType (Sum a b)   = "(" ++ show a ++ ") | (" ++ show b ++ ")"
showType (Arrow a b) =
  case a of
    Arrow _ _ -> wparen
    _         -> show a ++ " -> " ++ show b
    where wparen = "(" ++ show a ++ ") -> " ++ show b
showType (TVar s)    = s

showError :: Error -> String
showError (ParamMismatch t1 t2) = "expected type (" ++ show t1 ++ "), supplied type (" ++ show t2 ++ ")"
showError (MissingArrow t)      = "expected arrow type in the term \'" ++ show t ++ "\'" 
showError (UnboundVar ctx i)    = "variable indexed by \'" ++ show i ++ "\' not in the present context"
showError (MissingSum t)        = "expected sum type, recieved (" ++ show t ++ ")"
showError (SumMismatch a t)     = "expected type (" ++ show a ++ "), but recieved type (" ++ show t ++ ")"
showError (CaseBranchMismatch t1 t2) = "type mismatch in branches of case statement.  " ++ show t1 ++ " /= " ++ show t2
showError (CaseGuardMismatch)   = "type mismatch in guards, sum types do not match"
showError (CaseMissingSum)      = "missing sum types in case expression"



-- toFunct

toFunct :: Eq a => [(a, b)] -> Function a b
toFunct [] = \a -> Nothing
toFunct (x:xs) = \n -> if n == a then Just b else (toFunct xs) n where (a, b) = x



-- Typing

typeof :: Term -> Either Error Type
typeof = typeof0 (toFunct [])

typeof0 :: VContext -> Term -> Either Error Type
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
typeof0 ctx (Lft e t)      = do
  t1 <- typeof0 ctx e
  case t of
    Sum a b ->
      if t1 == a
        then return t
        else Left $ SumMismatch a t1
    _       -> Left $ MissingSum t
typeof0 ctx (Rit e t)      = do
  t1 <- typeof0 ctx e
  case t of
    Sum a b ->
      if t1 == b
        then return t
        else Left $ SumMismatch b t1
    _       -> Left $ MissingSum t
typeof0 ctx (Case e1 e2 e2' e3 e3') = do
  t1  <- typeof0 ctx e1
  t2  <- typeof0 ctx e2
  t2' <- typeof0 ctx e2'
  t3  <- typeof0 ctx e3
  t3' <- typeof0 ctx e3'
  case (t1, t2, t3) of
    (Sum a b, Sum c d, Sum e f) ->
      if a == c && c == e && b == d && d == f
        then if t2' == t3'
          then return t2'
          else Left $ CaseBranchMismatch t2' t3'
        else Left $ CaseGuardMismatch
    _ -> Left $ CaseMissingSum 
