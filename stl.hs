-- Type Checker for the Simply-Typed Lambda Calculus

-- Supported Language Features:

--   Abstractions
--   Application
--   Variables

-- Supported Typing Features:

--   Arrow Types (Function Types)
--   Type Variables

module STLambda
  ( Term (..)
  , Type (..)
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

data Type = Arrow Type Type
          | TVar String
           deriving Eq

type Function a b = a -> Maybe b

instance Show Term where
  show = showTerm (\a -> Nothing)

instance Show Type where
  show = showType


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
showTerm ctx (Abs s ty tm) = 
  "\\" ++ s ++ " : " ++ show ty ++ ". " ++ showTerm ctx' tm
  where ctx' = pushBinding ctx (s, ty)
showTerm ctx (App t1 t2)   = 
  "(" ++ showTerm ctx t1 ++ ") (" ++ showTerm ctx t2 ++ ")"
showTerm ctx (Var v)       = 
  case ctx v of
    Nothing     -> error "attempted access of unbound variable"
    Just (s, _) -> s

showType :: Type -> String
showType (Arrow a b) =
  case a of
    Arrow _ _ -> wparen
    _         -> showType a ++ " -> " ++ showType b
    where wparen = "(" ++ showType a ++ ") -> " ++ showType b
showType (TVar s)    = s

-- toFunct

toFunct :: Eq a => [(a, b)] -> Function a b
toFunct [] = \a -> Nothing
toFunct (x:xs) = \n -> if n == a then Just b else (toFunct xs) n where (a, b) = x

-- Typing

typeof :: Term -> Type
typeof = typeof0 (toFunct [])

typeof0 :: VContext -> Term -> Type
typeof0 ctx (Abs s ty1 tm) =
  Arrow ty1 ty2
  where ctx' = pushBinding ctx (s, ty1)
        ty2  = typeof0 ctx' tm
typeof0 ctx (App t1 t2)    =
  case ty1 of
    Arrow ty11 ty12 ->
      if ty11 == ty2
        then ty12
        else error "parameter type mismatch"
    _            -> error "arrow type expected as applicand"
    where ty1 = typeof0 ctx t1
          ty2 = typeof0 ctx t2
typeof0 ctx (Var v)        = 
  case ctx v of
    Nothing     -> error "attempted access of unbound variable in function \'typeof\'"
    Just (_, t) -> t
