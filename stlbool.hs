-- Type Checker for the Simply-Typed Lambda Calculus

-- Supported Language Features:

--   Abstractions
--   Application
--   Variables
--   Conditionals
--   Boolean Values

-- Supported Typing Features:

--   Arrow Types (Function Types)
--   Type Variables
--   Bool Type

module STLambdaBool
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
          | If Term Term Term
          | Tru
          | Fls

data Type = Arrow Type Type
          | TVar String
          | Bool
           deriving Eq

data Error = ParamMismatch Type Type
           | MissingArrow Type
           | UnboundVar VContext Int
           | NonBoolGaurd Type
           | CondBranchMismatch Type Type

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
showTerm _   Tru           = "True"
showTerm _   Fls           = "False"
showTerm ctx (If t1 t2 t3) = "if " ++ showTerm ctx t1 ++ " then " ++ showTerm ctx t2 ++ " else " ++ showTerm ctx t3
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
showType Bool        = "Bool"
showType (Arrow a b) =
  case a of
    Arrow _ _ -> wparen
    _         -> showType a ++ " -> " ++ showType b
    where wparen = "(" ++ showType a ++ ") -> " ++ showType b
showType (TVar s)    = s

showError :: Error -> String
showError (ParamMismatch t1 t2) = "Parameter type mismatch. Expected type (" ++ show t1 ++ "), supplied type (" ++ show t2 ++ ")"
showError (MissingArrow t)      = "Expected arrow type, supplied type (" ++ show t ++ ")" 
showError (UnboundVar ctx i)    = "Variable indexed by \'" ++ show i ++ "\' not in the present context" 
showError (NonBoolGaurd t)      = "Expected type Bool to guard, supplied type (" ++ show t ++ ")"
showError (CondBranchMismatch t1 t2) = "Type mismatch in conditional branchs. (" ++ show t1 ++ ") is not equivalent to (" ++ show t2 ++ ")"



-- toFunct

toFunct :: Eq a => [(a, b)] -> Function a b
toFunct [] = \a -> Nothing
toFunct (x:xs) = \n -> if n == a then Just b else (toFunct xs) n where (a, b) = x



-- Typing

typeof :: Term -> Either Error Type
typeof = typeof0 (toFunct [])

typeof0 :: VContext -> Term -> Either Error Type
typeof0 _   Tru            = return Bool
typeof0 _   Fls            = return Bool
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
    _            -> Left $ MissingArrow ty1
typeof0 ctx (Var v)        = 
  case ctx v of
    Nothing     -> Left $ UnboundVar ctx v
    Just (_, t) -> Right t
typeof0 ctx (If t1 t2 t3)  = do
  ty1 <- typeof0 ctx t1
  ty2 <- typeof0 ctx t2
  ty3 <- typeof0 ctx t3
  if ty1 == Bool
    then
      if ty2 == ty3
        then Right ty2
        else Left $ CondBranchMismatch ty2 ty3
    else Left $ NonBoolGaurd ty1 
