-- Type Checker for the Simply-Typed Lambda Calculus

-- Supported Language Features:

--   Abstractions
--   Application
--   Variables
--   Tuples
--   Tuple Projections

-- Supported Typing Features:

--   Arrow Types (Function Types)
--   Type Variables
--   Tuple Types:  (a, b,...,c)

module STLambdaTuple
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
          | Tup [Term]
          | At Int Term

data Type = Arrow Type Type
          | TVar  String
          | TTup [Type]
           deriving Eq

data Error = ParamMismatch Type     Type
           | MissingArrow  Term
           | UnboundVar    VContext Int
           | IncProj Int Int

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
showTerm ctx (At i t)      = "(" ++ showTerm ctx t ++ ")." ++ show i 
showTerm ctx (Abs s ty tm) = 
  "\\" ++ s ++ " : " ++ show ty ++ ". " ++ showTerm ctx' tm
  where ctx' = pushBinding ctx (s, ty)
showTerm ctx (App t1 t2)   = 
  "(" ++ showTerm ctx t1 ++ ") (" ++ showTerm ctx t2 ++ ")"
showTerm ctx (Var v)       = 
  case ctx v of
    Nothing     -> "(Var " ++ show v ++ ")"
    Just (s, _) -> s
showTerm ctx (Tup ts) = "(" ++ showTuple ts' ++ ")" where ts' = map (showTerm ctx) ts

showTuple :: [String] -> String
showTuple []     = ""
showTuple [t]    = t
showTuple (t:ts) = t ++ "," ++ showTuple ts

showType :: Type -> String
showType (TTup ts)   = "(" ++ showTuple ts' ++ ")" where ts' = map (showType) ts
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
showError (IncProj 0 i2)        = "cannot project elements of an empty tuple"
showError (IncProj i1 i2)       = "projection in range 0 <= p < " ++ show (i1 - 1) ++ " expected, but supplied projection of " ++ show i2



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
typeof0 ctx (Tup ts)       = do
  ts' <- mapM (typeof0 ctx) ts
  return $ TTup ts'
typeof0 ctx (At i t)       = do
  ty <- typeof0 ctx t
  case ty of
    TTup ts -> if length ts > i
      then return $ ts !! i
      else Left $ IncProj (length ts) i
    _       -> Left $ ParamMismatch (TTup [TVar "..."]) ty
