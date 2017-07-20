
module Parser
  ( Error(..)
  , parse
  )
where

import Language.AbstractSyntax
import Language.Tokens
import TypeChecker.Types
import TypeChecker.Utils

data Error = MissingParen
           | MissingExprStart [Token]
           | MissingPeriod
           | MissingColon
           | MissingElse
           | MissingThen
           | MissingId
           | MissingType
           | MissingTExpr
           | MissingIn
           | UnboundVariable
           deriving Show


parse :: [Token] -> Either Error Term
parse s = do
  (b, t1, _) <- expr nilmap s
  (_, t2, _) <- app nilmap t1 b
  return t2

expr :: VContext -> [Token] -> Either Error ([Token], Term, VContext)
expr ctx s = do
  (back, t, _) <- expr1 ctx s
  app ctx t back

app :: VContext -> Term -> [Token] -> Either Error ([Token], Term, VContext)
app ctx t [] = return ([], t, ctx)
app ctx t1 s =
  case s of
    RParen:_ -> return (s, t1, ctx)
    Then:_   -> return (s, t1, ctx)
    Else:_   -> return (s, t1, ctx)
    In:_     -> return (s, t1, ctx)
    _        -> do
      (back, t2, _) <- expr1 ctx s
      case back of
        RParen:_ -> return (back, App t1 t2, ctx)
        _        -> app ctx (App t1 t2) back  

expr1 :: VContext -> [Token] -> Either Error ([Token], Term, VContext)
expr1 ctx s =
  case s of
    Lambda:_   -> lambda ctx s
    LetT:_     -> llet ctx s
    IfT:_      -> cond ctx s
    (Id _):_   -> variable ctx s
    ZeroT:b    -> return (b, Zero, ctx)
    TruT:b     -> return (b, Tru, ctx)
    FlsT:b     -> return (b, Fls, ctx)
    SuccT:b1   -> do
      (b2, t, ctx') <- expr ctx b1
      return (b2, Succ t, ctx')
    PredT:b1   -> do
      (b2, t, ctx') <- expr ctx b1
      return (b2, Pred t, ctx')
    IsZeroT:b1 -> do
      (b2, t, ctx') <- expr ctx b1
      return (b2, IsZero t, ctx')
    FixT:b1    -> do
      (b2, t, ctx') <- expr ctx b1
      return (b2, Fix t, ctx')
    LParen:b1  -> do
      (b2, t, ctx') <- expr ctx b1
      case b2 of
        RParen:b3 -> return (b3, t, ctx')
        _         -> Left MissingParen
    _          -> Left $ MissingExprStart s

lambda :: VContext -> [Token] -> Either Error ([Token], Term, VContext)
lambda ctx (Lambda:(Id name):back) =
  case back of
    Colon:b1 -> do
      (b2, ty, _) <- ttype nilmap b1
      let ctx' = pushBinding ctx (name, ty)
      case b2 of
        Period:b3 -> do
          (b4, t, ctx'') <- expr ctx' b3
          return (b4, Abs name ty t, ctx'')
        _ -> Left MissingPeriod
    _ -> Left MissingColon

llet :: VContext -> [Token] -> Either Error ([Token], Term, VContext)
llet ctx (LetT:(Id name):Equ:back) = do
  (b1, e1, ctx') <- expr ctx back
  let ctx' = pushBinding ctx (name, Type $ TName "Dummy")
  case b1 of
    In:b2 -> do
      (b3, e2, ctx'') <- expr ctx' b2
      return $ (b3, Let name e1 e2, ctx'')
    _ -> Left MissingIn

cond :: VContext -> [Token] -> Either Error ([Token], Term, VContext)
cond ctx (IfT:back) = do
  (b1, t1, c1) <- expr ctx back
  case b1 of
    Then:b2 -> do
      (b3, t2, c2) <- expr c1 b2
      case b3 of
        Else:b4 -> do
          (b5, t3, c3) <- expr c2 b4
          return (b5, If t1 t2 t3, c3)
        _ -> Left MissingElse
    _ -> Left MissingThen 

variable :: VContext -> [Token] -> Either Error ([Token], Term, VContext)
variable ctx ((Id name):xs) = 
  let ma = findBind ctx name
  in case ma of
    Nothing        -> Left UnboundVariable
    Just (i, s, _) -> return (xs, Var i, ctx)
variable _ _ = Left MissingId

findBind :: VContext -> String -> Maybe (Int, String, Type)
findBind = findBind0 0

findBind0 :: Int -> VContext -> String -> Maybe (Int, String, Type)
findBind0 i ctx name =
  case ma of
    Nothing     -> Nothing
    Just (s, t) ->
      if s == name
        then Just (i, s, t)
        else findBind0 (i + 1) ctx name
  where ma = ctx i 

ttype :: TContext -> [Token] -> Either Error ([Token], Type, TContext)
ttype _ [] = Left MissingType
ttype ctx (ForallT:(Id name):Period:ts) = do
  (ts', ty, ctx') <- ttype (addBinding name name ctx) ts
  return (ts', Forall name ty, ctx')
ttype ctx (LParen:ts) = do
  (ts', ty, ctx') <- ttype ctx ts
  case ts' of
    RParen:back -> return (back, ty, ctx')
    _ -> Left MissingParen
ttype ctx ts = do
  (ts', te, ctx') <- texpr ctx ts
  return (ts', Type te, ctx')

texpr :: TContext -> [Token] -> Either Error ([Token], TExpr, TContext)
texpr _   [] = Left MissingTExpr
texpr ctx s  =
  case s of
    (Id "Bool"):back -> arrow ctx Bool back
    (Id "Nat"):back  -> arrow ctx Nat back
    (Id name):back   ->
      case ctx name of
        Nothing -> arrow ctx (TName name) back
        Just _  -> arrow ctx (TVar name) back
    LParen:back      -> do
      (b , ty1, ctx') <- texpr ctx back
      (b', ty2, ctx'') <- arrow ctx' ty1 b
      case b' of
        RParen:s' -> arrow ctx'' ty2 s'
        _         -> Left MissingParen

arrow :: TContext -> TExpr -> [Token] -> Either Error ([Token], TExpr, TContext)
arrow ctx t [] = return ([], t, ctx)
arrow ctx t s  =
  case s of
    Arr:back -> do
      (b, t2, ctx') <- texpr ctx back
      return (b, Arrow t t2, ctx')
    _ -> return (s, t, ctx)
