
module Parser
  ( Error(..)
  , parse
  )
where

import Data.Char (isLower)

import Language.AbstractSyntax
import Language.Tokens
import TypeChecker.Types
import TypeChecker.Utils
import TypeChecker.UniversalQuantifiers.Utils (quantify')

data Error = MissingParen       Token
           | MissingExprStart   Token
           | MissingPeriod      Token
           | MissingColon       Token
           | MissingElse        Token
           | MissingThen        Token
           | MissingId          Token
           | MissingType
           | MissingTExpr
           | MissingIn          Token
           | UnboundVariable    String
           | IncorrectUniversal String

instance Show Error where
  show = showError 

showError :: Error -> String
showError (MissingParen t)     = "parenthesis expected, received " ++ show t
showError (MissingExprStart t) = "start to expression expected, recieved " ++ show t
showError (MissingPeriod t)    = "body separator (.) expected, recieved " ++ show t
showError (MissingColon t)     = "type operator (:) expected, recieved " ++ show t
showError (MissingElse t)      = "expected \'else\' keyword, recieved " ++ show t
showError (MissingThen t)      = "expected \'then\' keyword, recieved " ++ show t
showError (MissingId t)        = "identifier expected, recieved " ++ show t
showError MissingType          = "type expected, recieved no further input"
showError MissingTExpr         = "type expression expected, recieved no further input"
showError (MissingIn t)        = "expected \'in\' keyword, recieved " ++ show t
showError (UnboundVariable n)  = "unbound variable \'" ++ n ++ "\'"
showError (IncorrectUniversal n) = "incorrect universal quantifier. \'" ++ n ++ "\' must be all lowercase"

parse :: [Token] -> Either Error Term
parse s = do
  (_, t, _) <- expr nilmap s
  return t

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
    Comma:_  -> return (s, t1, ctx)
    EOT:_    -> return (s, t1, ctx)
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
    FstT:b1    -> fun b1 Fst
    SndT:b1    -> fun b1 Snd
    SuccT:b1   -> fun b1 Succ
    PredT:b1   -> fun b1 Pred
    IsZeroT:b1 -> fun b1 IsZero
    FixT:b1    -> fun b1 Fix
    LParen:RParen:b -> return (b, EUnit, ctx)
    LParen:b1  -> do
      (b2, t, ctx') <- expr ctx b1
      case b2 of
        RParen:b3 -> return (b3, t, ctx')
        Comma:b3  -> do
          (b4, t2, _) <- expr ctx b3
          case b4 of
            RParen:b5 -> return (b5, Pair t t2, ctx)
            q:_       -> Left $ MissingParen q
        q:_       -> Left $ MissingParen q
    q:_        -> Left $ MissingExprStart q
  where fun b n = do (b2, t, ctx') <- expr ctx b; return (b2, n t, ctx')

lambda :: VContext -> [Token] -> Either Error ([Token], Term, VContext)
lambda ctx (Lambda:(Id name):back) =
  case back of
    Colon:b1 -> do
      (b2, ty) <- ttype b1
      let ctx' = pushBinding ctx (name, ty)
      case b2 of
        Period:b3 -> do
          (b4, t, ctx'') <- expr ctx' b3
          return (b4, Abs name ty t, ctx'')
        q:_       -> Left $ MissingPeriod q
    q:_      -> Left $ MissingColon q

llet :: VContext -> [Token] -> Either Error ([Token], Term, VContext)
llet ctx (LetT:(Id name):Equ:back) = do
  (b1, e1, ctx') <- expr ctx back
  let ctx' = pushBinding ctx (name, Type $ TName "")
  case b1 of
    In:b2 -> do
      (b3, e2, ctx'') <- expr ctx' b2
      return $ (b3, Let name e1 e2, ctx'')
    q:_   -> Left $ MissingIn q

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
        q:_     -> Left $ MissingElse q
    q:_     -> Left $ MissingThen q

variable :: VContext -> [Token] -> Either Error ([Token], Term, VContext)
variable ctx ((Id name):xs) = 
  let ma = findBind ctx name
  in case ma of
    Nothing        -> Left $ UnboundVariable name
    Just (i, s, _) -> return (xs, Var i, ctx)
variable _ (q:_) = Left $ MissingId q

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

ttype :: [Token] -> Either Error ([Token], Type)
ttype [] = Left MissingType
ttype (ForallT:(Id name):Period:ts) =
  if and (map (isLower) name)
    then do
      (ts', ty) <- ttype ts
      return (ts', quantify' $ Forall name ty)
    else Left $ IncorrectUniversal name
ttype (LParen:RParen:ts) = do
  (ts', te) <- texpr (LParen:RParen:ts)
  return (ts', quantify' $ Type te)
ttype (LParen:ts) = do
  (ts', ty) <- ttype ts
  case ts' of
    RParen:back -> return (back, ty)
    Comma:_     -> do
      (ts'', te) <- texpr $ LParen:ts
      return (ts'', quantify' $ Type te)
    q:_         -> Left $ MissingParen q
ttype ts = do
  (ts', te) <- texpr ts
  return (ts', quantify' $ Type te)

texpr :: [Token] -> Either Error ([Token], TExpr)
texpr []                 = Left $ MissingTExpr
texpr (LParen:RParen:b)  = arrow Unit b
texpr ((Id "Bool"):back) = arrow Bool back
texpr ((Id "Nat"):back)  = arrow Nat back
texpr ((Id name):back)
  | and (map (isLower) name) = arrow (TVar name) back
  | otherwise = arrow (TName name) back
texpr (LParen:b0)        = do
  (b1, ty1) <- texpr b0
  case b1 of
    Comma:b2 -> do
      (b3, ty2) <- texpr b2
      case b3 of
        RParen:b4 -> arrow (TPair ty1 ty2) b4
        q:_       -> Left $ MissingParen q
    _        -> do
      (b2, ty2) <- arrow ty1 b1
      case b2 of
        RParen:b3 -> arrow ty2 b2
        q:_       -> Left $ MissingParen q

arrow :: TExpr -> [Token] -> Either Error ([Token], TExpr)
arrow t [] = return ([], t)
arrow t s  =
  case s of
    Arr:back -> do
      (b, t2) <- texpr back
      return (b, Arrow t t2)
    _ -> return (s, t)
