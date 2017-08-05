module TypeChecker.Types
  ( Type (..)
  , TExpr (..)
  , TContext (..)
  , addAllBindings
  , addBinding
  , nilmap
  , isConcrete
  )
where

import TypeChecker.Utils

data Type = Forall String Type
          | Type   TExpr
          | Bottom
          | Top
          deriving Eq

data TExpr = Arrow TExpr  TExpr
           | TVar  String
           | TName String
           | Bool
           | Nat
           | Unit
           | List  TExpr
           | Sum   TExpr  TExpr
           | TPair TExpr  TExpr
           | TRec  Fields
           deriving Eq

type Fields = [(String, Type)]

type TContext = Function String String

instance Show Type where
  show = showType nilmap

instance Show TExpr where
  show = showTExpr

addAllBindings :: [String] -> TContext -> TContext
addAllBindings []     ctx = ctx
addAllBindings (x:xs) ctx = addBinding x x ctx' where ctx' = addAllBindings xs ctx

showFields :: Fields -> String
showFields []  = " "
showFields [f] = fst f ++ " : " ++ (show . snd) f
showFields (f:fs) = fst f ++ " : " ++ show (snd f) ++ "," ++ showFields fs

showType :: TContext -> Type -> String
showType _   Top          = "Top"
showType _   Bottom       = "Bottom"
showType _   (Type t)     = show t
showType ctx (Forall v t) = "forall " ++ v ++ ". (" ++ showType ctx' t ++ ")" where ctx' = addBinding v v ctx

showTExpr :: TExpr -> String
showTExpr Bool        = "Bool"
showTExpr Nat         = "Nat"
showTExpr Unit        = "()"
showTExpr (List a)    = "[" ++ show a ++ "]"
showTExpr (TVar n)    = n
showTExpr (TName n)   = n
showTExpr (TRec fs)   = "{" ++ showFields fs ++ "}"
showTExpr (TPair a b) = "(" ++ show a ++ "," ++ show b ++ ")"
showTExpr (Sum a b)   = "(" ++ show a ++ "|" ++ show b ++ ")"
showTExpr (Arrow a b) =
  case a of
    Arrow _ _ -> "(" ++ show a ++ ") -> " ++ show b
    _         -> show a ++ " -> " ++ show b

isConcrete0 :: Type -> Bool
isConcrete0 (Forall _ _) = False
isConcrete0 (Type t)     = isConcrete t

isConcrete :: TExpr -> Bool
isConcrete (TVar _)     = False
isConcrete Bool         = True
isConcrete Nat          = True
isConcrete Unit         = True
isConcrete (TName _)    = True
isConcrete (List  a)    = isConcrete a
isConcrete (TPair a  b) = isConcrete a && isConcrete b
isConcrete (Sum   a  b) = isConcrete a && isConcrete b
isConcrete (Arrow a  b) = isConcrete a && isConcrete b
isConcrete (TRec  fs)   = and $ map (isConcrete0 . snd) fs
