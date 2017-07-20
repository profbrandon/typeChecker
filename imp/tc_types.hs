-- Types for the testtc.hs Type Checker

module TypeChecker.Types
  ( Type (..)
  , TExpr (..)
  , TContext (..)
  , nilmap
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
           deriving Eq

type TContext = Function String String

instance Show Type where
  show = showType nilmap

instance Show TExpr where
  show = showTExpr

showType :: TContext -> Type -> String
showType _   Top          = "Top"
showType _   Bottom       = "Bottom"
showType _   (Type t)     = show t
showType ctx (Forall v t) = "forall " ++ v ++ ". (" ++ showType ctx' t ++ ")" where ctx' = addBinding v v ctx

showTExpr :: TExpr -> String
showTExpr Bool        = "Bool"
showTExpr Nat         = "Nat"
showTExpr Unit        = "()"
showTExpr (TVar n)    = n
showTExpr (TName n)   = n
showTExpr (Arrow a b) =
  case a of
    Arrow _ _ -> "(" ++ show a ++ ") -> " ++ show b
    _         -> show a ++ " -> " ++ show b
