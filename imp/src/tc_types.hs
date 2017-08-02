module TypeChecker.Types
  ( Type (..)
  , TExpr (..)
  , TContext (..)
  , addAllBindings
  , addBinding
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
showTExpr (TVar n)    = n
showTExpr (TName n)   = n
showTExpr (TRec fs)   = "{" ++ showFields fs ++ "}"
showTExpr (TPair a b) = "(" ++ show a ++ "," ++ show b ++ ")"
showTExpr (Arrow a b) =
  case a of
    Arrow _ _ -> "(" ++ show a ++ ") -> " ++ show b
    _         -> show a ++ " -> " ++ show b
