-- Abstract Syntax Module for the testtc.hs Type Checker

module Language.AbstractSyntax
  ( Term(..)
  , VContext(..)
  , nilmap
  , pushBinding
  , isValue
  )
where

import TypeChecker.Utils
import TypeChecker.Types

data Term = Abs    String Type   Term
          | App    Term   Term
          | Var    Int
          | Let    String Term   Term
          | Fix    Term
          | Record Fields
          | Proj   Term   String
          | Pair   Term   Term
          | Fst    Term
          | Snd    Term
          | If     Term   Term   Term
          | IsZero Term
          | Succ   Term
          | Pred   Term
          | Tru
          | Fls
          | Zero
          | EUnit
          | Error

type Fields = [(String, Term)]

type VContext = Function Int (String, Type)

instance Show Term where
  show = showTerm nilmap

shiftBindings :: VContext -> VContext
shiftBindings ctx = \n -> ctx $ n - 1

pushBinding :: VContext -> (String, Type) -> VContext
pushBinding ctx p = addBinding 0 p ctx' where ctx' = shiftBindings ctx

isValue :: Term -> Bool
isValue Tru         = True
isValue Fls         = True
isValue Zero        = True
isValue EUnit       = True
isValue Error       = True
isValue (Abs _ _ _) = True
isValue (Record _)  = True
isValue (Pair _ _)  = True
isValue (Succ t)    = isValue t
isValue _           = False

toInt :: Term -> Int
toInt Zero     = 0
toInt (Succ t) = 1 + (toInt t)
toInt _        = error "non-numeric args supplied to \'toInt\'"

showFields :: VContext -> Fields -> String
showFields _   [] = " "
showFields ctx [f]    = fst f ++ " = " ++ show (snd f)
showFields ctx (f:fs) = fst f ++ " = " ++ show (snd f) ++ "," ++ showFields ctx fs

showTerm :: VContext -> Term -> String
showTerm _   Tru           = "True"
showTerm _   Fls           = "False"
showTerm _   Zero          = "0"
showTerm _   EUnit         = "()"
showTerm _   Error         = "Error"
showTerm ctx (Record fs)   = "{" ++ showFields ctx fs ++ "}"
showTerm ctx (Proj t s)    = showTerm ctx t ++ "." ++ s
showTerm ctx (Pair t1 t2)  = "(" ++ showTerm ctx t1 ++ "," ++ showTerm ctx t2 ++ ")"
showTerm ctx (Let s t1 t2) = "let " ++ s ++ " = " ++ showTerm ctx t1 ++ " in " ++ showTerm ctx' t2 where ctx' = pushBinding ctx (s, Type $ TName "Dummy")
showTerm ctx (Fix t)       = "fix (" ++ showTerm ctx t ++ ")"
showTerm ctx (If t1 t2 t3) = "if " ++ s t1 ++ " then " ++ s t2 ++ " else " ++ s t3 where s a = showTerm ctx a
showTerm ctx (Fst t)       = "fst (" ++ showTerm ctx t ++ ")"
showTerm ctx (Snd t)       = "snd (" ++ showTerm ctx t ++ ")"
showTerm ctx (IsZero t)    = "iszero (" ++ showTerm ctx t ++ ")"
showTerm ctx (Succ t)
  | isValue t = show $ toInt (Succ t)
  | otherwise = "succ (" ++ showTerm ctx t ++ ")"
showTerm ctx (Pred t)      = "pred (" ++ showTerm ctx t ++ ")"
showTerm ctx (Abs s ty te) = "\\" ++ s ++ " : " ++ show ty ++ ". " ++ showTerm ctx' te where ctx' = pushBinding ctx (s, ty)
showTerm ctx (App t1 t2)   =
  front ++ " " ++ back
  where s t   = showTerm ctx t
        front = case t1 of Abs _ _ _ -> "(" ++ s t1 ++ ")"; _ -> s t1
        back  = case t2 of App _ _   -> "(" ++ s t2 ++ ")"; Abs _ _ _ -> "(" ++ s t2 ++ ")"; _ -> s t2
showTerm ctx (Var i)       =
  case ctx i of
    Nothing     -> "(Var " ++ show i ++ ")"
    Just (s, _) -> s
