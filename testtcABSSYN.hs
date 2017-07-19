-- Abstract Syntax Module for the testtc.hs Type Checker

module Language.AbstractSyntax
  ( Term(..)
  , VContext(..)
  , pushBinding
  )
where

import TypeChecker.Utils
import TypeChecker.Types

data Term = Abs    String Type Term
          | App    Term   Term
          | Var    Int
          | Fix    Term
          | If     Term   Term Term
          | IsZero Term
          | Succ   Term
          | Pred   Term
          | Tru
          | Fls
          | Zero
          | EUnit
          | Error

type VContext = Function Int (String, Type)

instance Show Term where
  show = showTerm (toFunction [])

shiftBindings :: VContext -> VContext
shiftBindings ctx = \n -> ctx $ n - 1

pushBinding :: VContext -> (String, Type) -> VContext
pushBinding ctx p = addBinding 0 p ctx' where ctx' = shiftBindings ctx

showTerm :: VContext -> Term -> String
showTerm _   Tru           = "True"
showTerm _   Fls           = "False"
showTerm _   Zero          = "0"
showTerm _   EUnit         = "()"
showTerm _   Error         = "Error"
showTerm ctx (Fix t)       = "fix (" ++ showTerm ctx t ++ ")"
showTerm ctx (If t1 t2 t3) = "if " ++ s t1 ++ " then " ++ s t2 ++ " else " ++ s t3 where s a = showTerm ctx a
showTerm ctx (IsZero t)    = "iszero (" ++ showTerm ctx t ++ ")"
showTerm ctx (Succ t)      = "succ (" ++ showTerm ctx t ++ ")"
showTerm ctx (Pred t)      = "pred (" ++ showTerm ctx t ++ ")"
showTerm ctx (Abs s ty te) = "\\" ++ s ++ " : " ++ show ty ++ ". " ++ showTerm ctx' te where ctx' = pushBinding ctx (s, ty)
showTerm ctx (App t1 t2)   =
  case t1 of
    Abs _ _ _ -> "(" ++ showTerm ctx t1 ++ ") " ++ showTerm ctx t2
    _         -> showTerm ctx t1 ++ " " ++ showTerm ctx t2
showTerm ctx (Var i)       =
  case ctx i of
    Nothing     -> "(Var " ++ show i ++ ")"
    Just (s, _) -> s
