-- Abstract Syntax Module for the testtc.hs Type Checker

module Language.AbstractSyntax
  ( Term(..)
  , VContext(..)
  , nilmap
  , pushBinding
  , pushAllBindings
  , isValue
  , addPatterns
  )
where

import Data.List (delete, lookup)
import Text.Parsec (SourcePos)

import TypeChecker.Utils
import TypeChecker.Types
import Language.Patterns

data Term = Abs    String Type   Term SourcePos
          | App    Term   Term        SourcePos
          | Var    Int                SourcePos
          | Let    Pat    Term   Term SourcePos
          | Fix    Term               SourcePos
          | Record Fields             SourcePos
          | Proj   Term   String      SourcePos
          | Pair   Term   Term        SourcePos
          | Fst    Term               SourcePos
          | Snd    Term               SourcePos
          | If     Term   Term   Term SourcePos
          | IsZero Term               SourcePos
          | Succ   Term               SourcePos
          | Pred   Term               SourcePos
          | Tru                       SourcePos
          | Fls                       SourcePos
          | Zero                      SourcePos
          | EUnit                     SourcePos
          deriving Eq

type Fields = [(String, Term)]

type VContext = Function Int (String, Type)

instance Show Term where
  show = showTerm nilmap

shiftBindings :: VContext -> VContext
shiftBindings ctx = \n -> ctx $ n - 1

pushBinding :: VContext -> (String, Type) -> VContext
pushBinding ctx p = addBinding 0 p ctx' where ctx' = shiftBindings ctx

pushAllBindings :: VContext -> [(String, Type)] -> VContext
pushAllBindings ctx [] = ctx
pushAllBindings ctx (p:ps) = pushAllBindings ctx' ps where ctx' = pushBinding ctx p

addRecPat :: VContext -> [(String, Pat)] -> VContext
addRecPat ctx []       = ctx
addRecPat ctx ((s, p):ps) = addRecPat ctx' ps where ctx' = addPatterns ctx p

addPatterns :: VContext -> Pat -> VContext
addPatterns ctx (PVar s)    = pushBinding ctx (s, Type $ TName "")
addPatterns ctx (PPair a b) = addPatterns ctx' b where ctx' = addPatterns ctx a
addPatterns ctx (PRec ps)   = addRecPat ctx ps

isValue :: Term -> Bool
isValue (Tru _)        = True
isValue (Fls _)        = True
isValue (Zero _)       = True
isValue (EUnit _)      = True
isValue (Abs _ _ _ _)  = True
isValue (Record _ _)   = True
isValue (Pair _ _ _)   = True
isValue (Succ t _)     = isValue t
isValue _              = False

toInt :: Term -> Int
toInt (Zero _)   = 0
toInt (Succ t _) = 1 + (toInt t)
toInt _          = error "non-numeric args supplied to \'toInt\'"

showFields :: VContext -> Fields -> String
showFields _   [] = " "
showFields ctx [f]    = fst f ++ " = " ++ showTerm ctx (snd f)
showFields ctx (f:fs) = fst f ++ " = " ++ showTerm ctx (snd f) ++ "," ++ showFields ctx fs

showTerm :: VContext -> Term -> String
showTerm _   (Tru _)         = "True"
showTerm _   (Fls _)         = "False"
showTerm _   (Zero _)        = "0"
showTerm _   (EUnit _)       = "()"
showTerm ctx (Record fs _)   = "{" ++ showFields ctx fs ++ "}"
showTerm ctx (Proj t s _)    = showTerm ctx t ++ "." ++ s
showTerm ctx (Pair t1 t2 _)  = "(" ++ showTerm ctx t1 ++ "," ++ showTerm ctx t2 ++ ")"
showTerm ctx (Let p t1 t2 _) = "let " ++ show p ++ " = " ++ showTerm ctx t1 ++ " in " ++ showTerm ctx' t2 where ctx' = addPatterns ctx p
showTerm ctx (Fix t _)       = "fix (" ++ showTerm ctx t ++ ")"
showTerm ctx (If t1 t2 t3 _) = "if " ++ s t1 ++ " then " ++ s t2 ++ " else " ++ s t3 where s a = showTerm ctx a
showTerm ctx (Fst t _)       = "fst (" ++ showTerm ctx t ++ ")"
showTerm ctx (Snd t _)       = "snd (" ++ showTerm ctx t ++ ")"
showTerm ctx (IsZero t _)    = "iszero (" ++ showTerm ctx t ++ ")"
showTerm ctx (Succ t pos)
  | isValue t = show $ toInt (Succ t pos)
  | otherwise = "succ (" ++ showTerm ctx t ++ ")"
showTerm ctx (Pred t _)      = "pred (" ++ showTerm ctx t ++ ")"
showTerm ctx (Abs s ty te _) = "\\" ++ s ++ " : " ++ show ty ++ ". " ++ showTerm ctx' te where ctx' = pushBinding ctx (s, ty)
showTerm ctx (App t1 t2 _)   =
  front ++ " " ++ back
  where s t   = showTerm ctx t
        front = case t1 of Abs _ _ _ _ -> "(" ++ s t1 ++ ")"; _ -> s t1
        back  = case t2 of App _ _ _   -> "(" ++ s t2 ++ ")"; Abs _ _ _ _ -> "(" ++ s t2 ++ ")"; _ -> s t2
showTerm ctx (Var i _)       =
  case ctx i of
    Nothing     -> "(Var " ++ show i ++ ")"
    Just (s, _) -> s