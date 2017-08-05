-- Module for the abstract syntax

module Language.AbstractSyntax
  ( Term(..)
  , Branches(..)
  , VContext(..)
  , pushBinding
  , pushAllBindings
  , isValue
  , findPVars
  , addPatterns
  )
where

import Prelude hiding (showList)
import Data.List (delete, lookup)
import Data.Maybe (isJust)
import Text.Parsec (SourcePos)

import TypeChecker.Utils (Function(..), nilmap, addBinding)
import TypeChecker.Types (Type(..), TExpr(..))
import Language.Patterns (Pat(..), countVars)

data Term = Var    Int                  SourcePos
          | App    Term   Term          SourcePos
          | Abs    String Type     Term SourcePos
          | If     Term   Term     Term SourcePos
          | Let    Pat    Term     Term SourcePos
          | Case   Term   Branches      SourcePos
          | Proj   Term   String        SourcePos
          | Record Fields               SourcePos
          | Pair   Term   Term          SourcePos
          | Cons   Term   Term          SourcePos
          | ELeft  Term   Type          SourcePos
          | ERight Term   Type          SourcePos
          | Fix    Term                 SourcePos
          | Fst    Term                 SourcePos
          | Snd    Term                 SourcePos
          | Succ   Term                 SourcePos
          | Pred   Term                 SourcePos
          | IsZero Term                 SourcePos
          | Tru                         SourcePos
          | Fls                         SourcePos
          | Zero                        SourcePos
          | EUnit                       SourcePos
          | Nil                         SourcePos

type Fields = [(String, Term)]

type Branches = [(Pat, Term)]

type VContext = Function Int (String, Type)

instance Show Term where
  show = showTerm nilmap

-- Shift all bindings by +1
shiftBindings :: VContext -> VContext
shiftBindings ctx = \n -> ctx $ n - 1

pushBinding :: VContext -> (String, Type) -> VContext
pushBinding ctx p = addBinding 0 p ctx' where ctx' = shiftBindings ctx

pushAllBindings :: VContext -> [(String, Type)] -> VContext
pushAllBindings ctx = foldl (pushBinding) ctx 

findPVars :: Pat -> [String]
findPVars (PPair  a b) = findPVars a ++ findPVars b
findPVars (PRec   ps)  = concatMap (\(_, p) -> findPVars p) ps
findPVars (PSucc  p)   = findPVars p
findPVars (PCons  a b) = findPVars a ++ findPVars b
findPVars (PLeft  p)   = findPVars p
findPVars (PRight p)   = findPVars p
findPVars (PVar   s)   = [s]
findPVars _            = []

addPatterns :: VContext -> Pat -> VContext
addPatterns vctx p = pushAllBindings vctx ps where ps = map (\s -> (s, Type $ TName "")) $ findPVars p

isValue :: Term -> Bool
isValue (Record   f _) = and $ map (isValue . snd) f
isValue (Pair   a b _) = and $ map isValue [a,b]
isValue (Cons   a b _) = and $ map isValue [a,b]
isValue (Succ     t _) = isValue t
isValue (ELeft  t _ _) = isValue t
isValue (ERight t _ _) = isValue t 
isValue (Abs  _ _ _ _) = True
isValue (Tru   _)      = True
isValue (Fls   _)      = True
isValue (Zero  _)      = True
isValue (EUnit _)      = True
isValue (Nil   _)      = True
isValue _              = False

toInt :: Term -> Int
toInt (Zero _)   = 0
toInt (Succ t _) = 1 + (toInt t)
toInt _          = error "non-numeric args supplied to \'toInt\'"

showFields :: VContext -> Fields -> String
showFields _   []     = ""
showFields ctx [f]    = fst f ++ " = " ++ showTerm ctx (snd f)
showFields ctx (f:fs) = fst f ++ " = " ++ showTerm ctx (snd f) ++ "," ++ showFields ctx fs

showBranches :: VContext -> Branches -> String
showBranches ctx [(p, t)]    = show p ++ " -> " ++ showTerm ctx' t where ctx' = addPatterns ctx p
showBranches ctx ((p, t):bs) = show p ++ " -> " ++ showTerm ctx' t ++ "; " ++ showBranches ctx bs where ctx' = addPatterns ctx p

showList :: VContext -> Term -> String
showList _   (Nil  _)           = ""
showList ctx (Cons t (Nil _) _) = showTerm ctx t
showList ctx (Cons t ts _)      = showTerm ctx t ++ ',':showList ctx ts
showList ctx _                  = error "non-list args supplied to \'showList\'"

showTerm :: VContext -> Term -> String
showTerm ctx (Var    i  _)    =
  case ctx i of
    Nothing     -> "(Var " ++ show i ++ ")"
    Just (s, _) -> s
showTerm ctx (App    t1 t2 _) =
  front ++ " " ++ back
  where s t   = showTerm ctx t
        front = case t1 of Abs _ _ _ _ -> "(" ++ s t1 ++ ")"; _ -> s t1
        back  = case t2 of App _ _ _   -> "(" ++ s t2 ++ ")"; Abs _ _ _ _ -> "(" ++ s t2 ++ ")"; _ -> s t2
showTerm ctx (Abs s  ty te _) = "\\"    ++ s ++ " : " ++ show ty ++ ". " ++ showTerm ctx' te where ctx' = pushBinding ctx (s, ty)
showTerm ctx (If  t1 t2 t3 _) = "if "   ++ s t1 ++ " then " ++ s t2 ++ " else " ++ s t3 where s a = showTerm ctx a
showTerm ctx (Let p  t1 t2 _) = "let "  ++ show p ++ " = " ++ showTerm ctx t1 ++ " in " ++ showTerm ctx' t2 where ctx' = addPatterns ctx p
showTerm ctx (Case   t  bs _) = "case " ++ showTerm ctx t ++ " of " ++ showBranches ctx bs
showTerm ctx (Proj   t  s  _) = showTerm ctx t ++ "." ++ s
showTerm ctx (Record    fs _) = "{"        ++ showFields ctx fs ++ "}"
showTerm ctx (Pair   t1 t2 _) = "("        ++ showTerm ctx t1 ++ "," ++ showTerm ctx t2 ++ ")"
showTerm ctx (Cons t1 t2 pos) 
  | isValue t1 && isValue t2  = "[" ++ showList ctx (Cons t1 t2 pos) ++ "]"
  | isValue t2                = "(" ++ showTerm ctx t1 ++ ")@[" ++ showList ctx t2 ++ "]"
  | otherwise                 = "(" ++ showTerm ctx t1 ++ ")@" ++ showTerm ctx t2
showTerm ctx (ELeft  t  ty _) = "Left "    ++ showTerm ctx t ++ " : " ++ show ty
showTerm ctx (ERight t  ty _) = "Right "   ++ showTerm ctx t ++ " : " ++ show ty
showTerm ctx (Fix    t  _)    = "fix ("    ++ showTerm ctx t ++ ")"
showTerm ctx (Fst    t  _)    = "fst ("    ++ showTerm ctx t ++ ")"
showTerm ctx (Snd    t  _)    = "snd ("    ++ showTerm ctx t ++ ")"
showTerm ctx (Succ   t  _)
  | isValue t                 = show $ 1 + toInt t
  | otherwise                 = "succ ("   ++ showTerm ctx t ++ ")"
showTerm ctx (Pred   t  _)    = "pred ("   ++ showTerm ctx t ++ ")"
showTerm ctx (IsZero t  _)    = "iszero (" ++ showTerm ctx t ++ ")"
showTerm _   (Tru    _)       = "True"
showTerm _   (Fls    _)       = "False"
showTerm _   (Zero   _)       = "0"
showTerm _   (EUnit  _)       = "()"
showTerm _   (Nil    _)       = "[]"
