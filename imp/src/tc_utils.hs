-- Utilities for the Type Checker

module TypeChecker.Utils
  ( Function(..)
  , nilmap
  , addBinding
  , toFunction
  )
where

type Function a b = a -> Maybe b

nilmap :: Function a b
nilmap _ = Nothing

addBinding :: Eq a => a -> b -> Function a b -> Function a b
addBinding a b f = \n -> if n == a then Just b else f n

toFunction :: Eq a => [(a, b)] -> Function a b
toFunction []          = nilmap
toFunction ((a, b):ps) = addBinding a b f where f = toFunction ps
