-- Utilities for the testtc.hs Type Checker

module TypeChecker.Utils
  ( Function(..)
  , addBinding
  , toFunction
  )
where

type Function a b = a -> Maybe b

addBinding :: Eq a => a -> b -> Function a b -> Function a b
addBinding a b f = \n -> if n == a then Just b else f a 

toFunction :: Eq a => [(a, b)] -> Function a b
toFunction []          = \_ -> Nothing
toFunction ((a, b):ps) = addBinding a b f where f = toFunction ps
