module Syntax where

import Enrichment
import Test
import Data.Set (Set)
import qualified Data.Set as Set

data Var = C Char
    | P Var -- prime
    deriving (Eq, Ord)

showVar :: Var -> String
showVar (C c) = [c]
showVar (P v) = (showVar v) ++ "'"

instance Show Var where
    show v = showVar v

data Term = V Var -- variable
    | L Var Term -- lambda
    | A Term Term -- application
    | R Rich -- rich type (constant)
    deriving (Eq)

termSize :: Term -> Int
termSize (V v) = 1
termSize (R r) = 1
termSize (A x y) = 1 + termSize x + termSize y


testTermSize = testEq (termSize (A (V (C 'a')) (R (RealNum 0)))) 3

freeVariables :: Term -> Set Var
freeVariables (V x) = Set.singleton x
freeVariables (L x t) = Set.delete x (freeVariables t)
freeVariables (A t1 t2) = Set.union (freeVariables t1) (freeVariables t2)
freeVariables (R _) = Set.empty

testFreeVariables = testEq (freeVariables (A (V (C 'a')) (L (C 'b') (A (V (C 'c')) (V (C 'b')))))) (Set.fromList [C 'a', C 'c'])


test = do
    putStrLn "TEST Syntax"
    testTermSize
    testFreeVariables

