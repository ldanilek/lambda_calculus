module Syntax where

data Var = C Char
    | P Var
    deriving (Eq)

data Term = V Var -- variable
    | L Var Term -- lambda
    | A Term Term -- application
    deriving (Eq)
