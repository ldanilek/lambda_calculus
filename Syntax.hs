module Syntax where

type Var = Char

data Term = V Var -- variable
    | L Var Term -- lambda
    | A Term Term deriving (Eq) -- application
