module Syntax where

import Enrichment

data Var = C Char
    | P Var -- prime
    deriving (Eq)

data Term = V Var -- variable
    | L Var Term -- lambda
    | A Term Term -- application
    | R Rich -- rich type (constant)
    deriving (Eq)
