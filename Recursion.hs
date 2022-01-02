module Recursion where

import Syntax
import Strings
import Semantics
import Numeral

omega = parse "(λx.xx)(λx.xx)"

-- (simpl omega) doesn't terminate.
-- we could update simpl to do something more reasonable than loop forever,
-- but this is sort of the correct behavior. we can't test it though.

-- testOmega = testEq (simpl omega) omega
testOmega = testEq omega omega

fix = parse "λf. (λx. f (λy. x x y)) (λx. f (λy. x x y))"

factorialG = subst' [('E', equal), ('0', c 0), ('1', c 1), ('T', times), ('P', prd)] "λf.λn.(En0) 1 f (P n)"

factorial = A fix factorialG

-- TODO: this is infinite looping
-- maybe have to have a different version of simpl that does call-by-value only.
testFactorial0 = testEq (simpl (A factorial (c 0))) (c 1)
testFactorial1 = testEq (simpl (A factorial (c 4))) (c 24)

test = do
    putStrLn "TEST Recursion"
    putStrLn (show fix)
    putStrLn (show factorial)
    testOmega
    testFactorial0
    testFactorial1

