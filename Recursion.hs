module Recursion where

import Syntax
import Strings
import Semantics
import Numeral
import Bool

omega = parse "(λx.xx)(λx.xx)"

-- (simpl omega) doesn't terminate.
-- we could update simpl to do something more reasonable than loop forever,
-- but this is sort of the correct behavior. we can't test it though.

-- testOmega = testEq (strictSimpl omega) omega
testOmega = testEq omega omega

fix = parse "λf. (λx. f (λy. x x y)) (λx. f (λy. x x y))"

gIdentity = parse "λg.λx.x"
fixIdentity = A fix gIdentity
fixTest0 = testEq (strictSimpl (A realNat (A fixIdentity (c 0)))) (rn 0)

-- todo: fibonacci

gConst = subst' [('S', scc'), ('I', R realIf), ('E', realEq'), ('2', c 2), ('1', c 1)] "λg.λn.I(En2)1(g(S n))"

fixConst = A fix gConst
fixTest1 = testEq (strictSimpl (A realNat (A fixConst (c 0)))) (rn 1)

-- TODO: this is clearly wrong. shouldn't it be using the times function?
factorialG = subst' [('E', equal), ('0', c 0), ('1', c 1), ('T', times), ('P', prd)] "λf.λn.(En0) 1 f (P n)"

-- enriched definition with real bools, as in the book
richFactorialG = subst' [('E', realEq'), ('0', c 0), ('1', c 1), ('T', times), ('P', prd), ('I', R realIf)] "λf.λn.I(En0) 1 f (P n)"

factorial = A fix richFactorialG

factorial0 = A realNat (A factorial (c 0))
testFactorial0 = testEq (strictSimpl factorial0) (c 1)
testFactorial1 = testEq (strictSimpl (A factorial (c 4))) (c 24)

test = do
    putStrLn "TEST Recursion"
    putStrLn (simplDebugStr (strictSimplDebug (A realNat (A fixIdentity (c 0)))))
    testOmega
    fixTest0
    putStrLn (simplDebugPrefix 5 (strictSimplDebug' (A realNat (A fixConst (c 0)))))
    fixTest1
    putStrLn (simplDebugStr (strictSimplDebug (A realNat factorial0)))
    testFactorial0
    testFactorial1

