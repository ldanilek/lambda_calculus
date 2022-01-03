module Recursion where

import Syntax
import Strings
import Semantics
import Numeral
import Bool
import Data

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

-- i looked at the answer in the back of the book :)
-- you need to wrap the conditional results in dummy variables to prevent them both being evaluated.
factorialG = subst' [('E', equal), ('0', c 0), ('1', c 1), ('T', times), ('P', prd)] "λf.λn.(En0) (λa.1) (λa.(T n (f (P n)))) 0"

-- enriched definition with real bools, as in the book
richFactorialG = subst' [('E', realEq'), ('0', c 0), ('1', c 1), ('T', times), ('P', prd), ('I', R realIf)] "λf.λn.I(En0) 1 (T n (f (P n)))"

factorial = A fix factorialG
richFactorial = A fix richFactorialG

factorial0 = A realNat (A richFactorial (c 0))
testFactorial0 = testEq (strictSimpl factorial0) (rn 1)
factorial4 = A realNat (A richFactorial (c 4))
testFactorial1 = testEq (strictSimpl factorial4) (rn 24)

fact0 = A realNat (A factorial (c 0))
testFactorial2 = testEq (strictSimpl fact0) (rn 1)
fact4 = A realNat (A factorial (c 4))
testFactorial3 = testEq (strictSimpl fact4) (rn 24)

-- 5.2.11
-- sum of numbers in list
-- could just do λl.lP0 where l is the list, P is plus, and 0 is (c 0)
-- but we are asked to use fix so let's.
-- wow it's much more complex this way.

-- this doesn't work because it doesn't take into account the extra argument to head'
-- we could make it work, but let's try to use head'' instead, which should combine with the nil check.
-- gSumList = subst' [('P', plus), ('0', c 0), ('N', isnil), ('H', head'), ('T', tail')] "λf.λl.(Nl)(λa.0)(λa.P(Hl)(f(Tl)))0"

gSumList = subst' [('P', plus), ('0', c 0), ('H', head''), ('T', tail')] "λf.λl.(Hl)(λj.Pj(f(Tl)))0"
sumList = A fix gSumList

sumListTest0 = testEq (strictSimpl (A realNat (A sumList nil'))) (rn 0)
sumListSingleton = A realNat (A sumList (list' [(c 0)]))
sumListTest1 = testEq (strictSimpl sumListSingleton) (rn 0)
sumListTest2 = testEq (strictSimpl (A realNat (A sumList (list' [(c 6)])))) (rn 6)
sumListTest3 = testEq (strictSimpl (A realNat (A sumList (list' [(c 3), (c 2), (c 5)])))) (rn 10)



test = do
    putStrLn "TEST Recursion"
    putStrLn (simplDebugStr (strictSimplDebug (A realNat (A fixIdentity (c 0)))))
    testOmega
    fixTest0
    -- putStrLn (simplDebugPrefix 50 (strictSimplDebug' (A fixConst (c 0))))
    fixTest1
    -- putStrLn (simplDebugStr (strictSimplDebug (A realNat factorial0)))
    testFactorial0
    testFactorial1
    -- putStrLn (simplDebugPrefix 50 (strictSimplDebug' fact0))
    testFactorial2
    testFactorial3
    sumListTest0
    -- putStrLn (simplDebugStr (strictSimplDebug (A sumList (list' [(c 0)]))))
    sumListTest1
    sumListTest2
    sumListTest3

