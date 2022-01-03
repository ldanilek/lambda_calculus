module Numeral where

import Syntax
import Strings
import Semantics
import Pair
import Bool
import Enrichment

applyTimes 0 = "z"
applyTimes n | n > 0 = "s("++(applyTimes (n-1))++")"

c n = parse ("λs.λz."++(applyTimes n))

testC0 = testEq (c 0) (parse "λs.λz.z")
testC3 = testEq (c 3) (parse "λs.λz.s(s(sz))")

-- successor
scc = parse "λn.λs.λz.s(nsz)"

testSucc3 = testEq (simpl (A scc (c 2))) (c 3)

scc' = parse "λn.λs.λz.ns(sz)"

testSucc'3 = testEq (simpl (A scc' (c 2))) (c 3)

-- plus
plus = parse "λm.λn.λs.λz.ms(nsz)"
testPlus0 = testEq (simpl (A (A plus (c 1)) (c 1))) (c 2)
testPlus1 = testEq (simpl (A (A plus (c 3)) (c 4))) (c 7)

-- multiplication
times = subst' [('P',plus),('0',c 0)] "λm.λn.m(P n)0"

oneTimesOne = A (A times (c 1)) (c 1)
testTimes0 = testEq (simpl oneTimesOne) (c 1)

testTimes1 = testEq (simpl (A (A times (c 4)) (c 5))) (c 20)

-- iszro
iszro = subst' [('F', fls), ('T', tru)] "λm.m(λx.F)T"

testIsZero0 = testEq (simpl (A iszro (c 0))) tru
testIsZero1 = testEq (simpl (A iszro (c 2))) fls

-- predecessor
zz = pair' (c 0) (c 0)
ss = subst' [('P', pair), ('S', snd'), ('A', plus), ('1', c 1)] "λp.P(Sp)(A1(Sp))"
prd = subst' [('F', fst'), ('S', ss), ('Z', zz)] "λm.F(mSZ)"

testPrd0 = testEq (simpl (A prd (c 3))) (c 2)
testPrd1 = testEq (simpl (A prd (c 0))) (c 0)

-- subtraction
sub = subst' [('P', prd)] "λn.λm.mPn"

testSub0 = testEq (simpl (A (A sub (c 5)) (c 2))) (c 3)
testSub1 = testEq (simpl (A (A sub (c 2)) (c 5))) (c 0)

-- equal
equal = subst' [('S', sub), ('A', and'), ('Z', iszro)] "λn.λm.A(Z(Snm))(Z(Smn))"
testEqual0 = testEq (simpl (A (A equal (c 5)) (c 2))) fls
testEqual1 = testEq (simpl (A (A equal (c 2)) (c 5))) fls
testEqual2 = testEq (simpl (A (A equal (c 3)) (c 3))) tru

testEqual3 = testEq (strictSimpl (A (A equal (c 0)) (c 0))) tru
testEqual4 = testEq (strictSimpl (A (A (A (A equal (c 0)) (c 0)) (c 1)) (V (C 'x')))) (c 1)

-- rich naturals
rn n = R (RealNum n)

realSuccFunc (RealNum x) = RealNum (x+1)

realSucc = R (RealFunction "succ" realSuccFunc)

realNat = subst' [('S', realSucc), ('0', rn 0)] "λm.m(λx.Sx)0"

realEqFunc' x (RealNum y) = RealBool (x == y)
realEqFunc (RealNum x) = RealFunction ("eq:" ++ show x) (realEqFunc' x)
realEq = RealFunction "eq" realEqFunc

-- realeq in the book takes two church numerals and outputs a real bool
-- but the "equal" function on church numerals is uber complicated,
-- so what happens if we convert the church numerals to naturals first, then compare.
realEq' = subst' [('R', R realEq), ('N', realNat)] "λn.λm.R(Nn)(Nm)"

test = do
    putStrLn "TEST Numeral"
    -- putStrLn (show oneTimesOne)
    -- putStrLn (simplDebugStr (simplDebug oneTimesOne))
    testC0
    testC3
    testSucc3
    testSucc'3
    testPlus0
    testPlus1
    testTimes0
    testTimes1
    testIsZero0
    testIsZero1
    testPrd0
    testPrd1
    testSub0
    testSub1
    testEqual0
    testEqual1
    testEqual2
    testEqual3
    testEqual4

