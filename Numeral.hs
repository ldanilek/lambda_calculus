module Numeral where

import Syntax
import Strings
import Semantics

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

test = do
    putStrLn "TEST Numeral"
    putStrLn (show oneTimesOne)
    putStrLn (simplDebugStr (simplDebug oneTimesOne))
    testC0
    testC3
    testSucc3
    testSucc'3
    testPlus0
    testPlus1
    testTimes0
    testTimes1

