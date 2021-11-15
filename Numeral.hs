module Numeral where

import Syntax
import Strings
import Semantics

applyTimes 0 = "z"
applyTimes n | n > 0 = "s("++(applyTimes (n-1))++")"

c n = parse ("λs.λz."++(applyTimes n))

testC0 = testEq (c 0) (parse "λs.λz.z")
testC3 = testEq (c 3) (parse "λs.λz.s(s(sz))")

scc = parse "λn.λs.λz.s(nsz)"

testSucc3 = testEq (simpl (A scc (c 2))) (c 3)

test = do
    putStrLn "TEST Numeral"
    testC0
    testC3
    testSucc3

