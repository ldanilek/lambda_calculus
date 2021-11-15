module Bool where

import Control.Exception
import Data.Maybe
import Syntax
import Strings
import Semantics

fls = parse "λt.λf.f"
tru = parse "λt.λf.t"

ifelse = parse "λl.λm.λn.lmn"

ifelseTest = subst 'T' ifelse (parse "TBvw")
testIfElseFalse = testEq (simpl (subst 'B' fls ifelseTest)) (parse "w")
testIfElseTrue = testEq (simpl (subst 'B' tru ifelseTest)) (parse "v")

-- boolean expressions
boolOp o a b = subst' [('B',b),('A',a),('O',o)] (parse "OAB")

and' = subst 'F' fls (parse "λb.λc.bcF")

testBool0 = testEq (simpl (boolOp and' tru fls)) fls
testBool1 = testEq (simpl (boolOp and' tru tru)) tru

or' = parse "λb.λc.bbc"

testOr0 = testEq (simpl (boolOp or' tru tru)) tru
testOr1 = testEq (simpl (boolOp or' tru fls)) tru
testOr2 = testEq (simpl (boolOp or' fls tru)) tru
testOr3 = testEq (simpl (boolOp or' fls fls)) fls

not' = subst' [('F',fls), ('T',tru)] (parse "λb.bFT")

testNot0 = testEq (simpl (A not' tru)) fls
testNot1 = testEq (simpl (A not' fls)) tru

xor' = subst 'N' not' (parse "λb.λc.b(Nc)c")

testXor0 = testEq (simpl (boolOp xor' tru tru)) fls
testXor1 = testEq (simpl (boolOp xor' tru fls)) tru
testXor2 = testEq (simpl (boolOp xor' fls tru)) tru
testXor3 = testEq (simpl (boolOp xor' fls fls)) fls

test = do
    putStrLn "TEST Bool"
    testIfElseFalse
    testIfElseTrue
    testBool0
    testBool1
    testOr0
    testOr1
    testOr2
    testOr3
    testNot0
    testNot1
    testXor0
    testXor1
    testXor2
    testXor3

