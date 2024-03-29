module Data where

import Syntax
import Strings
import Semantics
import Bool
import Numeral
import Pair
import Test

list' :: [Term] -> Term
list' [] = parse "λc.λn.n"
list' (t:ts) = case list' ts of
    (L c (L n v)) -> L c (L n (A (A (V (C 'c')) t) v))
    otherwise -> error "unexpected"

nil' = list' []

listTest0 = testEq nil' (parse "λc.λn.n")
smolList = list' [V (C 'x'), V (C 'y'), V (C 'z')]
listTest1 = testEq smolList (parse "λc.λn.cx(cy(czn))")

cons = parse "λh.λl.λc.λn.ch(lcn)"

consTest = testEq (simpl (A (A cons (V (C 'a'))) smolList)) (parse "λc.λn.ca(cx(cy(czn)))")

isnil = parse "λl.l(λx.λr.λt.λf.f)(λt.λf.t)"

isNilTest0 = testEq (simpl (A isnil nil')) tru
isNilTest1 = testEq (simpl (A isnil smolList)) fls

-- head' takes a list and a zero value
head' = parse "λl.λz.l(λx.λr.x)z"
headTest0 = testEq (simpl (A (A head' smolList) fls)) (V (C 'x'))
headTest1 = testEq (simpl (A (A head' nil') tru)) tru

-- append t l = l ++ [t]
append' = parse "λt.λl.λc.λn.lc(ctn)"

appendTest0 = testEq (simpl (A (A append' (V (C 'a'))) smolList)) (parse "λc.λn.cx(cy(cz(can)))")

reverse' = subst' [('A', append')] "λl.lAλc.λn.n"

reverseTest0 = testEq (simpl (A reverse' smolList)) (parse "λc.λn.cz(cy(cxn))")

-- the book hints the solution has something to do with pairs, but i was having trouble with the zero value.
-- so instead, we reverse the list and take the head.
-- oh... i implemented last here by mistake
last' = subst' [('H', head'), ('R', reverse')] "λl.λz.H(Rl)z"

lastTest0 = testEq (simpl (A (A last' smolList) fls)) (parse "z")
lastTest1 = testEq (simpl (A (A last' nil') tru)) tru



-- Optionals
-- could be represented as a list of len <= 1, but designing them from scratch is an exercise.
-- an optional takes two arguments c z. if it's None, it returns z. if it's Some j, it returns (c j)
some' = parse "λj.λc.λz.cj"
none' = parse "λc.λz.z"

somethin = A some' (c 3)

optMap = parse "λm.λo.λc.λz.o(λj.c(mj))z"

someThreeSuccessor = A (A optMap scc) somethin
optionalTest0 = testEq (simpl someThreeSuccessor) (simpl (A some' (c 4)))
optionalTest1 = testEq (simpl (A (A optMap scc) none')) none'

head'' = subst' [('S', some'), ('N', none')] "λl.l(λx.λr.Sx)N"
headTest2 = testEq (simpl (A head'' smolList)) (simpl (A some' (V (C 'x'))))
headTest3 = testEq (simpl (A head'' nil')) none'

last'' = subst' [('S', some'), ('N', none')] "λl.l(λx.λr.r(λj.r)(Sx))N"
lastTest2 = testEq (simpl (A last'' smolList)) (simpl (A some' (parse "z")))
lastTest3 = testEq (simpl (A last'' nil')) none'

tail' = subst' [
    ('P', pair), ('F', fst'), ('S', snd'), ('C', cons), ('N', nil')] "λl.S(l(λx.λr.P(Cx(Fr))(Fr)) (PNN))"

tailTest0 = testEq (simpl (A tail' smolList)) (list' [V (C 'y'), V (C 'z')])
tailTest1 = testEq (simpl (A tail' nil')) nil'

test = do
    putStrLn "TEST Data"
    listTest0
    listTest1
    consTest
    isNilTest0
    isNilTest1
    headTest0
    headTest1
    appendTest0
    reverseTest0
    lastTest0
    lastTest1
    optionalTest0
    -- putStrLn (simplDebugStr (simplDebug someThreeSuccessor))
    optionalTest1
    headTest2
    headTest3
    lastTest2
    lastTest3
    tailTest0
    tailTest1

