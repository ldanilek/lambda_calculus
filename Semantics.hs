module Semantics where

import Control.Exception
import Data.Maybe
import Syntax
import Strings

-- a "value" is a term that is finished computing and cannot be reduced any further.
-- the book says lambda abstractions are values, but it's nice to be able to simplify
-- within a lambda abstraction, for example to evaluate successor function for numerals.
isValue (A (L x y) a) = False
isValue (A x y) = isValue x && isValue y
isValue (L x y) = isValue y
isValue x = True

-- substitute [var -> v']v''
subst :: Var -> Term -> Term -> Term
subst var v' (V v'')
   | var == v'' = v'
   | otherwise = V v''
subst var v' (L var' v'')
    | var == var' = L var' v''
    | otherwise = L var' (subst var v' v'')
subst var v' (A v'' v''') = A (subst var v' v'') (subst var v' v''')

-- simplify term as much as possible
simpl :: Term -> Term
simpl x | isValue x = x
simpl (A (L x y) a) = simpl (subst x a (simpl y))
simpl (A x y) = simpl (A (simpl x) (simpl y))
simpl (L x y) = L x (simpl y)


simplDebug :: Term -> [(Term, Term)]
simplDebug x | isValue x = []
simplDebug (A (L x y) a) = let simplY = simpl y in
    (simplDebug y) ++ (simplDebug (subst x a simplY)) ++ [((A (L x y) a), simpl (subst x a simplY))]
simplDebug (A x y) = let simplX = simpl x in
                    let simplY = simpl y in
                    simplDebug x ++ simplDebug y ++ simplDebug (A simplX simplY)
simplDebug (L x y) = simplDebug y

simplDebugStr [] = ""
simplDebugStr ((t, t'):r) = show t ++ " -> " ++ show t' ++ "\n" ++ (simplDebugStr r)


testTrueSimpl = testEq (simpl (parse "(λl.λm.λn.lmn)(λt.λf.t)vw")) (parse "v")
testFalseSimpl = testEq (simpl (parse "(λl.λm.λn.lmn)(λt.λf.f)vw")) (parse "w")

testNestedSimpl0 = testEq (simpl (parse "λa.(λa.a)a")) (parse "λa.a")
testNestedSimpl1 = testEq (simpl (parse "λa.a((λa.a)a)")) (parse "λa.aa")

testSubst0 = testEq (subst 't' (parse "z") (parse "tt")) (parse "zz")
testSubst1 = testEq (subst 't' (parse "z") (parse "λt.t")) (parse "λt.t")
testSubst2 = testEq (subst 't' (parse "xy") (parse "λz.ytz")) (parse "λz.y(xy)z")
-- does this make sense? is x abstract or bound
testSubst3 = testEq (subst 't' (parse "xy") (parse "λx.xtz")) (parse "λx.x(xy)z")

subst' [] t = parse t
subst' ((var, v'):r) t = subst var v' (subst' r t)

test = do
    putStrLn "TEST Semantics"
    testTrueSimpl
    testFalseSimpl
    testNestedSimpl0
    testNestedSimpl1
    testSubst0
    testSubst1
    testSubst2
    testSubst3
