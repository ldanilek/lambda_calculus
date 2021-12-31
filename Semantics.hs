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

containsAbstract :: Term -> Var -> Bool
containsAbstract (V a) a'
    | a == a' = True
    | otherwise = False
containsAbstract (L a t) a'
    | a == a' = False
    | otherwise = containsAbstract t a'
containsAbstract (A t t') a = containsAbstract t a || containsAbstract t' a

nextNonAbstract :: Term -> Term -> Var -> Var
nextNonAbstract t t' v
    | containsAbstract t v || containsAbstract t' v = nextNonAbstract t t' (P v)
    | otherwise = v

-- substitute [var -> v']v''
-- all occurances of var within v'' are replaced with v',
-- and if v'' binds a variable that collides with var, that binding is renamed.
subst :: Var -> Term -> Term -> Term
subst var v' (V v'')
   | var == v'' = v'
   | otherwise = V v''
subst var v' (L var' v'')
    | var == var' = L var' v''
    | otherwise = let newBound = nextNonAbstract v' (L var' v'') var' in
        L newBound (subst var v' (subst var' (V newBound) v''))
subst var v' (A v'' v''') = A (subst var v' v'') (subst var v' v''')

removeUnnecessaryPrimes :: Term -> Term
removeUnnecessaryPrimes (V v) = (V v)
removeUnnecessaryPrimes (L (P x) y)
    | not (containsAbstract y x) = L x (removeUnnecessaryPrimes (subst (P x) (V x) y))
removeUnnecessaryPrimes (L x y) = L x (removeUnnecessaryPrimes y)
removeUnnecessaryPrimes (A x y) = A (removeUnnecessaryPrimes x) (removeUnnecessaryPrimes y)

-- simplify term as much as possible
simpl :: Term -> Term
simpl x | isValue x = removeUnnecessaryPrimes x
simpl (A (L x y) a) = simpl (subst x a (simpl y))
simpl (A x y) = simpl (A (simpl x) (simpl y))
simpl (L x y) = L x (simpl y)

-- Focus t1 [ss] t2 means t1 -> t2 with sub-steps ss
data DebugStep = Focus Term [DebugStep] Term

simplDebug :: Term -> DebugStep
simplDebug x | isValue x = Focus x [] x
simplDebug (A (L x y) a) = let simplY = simpl y in
    Focus (A (L x y) a) [simplDebug y, simplDebug (subst x a simplY)] (simpl (subst x a simplY))
simplDebug (A x y) = let simplX = simpl x in
                    let simplY = simpl y in
                    Focus (A x y) [simplDebug x, simplDebug y, simplDebug (A simplX simplY)] (simpl (A x y))
simplDebug (L x y) = Focus (L x y) [simplDebug y] (simpl (L x y))

indentStr 0 = ""
indentStr n = "｜" ++ indentStr (n-1)
simplDebugStr' :: Integer -> [DebugStep] -> [String]
simplDebugStr' i [] = []
simplDebugStr' i [Focus t1 ss t2] = (indentStr i ++ show t1 ++ " -> " ++ show t2):(simplDebugStr' (i+1) ss)
simplDebugStr' i (ds:dss) = simplDebugStr' i [ds] ++ simplDebugStr' i dss

simplDebugStr ds = unlines (simplDebugStr' 0 [ds])


testTrueSimpl = testEq (simpl (parse "(λl.λm.λn.lmn)(λt.λf.t)vw")) (parse "v")
testFalseSimpl = testEq (simpl (parse "(λl.λm.λn.lmn)(λt.λf.f)vw")) (parse "w")

testNestedSimpl0 = testEq (simpl (parse "λa.(λa.a)a")) (parse "λa.a")
testNestedSimpl1 = testEq (simpl (parse "λa.a((λa.a)a)")) (parse "λa.aa")

testSubst0 = testEq (subst (parseV "t") (parse "z") (parse "tt")) (parse "zz")
testSubst1 = testEq (subst (parseV "t") (parse "z") (parse "λt.t")) (parse "λt.t")
testSubst2 = testEq (subst (parseV "t") (parse "xy") (parse "λz.ytz")) (parse "λz.y(xy)z")
testSubst3 = testEq (subst (parseV "t''") (parse "xy") (parse "λz.yt''zt't'''")) (parse "λz.y(xy)zt't'''")

-- this example is tricky. Since t is abstract, x must also be abstract, not bound.
-- therefore we need to change the bound variable.
testBound0 = testEq (subst (parseV "t") (parse "x") (parse "λx.xt")) (parse "λx'.x'x")

testBound1 = testEq (subst (parseV "t") (parse "xy") (parse "λx.xtz")) (parse "λx'.x'(xy)z")
-- the bound variable should be changed to the next available (non-abstract) variable
testBound2 = testEq (subst (parseV "t") (parse "a'") (parse "λa'.a't")) (parse "λa''.a''a'")
testBound3 = testEq (subst (parseV "t") (parse "a") (parse "λa.a(λa.aa't)")) (parse "λa''.a''(λa''.a''a'a)")
testBound4 = testEq (subst (parseV "t") (parse "a") (parse "λa'.a'(λa.aa't)")) (parse "λa'.a'(λa''.a''a'a)")
testBound5 = testEq (subst (parseV "t") (parse "λx.xy") (parse "λx.xtz")) (parse "λx.x(λx.xy)z")


subst' [] t = parse t
subst' ((var, v'):r) t = subst (C var) v' (subst' r t)

test = do
    putStrLn "TEST Semantics"
    testTrueSimpl
    testFalseSimpl
    testNestedSimpl0
    testNestedSimpl1
    testSubst0
    testSubst1
    testSubst2
    putStrLn (simplDebugStr (simplDebug (parse "(λt.λz.ytz)(xy)")))
    testSubst3
    testBound0
    testBound1
    testBound2
    testBound3
    testBound4
    testBound5
