module Semantics where

import Control.Exception
import Data.Maybe
import Syntax
import Strings

-- a "value" is a term that is finished computing and cannot be reduced any further.
isValue (A (L x y) a) = False
isValue (A x y) = isValue x && isValue y
isValue x = True

-- substitute [var -> v']v''
subst var v' (V v'')
   | var == v'' = v'
   | otherwise = V v''
subst var v' (L var' v'')
    | var == var' = L var' v''
    | otherwise = L var' (subst var v' v'')
subst var v' (A v'' v''') = A (subst var v' v'') (subst var v' v''')

-- simplify term as much as possible
simpl x | isValue x = x
simpl (A (L x y) a) = simpl (subst x a (simpl y))
simpl (A x y) = simpl (A (simpl x) (simpl y))


testTrueSimpl = testEqual show (simpl (parse "(λl.λm.λn.lmn)(λt.λf.t)vw")) (parse "v")
testFalseSimpl = testEqual show (simpl (parse "(λl.λm.λn.lmn)(λt.λf.f)vw")) (parse "w")

testSubst0 = testEqual show (subst 't' (parse "z") (parse "tt")) (parse "zz")
testSubst1 = testEqual show (subst 't' (parse "z") (parse "λt.t")) (parse "λt.t")
testSubst2 = testEqual show (subst 't' (parse "xy") (parse "λz.ytz")) (parse "λz.y(xy)z")
-- does this make sense? is x abstract or bound
testSubst3 = testEqual show (subst 't' (parse "xy") (parse "λx.xtz")) (parse "λx.x(xy)z")

test = do
    testTrueSimpl
    testFalseSimpl
    testSubst0
    testSubst1
    testSubst2
    testSubst3
