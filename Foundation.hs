module Foundation where

import Control.Exception
import Data.Maybe
import Syntax
import Strings
import Semantics

-- identity function
id' = parseTerm "λx.x"

t = parse "t"
testIdentity0 = testEqual show (simpl (A id' t)) t

-- booleans
fls = parse "λt.λf.f"
tru = parse "λt.λf.t"

b = 'b'
c = 'c'
and' = L b (L c (A (A (V b) (V c)) (V b)))

testBool0 = testEqual show (simpl (A (A and' tru) fls)) fls
testBool1 = testEqual show (simpl (A (A and' tru) tru)) tru

test = do
    testIdentity0
    testBool0
    testBool1
