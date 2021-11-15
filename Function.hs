module Function where

import Syntax
import Strings
import Semantics

-- identity function
id' = parseTerm "λx.x"

t = parse "t"
testIdentity0 = testEq (simpl (A id' t)) t

test = do
    putStrLn "TEST Function"
    testIdentity0