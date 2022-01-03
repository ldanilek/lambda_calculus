module Function where

import Syntax
import Strings
import Semantics
import Enrichment

-- identity function
id' = parseTerm "λx.x"

t = parse "t"
testIdentity0 = testEq (simpl (A id' t)) t

-- enriched function
realId = RealFunction "id" (\x -> x)

test = do
    putStrLn "TEST Function"
    testIdentity0