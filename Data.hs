module Data where

import Syntax
import Strings
import Semantics
import Bool

pair = parse "λf.λs.λb. b f s"
pair' f s = subst' [('P', pair), ('F', f), ('S', s)] "PFS"
fst' = subst (C 'T') tru (parse "λp. p T")
snd' = subst (C 'F') fls (parse "λp. p F")

fstPair = subst' [('F',fst'),('P',pair)] "F (P v w)"
sndPair = subst' [('S',snd'),('P',pair)] "S (P v w)"

fstPairTest = testEq (simpl fstPair) (parse "v")
sndPairTest = testEq (simpl sndPair) (parse "w")

pairAB = pair' (parse "x") (parse "y")
pairSimplTest = testEq (simpl pairAB) (parse "λb.bxy")

test = do
    putStrLn "TEST Data"
    fstPairTest
    sndPairTest
    pairSimplTest

