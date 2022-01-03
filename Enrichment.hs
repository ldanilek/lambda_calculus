module Enrichment where


-- allows the lambda calculus to operate on constants like "true" and "4"

data Rich = RealBool Bool
    | RealNum Int
    | RealFunction String (Rich -> Rich) -- string is unique identifier

instance Eq Rich where
    (==) = eqRich
    (/=) x y = not (eqRich x y)

eqRich :: Rich -> Rich -> Bool
eqRich (RealBool x) (RealBool y) = (x == y)
eqRich (RealNum x) (RealNum y) = (x == y)
eqRich (RealFunction x _) (RealFunction y _) = (x == y)
eqRich _ _ = False

showRich (RealBool x) = show x
showRich (RealNum x) = show x
showRich (RealFunction x _) = x

instance Show Rich where
    show = showRich
