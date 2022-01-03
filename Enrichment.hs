module Enrichment where


-- allows the lambda calculus to operate on constants like "true" and "4"

data Rich = RealBool Bool
    | RealNum Int
    -- string is unique identifier.
    -- Function is call-by-value, so the argument must be evaluated.
    | RealFunction String (Rich -> Rich)
    -- If True and If False cannot be implemented as Functions because they
    -- need to short-circuit.
    | RealIf Bool

instance Eq Rich where
    (==) = eqRich
    (/=) x y = not (eqRich x y)

eqRich :: Rich -> Rich -> Bool
eqRich (RealBool x) (RealBool y) = (x == y)
eqRich (RealNum x) (RealNum y) = (x == y)
eqRich (RealFunction x _) (RealFunction y _) = (x == y)
eqRich (RealIf x) (RealIf y) = (x == y)
eqRich _ _ = False

showRich (RealBool x) = show x
showRich (RealNum x) = show x
showRich (RealFunction x _) = x
showRich (RealIf x) = "if" ++ (if x then "tru" else "fls")

instance Show Rich where
    show = showRich
