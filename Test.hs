module Test where

testEqual p x y = case x == y of
    True -> putStrLn ("PASS: " ++ (p x) ++ " = " ++ (p y))
    False -> putStrLn ("ERROR: " ++ (p x) ++ " != " ++ (p y))

testEq :: Eq a => Show a => a -> a -> IO ()
testEq t t' = testEqual show t t'
