module Strings where

import Syntax
import Data.Maybe

-- pretty-print a term, omitting parentheses when possible

showVar :: Var -> String
showVar (C c) = [c]
showVar (P v) = (showVar v) ++ "'"

instance Show Var where
    show v = showVar v

showTerm :: Term -> Bool -> Bool -> String
showTerm (V var) paren paren' = showVar var
showTerm (L var term) False paren' = "λ" ++ showVar var ++ "." ++ (showTerm term False False)
showTerm (A term term') paren False = showTerm term True False ++ showTerm term' paren True
showTerm x paren paren' | paren || paren' = "(" ++ showTerm x False False ++ ")"

instance Show Term where
    show t = showTerm t False False

-- parse a term in the same format as pretty-printing

parseTerm :: String -> Term
parseTerm x = let (t, s) = parseTermPrefix x in
    case s of
        "" -> fromJust t
        _ -> error ("unexpected suffix: " ++ s)

parse = parseTerm

parsePrimes :: Var -> String -> (Var, String)
parsePrimes v ('\'':t) = parsePrimes (P v) t
parsePrimes v t = (v, t)

parseVar :: String -> (Maybe Var, String)
parseVar "" = (Nothing, "")
parseVar (v:t) = let (v',s) = parsePrimes (C v) t in (Just v', s)

parseV :: String -> Var
parseV v = case parseVar v of
    (v', "") -> fromJust v'
    (_, s) -> error ("unexpected suffix: " ++ s)

parseTermPrefix :: String -> (Maybe Term, String)
parseTermPrefix ('λ':t) = let (var, t') = parseVar t in
    case (var, t') of
        (Nothing, _) -> (Nothing, "")
        (Just var,('.':t'')) -> let (t''', p) = parseTermPrefix t'' in
            (Just (L var (fromJust t''')), p)
        otherwise -> (Nothing, "")
parseTermPrefix t = parseApplyPrefix t Nothing

maybeApply :: Maybe Term -> Maybe Term -> Maybe Term
maybeApply Nothing t = t
maybeApply t Nothing = t
maybeApply (Just t) (Just t') = Just (A t t')

parseApplyPrefix :: String -> Maybe Term -> (Maybe Term, String)
parseApplyPrefix (')':t) t' = (t', (')':t))
parseApplyPrefix "" t' = (t', "")
parseApplyPrefix x t' =
    let (atom, suffix) = parseAtom x in
    parseApplyPrefix suffix (maybeApply t' atom)

parseAtom :: String -> (Maybe Term, String)
parseAtom ('(':x) =
    (let (t, s) = parseTermPrefix x in
    case s of
    (')':s') -> (t, s')
    _ -> error "no closing paren")
parseAtom ('λ':s) = parseTermPrefix ('λ':s)
parseAtom ('.':_) = error "atom cannot start with dot"
parseAtom (')':_) = error "atom cannot start with close paren"
parseAtom (' ':s) = (Nothing, s)
parseAtom (x:s) = case parseVar (x:s) of
    (Just v, s') -> (Just (V v), s')
    (Nothing, s') -> (Nothing, s')
parseAtom "" = (Nothing, "")

testEqual p x y = case x == y of
    True -> putStrLn ("PASS: " ++ (p x) ++ " = " ++ (p y))
    False -> putStrLn ("ERROR: " ++ (p x) ++ " != " ++ (p y))

testParse x y = let showed = show (parse x) in
    testEqual id showed y

testEq :: Term -> Term -> IO ()
testEq t t' = testEqual show t t'

testParse0 = testParse "λx.x" "λx.x"
testParse1 = testParse "λx.xz(λy.xy)" "λx.xzλy.xy"
testParse2 = testParse "λx.xzλy.xy" "λx.xzλy.xy"
testParse3 = testParse "(λx.xz)λy.wλw.wxyz" "(λx.xz)λy.wλw.wxyz"

test = do
    putStrLn "TEST Strings"
    testParse0
    testParse1
    testParse2
    testParse3
