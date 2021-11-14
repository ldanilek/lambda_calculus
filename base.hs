import Control.Exception
import Data.Maybe

type Var = Char

data Term = V Var -- variable
    | L Var Term -- lambda
    | A Term Term deriving (Eq) -- application

-- pretty-print a term, omitting parentheses when possible

showTerm :: Term -> Bool -> Bool -> String
showTerm (V var) paren paren' = [var]
showTerm (L var term) False paren' = "λ" ++ [var] ++ "." ++ (showTerm term False False)
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

parseTermPrefix :: String -> (Maybe Term, String)
parseTermPrefix ('λ':var:'.':t) = let (t', p) = parseTermPrefix t in
    (Just (L var (fromJust t')), p)
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
parseAtom (x:s) = (Just (V x), s)
parseAtom "" = (Nothing, "")

testParse x y = let showed = show (parseTerm x) in
    case showed == y of
    True -> putStrLn (showed ++ " = " ++ y)
    False -> putStrLn ("ERROR: " ++ showed ++ " != " ++ y)

testParse0 = testParse "λx.x" "λx.x"
testParse1 = testParse "λx.xz(λy.xy)" "λx.xzλy.xy"
testParse2 = testParse "λx.xzλy.xy" "λx.xzλy.xy"
testParse3 = testParse "(λx.xz)λy.wλw.wxyz" "(λx.xz)λy.wλw.wxyz"

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

-- some common variables
t = 't'
f = 'f'
s = 's'
z = 'z'

test0 = assert (subst t (V z) (A (V t) (V t)) == A (V z) (V z)) 0
test1 = assert (subst t (V z) (L t (V t)) == L t (V t)) 0

-- basic values
id' = L z (V z)

test2 = assert (simpl (A id' (V t)) == V t) 0

-- booleans
fls = L t (L f (V f))
tru = L t (L f (V t))

b = 'b'
c = 'c'
and' = L b (L c (A (A (V b) (V c)) (V b)))

test3 = assert (simpl (A (A and' tru) fls) == fls) 0
test4 = assert (simpl (A (A and' tru) tru) == tru) 0

