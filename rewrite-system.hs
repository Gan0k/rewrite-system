-- PRACTICA 1 HASKELL

-- Arnau Antoniucci, Guido

type Signature = [(String,Int)]
type Position = [Int]
type Substitution a = [(a,a)]

class Rewrite a where 
    getVars :: a -> [a]
    valid :: Signature -> a -> Bool
    match :: a -> a -> [(Position, Substitution a)]
    apply :: a -> Substitution a -> a
    replace :: a -> [(Position, a)] -> a
    evaluate :: a -> a

data Rule a = Rule a a
type RewriteSystem a = [Rule a]

instance Show a => Show (Rule a) where
    show (Rule l r) = show l ++ " --> " ++ show r

includes::Eq a => [a] -> [a] -> Bool
-- keep in mind: all _ [] -> True, since the empty list is included in all the lists
includes as bs = all (`elem` bs) as

validRule :: (Rewrite a, Eq a) => Signature -> Rule a -> Bool
validRule s (Rule a b) = valid s a && valid s b && includes (getVars b) (getVars a)

validRewriteSystem :: (Rewrite a, Eq a) => Signature -> RewriteSystem a -> Bool
validRewriteSystem = all . validRule

oneStepRewrite::(Rewrite a, Eq a) => RewriteSystem a -> a -> ([(Position, a)]->[(Position, a)]) -> a
oneStepRewrite rset x e = replace x (e (concatMap ((\(l,sn) -> map (\(p,sub) -> (p, apply sn sub)) l) . (\(Rule r1 r2) -> (match r1 x,r2))) rset))
-- if rset == [] the map won't execute, e will return [], and replace will output x without modifications
-- if no match found, the same behavior will occur

rewrite :: (Rewrite a, Eq a) => RewriteSystem a -> a -> ([(Position, a)]->[(Position, a)]) -> a
rewrite r x e = if x == os then x 
                else rewrite r os e 
                where os = evaluate (oneStepRewrite r x e)

nrewrite :: (Rewrite a, Eq a) => RewriteSystem a -> a -> ([(Position, a)]->[(Position, a)]) -> Int -> a
nrewrite r x e n 
    | n == 0 = x  -- no need to check if they are equal, it will stop anyway
    | otherwise = evaluate (nrewrite r (oneStepRewrite r x e) e (n-1))


------------------- RString

data RString = RString String

instance Eq RString where
    (RString x) == (RString y) = x == y


instance Rewrite RString where
    getVars _ = []

    valid sig o = all (`elem` fsts) sym 
                  where fsts = map fst sig
                        sym = splitSymbols o 
    -- sig will only contain (char, 0)
    -- it is assumed that sym will never be empty if the ruleset is also not empty

    match m o = matchPosRString ospl mspl 0 where mspl = splitSymbols m
                                                  ospl = splitSymbols o

    apply (RString o) subs = RString (o ++ show (snd (head subs)))
    -- no need to check if subs == [], oneStepRewrite does not call apply in the case
    -- there are no matches found

    replace o [] = o -- head of [] -> Error, also necessary if no match found
    replace (RString o) l = RString (take (head (fst (head l))) o ++ show (snd (head l)))

    evaluate = id

isCharNumber:: Char -> Bool
isCharNumber c = c >= '0' && c <= '9'

splitSymbols :: RString -> [String]
splitSymbols (RString "") = []
splitSymbols (RString s) = (head s : nums) : splitSymbols (RString ss)
        where (nums, ss) = span isCharNumber (tail s)

matchPosRString :: [String] -> [String] -> Int -> [(Position, Substitution RString)]
matchPosRString [] _ _ = []
matchPosRString o m n = if take (length m) o == m then ([n], [(RString "x", RString (concat (drop (length m) o)))]) : matchPosRString (tail o) m (n + length (head o))
                        else matchPosRString (tail o) m (n + length (head o))

readRString :: String -> RString
readRString = RString

readRStringSystem :: [(String,String)] -> RewriteSystem RString
readRStringSystem = map (\(s1,s2) -> Rule (RString s1) (RString s2))

instance Show RString where
    show (RString s) = s

leftmost :: [(Position, a)] -> [(Position, a)]
leftmost [] = []
leftmost (x:xs) = [foldl (\(p1,s1) (p2,s2) -> if head p1 < head p2 then (p1,s1) else (p2,s2)) x xs]
-- the resulting list of leftmost will only have one element

rightmost :: [(Position, a)] -> [(Position, a)]
rightmost [] = []
rightmost (x:xs) = [foldl (\(p1,s1) (p2,s2) -> if head p1 > head p2 then (p1,s1) else (p2,s2)) x xs]


-------------------- RTerm

data RTerm = Numb Integer | Var String | Sym String [RTerm] deriving (Eq)

-- sum and prod inlcuded in Sym
-- if [RTerm] is empty, then its a leaf
-- Vars and Ints nodes are always leafs

instance Rewrite RTerm where
    getVars (Numb x) = []
    getVars (Var s) = [Var s]
    getVars (Sym s l) = concatMap getVars l

    valid sig (Numb x) = True
    valid sig (Var s) = True
    valid sig (Sym s l) 
        | s == "+" || s == "*" = length l == 2 && all (valid sig) l
        | otherwise = any (\(a,p) -> a == s && length l == p) sig && all (valid sig) l
        --if Sym has no arguments, all _ [] = True (the unexisting RTerms wont be checked against the signature)

    match r o = matchPosTrees o r []

    apply v@(Var s) sub = (snd . head) (dropWhile ((/= v) . fst) sub)
    apply (Sym k sons) sub = Sym k (map (`apply` sub) sons)
    apply t _ = t -- if Numb then id
    -- apply grabs the first substitution of the variable needed since 
    -- in the substitution array there can be multiple instances of the SAME
    -- substitution (only one will be used, the other ones are ignored)

    -- it is assured that in the substitution sub there is a substitution 
    -- for ALL the variables of the RTerm (maybe some of the substitutions will go unused)

    replace = foldl (\o x -> uncurry (replacePosTree o) x)
    -- if [(Pos,a)] is empty, then o will be returned without modifications

    evaluate = until (\a -> a == evalTrees a) evalTrees

isMatchTree:: RTerm -> RTerm -> (Bool, Substitution RTerm)
isMatchTree (Numb x) (Numb y) = (x == y,[])
isMatchTree t v@(Var s) = (True, [(v,t)])
isMatchTree (Sym s1 br1) (Sym s2 br2) = if length br1 == length br2 && s1 == s2 && all fst z then (True, concatMap snd z)
                                        else (False, [])
                                        where z = zipWith isMatchTree br1 br2
isMatchTree _ _ = (False, [])

-- previous function: tells if the two trees match, and the substitution necessary to match

isValidTSubs :: Substitution RTerm -> Bool
isValidTSubs [] = True
isValidTSubs (s:ss) = if fst s `elem` map fst ss then snd (head d) == snd s && isValidTSubs ss
                    else isValidTSubs ss
                    where d = dropWhile ((/= fst s) . fst) ss

-- previous function: looks for various substitutions of the same variable and checks
-- if they are equal

matchPosTrees :: RTerm -> RTerm -> Position -> [(Position, Substitution RTerm)]
matchPosTrees o@(Sym s sons) rl p = if b && isValidTSubs l then (p,l) : cont
                                    else cont
                                    where (b,l) = isMatchTree o rl 
                                          cont = concatMap (\(t,pos) -> matchPosTrees t rl (p++[pos])) (zip sons [0..])
matchPosTrees o rl p = [(p, l) | b && isValidTSubs l] where (b,l) = isMatchTree o rl

-- previous function: looks in ALL of the positions of the tree for a match of the recieved rule
-- second case for leafs of type Var or Numb

-- each pair (p,l) indicates the substitutions necessary in order to match in that certain position
-- if Sym has no sons, then concatMap will be called over an empty list and cont will be an empty list,
-- ending the recursion

replacePosTree :: RTerm -> Position -> RTerm -> RTerm
replacePosTree _ [] r = r
replacePosTree (Sym k sons) (p:ps) r = Sym k (left ++ replacePosTree (sons !! p) ps r : tail right)
                                       where (left,right) = splitAt p sons

-- if Position still has elements, r HAS to be a symbol with enough sons to
-- find the next position, it cannot have less sons or be a leaf

sumRTrees :: RTerm -> RTerm -> RTerm -> RTerm
sumRTrees p (Numb x) (Numb y) = Numb (x+y)
sumRTrees p l r = Sym "+" (evalTrees l : [evalTrees r])

-- the product and the sum has allways two sons (it is checked in valid function)

prodRTrees :: RTerm -> RTerm -> RTerm -> RTerm
prodRTrees p (Numb x) (Numb y) = Numb (x*y)
prodRTrees p l r = Sym "*" (evalTrees l : [evalTrees r])

evalTrees :: RTerm -> RTerm
evalTrees r@(Sym s l) 
    | s == "+" = sumRTrees r (head l) (last l)
    | s == "*" = prodRTrees r (head l) (last l)
    | otherwise = Sym s (map evalTrees l)
    -- no need to check for length l == 2, checked in valid already
evalTrees v = v


instance Show RTerm where
    show (Numb x) = show x
    show (Var s) = s
    show (Sym s []) = s
    show (Sym s l) = s ++ "( " ++ concatMap ((++" , ") . show) (init l) ++ show (last l) ++ " )"


countArgs :: [(String,Int)] -> Int -> ([(String,Int)],[(String,Int)])
countArgs k n
    | n == 0 = ([],k) -- if k empty this will be executed, so we can do (head k) freely later
    | snd (head k) == -1 || snd (head k) == -2 = (head k : l, rem)
    | otherwise = (head k : l2, rem2)
    where (l,rem) = countArgs (tail k) (n-1)
          (l2,rem2) = countArgs (tail k) ((n-1) + snd (head k))

readRTreeTuple :: [(String,Int)] -> (RTerm,[(String,Int)])
readRTreeTuple (x:xs)
    | snd x == (-1) = (Var (fst x) , xs)
    | snd x == (-2) = (Numb (read (fst x)), xs)
    | otherwise = (Sym (fst x) (take (snd x) (map fst (iterate (readRTreeTuple . snd) (readRTreeTuple l)))), r) 
      where (l,r) = countArgs xs (snd x)

-- in case a Sym has 0 arguments, take 0 _ will return a empty list and the iterate
-- and readRTreeTuple will not be executed over the emptylist

readRTree :: [(String,Int)] -> RTerm
readRTree = fst . readRTreeTuple

readRTermSystem :: [([(String,Int)],[(String,Int)])] -> RewriteSystem RTerm
readRTermSystem = map (\(p1,p2) -> Rule (readRTree p1) (readRTree p2))

posOverlap:: Position -> Position -> Bool
posOverlap p1 p2 = and (zipWith (==) p1 p2)

-- the length of the posititons doesn't matter since zipWith 
-- will zip till the shortest list runs out of elements

sortLengthPos :: [(Position, a)] -> [(Position, a)]
sortLengthPos [] = []
sortLengthPos (p:xs) = (sortLengthPos [y | y<-xs, length (fst y) < lp ]) ++ [p] ++ (sortLengthPos [y | y<-xs, length (fst y) >= lp ])
                    where lp = length (fst p)

-- previous function: sorts the tuples in decreasing order of length
-- of the list of ints that form the positions

parallelinnermost :: [(Position, a)] -> [(Position, a)]
parallelinnermost l = foldr (\x z -> if any (posOverlap (fst x) . fst) z then z else x:z) [] (sortLengthPos l)

-- since the deepest replecements will be at the end of the list 
-- (the list is previously sorted), we can foldr and just take out the ones that overlap

leftmostinnermost :: [(Position, a)] -> [(Position, a)]
leftmostinnermost [] = []    -- in the case the list is empty we have cannot do head
leftmostinnermost l = [foldr (\x z -> if fst x < fst z then x else z) (head fl) (tail fl)]
                    where fl = parallelinnermost l

-- in the previous function we exploit the fact that haskell
-- compares lists lexicographically and the leftmost position
-- will be the one with the lowest lexicographical value

-- keep in mind, the replacements that are to the left have preference over
-- the ones that are deeper into the tree

paralleloutermost :: [(Position, a)] -> [(Position, a)]
paralleloutermost l = foldl (\z x -> if any (posOverlap (fst x) . fst) z then z else z ++ [x]) [] (sortLengthPos l)

-- note that we use foldl to start analyzing the list by the beggining
-- where the outer most replecements will be, then we just filter out the
-- ones that overlap

leftmostoutermost :: [(Position, a)] -> [(Position, a)]
leftmostoutermost [] = []
leftmostoutermost l = [foldr (\x z -> if fst x < fst z then x else z) (head fl) (tail fl)]
                    where fl = paralleloutermost l
