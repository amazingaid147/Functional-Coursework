
------------------------- Auxiliary functions

merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys)
    | x == y    = x : merge xs ys
    | x <= y    = x : merge xs (y:ys)
    | otherwise = y : merge (x:xs) ys

minus :: Ord a => [a] -> [a] -> [a]
minus xs [] = xs
minus [] _ = []
minus (x:xs) (y:ys)
    | x <  y    = x : minus    xs (y:ys)
    | x == y    =     minus    xs    ys
    | otherwise =     minus (x:xs)   ys

variables :: [Var]
variables = [ [x] | x <- ['a'..'z'] ] ++ [ x : show i | i <- [1..] , x <- ['a'..'z'] ]

removeAll :: [Var] -> [Var] -> [Var]
removeAll xs ys = [ x | x <- xs , not (elem x ys) ]

fresh :: [Var] -> Var
fresh = head . removeAll variables


-- - - - - - - - - - - -- Terms

type Var = String

data Term =
    Variable Var
  | Lambda   Var  Term
  | Apply    Term Term
  | Plus     
  | Num      Int
  | If       Term Term Term 

instance Show Term where
  show = pretty

pretty :: Term -> String
pretty = f 1
    where
      -- Index k means:
      --   1 : top level
      --   2 : function position
      --   3 : argument position
      f _ (Variable x)   = x
      f k (Lambda x m)   = if elem k [2,3] then "(" ++ s ++ ")" else s where s = "\\" ++ x ++ ". " ++ f 1 m 
      f k (Apply  m n)   = if elem k   [3] then "(" ++ s ++ ")" else s where s = f 2 m ++ " " ++ f 3 n
      f _ Plus           = "+"
      f _ (Num i)        = show i
      f k (If b m n)     = if elem k [2,3] then "(" ++ s ++ ")" else s where s = "if " ++ f 1 b ++ " then " ++ f 1 m ++ " else " ++ f 1 n



-- - - - - - - - - - - -- Numerals


numeral :: Int -> Term
numeral i = Lambda "f" (Lambda "x" (numeral' i))
  where
    numeral' i
      | i <= 0    = Variable "x"
      | otherwise = Apply (Variable "f") (numeral' (i-1))


-- - - - - - - - - - - -- Renaming, substitution, beta-reduction


used :: Term -> [Var]
used (Variable x) = [x]
used (Lambda x m) = [x] `merge` used m
used (Apply  m n) = used n `merge` used m 
used Plus = []
used (Num _) = []
used (If b m n) = used b `merge` used m `merge` used n


rename :: Var -> Var -> Term -> Term
rename y z (Variable x)
    | y == x    = Variable z
    | otherwise = Variable x
rename y z (Lambda x m)
    | y == x    = Lambda x m
    | otherwise = Lambda x (rename y z m)
rename y z (Apply m n) = Apply (rename y z m) (rename y z n)
rename _ _ Plus = Plus
rename _ _ (Num i) = Num i
rename y z (If b m n) = If (rename y z b) (rename y z m) (rename y z n)


substitute :: Var -> Term -> Term -> Term
substitute y p (Variable x)
    | y == x    = p
    | otherwise = Variable x
substitute y p (Lambda x m)
    | y == x    = Lambda x m
    | otherwise = Lambda z (substitute y p (rename x z m))
    where z = fresh (used p `merge` used m `merge` [x,y])
substitute y p (Apply m n) = Apply (substitute y p m) (substitute y p n)
substitute _ _ (Num i) = Num i
substitute _ _ Plus = Plus
substitute y p (If b m n) = If (substitute y p b) (substitute y p m) (substitute y p n)


beta :: Term -> [Term]
beta (Apply (Plus) (Apply (Num i) (Num j) )) = [Num (i + j)]
beta (Apply (Apply (Plus)(Num i) )(Num j)) = [Num (i + j)]
beta (Apply (Lambda x m) n) =
  [substitute x n m] ++ 
  [Apply (Lambda x m') n  | m' <- beta m] ++
  [Apply (Lambda x m ) n' | n' <- beta n]
beta (Variable _) = []
beta (Lambda x m) = [Lambda x m' | m' <- beta m]
beta (Apply  m n) =
  [Apply m' n  | m' <- beta m] ++
  [Apply m  n' | n' <- beta n]
beta (Num _) = []
beta Plus = []
beta (If (Num i) m n) 
  | i == 0    = [m]
  | otherwise = [n]
beta (If b m n) = [If b' m n | b' <- beta b]  ++ [If b m' n | m' <- beta m]  ++ [If b m n' | n' <- beta n] 

-- - - - - - - - - - - -- Normalize

normalize :: Term -> IO ()
normalize m = do
  print m
  let ms = beta m
  if null ms then
    return ()
  else
    normalize (head ms)


------------------------- Assignment 1


example :: Term
example  = Apply (Lambda "x" (Apply (Apply Plus (Num 1)) (Apply (Lambda "f" (Apply (Variable "f") (Num 2))) (Apply Plus (Variable "x"))))) (Num 3)

plus :: Term -> Term -> Term
plus m n = Apply (Apply Plus m) n


------------------------- Assignment 2


example2 :: Term
example2 = Apply (Lambda "f" (If 
    (Apply (Variable "f") (Num 0))
    (Apply (Lambda "x" (Variable "x")) (Num 0))
    (Apply (Variable "f") (Apply (Variable "f") (Num 2)))
  )) (Apply Plus (Num 1))


------------------------- Assignment 3

example3 :: Term
example3 = Apply (Lambda "x" (Variable "x")) (Variable "y")


-- - - - - - - - - - - -- Control

data Control = 
    Ap    String
  | ConTerm Term
  | Branch Term Term

instance Show Control where
 show = pretty'

pretty' :: Control -> String
pretty' = f 1 
    where
      f _ (ConTerm m)   = pretty m
      f _ (Ap x) = x
      f _ (Branch m n) = "(" ++ pretty m ++ " | " ++ pretty n ++ ")"
      

ap :: Control
ap = Ap "@"

term :: Term -> Control
term m = ConTerm m


-- - - - - - - - - - - -- State

type State = ([Term] , [Control])


example4 :: State
example4 = ( [Variable "a",Variable "b"] , [ term (Lambda "x" (Lambda "y" (Variable "x"))) , ap , term (Lambda "z" (Variable "z")) , ap , ap ] )


-- - - - - - - - - - - -- Transitions

step :: State -> [State]
step (ys, ConTerm(Apply m n) : xs) = [(ys, ConTerm(n) : ConTerm(m) : ap : xs)]
step (ys, ConTerm (If b m n) : xs) = [(ys, ConTerm b : branch m n : xs)]
step (Num 0 : ys, Branch m n : xs) = [(ys, ConTerm m : xs)]
step (Num i : ys, Branch m n : xs) = [(ys, ConTerm n : xs)]
step (ys, ConTerm (m): xs) = [(m:ys, xs)] 
step (Lambda (n) (m) : z : zs ,  Ap "@" : xs) = [(zs ,ConTerm (substitute n z m): xs)]
step (Plus : Num i : Num j : ys, Ap "@" : Ap "@" : xs) = [(Num (i + j) : ys, xs)]
step (Plus : i : ys, Ap "@" : xs) = [(Apply (Plus) (i) : ys, xs)]

step _ = []



-- - - - - - - - - - - -- Readback

readback :: State -> Term
readback ([m] , []) = m
readback (ys , ConTerm (m) : xs) = readback (m:ys,xs)
readback (m : n : ys, Ap "@":xs) = readback (Apply m n : ys , xs)
readback (ys, Branch m n : xs) = readback ([If (readback (ys, [])) m n], xs)
readback _ = Variable "Error"


-- - - - - - - - - - - -- Runs
   
run :: Term -> Term
run m = readback (finishedState (startingState m))
  where
    startingState :: Term -> State
    startingState m = ([], [term m])

    finishedState :: State -> State
    finishedState s = case step s of
      [] -> s  
      (nextState : _) -> finishedState nextState  


printRun :: Term -> IO ()
printRun m = putStrLn (showRun (makeRun ([],[term m])))
  where
    makeRun :: State -> [State]
    makeRun s = s : [ s2 | s1 <- step s , s2 <- makeRun s1 ]

    showRun :: [State] -> String
    showRun xs = unlines [ "( " ++ a ++ " , " ++ b ++ " )" | (a,b) <- zip as' bs' ]
      where
        align strs = [ replicate (m - length s) ' ' ++ s | s <- strs ] where m = maximum (map length strs)
        showStack []     = ""
        showStack [x]    = show x
        showStack (x:xs) = show x ++ " : " ++ showStack xs
        (as,bs) = unzip xs
        as'     = align (map showStack as)
        bs'     = align (map showStack bs)




------------------------- Assignment 4

branch :: Term -> Term -> Control
branch m n = Branch m n

