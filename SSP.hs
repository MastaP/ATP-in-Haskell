--Structural Synthesis of Programs
--(c) Pavel Grigorenko

module Ssp where

import List (delete, intersect, nub)
--import Maybe (isJust, fromJust)
--import qualified Data.Set as Set

data Var = Var String deriving Eq

type Inputs = [Var]
type Output = Var
type Outputs = [Var]

data Subtask = Subtask Inputs Outputs

data Axiom = UCStm Inputs Output
             | CStm [Subtask] Inputs Output

instance Show Var where
 show (Var x) = x

instance Show Subtask where
 show (Subtask is os) = "[" ++ showLst is ++ " -> " ++ showLst os ++ "]"

instance Show Axiom where
 show (UCStm is o)   = showLst is ++ " -> " ++ show o ++ "{f}"
 show (CStm ss is o) = showLst ss ++ (if not $ null is then ", " ++ showLst is ++ " " else " ") ++ "-> " ++ show o ++ "{f}"

showLst :: Show a => [a] -> String
showLst = foldl (\acc l -> if acc == "" then show l else acc ++ ", " ++ show l) ""

tAxiom1 = print $ UCStm [Var "a", Var "x"] (Var "y")
tAxiom2 = print $ UCStm [] (Var "y")
tAxiom3 = print $ CStm [Subtask [Var "u", Var "v"] [Var "x", Var "y"]] 
                       [Var "a", Var "b"] 
                       (Var "c")
tAxiom4 = print $ CStm [Subtask [Var "u"] [Var "v"], Subtask [Var "x"] [Var "y"]] 
                       [Var "a", Var "b"] 
                       (Var "c")
tAxiom5 = print $ CStm [Subtask [Var "u"] [Var "v"], Subtask [Var "x"] [Var "y"]] 
                       [] 
                       (Var "c")

-- transform IL into LL

--collect all propostional atoms in a list without dublicates
atoms :: [Prop] -> [Var]
atoms = nub . concat . map help where
 help (Atom a)   = [Var a]
 help (Conj l r) = help l ++ help r
 help (Impl l r) = help l ++ help r
 help _          = []

tAtoms = atoms [a*b, c*b, x, y, T, F]

transl p = (goal, as) where (goal, as, _) = tr p 0

tr :: Prop -> Int -> (Var, [Axiom], Int)
tr (Impl l r) c = (x, UCStm [x, lv] rv : CStm [Subtask [lv] [rv]] [] x : axioms, nc ) 
                   where (lv, rv, axioms, x, nc) = trHelp l r c  
tr (Conj l r) c = (x, UCStm [lv, rv] x : UCStm [x] lv : UCStm [x] rv : axioms, nc) 
                   where (lv, rv, axioms, x, nc) = trHelp l r c
tr (Atom p) c   = (Var p, [], c)

trHelp l r c = (lv, rv, laxioms ++ raxioms, x, nc) 
               where    x = makeVar nc
                        nc = rc + 1
                        (lv, laxioms, lc) = tr l c
                        (rv, raxioms, rc) = tr r lc

makeVar :: Int -> Var
makeVar c = Var ("X" ++ show c)
--tests
kripke = (((a --> b) --> a) --> a) --> b
kripke2 = ((((a --> b) --> a) --> a) --> b) --> b

testTransl f = show f ++ " -----> " ++ foldl (\acc l -> if null acc then show l else acc ++ "; " ++ show l) "" (snd $ transl f)

tt1 = testTransl kripke  -- in CoCoViLa the goal is X4 -> b;
tt2 = testTransl kripke2 -- in CoCoViLa the goal is -> X5;

-- /transform IL into LL

----------Propositional logic
data Prop = Atom String |
            Conj Prop  Prop |
            Impl Prop Prop |
            T |
            F
            deriving (Eq,Ord)

isAtom (Atom _) = True
isAtom _ = False

instance Num Prop where
    p * q = Conj p q
    negate p   = Impl p F

infixr 4 -->

p --> q = Impl p q

a = Atom "a"
b = Atom "b"
c = Atom "c"
p = Atom "p"
q = Atom "q"
r = Atom "r"
v = Atom "v"
x = Atom "x"
y = Atom "y"
z = Atom "z"

instance Show Prop where
    show (Atom p) = p
    show (Conj p q) = "(" ++ show p ++ "&" ++ show q ++ ")"
    show (Impl p q) = "(" ++ show p ++ "->" ++ show q ++ ")"
    show T = "T"
    show F = "F"

