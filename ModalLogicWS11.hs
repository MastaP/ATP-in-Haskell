module ModalTableau where

import Maybe

data Prop = Atm String
          | Not Prop
          | Conj Prop Prop
          | Disj Prop Prop
          | Impl Prop Prop
          | Box Prop
          | Dia Prop
          | T
          | F
          deriving(Eq,Ord)

instance Show Prop where
         show (Atm s)    = s
         show (Not p)    = "~" ++ show p
         show (Conj l r) = "(" ++ show l ++ " & " ++ show r ++ ")"
         show (Disj l r) = "(" ++ show l ++ " V " ++ show r ++ ")"
         show (Impl l r) = "(" ++ show l ++ " -> " ++ show r ++ ")"
         show (Box p)    = "[]" ++ show p
         show (Dia p)    = "<>" ++ show p
         show (T)        = "T"
         show (F)        = "F"

nnf :: Prop -> Prop
nnf t@(Not p) = case p of
                  (Atm s)    -> t
                  (Not q)    -> q
                  (Disj l r) -> nnf (Conj (Not l) (Not r))
                  (Conj l r) -> nnf (Disj (Not l) (Not r))
                  (Impl l r) -> nnf (Conj l (Not r))
                  (Dia s)    -> nnf (Box (Not s))
                  (Box s)    -> nnf (Dia (Not s))
                  T          -> F
                  F          -> T
nnf (Impl l r) = nnf (Disj (Not l) r)
nnf (Disj l r) = Disj (nnf l) (nnf r)
nnf (Conj l r) = Conj (nnf l) (nnf r)
nnf (Dia s)    = Dia (nnf s)
nnf (Box s)    = Box (nnf s)
nnf p          = p

p = Atm "p"
q = Atm "q"

f1 = Not(Impl(Box(Impl p q)) (Impl(Box p) (Box q)))
f2 = Not(Impl(Box p) p)
f3 = Not(Impl(Box p) (Box(Box p)))

test_nnf = putStr $ foldr (\f s -> show f ++ " => " ++ show (nnf f) ++ "\n" ++ s) "" [f1,f2,f3]

isAtom (Atm _) = True
isAtom _       = False
isNegAtom p = case p of 
                (Not p)   -> isAtom p
                otherwise -> False
invert (Not p) = p
invert p       = Not p

data TreeNode = Root [Prop] [TreeNode]
              | Node [Prop] [TreeNode] TreeNode

--id :: [Prop] -> 
rule_id [] = ["open"]
rule_id (p:ps) | isAtom p && (Not p) `elem` ps     = ["closed"]
               | isNegAtom p && invert p `elem` ps = ["closed"]
               | otherwise                         = rule_id ps

t1 = rule_id [q,(Not p),p]

rule_and [] = []
rule_and (p:ps) = case p of
                    (Conj l r) -> l:r:ps
                    otherwise  -> p : rule_and ps

t2 = rule_and [p,(Conj p q),q,(Not p)]

rule_or [] = []
rule_or (p:ps) = case p of
                   (Disj l r) -> []
                   otherwise  -> p : rule_or ps