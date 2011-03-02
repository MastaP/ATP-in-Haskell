module ModalTableau where

import Maybe
import List (delete)
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
nnf t@(Not (Atm _))  = t
nnf (Not (Not q))   = q
nnf (Not (Disj l r)) = nnf (Conj (Not l) (Not r))
nnf (Not (Conj l r)) = nnf (Disj (Not l) (Not r))
nnf (Not (Impl l r)) = nnf (Conj l (Not r))
nnf (Not (Dia s))   = nnf (Box (Not s))
nnf (Not (Box s))   = nnf (Dia (Not s))
nnf (Not T)         = F
nnf (Not F)         = T
nnf (Impl l r)      = nnf (Disj (Not l) r)
nnf (Disj l r)      = Disj (nnf l) (nnf r)
nnf (Conj l r)      = Conj (nnf l) (nnf r)
nnf (Dia s)         = Dia (nnf s)
nnf (Box s)         = Box (nnf s)
nnf p               = p

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

data Rule = RuleId | RuleConj | RuleDisj | RuleK deriving Show

data Tree = Node [Prop] Rule [Tree] (Maybe Tree) deriving Show

--axiomG3ip (Seq as [p]) | isAtom p && p `elem` as = [([],Axiom)]
--id :: [Prop] -> 
ruleId [] = []
ruleId (p:ps) | isAtom p && (Not p) `elem` ps     = [([],RuleId)]
               | isNegAtom p && invert p `elem` ps = [([],RuleId)]
               | otherwise                         = ruleId ps

t1 = ruleId [q,(Not p),p]

ruleConj fs = [([delConj fs], RuleConj)]

delConj (Conj l r:fs) = l:r:delConj fs
delConj (f:fs) = f:delConj fs
delConj [] = [] 

t2 = ruleConj [p,(Conj p q),q,(Not p),(Conj p (Not q))]

ruleDisj fs = [ (fs'',RuleDisj) | fs'' <- [ let fs' = delete f fs in [l:fs', r:fs'] | f@(Disj l r) <- fs]]

t3 = ruleDisj [p,(Disj p q),q,(Not p),(Disj p (Not q))]

--assumes boxes have been removed
isSaturated ((Conj _ _):_) = False
isSaturated ((Disj _ _):_) = False
isSaturated (_:fs)         = isSaturated fs
isSaturated []             = True

ruleK gs fs = let bs = [ b | Box b <- fs]
              in if isSaturated fs 
                    then [ ([fs'],RuleK) | fs' <- [ gs ++ (f : bs) | d@(Dia f) <- fs ]] 
                  else []

t4 = ruleK [] [p,Dia p,Box q]
t4_1 = ruleK [Not (Not p)] [p,Dia q,Box (Not q)]
t4_2 = ruleK [Not p] [p,Dia p,Box q,Conj p q]
t4_3 = ruleK [Not p] [p,Dia p,Box q,Dia q]

(f +++ g) x = f x ++ g x

tactics gs = ruleId +++ ruleConj +++ ruleDisj +++ (ruleK gs)

proof ts fs = --tactics formulas gamma
    let subtrees = [(subtree,rule) | (subgoal,rule) <- ts fs, subtree <- [map (proof ts) subgoal], all isJust subtree]
    in if null subtrees
          then Nothing
       else let (subtree,rule) = head subtrees in Just (Node fs rule (map fromJust $ subtree) Nothing)

fp1 = Not (Impl (Box (Impl p q)) (Impl (Box p) (Box q)))
tp1 = proof (tactics []) [nnf fp1]

fp2 = (Not(Impl (Box p) p))
tp2 = proof (tactics []) [nnf fp2]

fp3 = (Not(Impl (Box p) (Box (Box p))))
tp3 = proof (tactics []) [nnf fp3]

g1 = [Dia p]
tp_l = proof (tactics g1) $ map nnf $ g1 ++ [q]
