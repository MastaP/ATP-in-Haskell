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

ruleId [] = []
ruleId (p:ps) | isAtom p && (Not p) `elem` ps     = [([],RuleId)]
               | isNegAtom p && invert p `elem` ps = [([],RuleId)]
               | otherwise                         = ruleId ps

t1 = ruleId [q,(Not p),p]

--ruleDisj fs = [ ([l:r:delete f fs],RuleDisj) | f@(Disj l r) <- fs]
ruleDisj fs = let (ds,fs') = delDisj fs in if null ds then [] else [([ds ++ fs'],RuleDisj)]

delDisj (Disj l r:fs) = (l:r:ds,fs') where (ds,fs') = delDisj fs
delDisj (f:fs)        = (ds,f:fs')   where (ds,fs') = delDisj fs
delDisj []            = ([],[]) 

t2 = ruleDisj [p,(Disj p q),q,(Not p),(Disj p (Not q))]
t21 = ruleDisj [p,q,(Not p)]

ruleConj fs = [ (fs'',RuleConj) | fs'' <- [ let fs' = delete f fs in [l:fs', r:fs'] | f@(Conj l r) <- fs]]

t3 = ruleConj [p,(Conj p q),q,(Not p),(Conj p (Not q))]

--assumes boxes have been removed
isSaturated ((Conj _ _):_) = False
isSaturated ((Disj _ _):_) = False
isSaturated (_:fs)         = isSaturated fs
isSaturated []             = True

ruleK gs fs = let bs = [ b | Dia b <- fs]
              in if isSaturated fs 
                    then [ ([fs'],RuleK) | fs' <- [ gs ++ (f : bs) | d@(Box f) <- fs ]] 
                  else []

t4 = ruleK [] [p,Dia p,Box q]
t4_1 = ruleK [Not (Not p)] [p,Dia q,Box (Not q)]
t4_2 = ruleK [Not p] [p,Dia p,Box q,Conj p q]
t4_3 = ruleK [Not p] [p,Dia p,Box q,Dia q,Box p]

(f +++ g) x = f x ++ g x

tactics gs = ruleId +++ ruleConj +++ ruleDisj +++ (ruleK gs)

--http://www.polyomino.f2s.com/david/haskell/gentzen.html
proof ts fs = --tactics formulas gamma
    let subtrees = [(subtree,rule) | (subgoal,rule) <- ts fs, subtree <- [map (proof ts) subgoal], all isJust subtree]
    in if null subtrees
          then Nothing
       else let (subtree,rule) = head subtrees in Just (Node fs rule (map fromJust $ subtree) Nothing)

fp1 = Impl (Box (Impl p q)) (Impl (Box p) (Box q)) --sat
tp1 = proof (tactics []) [nnf fp1]

fp2 = Impl (Box p) p --unsat
tp2 = proof (tactics []) [nnf fp2]

fp3 = Impl (Box p) (Box (Box p)) --unsat
tp3 = proof (tactics []) [nnf fp3]

g1 = [Not(Dia p)]
tp_l = let g = map nnf g1 in proof (tactics g) $ g ++ [nnf q]-- $ map nnf $ g1 ++ [q]

tp = proof (tactics []) [nnf (Box(Disj p (Not p)))]--sat