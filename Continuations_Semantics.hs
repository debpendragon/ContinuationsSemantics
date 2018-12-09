{-# LANGUAGE GADTs, TypeFamilies, DataKinds #-}

module FinalProject where


----- Syntax of first-order predicate logic

data Variable = MkVar Int deriving Eq

data Term = VarTerm Variable | ConstTerm String deriving Eq

data Predicate = MkPred String deriving Eq

data Formula = Atom Predicate [Term]
             | Neg  Formula
             | Impl Formula Formula
             | Conj Formula Formula
             | Disj Formula Formula
             | Forall Variable Formula
             | Exists Variable Formula
             deriving Eq

instance Show Variable where show = showVar
showVar :: Variable -> String
showVar (MkVar n)  = "x" ++ (show n)

instance Show Term where show = showTerm
showTerm :: Term -> String
showTerm (VarTerm v)    = showVar v
showTerm (ConstTerm s)  = s

instance Show Predicate where show = showPredicate
showPredicate :: Predicate -> String
showPredicate (MkPred s) = s

instance Show Formula where show = showFormula
showFormula :: Formula -> String
showFormula (Atom p ts)   = (show p) ++ "(" ++ (foldr (\x y -> if elem "" [x,y] then x ++ y else x ++ "," ++ y) "" (map showTerm ts)) ++ ")"
showFormula (Neg form)    = '-' : (showFormula form)
showFormula (Impl f1 f2)  = "(" ++ showFormula f1 ++ " ==> " ++ showFormula f2 ++ ")"
showFormula (Conj f1 f2)  = "(" ++ showFormula f1 ++ " ^ " ++ showFormula f2 ++ ")"
showFormula (Disj f1 f2)  = "(" ++ showFormula f1 ++ " v " ++ showFormula f2 ++ ")"
showFormula (Forall v f)  = "(" ++ "A " ++  showVar v ++ (' ' : showFormula f) ++ ")"
showFormula (Exists v f)  = "(" ++ "E " ++  showVar v ++ (' ' : showFormula f) ++ ")"

-------------------------------------------------------------------
-------------------------------------------------------------------
----- A grammar encoded in the type system

data Cat = S | NP | VP | V | Adv deriving (Show,Eq)

data StrucDesc (a :: Cat) where
    VbSnt :: StrucDesc NP -> StrucDesc VP -> StrucDesc S
    TrVP  :: StrucDesc V -> StrucDesc NP -> StrucDesc VP
    NegVP :: StrucDesc Adv -> StrucDesc VP -> StrucDesc VP
    And :: StrucDesc a -> StrucDesc a -> StrucDesc a
    IfThen :: StrucDesc S -> StrucDesc S -> StrucDesc S
    John, Mary, Fred, Everyone, Someone, Anything , MoveAny:: StrucDesc NP
    Know, Meet, Buy :: StrucDesc V
    Not :: StrucDesc Adv
    
    ---added Anything and MoveAny with StrucDesc NP and added Not as StrucDesc Adv---

interpret :: StrucDesc S -> (String, Formula)
interpret sd = (pf sd id, lf sd id)

sd1 = VbSnt John (TrVP Meet Mary)
sd2 = VbSnt John (TrVP Meet Everyone)
sd3 = And sd1 (VbSnt Mary (TrVP Know Fred))
sd4 = VbSnt Mary (And (TrVP Know John) (TrVP Meet Fred))
sd5 = VbSnt Mary (TrVP (And Know Meet) John)
sd6 = VbSnt Mary (TrVP Know (And John Fred))
sd7 = VbSnt John (NegVP Not (TrVP Buy Anything))
sd8 = VbSnt John (NegVP Not (TrVP Buy MoveAny))

--sd7 is the sentence where the NPI is below negation while sd8 is the sentence where NPI is above negation---

type family SemInterp (a :: Cat) :: *
type instance SemInterp S  = Formula
type instance SemInterp NP = Term
type instance SemInterp VP = (Term -> Formula)
type instance SemInterp V  = (Term -> Term -> Formula)
type instance SemInterp Adv  = (Term -> Formula) -> Term -> Formula

--added SemInterp Adv--

lf :: StrucDesc a -> ((SemInterp a -> Formula) -> Formula)
lf (VbSnt np vp) = \k -> (lf np) (\r2 -> (lf vp) (\r1 -> k (r1 r2)))
lf (TrVP v np) = \k -> (lf v) (\r2 -> (lf np) (\r1 -> k (r2 r1)))

lf (NegVP adv vp) = if containsMove (NegVP adv vp) == True then \k -> (lf vp) (\r1 -> (lf adv) (\r2 -> k (r2 r1)))
else \k -> (lf adv) (\r1 -> (lf vp) (\r2 -> k (r1 r2)))

--added lf (NegVP adv vp) to handle cases of the different interpretation above and below negation---


lf John = \k -> k (ConstTerm "j")
lf Mary = \k -> k (ConstTerm "m")
lf Fred = \k -> k (ConstTerm "f")
lf Everyone = \k -> Forall (MkVar 1) (k (VarTerm (MkVar 1)))
lf Someone = \k -> Exists (MkVar 2) (k (VarTerm (MkVar 2)))
lf Know = \k -> k (\t1 -> \t2 -> (Atom (MkPred "K") [t2,t1]))
lf Meet = \k -> k (\t1 -> \t2 -> (Atom (MkPred "M") [t2,t1]))
lf Buy = \k -> k (\t1 -> \t2 -> (Atom (MkPred "B") [t2,t1]))
lf Anything = \k -> Exists (MkVar 3) (k (VarTerm (MkVar 3)))
lf MoveAny = \k -> Forall (MkVar 4) (k (VarTerm (MkVar 4)))
lf Not = \k -> Neg (k id)
lf (And t1 t2) =  \k -> (lf t1) (\r1 -> (lf t2) (\r2 -> (Conj (k r1)(k r2))))
lf (IfThen s1 s2) = \k -> (lf s2) (\r2 -> k (Impl (lf s1 id) r2))

--Anything is given an existential interpretation while MoveAny is given a universal interpretation--

containsMove :: StrucDesc a -> Bool 
containsMove MoveAny = True
containsMove  John = False
containsMove  Mary = False
containsMove  Fred = False
containsMove  Everyone = False
containsMove Someone = False
containsMove  Know = False
containsMove  Meet = False
containsMove  Buy = False
containsMove  Anything = False
containsMove  Not= False
containsMove (VbSnt np vp) = if containsMove np == True then True else containsMove vp
containsMove (TrVP v np) = if containsMove v == True then True else containsMove np
containsMove (NegVP adv vp) = if containsMove adv == True then True else containsMove vp
containsMove (And t1 t2) =  if containsMove t1 == True then True else containsMove t2
containsMove (IfThen s1 s2) = if containsMove s1 == True then True else containsMove s2

--containsMove looks through a StrucDesc to see whether MoveAny is part of it--

pf :: StrucDesc a -> ((String -> String) -> String)
pf John = \k -> k ("John")
pf Mary = \k -> k ("Mary")
pf Meet = \k -> k ("meets")

pf (VbSnt np1 vp) = \k -> (pf np1) (\r2 -> k (r2 +++ (pf vp id)))
pf (TrVP v np) = \k -> (pf v) (\r2 -> (pf np) (\r1 -> k (r2 +++ r1)))
pf (NegVP adv vp) = \k -> (pf adv) (\r2 -> (pf vp) (\r1 -> k (r2 +++ r1)))

pf Fred = \k -> k "Fred"
pf Everyone = \k -> k "everyone"
pf Someone = \k -> k "someone"
pf Know = \k -> k "knows"
pf Buy = \k -> k "buy"
pf Anything = \k -> k "anything"
pf (Not) = \k -> k "not"
pf MoveAny = \k -> "moveany" +++ k ""

--MoveAny is allowed to move above its continuation--

pf (And t1 t2) = \k -> (pf t1) (\r2 -> (pf t2) (\r1 -> k (r2 +++ "and" +++ r1)))
pf (IfThen s1 s2) = \k -> (pf s1) (\r2 -> (pf s2) (\r1 -> k ("if" +++ r2 +++ "then" +++ r1)))


--------------------------------------------------------------------

(+++) :: String -> String -> String
s +++ t =
    if s == "" || t == "" then
        s ++ t
    else
        s ++ " " ++ t

