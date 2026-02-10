-- SPDX-License-Identifier: PMPL-1.0-or-later
-- ProofTerm.idr - Dependent-typed representation of proof terms

module ProofTerm

-- AST for proof terms (dependent type theory)
public export
data ProofTerm : Type where
  -- Variables
  Var        : String -> ProofTerm

  -- Type constructors
  TyNat      : ProofTerm
  TyBool     : ProofTerm
  TyProp     : ProofTerm

  -- Term constructors
  Zero       : ProofTerm
  Succ       : ProofTerm -> ProofTerm
  True       : ProofTerm
  False      : ProofTerm

  -- Quantifiers
  Forall     : String -> ProofTerm -> ProofTerm -> ProofTerm
  Exists     : String -> ProofTerm -> ProofTerm -> ProofTerm

  -- Logic
  Implies    : ProofTerm -> ProofTerm -> ProofTerm
  And        : ProofTerm -> ProofTerm -> ProofTerm
  Or         : ProofTerm -> ProofTerm -> ProofTerm
  Not        : ProofTerm -> ProofTerm

  -- Equality
  Eq         : ProofTerm -> ProofTerm -> ProofTerm

  -- Function application
  App        : ProofTerm -> ProofTerm -> ProofTerm

  -- Lambda abstraction
  Lambda     : String -> ProofTerm -> ProofTerm -> ProofTerm

  -- Proof tactics as terms
  Axiom      : String -> ProofTerm
  Refl       : ProofTerm
  Intro      : String -> ProofTerm -> ProofTerm
  Apply      : ProofTerm -> ProofTerm -> ProofTerm

-- Pretty printing
export
Show ProofTerm where
  show (Var name) = name
  show TyNat = "Nat"
  show TyBool = "Bool"
  show TyProp = "Prop"
  show Zero = "0"
  show (Succ n) = "S(" ++ show n ++ ")"
  show True = "true"
  show False = "false"
  show (Forall name ty body) =
    "∀(" ++ name ++ " : " ++ show ty ++ "), " ++ show body
  show (Exists name ty body) =
    "∃(" ++ name ++ " : " ++ show ty ++ "), " ++ show body
  show (Implies p q) = show p ++ " → " ++ show q
  show (And p q) = show p ++ " ∧ " ++ show q
  show (Or p q) = show p ++ " ∨ " ++ show q
  show (Not p) = "¬" ++ show p
  show (Eq lhs rhs) = show lhs ++ " = " ++ show rhs
  show (App f arg) = show f ++ " " ++ show arg
  show (Lambda name ty body) =
    "λ(" ++ name ++ " : " ++ show ty ++ ") ⇒ " ++ show body
  show (Axiom name) = "axiom[" ++ name ++ "]"
  show Refl = "refl"
  show (Intro name body) = "intro " ++ name ++ "; " ++ show body
  show (Apply lemma goal) = "apply " ++ show lemma ++ " to " ++ show goal

-- Equality for proof terms
export
Eq ProofTerm where
  (Var n1) == (Var n2) = n1 == n2
  TyNat == TyNat = True
  TyBool == TyBool = True
  TyProp == TyProp = True
  Zero == Zero = True
  (Succ n1) == (Succ n2) = n1 == n2
  True == True = True
  False == False = True
  (Forall n1 ty1 b1) == (Forall n2 ty2 b2) =
    n1 == n2 && ty1 == ty2 && b1 == b2
  (Exists n1 ty1 b1) == (Exists n2 ty2 b2) =
    n1 == n2 && ty1 == ty2 && b1 == b2
  (Implies p1 q1) == (Implies p2 q2) = p1 == p2 && q1 == q2
  (And p1 q1) == (And p2 q2) = p1 == p2 && q1 == q2
  (Or p1 q1) == (Or p2 q2) = p1 == p2 && q1 == q2
  (Not p1) == (Not p2) = p1 == p2
  (Eq lhs1 rhs1) == (Eq lhs2 rhs2) = lhs1 == lhs2 && rhs1 == rhs2
  (App f1 a1) == (App f2 a2) = f1 == f2 && a1 == a2
  (Lambda n1 ty1 b1) == (Lambda n2 ty2 b2) =
    n1 == n2 && ty1 == ty2 && b1 == b2
  (Axiom n1) == (Axiom n2) = n1 == n2
  Refl == Refl = True
  (Intro n1 b1) == (Intro n2 b2) = n1 == n2 && b1 == b2
  (Apply l1 g1) == (Apply l2 g2) = l1 == l2 && g1 == g2
  _ == _ = False

-- Context for type checking
public export
data Context : Type where
  Empty  : Context
  Extend : Context -> String -> ProofTerm -> Context

-- Look up variable type in context
export
lookup : Context -> String -> Maybe ProofTerm
lookup Empty _ = Nothing
lookup (Extend ctx name ty) target =
  if name == target
    then Just ty
    else lookup ctx target

-- Example proof terms
export
exampleGoal : ProofTerm
exampleGoal = Forall "n" TyNat (Forall "m" TyNat
  (Eq (App (App (Var "plus") (Var "n")) (Var "m"))
      (App (App (Var "plus") (Var "m")) (Var "n"))))

export
exampleProof : ProofTerm
exampleProof = Intro "n" (Intro "m" Refl)
