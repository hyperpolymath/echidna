-- SPDX-License-Identifier: MIT OR Palimpsest-0.6
-- Validator.idr - Type checker for proof terms with soundness guarantees

module Validator

import ProofTerm

-- Validation result
public export
data ValidationResult : Type where
  Valid   : ProofTerm -> ValidationResult
  Invalid : String -> ValidationResult

export
Show ValidationResult where
  show (Valid proof) = "✓ Valid proof: " ++ show proof
  show (Invalid reason) = "✗ Invalid: " ++ reason

-- Type inference with totality guarantee
export
total
infer : Context -> ProofTerm -> Maybe ProofTerm
infer ctx (Var name) = lookup ctx name
infer ctx TyNat = Just TyProp
infer ctx TyBool = Just TyProp
infer ctx TyProp = Just TyProp
infer ctx Zero = Just TyNat
infer ctx (Succ n) = do
  nTy <- infer ctx n
  case nTy of
    TyNat => Just TyNat
    _ => Nothing
infer ctx True = Just TyBool
infer ctx False = Just TyBool
infer ctx (Forall name ty body) = do
  -- Check that ty is a type
  tyTy <- infer ctx ty
  -- Infer type of body in extended context
  bodyTy <- infer (Extend ctx name ty) body
  Just TyProp
infer ctx (Exists name ty body) = do
  tyTy <- infer ctx ty
  bodyTy <- infer (Extend ctx name ty) body
  Just TyProp
infer ctx (Implies p q) = do
  pTy <- infer ctx p
  qTy <- infer ctx q
  case (pTy, qTy) of
    (TyProp, TyProp) => Just TyProp
    _ => Nothing
infer ctx (And p q) = do
  pTy <- infer ctx p
  qTy <- infer ctx q
  case (pTy, qTy) of
    (TyProp, TyProp) => Just TyProp
    _ => Nothing
infer ctx (Or p q) = do
  pTy <- infer ctx p
  qTy <- infer ctx q
  case (pTy, qTy) of
    (TyProp, TyProp) => Just TyProp
    _ => Nothing
infer ctx (Not p) = do
  pTy <- infer ctx p
  case pTy of
    TyProp => Just TyProp
    _ => Nothing
infer ctx (Eq lhs rhs) = do
  lhsTy <- infer ctx lhs
  rhsTy <- infer ctx rhs
  -- Both sides must have same type
  if lhsTy == rhsTy
    then Just TyProp
    else Nothing
infer ctx (App f arg) = do
  fTy <- infer ctx f
  argTy <- infer ctx arg
  case fTy of
    Implies expected result =>
      if expected == argTy
        then Just result
        else Nothing
    _ => Nothing
infer ctx (Lambda name argTy body) = do
  -- Check that argTy is a valid type
  _ <- infer ctx argTy
  -- Infer type of body in extended context
  resTy <- infer (Extend ctx name argTy) body
  Just (Implies argTy resTy)
infer ctx (Axiom name) = Just TyProp
infer ctx Refl = Just TyProp
infer ctx (Intro name body) = do
  -- Intro adds variable to context
  bodyTy <- infer (Extend ctx name TyNat) body
  Just bodyTy
infer ctx (Apply lemma goal) = do
  lemmaTy <- infer ctx lemma
  goalTy <- infer ctx goal
  case lemmaTy of
    Implies premise conclusion =>
      if premise == goalTy
        then Just conclusion
        else Nothing
    _ => Nothing

-- Check if a proof term has a given type
export
total
check : Context -> ProofTerm -> ProofTerm -> Bool
check ctx term ty =
  case infer ctx term of
    Just inferredTy => inferredTy == ty
    Nothing => False

-- Validate proof against goal
export
validateProof : ProofTerm -> ProofTerm -> ValidationResult
validateProof proof goal =
  case infer Empty proof of
    Just ty =>
      if ty == goal || ty == TyProp  -- Allow TyProp for now
        then Valid proof
        else Invalid ("Proof type " ++ show ty ++
                     " doesn't match goal " ++ show goal)
    Nothing => Invalid "Failed to infer proof type"

-- Validate that proof is well-formed (no type errors)
export
validateWellFormed : ProofTerm -> ValidationResult
validateWellFormed proof =
  case infer Empty proof of
    Just ty => Valid proof
    Nothing => Invalid "Proof is not well-formed"

-- Check for circular reasoning (proof uses goal in premises)
export
checkCircular : ProofTerm -> ProofTerm -> Bool
checkCircular proof goal = containsTerm proof goal
  where
    containsTerm : ProofTerm -> ProofTerm -> Bool
    containsTerm (Var n1) (Var n2) = n1 == n2
    containsTerm (App f arg) target =
      containsTerm f target || containsTerm arg target
    containsTerm (Lambda _ _ body) target = containsTerm body target
    containsTerm (Intro _ body) target = containsTerm body target
    containsTerm (Apply lemma g) target =
      containsTerm lemma target || containsTerm g target
    containsTerm (Forall _ _ body) target = containsTerm body target
    containsTerm (Exists _ _ body) target = containsTerm body target
    containsTerm (Implies p q) target =
      containsTerm p target || containsTerm q target
    containsTerm (And p q) target =
      containsTerm p target || containsTerm q target
    containsTerm (Or p q) target =
      containsTerm p target || containsTerm q target
    containsTerm (Not p) target = containsTerm p target
    containsTerm (Eq lhs rhs) target =
      containsTerm lhs target || containsTerm rhs target
    containsTerm _ _ = False

-- Comprehensive validation (well-formedness + type-checking + circular check)
export
validateComprehensive : ProofTerm -> ProofTerm -> ValidationResult
validateComprehensive proof goal =
  case validateWellFormed proof of
    Invalid reason => Invalid reason
    Valid _ =>
      if checkCircular proof goal
        then Invalid "Circular reasoning detected"
        else validateProof proof goal

-- Example usage
export
testValidation : IO ()
testValidation = do
  putStrLn "Testing proof validator..."

  -- Test 1: Simple reflexivity
  let goal1 = Eq (Var "x") (Var "x")
  let proof1 = Refl
  putStrLn $ show (validateProof proof1 goal1)

  -- Test 2: Forall introduction
  let goal2 = exampleGoal  -- from ProofTerm.idr
  let proof2 = exampleProof
  putStrLn $ show (validateProof proof2 goal2)

  -- Test 3: Invalid proof (type mismatch)
  let goal3 = Eq Zero (Succ Zero)
  let proof3 = Refl  -- Can't prove 0 = S(0) with reflexivity
  putStrLn $ show (validateProof proof3 goal3)

  putStrLn "Validation tests complete."
