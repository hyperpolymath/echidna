-- SPDX-License-Identifier: PMPL-1.0-or-later
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
--
-- ProofStateSerialisation.idr
--
-- E12: ProofState serialization losslessness.
--
-- Proves the round-trip property for the ECHIDNA ProofState type:
-- for any well-formed ProofState, encode followed by decode returns
-- (Just ps) — the state is recovered exactly.
--
-- Modelling strategy
-- ------------------
-- The actual wire layer uses Cap'n Proto (crates/echidna-wire/).  Modelling
-- Cap'n Proto internals would require a deep embedding of the schema language
-- and byte-layout arithmetic.  Instead we model the key types faithfully and
-- prove the property at the abstract serialisation level, using an S-expression
-- tree as the intermediate wire type.  S-expressions provide:
--
--   1.  A simple, computable encode/decode pair with no string-parsing
--       complexity.
--   2.  A clean inductive structure that mirrors Term's tree structure,
--       making structural-induction proofs straightforward.
--   3.  Independence from any particular on-wire byte encoding — the
--       round-trip theorem holds regardless of how SExpr trees are
--       rendered to bytes (UTF-8, Cap'n Proto, CBOR, etc.).
--
-- The Serialisation record is parameterised over both the value type `a`
-- and the wire type `wire`.  Fixing `wire = SExpr` gives us the model;
-- the real implementation fixes `wire = Bytes` (Cap'n Proto).  The
-- round-trip property has identical statement in both cases.
--
-- Types modelled (from crates/echidna-core/src/core.rs)
-- ------------------------------------------------------
--   Term      -- Const | Var | App { func, args } | Lambda { param, param_type, body }
--              | Pi { param, param_type, body }
--   Goal      -- { id : String, target : Term, hypotheses : List (String, Term) }
--   ProofState -- { goals : List Goal, context : List (String, Term) }
--
-- Term is modelled with the five constructors used in the primary
-- proof-exchange paths (OpenTheory, Dedukti, GNN graph builder).
-- The remaining constructors (Sigma, Type, Sort, Let, Match, Fix, Hole,
-- Meta, ProverSpecific) follow the same structural pattern and can be
-- added without changing the proof strategy.
--
-- Zero believe_me.  All proofs are constructive (Refl / structural
-- induction / congruence).  No external libraries beyond `base`.

module ProofStateSerialisation

import Data.List

%default total

-- ============================================================================
-- Section 1: S-expression wire type
-- ============================================================================

||| A simple S-expression tree used as the abstract wire format.
|||
||| Each algebraic constructor is encoded as a Node whose tag string
||| uniquely identifies the constructor; fields become ordered children.
||| This tag-uniqueness is the invariant the decoder exploits.
public export
data SExpr : Type where
  ||| A leaf carrying a string label (constructor tag or literal value).
  Atom : String -> SExpr
  ||| An interior node: a tag string plus an ordered list of children.
  Node : String -> List SExpr -> SExpr

-- ============================================================================
-- Section 2: Serialisation record (polymorphic in wire type)
-- ============================================================================

||| A certified serialisation scheme for type `a` over wire type `wire`.
|||
||| The `roundtrip` field is a compile-time proof that decode is a left
||| inverse of encode — the losslessness invariant.
public export
record Serialisation (a : Type) (wire : Type) where
  constructor MkSer
  ||| Encode a value to the wire format.
  encode    : a -> wire
  ||| Decode a wire value, returning Nothing on malformed input.
  decode    : wire -> Maybe a
  ||| Proof that decode (encode x) = Just x for all x.
  roundtrip : (x : a) -> decode (encode x) = Just x

-- ============================================================================
-- Section 3: Term model
-- ============================================================================

||| Faithful model of `Term` from crates/echidna-core/src/core.rs.
|||
||| We model the five constructors used in the primary proof-exchange
||| paths (OpenTheory exporter, Dedukti exporter, GNN graph builder).
||| The structural proof pattern is identical for all remaining
||| constructors; they can be added without changing strategy.
|||
||| Matches `pub enum Term` in core.rs.
public export
data Term : Type where
  ||| Constant / atom.  Matches Term::Const(String).
  Const  : String -> Term
  ||| Variable.  Matches Term::Var(String).
  Var    : String -> Term
  ||| Function application.
  ||| Matches Term::App { func: Box<Term>, args: Vec<Term> }.
  App    : Term -> List Term -> Term
  ||| Lambda abstraction.
  ||| Matches Term::Lambda { param: String, param_type: Option<Box<Term>>, body: Box<Term> }.
  ||| param_type is modelled as Maybe Term (None = unannotated binder).
  Lambda : String -> Maybe Term -> Term -> Term
  ||| Dependent product (Pi type).
  ||| Matches Term::Pi { param: String, param_type: Box<Term>, body: Box<Term> }.
  Pi     : String -> Term -> Term -> Term

-- ============================================================================
-- Section 4: Term encoder / decoder (mutual definition)
-- ============================================================================

-- All helper encoders are lifted to top level so round-trip lemmas can
-- reference them directly.  Idris2 `where`-clause bindings are local and
-- cannot be mentioned in the types of sibling definitions.

||| Encode a Term to an SExpr.
|||
||| Encoding scheme (must be matched exactly by decodeTerm):
|||   Const s              → Node "Const" [Atom s]
|||   Var s                → Node "Var"   [Atom s]
|||   App f args           → Node "App"   [encodeTerm f,
|||                                         Node "args" (encodeTermList args)]
|||   Lambda p Nothing b   → Node "Lambda" [Atom p, Atom "none", encodeTerm b]
|||   Lambda p (Just t) b  → Node "Lambda" [Atom p, Node "some" [encodeTerm t],
|||                                          encodeTerm b]
|||   Pi p t b             → Node "Pi"    [Atom p, encodeTerm t, encodeTerm b]
public export
encodeTerm : Term -> SExpr

||| Encode a list of Terms.  Auxiliary for App encoding.
public export
encodeTermList : List Term -> List SExpr

encodeTerm (Const s)          = Node "Const" [Atom s]
encodeTerm (Var s)            = Node "Var"   [Atom s]
encodeTerm (App f args)       = Node "App"   [encodeTerm f, Node "args" (encodeTermList args)]
encodeTerm (Lambda p Nothing b)  = Node "Lambda" [Atom p, Atom "none", encodeTerm b]
encodeTerm (Lambda p (Just t) b) = Node "Lambda" [Atom p, Node "some" [encodeTerm t], encodeTerm b]
encodeTerm (Pi p t b)         = Node "Pi"    [Atom p, encodeTerm t, encodeTerm b]

encodeTermList []        = []
encodeTermList (t :: ts) = encodeTerm t :: encodeTermList ts

||| Decode an SExpr back to a Term.  Returns Nothing on malformed input.
|||
||| Each clause is the exact inverse of the corresponding encodeTerm clause.
public export
decodeTerm : SExpr -> Maybe Term

||| Decode a list of SExprs back to a list of Terms.
public export
decodeTermList : List SExpr -> Maybe (List Term)

decodeTerm (Node "Const" [Atom s]) = Just (Const s)
decodeTerm (Node "Var"   [Atom s]) = Just (Var s)
decodeTerm (Node "App" [fe, Node "args" argsE]) =
  case (decodeTerm fe, decodeTermList argsE) of
    (Just f, Just args) => Just (App f args)
    _                   => Nothing
decodeTerm (Node "Lambda" [Atom p, Atom "none", be]) =
  case decodeTerm be of
    Just b  => Just (Lambda p Nothing b)
    Nothing => Nothing
decodeTerm (Node "Lambda" [Atom p, Node "some" [te], be]) =
  case (decodeTerm te, decodeTerm be) of
    (Just t, Just b) => Just (Lambda p (Just t) b)
    _                => Nothing
decodeTerm (Node "Pi" [Atom p, te, be]) =
  case (decodeTerm te, decodeTerm be) of
    (Just t, Just b) => Just (Pi p t b)
    _                => Nothing
decodeTerm _ = Nothing

decodeTermList [] = Just []
decodeTermList (e :: es) =
  case (decodeTerm e, decodeTermList es) of
    (Just t, Just ts) => Just (t :: ts)
    _                 => Nothing

-- ============================================================================
-- Section 5: Round-trip proof for Term (mutual induction)
-- ============================================================================

||| Key lemma: decodeTermList (encodeTermList ts) = Just ts.
|||
||| Proved by structural induction on ts, using termRoundtrip as IH
||| for each element.  Mutually recursive with termRoundtrip because
||| App contains a List Term.
public export
termListRoundtrip : (ts : List Term)
                  -> decodeTermList (encodeTermList ts) = Just ts

||| Round-trip theorem for Term.
|||
||| Proof strategy: structural induction on t.
|||   Const, Var   : decoder matches unique tag; returns Just immediately. Refl.
|||   App          : IH on func; termListRoundtrip on args.  Rewrite + Refl.
|||   Lambda None  : IH on body.  Rewrite + Refl.
|||   Lambda Some  : IH on param_type and body.  Rewrite + Refl.
|||   Pi           : IH on param_type and body.  Rewrite + Refl.
public export
termRoundtrip : (t : Term)
              -> decodeTerm (encodeTerm t) = Just t

termRoundtrip (Const s) = Refl
termRoundtrip (Var   s) = Refl

termRoundtrip (App f args) =
  -- decodeTerm (Node "App" [encodeTerm f, Node "args" (encodeTermList args)])
  -- reduces to:
  --   case (decodeTerm (encodeTerm f), decodeTermList (encodeTermList args)) of
  --     (Just f', Just args') => Just (App f' args')
  -- By IH: both return Just. QED.
  rewrite termRoundtrip f in
  rewrite termListRoundtrip args in
  Refl

termRoundtrip (Lambda p Nothing b) =
  -- decodeTerm (Node "Lambda" [Atom p, Atom "none", encodeTerm b])
  -- reduces to:
  --   case decodeTerm (encodeTerm b) of Just b' => Just (Lambda p Nothing b')
  -- By IH on b. QED.
  rewrite termRoundtrip b in
  Refl

termRoundtrip (Lambda p (Just t) b) =
  -- decodeTerm (Node "Lambda" [Atom p, Node "some" [encodeTerm t], encodeTerm b])
  -- reduces to:
  --   case (decodeTerm (encodeTerm t), decodeTerm (encodeTerm b)) of
  --     (Just t', Just b') => Just (Lambda p (Just t') b')
  -- By IH on t and b. QED.
  rewrite termRoundtrip t in
  rewrite termRoundtrip b in
  Refl

termRoundtrip (Pi p t b) =
  -- decodeTerm (Node "Pi" [Atom p, encodeTerm t, encodeTerm b])
  -- reduces to:
  --   case (decodeTerm (encodeTerm t), decodeTerm (encodeTerm b)) of
  --     (Just t', Just b') => Just (Pi p t' b')
  -- By IH on t and b. QED.
  rewrite termRoundtrip t in
  rewrite termRoundtrip b in
  Refl

-- List round-trip by structural induction.
termListRoundtrip [] = Refl
termListRoundtrip (t :: ts) =
  rewrite termRoundtrip t in
  rewrite termListRoundtrip ts in
  Refl

-- ============================================================================
-- Section 6: Hypothesis pair encoder / decoder
-- ============================================================================

||| Encode a (name, type) hypothesis pair to an SExpr.
||| Used by encodeGoal.
public export
encodeHyp : (String, Term) -> SExpr
encodeHyp (name, ty) = Node "hyp" [Atom name, encodeTerm ty]

||| Encode a list of hypothesis pairs.
public export
encodeHypList : List (String, Term) -> List SExpr
encodeHypList = map encodeHyp

||| Decode a single hypothesis pair.
public export
decodeHyp : SExpr -> Maybe (String, Term)
decodeHyp (Node "hyp" [Atom name, te]) =
  case decodeTerm te of
    Just ty => Just (name, ty)
    Nothing => Nothing
decodeHyp _ = Nothing

||| Decode a list of hypothesis pairs.
public export
decodeHypList : List SExpr -> Maybe (List (String, Term))
decodeHypList [] = Just []
decodeHypList (e :: es) =
  case (decodeHyp e, decodeHypList es) of
    (Just h, Just hs) => Just (h :: hs)
    _                 => Nothing

-- ============================================================================
-- Section 7: Round-trip proof for hypotheses
-- ============================================================================

||| Lemma: decodeHyp (encodeHyp h) = Just h.
public export
hypRoundtrip : (h : (String, Term)) -> decodeHyp (encodeHyp h) = Just h
hypRoundtrip (name, ty) =
  -- encodeHyp (name, ty) = Node "hyp" [Atom name, encodeTerm ty]
  -- decodeHyp matches: case decodeTerm (encodeTerm ty) of Just ty' => Just (name, ty')
  -- By termRoundtrip ty: decodeTerm (encodeTerm ty) = Just ty. QED.
  rewrite termRoundtrip ty in
  Refl

||| Lemma: decodeHypList (encodeHypList hyps) = Just hyps.
public export
hypListRoundtrip : (hyps : List (String, Term))
                 -> decodeHypList (encodeHypList hyps) = Just hyps
hypListRoundtrip [] = Refl
hypListRoundtrip (h :: hs) =
  rewrite hypRoundtrip h in
  rewrite hypListRoundtrip hs in
  Refl

-- ============================================================================
-- Section 8: Goal model and encoder / decoder
-- ============================================================================

||| Model of `Goal` from crates/echidna-core/src/core.rs.
|||
||| Matches:
|||   pub struct Goal { pub id: String, pub target: Term,
|||                     pub hypotheses: Vec<Hypothesis> }
|||
||| Hypotheses are modelled as (name, type) pairs.  The optional body
||| field and type_info are omitted from the losslessness claim.
public export
record Goal where
  constructor MkGoal
  ||| Unique goal identifier.  Matches Goal::id.
  goalId     : String
  ||| The proposition to prove.  Matches Goal::target.
  target     : Term
  ||| Local hypotheses as (name, type) pairs.  Matches Goal::hypotheses.
  hypotheses : List (String, Term)

||| Encode a Goal to an SExpr.
|||
||| Encoding scheme:
|||   Node "Goal" [Atom id, encodeTerm target,
|||                Node "hyps" (encodeHypList hypotheses)]
public export
encodeGoal : Goal -> SExpr
encodeGoal (MkGoal gid tgt hyps) =
  Node "Goal" [Atom gid, encodeTerm tgt, Node "hyps" (encodeHypList hyps)]

||| Decode a Goal from an SExpr.
public export
decodeGoal : SExpr -> Maybe Goal
decodeGoal (Node "Goal" [Atom gid, te, Node "hyps" hypsE]) =
  case (decodeTerm te, decodeHypList hypsE) of
    (Just tgt, Just hyps) => Just (MkGoal gid tgt hyps)
    _                     => Nothing
decodeGoal _ = Nothing

-- ============================================================================
-- Section 9: Round-trip proof for Goal
-- ============================================================================

||| Round-trip theorem for Goal.
|||
||| Proof: rewrite with termRoundtrip for target and hypListRoundtrip for
||| hypotheses; both sub-decoders return Just; decoder fires. QED.
public export
goalRoundtrip : (g : Goal) -> decodeGoal (encodeGoal g) = Just g
goalRoundtrip (MkGoal gid tgt hyps) =
  -- encodeGoal g = Node "Goal" [Atom gid, encodeTerm tgt, Node "hyps" (encodeHypList hyps)]
  -- decodeGoal matches Node "Goal" [Atom gid, te, Node "hyps" hypsE]:
  --   case (decodeTerm te, decodeHypList hypsE) of
  --     (Just tgt', Just hyps') => Just (MkGoal gid tgt' hyps')
  -- By termRoundtrip tgt and hypListRoundtrip hyps. QED.
  rewrite termRoundtrip tgt in
  rewrite hypListRoundtrip hyps in
  Refl

-- ============================================================================
-- Section 10: Goal list encoder / decoder
-- ============================================================================

||| Encode a list of Goals.
public export
encodeGoalList : List Goal -> List SExpr
encodeGoalList = map encodeGoal

||| Decode a list of Goals.
public export
decodeGoalList : List SExpr -> Maybe (List Goal)
decodeGoalList [] = Just []
decodeGoalList (e :: es) =
  case (decodeGoal e, decodeGoalList es) of
    (Just g, Just gs) => Just (g :: gs)
    _                 => Nothing

||| Lemma: decodeGoalList (encodeGoalList gs) = Just gs.
public export
goalListRoundtrip : (gs : List Goal)
                  -> decodeGoalList (encodeGoalList gs) = Just gs
goalListRoundtrip [] = Refl
goalListRoundtrip (g :: gs) =
  rewrite goalRoundtrip g in
  rewrite goalListRoundtrip gs in
  Refl

-- ============================================================================
-- Section 11: Context entry encoder / decoder
-- ============================================================================

||| Encode a context entry (name, type) to an SExpr.
||| Used by encodeProofState.
public export
encodeCtxEntry : (String, Term) -> SExpr
encodeCtxEntry (name, ty) = Node "ctx" [Atom name, encodeTerm ty]

||| Encode a list of context entries.
public export
encodeCtxList : List (String, Term) -> List SExpr
encodeCtxList = map encodeCtxEntry

||| Decode a single context entry.
public export
decodeCtxEntry : SExpr -> Maybe (String, Term)
decodeCtxEntry (Node "ctx" [Atom name, te]) =
  case decodeTerm te of
    Just ty => Just (name, ty)
    Nothing => Nothing
decodeCtxEntry _ = Nothing

||| Decode a list of context entries.
public export
decodeCtxList : List SExpr -> Maybe (List (String, Term))
decodeCtxList [] = Just []
decodeCtxList (e :: es) =
  case (decodeCtxEntry e, decodeCtxList es) of
    (Just c, Just cs) => Just (c :: cs)
    _                 => Nothing

||| Lemma: decodeCtxEntry (encodeCtxEntry entry) = Just entry.
public export
ctxEntryRoundtrip : (entry : (String, Term))
                  -> decodeCtxEntry (encodeCtxEntry entry) = Just entry
ctxEntryRoundtrip (name, ty) =
  rewrite termRoundtrip ty in
  Refl

||| Lemma: decodeCtxList (encodeCtxList ctx) = Just ctx.
public export
ctxListRoundtrip : (ctx : List (String, Term))
                 -> decodeCtxList (encodeCtxList ctx) = Just ctx
ctxListRoundtrip [] = Refl
ctxListRoundtrip (entry :: entries) =
  rewrite ctxEntryRoundtrip entry in
  rewrite ctxListRoundtrip entries in
  Refl

-- ============================================================================
-- Section 12: ProofState model and encoder / decoder
-- ============================================================================

||| Model of `ProofState` from crates/echidna-core/src/core.rs.
|||
||| Matches:
|||   pub struct ProofState {
|||     pub goals    : Vec<Goal>,
|||     pub context  : Context,
|||     pub metadata : HashMap<String, Value>,
|||   }
|||
||| The `metadata` field is excluded from the losslessness claim.  It
||| carries prover-specific JSON values whose round-trip depends on the
||| JSON encoding, not on Term/Goal encoding.  The claim is:
|||   "the proof-relevant fields (goals, context) are recovered exactly".
|||
||| `context` is modelled as a flat list of (name, type) pairs
||| (Context::theorems and Context::axioms collapsed), which is the
||| minimal structure used by the cross-prover exchange layer
||| (exchange/opentheory.rs, exchange/dedukti.rs).
public export
record ProofState where
  constructor MkProofState
  ||| Outstanding proof goals.  Matches ProofState::goals.
  goals   : List Goal
  ||| Global context: named type terms.  Matches Context::theorems
  ||| and Context::axioms, collapsed.
  context : List (String, Term)

||| Encode a ProofState to an SExpr.
|||
||| Encoding scheme:
|||   Node "ProofState"
|||     [ Node "goals"   (encodeGoalList goals)
|||     , Node "context" (encodeCtxList context)
|||     ]
public export
encodeProofState : ProofState -> SExpr
encodeProofState (MkProofState gs ctx) =
  Node "ProofState"
    [ Node "goals"   (encodeGoalList gs)
    , Node "context" (encodeCtxList ctx)
    ]

||| Decode a ProofState from an SExpr.
public export
decodeProofState : SExpr -> Maybe ProofState
decodeProofState (Node "ProofState" [Node "goals" gsE, Node "context" ctxE]) =
  case (decodeGoalList gsE, decodeCtxList ctxE) of
    (Just gs, Just ctx) => Just (MkProofState gs ctx)
    _                   => Nothing
decodeProofState _ = Nothing

-- ============================================================================
-- Section 13: E12 — Main theorem: ProofState serialization losslessness
-- ============================================================================

||| E12 — ProofState serialization losslessness.
|||
||| For any well-formed ProofState ps, decoding the encoding of ps returns
||| Just ps.  This is the formal statement of the round-trip property for
||| the ECHIDNA proof state.
|||
||| Proof:
|||   1. encodeProofState ps = Node "ProofState" [Node "goals" (encodeGoalList gs),
|||                                                Node "context" (encodeCtxList ctx)]
|||   2. decodeProofState matches the unique Node "ProofState" [...] pattern.
|||   3. goalListRoundtrip gs : decodeGoalList (encodeGoalList gs) = Just gs
|||   4. ctxListRoundtrip ctx : decodeCtxList (encodeCtxList ctx) = Just ctx
|||   5. Both sub-decoders return Just ⟹ Just (MkProofState gs ctx). QED.
|||
||| The proof is fully constructive: structural induction + rewriting.
||| Zero believe_me, zero sorry, zero assert_total.
public export
proofStateRoundtrip : (ps : ProofState)
                    -> decodeProofState (encodeProofState ps) = Just ps
proofStateRoundtrip (MkProofState gs ctx) =
  rewrite goalListRoundtrip gs in
  rewrite ctxListRoundtrip ctx in
  Refl

-- ============================================================================
-- Section 14: Serialisation record witnesses
-- ============================================================================

||| Certified serialisation scheme for Term over SExpr.
public export
termSerialisation : Serialisation Term SExpr
termSerialisation = MkSer
  { encode    = encodeTerm
  , decode    = decodeTerm
  , roundtrip = termRoundtrip
  }

||| Certified serialisation scheme for Goal over SExpr.
public export
goalSerialisation : Serialisation Goal SExpr
goalSerialisation = MkSer
  { encode    = encodeGoal
  , decode    = decodeGoal
  , roundtrip = goalRoundtrip
  }

||| Certified serialisation scheme for ProofState over SExpr.
|||
||| This is the primary deliverable of E12: a certified serialisation
||| scheme for ECHIDNA's core ProofState type.  The `roundtrip` field
||| is a constructive proof that no information is lost.
public export
proofStateSerialisation : Serialisation ProofState SExpr
proofStateSerialisation = MkSer
  { encode    = encodeProofState
  , decode    = decodeProofState
  , roundtrip = proofStateRoundtrip
  }

-- ============================================================================
-- Section 15: Corollaries
-- ============================================================================

||| Corollary: decodeProofState (encodeProofState ps) = Just ps.
||| Direct alias for proofStateRoundtrip, for documentation clarity.
public export
encodeDecodeJust : (ps : ProofState)
                 -> decodeProofState (encodeProofState ps) = Just ps
encodeDecodeJust = proofStateRoundtrip

||| Corollary: the encoding is injective.
|||
||| If two ProofStates have the same SExpr encoding, they are equal.
|||
||| Proof: from the round-trip property, decode is a left inverse of encode.
|||   encode ps1 = encode ps2
|||   ⟹  decode (encode ps1) = decode (encode ps2)    [cong decode]
|||   ⟹  Just ps1 = Just ps2                           [proofStateRoundtrip]
|||   ⟹  ps1 = ps2                                     [Just injective]
public export
encodeInjective : (ps1, ps2 : ProofState)
                -> encodeProofState ps1 = encodeProofState ps2
                -> ps1 = ps2
encodeInjective ps1 ps2 encodeEq =
  justInj (trans (sym (proofStateRoundtrip ps1))
                 (trans (cong decodeProofState encodeEq)
                        (proofStateRoundtrip ps2)))
  where
    ||| Injectivity of the Just constructor.
    justInj : {0 a : Type} -> {0 x, y : a} -> Just x = Just y -> x = y
    justInj Refl = Refl

||| Corollary: round-trip is stable for a flat list of goals drawn from
||| multiple ProofStates.  This witnesses that the batch-goals encoding
||| used in the wire layer inherits losslessness from goalListRoundtrip.
public export
batchGoalsRoundtrip : (pss : List ProofState)
                    -> let allGoals = concatMap (\ps => goals ps) pss
                       in  decodeGoalList (encodeGoalList allGoals) = Just allGoals
batchGoalsRoundtrip pss = goalListRoundtrip (concatMap (\ps => goals ps) pss)
