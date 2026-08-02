<!--
SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Type-Discipline Embedding — 39-Discipline Corpus Annotation

**Status**: canonical. Companion to
`docs/architecture/VERISIM-ER-SCHEMA.md` and `docs/CORPUS-ADAPTERS.md`.
**Last revised**: 2026-06-01.
**Tier**: see `docs/PROVER_COUNT.md` Tier 9 ("TypeChecker disciplines").

## 1. Why this doc exists

The 2026-06-01 saturation campaign added 17 corpus adapters (see
`docs/CORPUS-ADAPTERS.md`). Every adapter emits `CorpusEntry` values
with a flat `DeclKind = {Function, Data, Record, Postulate, Module}`
(defined at `src/rust/corpus/mod.rs:53`). That flat tagging is
sufficient for hazard accounting but blind to the *type discipline*
each declaration belongs to.

The HP type-checker ecosystem distinguishes **39 type disciplines**,
each routed through TypedWasm Sigma parameters in `crates/typed_wasm`
and dispatched by `src/rust/provers/hp_ecosystem.rs:63-126`. This
document specifies how every CorpusEntry — regardless of which adapter
produced it — gains a `type_discipline_tags: Vec<TypeDiscipline>`
annotation so that:

1. cross-prover identity queries (E6 Rel-2 in
   `VERISIM-ER-SCHEMA.md`) can constrain by discipline,
2. the Julia GNN training pipeline (`src/julia/training/train.jl`)
   gets a 39-dim multi-hot feature vector per example, and
3. Panll and Katagoria consumers — neither of which has shipped — can
   read the tags as pre-computed type-checker hints rather than
   re-deriving them per-query.

Detection is heuristic, marker-based, and adapter-aware. Confidence is
the cumulative weight of matched markers; see §7.

## 2. The 39-discipline taxonomy

Ten families, 39 disciplines. Sigma parameter names match
`src/rust/disciplines/disciplines.rs::typell_sigma()` and the dispatch table
at `src/rust/provers/hp_ecosystem.rs:63-126`.

### 2.1 Polymorphism (7)

| Discipline | TypeLL Sigma | Canonical paper | Markers excerpt |
|---|---|---|---|
| hindley-milner | `HM` | Milner, "A Theory of Type Polymorphism in Programming" (1978) | `forall a.`, `let`-generalisation, `ML`-style polymorphism |
| system-f | `SF` | Reynolds, "Towards a Theory of Type Structure" (1974); Girard PhD (1972) | `Λ`, `Forall`, explicit type abstraction `/\` |
| rank-n | `RankN` | Peyton Jones et al., "Practical Type Inference for Arbitrary-Rank Types" (2007) | `forall` under arrow LHS, `RankNTypes` |
| phantom | `Phantom` | Leijen & Meijer, "Domain Specific Embedded Compilers" (1999) | unused type parameter on data decl, ghost `PhantomData` |
| existential | `Exist` | Mitchell & Plotkin, "Abstract Types Have Existential Type" (1988) | `exists`, `∃`, `pack`/`unpack`, `Sigma`-as-existential |
| higher-kinded | `HKT` | Jones, "A System of Constructor Classes" (1995) | `f : Type -> Type`, kind annotations beyond `*` |
| row-poly | `Row` | Wand, "Complete Type Inference for Simple Objects" (1987); Rémy (1989) | `{l : t \| r}`, row variables, extensible records |

### 2.2 Subtyping (4)

| Discipline | TypeLL Sigma | Canonical paper | Markers excerpt |
|---|---|---|---|
| subtyping | `Sub` | Cardelli, "A Semantics of Multiple Inheritance" (1984) | `<:`, `≤`, structural subsumption |
| intersection | `Int` | Coppo, Dezani-Ciancaglini & Venneri (1981) | `∩`, `&`, conjunctive types |
| union | `Uni` | Pierce, "Programming with Intersection Types, Union Types, and Polymorphism" (1991) | `∪`, `\|`, sum-as-untagged |
| gradual | `Gra` | Siek & Taha, "Gradual Typing for Functional Languages" (2006) | `?`, `dyn`, `Any` with consistency |

### 2.3 Dependent (5)

| Discipline | TypeLL Sigma | Canonical paper | Markers excerpt |
|---|---|---|---|
| dependent | `Dep` | Martin-Löf, "Intuitionistic Type Theory" (1984) | `(x : A) -> B x`, `Π`, `Pi` |
| refinement | `Ref` | Freeman & Pfenning, "Refinement Types for ML" (1991); Rondon et al. Liquid (2008) | `{v : t \| p v}`, `predicate`, `requires`/`ensures` |
| hoare | `Hoa` | Hoare, "An Axiomatic Basis for Computer Programming" (1969); Nanevski et al. HTT | `{P} c {Q}`, `Hoare ?st ?p ?q` |
| indexed | `Ind` | Zenger, "Indexed Types" (1997); Xi & Pfenning DML (1999) | `Vec n a`, type-level Nat indices |
| qtt | `QTT` | McBride, "I Got Plenty o' Nuttin'" (2016); Atkey, "Syntax and Semantics of Quantitative Type Theory" (2018) | `0 \|- t : T`, multiplicities `0 / 1 / ω` |

### 2.4 Substructural (5)

| Discipline | TypeLL Sigma | Canonical paper | Markers excerpt |
|---|---|---|---|
| linear | `Lin` | Wadler, "Linear Types Can Change the World!" (1990); Girard "Linear Logic" (1987) | `!`, `⊸`, `1` use exactly once |
| affine | `Aff` | TBD — fill from author (commonly cited: Walker, "Substructural Type Systems" in ATTAPL ch. 1, 2005) | at-most-once use, `Drop`, `move` semantics |
| relevant | `Rel` | TBD — fill from author (Walker ATTAPL ch. 1, 2005) | at-least-once use, mandatory consumption |
| ordered | `Ord` | Polakow & Pfenning, "Natural Deduction for Intuitionistic Non-commutative Linear Logic" (1999) | non-exchange contexts, sequence preservation |
| uniqueness | `Unq` | Barendsen & Smetsers, "Uniqueness Typing for Functional Languages" (1996) | Clean `*` annotation, unique-reference invariant |

### 2.5 Mutability / capability (3)

| Discipline | TypeLL Sigma | Canonical paper | Markers excerpt |
|---|---|---|---|
| immutable | `Imm` | TBD — fill from author | `const`, `final`, `readonly`, `val` |
| capability | `Cap` | Crary, Walker & Morrisett, "Typed Memory Management in a Calculus of Capabilities" (1999) | `cap`, capability sets, `acquire`/`release` |
| bunched | `Bun` | O'Hearn & Pym, "The Logic of Bunched Implications" (1999) | `*` (separating conjunction), `-*`, BI assertion |

### 2.6 Modal (4)

| Discipline | TypeLL Sigma | Canonical paper | Markers excerpt |
|---|---|---|---|
| modal | `Mod` | Pfenning & Davies, "A Judgmental Reconstruction of Modal Logic" (2001) | `□`, `◇`, `box`, `dia` |
| epistemic | `Epi` | Hintikka, "Knowledge and Belief" (1962); Fagin et al. (1995) | `K`, `K_i`, `knows`, agent indices |
| temporal | `Tem` | Pnueli, "The Temporal Logic of Programs" (1977) | `□`, `◇`, `next`, `until`, LTL/CTL operators |
| provability | `Prv` | Gödel, Löb; Boolos, "The Logic of Provability" (1993) | `Bew`, `Prov`, `□` as provability operator |

### 2.7 Effects / coeffects (4)

| Discipline | TypeLL Sigma | Canonical paper | Markers excerpt |
|---|---|---|---|
| effect-row | `ERow` | Leijen, "Type Directed Compilation of Row-Typed Algebraic Effects" (2017) | `<eff \| r>`, `effect E`, `handle` |
| impure | `Imp` | Wadler, "Comprehending Monads" (1990); Moggi (1989) | `IO`, `m a`, `do`-notation |
| coeffect | `Coef` | Petricek, Orchard & Mycroft, "Coeffects: Unified Static Analysis of Context-Dependence" (2014) | graded context, `[A]r`, resource grading |
| probabilistic | `Prob` | Borgström et al., "Measure Transformer Semantics for Bayesian Machine Learning" (2011) | `sample`, `observe`, distribution types |

### 2.8 Session / process (4)

| Discipline | TypeLL Sigma | Canonical paper | Markers excerpt |
|---|---|---|---|
| session | `Ses` | Honda, "Types for Dyadic Interaction" (1993); Honda, Vasconcelos & Kubo (1998) | `!T.S`, `?T.S`, `end`, channel session types |
| choreographic | `Cho` | Carbone, Honda & Yoshida, "Multiparty Asynchronous Session Types" (2008); Montesi PhD (2013) | global protocol, role indices `A -> B : t` |
| dyadic | `Dy` | echo-types (`hyperpolymath/echo-types`); see also Honda's "dyadic interaction" (1993) | `dyad`, `peer A B`, two-party protocol |
| echo | `Echo` | echo-types (`hyperpolymath/echo-types`) — TBD canonical paper; provisional spec in repo `docs/` | `echo`, `replay`, `obs A`, observational equivalence under echo |

### 2.9 Homotopy (3)

| Discipline | TypeLL Sigma | Canonical paper | Markers excerpt |
|---|---|---|---|
| homotopy | `Hom` | Univalent Foundations Program, "Homotopy Type Theory" (2013) | univalence axiom, `Path`, identity types as paths |
| cubical | `Cub` | Cohen, Coquand, Huber & Mörtberg, "Cubical Type Theory" (2018) | `Path`, `PathP`, `i0`/`i1`, interval `I` |
| nominal | `Nom` | Pitts, "Nominal Logic" (2001); Gabbay & Pitts (2002) | `name`, `swap`, `freshness ⊥`, `α`-equivalence |

### 2.10 Resource (2)

| Discipline | TypeLL Sigma | Canonical paper | Markers excerpt |
|---|---|---|---|
| tropical | `Trop` | tropical-resource-typing repo (`verification-ecosystem/tropical-resource-typing`); see also Speyer & Sturmfels (2009) for the algebra | tropical semiring `(min, +)`, resource cost annotations |
| ceremonial | `Cer` | Panll language spec (Panll = panll language) — TBD canonical paper; ceremonial sub-language doc in `panll/docs/` | `@[ceremony]`, `ritual`, ceremonial obligation markers |

## 3. Detection topology

```
Corpus adapter ingests *.<ext>
  → CorpusEntry { statement, proof, ... }       (src/rust/corpus/mod.rs:138)
    → detect_disciplines(adapter_name, statement, proof, registry)
                                                (src/rust/disciplines/detector.rs)
      → Vec<TypeDiscipline>                     (src/rust/disciplines/disciplines.rs)
        → CorpusEntry.type_discipline_tags
          → Octad SemanticPayload               (src/rust/verisim_bridge.rs)
            → VeriSimDB cross-prover identity index  (E6 in VERISIM-ER-SCHEMA.md)
            → Julia GNN training feature row    (src/julia/training/train.jl)
```

The detector is pure: same `(adapter, statement, proof, registry)` always
returns the same `Vec<TypeDiscipline>`. The registry
(`src/rust/disciplines/registry.rs::MarkerRegistry`) is built once at
process start from `data/synonyms/_disciplines.toml` plus the
per-language augmentations in each `data/synonyms/<adapter>.toml`.

## 4. Per-adapter coverage matrix

The 17 saturation-campaign adapters × 10 discipline families. `✓` means
the adapter routinely surfaces declarations in that family; `partial`
means only via specific idioms; `—` means the family is essentially
absent from typical sources for that adapter.

### 4.1 Polymorphism, Subtyping (sub-table 1 of 4)

| Adapter | HM | SF | RankN | Phantom | Exist | HKT | Row | Sub | Int | Uni | Gra |
|---|---|---|---|---|---|---|---|---|---|---|---|
| agda | ✓ | ✓ | ✓ | partial | ✓ | ✓ | — | — | — | — | — |
| coq | partial | ✓ | ✓ | partial | ✓ | ✓ | — | partial | — | — | — |
| lean | partial | ✓ | ✓ | partial | ✓ | ✓ | — | partial | — | — | — |
| idris2 | ✓ | ✓ | ✓ | partial | ✓ | ✓ | — | — | — | — | — |
| isabelle | ✓ | partial | — | partial | partial | partial | — | partial | — | — | — |
| metamath | — | — | — | — | — | — | — | — | — | — | — |
| mizar | — | — | — | — | — | — | — | partial | — | — | — |
| hol_light | ✓ | partial | — | partial | — | — | — | — | — | — | — |
| hol4 | ✓ | partial | — | partial | — | — | — | — | — | — | — |
| dafny | partial | — | — | partial | — | — | — | ✓ | — | — | — |
| why3 | ✓ | partial | — | partial | — | partial | — | partial | — | — | — |
| fstar | ✓ | ✓ | ✓ | partial | ✓ | partial | — | partial | — | — | — |
| acl2_books | — | — | — | — | — | — | — | — | — | — | — |
| tptp | — | partial | — | — | partial | — | — | — | — | — | — |
| smtlib | — | — | — | — | — | — | — | partial | — | — | — |
| proofnet | partial | partial | — | — | partial | — | — | — | — | — | — |
| minif2f | partial | partial | — | — | partial | — | — | — | — | — | — |

### 4.2 Dependent, Substructural (sub-table 2 of 4)

| Adapter | Dep | Ref | Hoa | Ind | QTT | Lin | Aff | Rel | Ord | Unq |
|---|---|---|---|---|---|---|---|---|---|---|
| agda | ✓ | partial | — | ✓ | — | ✓ | ✓ | — | — | — |
| coq | ✓ | partial | partial | ✓ | — | partial | partial | — | — | — |
| lean | ✓ | partial | partial | ✓ | — | partial | partial | — | — | — |
| idris2 | ✓ | partial | — | ✓ | ✓ | ✓ | ✓ | — | — | partial |
| isabelle | partial | — | ✓ | partial | — | — | — | — | — | — |
| metamath | — | — | — | — | — | — | — | — | — | — |
| mizar | partial | — | — | — | — | — | — | — | — | — |
| hol_light | — | — | partial | — | — | — | — | — | — | — |
| hol4 | — | — | partial | — | — | — | — | — | — | — |
| dafny | partial | ✓ | ✓ | partial | — | — | — | — | — | — |
| why3 | partial | ✓ | ✓ | partial | — | — | — | — | — | — |
| fstar | ✓ | ✓ | ✓ | ✓ | — | partial | partial | — | — | — |
| acl2_books | — | — | — | — | — | — | — | — | — | — |
| tptp | partial | — | — | — | — | — | — | — | — | — |
| smtlib | — | — | — | — | — | — | — | — | — | — |
| proofnet | partial | partial | partial | partial | — | — | — | — | — | — |
| minif2f | partial | partial | partial | partial | — | — | — | — | — | — |

### 4.3 Mutability, Modal, Effects (sub-table 3 of 4)

| Adapter | Imm | Cap | Bun | Mod | Epi | Tem | Prv | ERow | Imp | Coef | Prob |
|---|---|---|---|---|---|---|---|---|---|---|---|
| agda | — | — | — | partial | — | — | — | — | partial | — | — |
| coq | — | — | partial | partial | — | partial | partial | — | partial | — | — |
| lean | — | — | — | partial | — | partial | partial | — | partial | — | — |
| idris2 | — | — | — | — | — | — | — | partial | partial | — | — |
| isabelle | — | — | — | partial | partial | ✓ | partial | — | — | — | partial |
| metamath | — | — | — | partial | — | — | partial | — | — | — | — |
| mizar | — | — | — | — | — | — | — | — | — | — | — |
| hol_light | — | — | — | partial | — | partial | partial | — | — | — | — |
| hol4 | — | — | — | partial | — | partial | partial | — | — | — | — |
| dafny | ✓ | ✓ | partial | — | — | — | — | — | ✓ | — | — |
| why3 | partial | — | — | — | — | — | — | — | ✓ | — | — |
| fstar | partial | partial | partial | — | — | — | — | ✓ | ✓ | — | partial |
| acl2_books | — | — | — | — | — | partial | — | — | — | — | — |
| tptp | — | — | — | partial | partial | partial | — | — | — | — | — |
| smtlib | — | — | — | — | — | partial | — | — | — | — | — |
| proofnet | — | — | — | partial | — | — | — | — | partial | — | — |
| minif2f | — | — | — | partial | — | — | — | — | partial | — | — |

### 4.4 Session, Homotopy, Resource (sub-table 4 of 4)

| Adapter | Ses | Cho | Dy | Echo | Hom | Cub | Nom | Trop | Cer |
|---|---|---|---|---|---|---|---|---|---|
| agda | — | — | — | — | ✓ | ✓ | — | — | — |
| coq | — | — | — | — | partial | — | partial | — | — |
| lean | — | — | — | — | partial | — | — | — | — |
| idris2 | — | — | — | — | — | — | — | — | — |
| isabelle | — | — | — | — | — | — | partial | — | — |
| metamath | — | — | — | — | — | — | — | — | — |
| mizar | — | — | — | — | — | — | — | — | — |
| hol_light | — | — | — | — | — | — | — | — | — |
| hol4 | — | — | — | — | — | — | — | — | — |
| dafny | — | — | — | — | — | — | — | — | — |
| why3 | — | — | — | — | — | — | — | — | — |
| fstar | — | — | — | — | — | — | — | — | — |
| acl2_books | — | — | — | — | — | — | — | — | — |
| tptp | — | — | — | — | — | — | — | — | — |
| smtlib | — | — | — | — | — | — | — | — | — |
| proofnet | partial | — | — | — | partial | partial | — | — | — |
| minif2f | — | — | — | — | partial | partial | — | — | — |

Cells are best-effort priors based on typical mathlib4 / stdlib /
AFP / mizar-mml content. The detector returns whatever markers fire,
so a `partial`-marked cell can still produce real tags when the
specific declaration uses the relevant idiom; the matrix only
documents expected hit frequency for triage.

## 5. Crosswalk to TypeLL / Katagoria / VCL-UT / Panll

### 5.1 TypeLL

Each `TypeDiscipline` variant has a Sigma parameter name returned by
`src/rust/disciplines/disciplines.rs::typell_sigma()`. The Sigma names are
single-token strings (`"HM"`, `"SF"`, `"Lin"`, `"Aff"`, `"Dep"`,
`"QTT"`, `"Echo"`, `"Cub"`, `"Trop"`, `"Cer"`, …) and exactly match
the discipline tag passed to `typell --discipline=<tag>` by
`src/rust/provers/hp_ecosystem.rs:63-126`. The Sigma table is the
single source of truth for the discipline ↔ CLI mapping; this
document does not re-list it.

### 5.2 Katagoria

Katagoria (`hyperpolymath/katagoria`, dispatched as
`ProverKind::KatagoriaVerifier` at
`src/rust/provers/hp_ecosystem.rs:66`) reserves invariant slots
keyed by discipline tag. The intended mapping — which tags populate
which Katagoria invariant slots — is **TBD — needs Katagoria spec
audit**. Until then, the detector emits the tag and Katagoria
consumers ignore unknown tags.

### 5.3 VCL-UT

VCL-UT (`src/rust/vcl_ut.rs:1-1083`) already exposes a 10-level
`TypeLevel` safety annotation. Discipline tags are orthogonal: a
VCL-UT query can additionally constrain by discipline, e.g.

```text
select octad
where_discipline(TypeDiscipline::Linear)
where type_level >= TypeLevel::L7
```

The VCL-UT planner pushes the discipline filter down to the
`octads_semantic` materialised view (E2 in `VERISIM-ER-SCHEMA.md`),
which indexes on the new `type_discipline_tags` array column.

### 5.4 Panll

Panll's type system is the union of all 39 disciplines plus
cross-discipline composition operators (per the
`panll/docs/type-system/` design notes). Discipline tags are
**pre-Panll annotation**: they are computed by adapters that pre-date
the Panll compiler, stored in VeriSimDB, and consumed downstream once
Panll lands. The contract is:

- adapters MUST emit tags they detect, even if Panll cannot yet
  consume them;
- Panll's compiler, when it ships, MUST read `type_discipline_tags`
  as hints (not authoritative) and may refine or extend the set.

## 6. Wire schema impact

The `SemanticPayload` struct in `src/rust/verisim_bridge.rs` gains a
new field:

```rust
pub struct SemanticPayload {
    // ...existing fields...
    pub type_discipline_tags: Vec<String>, // kebab-case slugs
}
```

The slugs are the canonical discipline names from §2 (e.g.
`"hindley-milner"`, `"linear"`, `"echo"`, `"tropical"`).

The Cap'n Proto schema at
`crates/echidna-wire/schemas/verisim_er.capnp` adds field 11 on the
`Semantic` struct:

```capnp
struct Semantic {
    # ...fields @0..@10 unchanged...
    typeDisciplineTags @11 :List(Text);
}
```

VeriSimDB stores this as an `Array(LowCardinality(String))` column on
the `octads_semantic` table, with a secondary skip index for
discipline-filtered queries. The drift-detection SHA in §"Drift
detection" of `VERISIM-ER-SCHEMA.md` MUST be re-computed when this
field lands.

## 7. Detection confidence

The detector is heuristic; tags are emitted when cumulative marker
score for a discipline exceeds 0.7. Marker entries in
`MarkerRegistry` have shape:

```rust
pub struct Marker {
    pub pattern: String,       // literal string or regex (compiled lazily)
    pub discipline: TypeDiscipline,
    pub weight: f64,           // 0.0..1.0
    pub adapters: &'static [&'static str], // empty == language-agnostic
}
```

- **HIGH-confidence markers** like `@[ceremony]` are unambiguous —
  weight 0.95. A single occurrence crosses the 0.7 threshold.
- **MEDIUM-confidence markers** like `forall` need corroborating
  evidence (e.g. a type variable in scope) before they tag
  System F or Rank-N. Typical weight 0.45–0.6.
- **LOW-confidence markers** like `!` (which could be linear-logic
  exponential, boolean negation, factorial, or Haskell strictness)
  carry weight 0.2 and require multiple co-occurring markers to fire.

The `adapters` slice scopes a marker: `adapters: &[]` (empty) means
the marker is language-agnostic; `adapters: &["lean"]` restricts it
to Lean sources only. This matters because `!` means "linear bang" in
Linear Logic encodings but "decide" in Lean tactic scripts.

## 8. Per-discipline owner-direction status

Status of the nine disciplines the owner explicitly called out during
campaign scoping:

- **linear**: ✓ detector + markers + synonyms shipped
  (`data/synonyms/_disciplines.toml::[linear]`).
- **affine**: ✓ ditto. Cross-references the Rust borrow-checker
  vocabulary (`move`, `Copy`, `Drop`) used in `idaptik` corpus.
- **dependent**: ✓ ditto. Routes through `DependentTypeChecker`
  (`src/rust/provers/hp_ecosystem.rs:75`).
- **equality**: ✓ as part of subtyping/dependent; markers `=`, `≡`,
  `==`, propositional-equality (`Path`, `Id`, `eq`). Not a standalone
  Sigma; surfaces under `Dep` or `Hom` depending on context.
- **ceremonial**: ✓ markers shipped (`@[ceremony]`, `ritual`,
  ceremonial-obligation slugs). Detector may need expansion as Panll's
  ceremonial sub-language stabilises.
- **dyadic**: ✓ from echo-types (`hyperpolymath/echo-types`); routes
  through `DyadicTypeChecker`
  (`src/rust/provers/hp_ecosystem.rs:111`).
- **tropical**: ✓ from tropical-resource-typing repo; routes through
  `TropicalTypeChecker` (`src/rust/provers/hp_ecosystem.rs:67`).
- **choreographic**: ✓ markers shipped (global-protocol syntax,
  multi-role declarations); routes through
  `ChoreographicTypeChecker` (`src/rust/provers/hp_ecosystem.rs:68`).
- **epistemic**: ✓ markers shipped (`K`, `K_i`, `knows`); routes
  through `EpistemicTypeChecker`
  (`src/rust/provers/hp_ecosystem.rs:69`).

## 9. Integration with the GNN training pipeline

The `type_discipline_tags` field flows from CorpusEntry → octad
emission → Julia corpus loader → training example:

```
CorpusEntry.type_discipline_tags
  → SemanticPayload.type_discipline_tags         (verisim_bridge.rs)
  → octads_semantic.type_discipline_tags         (VeriSimDB column)
  → premises_<adapter>.jsonl                     (corpus-emit CLI)
  → src/julia/training/corpus_loader.jl          (reads JSONL)
  → TrainingExample.discipline_features          (39-dim multi-hot)
  → train.jl                                     (consumes both heads)
```

Two heads:

- **Value head**: discipline tags are concatenated as a 39-dim
  multi-hot vector and fed to the value-prediction MLP. Disciplines
  that imply harder goals (Dep, QTT, Cub) shift the value prior down;
  the model learns the offsets.
- **Policy head**: discipline tags constrain candidate tactics. For a
  `Linear`-tagged goal, the policy head prefers tactics that respect
  linearity (no duplication, no discarding). The constraint is a soft
  prior implemented as a logit bias in the tactic-ranking softmax —
  see the GNN service in `src/julia/server/gnn_api.jl`.

## 10. Open follow-ups

- **T1** — wire `type_discipline_tags` into `CorpusEntry` serde so
  every adapter's emit path populates the field.
- **T2** — each per-language detector gets adapter-aware refinement
  beyond plain text-matching (e.g. AST-walking the Coq term for
  `Π`-binders rather than regexing the source).
- **T3** — Cap'n Proto schema delta on `Semantic @11`.
- **T4** — `src/julia/training/corpus_loader.jl` pass-through of the
  39-dim feature.
- **T5** — cross-reference echo-types repo
  (`hyperpolymath/echo-types`) for the canonical Echo / Dyadic marker
  set; audit pending. Per the standing
  "[Proofs MUST check + cross-doc echo-types]" directive, every
  Echo/Dyadic marker addition MUST first audit echo-types and reuse
  if applicable, extend upstream WITH proofs if not.
- **T6** — Katagoria invariant-slot mapping (§5.2) needs spec audit.
- **T7** — Panll's compiler integration once it lands (§5.4).

## 11. References

- `src/rust/disciplines/disciplines.rs` — the `TypeDiscipline` enum and
  `typell_sigma()` mapping.
- `src/rust/disciplines/registry.rs` — the `MarkerRegistry`.
- `src/rust/disciplines/detector.rs` — the `detect_disciplines` entry
  point.
- `data/synonyms/_disciplines.toml` — the cross-prover discipline
  vocabulary.
- `docs/architecture/VERISIM-ER-SCHEMA.md` — E2 Semantic modality
  target (this doc adds field `@11`).
- `crates/echidna-wire/schemas/verisim_er.capnp` — wire schema
  (pending field-11 delta per T3).
- `crates/typed_wasm/src/lib.rs` — Sigma parameter routing target.
- `src/rust/provers/hp_ecosystem.rs:63-126` — 39-discipline dispatch
  table.
- `docs/PROVER_COUNT.md` Tier 9 — the canonical tier table.
- `docs/CORPUS-ADAPTERS.md` — adapter inventory consumed by §4.
