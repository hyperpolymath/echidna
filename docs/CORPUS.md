<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->

# Echidna Corpus — N-dimensional, octad-shaped, cross-prover

The corpus subsystem (`src/rust/corpus/`) is an N-dimensional index
over named declarations across multiple proof assistants, designed to
be the substrate for design-search, MCTS priors, and the
`suggest`/`learning` agentic surfaces. It also emits VeriSim-shaped
8-modality octads so the same data round-trips through the
`/api/v1/octads` endpoint.

> **For the design history** see
> [`docs/decisions/2026-04-28-corpus-and-design-search.md`](decisions/2026-04-28-corpus-and-design-search.md).

## What it is

Walks a project tree, parses every `*.agda` / `*.v` / `*.lean` /
`*.idr` file with adapter-specific heuristics, and produces:

- A list of **modules** (`ModuleEntry`) with options, imports, and
  back-references to their declarations.
- A list of **declarations** (`CorpusEntry`) with name, qualified
  name, kind, statement, optional proof body, source line,
  forward dependencies, and an `AxiomUsage` hazard flag set.
- Three indices: `by_name`, `by_qualified`, and **`dependents`**
  (reverse-dep — the inverse of `dependencies`). Reverse-deps answer
  "what proofs would break if I change `wf-<`?".
- A **per-entry metrics tensor** (`EntryMetrics`): size, connectivity,
  shape (recursive vs structural), hazards, K-elimination risk, head-
  symbol class.
- A **per-entry embedding** (`Vec<f32>`, default 32-dim hashing-trick;
  GNN backend pluggable via the `Embedder` trait).
- An **8-modality octad** (`DeclarationOctad`) form for VeriSim
  compatibility — semantic / temporal / provenance / document / graph
  / vector / tensor / spatial.

## Adapters

| Prover | File extension | Notes |
|---|---|---|
| Agda | `*.agda` | Module/options/imports/data/record/postulate-block/typesig+multi-clause body. Hazards: postulate, believe_me, assert_total, idris_crash. |
| Coq | `*.v` | `Theorem ... Qed./Defined./Admitted.`, `Definition`, `Fixpoint`, `Inductive`, `Record`, `Axiom`. Hazards: `Admitted`, `admit`, `Axiom`. |
| Lean 4 | `*.lean` | `def`/`theorem`/`lemma`/`inductive`/`structure`/`class`/`axiom`. Strips `@[…]` attributes + `private`/`protected`/`noncomputable`/etc. modifiers. Hazards: `sorry`, `admit`. |
| Idris 2 | `*.idr` | Same shape as Agda; `||| …` doc comments; `%foreign`/`%default`/`%hint` pragmas. Hazards: `believe_me`, `assert_total`, `assert_smaller`, `idris_crash`. |

## CLI

```bash
# Build an index
echidna corpus ingest --root <project> --adapter <agda|coq|lean|idris2>

# Query by name (qualified, short, or substring)
echidna corpus query <pattern> [--deps] [--reverse-deps] [--reverse-closure]

# Cosine-similarity nearest neighbours
echidna corpus near "<query text>" [--top N]

# Cross-prover semantic-class lookup (synonym table)
echidna corpus crossquery <semantic-class>

# Octad emit / round-trip
echidna corpus export-octads --index <X.json> --out <X.octads.jsonl>
echidna corpus import-octads --octads <X.octads.jsonl> --out <X.json>

# Stats
echidna corpus stats [--index <X.json>]
```

## Programmatic surface — the multi-axis query DSL

```rust
use echidna::corpus::{Corpus, DeclKind, query::SortKey};

let corpus = Corpus::load_json("data/corpus/echo-types.json")?;

// Recursive functions, axiom-free, sorted by similarity to a goal.
let hits = corpus.query()
    .where_kind(DeclKind::Function)
    .where_axiom_free()
    .where_recursive()
    .near_text("WellFounded _<_")
    .order_by(SortKey::Similarity)
    .limit(10)
    .run();

for hit in hits {
    println!(
        "{:.3}  {}  : {}",
        hit.similarity.unwrap_or(0.0),
        hit.entry.qualified,
        hit.entry.statement
    );
}
```

### Filter axes

| Method | What |
|---|---|
| `where_kind(K)` / `where_kind_in(&[K, …])` | Filter by `DeclKind` (Function/Data/Record/Postulate/Module). |
| `where_axiom_free()` | Exclude any hazard. |
| `where_no_hazards()` | Exclude hazards but keep declared `Postulate`s. |
| `where_recursive()` / `where_non_recursive()` | Self-reference detection from the proof body. |
| `where_structural()` | Constructor-pattern shape detection. |
| `where_name_contains(s)` / `where_qualified_contains(s)` | Substring filter. |
| `where_head_symbol(s)` | Exact match on the statement's first identifier. |
| `where_adapter(s)` | Restrict to one prover. |
| `where_has_reverse_deps()` | Non-leaf entries. |
| `where_custom(fn)` | Escape hatch — closure over `(&Entry, &Metrics)`. |

### Similarity (Vector octad)

| Method | What |
|---|---|
| `near_text("…")` | Embed via `HashEmbedder`, cosine-rank. |
| `near_vector(Vec<f32>)` | Pre-computed embedding (e.g. from a GNN). |

### Ordering (Tensor octad metrics)

`SortKey::{Default, Similarity, StatementSize, ProofDepth, Fanin, Fanout}`.

## File layout

```
src/rust/corpus/
├── mod.rs       # Corpus + CorpusEntry + ModuleEntry + DeclKind + AxiomUsage
├── agda.rs      # Agda adapter
├── coq.rs       # Coq adapter
├── lean.rs      # Lean 4 adapter
├── idris2.rs    # Idris 2 adapter
├── metrics.rs   # EntryMetrics tensor (Step 4)
├── embed.rs     # Embedder trait + HashEmbedder (Step 5)
├── octad.rs     # DeclarationOctad (8-modality, Step 3)
└── query.rs     # Multi-axis query DSL (capstone)

data/corpus/<basename>.json          # Local lossless index (gitignored)
data/corpus/<basename>.octads.jsonl  # 8-modality octad export

data/synonyms/<prover>.toml          # Tactic + lemma synonyms;
                                     # `semantic_class` field joins
                                     # entries across provers
```

## Octad shape

Each declaration becomes one `DeclarationOctad` with eight modalities
(see `corpus/octad.rs`):

| Modality | Carries |
|---|---|
| `semantic`  | adapter, kind, name, qualified, statement, proof |
| `document`  | searchable_text + aspect tags (incl. hazard tags) |
| `graph`     | depends_on + depended_on_by + cross_prover_id |
| `provenance`| SHA-256 hash chain over (parent, event, ts, file, line) |
| `spatial`   | file path + line + adapter namespace |
| `temporal`  | version chain — content_hash per rung |
| `tensor`    | EntryMetrics serialised as `HashMap<String, f64>` |
| `vector`    | embedding (default 32-dim HashEmbedder) |

`cross_prover_id` is SHA-256 of the qualified-name's *local tail*, so
`Foo.WellFounded` (Agda) and `Bar.WellFounded` (Coq) share an
identity — cross-prover joins fall out of the graph octad without
going through the synonym layer.

## Synonym table cross-prover joins

Each `data/synonyms/<prover>.toml` entry can carry a `semantic_class`
field. Entries with matching class — across any prover — are
considered equivalent under the same name:

```bash
$ echidna corpus crossquery well-foundedness
Agda:   WellFounded
Coq:    well_founded
Lean:   WellFounded
Idris2: WellFounded
4 entries across 4 prover(s) for semantic class 'well-foundedness'
```

Use cases:

- **`suggest`** can fall back to a peer-prover's name if the local
  one isn't found.
- **SA energy** can answer "is `osuc-mono` proved in *any* prover?"
  in one query.
- **Cross-prover proof exchange** (OpenTheory, Dedukti) consumes
  these classes when translating goals.

Currently seeded: `well-foundedness`, `accessibility`, `wf-induction`,
`wf-subrelation-transport`. More entries land alongside the proof
work that needs them.

## Limitations / known gaps

- **Adapter parsers are heuristic, not full grammars.** Coq's
  notation system, Lean 4's macros, Idris 2's mixfix all have edge
  cases the line/keyword approach misses. Verified against real
  fixtures; iterate as gaps surface.
- **Dependency edges store short names.** Cross-module name
  collisions widen reverse-closures (over-conservative, which is the
  safer side for impact analysis). Step 3's `cross_prover_id` and
  octad provenance can underwrite a follow-up content-addressed dep
  resolver.
- **Hashing-trick embeddings collide** at 32 dims on large corpora;
  swap in a GNN backend (`Embedder` trait) when the Julia ML
  pipeline is primed against real corpora.

## Verified end-to-end

| Repo | Adapter | Modules | Entries |
|---|---|---|---|
| `echo-types/proofs/agda` | agda | 57 | 640 |
| `echidna/proofs/coq` | coq | 5 | 108 |
| `jtv/jtv_proofs` | lean | 7 | 147 |
| `eclexia/src/abi` | idris2 | 4 | 93 |

1059 lib tests pass; 36 corpus-specific.
