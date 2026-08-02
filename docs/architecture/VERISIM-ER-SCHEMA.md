<!--
SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
SPDX-License-Identifier: CC-BY-SA-4.0
-->

# VeriSim ↔ ECHIDNA Entity-Relationship Schema

**Status**: canonical. Replaces the aspirational text in
`docs/design/ECHIDNA-VERISIM-TRIANGULATION-2026-04-17.adoc` as the
formal data-model spec.
**Last revised**: 2026-06-01.
**Companion**: `crates/echidna-wire/schemas/verisim_er.capnp` (wire format).

## Why a formal E-R now

The 2026-04-17 triangulation document described the *workflow* for
absorbing 41 provers across 4 phases. It did NOT define the entities
themselves. Implementation drift was easy: the Rust octad payload in
`src/rust/verisim_bridge.rs` carries 8 modalities, but the
ClickHouse / VeriSimDB store at the other end uses 11 tables (per the
VeriSimDB README) — what maps to what was implicit.

This document closes the gap. Every entity has:

- a Rust struct it implements,
- a VeriSimDB table it stores in,
- a Cap'n Proto schema it serialises through (where wire-level
  contracts apply), and
- a primary key + foreign-key set.

Diagram drift is detected by a single hash over this file plus the
`.capnp` schema; mismatches are blocked by the per-PR `er-drift` CI
gate (TODO — track in `docs/decisions/2026-06-01-er-drift-gate.md`).

## Entity inventory

There are **12 first-class entities** and **7 first-class relationships**.

### E1 — `Octad`

A snapshot of one declaration (theorem / lemma / definition / axiom)
at one moment in time, with all 8 modalities populated.

| Field | Type | Source of truth |
|---|---|---|
| `key` (PK) | `UUIDv7` | Generated client-side at builder time |
| `created_at` | `Timestamp` | Auto-set on insert |
| `adapter` | `String` (`"agda"`/`"coq"`/…/`"metamath"`/`"mizar"`/`"tptp"`/`"smtlib"`/`"proofnet"`/`"minif2f"`) | `Corpus.adapter` |
| `module_qualified` | `String` | `CorpusEntry.qualified` |

Rust: `src/rust/verisim_bridge.rs::OctadPayload`
Cap'n Proto: `verisim_er.capnp::Octad` (struct id `@0x80…001`)
VeriSimDB table: `octads`
Implementation status: **complete**.

### E2 — `SemanticModality`

The textual / structural content of the declaration.

| Field | Type | Notes |
|---|---|---|
| `octad_key` (PK,FK→E1) | `UUIDv7` | one-to-one with Octad |
| `kind` | enum `Function`/`Data`/`Record`/`Postulate`/`Module` | `DeclKind` from `src/rust/corpus/mod.rs:53` |
| `name` | `String` | local name |
| `statement` | `String` | type signature |
| `proof` | `Option<String>` | proof body — None for postulates |

Rust: `OctadPayload.semantic`
Cap'n Proto: `verisim_er.capnp::Semantic`
VeriSimDB table: `octads_semantic`

### E3 — `TemporalModality`

Version chain across edits, refactorings, rename events.

| Field | Type | Notes |
|---|---|---|
| `octad_key` (PK,FK→E1) | `UUIDv7` | |
| `versions` | `List<VersionEntry>` | each entry: timestamp, change_kind, parent_key |
| `parent_octad_key` | `Option<UUIDv7>` | self-FK: previous version of this declaration |

Rust: `OctadPayload.temporal`
VeriSimDB table: `octads_temporal`
Foreign-key cycle: `temporal.parent_octad_key → octads.key` (self).

### E4 — `ProvenanceModality`

Hash chain for replay + audit (who ingested when from where).

| Field | Type | Notes |
|---|---|---|
| `octad_key` (PK,FK→E1) | `UUIDv7` | |
| `source_hash` | `String` (SHA-256 hex) | hash of the originating source file |
| `ingest_actor` | `String` | who/what ran the ingest (CI job ID, user agent) |
| `ingest_ts` | `Timestamp` | |
| `chain_prev_hash` | `Option<String>` | previous link in chain |

Rust: `OctadPayload.provenance`
VeriSimDB table: `octads_provenance`

### E5 — `DocumentModality`

Full-text searchable representation (for `near_text` queries).

| Field | Type | Notes |
|---|---|---|
| `octad_key` (PK,FK→E1) | `UUIDv7` | |
| `searchable_text` | `String` | name + statement + proof + aspects, lowercased |
| `aspects` | `List<String>` | aspect tags (`induction`, `well-founded`, …) |

Rust: `OctadPayload.document`
VeriSimDB table: `octads_document`
Indexed by: Tantivy full-text index on `searchable_text`.

### E6 — `GraphModality`

Dependency edges + cross-prover identity edges.

| Field | Type | Notes |
|---|---|---|
| `octad_key` (PK,FK→E1) | `UUIDv7` | |
| `depends_on` | `List<UUIDv7>` | forward deps |
| `depended_on_by` | `List<UUIDv7>` | reverse deps |
| `cross_prover_identity_key` | `String` | groups Octads representing the SAME mathematical object across adapters — see Rel-2 below |

Rust: `OctadPayload.graph`
VeriSimDB table: `octads_graph`
Indexed by: `cross_prover_identity_key` (HNSW for fuzzy match, exact for direct).

### E7 — `VectorModality`

Goal embeddings for `near_text` and GNN-guided search.

| Field | Type | Notes |
|---|---|---|
| `octad_key` (PK,FK→E1) | `UUIDv7` | |
| `goal_embedding` | `List<f32>` | currently 32-dim HashEmbedder, future 256-dim GNN |
| `embedder` | `String` (`"hash-v1"`/`"gnn-v1"`) | versioning |

Rust: `OctadPayload.vector`
VeriSimDB table: `octads_vector`
Indexed by: HNSW on `goal_embedding`.

### E8 — `TensorModality`

Numeric metrics over the declaration (proof depth, AST size, hazard
flag bitmap, …).

| Field | Type | Notes |
|---|---|---|
| `octad_key` (PK,FK→E1) | `UUIDv7` | |
| `proof_depth` | `u32` | tactic nesting depth |
| `statement_size_tokens` | `u32` | |
| `hazard_bitmap` | `u32` | postulate / believe_me / admit / sorry / trustme / other |
| `axiom_count` | `u32` | declared axioms touched |

Rust: `OctadPayload.tensor`
VeriSimDB table: `octads_tensor`

### E9 — `SpatialModality`

File path + line number in the originating source tree.

| Field | Type | Notes |
|---|---|---|
| `octad_key` (PK,FK→E1) | `UUIDv7` | |
| `file_path` | `String` | relative to corpus root |
| `line` | `u32` | 1-based |
| `column` | `Option<u32>` | optional column start |

Rust: `OctadPayload.spatial`
VeriSimDB table: `octads_spatial`

### E10 — `ProofAttempt`

A single invocation of a prover backend against a goal.

| Field | Type | Notes |
|---|---|---|
| `attempt_id` (PK) | `UUIDv7` | |
| `octad_key` (FK→E1) | `UUIDv7` | the goal |
| `prover` | enum `ProverKind` | which of the 128 backends |
| `verdict` | enum `Proven`/`Refuted`/`Timeout`/`Unknown`/`Error` | outcome |
| `started_at` | `Timestamp` | |
| `latency_ms` | `u64` | wall-clock |
| `axiom_cost` | `u32` | declared axioms used (input to E16) |
| `certificate_blob_key` | `Option<String>` | pointer into E11 |
| `confidence_self_reported` | `Option<f64>` | when the backend self-rates |

Rust: `src/rust/verisim_bridge.rs::ProofAttempt`
VeriSimDB table: `proof_attempts`

### E11 — `CertificateBlob`

Raw proof certificate produced by the backend (Alethe, DRAT/LRAT,
TSTP, OpenTheory, Dedukti, Lambdapi).

| Field | Type | Notes |
|---|---|---|
| `blob_key` (PK) | `String` (SHAKE3-512 hex of contents) | content-addressed |
| `format` | enum `Alethe`/`Drat`/`Lrat`/`Tstp`/`OpenTheory`/`Dedukti`/`Lambdapi`/`SmtCoq`/`Other` | exchange format |
| `bytes` | `Bytes` | raw certificate |
| `created_at` | `Timestamp` | |

Rust: TBD — currently inlined in `ProofAttempt.certificate_path`. **Migration entry**: extract to dedicated table 2026-Q3.
VeriSimDB table: `certificate_blobs`

### E12 — `ProverBinaryIntegrity`

Hash-pinned identity of the binary that produced an attempt.

| Field | Type | Notes |
|---|---|---|
| `prover` (PK part 1) | enum `ProverKind` | |
| `binary_hash` (PK part 2) | `String` (SHAKE3-512 + BLAKE3) | dual-hash |
| `version_label` | `String` | `"z3-4.13.0-ubuntu22-x64"` etc. |
| `first_seen_ts` | `Timestamp` | |

Rust: `src/rust/integrity/solver_integrity.rs`
VeriSimDB table: `prover_binary_integrity`

## Relationship inventory

### Rel-1 — `Octad has-modalities` (composition)

`Octad (1) — (1) {Semantic, Temporal, Provenance, Document, Graph,
Vector, Tensor, Spatial}`

Composition. Deleting an Octad cascades all modality rows.
Each modality table holds at most one row per octad_key.

### Rel-2 — `Cross-prover identity` (many-to-many self-relation on E1)

`Octad (M) ←→ (N) Octad` keyed by `GraphModality.cross_prover_identity_key`.

Semantics: two Octads `o1`, `o2` are *cross-prover-identified*
iff `o1.graph.cross_prover_identity_key == o2.graph.cross_prover_identity_key`
AND they have distinct adapters. Example: the Coq `Nat.add_comm` and
the Lean `Nat.add_comm` both carry identity key
`"nat-add-commutativity"`. Used to answer queries like *"every prover
that has formalised theorem X"*.

Materialised view: `cross_prover_clusters` in VeriSimDB.

### Rel-3 — `ProofAttempt of Octad`

`ProofAttempt (M) → (1) Octad`

A single Octad accumulates many ProofAttempts (one per prover × time).
The attempt FK enables the `query_prover_success_by_class` analytic.

### Rel-4 — `ProofAttempt produces CertificateBlob`

`ProofAttempt (1) → (0..1) CertificateBlob`

Optional: only some backends emit machine-checkable certificates.
Cardinality is 0..1 because failed attempts produce no blob.

### Rel-5 — `ProofAttempt runs ProverBinaryIntegrity`

`ProofAttempt (M) → (1) ProverBinaryIntegrity`

Every attempt links to the exact binary that ran. Enables replay:
"reproduce attempt X" = fetch the binary at this hash + re-run.

### Rel-6 — `Octad depends-on Octad` (DAG)

`Octad (M) → (N) Octad` keyed by `GraphModality.depends_on`.

Forward-dep edges. Transitively walked by `Corpus::closure`. The
reverse edges in `depended_on_by` are computed by `Corpus::reindex`
and stored materialised in `octads_graph` for query speed.

### Rel-7 — `Octad evolved-from Octad` (linear chain)

`Octad (1) → (0..1) Octad` keyed by `TemporalModality.parent_octad_key`.

The version chain. Used to answer "what did this theorem look like
before refactor X?". Stored as a singly-linked list — chain head has
`parent_octad_key == None`.

## ENTITY ↔ STRUCT ↔ TABLE crosswalk

| Entity | Rust struct | Cap'n Proto | ClickHouse table |
|---|---|---|---|
| E1 Octad | `OctadPayload` | `Octad@0x80…001` | `octads` |
| E2 Semantic | `SemanticPayload` | `Semantic@0x80…002` | `octads_semantic` |
| E3 Temporal | `TemporalPayload` | `Temporal@0x80…003` | `octads_temporal` |
| E4 Provenance | `ProvenancePayload` | `Provenance@0x80…004` | `octads_provenance` |
| E5 Document | `DocumentPayload` | `Document@0x80…005` | `octads_document` |
| E6 Graph | `GraphPayload` | `Graph@0x80…006` | `octads_graph` |
| E7 Vector | `VectorPayload` | `Vector@0x80…007` | `octads_vector` |
| E8 Tensor | `TensorPayload` | `Tensor@0x80…008` | `octads_tensor` |
| E9 Spatial | `SpatialPayload` | `Spatial@0x80…009` | `octads_spatial` |
| E10 ProofAttempt | `ProofAttempt` | `ProofAttempt@0x80…00a` | `proof_attempts` |
| E11 CertificateBlob | (extract pending) | `CertificateBlob@0x80…00b` | `certificate_blobs` |
| E12 ProverBinaryIntegrity | `ProverBinaryIntegrity` | `ProverBinaryIntegrity@0x80…00c` | `prover_binary_integrity` |

## Drift detection

The single source of truth is this document plus its companion
`verisim_er.capnp` schema. Any code change that adds, removes, or
renames an entity / relationship MUST also update both files in the
same PR. A CI gate (TODO: `er-drift.yml`) computes:

```
sha256( cat docs/architecture/VERISIM-ER-SCHEMA.md
        crates/echidna-wire/schemas/verisim_er.capnp )
```

and fails the build if the result differs from the value stored in
`.machine_readable/er-schema.sha256`. When the schema changes
intentionally, update the SHA in the same PR.

## Open migrations (tracked here, not in CHANGELOG)

| Item | Status |
|---|---|
| Extract `CertificateBlob` to dedicated table (currently inlined) | tracked, 2026-Q3 |
| Add `er-drift.yml` CI gate | tracked, see `docs/decisions/2026-06-01-er-drift-gate.md` |
| Cap'n Proto schema concrete struct IDs (placeholder `@0x80…001` etc.) | tracked, fill before first wire-level consumer |
| Migrate `query.rs` to span multiple adapters (currently single-adapter) | tracked, see capstone in `src/rust/corpus/query.rs` |
| VeriSim-side: ensure all 12 entities have writers + readers (currently 10/12 — E11 + E12 deferred) | tracked at verisimdb#XX |

## Cross-document references

- Octad implementation: `src/rust/verisim_bridge.rs:36-471`
- VCL-UT query language: `src/rust/vcl_ut.rs:1-1083` (consumer of this schema)
- Learning data flow: `docs/LEARNING-ARCHITECTURE.adoc` (consumer of `proof_attempts`)
- Arbitration: `src/rust/verification/{portfolio,bayesian_arbiter,dempster_shafer,pareto_arbiter}.rs` (consumers of `proof_attempts`)
- Corpus adapters: `src/rust/corpus/{agda,coq,lean,idris2,isabelle,metamath,mizar,hol_light,hol4,dafny,why3,fstar,acl2_books,tptp,smtlib,proofnet,minif2f}.rs` (producers of E1–E9)
