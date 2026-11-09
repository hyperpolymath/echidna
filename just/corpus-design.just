# SPDX-License-Identifier: MPL-2.0
# Imported by the root Justfile (hotspot split); recipes moved verbatim.

# ────────────────────────────────────────────────────────────────────
# Corpus + design-search (added 2026-04-28)
# ────────────────────────────────────────────────────────────────────

# Ingest an Agda project into the corpus
corpus-ingest-agda root:
    cargo run --bin echidna -- corpus ingest --root {{root}} --adapter agda

# Ingest a Coq project into the corpus
corpus-ingest-coq root:
    cargo run --bin echidna -- corpus ingest --root {{root}} --adapter coq

# Ingest a Lean 4 project into the corpus
corpus-ingest-lean root:
    cargo run --bin echidna -- corpus ingest --root {{root}} --adapter lean

# Ingest an Idris 2 project into the corpus
corpus-ingest-idris root:
    cargo run --bin echidna -- corpus ingest --root {{root}} --adapter idris2

# Query the corpus by name with full reverse-dep impact set
corpus-impact name index="data/corpus/agda.json":
    cargo run --bin echidna -- corpus query "{{name}}" --index {{index}} --reverse-closure

# Cosine-similarity nearest-neighbour query
corpus-near query index="data/corpus/agda.json" top="10":
    cargo run --bin echidna -- corpus near "{{query}}" --index {{index}} --top {{top}}

# Cross-prover semantic-class lookup
corpus-cross class:
    cargo run --bin echidna -- corpus crossquery {{class}}

# Export a JSON index as 8-modality octad JSONL (VeriSim-compatible)
corpus-octads in="data/corpus/agda.json" out="data/corpus/agda.octads.jsonl":
    cargo run --bin echidna -- corpus export-octads --index {{in}} --out {{out}}

# Run the SA design-search on a named problem
design-search problem="brouwer-leq" iterations="2000" top="10":
    cargo run --bin echidna -- design search {{problem}} --iterations {{iterations}} --top {{top}}

# Run the parallel-swarm design-search
design-swarm problem="brouwer-leq" agents="4" iterations="800":
    cargo run --bin echidna -- design swarm {{problem}} --agents {{agents}} --iterations {{iterations}} --broadcast-every 50
