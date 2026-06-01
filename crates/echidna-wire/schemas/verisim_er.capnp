# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-License-Identifier: MPL-2.0
#
# VeriSim ↔ ECHIDNA E-R schema (wire format).
# Companion to docs/architecture/VERISIM-ER-SCHEMA.md.

@0xe4dc7b1f01a06001;

using Common = import "common.capnp";

# --- E1 — Octad ---
struct Octad {
  key              @0  :Text;             # UUIDv7
  createdAt        @1  :UInt64;           # epoch millis
  adapter          @2  :Text;             # "agda" / "coq" / "lean" / "idris2" / "isabelle" / "metamath" / "mizar" / "hol_light" / "hol4" / "dafny" / "why3" / "fstar" / "acl2_books" / "tptp" / "smtlib" / "proofnet" / "minif2f"
  moduleQualified  @3  :Text;             # CorpusEntry.qualified
  semantic         @4  :Semantic;
  temporal         @5  :Temporal;
  provenance       @6  :Provenance;
  document         @7  :Document;
  graph            @8  :Graph;
  vector           @9  :Vector;
  tensor           @10 :Tensor;
  spatial          @11 :Spatial;
}

# --- E2 — Semantic ---
enum DeclKind {
  function   @0;
  data       @1;
  record     @2;
  postulate  @3;
  module     @4;
}

struct Semantic {
  octadKey   @0 :Text;
  kind       @1 :DeclKind;
  name       @2 :Text;
  statement  @3 :Text;
  proof      @4 :Text;          # empty string if no proof (postulate / data)
}

# --- E3 — Temporal ---
enum ChangeKind {
  created     @0;
  edited      @1;
  renamed     @2;
  refactored  @3;
  deleted     @4;
}

struct VersionEntry {
  timestamp   @0 :UInt64;
  changeKind  @1 :ChangeKind;
  parentKey   @2 :Text;         # UUIDv7 of parent, empty for created
}

struct Temporal {
  octadKey         @0 :Text;
  versions         @1 :List(VersionEntry);
  parentOctadKey   @2 :Text;    # empty = chain head
}

# --- E4 — Provenance ---
struct Provenance {
  octadKey         @0 :Text;
  sourceHash       @1 :Text;    # SHA-256 hex of source file
  ingestActor      @2 :Text;    # CI job id / user agent
  ingestTs         @3 :UInt64;
  chainPrevHash    @4 :Text;    # empty = chain head
}

# --- E5 — Document ---
struct Document {
  octadKey         @0 :Text;
  searchableText   @1 :Text;
  aspects          @2 :List(Text);
}

# --- E6 — Graph ---
struct Graph {
  octadKey                  @0 :Text;
  dependsOn                 @1 :List(Text);   # UUIDv7 list
  dependedOnBy              @2 :List(Text);
  crossProverIdentityKey    @3 :Text;
}

# --- E7 — Vector ---
struct Vector {
  octadKey         @0 :Text;
  goalEmbedding    @1 :List(Float32);
  embedder         @2 :Text;    # "hash-v1" / "gnn-v1"
  embedderDim      @3 :UInt32;
}

# --- E8 — Tensor ---
struct Tensor {
  octadKey              @0 :Text;
  proofDepth            @1 :UInt32;
  statementSizeTokens   @2 :UInt32;
  hazardBitmap          @3 :UInt32;
  # bit 0 = postulate, 1 = believe_me, 2 = admitted, 3 = sorry,
  # 4 = trustme, 5+ = adapter-specific other flags
  axiomCount            @4 :UInt32;
}

# --- E9 — Spatial ---
struct Spatial {
  octadKey   @0 :Text;
  filePath   @1 :Text;
  line       @2 :UInt32;
  column     @3 :UInt32;  # 0 if unknown
}

# --- E10 — ProofAttempt ---
enum Verdict {
  proven     @0;
  refuted    @1;
  timeout    @2;
  unknown    @3;
  error      @4;
}

struct ProofAttempt {
  attemptId                 @0 :Text;       # UUIDv7
  octadKey                  @1 :Text;       # FK -> Octad.key
  prover                    @2 :Text;       # ProverKind string
  verdict                   @3 :Verdict;
  startedAt                 @4 :UInt64;
  latencyMs                 @5 :UInt64;
  axiomCost                 @6 :UInt32;
  certificateBlobKey        @7 :Text;       # FK -> CertificateBlob.blobKey, empty if none
  proverBinaryHash          @8 :Text;       # FK -> ProverBinaryIntegrity.binaryHash
  confidenceSelfReported    @9 :Float64;    # NaN if not reported
}

# --- E11 — CertificateBlob ---
enum CertificateFormat {
  alethe       @0;
  drat         @1;
  lrat         @2;
  tstp         @3;
  openTheory   @4;
  dedukti      @5;
  lambdapi     @6;
  smtCoq       @7;
  other        @8;
}

struct CertificateBlob {
  blobKey      @0 :Text;        # SHAKE3-512 hex of content
  format       @1 :CertificateFormat;
  bytes        @2 :Data;        # raw certificate
  createdAt    @3 :UInt64;
}

# --- E12 — ProverBinaryIntegrity ---
struct ProverBinaryIntegrity {
  prover          @0 :Text;
  binaryHash      @1 :Text;     # SHAKE3-512 + BLAKE3
  versionLabel    @2 :Text;     # e.g. "z3-4.13.0-ubuntu22-x64"
  firstSeenTs     @3 :UInt64;
}

# --- Bulk transport envelopes ---

# Used when streaming many octads in one wire message (e.g. corpus
# ingest emit). One per producer batch.
struct OctadBatch {
  batchId      @0 :Text;
  producer     @1 :Text;
  octads       @2 :List(Octad);
}

# Used when streaming many attempts (e.g. nightly learning daemon).
struct ProofAttemptBatch {
  batchId      @0 :Text;
  producer     @1 :Text;
  attempts     @2 :List(ProofAttempt);
}

# --- E-R cross-prover cluster (materialised view) ---
# Read-mostly: produced by VeriSimDB-side join, consumed by ECHIDNA.
struct CrossProverCluster {
  identityKey  @0 :Text;        # e.g. "nat-add-commutativity"
  octadKeys    @1 :List(Text);  # all octads sharing this identity
  adapters     @2 :List(Text);  # distinct adapter names in this cluster
}
