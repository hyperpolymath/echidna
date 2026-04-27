-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- IntegrityVerification.lean
--
-- Proof obligation **E11**: solver-binary integrity verification using
-- the Keccak-derived "SHAKE3-512" (= SHAKE-256 squeezing 512 bits,
-- per FIPS 202) and BLAKE3 (Bao tree hashing).
--
-- Models the Rust implementation in `src/rust/integrity/solver_integrity.rs`.
--
-- /-! # Integrity verification (E11)
--
-- ## Terminology note
--
-- The codebase calls its primary integrity hash `SHAKE3-512`.  No such
-- function exists in the standard nomenclature: there is *Keccak-512*
-- (the Round-3 SHA-3 candidate output length) and *SHAKE-256 squeezed
-- to 512 bits* (FIPS 202).  The Rust implementation uses
-- `tiny_keccak::Shake::v256()` and squeezes a 64-byte (512-bit) output
-- — i.e. **SHAKE-256 with 512 output bits**.  We treat this hash as an
-- abstract function `hashShake : ByteString → Digest512` and the
-- BLAKE3 hash as `hashBlake3 : ByteString → Digest256` and reason
-- about the verifier *given* the standard collision-resistance
-- assumption on each.
--
-- ## What's proved
--
-- 1. **Verifier soundness** — the verifier returns `Verified` only
--    when the computed hash equals the expected manifest hash.
-- 2. **Verifier completeness** — when the manifest is initialised
--    (no placeholder), the verifier returns `Verified` iff the
--    computed hash matches the expected hash.
-- 3. **Tamper detection** — if the binary content has changed and the
--    hash is not a placeholder, status ≠ Verified.  Conditional on
--    the standard collision-resistance assumption (Sec.5).
-- 4. **Status exhaustiveness** — every binary lookup yields exactly
--    one of `{Verified, Tampered, Missing, Uninitialized}` (the fifth
--    variant `Unchecked` is the *not-yet-checked* state and never
--    appears as a verifier output).
-- 5. **Placeholder transition** — a manifest entry whose hash starts
--    with "PLACEHOLDER" produces `Uninitialized`, regardless of the
--    actual binary content.
-- 6. **BLAKE3 cache freshness** — if the cached BLAKE3 hash matches
--    the current BLAKE3 hash, the binary content is the same as at
--    the last full verification (conditional on BLAKE3 collision
--    resistance).
--
-- ## Why it matters
--
-- The integrity check is the trust *root* of the dispatch pipeline:
-- a tampered solver could trivially manufacture false theorems.  The
-- `compute_trust_level` function in `confidence.rs` caps trust at
-- `Level1` whenever `solver_integrity_ok = false`; that cap is only
-- meaningful if `solver_integrity_ok` itself faithfully reflects the
-- binary state.  This file formalises that "faithfully reflects"
-- claim modulo standard hash assumptions.
-- -/

namespace EchidnaIntegrity

-- ==========================================================================
-- Section 1: Abstract hash domain
-- ==========================================================================

/-- A byte string (model of file contents).  Represented as an opaque
    `ByteString` type with decidable equality. -/
structure ByteString where
  bytes : List UInt8
deriving DecidableEq, Repr

/-- A 512-bit digest (SHAKE-256 squeezed to 512 bits). -/
structure Digest512 where
  bytes : List UInt8  -- canonical length = 64
deriving DecidableEq, Repr

/-- A 256-bit digest (BLAKE3 standard output). -/
structure Digest256 where
  bytes : List UInt8  -- canonical length = 32
deriving DecidableEq, Repr

-- ==========================================================================
-- Section 2: Hash functions (modelled as opaque pure functions)
-- ==========================================================================

/-- The SHAKE-256-with-512-bit-output hash, named "SHAKE3-512" in the
    Rust codebase.  Modelled as an opaque pure function from byte
    strings to 512-bit digests.

    Implementation reference: `IntegrityChecker::compute_shake3_512`
    in `src/rust/integrity/solver_integrity.rs:108-121`. -/
opaque hashShake : ByteString → Digest512

/-- The BLAKE3 hash (standard 32-byte output).

    Implementation reference: `IntegrityChecker::compute_blake3`
    in `src/rust/integrity/solver_integrity.rs:123-130`. -/
opaque hashBlake3 : ByteString → Digest256

-- ==========================================================================
-- Section 3: Manifest entry and integrity status
-- ==========================================================================

/-- Path string (no canonicalisation logic — opaque tag). -/
structure Path where
  raw : String
deriving DecidableEq, Repr

/-- Encoded SHAKE-256/512 hash as a hex string.  Either an actual hex
    digest or the placeholder marker. -/
inductive ManifestHash : Type where
  | placeholder : ManifestHash
  | digest      : Digest512 → ManifestHash
deriving DecidableEq, Repr

/-- Mirrors `SolverManifestEntry` in solver_integrity.rs. -/
structure ManifestEntry where
  version        : String
  hash           : ManifestHash
  primary_path   : Path
  fallback_paths : List Path
deriving Repr

/-- Mirrors `IntegrityStatus` in solver_integrity.rs.  Note that the
    Rust enum has a fifth variant `Unchecked` for the not-yet-checked
    initial state; that variant cannot appear as a *verifier output*
    and is therefore omitted from this verifier model. -/
inductive IntegrityStatus : Type where
  | verified      : IntegrityStatus
  | tampered      : IntegrityStatus
  | missing       : IntegrityStatus
  | uninitialized : IntegrityStatus
deriving DecidableEq, Repr

/-- Filesystem read result: either the binary's contents or absence. -/
inductive FileResult : Type where
  | found    : ByteString → FileResult
  | notFound : FileResult
deriving Repr

-- ==========================================================================
-- Section 4: Verifier (pure model of `verify_solver`)
-- ==========================================================================

/-- The pure decision core of `IntegrityChecker::verify_solver`,
    extracted from the async / I/O wrapper.

    Behaviour:
    * If filesystem returns `notFound`, status = `missing`.
    * If the manifest entry's hash is `placeholder`, status =
      `uninitialized` (initial-import case — the verifier records
      the freshly computed hash for future runs).
    * Otherwise compare the computed hash with the manifest digest;
      `verified` on equality, `tampered` on mismatch.

    Mirrors `solver_integrity.rs:212-311`. -/
def verify (entry : ManifestEntry) (file : FileResult) : IntegrityStatus :=
  match file with
  | FileResult.notFound => IntegrityStatus.missing
  | FileResult.found bs =>
    match entry.hash with
    | ManifestHash.placeholder => IntegrityStatus.uninitialized
    | ManifestHash.digest expected =>
      if hashShake bs = expected then
        IntegrityStatus.verified
      else
        IntegrityStatus.tampered

-- ==========================================================================
-- Section 5: Soundness, completeness, exhaustiveness
-- ==========================================================================

/-- **PI-1 (E11/1) Verifier soundness**: if `verify` returns
    `verified`, the computed hash of the binary equals the manifest
    digest. -/
theorem verify_sound (entry : ManifestEntry) (file : FileResult) :
    verify entry file = IntegrityStatus.verified →
    ∃ bs expected,
      file = FileResult.found bs
      ∧ entry.hash = ManifestHash.digest expected
      ∧ hashShake bs = expected := by
  intro h
  unfold verify at h
  match hf : file, hh : entry.hash with
  | FileResult.notFound, _ =>
    rw [hf] at h; simp at h
  | FileResult.found bs, ManifestHash.placeholder =>
    rw [hf, hh] at h; simp at h
  | FileResult.found bs, ManifestHash.digest expected =>
    rw [hf, hh] at h
    by_cases heq : hashShake bs = expected
    · exact ⟨bs, expected, hf, hh, heq⟩
    · simp [heq] at h

/-- **PI-2 (E11/2) Verifier completeness**: if the file is found and
    the manifest digest matches, `verify` returns `verified`. -/
theorem verify_complete (entry : ManifestEntry) (bs : ByteString)
    (expected : Digest512)
    (hfile : entry.hash = ManifestHash.digest expected)
    (hhash : hashShake bs = expected) :
    verify entry (FileResult.found bs) = IntegrityStatus.verified := by
  unfold verify
  rw [hfile]
  simp [hhash]

/-- **PI-3 (E11/3) Tamper detection**: if the manifest is initialised
    (digest, not placeholder), the binary is found, and the *content*
    differs from a known-good content with identical manifest, the
    verifier output is *not* `verified`.

    This is conditional on the SHAKE-256 collision-resistance
    assumption (Sec.6 below).  The unconditional statement here is the
    contrapositive of `verify_sound`: a `verified` outcome forces hash
    equality. -/
theorem verify_tamper_detection (entry : ManifestEntry)
    (bs bs' : ByteString) (expected : Digest512)
    (hfile : entry.hash = ManifestHash.digest expected)
    (hgood : hashShake bs' = expected)
    (hdiff : hashShake bs ≠ hashShake bs') :
    verify entry (FileResult.found bs) ≠ IntegrityStatus.verified := by
  intro hv
  unfold verify at hv
  rw [hfile] at hv
  by_cases heq : hashShake bs = expected
  · rw [hgood] at hdiff
    exact hdiff heq
  · simp [heq] at hv

/-- **PI-4 (E11/4) Status exhaustiveness**: every input pair maps to
    one of the four declared statuses. -/
theorem verify_exhaustive (entry : ManifestEntry) (file : FileResult) :
    verify entry file = IntegrityStatus.verified
    ∨ verify entry file = IntegrityStatus.tampered
    ∨ verify entry file = IntegrityStatus.missing
    ∨ verify entry file = IntegrityStatus.uninitialized := by
  unfold verify
  match file with
  | FileResult.notFound =>
    right; right; left; rfl
  | FileResult.found bs =>
    match entry.hash with
    | ManifestHash.placeholder =>
      right; right; right; rfl
    | ManifestHash.digest expected =>
      by_cases heq : hashShake bs = expected
      · left; simp [heq]
      · right; left; simp [heq]

/-- **PI-5 (E11/5) Placeholder transition**: a placeholder manifest
    entry produces `uninitialized` regardless of binary content. -/
theorem verify_placeholder (entry : ManifestEntry) (bs : ByteString)
    (hph : entry.hash = ManifestHash.placeholder) :
    verify entry (FileResult.found bs) = IntegrityStatus.uninitialized := by
  unfold verify
  rw [hph]

/-- **PI-6 (E11/6) Missing dispatch**: a `notFound` filesystem result
    always yields `missing`, regardless of manifest entry contents. -/
theorem verify_missing (entry : ManifestEntry) :
    verify entry FileResult.notFound = IntegrityStatus.missing := by
  unfold verify
  rfl

-- ==========================================================================
-- Section 6: Collision resistance and tamper detection (conditional)
-- ==========================================================================

/-- **The collision-resistance assumption (CR)** for the SHAKE-256/512
    hash, as a Lean axiom-class.  This is *not* proved here; it is the
    standard cryptographic assumption that `hashShake` is collision
    resistant on practically-bounded inputs.  The implementation relies
    on the Keccak permutation's resistance to differential and linear
    cryptanalysis, plus the squeeze-output construction's preservation
    of those properties.

    NOTE — *not declared as a Lean `axiom`* per project convention
    (zero-axiom policy on this codebase).  Instead expressed as a
    typeclass instance the application can supply.  Any consumer who
    wants the conditional theorem in §PI-7 must provide an instance
    of this class explicitly. -/
class CollisionResistantShake : Prop where
  injective : ∀ x y : ByteString, hashShake x = hashShake y → x = y

/-- **PI-7 (E11/7) Conditional tamper detection**: under SHAKE
    collision-resistance, any change to the binary content detectably
    changes the hash, so a tampered binary cannot pass verification. -/
theorem verify_tamper_detected_under_cr [cr : CollisionResistantShake]
    (entry : ManifestEntry) (bs bs' : ByteString) (expected : Digest512)
    (hfile : entry.hash = ManifestHash.digest expected)
    (hgood : hashShake bs' = expected)
    (hbs_ne : bs ≠ bs') :
    verify entry (FileResult.found bs) ≠ IntegrityStatus.verified := by
  apply verify_tamper_detection entry bs bs' expected hfile hgood
  intro hheq
  exact hbs_ne (cr.injective bs bs' hheq)

-- ==========================================================================
-- Section 7: BLAKE3 fast re-verification cache
-- ==========================================================================

/-- A BLAKE3 cache entry: name → cached BLAKE3 of the binary at the
    last full SHAKE verification.  Mirrors
    `IntegrityChecker::blake3_cache` (a `HashMap<String, String>`). -/
structure Blake3CacheEntry where
  solver_name      : String
  cached_blake3    : Digest256
  last_verified_bs : ByteString
deriving Repr

/-- **PI-8 (E11/8) Cache invariant**: the cached BLAKE3 hash is the
    BLAKE3 hash of the byte-string that was current at the last full
    verification.  This is the invariant `IntegrityChecker` is meant
    to maintain when populating the cache after a successful
    `verify_solver` call. -/
def cacheInvariant (e : Blake3CacheEntry) : Prop :=
  e.cached_blake3 = hashBlake3 e.last_verified_bs

/-- The fast re-verifier: returns `true` iff the BLAKE3 hash of the
    current binary matches the cached BLAKE3 hash.

    Mirrors `IntegrityChecker::quick_reverify` in
    `solver_integrity.rs:315-…`. -/
def quickReverify (e : Blake3CacheEntry) (current : ByteString) : Bool :=
  decide (hashBlake3 current = e.cached_blake3)

/-- **PI-9 (E11/9) Quick-reverify soundness (conditional)**: if the
    cache invariant holds and BLAKE3 is collision-resistant, then
    `quickReverify` returns `true` only when the binary content
    actually equals the last-verified content. -/
class CollisionResistantBlake3 : Prop where
  injective : ∀ x y : ByteString, hashBlake3 x = hashBlake3 y → x = y

theorem quickReverify_sound_under_cr [cr : CollisionResistantBlake3]
    (e : Blake3CacheEntry) (current : ByteString)
    (hinv : cacheInvariant e)
    (hquick : quickReverify e current = true) :
    current = e.last_verified_bs := by
  unfold quickReverify at hquick
  unfold cacheInvariant at hinv
  rw [hinv] at hquick
  have heq : hashBlake3 current = hashBlake3 e.last_verified_bs :=
    of_decide_eq_true hquick
  exact cr.injective _ _ heq

/-- **PI-10 (E11/10) Quick-reverify completeness**: if the binary
    content is unchanged since last verification, `quickReverify`
    accepts (this direction is unconditional — equal content always
    gives equal BLAKE3 hashes). -/
theorem quickReverify_complete (e : Blake3CacheEntry) (current : ByteString)
    (hinv : cacheInvariant e)
    (heq : current = e.last_verified_bs) :
    quickReverify e current = true := by
  unfold quickReverify
  unfold cacheInvariant at hinv
  rw [heq, hinv]
  simp

-- ==========================================================================
-- Section 8: Trust pipeline interaction (E11 ↔ E4)
-- ==========================================================================

/-- The trust pipeline (E4 — see `ConfidenceLattice.lean`) gates
    `solver_integrity_ok` on the verifier's output.  We record the
    canonical mapping here so that downstream proofs can chain the
    integrity result into the trust-level computation. -/
def integrityToBool (s : IntegrityStatus) : Bool :=
  s = IntegrityStatus.verified

/-- **PI-11 (E11/11) Trust gate**: `solver_integrity_ok` is `true` iff
    the verifier returns `verified`. -/
theorem trust_gate_iff_verified (s : IntegrityStatus) :
    integrityToBool s = true ↔ s = IntegrityStatus.verified := by
  unfold integrityToBool
  cases s <;> simp

/-- **PI-12 (E11/12) Tampered → integrity_ok = false**.  Composes with
    `confidence.rs` `compute_trust_level` to cap a tampered solver's
    output at `Level1`. -/
theorem tampered_kills_trust :
    integrityToBool IntegrityStatus.tampered = false := by
  unfold integrityToBool
  decide

end EchidnaIntegrity
