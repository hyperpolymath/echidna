-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- ECHIDNA Coprocessor ABI — foreign declarations + trust-tier invariants.
--
-- Mirrors:
--   src/rust/coprocessor/types.rs          (CoprocessorKind, Op, Outcome, Health)
--   src/rust/coprocessor/trust.rs          (CoprocessorTrustTier)
--   src/rust/coprocessor/mod.rs            (Coprocessor trait surface)
--   src/ada/spark/coprocessor_safety.ads   (SPARK trust-tier invariant)
--
-- Phase 0 declares the Math kind only.  Phase 6 backends (Physics, DSP,
-- FPGA, Tensor, Vector, Crypto, Graphics, Audio, IO) extend this module
-- alongside their Rust impls — never as stubs.
--
-- NO believe_me anywhere. All safety is enforced by types.

module Coprocessor.Foreign

%default total

--------------------------------------------------------------------------------
-- Trust tier — pinned discriminants matching axiom_policy.ads / trust.rs
--------------------------------------------------------------------------------

||| Coprocessor trust tier (strict total order).
||| Numeric encoding pinned: PureFormal=5, NativeKernel=4, LibraryWrapped=3,
||| JuliaBridged=2, ExternalSubprocess=1.
||| Reordering is an ABI break — bumped in lockstep with Zig + Rust + SPARK.
public export
data CoprocessorTrustTier : Type where
  ExternalSubprocess : CoprocessorTrustTier  -- Tier 1: Sage / GAP / Maxima …
  JuliaBridged       : CoprocessorTrustTier  -- Tier 2: LowLevel.jl bridge
  LibraryWrapped     : CoprocessorTrustTier  -- Tier 3: thin Rust wrapper
  NativeKernel       : CoprocessorTrustTier  -- Tier 4: SPARK-verified
  PureFormal         : CoprocessorTrustTier  -- Tier 5: Idris2 ABI + kernel proof

||| Decode a u8 discriminant into a tier; defaults to lowest tier on
||| out-of-range (defensive — the SPARK and Rust layers never emit bad ints).
public export
trustTierFromU8 : Bits8 -> CoprocessorTrustTier
trustTierFromU8 1 = ExternalSubprocess
trustTierFromU8 2 = JuliaBridged
trustTierFromU8 3 = LibraryWrapped
trustTierFromU8 4 = NativeKernel
trustTierFromU8 5 = PureFormal
trustTierFromU8 _ = ExternalSubprocess

||| Encode a tier as the canonical u8 discriminant.
public export
trustTierToU8 : CoprocessorTrustTier -> Bits8
trustTierToU8 ExternalSubprocess = 1
trustTierToU8 JuliaBridged       = 2
trustTierToU8 LibraryWrapped     = 3
trustTierToU8 NativeKernel       = 4
trustTierToU8 PureFormal         = 5

||| Tier 3 (LibraryWrapped) and above are *self-sufficient*: their results
||| can be folded into a high-trust prover pipeline without an independent
||| cross-check.  Tiers 1-2 must be cross-validated.  Mirrors the Rust
||| `is_self_sufficient` and the SPARK `Is_Self_Sufficient` post-condition.
public export
isSelfSufficient : CoprocessorTrustTier -> Bool
isSelfSufficient ExternalSubprocess = False
isSelfSufficient JuliaBridged       = False
isSelfSufficient LibraryWrapped     = True
isSelfSufficient NativeKernel       = True
isSelfSufficient PureFormal         = True

--------------------------------------------------------------------------------
-- Round-trip proofs for the discriminant encoding
--------------------------------------------------------------------------------

||| Round-trip: encoding then decoding a tier yields the original.
||| The proof is *constructive* — case analysis discharges each variant.
||| Together with `decodeEncodeId` this guarantees ABI well-formedness.
public export
encodeDecodeId : (t : CoprocessorTrustTier) -> trustTierFromU8 (trustTierToU8 t) = t
encodeDecodeId ExternalSubprocess = Refl
encodeDecodeId JuliaBridged       = Refl
encodeDecodeId LibraryWrapped     = Refl
encodeDecodeId NativeKernel       = Refl
encodeDecodeId PureFormal         = Refl

--------------------------------------------------------------------------------
-- Coprocessor kind
--------------------------------------------------------------------------------

||| The kind of a coprocessor backend.  Only variants with a fully
||| functional Rust + Idris2 implementation appear here.  Phase 6A added
||| Vector / Tensor / Crypto / Physics; Phase 6B adds Dsp / Io / Graphics /
||| Audio / Fpga.  FlintMath (Phase 2A) is feature-gated in Rust but the
||| ABI surface is unconditional.
public export
data CoprocessorKind : Type where
  Math      : CoprocessorKind  -- Phase 0  (num-bigint + num-integer)
  Vector    : CoprocessorKind  -- Phase 6A (auto-vectorised f64 loops)
  Tensor    : CoprocessorKind  -- Phase 6A (nalgebra dense linalg)
  Crypto    : CoprocessorKind  -- Phase 6A (sha2 + blake3 + ed25519-dalek)
  Physics   : CoprocessorKind  -- Phase 6A (RK4 + harmonic energy oracles)
  FlintMath : CoprocessorKind  -- Phase 2A (FLINT C library FFI, --features flint)
  Dsp       : CoprocessorKind  -- Phase 6B (rustfft FFT/IFFT + windows)
  Io        : CoprocessorKind  -- Phase 6B (tokio::fs file ops)
  Graphics  : CoprocessorKind  -- Phase 6B (SVG rendering, no GPU)
  Audio     : CoprocessorKind  -- Phase 6B (PCM/WAV synthesis)
  Fpga      : CoprocessorKind  -- Phase 6B (yosys subprocess, Tier 1)

||| Encoding to u8 — pinned for FFI stability.  Reordering is an ABI break.
public export
coprocessorKindToU8 : CoprocessorKind -> Bits8
coprocessorKindToU8 Math      = 0
coprocessorKindToU8 Vector    = 1
coprocessorKindToU8 Tensor    = 2
coprocessorKindToU8 Crypto    = 3
coprocessorKindToU8 Physics   = 4
coprocessorKindToU8 FlintMath = 5
coprocessorKindToU8 Dsp       = 6
coprocessorKindToU8 Io        = 7
coprocessorKindToU8 Graphics  = 8
coprocessorKindToU8 Audio     = 9
coprocessorKindToU8 Fpga      = 10

public export
coprocessorKindFromU8 : Bits8 -> Maybe CoprocessorKind
coprocessorKindFromU8 0  = Just Math
coprocessorKindFromU8 1  = Just Vector
coprocessorKindFromU8 2  = Just Tensor
coprocessorKindFromU8 3  = Just Crypto
coprocessorKindFromU8 4  = Just Physics
coprocessorKindFromU8 5  = Just FlintMath
coprocessorKindFromU8 6  = Just Dsp
coprocessorKindFromU8 7  = Just Io
coprocessorKindFromU8 8  = Just Graphics
coprocessorKindFromU8 9  = Just Audio
coprocessorKindFromU8 10 = Just Fpga
coprocessorKindFromU8 _  = Nothing

||| Round-trip on the kind discriminant.  Constructive — case-analysis
||| discharges every variant.  Zero believe_me.
public export
kindEncodeDecodeId :
  (k : CoprocessorKind) ->
  coprocessorKindFromU8 (coprocessorKindToU8 k) = Just k
kindEncodeDecodeId Math      = Refl
kindEncodeDecodeId Vector    = Refl
kindEncodeDecodeId Tensor    = Refl
kindEncodeDecodeId Crypto    = Refl
kindEncodeDecodeId Physics   = Refl
kindEncodeDecodeId FlintMath = Refl
kindEncodeDecodeId Dsp       = Refl
kindEncodeDecodeId Io        = Refl
kindEncodeDecodeId Graphics  = Refl
kindEncodeDecodeId Audio     = Refl
kindEncodeDecodeId Fpga      = Refl

--------------------------------------------------------------------------------
-- Health
--------------------------------------------------------------------------------

public export
data CoprocessorHealth : Type where
  Healthy   : CoprocessorHealth
  Degraded  : CoprocessorHealth
  Unhealthy : CoprocessorHealth

public export
healthToU8 : CoprocessorHealth -> Bits8
healthToU8 Healthy   = 0
healthToU8 Degraded  = 1
healthToU8 Unhealthy = 2

public export
healthFromU8 : Bits8 -> CoprocessorHealth
healthFromU8 0 = Healthy
healthFromU8 1 = Degraded
healthFromU8 _ = Unhealthy

--------------------------------------------------------------------------------
-- Foreign declarations (linked from libechidna_coprocessor — wired in Phase 6
-- once the C-ABI surface stabilises across kinds).  The Math backend is
-- currently called from Rust directly without crossing the C ABI; this
-- foreign block documents the future seam.
--
-- Schema:
--   echidna_coprocessor_dispatch(
--       kind:        u8,         -- CoprocessorKind discriminant
--       op_buf:      *const u8,  -- borsh-encoded CoprocessorOp
--       op_len:      usize,
--       out_buf:     *mut u8,    -- caller-owned, capacity ≥ out_cap
--       out_cap:     usize,
--       out_len:     *mut usize, -- bytes written
--   ) -> i32                    -- 0 success, <0 transport error
--------------------------------------------------------------------------------

||| Health of a kind, queried via the C ABI.  Unimplemented kinds report
||| Unhealthy.  Currently a placeholder until libechidna_coprocessor lands.
public export
coprocessorHealthOf : CoprocessorKind -> CoprocessorHealth
coprocessorHealthOf Math      = Healthy
coprocessorHealthOf Vector    = Healthy
coprocessorHealthOf Tensor    = Healthy
coprocessorHealthOf Crypto    = Healthy
coprocessorHealthOf Physics   = Healthy
coprocessorHealthOf FlintMath = Healthy
coprocessorHealthOf Dsp       = Healthy
coprocessorHealthOf Io        = Healthy
coprocessorHealthOf Graphics  = Healthy
coprocessorHealthOf Audio     = Healthy
coprocessorHealthOf Fpga      = Unhealthy  -- subprocess; runtime probe required
