// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later
// (MPL-2.0 is automatic legal fallback until PMPL is formally recognised)

//! Coprocessor type surface.
//!
//! Defines the input/output language of the coprocessor abstraction:
//! `CoprocessorOp` is the request, `CoprocessorOutcome` is the reply,
//! `CoprocessorCapabilities` is what a backend reports it can do, and
//! `CoprocessorHealth` is its runtime liveness.
//!
//! The op set starts with the Math operations needed by the number-theory
//! and algebraic-decision-procedure backends planned for Phases 2 and 3
//! (FLINT, PARI/GP, GAP, QEPCAD-B, …).  Future variants for Physics, DSP,
//! FPGA, Tensor, Vector, Crypto, Graphics, Audio, IO are added alongside
//! their backend implementations in Phase 6 — never as stubs.

use serde::{Deserialize, Serialize};

/// The kind of coprocessor a backend implements.
///
/// Only variants with a fully-functional backend are present.  Phase 6A
/// adds Vector / Tensor / Crypto / Physics; Phase 6B will add DSP / FPGA /
/// Graphics / Audio / IO together with their implementations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum CoprocessorKind {
    /// Number theory, exact arithmetic, polynomial algebra over Q.
    /// Native Rust impl backed by `num-bigint` / `num-integer` / `num-rational`.
    Math,

    /// Dense vector arithmetic (auto-vectorised f64 loops).  Backs
    /// SIMD-batched ops for the GNN inference path and aggregate reasoning.
    Vector,

    /// Dense tensor / matrix linear algebra via `nalgebra`.  Backs node-
    /// embedding aggregation, Pareto-frontier dominance computations, and
    /// the matrix kernels that cross-prover certificate exchange depends on.
    Tensor,

    /// Cryptographic primitives — hashing, signature verification.
    /// Pairs with the future EasyCrypt / Tamarin / ProVerif backends as
    /// the *computational* (vs symbolic) crypto surface.
    Crypto,

    /// Numerical integration of ODE / Hamiltonian systems.  Pairs with the
    /// future KeYmaera X backend as a sanity-check oracle for hybrid-system
    /// trajectories proven correct symbolically.
    Physics,

    /// FLINT integer and polynomial algebra — the only CAS backend that links
    /// the library in-process rather than shelling out.  Requires
    /// `--features flint` and a system FLINT (LGPL-3) installation.
    /// Enabled by `CoprocessorFactory::native`; absent without the feature.
    FlintMath,

    /// Digital signal processing — FFT/IFFT, window functions.  Backed by
    /// `rustfft`.  Pairs with the Tamarin / ProVerif backends for proofs
    /// about communication channels and signal-bearing protocols.
    Dsp,

    /// File and stream I/O.  Async via `tokio::fs`.  Backs proof-artifact
    /// handling — read a Coq .v file, hash it, line-count it.
    Io,

    /// 2-D graphics — emits SVG strings.  No GPU dependency.  Backs the
    /// proof-graph visualisation that the GNN-guided search consumes,
    /// and renders Pareto-frontier diagnostics.
    Graphics,

    /// Audio synthesis — generates PCM / WAV.  Backs the completion-chime
    /// machinery and any audio-signal proof obligations (rare but real
    /// for cyber-physical KeYmaera X targets that involve audible signals).
    Audio,

    /// FPGA / hardware verification — subprocess to yosys.  Trust tier
    /// `ExternalSubprocess` (Tier 1).  Backs proofs about hardware modules
    /// expressed in Verilog / SystemVerilog.
    Fpga,
}

/// A request dispatched to a coprocessor.
///
/// The op set is closed over the union of operations needed by the planned
/// backends.  Each variant is small and total — wide signatures are split
/// into smaller ops rather than packed into a generic blob.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum CoprocessorOp {
    // ── Math: integer arithmetic ─────────────────────────────────────────
    /// Greatest common divisor of two arbitrary-precision integers.
    BigIntGcd { a: String, b: String },

    /// Least common multiple.
    BigIntLcm { a: String, b: String },

    /// Modular exponentiation: base^exp mod modulus, with modulus > 0.
    BigIntModExp { base: String, exp: String, modulus: String },

    /// Modular inverse: returns a^-1 mod modulus, or `None` if non-invertible.
    BigIntModInverse { a: String, modulus: String },

    /// Miller–Rabin probabilistic primality test (40 rounds — error ≤ 2⁻⁸⁰).
    BigIntIsProbablePrime { n: String },

    /// Trial-division factorisation up to a small bound, then Pollard rho
    /// for the remainder.  Returns prime factors with multiplicity.
    /// Useful as a fast oracle for SMT theories of arithmetic.
    BigIntFactor { n: String },

    // ── Math: rational arithmetic ────────────────────────────────────────
    /// Simplify a rational p/q to lowest terms; returns canonical form.
    RationalSimplify { num: String, den: String },

    // ── Math: integer sequences ──────────────────────────────────────────
    /// Fibonacci F_n (closed-form via matrix exponentiation).
    Fibonacci { n: u64 },

    /// Factorial n! (memoised under the hood).
    Factorial { n: u64 },

    // ── Vector: dense f64 arithmetic ─────────────────────────────────────
    /// Element-wise addition.  Vectors must be the same length.
    VectorAdd { a: Vec<f64>, b: Vec<f64> },

    /// Inner product ∑ aᵢbᵢ.  Vectors must be the same length.
    VectorDot { a: Vec<f64>, b: Vec<f64> },

    /// Euclidean (L²) norm.
    VectorNorm { a: Vec<f64> },

    /// Scalar multiplication k·a.
    VectorScale { a: Vec<f64>, k: f64 },

    // ── Tensor: dense linear algebra over f64 ────────────────────────────
    /// Matrix multiplication A·B.  `a` is row-major (rows_a × cols_a),
    /// `b` is row-major (rows_b × cols_b).  cols_a must equal rows_b.
    TensorMatMul {
        a: Vec<Vec<f64>>,
        b: Vec<Vec<f64>>,
    },

    /// Matrix transpose.  Returns row-major Aᵀ.
    TensorTranspose { a: Vec<Vec<f64>> },

    /// Trace of a square matrix.
    TensorTrace { a: Vec<Vec<f64>> },

    /// Determinant of a square matrix (LU under the hood for n > 4).
    TensorDeterminant { a: Vec<Vec<f64>> },

    // ── Crypto: computational primitives ─────────────────────────────────
    /// SHA-256 of arbitrary bytes; result is hex-encoded.
    CryptoSha256 { bytes: Vec<u8> },

    /// BLAKE3 of arbitrary bytes; result is hex-encoded.
    CryptoBlake3 { bytes: Vec<u8> },

    /// Verify an Ed25519 signature.  Public key + signature + message all
    /// raw bytes.  Returns Boolean(true) on valid, Boolean(false) on
    /// invalid signature, Failure on malformed key/sig length.
    CryptoEd25519Verify {
        public_key: Vec<u8>,
        signature: Vec<u8>,
        message: Vec<u8>,
    },

    // ── Physics: ODE integration / energy invariants ─────────────────────
    /// One Runge-Kutta-4 step for ẋ = f(x).  `f` is encoded as a fixed
    /// well-known kernel name plus parameters, so the wire form stays
    /// serialisable (closures don't cross the wire).  Currently supported
    /// kernels: "harmonic-oscillator" (ẋ = -ω²x), "exponential-decay"
    /// (ẋ = -λx), "linear" (ẋ = a·x + b).
    PhysicsRk4Step {
        kernel: String,
        params: Vec<f64>,
        x: Vec<f64>,
        dt: f64,
    },

    /// Total mechanical energy of a unit-mass harmonic oscillator at
    /// (x, p): E = ½p² + ½ω²x².  Trivial but useful as an invariant
    /// oracle in proofs about Hamiltonian systems.
    PhysicsHarmonicEnergy { x: f64, p: f64, omega: f64 },

    // ── FLINT: polynomial algebra over Z ─────────────────────────────────────
    /// Primitive GCD of two polynomials over Z.
    ///
    /// Wire format: space-separated decimal integer coefficients in
    /// degree-ascending order.  `"1 0 -1"` encodes `1 − x²`.  Zero
    /// polynomial: `"0"`.  Result has positive leading coefficient.
    FlintPolyGcd { f: String, g: String },

    /// Product of two polynomials over Z.
    FlintPolyMul { f: String, g: String },

    /// Pseudo-remainder of `f` divided by `g` over Z.
    ///
    /// Satisfies `lc(g)^d · f = q · g + r` for the returned `r` (`d ≥ 0`).
    /// Returns the zero polynomial when `g` exactly divides `f`.
    /// Errors if `g` is the zero polynomial.
    FlintPolyRem { f: String, g: String },

    /// Content of a polynomial — the GCD of all its coefficients (positive).
    /// Returns `BigInt("0")` for the zero polynomial.
    FlintPolyContent { f: String },

    // ── FLINT: enhanced integer arithmetic ───────────────────────────────────
    /// Exact integer k-th root.
    ///
    /// Returns `BigInt(r)` if `n = r^k` for some integer `r`; `Empty`
    /// otherwise.  `k` must be ≥ 1.
    FlintNthRoot { n: String, k: u32 },

    /// Binomial coefficient C(n, k).  Exact arbitrary-precision result.
    FlintBinomial { n: u64, k: u64 },

    // ── DSP: signal processing ───────────────────────────────────────────
    /// Forward Fast Fourier Transform.  Returns a `FloatVec` of 2*N values:
    /// real and imaginary components interleaved (re_0, im_0, re_1, im_1, …).
    DspFft { samples: Vec<f64> },

    /// Inverse Fast Fourier Transform.  Input is 2*N interleaved re/im
    /// components.  Returns N real values (imaginary parts discarded —
    /// caller must ensure conjugate-symmetric input for a real signal).
    DspIfft { spectrum: Vec<f64> },

    /// Apply a Hann window: w[n] = 0.5·(1 − cos(2πn/(N−1))).
    DspHannWindow { samples: Vec<f64> },

    /// Apply a Hamming window: w[n] = 0.54 − 0.46·cos(2πn/(N−1)).
    DspHammingWindow { samples: Vec<f64> },

    // ── IO: file / stream operations ─────────────────────────────────────
    /// Read a file's full contents as bytes (returns Hex-encoded so the
    /// wire format stays consistent).  Empty if path doesn't exist;
    /// Failure on permission errors etc.
    IoReadAll { path: String },

    /// Count newline-separated lines in a file.  Returns BigInt(N) so big
    /// counts work on the wire.
    IoLineCount { path: String },

    /// Compute SHA-256 of a file.  Equivalent to read-then-hash; provided
    /// as one op so callers don't transit large buffers.
    IoSha256OfFile { path: String },

    // ── Graphics: 2-D SVG rendering (no GPU) ─────────────────────────────
    /// Render a proof DAG to SVG.  `nodes` is `(id, label)`; `edges` is
    /// `(from_id, to_id)`.  Layout: simple vertical waterfall with depth
    /// alignment.  Returns the SVG document as a string.
    GraphicsProofGraphSvg {
        nodes: Vec<(String, String)>,
        edges: Vec<(String, String)>,
    },

    /// Render a 1-D bar chart to SVG.  `bars` is `(label, height)`.
    GraphicsBarChartSvg {
        title: String,
        bars: Vec<(String, f64)>,
    },

    // ── Audio: synthesis (PCM / WAV) ─────────────────────────────────────
    /// Sine wave at `frequency_hz` for `duration_ms` at `sample_rate` Hz.
    /// Encoded as little-endian 16-bit PCM in a WAV container.  Returns
    /// the WAV bytes (Hex-encoded for the wire).
    AudioSineWave {
        frequency_hz: f64,
        duration_ms: u32,
        sample_rate: u32,
    },

    /// Pre-baked completion chime — three ascending notes (C5/E5/G5,
    /// 100 ms each).  Used by the Stop hook variant for an audible
    /// "done" signal.
    AudioCompletionChime { sample_rate: u32 },

    // ── FPGA: hardware synthesis (subprocess) ────────────────────────────
    /// Synthesise a Verilog module via yosys (`synth` command).  Returns
    /// the netlist as a string.  Tier 1 (external subprocess).  Failure
    /// if yosys is not on PATH or the verilog source has parse errors.
    FpgaYosysSynth { verilog: String, top_module: String },
}

/// The outcome of a dispatched op.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum CoprocessorOutcome {
    /// A single arbitrary-precision integer (decimal string).
    BigInt(String),

    /// A pair of integers, e.g. canonical (numerator, denominator).
    BigIntPair(String, String),

    /// A list of (prime, multiplicity) pairs from a factorisation.
    Factors(Vec<(String, u32)>),

    /// A boolean answer (e.g. primality test, signature verification).
    Boolean(bool),

    /// A scalar f64 (Vector L²-norm, Tensor trace/determinant, Physics energy).
    Float(f64),

    /// A dense f64 vector (Vector add/scale, Physics Rk4Step state).
    FloatVec(Vec<f64>),

    /// A dense f64 matrix in row-major form (Tensor matmul/transpose).
    FloatMatrix(Vec<Vec<f64>>),

    /// Hex-encoded byte sequence (cryptographic digest).
    Hex(String),

    /// A polynomial in wire format: space-separated decimal integer
    /// coefficients in degree-ascending order.  `"1 0 -1"` encodes `1 − x²`.
    /// The zero polynomial is represented as `"0"`.
    Polynomial(String),

    /// `None` — well-formed input but no answer exists (e.g. non-invertible
    /// modular inverse, or non-exact k-th root).  Distinct from `Failure`,
    /// which means the op itself could not be carried out.
    Empty,

    /// The op could not be executed.  Carries a human-readable reason; the
    /// classifier in `mod.rs` decides how this maps to trust accounting.
    Failure(String),
}

impl CoprocessorOutcome {
    /// Whether this outcome counts as a successful answer (success or `Empty`).
    /// Only `Failure` is treated as a non-answer.
    pub fn is_ok(&self) -> bool {
        !matches!(self, CoprocessorOutcome::Failure(_))
    }
}

/// What a coprocessor backend self-reports as its capability surface.
///
/// Used by `MetaController` to route ops without invoking a backend that
/// will only fail with `Failure("unsupported op")`.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct CoprocessorCapabilities {
    /// Canonical names of supported ops (matching `CoprocessorOp` variant names).
    pub supported_ops: Vec<String>,

    /// Approximate single-op latency in microseconds (median, well-warmed).
    /// Drives the Pareto frontier when MetaController has multiple backends
    /// covering the same op.
    pub typical_latency_us: u64,

    /// Whether this backend is deterministic — same input always produces
    /// same output.  Probabilistic primality (Miller–Rabin) is *true* here
    /// because we always seed deterministically; randomised CAS oracles
    /// (e.g. some Sage operations) would set this `false`.
    pub deterministic: bool,
}

/// Backend liveness signal.
///
/// Distinguishes from trust tier: `Health` is *can the backend run right
/// now*, `TrustTier` is *how much we trust its answer when it does*.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum CoprocessorHealth {
    /// Backend is up and serving normally.
    Healthy,

    /// Backend is up but degraded (e.g. fallback path engaged, library
    /// version mismatch, Julia bridge unreachable but native path live).
    Degraded,

    /// Backend is unreachable.  Dispatch will return `Failure`.
    Unhealthy,
}
