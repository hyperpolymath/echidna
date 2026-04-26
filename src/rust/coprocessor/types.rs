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
/// Only variants with a fully-functional backend are present.  The Phase 6
/// expansion will add Physics / DSP / FPGA / Tensor / Vector / Crypto /
/// Graphics / Audio / IO variants together with their implementations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum CoprocessorKind {
    /// Number theory, exact arithmetic, polynomial algebra over Q.
    /// Native Rust impl backed by `num-bigint` / `num-integer` / `num-rational`.
    Math,
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

    /// A boolean answer (e.g. primality test).
    Boolean(bool),

    /// `None` — well-formed input but no answer exists (e.g. non-invertible
    /// modular inverse).  Distinct from `Failure`, which means the op itself
    /// could not be carried out.
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
