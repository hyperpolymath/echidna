// SPDX-License-Identifier: MPL-2.0

//! # echidna-core-creusot
//!
//! Creusot-annotated trust-pipeline kernel for ECHIDNA.
//!
//! ## Purpose
//!
//! This crate is a **parallel verification artefact** for the modules in
//! `src/rust/verification/`.  It re-implements the invariant-heavy subset
//! of that surface (`confidence.rs`, `axiom_tracker.rs`) with formal proof
//! annotations in the style of [Creusot](https://github.com/creusot-rs/creusot).
//!
//! The crate is **NOT** a runtime dependency of the main `echidna` binary.
//! It exists so that:
//!
//! 1. Proof obligations can be stated as Creusot contracts (`#[requires]` /
//!    `#[ensures]`) and discharged by SMT solvers (Z3/CVC5/Alt-Ergo — the
//!    same solvers echidna already ships, giving meta-dogfooding).
//! 2. The same invariants compile as `#[test]` functions on stable Rust so
//!    CI always exercises them even without Creusot installed.
//! 3. Annotation work can proceed independently of the main crate's
//!    release cadence.
//!
//! ## Feature flag
//!
//! All Creusot-specific items are gated behind the `creusot` feature.
//! Build without it for normal stable-Rust use:
//!
//! ```text
//! cargo build -p echidna-core-creusot          # stable, no annotations
//! cargo +nightly creusot -p echidna-core-creusot -- --features creusot
//! ```
//!
//! See [`CREUSOT-SETUP.adoc`](../CREUSOT-SETUP.adoc) for full toolchain setup.
//!
//! ## Verification status (honest)
//!
//! The annotations are **stated, not proved**. `creusot-contracts` is not yet
//! a dependency, the nightly pin predates current Creusot, and no CI run has
//! discharged a single obligation. What CI does run is the stable-Rust
//! `#[test]` mirror of every obligation. The crate was formerly named
//! `echidna-core-spark`; it is Creusot (Rust), not SPARK (Ada).
//!
//! ## Roadmap stage
//!
//! This scaffold is the **Stage 8c** artefact of the ECHIDNA ROADMAP
//! ("verified trust kernel scaffold").  The migration roadmap in
//! `.machine_readable/descriptiles/STATE.a2ml` tracks `axiom_tracker.rs` and
//! `confidence.rs` as highest-leverage targets.
//!
//! ## Modules
//!
//! | Module | Source | Invariants |
//! |---|---|---|
//! | (this file) | `confidence.rs` | `TrustLevel` total order, combine monotonicity |
//! | [`axiom_tracker`] | `axiom_tracker.rs` | `DangerLevel` order, classify monotonicity |
//! | [`pareto`] | `verification/pareto.rs` | Dominance irreflexivity / antisymmetry / transitivity, frontier soundness + completeness, best-axis preservation (E10) |
//! | [`estate_layers`] | `corpus/profile.rs` | Layer classification totality (PO-L1/L2), partition (PO-L3), "every ABI is Idris2" (PO-L4) |

pub mod axiom_tracker;
pub mod estate_layers;
pub mod pareto;

// ---------------------------------------------------------------------------
// Creusot prelude — only imported when verifying
// ---------------------------------------------------------------------------

#[cfg(feature = "creusot")]
use creusot_contracts::*;

// ---------------------------------------------------------------------------
// TrustLevel
// ---------------------------------------------------------------------------

/// Five-level trust hierarchy for proof confidence scoring.
///
/// The discriminants are fixed to `1..=5` so that `TrustLevel::value()` is
/// trivially a bijection and the total ordering is the natural integer order.
///
/// ## Creusot proof obligations
///
/// 1. **Total order** — `Level1 < Level2 < Level3 < Level4 < Level5`.
///    Discharged by the `#[ensures]` on [`TrustLevel::value`] combined with
///    the derived `Ord` impl.
/// 2. **Combining decreases** — `combine_trust(a, b) <= min(a, b)`.
///    Discharged by [`combine_trust`]'s `#[ensures]` clause.
/// 3. **Reject caps at Level1** — `DangerLevel::Reject` input to
///    [`compute_trust_level`] always yields `Level1`.
///    Discharged by the `#[ensures]` on [`compute_trust_level`].
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
pub enum TrustLevel {
    /// Large-TCB system, unchecked result, or uses dangerous axioms.
    Level1 = 1,
    /// Single prover result without certificate, but no dangerous axioms.
    Level2 = 2,
    /// Single prover with proof certificate (Alethe, DRAT/LRAT).
    Level3 = 3,
    /// Checked by small-kernel system (Lean4, Coq, Isabelle) with proof certificate.
    Level4 = 4,
    /// Cross-checked by 2+ independent small-kernel systems with certificates.
    Level5 = 5,
}

impl TrustLevel {
    /// Human-readable description of the level.
    pub fn description(&self) -> &'static str {
        match self {
            TrustLevel::Level1 => "Minimal trust: large-TCB, unchecked, or dangerous axioms",
            TrustLevel::Level2 => "Basic trust: single prover, no dangerous axioms",
            TrustLevel::Level3 => "Moderate trust: single prover with proof certificate",
            TrustLevel::Level4 => "High trust: small-kernel prover with certificate",
            TrustLevel::Level5 => "Maximum trust: cross-checked by 2+ small-kernel systems",
        }
    }

    /// Numeric value in `1..=5`.
    ///
    /// ### Creusot contract
    /// ```text
    /// #[ensures(result >= 1 && result <= 5)]
    /// #[ensures(*self == TrustLevel::Level1 ==> result == 1)]
    /// #[ensures(*self == TrustLevel::Level5 ==> result == 5)]
    /// ```
    #[cfg_attr(feature = "creusot", ensures(result >= 1u8 && result <= 5u8))]
    pub fn value(self) -> u8 {
        self as u8
    }

    /// Returns the minimum (lower-trust) of two `TrustLevel` values.
    ///
    /// This is a pure helper used in contract annotations and invariant tests.
    ///
    /// ### Creusot contract
    /// ```text
    /// #[ensures(result <= a)]
    /// #[ensures(result <= b)]
    /// #[ensures(result == a || result == b)]
    /// ```
    #[cfg_attr(feature = "creusot",
        ensures(result <= a),
        ensures(result <= b),
        ensures(result == a || result == b)
    )]
    pub fn min_level(a: TrustLevel, b: TrustLevel) -> TrustLevel {
        if a <= b {
            a
        } else {
            b
        }
    }

    /// Returns the maximum (higher-trust) of two `TrustLevel` values.
    ///
    /// ### Creusot contract
    /// ```text
    /// #[ensures(result >= a)]
    /// #[ensures(result >= b)]
    /// #[ensures(result == a || result == b)]
    /// ```
    #[cfg_attr(feature = "creusot",
        ensures(result >= a),
        ensures(result >= b),
        ensures(result == a || result == b)
    )]
    pub fn max_level(a: TrustLevel, b: TrustLevel) -> TrustLevel {
        if a >= b {
            a
        } else {
            b
        }
    }
}

impl std::fmt::Display for TrustLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Level {} ({})", self.value(), self.description())
    }
}

// ---------------------------------------------------------------------------
// TrustFactors  (self-contained — does not depend on ProverKind from the
//                main crate; mirrors the shape of confidence.rs)
// ---------------------------------------------------------------------------

/// Which prover class produced the result.
///
/// A deliberately minimal enum that covers the distinctions the trust
/// algorithm cares about without pulling in the full 105-variant
/// `ProverKind` from the main `echidna` crate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum ProverClass {
    /// Small-kernel proof assistant (Lean4, Coq, Isabelle, Agda, Metamath,
    /// HOLLight, HOL4, Idris2, F*, Twelf, Nuprl, Minlog).
    SmallKernel,
    /// SMT / first-order ATP solver (Z3, CVC5, Alt-Ergo, Vampire, …).
    SmtOrAtp,
    /// Any other prover not in the above categories.
    Other,
}

/// Input factors for computing the trust level of a single proof result.
///
/// This mirrors `TrustFactors` in `confidence.rs` but uses [`ProverClass`]
/// instead of the full `ProverKind` enum, keeping the crate self-contained.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct TrustFactors {
    /// Class of prover that produced the result.
    pub prover_class: ProverClass,
    /// Number of independent provers that agree on this result.
    pub confirming_provers: u32,
    /// How many of the `confirming_provers` are small-kernel systems whose
    /// certificate for this result was independently verified, the producing
    /// prover included. Level 5 needs at least two. `confirming_provers`
    /// alone cannot decide that, because it does not say what kind of system
    /// each confirmer is. Defaults to 0, so data written before this field
    /// existed can never reach Level 5.
    #[serde(default)]
    pub small_kernel_confirmations: u32,
    /// Whether a proof certificate was produced.
    pub has_certificate: bool,
    /// Whether the certificate was independently verified.
    pub certificate_verified: bool,
    /// Worst axiom danger level found in the proof.
    pub worst_axiom_danger: axiom_tracker::DangerLevel,
    /// Whether the solver binary passed integrity checks.
    pub solver_integrity_ok: bool,
}

// ---------------------------------------------------------------------------
// combine_trust
// ---------------------------------------------------------------------------

/// Combine two trust levels using weakest-link semantics.
///
/// Combining two trust levels can never *increase* trust — the result is
/// always `<= min(a, b)`.  In practice the result equals `min(a, b)`,
/// but the contract is stated as `<=` to leave room for future
/// policies that further penalise combinations.
///
/// ### Invariants (stated as Creusot contracts in comments)
///
/// ```text
/// #[requires(true)]   // no precondition
/// #[ensures(result <= a && result <= b)]
/// #[ensures(result == TrustLevel::min_level(a, b))]
/// ```
///
/// Commutativity: `combine_trust(a, b) == combine_trust(b, a)`.
/// Associativity: `combine_trust(combine_trust(a, b), c) == combine_trust(a, combine_trust(b, c))`.
/// Both follow from the `min` semantics and are testable via [`impl_invariants`].
#[cfg_attr(feature = "creusot",
    ensures(result <= a),
    ensures(result <= b),
    ensures(result == TrustLevel::min_level(a, b))
)]
pub fn combine_trust(a: TrustLevel, b: TrustLevel) -> TrustLevel {
    // Weakest-link: the combined trust is no stronger than the weaker input.
    TrustLevel::min_level(a, b)
}

// ---------------------------------------------------------------------------
// clamp_trust
// ---------------------------------------------------------------------------

/// Clamp a `TrustLevel` to the inclusive range `[min_level, max_level]`.
///
/// ### Precondition
/// `min_level <= max_level`  (caller's responsibility).
///
/// ### Creusot contracts
/// ```text
/// #[requires(min_level <= max_level)]
/// #[ensures(result >= min_level && result <= max_level)]
/// ```
#[cfg_attr(feature = "creusot",
    requires(min_level <= max_level),
    ensures(result >= min_level && result <= max_level)
)]
pub fn clamp_trust(level: TrustLevel, min_level: TrustLevel, max_level: TrustLevel) -> TrustLevel {
    if level < min_level {
        min_level
    } else if level > max_level {
        max_level
    } else {
        level
    }
}

// ---------------------------------------------------------------------------
// compute_trust_level
// ---------------------------------------------------------------------------

/// Compute the trust level for a proof result given its input factors.
///
/// This is the primary trust-scoring function.  The key invariant is:
///
/// > **Reject cap**: if `factors.worst_axiom_danger == DangerLevel::Reject`,
/// > the result is always `TrustLevel::Level1`, regardless of all other factors.
///
/// ### Creusot contracts
/// ```text
/// #[requires(true)]
/// #[ensures(factors.worst_axiom_danger == DangerLevel::Reject ==> result == TrustLevel::Level1)]
/// #[ensures(factors.worst_axiom_danger == DangerLevel::Warning ==> result == TrustLevel::Level1)]
/// #[ensures(!factors.solver_integrity_ok ==> result == TrustLevel::Level1)]
/// // TK-4: Level 4 and above need a small kernel AND a produced, verified certificate.
/// #[ensures(result >= TrustLevel::Level4 ==>
///     factors.prover_class == ProverClass::SmallKernel
///     && factors.has_certificate && factors.certificate_verified)]
/// // TK-5: Level 5 needs two or more small-kernel systems that checked a certificate.
/// #[ensures(result == TrustLevel::Level5 ==>
///     factors.small_kernel_confirmations >= 2 && factors.confirming_provers >= 2)]
/// #[ensures(result >= TrustLevel::Level1 && result <= TrustLevel::Level5)]
/// ```
///
/// TK-4 and TK-5 close two defects in the earlier rule. Level 4 used to fire
/// on `certificate_verified` without `has_certificate`. Level 5 used to check
/// only the producing prover's kernel class, never the confirmers'. Both
/// are checked exhaustively over a finite input space by
/// `impl_invariants::tk_*`, which run on stable Rust in CI. The Creusot
/// annotations are stated, not yet discharged (see the crate header).
#[cfg_attr(feature = "creusot",
    ensures(
        factors.worst_axiom_danger == DangerLevel::Reject
        ==> result == TrustLevel::Level1
    ),
    ensures(
        factors.worst_axiom_danger == DangerLevel::Warning
        ==> result == TrustLevel::Level1
    ),
    ensures(!factors.solver_integrity_ok ==> result == TrustLevel::Level1),
    ensures(
        result >= TrustLevel::Level4
        ==> (factors.prover_class == ProverClass::SmallKernel
             && factors.has_certificate && factors.certificate_verified)
    ),
    ensures(
        result == TrustLevel::Level5
        ==> (factors.small_kernel_confirmations >= 2u32 && factors.confirming_provers >= 2u32)
    ),
    ensures(result >= TrustLevel::Level1 && result <= TrustLevel::Level5)
)]
pub fn compute_trust_level(factors: &TrustFactors) -> TrustLevel {
    use axiom_tracker::DangerLevel;

    // --- Hard caps that always produce Level1 ---

    // Reject-level axioms (believe_me, mk_thm, --type-in-type, etc.) can
    // trivially manufacture false theorems; no certificate or cross-check
    // can rehabilitate a proof that uses them.
    if factors.worst_axiom_danger == DangerLevel::Reject {
        return TrustLevel::Level1;
    }

    // Warning-level axioms (sorry, Admitted, postulate, native_decide) leave
    // proof obligations unfilled.  Cap at Level1.
    if factors.worst_axiom_danger == DangerLevel::Warning {
        return TrustLevel::Level1;
    }

    // If the solver binary failed its BLAKE3/SHAKE3-512 integrity check,
    // any output from it is untrustworthy.
    if !factors.solver_integrity_ok {
        return TrustLevel::Level1;
    }

    let is_small_kernel = factors.prover_class == ProverClass::SmallKernel;
    // A certificate counts only when one was produced AND it was verified;
    // a verification flag on a result with no certificate carries nothing.
    let certified = factors.has_certificate && factors.certificate_verified;
    // Small-kernel confirmations can never exceed the confirming provers;
    // an inconsistent input is read at the lower count.
    let small_kernel_confirmations =
        if factors.small_kernel_confirmations < factors.confirming_provers {
            factors.small_kernel_confirmations
        } else {
            factors.confirming_provers
        };

    // --- Level 5: two or more small-kernel systems checked a certificate ---
    if certified && is_small_kernel && small_kernel_confirmations >= 2 {
        return TrustLevel::Level5;
    }

    // --- Level 4: small-kernel system with a produced, verified certificate ---
    if certified && is_small_kernel {
        return TrustLevel::Level4;
    }

    // --- Level 3: any prover with a produced, verified certificate ---
    if certified {
        return TrustLevel::Level3;
    }

    // --- Level 3: cross-checked by 2+ provers (no certificate) ---
    if factors.confirming_provers >= 2 {
        return TrustLevel::Level3;
    }

    // --- Level 2: single prover, no dangerous axioms (already checked above) ---
    TrustLevel::Level2
}

// ---------------------------------------------------------------------------
// Invariant test suite  (impl_invariants)
// ---------------------------------------------------------------------------

/// Invariant proofs stated as both `#[test]` functions (always run on
/// stable Rust) and as Creusot lemma stubs (run when `--features creusot`).
///
/// Each test corresponds to a named proof obligation from the SPARK
/// adoption plan (`docs/design/SPARK_ADOPTION_PLAN.adoc`, §M3).
pub mod impl_invariants {
    // These imports are only used in #[test] functions.  The module itself
    // is pub so that Creusot can see the lemma stubs, but the items are
    // only exercised at test time — hence the allow.
    #[allow(unused_imports)]
    use crate::{
        axiom_tracker::DangerLevel, clamp_trust, combine_trust, compute_trust_level, ProverClass,
        TrustFactors, TrustLevel,
    };

    // -----------------------------------------------------------------------
    // Property: TrustLevel is totally ordered (Level1 < Level2 < … < Level5)
    // -----------------------------------------------------------------------

    /// **PO-1** Total order: `Level1 < Level2 < Level3 < Level4 < Level5`.
    ///
    /// Creusot lemma stub:
    /// ```text
    /// #[logic]
    /// fn trust_level_total_order() -> bool {
    ///     TrustLevel::Level1 < TrustLevel::Level2
    ///     && TrustLevel::Level2 < TrustLevel::Level3
    ///     && TrustLevel::Level3 < TrustLevel::Level4
    ///     && TrustLevel::Level4 < TrustLevel::Level5
    /// }
    /// #[ensures(trust_level_total_order())]
    /// fn lemma_trust_total_order() {}
    /// ```
    #[test]
    fn po1_trust_level_total_order() {
        assert!(TrustLevel::Level1 < TrustLevel::Level2);
        assert!(TrustLevel::Level2 < TrustLevel::Level3);
        assert!(TrustLevel::Level3 < TrustLevel::Level4);
        assert!(TrustLevel::Level4 < TrustLevel::Level5);
    }

    // -----------------------------------------------------------------------
    // Property: combine_trust(a, b) <= min(a, b)
    // -----------------------------------------------------------------------

    /// **PO-2** Weakest-link: combining trust can only decrease (or preserve)
    /// the trust level.
    ///
    /// Creusot lemma stub:
    /// ```text
    /// #[logic]
    /// fn combine_decreases(a: TrustLevel, b: TrustLevel) -> bool {
    ///     combine_trust(a, b) <= a && combine_trust(a, b) <= b
    /// }
    /// ```
    #[test]
    fn po2_combine_trust_decreases() {
        use crate::TrustLevel::*;
        let levels = [Level1, Level2, Level3, Level4, Level5];
        for &a in &levels {
            for &b in &levels {
                let combined = combine_trust(a, b);
                assert!(
                    combined <= a,
                    "combine_trust({a:?}, {b:?}) = {combined:?} > {a:?}"
                );
                assert!(
                    combined <= b,
                    "combine_trust({a:?}, {b:?}) = {combined:?} > {b:?}"
                );
            }
        }
    }

    /// **PO-3** Commutativity: `combine_trust(a, b) == combine_trust(b, a)`.
    #[test]
    fn po3_combine_trust_commutative() {
        use crate::TrustLevel::*;
        let levels = [Level1, Level2, Level3, Level4, Level5];
        for &a in &levels {
            for &b in &levels {
                assert_eq!(
                    combine_trust(a, b),
                    combine_trust(b, a),
                    "combine_trust is not commutative for {a:?}, {b:?}"
                );
            }
        }
    }

    /// **PO-4** Associativity:
    /// `combine_trust(combine_trust(a, b), c) == combine_trust(a, combine_trust(b, c))`.
    #[test]
    fn po4_combine_trust_associative() {
        use crate::TrustLevel::*;
        let levels = [Level1, Level2, Level3, Level4, Level5];
        for &a in &levels {
            for &b in &levels {
                for &c in &levels {
                    let lhs = combine_trust(combine_trust(a, b), c);
                    let rhs = combine_trust(a, combine_trust(b, c));
                    assert_eq!(
                        lhs, rhs,
                        "combine_trust not associative for {a:?}, {b:?}, {c:?}"
                    );
                }
            }
        }
    }

    // -----------------------------------------------------------------------
    // Property: DangerLevel::Reject always yields TrustLevel::Level1
    // -----------------------------------------------------------------------

    /// **PO-5** Reject cap: no matter what other factors are set, a
    /// `DangerLevel::Reject` axiom usage always results in `Level1`.
    ///
    /// This is the single most important soundness property of the trust
    /// pipeline: a proof containing `believe_me` or `mk_thm` must NEVER
    /// receive a trust level above 1, even with perfect certificates and
    /// cross-checking.
    #[test]
    fn po5_reject_danger_always_level1() {
        let factors = TrustFactors {
            prover_class: ProverClass::SmallKernel,
            confirming_provers: 10, // maximum cross-checking
            small_kernel_confirmations: 10,
            has_certificate: true,
            certificate_verified: true,
            worst_axiom_danger: DangerLevel::Reject,
            solver_integrity_ok: true,
        };
        assert_eq!(
            compute_trust_level(&factors),
            TrustLevel::Level1,
            "DangerLevel::Reject must always cap trust at Level1"
        );
    }

    // -----------------------------------------------------------------------
    // Property: integrity failure always yields TrustLevel::Level1
    // -----------------------------------------------------------------------

    /// **PO-6** Integrity cap: a failed solver-binary integrity check always
    /// results in `Level1`, regardless of certificates or cross-checking.
    #[test]
    fn po6_integrity_failure_always_level1() {
        let factors = TrustFactors {
            prover_class: ProverClass::SmallKernel,
            confirming_provers: 5,
            small_kernel_confirmations: 5,
            has_certificate: true,
            certificate_verified: true,
            worst_axiom_danger: DangerLevel::Safe,
            solver_integrity_ok: false, // <-- integrity failure
        };
        assert_eq!(
            compute_trust_level(&factors),
            TrustLevel::Level1,
            "Integrity failure must always cap trust at Level1"
        );
    }

    // -----------------------------------------------------------------------
    // Property: clamp_trust always returns a value within [min, max]
    // -----------------------------------------------------------------------

    /// **PO-7** Clamp is within bounds: `min_level <= clamp_trust(x, min, max) <= max_level`.
    #[test]
    fn po7_clamp_trust_in_bounds() {
        use crate::TrustLevel::*;
        let levels = [Level1, Level2, Level3, Level4, Level5];
        for &lo in &levels {
            for &hi in &levels {
                if lo > hi {
                    continue; // precondition not satisfied — skip
                }
                for &x in &levels {
                    let clamped = clamp_trust(x, lo, hi);
                    assert!(
                        clamped >= lo && clamped <= hi,
                        "clamp_trust({x:?}, {lo:?}, {hi:?}) = {clamped:?} out of bounds"
                    );
                }
            }
        }
    }

    // -----------------------------------------------------------------------
    // Property: value() is a bijection to 1..=5 preserving order
    // -----------------------------------------------------------------------

    /// **PO-8** Value bijection: `TrustLevel::value()` maps each level to a
    /// distinct value in `1..=5`, preserving the order.
    #[test]
    fn po8_value_bijection_and_order_preserving() {
        let pairs = [
            (TrustLevel::Level1, 1u8),
            (TrustLevel::Level2, 2),
            (TrustLevel::Level3, 3),
            (TrustLevel::Level4, 4),
            (TrustLevel::Level5, 5),
        ];
        for (level, expected) in pairs {
            assert_eq!(level.value(), expected);
        }
        // Strictly increasing
        assert!(TrustLevel::Level1.value() < TrustLevel::Level2.value());
        assert!(TrustLevel::Level2.value() < TrustLevel::Level3.value());
        assert!(TrustLevel::Level3.value() < TrustLevel::Level4.value());
        assert!(TrustLevel::Level4.value() < TrustLevel::Level5.value());
    }

    // -----------------------------------------------------------------------
    // TK-4 / TK-5: the certificate and kernel conditions of Levels 4 and 5,
    // checked over every input in a finite space (bounded model check).
    // -----------------------------------------------------------------------

    /// Every `TrustFactors` with counts in `0..=4`, both certificate flags,
    /// every danger level, both integrity states and every prover class.
    #[cfg(test)]
    fn all_factors() -> Vec<TrustFactors> {
        use crate::axiom_tracker::DangerLevel::{Noted, Reject, Safe, Warning};
        let mut out = Vec::new();
        for pc in [
            ProverClass::SmallKernel,
            ProverClass::SmtOrAtp,
            ProverClass::Other,
        ] {
            for confirming_provers in 0u32..=4 {
                for small_kernel_confirmations in 0u32..=4 {
                    for has_certificate in [false, true] {
                        for certificate_verified in [false, true] {
                            for worst_axiom_danger in [Safe, Noted, Warning, Reject] {
                                for solver_integrity_ok in [false, true] {
                                    out.push(TrustFactors {
                                        prover_class: pc,
                                        confirming_provers,
                                        small_kernel_confirmations,
                                        has_certificate,
                                        certificate_verified,
                                        worst_axiom_danger,
                                        solver_integrity_ok,
                                    });
                                }
                            }
                        }
                    }
                }
            }
        }
        out
    }

    /// **TK-4** Level 4 and above need a small-kernel prover with a
    /// certificate that was both produced and verified.
    #[test]
    fn tk4_level4_needs_small_kernel_and_produced_verified_certificate() {
        for f in all_factors() {
            if compute_trust_level(&f) >= TrustLevel::Level4 {
                assert!(
                    f.prover_class == ProverClass::SmallKernel
                        && f.has_certificate
                        && f.certificate_verified,
                    "TK-4 violated by {f:?}"
                );
            }
        }
    }

    /// **TK-5** Level 5 needs two or more small-kernel systems that checked a
    /// certificate, and two or more confirming provers.
    #[test]
    fn tk5_level5_needs_two_small_kernel_confirmations() {
        for f in all_factors() {
            if compute_trust_level(&f) == TrustLevel::Level5 {
                assert!(
                    f.small_kernel_confirmations >= 2 && f.confirming_provers >= 2,
                    "TK-5 violated by {f:?}"
                );
            }
        }
    }

    /// **TK-6** Monotone in the evidence: one more confirming prover, one more
    /// small-kernel confirmation, or a produced and verified certificate
    /// never lowers the level.
    #[test]
    fn tk6_more_evidence_never_lowers_trust() {
        for f in all_factors() {
            let base = compute_trust_level(&f);
            let more_provers = TrustFactors {
                confirming_provers: f.confirming_provers + 1,
                ..f.clone()
            };
            let more_kernels = TrustFactors {
                confirming_provers: f.confirming_provers + 1,
                small_kernel_confirmations: f.small_kernel_confirmations + 1,
                ..f.clone()
            };
            let certified = TrustFactors {
                has_certificate: true,
                certificate_verified: true,
                ..f.clone()
            };
            for g in [more_provers, more_kernels, certified] {
                assert!(
                    compute_trust_level(&g) >= base,
                    "TK-6: {g:?} scored below {f:?}"
                );
            }
        }
    }

    /// Regression: the two defects found in the 2026-11-09 proof audit.
    #[test]
    fn tk_regressions_for_the_audited_defects() {
        use crate::axiom_tracker::DangerLevel::Safe;
        // Level 5 from one small-kernel prover plus an SMT confirmer: the old
        // rule saw only the producing prover's class and returned Level5.
        let one_kernel = TrustFactors {
            prover_class: ProverClass::SmallKernel,
            confirming_provers: 2,
            small_kernel_confirmations: 1,
            has_certificate: true,
            certificate_verified: true,
            worst_axiom_danger: Safe,
            solver_integrity_ok: true,
        };
        assert_eq!(compute_trust_level(&one_kernel), TrustLevel::Level4);
        // Level 4 without a produced certificate: the old rule returned Level4.
        let no_certificate = TrustFactors {
            prover_class: ProverClass::SmallKernel,
            confirming_provers: 1,
            small_kernel_confirmations: 1,
            has_certificate: false,
            certificate_verified: true,
            worst_axiom_danger: Safe,
            solver_integrity_ok: true,
        };
        assert_eq!(compute_trust_level(&no_certificate), TrustLevel::Level2);
    }

    // -----------------------------------------------------------------------
    // Property: compute_trust_level output is always in [Level1, Level5]
    // -----------------------------------------------------------------------

    /// **PO-9** Range: `compute_trust_level` never returns a value outside
    /// `Level1..=Level5` (trivially true by type, but validated exhaustively
    /// for documentation purposes).
    #[test]
    fn po9_compute_trust_level_range() {
        use crate::axiom_tracker::DangerLevel::{Noted, Reject, Safe, Warning};
        use crate::TrustLevel::{Level1, Level5};
        let danger_levels = [Safe, Noted, Warning, Reject];
        let prover_classes = [
            ProverClass::SmallKernel,
            ProverClass::SmtOrAtp,
            ProverClass::Other,
        ];
        for &dl in &danger_levels {
            for &pc in &prover_classes {
                for &certs in &[false, true] {
                    for &integrity in &[false, true] {
                        for confirming in [1u32, 2, 5] {
                            let f = TrustFactors {
                                prover_class: pc,
                                confirming_provers: confirming,
                                small_kernel_confirmations: confirming,
                                has_certificate: certs,
                                certificate_verified: certs,
                                worst_axiom_danger: dl,
                                solver_integrity_ok: integrity,
                            };
                            let result = compute_trust_level(&f);
                            assert!(
                                result >= Level1 && result <= Level5,
                                "compute_trust_level returned out-of-range value"
                            );
                        }
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use axiom_tracker::DangerLevel;

    #[test]
    fn test_small_kernel_cross_checked_with_certs_level5() {
        let factors = TrustFactors {
            prover_class: ProverClass::SmallKernel,
            confirming_provers: 2,
            small_kernel_confirmations: 2,
            has_certificate: true,
            certificate_verified: true,
            worst_axiom_danger: DangerLevel::Safe,
            solver_integrity_ok: true,
        };
        assert_eq!(compute_trust_level(&factors), TrustLevel::Level5);
    }

    #[test]
    fn test_small_kernel_with_cert_level4() {
        let factors = TrustFactors {
            prover_class: ProverClass::SmallKernel,
            confirming_provers: 1,
            small_kernel_confirmations: 0,
            has_certificate: true,
            certificate_verified: true,
            worst_axiom_danger: DangerLevel::Safe,
            solver_integrity_ok: true,
        };
        assert_eq!(compute_trust_level(&factors), TrustLevel::Level4);
    }

    #[test]
    fn test_smt_with_cert_level3() {
        let factors = TrustFactors {
            prover_class: ProverClass::SmtOrAtp,
            confirming_provers: 1,
            small_kernel_confirmations: 0,
            has_certificate: true,
            certificate_verified: true,
            worst_axiom_danger: DangerLevel::Safe,
            solver_integrity_ok: true,
        };
        assert_eq!(compute_trust_level(&factors), TrustLevel::Level3);
    }

    #[test]
    fn test_single_solver_no_cert_level2() {
        let factors = TrustFactors {
            prover_class: ProverClass::SmtOrAtp,
            confirming_provers: 1,
            small_kernel_confirmations: 0,
            has_certificate: false,
            certificate_verified: false,
            worst_axiom_danger: DangerLevel::Safe,
            solver_integrity_ok: true,
        };
        assert_eq!(compute_trust_level(&factors), TrustLevel::Level2);
    }

    #[test]
    fn test_noted_axiom_still_allows_level4() {
        // Classical axioms (Noted) do not cap the trust level.
        let factors = TrustFactors {
            prover_class: ProverClass::SmallKernel,
            confirming_provers: 1,
            small_kernel_confirmations: 0,
            has_certificate: true,
            certificate_verified: true,
            worst_axiom_danger: DangerLevel::Noted,
            solver_integrity_ok: true,
        };
        // Noted axioms are allowed; Level4 is reachable.
        assert_eq!(compute_trust_level(&factors), TrustLevel::Level4);
    }

    #[test]
    fn test_display_format() {
        let level = TrustLevel::Level3;
        let s = format!("{level}");
        assert!(s.contains("Level 3"));
    }
}
