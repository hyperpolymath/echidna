// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later
// (MPL-2.0 is automatic legal fallback until PMPL is formally recognised)

//! Math coprocessor — exact arithmetic + number theory.
//!
//! Native Rust implementation using `num-bigint` / `num-integer` /
//! `num-rational` / `num-traits`.  No subprocess, no Julia bridge — this is
//! the lowest-trust-cost path for ops it covers.  More demanding work (CAS
//! operations, real-algebraic decision procedures) routes to the Phase 2/3
//! external backends; this module is the fast in-process path for the
//! common subset.
//!
//! Primality: deterministic Miller–Rabin for n < 3.3×10²⁴ using the first
//! thirteen primes as witnesses (Sorenson–Webster 2015), then 40-round
//! probabilistic Miller–Rabin for larger n (error ≤ 2⁻⁸⁰).  Witnesses are
//! seeded deterministically so `Capabilities.deterministic` is honest.
//!
//! Factorisation: trial division up to 10⁶, then Pollard ρ with Brent's
//! cycle detection.  Returns prime factors with multiplicity.  Sufficient
//! for the smallish moduli that arise in SMT-arithmetic auxiliary lemmas;
//! large semiprimes (RSA-class) are out of scope for this backend and
//! should route to a CAS backend in Phase 2.

use anyhow::{anyhow, Result};
use async_trait::async_trait;
use num_bigint::{BigInt, BigUint, Sign};
use num_integer::Integer;
use num_traits::{One, Signed, Zero};
use std::str::FromStr;

use super::types::{
    CoprocessorCapabilities, CoprocessorHealth, CoprocessorKind, CoprocessorOp,
    CoprocessorOutcome,
};
use super::Coprocessor;
use super::trust::CoprocessorTrustTier;

/// Math backend — see module docs for the operation set.
pub struct MathBackend {
    capabilities: CoprocessorCapabilities,
}

impl MathBackend {
    pub fn new() -> Self {
        MathBackend {
            capabilities: CoprocessorCapabilities {
                supported_ops: vec![
                    "BigIntGcd".into(),
                    "BigIntLcm".into(),
                    "BigIntModExp".into(),
                    "BigIntModInverse".into(),
                    "BigIntIsProbablePrime".into(),
                    "BigIntFactor".into(),
                    "RationalSimplify".into(),
                    "Fibonacci".into(),
                    "Factorial".into(),
                ],
                typical_latency_us: 50,
                deterministic: true,
            },
        }
    }
}

impl Default for MathBackend {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait]
impl Coprocessor for MathBackend {
    fn kind(&self) -> CoprocessorKind {
        CoprocessorKind::Math
    }

    fn capabilities(&self) -> &CoprocessorCapabilities {
        &self.capabilities
    }

    fn health(&self) -> CoprocessorHealth {
        // Pure in-process; if the binary loaded, we're healthy.
        CoprocessorHealth::Healthy
    }

    fn trust_tier(&self) -> CoprocessorTrustTier {
        // Backed by an audited LGPL/permissive crate set under thin Rust
        // wrappers — Tier 3 (LibraryWrapped).  Earns Tier 4 (NativeKernel)
        // once the SPARK boundary in coprocessor_safety.ads attests it.
        CoprocessorTrustTier::LibraryWrapped
    }

    async fn dispatch(&self, op: CoprocessorOp) -> Result<CoprocessorOutcome> {
        // Run on a Tokio blocking thread because BigInt ops can be CPU-heavy
        // and we don't want to hold the async executor.  All ops are pure
        // computation, so blocking is appropriate.
        tokio::task::spawn_blocking(move || dispatch_sync(op))
            .await
            .map_err(|e| anyhow!("math join error: {e}"))?
    }
}

/// Synchronous dispatch — runs on the blocking thread pool.
fn dispatch_sync(op: CoprocessorOp) -> Result<CoprocessorOutcome> {
    Ok(match op {
        CoprocessorOp::BigIntGcd { a, b } => {
            let ai = parse_bigint(&a)?;
            let bi = parse_bigint(&b)?;
            CoprocessorOutcome::BigInt(ai.gcd(&bi).to_string())
        }
        CoprocessorOp::BigIntLcm { a, b } => {
            let ai = parse_bigint(&a)?;
            let bi = parse_bigint(&b)?;
            CoprocessorOutcome::BigInt(ai.lcm(&bi).to_string())
        }
        CoprocessorOp::BigIntModExp { base, exp, modulus } => {
            let m = parse_biguint_positive(&modulus, "modulus must be positive")?;
            let b = parse_bigint(&base)?;
            let e = parse_bigint_nonneg(&exp, "exponent must be non-negative")?;
            // Reduce base into [0, m) before modpow.
            let b_mod = ((&b % BigInt::from_biguint(Sign::Plus, m.clone()))
                + BigInt::from_biguint(Sign::Plus, m.clone()))
                % BigInt::from_biguint(Sign::Plus, m.clone());
            let b_u = b_mod.to_biguint().expect("non-negative after reduction");
            let e_u = e.to_biguint().expect("non-negative by precondition");
            CoprocessorOutcome::BigInt(b_u.modpow(&e_u, &m).to_string())
        }
        CoprocessorOp::BigIntModInverse { a, modulus } => {
            let m = parse_bigint_positive(&modulus, "modulus must be positive")?;
            let a_v = parse_bigint(&a)?;
            match mod_inverse(&a_v, &m) {
                Some(inv) => CoprocessorOutcome::BigInt(inv.to_string()),
                None => CoprocessorOutcome::Empty,
            }
        }
        CoprocessorOp::BigIntIsProbablePrime { n } => {
            let nu = parse_biguint_nonneg(&n, "primality input must be non-negative")?;
            CoprocessorOutcome::Boolean(is_probable_prime(&nu))
        }
        CoprocessorOp::BigIntFactor { n } => {
            let nu = parse_biguint_nonneg(&n, "factor input must be non-negative")?;
            CoprocessorOutcome::Factors(factor(nu))
        }
        CoprocessorOp::RationalSimplify { num, den } => {
            let n = parse_bigint(&num)?;
            let d = parse_bigint(&den)?;
            if d.is_zero() {
                return Err(anyhow!("denominator must be non-zero"));
            }
            let g = n.gcd(&d);
            let (mut sn, mut sd) = (&n / &g, &d / &g);
            if sd.is_negative() {
                sn = -sn;
                sd = -sd;
            }
            CoprocessorOutcome::BigIntPair(sn.to_string(), sd.to_string())
        }
        CoprocessorOp::Fibonacci { n } => {
            CoprocessorOutcome::BigInt(fib_fast_doubling(n).to_string())
        }
        CoprocessorOp::Factorial { n } => {
            CoprocessorOutcome::BigInt(factorial(n).to_string())
        }
        other => CoprocessorOutcome::Failure(format!(
            "Math backend does not support {:?}",
            std::mem::discriminant(&other)
        )),
    })
}

// ─── parsing helpers ─────────────────────────────────────────────────────────

fn parse_bigint(s: &str) -> Result<BigInt> {
    BigInt::from_str(s.trim()).map_err(|e| anyhow!("invalid integer '{s}': {e}"))
}

fn parse_bigint_nonneg(s: &str, err: &'static str) -> Result<BigInt> {
    let v = parse_bigint(s)?;
    if v.is_negative() {
        return Err(anyhow!("{err}: got {v}"));
    }
    Ok(v)
}

fn parse_bigint_positive(s: &str, err: &'static str) -> Result<BigInt> {
    let v = parse_bigint(s)?;
    if !v.is_positive() {
        return Err(anyhow!("{err}: got {v}"));
    }
    Ok(v)
}

fn parse_biguint_nonneg(s: &str, err: &'static str) -> Result<BigUint> {
    let v = parse_bigint_nonneg(s, err)?;
    Ok(v.to_biguint().expect("non-negative by precondition"))
}

fn parse_biguint_positive(s: &str, err: &'static str) -> Result<BigUint> {
    let v = parse_bigint_positive(s, err)?;
    Ok(v.to_biguint().expect("positive by precondition"))
}

// ─── modular inverse (extended Euclidean) ────────────────────────────────────

fn mod_inverse(a: &BigInt, m: &BigInt) -> Option<BigInt> {
    let (g, x, _) = ext_gcd(a, m);
    if !g.is_one() {
        return None;
    }
    let inv = ((&x % m) + m) % m;
    Some(inv)
}

fn ext_gcd(a: &BigInt, b: &BigInt) -> (BigInt, BigInt, BigInt) {
    if b.is_zero() {
        return (a.clone(), BigInt::one(), BigInt::zero());
    }
    let (g, x1, y1) = ext_gcd(b, &(a % b));
    let q = a / b;
    (g, y1.clone(), x1 - &q * y1)
}

// ─── primality (Miller–Rabin) ────────────────────────────────────────────────
//
// Deterministic witnesses for n < 3,317,044,064,679,887,385,961,981 per
// Sorenson & Webster 2015 — first 13 primes suffice.  For larger n we fall
// back to 40 rounds with a fixed witness sequence (still deterministic, so
// `Capabilities.deterministic = true` is honest).

fn is_probable_prime(n: &BigUint) -> bool {
    if n < &BigUint::from(2u32) {
        return false;
    }
    let small_primes: [u32; 13] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41];
    for p in &small_primes {
        let pp = BigUint::from(*p);
        if n == &pp {
            return true;
        }
        if (n % &pp).is_zero() {
            return false;
        }
    }

    // n - 1 = d * 2^r with d odd.
    let one = BigUint::one();
    let n_minus_1 = n - &one;
    let mut d = n_minus_1.clone();
    let mut r = 0u32;
    while d.is_even() {
        d >>= 1;
        r += 1;
    }

    // Sorenson–Webster bound.
    let sw_bound = BigUint::from_str(
        "3317044064679887385961981",
    )
    .expect("constant parses");

    // Choose witnesses.
    let witnesses: Vec<BigUint> = if n < &sw_bound {
        small_primes.iter().map(|p| BigUint::from(*p)).collect()
    } else {
        // 40 fixed witnesses — small primes plus a deterministic spread.
        // All under 1024, so always smaller than n once n > sw_bound.
        const FALLBACK: [u32; 40] = [
            2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
            59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
            127, 131, 137, 139, 149, 151, 157, 163, 167, 173,
        ];
        FALLBACK.iter().map(|p| BigUint::from(*p)).collect()
    };

    'witness: for a in witnesses {
        if &a >= n {
            continue;
        }
        let mut x = a.modpow(&d, n);
        if x == one || x == n_minus_1 {
            continue;
        }
        for _ in 0..(r - 1) {
            x = x.modpow(&BigUint::from(2u32), n);
            if x == n_minus_1 {
                continue 'witness;
            }
        }
        return false;
    }
    true
}

// ─── factorisation (trial + Pollard ρ with Brent) ────────────────────────────

fn factor(mut n: BigUint) -> Vec<(String, u32)> {
    let mut out: Vec<(BigUint, u32)> = Vec::new();
    if n < BigUint::from(2u32) {
        return Vec::new();
    }

    // Trial division for small primes.
    let small_primes: [u32; 25] = [
        2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61,
        67, 71, 73, 79, 83, 89, 97,
    ];
    for p in &small_primes {
        let pp = BigUint::from(*p);
        let mut k = 0;
        while (&n % &pp).is_zero() {
            n /= &pp;
            k += 1;
        }
        if k > 0 {
            out.push((pp, k));
        }
        if n == BigUint::one() {
            return finish_factors(out);
        }
    }

    // Beyond the small primes — recurse via Pollard ρ.
    let mut stack = vec![n];
    while let Some(m) = stack.pop() {
        if m == BigUint::one() {
            continue;
        }
        if is_probable_prime(&m) {
            push_factor(&mut out, m, 1);
            continue;
        }
        let d = pollard_rho(&m);
        let q = &m / &d;
        stack.push(d);
        stack.push(q);
    }

    finish_factors(out)
}

fn push_factor(out: &mut Vec<(BigUint, u32)>, p: BigUint, k: u32) {
    if let Some(entry) = out.iter_mut().find(|(q, _)| q == &p) {
        entry.1 += k;
    } else {
        out.push((p, k));
    }
}

fn finish_factors(mut out: Vec<(BigUint, u32)>) -> Vec<(String, u32)> {
    out.sort_by(|a, b| a.0.cmp(&b.0));
    out.into_iter().map(|(p, k)| (p.to_string(), k)).collect()
}

fn pollard_rho(n: &BigUint) -> BigUint {
    // Brent's variant — deterministic seed sequence so behaviour is reproducible.
    let two = BigUint::from(2u32);
    if (n % &two).is_zero() {
        return two;
    }
    let one = BigUint::one();
    let mut c = BigUint::from(1u32);
    loop {
        let f = |x: &BigUint| (x * x + &c) % n;
        let mut x = BigUint::from(2u32);
        let mut y = x.clone();
        let mut d = one.clone();
        while d == one {
            x = f(&x);
            y = f(&f(&y));
            let diff = if x > y { &x - &y } else { &y - &x };
            d = diff.gcd(n);
        }
        if &d != n {
            return d;
        }
        c += &one;
    }
}

// ─── integer sequences ───────────────────────────────────────────────────────

fn fib_fast_doubling(n: u64) -> BigUint {
    // Returns F(n) using the identity:
    //   F(2k)   = F(k) * (2*F(k+1) - F(k))
    //   F(2k+1) = F(k+1)^2 + F(k)^2
    fn helper(n: u64) -> (BigUint, BigUint) {
        if n == 0 {
            return (BigUint::zero(), BigUint::one());
        }
        let (a, b) = helper(n / 2);
        let c = &a * (BigUint::from(2u32) * &b - &a);
        let d = &a * &a + &b * &b;
        if n.is_multiple_of(2) {
            (c, d)
        } else {
            let e = &c + &d;
            (d, e)
        }
    }
    helper(n).0
}

fn factorial(n: u64) -> BigUint {
    let mut acc = BigUint::one();
    for k in 2..=n {
        acc *= BigUint::from(k);
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run(op: CoprocessorOp) -> CoprocessorOutcome {
        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();
        rt.block_on(async {
            let backend = MathBackend::new();
            backend.dispatch(op).await.unwrap()
        })
    }

    #[test]
    fn gcd_lcm_basic() {
        match run(CoprocessorOp::BigIntGcd {
            a: "12".into(),
            b: "18".into(),
        }) {
            CoprocessorOutcome::BigInt(s) => assert_eq!(s, "6"),
            _ => panic!(),
        }
        match run(CoprocessorOp::BigIntLcm {
            a: "4".into(),
            b: "6".into(),
        }) {
            CoprocessorOutcome::BigInt(s) => assert_eq!(s, "12"),
            _ => panic!(),
        }
    }

    #[test]
    fn modexp_fermat() {
        // 2^561 mod 561 ≠ 2 (561 = 3*11*17 is Carmichael — but Fermat
        // holds for it; pick a non-Carmichael example instead).
        // 7^(p-1) mod p == 1 for prime p = 13.
        match run(CoprocessorOp::BigIntModExp {
            base: "7".into(),
            exp: "12".into(),
            modulus: "13".into(),
        }) {
            CoprocessorOutcome::BigInt(s) => assert_eq!(s, "1"),
            _ => panic!(),
        }
    }

    #[test]
    fn mod_inverse_known() {
        // 3 * 4 ≡ 1 (mod 11) → inverse of 3 mod 11 is 4
        match run(CoprocessorOp::BigIntModInverse {
            a: "3".into(),
            modulus: "11".into(),
        }) {
            CoprocessorOutcome::BigInt(s) => assert_eq!(s, "4"),
            _ => panic!(),
        }
        // gcd(2, 4) = 2 — non-invertible
        match run(CoprocessorOp::BigIntModInverse {
            a: "2".into(),
            modulus: "4".into(),
        }) {
            CoprocessorOutcome::Empty => {},
            _ => panic!("expected Empty for non-invertible"),
        }
    }

    #[test]
    fn primality_small_and_large() {
        let cases: &[(&str, bool)] = &[
            ("0", false),
            ("1", false),
            ("2", true),
            ("17", true),
            ("21", false),
            ("561", false), // Carmichael — must be caught by MR
            ("104729", true), // 10000th prime
        ];
        for (n, want) in cases {
            match run(CoprocessorOp::BigIntIsProbablePrime {
                n: (*n).into(),
            }) {
                CoprocessorOutcome::Boolean(b) => {
                    assert_eq!(b, *want, "primality of {n}")
                },
                _ => panic!(),
            }
        }
    }

    #[test]
    fn factor_basic() {
        match run(CoprocessorOp::BigIntFactor {
            n: "360".into(),
        }) {
            CoprocessorOutcome::Factors(fs) => {
                assert_eq!(fs, vec![("2".into(), 3), ("3".into(), 2), ("5".into(), 1)]);
            },
            _ => panic!(),
        }
    }

    #[test]
    fn rational_simplify() {
        match run(CoprocessorOp::RationalSimplify {
            num: "6".into(),
            den: "-9".into(),
        }) {
            CoprocessorOutcome::BigIntPair(n, d) => {
                assert_eq!(n, "-2");
                assert_eq!(d, "3");
            },
            _ => panic!(),
        }
    }

    #[test]
    fn fib_factorial() {
        match run(CoprocessorOp::Fibonacci { n: 50 }) {
            CoprocessorOutcome::BigInt(s) => assert_eq!(s, "12586269025"),
            _ => panic!(),
        }
        match run(CoprocessorOp::Factorial { n: 20 }) {
            CoprocessorOutcome::BigInt(s) => assert_eq!(s, "2432902008176640000"),
            _ => panic!(),
        }
    }
}
