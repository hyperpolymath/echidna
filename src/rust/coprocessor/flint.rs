// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later
// (MPL-2.0 is automatic legal fallback until PMPL is formally recognised)

//! FLINT coprocessor backend — integer and polynomial algebra via C FFI.
//!
//! FLINT (Fast Library for Number Theory, LGPL-3) provides highly-optimised
//! arbitrary-precision integer arithmetic (`fmpz`) and polynomial algebra
//! over Z (`fmpz_poly`).  This is the only CAS backend in ECHIDNA that links
//! the library in-process rather than shelling out; it therefore earns
//! `CoprocessorTrustTier::LibraryWrapped` (Tier 3), the same tier as the
//! pure-Rust `MathBackend`.
//!
//! Enabled via `--features flint`.  `build.rs` locates the system FLINT
//! installation via `pkg-config` or a direct `-lflint` probe.  Without the
//! feature, `CoprocessorFactory::native(CoprocessorKind::FlintMath)` returns
//! `None` and all Flint* `CoprocessorOp` variants are unreachable through the
//! factory.
//!
//! ## Supported ops
//!
//! | Op                  | Description                                | Output            |
//! |---------------------|--------------------------------------------|-------------------|
//! | `FlintPolyGcd`      | Primitive GCD of two polynomials over Z    | `Polynomial`      |
//! | `FlintPolyMul`      | Product of two polynomials over Z          | `Polynomial`      |
//! | `FlintPolyRem`      | Pseudo-remainder of f by g over Z          | `Polynomial`      |
//! | `FlintPolyContent`  | GCD of all coefficients of a polynomial    | `BigInt`          |
//! | `FlintNthRoot`      | Exact integer k-th root (or Empty)         | `BigInt` or Empty |
//! | `FlintBinomial`     | Binomial coefficient C(n, k)               | `BigInt`          |
//!
//! ## Polynomial wire format
//!
//! Space-separated decimal integer coefficients in degree-ascending order.
//! `"1 0 -1"` encodes `1 − x²`.  The zero polynomial is represented as
//! `"0"`.  Input with trailing-degree zeros (e.g. `"3 0"`) is accepted;
//! output is always normalised (no trailing-degree zeros).
//!
//! ## Thread safety
//!
//! FLINT is thread-safe from version 2.4 onwards provided each thread owns
//! its `fmpz` / `fmpz_poly` instances exclusively.  All FLINT objects in
//! this module are created on the blocking thread, used, and dropped before
//! the thread returns — no sharing occurs.

use anyhow::{anyhow, Result};
use async_trait::async_trait;
use std::ffi::{CStr, CString};
use std::os::raw::{c_char, c_int};

use super::trust::CoprocessorTrustTier;
use super::types::{
    CoprocessorCapabilities, CoprocessorHealth, CoprocessorKind, CoprocessorOp,
    CoprocessorOutcome,
};
use super::Coprocessor;

// ── Type aliases — must match FLINT's typedefs on 64-bit Linux ───────────────

// FLINT slong = long = i64 on 64-bit Linux
type Slong = i64;
// FLINT ulong = unsigned long = u64 on 64-bit Linux
type Ulong = u64;

// ── Struct layouts (must match C ABI precisely) ───────────────────────────────

/// Rust mirror of `fmpz_poly_struct` from FLINT.
///
/// Three pointer-sized fields (24 bytes on 64-bit):
/// - `coeffs`: pointer to an array of `fmpz` (each stored as `Slong`, either
///   a small value directly or a GMP heap-pointer encoded as a tagged integer)
/// - `alloc`: allocated coefficient count
/// - `length`: used coefficient count (`degree + 1` for non-zero; `0` for zero)
///
/// We never read or write these fields directly — all access goes through
/// FLINT functions.
#[repr(C)]
struct FmpzPolyStruct {
    coeffs: *mut Slong,
    alloc: Slong,
    length: Slong,
}

// ── FFI declarations ──────────────────────────────────────────────────────────
//
// `fmpz_t` in C = `slong[1]`.  Passing `fmpz_t x` to a C function is
// equivalent to passing `slong *x`.  In Rust we pass `*mut Slong` (mutable)
// or `*const Slong` (const-qualified input) as appropriate.
//
// `fmpz_poly_t` = `fmpz_poly_struct[1]`.  We pass `*mut FmpzPolyStruct` or
// `*const FmpzPolyStruct` to the corresponding functions.

extern "C" {
    // ── fmpz lifecycle ────────────────────────────────────────────────────────
    fn fmpz_init(f: *mut Slong);
    fn fmpz_clear(f: *mut Slong);

    // ── fmpz string I/O ───────────────────────────────────────────────────────
    // Returns 0 on success, -1 on malformed input.
    fn fmpz_set_str(f: *mut Slong, s: *const c_char, base: c_int) -> c_int;
    // When `str` is NULL, allocates; caller frees with `flint_free`.
    fn fmpz_get_str(str: *mut c_char, base: c_int, f: *const Slong) -> *mut c_char;

    // ── fmpz arithmetic ───────────────────────────────────────────────────────
    fn fmpz_gcd(f: *mut Slong, g: *const Slong, h: *const Slong);
    // Returns 1 if exact k-th root, 0 if not (r holds floor(|f|^(1/k))).
    fn fmpz_root(r: *mut Slong, f: *const Slong, n: Slong) -> c_int;
    fn fmpz_bin_uiui(res: *mut Slong, n: Ulong, k: Ulong);

    // ── fmpz_poly lifecycle ───────────────────────────────────────────────────
    fn fmpz_poly_init(poly: *mut FmpzPolyStruct);
    fn fmpz_poly_clear(poly: *mut FmpzPolyStruct);

    // ── fmpz_poly access ──────────────────────────────────────────────────────
    fn fmpz_poly_length(poly: *const FmpzPolyStruct) -> Slong;
    fn fmpz_poly_set_coeff_fmpz(poly: *mut FmpzPolyStruct, n: Slong, x: *const Slong);
    fn fmpz_poly_get_coeff_fmpz(x: *mut Slong, poly: *const FmpzPolyStruct, n: Slong);

    // ── fmpz_poly operations ──────────────────────────────────────────────────
    // All three require res to be distinct from the input polys.
    fn fmpz_poly_gcd(
        res: *mut FmpzPolyStruct,
        f: *const FmpzPolyStruct,
        g: *const FmpzPolyStruct,
    );
    fn fmpz_poly_mul(
        res: *mut FmpzPolyStruct,
        f: *const FmpzPolyStruct,
        g: *const FmpzPolyStruct,
    );
    // Pseudo-remainder: lc(g)^d · f = q·g + r; g must be non-zero.
    fn fmpz_poly_pseudo_rem(
        r: *mut FmpzPolyStruct,
        d: *mut Ulong,
        f: *const FmpzPolyStruct,
        g: *const FmpzPolyStruct,
    );
    // Content = GCD of all coefficients (positive; 0 for the zero polynomial).
    fn fmpz_poly_content(res: *mut Slong, poly: *const FmpzPolyStruct);

    // ── FLINT allocator ───────────────────────────────────────────────────────
    fn flint_free(ptr: *mut std::ffi::c_void);
}

// ── RAII wrapper for a single fmpz ───────────────────────────────────────────

struct Fmpz {
    inner: Slong,
}

impl Fmpz {
    fn new() -> Self {
        let mut f = Fmpz { inner: 0 };
        unsafe { fmpz_init(&mut f.inner) };
        f
    }

    fn from_str(s: &str) -> Result<Self> {
        let mut f = Self::new();
        f.set_str(s)?;
        Ok(f)
    }

    fn set_str(&mut self, s: &str) -> Result<()> {
        let cs = CString::new(s.trim())
            .map_err(|e| anyhow!("fmpz string contains NUL byte: {e}"))?;
        let ret = unsafe { fmpz_set_str(&mut self.inner, cs.as_ptr(), 10) };
        if ret == 0 {
            Ok(())
        } else {
            Err(anyhow!("invalid decimal integer string: '{s}'"))
        }
    }

    fn get_str(&self) -> String {
        // FLINT allocates when str argument is NULL; we free with flint_free.
        let ptr: *mut c_char =
            unsafe { fmpz_get_str(std::ptr::null_mut(), 10, &self.inner) };
        if ptr.is_null() {
            return "0".to_string();
        }
        let s = unsafe { CStr::from_ptr(ptr).to_string_lossy().into_owned() };
        unsafe { flint_free(ptr.cast()) };
        s
    }
}

impl Drop for Fmpz {
    fn drop(&mut self) {
        unsafe { fmpz_clear(&mut self.inner) };
    }
}

// ── RAII wrapper for a single fmpz_poly ──────────────────────────────────────

struct FmpzPoly {
    inner: FmpzPolyStruct,
}

impl FmpzPoly {
    fn new() -> Self {
        let mut p = FmpzPoly {
            inner: FmpzPolyStruct {
                coeffs: std::ptr::null_mut(),
                alloc: 0,
                length: 0,
            },
        };
        unsafe { fmpz_poly_init(&mut p.inner) };
        p
    }

    fn length(&self) -> Slong {
        unsafe { fmpz_poly_length(&self.inner) }
    }

    fn is_zero(&self) -> bool {
        self.length() == 0
    }
}

impl Drop for FmpzPoly {
    fn drop(&mut self) {
        unsafe { fmpz_poly_clear(&mut self.inner) };
    }
}

// ── Polynomial wire-format helpers ────────────────────────────────────────────

/// Parse a polynomial from the wire format into an `FmpzPoly`.
///
/// `"1 0 -1"` → `1 + 0·x − x²`.  `"0"` and `""` both produce the zero
/// polynomial.  All other inputs are coefficient strings for increasing
/// degrees, each parsed as an arbitrary-precision decimal integer.
fn parse_poly(s: &str) -> Result<FmpzPoly> {
    let s = s.trim();
    let mut poly = FmpzPoly::new();
    if s == "0" || s.is_empty() {
        return Ok(poly);
    }
    for (i, token) in s.split_whitespace().enumerate() {
        let coeff = Fmpz::from_str(token)?;
        unsafe {
            fmpz_poly_set_coeff_fmpz(&mut poly.inner, i as Slong, &coeff.inner)
        };
    }
    Ok(poly)
}

/// Serialise an `FmpzPoly` to wire format.
///
/// Returns `"0"` for the zero polynomial; otherwise returns space-separated
/// coefficients from degree 0 to degree n (the output is FLINT-normalised,
/// so the leading coefficient is never zero).
fn poly_to_string(poly: &FmpzPoly) -> String {
    let len = poly.length();
    if len == 0 {
        return "0".to_string();
    }
    let mut coeff = Fmpz::new();
    let mut parts = Vec::with_capacity(len as usize);
    for i in 0..len {
        unsafe { fmpz_poly_get_coeff_fmpz(&mut coeff.inner, &poly.inner, i) };
        parts.push(coeff.get_str());
    }
    parts.join(" ")
}

// ── Backend ───────────────────────────────────────────────────────────────────

/// FLINT in-process CAS coprocessor.  Requires `--features flint` and a
/// system FLINT installation discoverable by `build.rs`.
pub struct FlintMathBackend {
    capabilities: CoprocessorCapabilities,
}

impl FlintMathBackend {
    pub fn new() -> Self {
        FlintMathBackend {
            capabilities: CoprocessorCapabilities {
                supported_ops: vec![
                    "FlintPolyGcd".into(),
                    "FlintPolyMul".into(),
                    "FlintPolyRem".into(),
                    "FlintPolyContent".into(),
                    "FlintNthRoot".into(),
                    "FlintBinomial".into(),
                ],
                typical_latency_us: 20,
                deterministic: true,
            },
        }
    }
}

impl Default for FlintMathBackend {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait]
impl Coprocessor for FlintMathBackend {
    fn kind(&self) -> CoprocessorKind {
        CoprocessorKind::FlintMath
    }

    fn capabilities(&self) -> &CoprocessorCapabilities {
        &self.capabilities
    }

    fn health(&self) -> CoprocessorHealth {
        CoprocessorHealth::Healthy
    }

    fn trust_tier(&self) -> CoprocessorTrustTier {
        // FLINT is an LGPL-3 C library with a long public audit history.
        // The Rust wrapper adds no hidden data paths.  Tier 3 (LibraryWrapped).
        // Earns Tier 4 once the SPARK boundary in `coprocessor_safety.ads`
        // formally attests each FFI precondition.
        CoprocessorTrustTier::LibraryWrapped
    }

    async fn dispatch(&self, op: CoprocessorOp) -> Result<CoprocessorOutcome> {
        tokio::task::spawn_blocking(move || dispatch_sync(op))
            .await
            .map_err(|e| anyhow!("flint blocking-thread join error: {e}"))?
    }
}

// ── Synchronous dispatch (runs on the Tokio blocking thread pool) ─────────────

fn dispatch_sync(op: CoprocessorOp) -> Result<CoprocessorOutcome> {
    match op {
        CoprocessorOp::FlintPolyGcd { f, g } => {
            let fp = parse_poly(&f)?;
            let gp = parse_poly(&g)?;
            let mut res = FmpzPoly::new();
            unsafe { fmpz_poly_gcd(&mut res.inner, &fp.inner, &gp.inner) };
            Ok(CoprocessorOutcome::Polynomial(poly_to_string(&res)))
        }

        CoprocessorOp::FlintPolyMul { f, g } => {
            let fp = parse_poly(&f)?;
            let gp = parse_poly(&g)?;
            let mut res = FmpzPoly::new();
            unsafe { fmpz_poly_mul(&mut res.inner, &fp.inner, &gp.inner) };
            Ok(CoprocessorOutcome::Polynomial(poly_to_string(&res)))
        }

        CoprocessorOp::FlintPolyRem { f, g } => {
            let fp = parse_poly(&f)?;
            let gp = parse_poly(&g)?;
            if gp.is_zero() {
                return Err(anyhow!(
                    "FlintPolyRem: divisor must be a non-zero polynomial"
                ));
            }
            let mut rem = FmpzPoly::new();
            let mut d: Ulong = 0;
            unsafe {
                fmpz_poly_pseudo_rem(&mut rem.inner, &mut d, &fp.inner, &gp.inner)
            };
            Ok(CoprocessorOutcome::Polynomial(poly_to_string(&rem)))
        }

        CoprocessorOp::FlintPolyContent { f } => {
            let fp = parse_poly(&f)?;
            let mut content = Fmpz::new();
            unsafe { fmpz_poly_content(&mut content.inner, &fp.inner) };
            Ok(CoprocessorOutcome::BigInt(content.get_str()))
        }

        CoprocessorOp::FlintNthRoot { n, k } => {
            if k == 0 {
                return Err(anyhow!(
                    "FlintNthRoot: exponent k must be ≥ 1, got 0"
                ));
            }
            let nz = Fmpz::from_str(&n)?;
            let mut root = Fmpz::new();
            let exact =
                unsafe { fmpz_root(&mut root.inner, &nz.inner, k as Slong) };
            if exact == 1 {
                Ok(CoprocessorOutcome::BigInt(root.get_str()))
            } else {
                Ok(CoprocessorOutcome::Empty)
            }
        }

        CoprocessorOp::FlintBinomial { n, k } => {
            let mut res = Fmpz::new();
            unsafe { fmpz_bin_uiui(&mut res.inner, n, k) };
            Ok(CoprocessorOutcome::BigInt(res.get_str()))
        }

        other => Ok(CoprocessorOutcome::Failure(format!(
            "FlintMathBackend: op not handled by this backend: {other:?}"
        ))),
    }
}

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn run(op: CoprocessorOp) -> CoprocessorOutcome {
        tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap()
            .block_on(async {
                FlintMathBackend::new().dispatch(op).await.unwrap()
            })
    }

    #[test]
    fn poly_gcd_linear_factor() {
        // GCD(1 − x², x − 1):
        //   1 − x² = −(x−1)(x+1),  x − 1.
        //   Primitive GCD with positive leading coeff = x − 1 → wire: "-1 1"
        match run(CoprocessorOp::FlintPolyGcd {
            f: "1 0 -1".into(),  // 1 − x²
            g: "-1 1".into(),    // x − 1
        }) {
            CoprocessorOutcome::Polynomial(s) => assert_eq!(s, "-1 1"),
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn poly_mul_difference_of_squares() {
        // (1 + x)(1 − x) = 1 − x²  →  wire: "1 0 -1"
        match run(CoprocessorOp::FlintPolyMul {
            f: "1 1".into(),   // 1 + x
            g: "1 -1".into(),  // 1 − x
        }) {
            CoprocessorOutcome::Polynomial(s) => assert_eq!(s, "1 0 -1"),
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn poly_rem_exact_division_is_zero() {
        // pseudo_rem(1 − x², x − 1) = 0  because (x−1) | (1 − x²)
        match run(CoprocessorOp::FlintPolyRem {
            f: "1 0 -1".into(),  // 1 − x²
            g: "-1 1".into(),    // x − 1
        }) {
            CoprocessorOutcome::Polynomial(s) => assert_eq!(s, "0"),
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn poly_content_extracts_gcd_of_coefficients() {
        // content(6 + 4x + 2x²) = gcd(6, 4, 2) = 2
        match run(CoprocessorOp::FlintPolyContent {
            f: "6 4 2".into(),
        }) {
            CoprocessorOutcome::BigInt(s) => assert_eq!(s, "2"),
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn nth_root_exact_cube_and_inexact() {
        // 27 = 3³  →  exact cube root = 3
        match run(CoprocessorOp::FlintNthRoot {
            n: "27".into(),
            k: 3,
        }) {
            CoprocessorOutcome::BigInt(s) => assert_eq!(s, "3"),
            other => panic!("unexpected: {other:?}"),
        }
        // 2 is not a perfect cube  →  Empty
        match run(CoprocessorOp::FlintNthRoot {
            n: "2".into(),
            k: 3,
        }) {
            CoprocessorOutcome::Empty => {},
            other => panic!("expected Empty, got: {other:?}"),
        }
    }

    #[test]
    fn binomial_small_and_medium() {
        // C(10, 3) = 120
        match run(CoprocessorOp::FlintBinomial { n: 10, k: 3 }) {
            CoprocessorOutcome::BigInt(s) => assert_eq!(s, "120"),
            other => panic!("unexpected: {other:?}"),
        }
        // C(100, 2) = 4950
        match run(CoprocessorOp::FlintBinomial { n: 100, k: 2 }) {
            CoprocessorOutcome::BigInt(s) => assert_eq!(s, "4950"),
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn zero_polynomial_gcd() {
        // GCD(0, 0) = 0
        match run(CoprocessorOp::FlintPolyGcd {
            f: "0".into(),
            g: "0".into(),
        }) {
            CoprocessorOutcome::Polynomial(s) => assert_eq!(s, "0"),
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn poly_rem_zero_divisor_returns_err() {
        // Dividing by the zero polynomial must return Err (not panic).
        let result = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap()
            .block_on(async {
                FlintMathBackend::new()
                    .dispatch(CoprocessorOp::FlintPolyRem {
                        f: "1 1".into(),
                        g: "0".into(),
                    })
                    .await
            });
        assert!(result.is_err(), "expected Err for zero divisor");
    }
}
