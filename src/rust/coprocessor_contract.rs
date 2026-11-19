// SPDX-License-Identifier: MPL-2.0

//! Producer side of the `echidna.coprocessor.result/1` contract.
//!
//! `echidna coprocessor dispatch` reads one `echidna.coprocessor.request/1`
//! object and prints one [`CoprocessorResult`] as JCS-canonical I-JSON on
//! stdout. `echidna coprocessor capabilities` prints one
//! [`CapabilitiesReport`]. This module holds the types and the pure
//! request-to-result function; `src/rust/cli/coprocessor.rs` does the I/O.
//!
//! Trust rule: a coprocessor answer is a hint, never a proof. No status
//! says `verified`, `proved` or `proven`, and `trust.proof` is the type
//! [`NotAProof`], which can only serialise as `false`.
//!
//! See `docs/COPROCESSOR-CONTRACT.adoc` for the contract.

use std::time::Instant;

use serde::{Serialize, Serializer};
use serde_json::Value;

use crate::coprocessor::{
    Coprocessor, CoprocessorFactory, CoprocessorHealth, CoprocessorKind, CoprocessorOp,
    CoprocessorOutcome, CoprocessorTrustTier,
};
pub use crate::prove_contract::ECHIDNA_VERSION;
use echidna_core::prove_result::MAX_SAFE_INTEGER;

/// The request schema this module accepts.
pub const REQUEST_SCHEMA: &str = "echidna.coprocessor.request/1";

/// The result schema this module emits.
pub const RESULT_SCHEMA: &str = "echidna.coprocessor.result/1";

/// The capabilities schema this module emits.
pub const CAPABILITIES_SCHEMA: &str = "echidna.coprocessor.capabilities/1";

/// The value `trust.proof` always carries. A coprocessor answer is a hint.
pub const IS_PROOF: bool = false;

/// The fail-closed allow-list of kinds that contract version 1 exposes.
///
/// Only in-process kinds that start no external program and read no file.
/// Every kind not listed here answers `unavailable`, and its backend is
/// never constructed. `FlintMath` is listed only when the `flint` feature
/// is compiled in.
#[cfg(not(feature = "flint"))]
pub const EXPOSED_KINDS: &[CoprocessorKind] = &[
    CoprocessorKind::Math,
    CoprocessorKind::Vector,
    CoprocessorKind::Tensor,
    CoprocessorKind::Crypto,
    CoprocessorKind::Dsp,
    CoprocessorKind::Physics,
];

/// The fail-closed allow-list of kinds that contract version 1 exposes.
///
/// Only in-process kinds that start no external program and read no file.
/// Every kind not listed here answers `unavailable`, and its backend is
/// never constructed. `FlintMath` is listed only when the `flint` feature
/// is compiled in.
#[cfg(feature = "flint")]
pub const EXPOSED_KINDS: &[CoprocessorKind] = &[
    CoprocessorKind::Math,
    CoprocessorKind::Vector,
    CoprocessorKind::Tensor,
    CoprocessorKind::Crypto,
    CoprocessorKind::Dsp,
    CoprocessorKind::Physics,
    CoprocessorKind::FlintMath,
];

/// Every `CoprocessorKind` variant, in discriminant order.
pub const ALL_KINDS: [CoprocessorKind; 16] = [
    CoprocessorKind::Math,
    CoprocessorKind::Vector,
    CoprocessorKind::Tensor,
    CoprocessorKind::Crypto,
    CoprocessorKind::Physics,
    CoprocessorKind::FlintMath,
    CoprocessorKind::Dsp,
    CoprocessorKind::Io,
    CoprocessorKind::Graphics,
    CoprocessorKind::Audio,
    CoprocessorKind::Fpga,
    CoprocessorKind::PariGp,
    CoprocessorKind::Maxima,
    CoprocessorKind::Singular,
    CoprocessorKind::Gap,
    CoprocessorKind::Macaulay2,
];

/// Whether contract version 1 exposes `kind`.
pub fn is_exposed(kind: CoprocessorKind) -> bool {
    EXPOSED_KINDS.contains(&kind)
}

/// The closed status vocabulary of a coprocessor result.
///
/// There is deliberately no `verified`, `proved` or `proven`: a
/// coprocessor answer is a hint.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum CoprocessorStatus {
    /// The backend returned an outcome other than `Failure`.
    Computed,
    /// The backend returned `Failure`: the input was well formed, and the
    /// operation refused it.
    Declined,
    /// The kind is not exposed, has no backend in this build, or its
    /// backend is not healthy.
    Unavailable,
    /// The request is malformed, dispatch failed, or the outcome cannot be
    /// written as I-JSON.
    Error,
}

impl CoprocessorStatus {
    /// Every status, in contract order.
    pub const ALL: [CoprocessorStatus; 4] = [
        CoprocessorStatus::Computed,
        CoprocessorStatus::Declined,
        CoprocessorStatus::Unavailable,
        CoprocessorStatus::Error,
    ];

    /// The wire string of this status.
    pub fn as_str(self) -> &'static str {
        match self {
            CoprocessorStatus::Computed => "computed",
            CoprocessorStatus::Declined => "declined",
            CoprocessorStatus::Unavailable => "unavailable",
            CoprocessorStatus::Error => "error",
        }
    }

    /// The process exit code for this status: 0 only for `computed`.
    pub fn exit_code(self) -> i32 {
        match self {
            CoprocessorStatus::Computed => 0,
            _ => 1,
        }
    }
}

/// Marker that a coprocessor answer is not a proof.
///
/// It has one value and serialises as [`IS_PROOF`] (`false`), so no code
/// path can emit `trust.proof: true`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct NotAProof;

impl Serialize for NotAProof {
    /// Write the JSON literal `false`.
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.serialize_bool(IS_PROOF)
    }
}

/// The `trust` object: the backend's tier, and the fixed `proof: false`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CoprocessorTrust {
    /// The `CoprocessorTrustTier` variant name, or `None` when no backend ran.
    pub tier: Option<String>,
    /// The tier's `u8` rank, or `None` when no backend ran.
    pub rank: Option<u8>,
    /// Always `false`.
    pub proof: NotAProof,
}

impl CoprocessorTrust {
    /// The trust object for a backend of tier `tier`.
    pub fn of(tier: CoprocessorTrustTier) -> Self {
        CoprocessorTrust {
            tier: Some(format!("{tier:?}")),
            rank: Some(tier.as_u8()),
            proof: NotAProof,
        }
    }

    /// The trust object when no backend was constructed.
    pub fn none() -> Self {
        CoprocessorTrust {
            tier: None,
            rank: None,
            proof: NotAProof,
        }
    }
}

/// One `echidna.coprocessor.result/1` object.
#[derive(Debug, Clone, Serialize)]
pub struct CoprocessorResult {
    /// Always [`RESULT_SCHEMA`].
    pub schema: &'static str,
    /// The verdict, from the closed vocabulary.
    pub status: CoprocessorStatus,
    /// The kind's variant name, or `None` when the request did not parse.
    pub kind: Option<String>,
    /// The op's variant name, or `None` when the request did not parse.
    pub op: Option<String>,
    /// The backend outcome (`computed` and `declined` only).
    pub outcome: Option<CoprocessorOutcome>,
    /// Human-readable diagnostic; may be empty.
    pub message: String,
    /// The backend's trust tier and the fixed `proof: false`.
    pub trust: CoprocessorTrust,
    /// The backend's `deterministic` capability, or `None` with no backend.
    pub deterministic: Option<bool>,
    /// Wall-clock time of the whole request, in milliseconds.
    pub duration_ms: u64,
    /// The ECHIDNA version that emitted this object.
    pub echidna_version: String,
}

/// What a result says about the backend that served it.
#[derive(Debug, Clone, Copy)]
pub struct BackendFacts {
    /// The backend's trust tier.
    pub tier: CoprocessorTrustTier,
    /// The backend's `deterministic` capability.
    pub deterministic: bool,
}

impl BackendFacts {
    /// Read the facts from a constructed backend.
    pub fn of(backend: &dyn Coprocessor) -> Self {
        BackendFacts {
            tier: backend.trust_tier(),
            deterministic: backend.capabilities().deterministic,
        }
    }
}

impl CoprocessorResult {
    /// Build a result with the current schema and version.
    ///
    /// `duration_ms` saturates at 2^53 - 1.
    pub fn new(
        status: CoprocessorStatus,
        names: Option<(CoprocessorKind, &str)>,
        outcome: Option<CoprocessorOutcome>,
        message: impl Into<String>,
        backend: Option<BackendFacts>,
        duration_ms: u64,
    ) -> Self {
        CoprocessorResult {
            schema: RESULT_SCHEMA,
            status,
            kind: names.map(|(k, _)| kind_name(k)),
            op: names.map(|(_, o)| o.to_string()),
            outcome,
            message: message.into(),
            trust: backend
                .map(|b| CoprocessorTrust::of(b.tier))
                .unwrap_or_else(CoprocessorTrust::none),
            deterministic: backend.map(|b| b.deterministic),
            duration_ms: duration_ms.min(MAX_SAFE_INTEGER),
            echidna_version: ECHIDNA_VERSION.to_string(),
        }
    }

    /// An `error` result for a request that did not parse.
    pub fn malformed(message: impl Into<String>, duration_ms: u64) -> Self {
        CoprocessorResult::new(
            CoprocessorStatus::Error,
            None,
            None,
            message,
            None,
            duration_ms,
        )
    }

    /// Serialise to the one-line JCS-canonical I-JSON form (no newline).
    ///
    /// Fails rather than emit a non-finite float or an unsafe integer.
    pub fn to_jcs(&self) -> Result<String, String> {
        if self.duration_ms > MAX_SAFE_INTEGER {
            return Err(format!(
                "duration_ms {} exceeds the I-JSON safe range",
                self.duration_ms
            ));
        }
        if let Some(o) = &self.outcome {
            if !outcome_is_finite(o) {
                return Err(NON_FINITE.to_string());
            }
        }
        serde_json_canonicalizer::to_string(self).map_err(|e| e.to_string())
    }
}

/// The message for an outcome that holds NaN or an infinity.
const NON_FINITE: &str =
    "the outcome holds a non-finite float (NaN or infinity), which I-JSON cannot carry";

/// Whether every float in `outcome` is finite (I-JSON has no NaN or infinity).
pub fn outcome_is_finite(outcome: &CoprocessorOutcome) -> bool {
    match outcome {
        CoprocessorOutcome::Float(x) => x.is_finite(),
        CoprocessorOutcome::FloatVec(v) => v.iter().all(|x| x.is_finite()),
        CoprocessorOutcome::FloatMatrix(m) => m.iter().flatten().all(|x| x.is_finite()),
        CoprocessorOutcome::BigInt(_)
        | CoprocessorOutcome::BigIntPair(_, _)
        | CoprocessorOutcome::Factors(_)
        | CoprocessorOutcome::Boolean(_)
        | CoprocessorOutcome::Hex(_)
        | CoprocessorOutcome::Polynomial(_)
        | CoprocessorOutcome::Text(_)
        | CoprocessorOutcome::Empty
        | CoprocessorOutcome::Failure(_) => true,
    }
}

/// The wire name of `kind` (its serde form, which is the variant name).
pub fn kind_name(kind: CoprocessorKind) -> String {
    match serde_json::to_value(kind) {
        Ok(Value::String(s)) => s,
        _ => format!("{kind:?}"),
    }
}

/// The wire name of `op` (the key of its externally tagged serde form).
pub fn op_name(op: &CoprocessorOp) -> String {
    match serde_json::to_value(op) {
        Ok(Value::Object(m)) if m.len() == 1 => m.keys().next().cloned().unwrap_or_default(),
        Ok(Value::String(s)) => s,
        _ => String::new(),
    }
}

/// A request that parsed: the kind and the op.
#[derive(Debug, Clone)]
pub struct CoprocessorRequest {
    /// The requested kind.
    pub kind: CoprocessorKind,
    /// The requested op, in the existing `CoprocessorOp` serde form.
    pub op: CoprocessorOp,
}

/// Parse one `echidna.coprocessor.request/1` object.
///
/// Rejects anything that is not a JSON object with exactly the keys
/// `schema`, `kind` and `op`, a schema other than [`REQUEST_SCHEMA`], an
/// unknown kind, and an op that does not parse as a `CoprocessorOp`.
pub fn parse_request(input: &str) -> Result<CoprocessorRequest, String> {
    let value: Value =
        serde_json::from_str(input).map_err(|e| format!("request is not JSON: {e}"))?;
    let Value::Object(map) = value else {
        return Err("request must be a JSON object".into());
    };
    if let Some(extra) = map
        .keys()
        .find(|k| !matches!(k.as_str(), "schema" | "kind" | "op"))
    {
        return Err(format!("unknown top-level key {extra:?}"));
    }
    match map.get("schema") {
        Some(Value::String(s)) if s == REQUEST_SCHEMA => {},
        Some(Value::String(s)) => return Err(format!("unsupported schema {s:?}")),
        Some(_) => return Err("`schema` must be a string".into()),
        None => return Err("missing key `schema`".into()),
    }
    let kind_v = map.get("kind").ok_or("missing key `kind`")?;
    let kind: CoprocessorKind = serde_json::from_value(kind_v.clone())
        .map_err(|e| format!("unknown kind {kind_v}: {e}"))?;
    let op_v = map.get("op").ok_or("missing key `op`")?;
    let op: CoprocessorOp =
        serde_json::from_value(op_v.clone()).map_err(|e| format!("op does not parse: {e}"))?;
    Ok(CoprocessorRequest { kind, op })
}

/// Turn a backend outcome into a result (`computed`, `declined` or `error`).
///
/// A `Failure` outcome is `declined`; an outcome with a non-finite float is
/// `error` with no outcome; anything else is `computed`.
pub fn result_from_outcome(
    kind: CoprocessorKind,
    op: &str,
    outcome: CoprocessorOutcome,
    backend: BackendFacts,
    duration_ms: u64,
) -> CoprocessorResult {
    let names = Some((kind, op));
    match outcome {
        CoprocessorOutcome::Failure(reason) => CoprocessorResult::new(
            CoprocessorStatus::Declined,
            names,
            Some(CoprocessorOutcome::Failure(reason.clone())),
            reason,
            Some(backend),
            duration_ms,
        ),
        o if !outcome_is_finite(&o) => CoprocessorResult::new(
            CoprocessorStatus::Error,
            names,
            None,
            NON_FINITE,
            Some(backend),
            duration_ms,
        ),
        o => CoprocessorResult::new(
            CoprocessorStatus::Computed,
            names,
            Some(o),
            "",
            Some(backend),
            duration_ms,
        ),
    }
}

/// The `unavailable` message for a kind that contract version 1 does not expose.
fn not_exposed_message(kind: CoprocessorKind) -> String {
    format!(
        "kind {} is not exposed by contract version 1: the sandboxed runner of plan item 1.5 does not exist yet",
        kind_name(kind)
    )
}

/// Run one request end to end. Never fails: every failure is a result.
///
/// `duration_ms` covers parsing, backend construction and dispatch.
pub async fn dispatch_request(input: &str) -> CoprocessorResult {
    let start = Instant::now();
    let elapsed = || u64::try_from(start.elapsed().as_millis()).unwrap_or(u64::MAX);

    let req = match parse_request(input) {
        Ok(r) => r,
        Err(e) => return CoprocessorResult::malformed(e, elapsed()),
    };
    let op = op_name(&req.op);
    let names = Some((req.kind, op.as_str()));

    if !is_exposed(req.kind) {
        return CoprocessorResult::new(
            CoprocessorStatus::Unavailable,
            names,
            None,
            not_exposed_message(req.kind),
            None,
            elapsed(),
        );
    }
    let Some(backend) = CoprocessorFactory::native(req.kind) else {
        return CoprocessorResult::new(
            CoprocessorStatus::Unavailable,
            names,
            None,
            format!("this build has no backend for kind {}", kind_name(req.kind)),
            None,
            elapsed(),
        );
    };
    let facts = BackendFacts::of(&*backend);
    let health = backend.health();
    if health != CoprocessorHealth::Healthy {
        return CoprocessorResult::new(
            CoprocessorStatus::Unavailable,
            names,
            None,
            format!("backend health is {health:?}"),
            Some(facts),
            elapsed(),
        );
    }
    if !backend
        .capabilities()
        .supported_ops
        .iter()
        .any(|s| s == &op)
    {
        return CoprocessorResult::new(
            CoprocessorStatus::Error,
            names,
            None,
            format!("op {op} does not belong to kind {}", kind_name(req.kind)),
            Some(facts),
            elapsed(),
        );
    }
    match backend.dispatch(req.op).await {
        Ok(outcome) => result_from_outcome(req.kind, &op, outcome, facts, elapsed()),
        Err(e) => CoprocessorResult::new(
            CoprocessorStatus::Error,
            names,
            None,
            format!("{e:#}"),
            Some(facts),
            elapsed(),
        ),
    }
}

/// One entry of the capabilities report.
#[derive(Debug, Clone, Serialize)]
pub struct KindCapability {
    /// The kind's variant name.
    pub kind: String,
    /// Whether contract version 1 exposes the kind (the allow-list).
    pub exposed: bool,
    /// Exposed, a backend exists in this build, and it is healthy.
    pub available: bool,
    /// The backend's trust object, or `None` when no backend was constructed.
    pub trust: Option<CoprocessorTrust>,
    /// The backend's `deterministic` capability, or `None` with no backend.
    pub deterministic: Option<bool>,
    /// The backend's supported op names; empty when not available.
    pub supported_ops: Vec<String>,
}

/// One `echidna.coprocessor.capabilities/1` object.
#[derive(Debug, Clone, Serialize)]
pub struct CapabilitiesReport {
    /// Always [`CAPABILITIES_SCHEMA`].
    pub schema: &'static str,
    /// The ECHIDNA version that emitted this object.
    pub echidna_version: String,
    /// One entry per `CoprocessorKind` variant, sorted by kind name.
    pub kinds: Vec<KindCapability>,
}

impl CapabilitiesReport {
    /// Serialise to the one-line JCS-canonical form (no newline).
    pub fn to_jcs(&self) -> Result<String, String> {
        serde_json_canonicalizer::to_string(self).map_err(|e| e.to_string())
    }
}

/// Build the capabilities report. Constructs only exposed backends.
pub fn capabilities() -> CapabilitiesReport {
    let mut kinds: Vec<KindCapability> = ALL_KINDS
        .iter()
        .map(|&kind| {
            let exposed = is_exposed(kind);
            let backend = if exposed {
                CoprocessorFactory::native(kind)
            } else {
                None
            };
            match backend {
                None => KindCapability {
                    kind: kind_name(kind),
                    exposed,
                    available: false,
                    trust: None,
                    deterministic: None,
                    supported_ops: Vec::new(),
                },
                Some(b) => {
                    let available = b.health() == CoprocessorHealth::Healthy;
                    KindCapability {
                        kind: kind_name(kind),
                        exposed,
                        available,
                        trust: Some(CoprocessorTrust::of(b.trust_tier())),
                        deterministic: Some(b.capabilities().deterministic),
                        supported_ops: if available {
                            b.capabilities().supported_ops.clone()
                        } else {
                            Vec::new()
                        },
                    }
                },
            }
        })
        .collect();
    kinds.sort_by(|a, b| a.kind.cmp(&b.kind));
    CapabilitiesReport {
        schema: CAPABILITIES_SCHEMA,
        echidna_version: ECHIDNA_VERSION.to_string(),
        kinds,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Request JSON for `kind` and an op given as raw JSON.
    fn request(kind: &str, op: &str) -> String {
        format!(r#"{{"schema":"{REQUEST_SCHEMA}","kind":"{kind}","op":{op}}}"#)
    }

    /// The parsed JSON of a result, after checking `trust.proof` is false.
    fn json(r: &CoprocessorResult) -> Value {
        let v: Value = serde_json::from_str(&r.to_jcs().expect("serialises")).unwrap();
        assert_eq!(v["trust"]["proof"], Value::Bool(false), "{v}");
        v
    }

    /// Golden JCS bytes for one `computed` result with fixed fields.
    #[test]
    fn golden_computed_result() {
        let facts = BackendFacts {
            tier: CoprocessorTrustTier::LibraryWrapped,
            deterministic: true,
        };
        let r = result_from_outcome(
            CoprocessorKind::Math,
            "BigIntGcd",
            CoprocessorOutcome::BigInt("6".into()),
            facts,
            7,
        );
        let expected = format!(
            r#"{{"deterministic":true,"duration_ms":7,"echidna_version":"{ECHIDNA_VERSION}","kind":"Math","message":"","op":"BigIntGcd","outcome":{{"BigInt":"6"}},"schema":"echidna.coprocessor.result/1","status":"computed","trust":{{"proof":false,"rank":3,"tier":"LibraryWrapped"}}}}"#
        );
        assert_eq!(r.to_jcs().unwrap(), expected);
    }

    /// A real request through the real backend computes gcd(12, 18) = 6.
    #[tokio::test]
    async fn math_gcd_is_computed() {
        let r = dispatch_request(&request("Math", r#"{"BigIntGcd":{"a":"12","b":"18"}}"#)).await;
        assert_eq!(r.status, CoprocessorStatus::Computed);
        let v = json(&r);
        assert_eq!(v["outcome"], serde_json::json!({"BigInt": "6"}));
        assert_eq!(v["kind"], "Math");
        assert_eq!(v["op"], "BigIntGcd");
    }

    /// `VectorAdd` on vectors of different length makes the backend return
    /// `Failure` (`vector.rs`), which is `declined`.
    #[tokio::test]
    async fn length_mismatch_is_declined() {
        let r = dispatch_request(&request(
            "Vector",
            r#"{"VectorAdd":{"a":[1.0,2.0],"b":[1.0]}}"#,
        ))
        .await;
        assert_eq!(r.status, CoprocessorStatus::Declined, "{r:?}");
        assert!(!r.message.is_empty());
        let v = json(&r);
        assert!(v["outcome"]["Failure"].is_string(), "{v}");
    }

    /// A kind outside the allow-list is `unavailable`, with no backend.
    #[tokio::test]
    async fn io_is_unavailable() {
        let r = dispatch_request(&request("Io", r#"{"IoLineCount":{"path":"/etc/passwd"}}"#)).await;
        assert_eq!(r.status, CoprocessorStatus::Unavailable);
        assert!(r.message.contains("not exposed by contract version 1"));
        assert!(r.message.contains("1.5"));
        assert_eq!(r.trust, CoprocessorTrust::none());
        assert!(r.outcome.is_none());
        json(&r);
    }

    /// Malformed requests are `error` with `kind` and `op` null.
    #[tokio::test]
    async fn malformed_requests_are_errors() {
        let gcd = r#"{"BigIntGcd":{"a":"12","b":"18"}}"#;
        let cases = [
            "{not json".to_string(),
            "[]".to_string(),
            request("Math", gcd).replace(REQUEST_SCHEMA, "echidna.coprocessor.request/9"),
            request("NoSuchKind", gcd),
            request("Math", r#"{"NoSuchOp":{}}"#),
            request("Math", r#"{"BigIntGcd":{"a":"12"}}"#),
            request("Math", gcd).replacen('{', r#"{"extra":1,"#, 1),
            r#"{"schema":"echidna.coprocessor.request/1","kind":"Math"}"#.to_string(),
        ];
        for c in cases {
            let r = dispatch_request(&c).await;
            assert_eq!(r.status, CoprocessorStatus::Error, "{c}");
            assert_eq!(r.kind, None, "{c}");
            assert_eq!(r.op, None, "{c}");
            assert!(!r.message.is_empty(), "{c}");
            json(&r);
        }
    }

    /// An op of another kind is `error`, not `declined`.
    #[tokio::test]
    async fn op_of_another_kind_is_an_error() {
        let r = dispatch_request(&request("Math", r#"{"VectorNorm":{"a":[3.0,4.0]}}"#)).await;
        assert_eq!(r.status, CoprocessorStatus::Error);
        assert!(r.message.contains("does not belong"), "{}", r.message);
        assert!(r.outcome.is_none());
        json(&r);
    }

    /// A non-finite float in an outcome is `error`, and `to_jcs` refuses it.
    #[test]
    fn non_finite_outcome_is_an_error() {
        let facts = BackendFacts {
            tier: CoprocessorTrustTier::LibraryWrapped,
            deterministic: true,
        };
        for o in [
            CoprocessorOutcome::Float(f64::NAN),
            CoprocessorOutcome::FloatVec(vec![1.0, f64::INFINITY]),
            CoprocessorOutcome::FloatMatrix(vec![vec![f64::NEG_INFINITY]]),
        ] {
            let mut r =
                result_from_outcome(CoprocessorKind::Vector, "VectorNorm", o.clone(), facts, 1);
            assert_eq!(r.status, CoprocessorStatus::Error);
            assert!(r.outcome.is_none());
            json(&r);
            r.outcome = Some(o);
            assert!(r.to_jcs().is_err());
        }
    }

    /// The allow-list is exactly the in-process kinds named by the contract.
    #[test]
    fn allow_list_is_exact() {
        use CoprocessorKind::*;
        let mut expected = vec![Math, Vector, Tensor, Crypto, Dsp, Physics];
        if cfg!(feature = "flint") {
            expected.push(FlintMath);
        }
        let mut got = EXPOSED_KINDS.to_vec();
        got.sort_by_key(|k| *k as u8);
        expected.sort_by_key(|k| *k as u8);
        assert_eq!(got, expected);
        for k in [
            Io, Graphics, Audio, Fpga, PariGp, Maxima, Singular, Gap, Macaulay2,
        ] {
            assert!(!is_exposed(k), "{k:?}");
        }
    }

    /// `ALL_KINDS` lists every variant once.
    #[test]
    fn all_kinds_is_complete() {
        /// Fails to compile when a variant is added and not handled here.
        fn listed(k: CoprocessorKind) -> bool {
            use CoprocessorKind::*;
            match k {
                Math | Vector | Tensor | Crypto | Physics | FlintMath | Dsp | Io | Graphics
                | Audio | Fpga | PariGp | Maxima | Singular | Gap | Macaulay2 => {
                    ALL_KINDS.contains(&k)
                },
            }
        }
        let tags: Vec<u8> = ALL_KINDS.iter().map(|k| *k as u8).collect();
        assert_eq!(tags, (0..16).collect::<Vec<u8>>());
        assert!(ALL_KINDS.iter().all(|k| listed(*k)));
    }

    /// No status spells a proof claim, and every status but `computed` exits non-zero.
    #[test]
    fn status_vocabulary_is_closed_and_hint_only() {
        let names: Vec<&str> = CoprocessorStatus::ALL.iter().map(|s| s.as_str()).collect();
        assert_eq!(names, ["computed", "declined", "unavailable", "error"]);
        for s in CoprocessorStatus::ALL {
            assert_eq!(serde_json::to_value(s).unwrap(), s.as_str());
            assert_eq!(s.exit_code() == 0, s == CoprocessorStatus::Computed);
        }
        assert_eq!(serde_json::to_value(NotAProof).unwrap(), Value::Bool(false));
    }

    /// The capabilities report has one sorted entry per kind and honours the allow-list.
    #[test]
    fn capabilities_cover_every_kind() {
        let report = capabilities();
        let line = report.to_jcs().unwrap();
        let v: Value = serde_json::from_str(&line).unwrap();
        assert_eq!(v["schema"], CAPABILITIES_SCHEMA);
        let kinds = v["kinds"].as_array().unwrap();
        assert_eq!(kinds.len(), ALL_KINDS.len());
        let names: Vec<&str> = kinds.iter().map(|k| k["kind"].as_str().unwrap()).collect();
        let mut sorted = names.clone();
        sorted.sort();
        assert_eq!(names, sorted);
        for k in kinds {
            let exposed = k["exposed"].as_bool().unwrap();
            if !exposed {
                assert_eq!(k["available"], false, "{k}");
                assert!(k["trust"].is_null(), "{k}");
                assert!(k["supported_ops"].as_array().unwrap().is_empty(), "{k}");
            } else if k["available"] == true {
                assert_eq!(k["trust"]["proof"], false, "{k}");
                assert!(!k["supported_ops"].as_array().unwrap().is_empty(), "{k}");
            }
        }
        let math = kinds.iter().find(|k| k["kind"] == "Math").unwrap();
        assert_eq!(math["available"], true);
    }
}
