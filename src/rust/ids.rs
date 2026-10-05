// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! The single place echidna mints identifiers.
//!
//! Every UUID echidna creates comes from one of the functions here; no other
//! module calls `Uuid::new_v4`/`Uuid::now_v7` directly. There are two kinds:
//!
//! * [`new_record_id`] — a **UUIDv7** (RFC 9562 §5.7) for things that
//!   *happen*: proof requests, sessions, attempts, runs, findings. v7 is
//!   time-ordered, so ids sort by creation time. Within one process the `uuid`
//!   crate's shared v7 context makes successive ids strictly increasing.
//!   This is the estate default (standards `docs/UUID-V7-ESTATE-STANDARD.adoc`).
//! * [`content_id`] — a **UUIDv8** (RFC 9562 §5.8, Appendix B.2 hash-based
//!   layout) for things that *are*: proof goals, prove results, corpus
//!   entries, octads. The id is derived from the value alone, so equal content
//!   always gets the same id, wherever and whenever it is computed:
//!
//!   1. canonicalise the value with JCS (RFC 8785);
//!   2. SHA-256 the canonical bytes;
//!   3. take the first 16 bytes of the digest;
//!   4. set the version nibble to `8` and the variant bits to `10`.
//!
//! The v8 layout is an owner decision of 2026-10-05; the estate v7 standard
//! defines no v8 layout yet, so this module is where it is written down.
//!
//! [`temp_token`] is for throwaway temp-file names only. It is a v7 in simple
//! (hyphen-free) form and never leaves the machine.

use serde::Serialize;
use sha2::{Digest, Sha256};
use uuid::Uuid;

/// Mint a fresh time-ordered record id (UUIDv7) for an event or record:
/// a proof request, session, attempt, run or finding.
pub fn new_record_id() -> Uuid {
    Uuid::now_v7()
}

/// Derive the deterministic content id (UUIDv8, SHA-256 over the JCS form)
/// of a serialisable value: a proof goal, prove result, corpus entry or octad.
///
/// Two values with the same JCS canonical form always get the same id.
/// Fails only when the value cannot be represented as JSON (for example a
/// map with non-string keys or a non-finite float).
pub fn content_id<T: Serialize>(value: &T) -> Result<Uuid, serde_json::Error> {
    let canonical = serde_json_canonicalizer::to_vec(value)?;
    Ok(content_id_from_canonical_bytes(&canonical))
}

/// Derive the UUIDv8 content id from bytes that are already JCS-canonical.
///
/// Callers holding canonical bytes (for example the stdout of a JCS emitter)
/// use this to avoid a re-serialisation; [`content_id`] calls it too.
pub fn content_id_from_canonical_bytes(canonical: &[u8]) -> Uuid {
    let digest = Sha256::digest(canonical);
    let mut bytes = [0u8; 16];
    bytes.copy_from_slice(&digest[..16]);
    // `new_v8` sets the version nibble to 8 and the variant bits to 0b10.
    Uuid::new_v8(bytes)
}

/// Return a unique, filesystem-safe token for a temp-file name.
///
/// Not an identifier of anything: it only keeps concurrent prover
/// invocations from colliding in the temp directory.
pub fn temp_token() -> String {
    new_record_id().simple().to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn record_id_is_v7_with_rfc_variant() {
        let id = new_record_id();
        assert_eq!(id.get_version_num(), 7);
        assert_eq!(id.get_variant(), uuid::Variant::RFC4122);
    }

    #[test]
    fn record_ids_are_strictly_monotonic_in_process() {
        let ids: Vec<Uuid> = (0..10_000).map(|_| new_record_id()).collect();
        for pair in ids.windows(2) {
            assert!(pair[0] < pair[1], "{} !< {}", pair[0], pair[1]);
        }
    }

    #[test]
    fn content_id_is_v8_with_rfc_variant() {
        let id = content_id(&json!({"goal": "forall n, n + 0 = n"})).unwrap();
        assert_eq!(id.get_version_num(), 8);
        assert_eq!(id.get_variant(), uuid::Variant::RFC4122);
        // Variant bits 10 in the top of byte 8; version 8 in byte 6.
        let b = id.as_bytes();
        assert_eq!(b[6] >> 4, 0x8);
        assert_eq!(b[8] >> 6, 0b10);
    }

    #[test]
    fn same_jcs_content_gives_same_id() {
        // Key order and whitespace differ; the JCS form is identical.
        let a: serde_json::Value =
            serde_json::from_str(r#"{"prover":"lean","goal":"p","n":1.0}"#).unwrap();
        let b: serde_json::Value =
            serde_json::from_str(r#"{ "n": 1, "goal": "p", "prover": "lean" }"#).unwrap();
        assert_eq!(content_id(&a).unwrap(), content_id(&b).unwrap());
    }

    #[test]
    fn different_content_gives_different_id() {
        let a = content_id(&json!({"goal": "p"})).unwrap();
        let b = content_id(&json!({"goal": "q"})).unwrap();
        assert_ne!(a, b);
    }

    #[test]
    fn content_id_matches_documented_construction() {
        // Planted positive control: recompute the layout by hand.
        let canonical = br#"{"a":1,"b":[true,null]}"#;
        let value = json!({"b": [true, null], "a": 1});
        assert_eq!(
            serde_json_canonicalizer::to_vec(&value).unwrap(),
            canonical.to_vec()
        );
        let digest = Sha256::digest(canonical);
        let mut expect = [0u8; 16];
        expect.copy_from_slice(&digest[..16]);
        expect[6] = (expect[6] & 0x0f) | 0x80;
        expect[8] = (expect[8] & 0x3f) | 0x80;
        assert_eq!(content_id(&value).unwrap(), Uuid::from_bytes(expect));
    }

    #[test]
    fn temp_token_is_hyphen_free_and_unique() {
        let a = temp_token();
        let b = temp_token();
        assert_eq!(a.len(), 32);
        assert!(!a.contains('-'));
        assert_ne!(a, b);
    }
}
