// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later
// (MPL-2.0 is automatic legal fallback until PMPL is formally recognised)

//! Crypto coprocessor — computational cryptographic primitives.
//!
//! Pairs with the symbolic-crypto provers (Tamarin, ProVerif) and the
//! future computational-crypto backends (EasyCrypt, CryptoVerif) by
//! providing concrete digest / verification ops the symbolic side can
//! cross-check against ground-truth bytes.
//!
//! Currently exposes:
//! - SHA-256          (RustCrypto `sha2` — RFC 6234 reference impl)
//! - BLAKE3           (`blake3` — designer's reference impl)
//! - Ed25519 verify   (`ed25519-dalek` — RFC 8032)
//!
//! All three primitives have widely-audited canonical impls.  The trust
//! tier is `LibraryWrapped` (Tier 3); the same primitives reach Tier 4
//! once the SPARK + Idris2 ABI proofs in `coprocessor_safety.ads` are
//! extended in Phase 7 to constrain the byte-level wire shape.

use anyhow::{anyhow, Result};
use async_trait::async_trait;
use ed25519_dalek::{Signature, Verifier, VerifyingKey};
use sha2::{Digest, Sha256};

use super::types::{
    CoprocessorCapabilities, CoprocessorHealth, CoprocessorKind, CoprocessorOp,
    CoprocessorOutcome,
};
use super::trust::CoprocessorTrustTier;
use super::Coprocessor;

pub struct CryptoBackend {
    capabilities: CoprocessorCapabilities,
}

impl CryptoBackend {
    pub fn new() -> Self {
        CryptoBackend {
            capabilities: CoprocessorCapabilities {
                supported_ops: vec![
                    "CryptoSha256".into(),
                    "CryptoBlake3".into(),
                    "CryptoEd25519Verify".into(),
                ],
                typical_latency_us: 10,
                deterministic: true,
            },
        }
    }
}

impl Default for CryptoBackend {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait]
impl Coprocessor for CryptoBackend {
    fn kind(&self) -> CoprocessorKind {
        CoprocessorKind::Crypto
    }

    fn capabilities(&self) -> &CoprocessorCapabilities {
        &self.capabilities
    }

    fn health(&self) -> CoprocessorHealth {
        CoprocessorHealth::Healthy
    }

    fn trust_tier(&self) -> CoprocessorTrustTier {
        // RustCrypto's sha2 + ed25519-dalek + blake3 reference are all
        // widely audited and constant-time by design — Tier 3.  Earns
        // Tier 4 once the SPARK boundary attests byte-level invariants.
        CoprocessorTrustTier::LibraryWrapped
    }

    async fn dispatch(&self, op: CoprocessorOp) -> Result<CoprocessorOutcome> {
        tokio::task::spawn_blocking(move || dispatch_sync(op))
            .await
            .map_err(|e| anyhow!("crypto join error: {e}"))?
    }
}

fn dispatch_sync(op: CoprocessorOp) -> Result<CoprocessorOutcome> {
    Ok(match op {
        CoprocessorOp::CryptoSha256 { bytes } => {
            let mut hasher = Sha256::new();
            hasher.update(&bytes);
            CoprocessorOutcome::Hex(hex(&hasher.finalize()))
        }
        CoprocessorOp::CryptoBlake3 { bytes } => {
            let digest = blake3::hash(&bytes);
            CoprocessorOutcome::Hex(digest.to_hex().to_string())
        }
        CoprocessorOp::CryptoEd25519Verify {
            public_key,
            signature,
            message,
        } => {
            // Ed25519 keys are 32 bytes, sigs are 64 bytes — RFC 8032.
            if public_key.len() != 32 {
                return Ok(CoprocessorOutcome::Failure(format!(
                    "CryptoEd25519Verify: public key must be 32 bytes (got {})",
                    public_key.len()
                )));
            }
            if signature.len() != 64 {
                return Ok(CoprocessorOutcome::Failure(format!(
                    "CryptoEd25519Verify: signature must be 64 bytes (got {})",
                    signature.len()
                )));
            }
            let mut pk_bytes = [0u8; 32];
            pk_bytes.copy_from_slice(&public_key);
            let mut sig_bytes = [0u8; 64];
            sig_bytes.copy_from_slice(&signature);
            let vk = match VerifyingKey::from_bytes(&pk_bytes) {
                Ok(k) => k,
                Err(e) => {
                    return Ok(CoprocessorOutcome::Failure(format!(
                        "CryptoEd25519Verify: invalid public key: {e}"
                    )))
                }
            };
            let sig = Signature::from_bytes(&sig_bytes);
            CoprocessorOutcome::Boolean(vk.verify(&message, &sig).is_ok())
        }
        other => CoprocessorOutcome::Failure(format!(
            "Crypto backend does not support {:?}",
            std::mem::discriminant(&other)
        )),
    })
}

fn hex(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        out.push_str(&format!("{:02x}", b));
    }
    out
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
            CryptoBackend::new().dispatch(op).await.unwrap()
        })
    }

    #[test]
    fn sha256_empty_known_digest() {
        // SHA-256("") = e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
        match run(CoprocessorOp::CryptoSha256 { bytes: vec![] }) {
            CoprocessorOutcome::Hex(h) => assert_eq!(
                h,
                "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
            ),
            _ => panic!(),
        }
    }

    #[test]
    fn sha256_abc_known_digest() {
        // SHA-256("abc") = ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad
        match run(CoprocessorOp::CryptoSha256 {
            bytes: b"abc".to_vec(),
        }) {
            CoprocessorOutcome::Hex(h) => assert_eq!(
                h,
                "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
            ),
            _ => panic!(),
        }
    }

    #[test]
    fn blake3_empty_known_digest() {
        // BLAKE3("") = af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262
        match run(CoprocessorOp::CryptoBlake3 { bytes: vec![] }) {
            CoprocessorOutcome::Hex(h) => assert_eq!(
                h,
                "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
            ),
            _ => panic!(),
        }
    }

    #[test]
    fn ed25519_verify_rfc8032_test_vector_1() {
        // RFC 8032 §7.1, test vector 1 — empty message.
        let sk_seed: [u8; 32] = [
            0x9d, 0x61, 0xb1, 0x9d, 0xef, 0xfd, 0x5a, 0x60, 0xba, 0x84, 0x4a, 0xf4,
            0x92, 0xec, 0x2c, 0xc4, 0x44, 0x49, 0xc5, 0x69, 0x7b, 0x32, 0x69, 0x19,
            0x70, 0x3b, 0xac, 0x03, 0x1c, 0xae, 0x7f, 0x60,
        ];
        // Derive verifying key from seed via SigningKey to keep the test
        // self-contained without hard-coding the public key.
        let sk = ed25519_dalek::SigningKey::from_bytes(&sk_seed);
        let vk = sk.verifying_key();
        // Sign empty message.
        let sig = ed25519_dalek::Signer::sign(&sk, b"");
        match run(CoprocessorOp::CryptoEd25519Verify {
            public_key: vk.to_bytes().to_vec(),
            signature: sig.to_bytes().to_vec(),
            message: vec![],
        }) {
            CoprocessorOutcome::Boolean(true) => {},
            other => panic!("expected verify=true, got {other:?}"),
        }
    }

    #[test]
    fn ed25519_verify_tamper_detected() {
        let sk = ed25519_dalek::SigningKey::from_bytes(&[7u8; 32]);
        let vk = sk.verifying_key();
        let sig = ed25519_dalek::Signer::sign(&sk, b"original");
        match run(CoprocessorOp::CryptoEd25519Verify {
            public_key: vk.to_bytes().to_vec(),
            signature: sig.to_bytes().to_vec(),
            message: b"TAMPERED".to_vec(),
        }) {
            CoprocessorOutcome::Boolean(false) => {},
            other => panic!("expected verify=false, got {other:?}"),
        }
    }

    #[test]
    fn ed25519_verify_short_key_returns_failure() {
        match run(CoprocessorOp::CryptoEd25519Verify {
            public_key: vec![0u8; 16],
            signature: vec![0u8; 64],
            message: vec![],
        }) {
            CoprocessorOutcome::Failure(_) => {},
            _ => panic!(),
        }
    }
}
