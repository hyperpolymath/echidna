// SPDX-License-Identifier: PMPL-1.0-or-later

//! ECHIDNA L1 wire layer — Cap'n Proto schemas and generated bindings.
//!
//! This crate is schema-only (L1.0). The transport layer (UDS, TCP,
//! WebSocket), peer integrations (Julia, Chapel, UI), Idris2 ABI proofs,
//! and conversion helpers from `echidna-core` types ship in L1.1+.
//!
//! # Module layout
//!
//! The capnpc-rust generator emits `crate::<stem>_capnp::` as the
//! canonical intra-crate path for cross-file references (e.g. prover_capnp
//! referencing common_capnp).  We therefore expose the modules under the
//! names the generator expects (`common_capnp`, `prover_capnp`, …) and
//! additionally re-export them under the nicer aliases (`common`, `prover`,
//! …) for use by downstream crates.

#[allow(unused_imports)]
pub mod common_capnp {
    include!(concat!(env!("OUT_DIR"), "/common_capnp.rs"));
}

#[allow(unused_imports)]
pub mod prover_capnp {
    include!(concat!(env!("OUT_DIR"), "/prover_capnp.rs"));
}

#[allow(unused_imports)]
pub mod proof_capnp {
    include!(concat!(env!("OUT_DIR"), "/proof_capnp.rs"));
}

#[allow(unused_imports)]
pub mod gnn_capnp {
    include!(concat!(env!("OUT_DIR"), "/gnn_capnp.rs"));
}

// Ergonomic re-exports under shorter names.
pub use common_capnp as common;
pub use proof_capnp as proof;
pub use prover_capnp as prover;
pub use gnn_capnp as gnn;

#[cfg(test)]
mod smoke {
    use super::*;
    use capnp::message::{Builder, HeapAllocator};

    #[test]
    fn construct_proof_goal() {
        let mut msg = Builder::<HeapAllocator>::new_default();
        let mut pg = msg.init_root::<proof::proof_goal::Builder>();
        pg.set_request_id("test-req-0");
        pg.set_session_id("");
        pg.set_timeout_ms(300_000);
        pg.set_schema_version(1);
        let bytes = capnp::serialize::write_message_to_words(&msg);
        assert!(!bytes.is_empty());

        // Round-trip read
        let reader = capnp::serialize::read_message_from_flat_slice(
            &mut &bytes[..],
            capnp::message::ReaderOptions::new(),
        )
        .unwrap();
        let root = reader.get_root::<proof::proof_goal::Reader>().unwrap();
        assert_eq!(root.get_request_id().unwrap().to_str().unwrap(), "test-req-0");
        assert_eq!(root.get_schema_version(), 1);
        assert_eq!(root.get_timeout_ms(), 300_000);
    }

    #[test]
    fn construct_gnn_rank_request() {
        let mut msg = Builder::<HeapAllocator>::new_default();
        let mut req = msg.init_root::<gnn::gnn_rank_request::Builder>();
        req.set_request_id("gnn-0");
        req.set_top_k(10);
        req.set_min_score(0.1);
        let bytes = capnp::serialize::write_message_to_words(&msg);
        assert!(!bytes.is_empty());
    }

    #[test]
    fn construct_trusted_outcome_proved() {
        let mut msg = Builder::<HeapAllocator>::new_default();
        let mut outcome = msg.init_root::<prover::trusted_outcome::Builder>();
        outcome.set_invocation_id("inv-0");
        outcome.set_trust_level(3);
        outcome.set_prover_name("Z3");
        outcome.set_prover_kind(9);
        let status = outcome.reborrow().init_status();
        let mut proved = status.init_proved();
        proved.set_elapsed_ms(42);
        let bytes = capnp::serialize::write_message_to_words(&msg);
        assert!(!bytes.is_empty());
    }
}
