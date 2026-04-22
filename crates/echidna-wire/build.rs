// SPDX-License-Identifier: PMPL-1.0-or-later

fn main() {
    capnpc::CompilerCommand::new()
        .src_prefix("schemas")
        .file("schemas/common.capnp")
        .file("schemas/prover.capnp")
        .file("schemas/proof.capnp")
        .file("schemas/gnn.capnp")
        .run()
        .expect("capnpc build failed");
}
