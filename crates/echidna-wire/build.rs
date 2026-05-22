// SPDX-License-Identifier: MPL-2.0

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
