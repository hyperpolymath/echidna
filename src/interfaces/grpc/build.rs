// SPDX-License-Identifier: MPL-2.0

fn main() -> Result<(), Box<dyn std::error::Error>> {
    tonic_prost_build::compile_protos("proto/echidna.proto")?;
    Ok(())
}
