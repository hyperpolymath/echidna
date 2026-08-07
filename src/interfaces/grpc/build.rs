// SPDX-License-Identifier: AGPL-3.0-or-later

fn main() -> Result<(), Box<dyn std::error::Error>> {
    tonic_prost_build::compile_protos("proto/echidna.proto")?;
    Ok(())
}
