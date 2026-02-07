// SPDX-License-Identifier: PMPL-1.0-or-later

fn main() -> Result<(), Box<dyn std::error::Error>> {
    tonic_build::compile_protos("proto/echidna.proto")?;
    Ok(())
}
