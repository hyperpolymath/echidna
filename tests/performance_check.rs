// SPDX-License-Identifier: PMPL-1.0-or-later
// Simple performance check for prover backends

use echidna::provers::{ProverBackend, ProverConfig, ProverFactory, ProverKind};
use std::time::Instant;

#[tokio::test]
async fn test_prover_creation_performance() {
    println!("\n=== Prover Creation Performance ===");

    for kind in ProverKind::all() {
        let start = Instant::now();
        let config = ProverConfig::default();
        let result = ProverFactory::create(kind, config);
        let elapsed = start.elapsed();

        match result {
            Ok(_) => println!("{:?}: {:?}", kind, elapsed),
            Err(e) => println!("{:?}: Error - {}", kind, e),
        }
    }
}

#[tokio::test]
async fn test_parse_performance_subset() {
    println!("\n=== Parse Performance (Subset) ===");

    let tests = vec![
        (ProverKind::Lean, "theorem trivial : True := trivial"),
        (ProverKind::Coq, "Definition id (x : nat) := x."),
        (ProverKind::Z3, "(assert true)"),
    ];

    for (kind, input) in tests {
        let config = ProverConfig::default();
        if let Ok(backend) = ProverFactory::create(kind, config) {
            let start = Instant::now();
            let result = backend.parse_string(input).await;
            let elapsed = start.elapsed();

            match result {
                Ok(_) => println!("{:?} parse: {:?}", kind, elapsed),
                Err(e) => println!("{:?} parse error: {}", kind, e),
            }
        }
    }
}
