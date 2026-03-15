# Trust Framework Implementation Guide

**Quick Start**: How to implement and use ECHIDNA's trust and validation framework.

---

## Phase 1: Benchmarking (Week 1)

### Setup

```bash
# Add dependencies to Cargo.toml
[dev-dependencies]
criterion = { version = "0.5", features = ["html_reports"] }
proptest = "1.4"

[[bench]]
name = "proof_benchmarks"
harness = false
```

### Run Benchmarks

```bash
# Run all benchmarks
cargo bench

# View HTML reports
open target/criterion/report/index.html

# Run specific benchmark
cargo bench --bench proof_benchmarks -- simple_arithmetic
```

### Set Up CI Benchmarking

```bash
# Already created: .github/workflows/benchmarks.yml
# Pushes to main will track performance over time
# PR benchmarks will compare against main branch
```

---

## Phase 2: Property-Based Testing (Week 1)

### Run Property Tests

```bash
# Run all property tests
cargo test property_tests

# Run with verbose output
cargo test property_tests -- --nocapture

# Run specific property
cargo test reflexivity_is_idempotent
```

### Add New Property

```rust
// In tests/property_tests.rs
proptest! {
    #[test]
    fn my_new_property(input in "[a-z]+") {
        // Your property here
        prop_assert!(some_invariant(input));
    }
}
```

---

## Phase 3: Idris2 Validator (Week 2-3)

### Install Idris2

```bash
# Option 1: From package manager
# Fedora
sudo dnf install idris2

# Option 2: From source
git clone https://github.com/idris-lang/Idris2.git
cd Idris2
make bootstrap
make install
```

### Build Validator

```bash
# Navigate to Idris source
cd src/idris

# Build package
idris2 --build echidna-validator.ipkg

# Run tests
idris2 --repl Validator.idr
> :exec testValidation
```

### Integrate with Rust

```rust
// In src/rust/main.rs or lib.rs
pub mod anomaly_detection;

// Use the validator
use anomaly_detection::{AnomalyDetector, ProofResult};

let detector = AnomalyDetector::new();
let result = ProofResult { /* ... */ };
let anomalies = detector.detect(&result);

if !anomalies.is_empty() {
    println!("⚠️  Anomalies detected: {:?}", anomalies);
}
```

---

## Phase 4: Anomaly Detection (Week 3)

### Basic Usage

```rust
use echidna::anomaly_detection::{AnomalyDetector, ProofResult};

// Create detector with defaults
let detector = AnomalyDetector::new();

// Or with custom baseline
let detector = AnomalyDetector::with_baseline(BaselineMetrics {
    max_tactics: 15,
    max_complexity: 80,
    avg_proof_time_ms: 3000,
    confidence_threshold: 0.92,
});

// Check a proof for anomalies
let result = ProofResult {
    goal: "forall n, n + 0 = n".to_string(),
    success: true,
    confidence: 0.85,
    tactic_count: 3,
    time_ms: 1500,
    premises: vec![],
};

let anomalies = detector.detect(&result);
for anomaly in anomalies {
    println!("Anomaly: {:?}", anomaly);
}
```

### Multi-Prover Consensus

```rust
use echidna::anomaly_detection::ConsensusChecker;

let checker = ConsensusChecker::new(3); // Need 3 agreeing

let results = vec![
    ("coq".to_string(), true),
    ("lean".to_string(), true),
    ("agda".to_string(), true),
    ("isabelle".to_string(), false),
];

let consensus = checker.check_consensus("n + 0 = n", results);

if consensus.agreed {
    println!("✓ Consensus reached ({})", consensus.confidence);
} else {
    println!("✗ No consensus - prover disagreement!");
}
```

---

## Phase 5: Integration (Week 4)

### Add to API Endpoint

```rust
// In src/rust/server.rs
async fn prove_endpoint(
    Json(req): Json<ProveRequest>
) -> Result<Json<ProveResponse>, AppError> {
    // 1. Get proof from prover
    let proof_result = prover.prove(&req.goal).await?;

    // 2. Check for anomalies
    let detector = AnomalyDetector::new();
    let anomalies = detector.detect(&proof_result);

    // 3. Get multi-prover consensus
    let consensus = check_all_provers(&req.goal).await;

    // 4. Calculate trust score
    let trust_score = calculate_trust_score(
        &proof_result,
        &anomalies,
        &consensus
    );

    // 5. Return result with trust metrics
    Ok(Json(ProveResponse {
        success: proof_result.success,
        proof: proof_result.proof,
        trust_score,
        anomalies,
        consensus_confidence: consensus.confidence,
    }))
}
```

### Trust Score API

```rust
#[derive(Serialize)]
pub struct TrustScore {
    /// Overall trust score (0.0 - 1.0)
    pub overall: f64,

    /// Multi-prover agreement (0.0 - 1.0)
    pub agreement: f64,

    /// Number of anomalies detected
    pub anomaly_count: usize,

    /// Formally verified by Idris2
    pub formally_verified: bool,

    /// Detailed breakdown
    pub details: TrustDetails,
}

fn calculate_trust_score(
    result: &ProofResult,
    anomalies: &[Anomaly],
    consensus: &ConsensusResult,
) -> TrustScore {
    let agreement_score = consensus.confidence;
    let anomaly_penalty = 0.1 * anomalies.len() as f64;

    let overall = (agreement_score - anomaly_penalty)
        .max(0.0)
        .min(1.0);

    TrustScore {
        overall,
        agreement: agreement_score,
        anomaly_count: anomalies.len(),
        formally_verified: false, // TODO: integrate Idris2
        details: TrustDetails {
            prover_votes: consensus.voting.clone(),
            detected_anomalies: anomalies.to_vec(),
        },
    }
}
```

---

## Testing the Framework

### Run All Tests

```bash
# Unit tests
cargo test

# Property tests
cargo test property_tests

# Benchmarks
cargo bench

# Idris2 validator
cd src/idris && idris2 --test echidna-validator.ipkg
```

### Test Anomaly Detection

```bash
# Run anomaly detection tests
cargo test anomaly_detection

# Test with real proofs
cargo run --example test_anomalies
```

---

## Monitoring Dashboard (Future)

### Prometheus Metrics

```rust
use prometheus::{Counter, Histogram, Registry};

lazy_static! {
    static ref PROOFS_ATTEMPTED: Counter = Counter::new(
        "echidna_proofs_attempted_total",
        "Total proof attempts"
    ).unwrap();

    static ref ANOMALIES_DETECTED: Counter = Counter::new(
        "echidna_anomalies_detected_total",
        "Anomalies detected"
    ).unwrap();

    static ref PROOF_TIME: Histogram = Histogram::new(
        "echidna_proof_time_seconds",
        "Proof search time in seconds"
    ).unwrap();
}

// Record metrics
PROOFS_ATTEMPTED.inc();
ANOMALIES_DETECTED.inc_by(anomalies.len() as f64);
PROOF_TIME.observe(duration_secs);
```

### Grafana Dashboard

```yaml
# docker-compose.yml
services:
  prometheus:
    image: prom/prometheus
    ports:
      - "9090:9090"
    volumes:
      - ./prometheus.yml:/etc/prometheus/prometheus.yml

  grafana:
    image: grafana/grafana
    ports:
      - "3001:3000"
    environment:
      - GF_SECURITY_ADMIN_PASSWORD=admin
```

---

## FAQ

### Q: How do I know if a proof is trustworthy?

Check the trust score:
- **0.9-1.0**: Very trustworthy (multiple provers agree, no anomalies)
- **0.7-0.9**: Trustworthy (some agreement, minor issues)
- **0.5-0.7**: Questionable (low agreement or multiple anomalies)
- **<0.5**: Not trustworthy (prover disagreement or serious anomalies)

### Q: What if the ML model is overconfident?

The anomaly detector will flag `UnusuallyHighConfidence` if the model is >95% confident on a complex theorem. This doesn't mean the proof is wrong, just that it needs extra verification.

### Q: How many provers need to agree?

Recommended: **3 out of 12** for basic trust, **6 out of 12** for high trust, **9+ out of 12** for critical applications.

### Q: Can the ML component introduce unsoundness?

**No.** The ML component only *suggests tactics* - all proofs are verified by formal theorem provers (Coq, Lean, etc.). The ML cannot generate unsound proofs because provers reject invalid tactics.

### Q: What's the Idris2 validator for?

Extra assurance. Even if a prover claims a proof is valid, the Idris2 validator provides a **second opinion** with a formally verified type checker. If Idris2 agrees, you have mathematical certainty.

---

## Next Steps

1. ✅ **Week 1**: Run benchmarks and property tests
2. ⏳ **Week 2**: Install Idris2 and build validator
3. ⏳ **Week 3**: Integrate anomaly detection into API
4. ⏳ **Week 4**: Add multi-prover consensus checking
5. ⏳ **Week 5**: Deploy monitoring dashboard

---

*ECHIDNA Trust Framework - Quick Implementation Guide*
*Co-Authored-By: Claude Sonnet 4.5 <noreply@anthropic.com>*
