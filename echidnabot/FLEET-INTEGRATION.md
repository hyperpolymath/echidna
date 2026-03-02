# Gitbot Fleet Integration

## Overview

Echidnabot is now integrated with the [gitbot-fleet](https://github.com/hyperpolymath/gitbot-fleet) orchestration system. This enables coordinated analysis across multiple bots and shared context for better repository insights.

## Architecture

```
GitHub/GitLab → echidnabot → ECHIDNA Core (30 provers) → Fleet Context
                     ↓
              Shared Findings → Other Bots (rhodibot, sustainabot, etc.)
```

## Bot Tier

Echidnabot operates as a **Tier 1 Verifier** bot:
- **Execution Order**: 1 (runs first with other verifiers)
- **Role**: Produces findings through formal verification
- **Peers**: rhodibot (RSR compliance), sustainabot (sustainability)
- **Consumers**: glambot, seambot, finishbot (Tier 2 finishers)

## Usage

### Standalone Mode (Current)

Echidnabot works independently as before:

```rust
use echidnabot::EchidnaClient;

let client = EchidnaClient::new(&config);
let result = client.verify_proof(prover, content).await?;
```

### Fleet Mode (New)

Echidnabot can now participate in fleet orchestration:

```rust
use echidnabot::fleet::FleetIntegration;

// Create fleet integration for a repository
let mut fleet = FleetIntegration::new("my-repo", "/path/to/repo");

// Start echidnabot's execution
fleet.start()?;

// Verify proofs and record findings
for proof_file in proof_files {
    let result = echidna_client.verify_proof(prover, &content).await?;
    fleet.add_proof_result(&proof_file, &theorem_name, &prover_name, &result);
}

// Complete execution with statistics
fleet.complete(findings.len(), errors, files_analyzed)?;

// Access findings
let findings = fleet.findings();
let has_errors = fleet.has_critical_errors();
```

## Finding Types

Echidnabot generates 5 types of findings:

| Rule ID | Severity | Description | Blocks Release? |
|---------|----------|-------------|-----------------|
| ECHIDNA-VERIFY-001 | Info | Proof verified successfully | No |
| ECHIDNA-VERIFY-002 | Error | Proof verification failed | Yes |
| ECHIDNA-VERIFY-003 | Warning | Verification timed out | No |
| ECHIDNA-VERIFY-004 | Error | Verification error occurred | Yes |
| ECHIDNA-VERIFY-005 | Warning | Verification status unknown | No |

## Shared Context

The fleet uses a shared context layer (`gitbot-shared-context`) that:
- Tracks bot execution status
- Aggregates findings across all bots
- Enables cross-bot communication
- Provides release blocking logic

### Data Flow

1. **Registration**: Echidnabot registers with the fleet context
2. **Execution**: Echidnabot starts its analysis pass
3. **Findings**: Echidnabot adds findings to shared context
4. **Completion**: Echidnabot marks execution complete with stats
5. **Coordination**: Other bots can query echidnabot's findings

## Integration Points

### Fleet Coordinator

The fleet-coordinator.sh script orchestrates bot execution:

```bash
# Run full fleet scan on a repository
/path/to/gitbot-fleet/fleet-coordinator.sh run-scan /path/to/repo

# Process findings and generate fixes
/path/to/gitbot-fleet/fleet-coordinator.sh process-findings
```

### Hypatia Engine

Hypatia (neurosymbolic CI/CD engine) coordinates all bots:
- Learns patterns from echidnabot findings
- Generates rules for common proof issues
- Triggers automated fixes via robot-repo-automaton

## Testing

Fleet integration includes comprehensive tests:

```bash
# Run fleet integration tests
cargo test --lib fleet

# All 4 tests:
# - test_fleet_integration_creation
# - test_add_verified_proof
# - test_add_failed_proof
# - test_has_critical_errors
```

## Benefits

### For Users

- **Holistic Analysis**: Formal verification findings combined with structure, security, and sustainability checks
- **Better Context**: Cross-bot insights (e.g., proof errors correlated with code quality issues)
- **Automated Fixes**: Fleet can propose fixes based on patterns across repos

### For Developers

- **Shared Infrastructure**: Reuse finding types, storage, reporting across bots
- **Consistent UX**: All bots follow the same finding format
- **Learning Engine**: Hypatia learns from proof patterns to improve suggestions

## Migration

Existing echidnabot deployments continue to work without changes. Fleet integration is opt-in:

1. **Standalone**: Use `EchidnaClient` directly (current behavior)
2. **Fleet**: Use `FleetIntegration` wrapper (new capability)

## Dependencies

```toml
[dependencies]
gitbot-shared-context = { path = "../../gitbot-fleet/shared-context" }
```

## See Also

- [gitbot-fleet README](https://github.com/hyperpolymath/gitbot-fleet/blob/main/README.adoc)
- [Hypatia Documentation](https://github.com/hyperpolymath/hypatia)
- [ECHIDNA Core](https://github.com/hyperpolymath/echidna)
