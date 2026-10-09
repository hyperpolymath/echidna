# Echidna Issue Specifications

This directory contains the canonical issue specifications for the ParadisEO metaheuristic integration work.

## Status

- **ECH-01..04 bodies and labels**: Synchronised with GitHub issues #420, #421, #422, #424
- **PB-01**: Filed as hyperpolymath/proof-burrower#108 (verified against be897dd07e1a16014f2d0f8d9cbedffb0240dd4a)
- **PB-02**: Filed as hyperpolymath/proof-burrower#109 (verified against be897dd07e1a16014f2d0f8d9cbedffb0240dd4a)
- **EB-01**: Filed as hyperpolymath/echidnabot#177 (verified against ae5283323b815f82d2a556080b59e0bb648de62b)

## Provenance

- **ECH-01..04**: Created from local issue files, synchronised with GitHub
- **PB-01**: Based on read-only look at proof-burrower@be897dd07e1a16014f2d0f8d9cbedffb0240dd4a (corrected claims)
- **PB-02**: Based on read-only look at proof-burrower@be897dd07e1a16014f2d0f8d9cbedffb0240dd4a (corrected RecordResult.status and Learning.pattern_kind values)
- **EB-01**: Based on read-only look at echidnabot@ae5283323b815f82d2a556080b59e0bb648de62b (corrected: [scheduler] job_timeout_seconds does not exist)

## File Index

| ID | File | Target Repository | Title |
|----|------|-------------------|-------|
| ECH-01 | echidna-01-pareto-moeo.md | hyperpolymath/echidna | feat(pareto): integrate exact hypervolume indicator and MOEO non-dominated sorting |
| ECH-02 | echidna-02-cmaes-julia-gnn.md | hyperpolymath/echidna | feat(ml): black-box hyperparameter & temperature calibration for GNN premise rankers |
| ECH-03 | echidna-03-chapel-island-migration.md | hyperpolymath/echidna | feat(chapel): island-model asynchronous migration topologies |
| ECH-04 | echidna-04-ffi-abi-bridge.md | hyperpolymath/echidna | feat(ffi): C-ABI / Zig bridge specification |
| PB-01 | proof-burrower-01-combinatorial-tactic-synthesis.md | hyperpolymath/proof-burrower | feat(swarm): combinatorial tactic playbook synthesis |
| PB-02 | proof-burrower-02-ledger-fitness-formulation.md | hyperpolymath/proof-burrower | feat(ledger): anti-pattern mining and objective fitness formulation |
| EB-01 | echidnabot-01-adaptive-ci-portfolio-scheduler.md | hyperpolymath/echidnabot | feat(dispatcher): adaptive portfolio timeout and solver selection |

## Usage

These files serve as the source of truth for issue bodies. When updating GitHub issues, use:

```bash
awk 'f;/^# /{f=1}' issues/<file> | sed '1{/^$/d}' > /tmp/body.md
```

This extracts the body (everything after the first `# ` heading) and removes leading empty lines.
