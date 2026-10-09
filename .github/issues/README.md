# Echidna Issue Specifications

This directory contains the canonical issue specifications for the ParadisEO metaheuristic integration work.

## Status

- **ECH-01..04 bodies and labels**: Synchronised with GitHub issues #420, #421, #422, #424
- **PB-01, PB-02**: Draft specifications for hyperpolymath/proof-burrower (unverified claims)
- **EB-01**: Draft specification for hyperpolymath/echidnabot (unverified claims)

## Provenance

- **ECH-01..04**: Created from local issue files, not yet pushed to GitHub
- **PB-01**: Based on read-only look at proof-burrower@be897dd
- **PB-02**: Based on read-only look at proof-burrower@be897dd
- **EB-01**: Based on read-only look at echidnabot@ae52833

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
