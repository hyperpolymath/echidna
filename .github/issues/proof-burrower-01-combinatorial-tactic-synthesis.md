# PB-01: feat(swarm): combinatorial tactic playbook synthesis using delta/partial neighborhood evaluation (ParadisEO-mo)

**ID:** PB-01  
**Target Repository:** hyperpolymath/proof-burrower  
**Area:** Rust / Search Engine  
**Labels:** enhancement, area:swarm, rust, search-tactics  
**Status:** Draft (unverified)  

**Provenance:** Based on read-only look at proof-burrower@be897dd07e1a16014f2d0f8d9cbedffb0240dd4a  

---

## Context & Motivation

The Proof Burrower system performs automated tactic selection and proof search. Currently, it uses heuristic-based selection which can miss optimal tactic combinations.

ParadisEO-mo (Multi-Objective Optimization) provides delta/partial neighborhood evaluation capabilities that can intelligently explore combinatorial search spaces. Applying these to Proof Burrower's tactic playbook synthesis would enable more systematic exploration of tactic combinations.

## Current State

Verified against proof-burrower@be897dd07e1a16014f2d0f8d9cbedffb0240dd4a:
- `TacticTemplate/Playbook/run_playbook/generate_probe` exists in `crates/burrower-core/src/attempt.rs`
- `SWARM_RELEVANCE_THRESHOLD = 0.02` is defined in `specialist.rs`
- `Swarm::attempt_all` exists in `specialist.rs`

## Proposed Changes

- **Delta Evaluation**: Implement ParadisEO-mo delta evaluation to measure marginal improvement of adding/removing tactics from playbooks
- **Partial Neighborhood Search**: Use mo's partial neighborhood evaluation to explore tactic combinations without full re-evaluation
- **Playbook Optimization**: Apply multi-objective optimization to synthesize optimal tactic playbooks for different proof domains

## Acceptance Criteria

- [ ] Delta evaluation reduces playbook synthesis time by at least 30%
- [ ] Partial neighborhood search maintains proof success rate while exploring fewer combinations
- [ ] Optimized playbooks outperform hand-crafted playbooks on benchmark corpus

## References

- ParadisEO-mo module in nojhan/paradiseo
- Proof Burrower architecture documentation

---

**Related Issues:**
- [ECH-04: FFI bridge](echidna-04-ffi-abi-bridge.md) - Enables direct ParadisEO-mo integration

**Repository:** [hyperpolymath/proof-burrower](https://github.com/hyperpolymath/proof-burrower)
