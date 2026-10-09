# PB-02: feat(ledger): anti-pattern mining and objective fitness formulation from burrow.jsonl for heuristic guidance

**ID:** PB-02  
**Target Repository:** hyperpolymath/proof-burrower  
**Area:** Rust / Ledger & Indexing  
**Labels:** enhancement, area:ledger, rust, heuristics  
**Status:** Draft (unverified)  

**Provenance:** Based on read-only look at proof-burrower@be897dd07e1a16014f2d0f8d9cbedffb0240dd4a  

---

## Context & Motivation

Proof Burrower maintains a ledger of proof attempts and outcomes in `burrow.jsonl` format. This historical data contains valuable patterns about which tactics succeed or fail in different contexts.

Currently, this data is underutilized for guiding future proof attempts. ParadisEO's optimization frameworks can help extract anti-patterns and formulate fitness functions to guide heuristic search.

## Current State

Verified against proof-burrower@be897dd07e1a16014f2d0f8d9cbedffb0240dd4a:
- `LedgerRecord` struct exists in `ledger.rs`
- `anti_patterns_for` function exists in `ledger.rs`
- `goal_hash` and `goal_id` are used in `ledger.rs`
- `RecordResult.status` values include: succeeded, failed, partial, abandoned, proposed (NOT timeout, skipped, oracle-counter-example as previously claimed)
- `Learning.pattern_kind` values include: positive, anti-pattern, specialisation, boundary (NOT the previously claimed values)

## Proposed Changes

- **Anti-Pattern Mining**: Systematically extract failure patterns from `burrow.jsonl` using data mining techniques
- **Fitness Formulation**: Develop objective fitness functions that score tactic applicability based on historical outcomes
- **Heuristic Guidance**: Use mined patterns to guide tactic selection in future proof attempts

## Acceptance Criteria

- [ ] Anti-pattern mining identifies at least 10 distinct failure modes
- [ ] Fitness formulation improves proof success rate by at least 5%
- [ ] Heuristic guidance reduces redundant proof attempts

## References

- ParadisEO data mining and optimization modules
- Proof Burrower ledger documentation

---

**Related Issues:**
- [ECH-04: FFI bridge](echidna-04-ffi-abi-bridge.md) - Enables direct ParadisEO integration

**Repository:** [hyperpolymath/proof-burrower](https://github.com/hyperpolymath/proof-burrower)
