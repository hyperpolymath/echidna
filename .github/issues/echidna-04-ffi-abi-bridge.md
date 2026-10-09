# ECH-04: feat(ffi): C-ABI / Zig bridge specification for embedding ParadisEO metaheuristics engine with Idris2 contracts

**ID:** ECH-04  
**Target Repository:** hyperpolymath/echidna  
**Area:** ABI / FFI / Multi-Language  
**Labels:** enhancement, area:abi, zig, idris2, ffi  
**Status:** Open  
**Roadmap:** [ParadisEO Metaheuristic Integration](../ROADMAP-PARADISEO.md)  

---

## Context & Motivation

To utilize ParadisEO's battle-tested C++17 metaheuristic engine (including mo, moeo, and edo) within ECHIDNA's Rust core without compromising memory safety or high-assurance trust guarantees, we need a formally specified and hardened FFI boundary.

ECHIDNA maintains strict type contracts using an Idris2 ABI layer (src/abi/EchidnaABI/) and Zig FFI glue.

## Proposed Changes

- **Zig C-ABI Shim (ffi/zig/paradiseo_bridge.zig):** Provide extern "C" abstraction wrapping ParadisEO's core C++ template instantiations (paradiseo_moeo_nsga2_rank, paradiseo_edo_cmaes_step, paradiseo_mo_tabu_search) with clean allocation/deallocation lifetimes and zero memory leaks across the C++/Rust boundary
- **Idris2 ABI Specification & Proofs:** Formalize parameter bounds, return value structs, and status codes in src/abi/EchidnaABI/OptimizationABI.idr with totality and non-divergence properties under %default total with 0 postulate / 0 believe_me
- **Rust Safe Bindings (crates/echidna-metaheuristics):** Expose idiomatic, memory-safe Rust wrapper structs implementing the OptimizerBackend trait, guarded behind feature flags (--features paradiseo-opt) with safe fallbacks in pure Rust

## Acceptance Criteria

- [ ] zig build test passes all FFI memory leak and lifetime checks (using Zig's GPA / GeneralPurposeAllocator)
- [ ] idris2 --build src/abi/echidnaabi.ipkg compiles and verifies totality without warnings
- [ ] cargo clippy --workspace --all-targets -D warnings and cargo test pass cleanly

## References

- [ECHIDNA ABI documentation](../docs/ABI_SPECIFICATION.adoc)
- [ParadisEO C++ source: eo](https://github.com/Alessandro624/paradiseo/tree/master/eo)
- [ParadisEO C++ source: mo](https://github.com/Alessandro624/paradiseo/tree/master/mo)
- [ParadisEO C++ source: moeo](https://github.com/Alessandro624/paradiseo/tree/master/moeo)
- [ParadisEO C++ source: edo](https://github.com/Alessandro624/paradiseo/tree/master/edo)

## Related Issues

- [ECH-01: Pareto MOEO sorting](echidna-01-pareto-moeo.md) - Uses moeo module via FFI
- [ECH-02: GNN calibration](echidna-02-cmaes-julia-gnn.md) - Uses EDO module via FFI
- [ECH-03: Chapel island model](echidna-03-chapel-island-migration.md) - Uses SMP/PEO modules via FFI
- [PB-01: proof-burrower swarm](https://github.com/hyperpolymath/proof-burrower/issues/proof-burrower-01-combinatorial-tactic-synthesis.md) - Uses MO module via FFI
- [PB-02: proof-burrower ledger](https://github.com/hyperpolymath/proof-burrower/issues/proof-burrower-02-ledger-fitness-formulation.md) - Uses ParadisEO via FFI

---

**See Also:** [Full ParadisEO Roadmap](../ROADMAP-PARADISEO.md)  
**Repository:** [hyperpolymath/echidna](https://github.com/hyperpolymath/echidna)
