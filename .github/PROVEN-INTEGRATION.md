# proven Integration Plan

This document outlines the recommended [proven](https://github.com/hyperpolymath/proven) modules for ECHIDNA.

## Recommended Modules

| Module | Purpose | Priority |
|--------|---------|----------|
| SafeGraph | Directed graphs with cycle detection proofs for proof dependency tracking | High |
| SafeOrdering | Temporal ordering with causality proofs for proof step sequencing | High |
| SafeConsensus | Distributed consensus with quorum proofs for multi-prover agreement | High |

## Integration Notes

ECHIDNA as a neurosymbolic theorem proving platform supporting 12 provers requires formally verified proof management:

- **SafeGraph** models proof dependencies as DAGs. The `Acyclic` proof guarantees no circular dependencies in proof chains, and `topoSort` provides correct ordering for proof verification. `PathExists` verifies lemma reachability.

- **SafeOrdering** sequences proof steps with verified causality. When combining proofs from multiple provers, the vector clock implementation ensures steps are merged in the correct order. `CausalDelivery` guarantees proper ordering of distributed proof events.

- **SafeConsensus** enables multi-prover agreement. When multiple provers (Coq, Lean, Agda, etc.) verify the same theorem, `Quorum` proves sufficient agreement, and `Agreement` proves all agreeing provers have the same result.

As ECHIDNA already uses proven for its Idris 2 proofs (see `Proven/FFI/Echidna.idr`), these modules extend that integration to the proof orchestration layer.

## Related

- [proven library](https://github.com/hyperpolymath/proven)
- [Idris 2 documentation](https://idris2.readthedocs.io/)
- [ECHIDNA-proven FFI](https://github.com/hyperpolymath/proven/blob/main/src/Proven/FFI/Echidna.idr)
