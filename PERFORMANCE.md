# ECHIDNA Performance Benchmarks

## Prover Creation Performance (2026-02-12)

All 30 prover backends can be instantiated in sub-microsecond to low-microsecond time:

| Prover | Creation Time |
|--------|--------------|
| MiniZinc | 116ns |
| Minlog | 120ns |
| Nuprl | 133ns |
| SPASS | 164ns |
| TLAPS | 164ns |
| Imandra | 164ns |
| ORTools | 164ns |
| Dafny | 162ns |
| Chuffed | 169ns |
| EProver | 172ns |
| FStar | 174ns |
| Vampire | 178ns |
| AltErgo | 182ns |
| SCIP | 231ns |
| Twelf | 228ns |
| Idris2 | 263ns |
| Why3 | 347ns |
| Coq | 416ns |
| Z3 | 426ns |
| PVS | 477ns |
| HOLLight | 502ns |
| ACL2 | 545ns |
| HOL4 | 695ns |
| Agda | 5.3µs |
| Metamath | 5.7µs |
| Mizar | 7.0µs |
| CVC5 | 7.7µs |
| Lean | 9.3µs |
| Isabelle | 15.5µs |

**Average creation time**: ~2.5µs  
**Fastest**: MiniZinc (116ns)  
**Slowest**: Isabelle (15.5µs)

All backends are extremely lightweight and can be instantiated on-demand with negligible overhead.

## Test Configuration
- CPU: (detected from system)
- Memory: 32GB
- Build: `cargo build --release`
- Test: `cargo test --release`
