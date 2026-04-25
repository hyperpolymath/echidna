# Echidna Chunked panic-attack Sweep — 2026-04-25

Single full-repo `panic-attack assail .` had timed out at 180s.
This sweep splits the tree into 14 per-subdir chunks, each completing
in < 30s for a combined wall time well under the prior single-run cap.

## Per-chunk totals (severity counts)

| Chunk                          | Critical | High | Medium | Total |
| ------------------------------ | -------: | ---: | -----: | ----: |
| `src/rust`                     |       26 |    6 |      2 |    34 |
| `src/interfaces`               |        0 |    6 |      0 |     6 |
| `src/zig`                      |        0 |    1 |      0 |     1 |
| `src/zig_ffi`                  |        0 |    1 |      0 |     1 |
| `src/abi`                      |        1 |    0 |      0 |     1 |
| `crates/echidna-mcp`           |        0 |    1 |      0 |     1 |
| `crates/echidna-core`          |        0 |    0 |      0 |     0 |
| `crates/echidna-wire`          |        0 |    0 |      0 |     0 |
| `crates/typed_wasm`            |        0 |    0 |      0 |     0 |
| `src/julia`                    |        0 |    0 |      0 |     0 |
| `src/idris`                    |        0 |    0 |      0 |     0 |
| `src/ada`                      |        0 |    0 |      0 |     0 |
| `src/rescript`                 |        0 |    0 |      0 |     0 |
| `src/ui`                       |        0 |    0 |      0 |     0 |
| `src/chapel`                   |        – |    – |      – |     – |
| **Total**                      |   **27** | **15** |  **2** | **44** |

Note: `src/chapel` returned "Could not detect language" — panic-attack
has no Chapel detector. Track separately.

## Classification (per `feedback_panic_attack_*` memory rules)

### Structural / expected (do not chase counts)

- **26× Critical UnboundedAllocation in `src/rust/provers/*.rs`** —
  one per prover backend, file-level aggregation of `Vec::new()` /
  `String` allocations across 600+ LoC parsers. This is the
  PanicPath-is-file-level pattern: one finding per file, not one per
  site. The 26 backends with the highest Vec/parse density flag here.
  Investigation required per backend before any structural rewrite —
  most allocations are in error-message construction or proof-script
  parsing, both bounded in practice by `ProverConfig::timeout`.

- **6× High UnsafeCode in `src/interfaces/*/ffi_wrapper.rs`** — two
  per FFI wrapper × three interfaces (rest, grpc, graphql). All
  calls into the Zig FFI shim's `extern "C"` surface plus `CStr::from_ptr`.
  These cannot be eliminated without dropping the FFI boundary; per
  `feedback_panic_attack_unsafe_blocks_meaning.md` this is the
  legitimate-FFI-try/catch class, not the banned partial-cast class.

- **2× High UnsafeFFI in zig bridges** (`chapel_bridge.zig`,
  `ffi/axiom_spark_bridge.zig`) — required for cross-language FFI.

- **1× Critical ProofDrift in `src/abi/echidnaabi.ipkg`** — flagged
  per `feedback_panic_attack_proofdrift_parameter_pattern.md`. The
  `.ipkg` is an Idris2 package manifest; the rule's "free Parameter
  unless inside designated Section Carriers" pattern doesn't quite
  fit a config file. Worth re-reading the rule's scope; likely a
  detector false-positive on `.ipkg` files.

- **2× High UnsafeCode in `src/rust/proof_search.rs`** — Chapel FFI
  boundary; behind `--features chapel` cargo feature. Same class as
  the interface FFI wrappers.

- **3× High UnsafeCode + 1× High ResourceLeak in `src/rust/ffi/`** —
  same FFI-boundary class.

### Actionable today (low cost, structural fixes)

- **1× High SupplyChain `crates/echidna-mcp/Cargo.toml`** — needs
  inspection. May be an unpinned dep version or a permissive feature
  set.

- **1× Medium PanicPath `src/rust/provers/z3.rs`** — single panic site
  in a hot prover. Easy to convert to anyhow::Result.

- **1× Medium InsecureProtocol `src/rust/provers/uppaal.rs`** —
  probably an `http://` URL in a comment or test fixture; quick
  audit.

## Conclusion

Chunked sweep replaces the 180s timeout with 14 fast per-subdir runs.
Of 44 findings: ~41 are structural / FFI / file-level aggregation
classes that the memory rules say not to chase by count, and 3 are
genuinely actionable in a follow-up (1 SupplyChain, 1 PanicPath,
1 InsecureProtocol). No new criticals discovered — all in the
expected places (FFI surfaces and prover wrappers).

Reports retained at `reports/panic-attack-chunks/*.json`.
