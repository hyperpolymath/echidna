# Chapel Metalayer: Pluggable Architecture Design

**Status**: Design Document
**Date**: 2026-01-29
**Purpose**: Make Chapel optional to avoid intimidating non-Chapel developers

---

## Design Principle

**Chapel should be a performance accelerator, not a barrier to entry.**

Developers should be able to:
- ✅ Contribute to ECHIDNA without knowing Chapel
- ✅ Run ECHIDNA without Chapel installed
- ✅ Add new provers without touching Chapel code
- ✅ Work on Chapel layer independently if desired

---

## Architecture: Chapel as Optional Plugin

```
┌─────────────────────────────────────────────────────────┐
│  ECHIDNA Core (Rust)                                   │
│  - Always available                                     │
│  - Sequential proof search (default)                    │
│  - No Chapel dependency                                 │
└────────────────────┬────────────────────────────────────┘
                     │
                     │ Trait: ProofSearchStrategy
                     │
       ┌─────────────┴──────────────┐
       │                            │
   ┌───▼──────────┐        ┌────────▼────────────────┐
   │  Sequential  │        │  Chapel Parallel        │
   │  (Built-in)  │        │  (Optional Plugin)      │
   │              │        │                         │
   │  - Rust only │        │  - Feature flag         │
   │  - No deps   │        │  - Separate crate       │
   │  - Always on │        │  - FFI boundary         │
   └──────────────┘        └─────────────────────────┘
```

---

## Implementation Strategy

### 1. Trait-Based Abstraction

**Define common interface** (no Chapel knowledge needed):

```rust
// src/rust/core/proof_search.rs
pub trait ProofSearchStrategy: Send + Sync {
    /// Search for proof using this strategy
    fn search(
        &self,
        goal: &str,
        provers: &[Box<dyn ProverBackend>],
        timeout: Duration,
    ) -> Result<ProofResult>;

    /// Strategy name for logging
    fn name(&self) -> &str;

    /// Can this strategy run? (checks dependencies)
    fn available(&self) -> bool;
}
```

**Sequential implementation** (always available):

```rust
// src/rust/core/sequential_search.rs
pub struct SequentialSearch;

impl ProofSearchStrategy for SequentialSearch {
    fn search(
        &self,
        goal: &str,
        provers: &[Box<dyn ProverBackend>],
        timeout: Duration,
    ) -> Result<ProofResult> {
        // Try each prover in order
        for prover in provers {
            if let Ok(result) = prover.prove(goal) {
                return Ok(result);  // Stop at first success
            }
        }
        Err(Error::AllProversFailed)
    }

    fn name(&self) -> &str {
        "Sequential"
    }

    fn available(&self) -> bool {
        true  // Always available
    }
}
```

**Chapel implementation** (optional, behind feature flag):

```rust
// src/rust/chapel/parallel_search.rs
#[cfg(feature = "chapel")]
pub struct ChapelParallelSearch {
    ffi: ChapelFFI,
}

#[cfg(feature = "chapel")]
impl ProofSearchStrategy for ChapelParallelSearch {
    fn search(
        &self,
        goal: &str,
        provers: &[Box<dyn ProverBackend>],
        timeout: Duration,
    ) -> Result<ProofResult> {
        // Call Chapel via FFI
        self.ffi.parallel_search(goal, provers, timeout)
    }

    fn name(&self) -> &str {
        "Chapel Parallel"
    }

    fn available(&self) -> bool {
        // Check if Chapel runtime is available
        self.ffi.is_loaded()
    }
}
```

---

### 2. Cargo Feature Flag

**Cargo.toml**:
```toml
[features]
default = []  # Chapel NOT enabled by default
chapel = ["dep:chapel-sys"]  # Enable with --features chapel

[dependencies]
# Always available (no Chapel)
serde = "1.0"
tokio = { version = "1.0", features = ["full"] }
# ... other deps

[dependencies.chapel-sys]
version = "0.1"
optional = true  # Only if 'chapel' feature enabled
```

**Conditional compilation**:
```rust
// src/rust/lib.rs
pub mod core;
pub mod provers;

#[cfg(feature = "chapel")]
pub mod chapel;  // Only compile if --features chapel
```

---

### 3. Runtime Strategy Selection

**Auto-detect best available strategy**:

```rust
// src/rust/core/strategy_selector.rs
pub struct StrategySelector {
    strategies: Vec<Box<dyn ProofSearchStrategy>>,
}

impl StrategySelector {
    pub fn auto() -> Self {
        let mut strategies: Vec<Box<dyn ProofSearchStrategy>> = vec![];

        // Always add sequential (fallback)
        strategies.push(Box::new(SequentialSearch));

        // Try to add Chapel (if feature enabled and runtime available)
        #[cfg(feature = "chapel")]
        {
            use crate::chapel::ChapelParallelSearch;

            if let Ok(chapel) = ChapelParallelSearch::new() {
                if chapel.available() {
                    strategies.push(Box::new(chapel));
                    info!("Chapel parallel search enabled");
                } else {
                    warn!("Chapel feature enabled but runtime not found");
                }
            }
        }

        Self { strategies }
    }

    /// Get best available strategy (prefers parallel if available)
    pub fn best(&self) -> &dyn ProofSearchStrategy {
        // Prefer later entries (Chapel if available)
        self.strategies.last().unwrap().as_ref()
    }

    /// Get strategy by name
    pub fn by_name(&self, name: &str) -> Option<&dyn ProofSearchStrategy> {
        self.strategies.iter()
            .find(|s| s.name() == name)
            .map(|s| s.as_ref())
    }
}
```

**Usage**:
```rust
// Automatic (uses best available)
let selector = StrategySelector::auto();
let strategy = selector.best();
let result = strategy.search(goal, &provers, timeout)?;

// Manual selection
let strategy = selector.by_name("Sequential")
    .ok_or(Error::StrategyNotFound)?;
```

---

### 4. Separate Chapel Crate (Optional)

**Project structure**:
```
echidna/
├── Cargo.toml              # Main crate
├── src/rust/
│   ├── lib.rs              # Core (no Chapel)
│   ├── core/               # Always available
│   ├── provers/            # Always available
│   └── chapel/             # Only if feature enabled
│       └── ffi.rs
│
└── crates/
    └── echidna-chapel/     # Separate crate (optional)
        ├── Cargo.toml
        ├── src/
        │   ├── lib.rs      # Rust FFI bindings
        │   └── ffi.rs
        ├── chapel/
        │   ├── parallel_proof_search.chpl
        │   └── build.sh
        └── README.md       # Chapel-specific docs
```

**Workspace Cargo.toml**:
```toml
[workspace]
members = [
    ".",                    # Main crate (core)
    "crates/echidna-chapel" # Optional Chapel crate
]

[dependencies]
# Main crate doesn't depend on echidna-chapel by default

[dependencies.echidna-chapel]
path = "crates/echidna-chapel"
optional = true
```

**Benefits**:
- Chapel developers work in `crates/echidna-chapel/` only
- Core developers never see Chapel code
- Separate CI jobs for Chapel (can skip if not changed)
- Independent versioning possible

---

### 5. Build System Integration

**Justfile** (primary build system):
```justfile
# Build without Chapel (default)
build:
    cargo build --release

# Build with Chapel (opt-in)
build-chapel:
    #!/usr/bin/env bash
    echo "Building with Chapel support..."

    # Check Chapel availability
    if ! command -v chpl &> /dev/null; then
        echo "ERROR: Chapel compiler not found"
        echo "Install Chapel or build without: just build"
        exit 1
    fi

    # Build Chapel module
    cd crates/echidna-chapel/chapel
    ./build.sh

    # Build Rust with Chapel feature
    cargo build --release --features chapel

# Test without Chapel
test:
    cargo test

# Test with Chapel
test-chapel:
    cargo test --features chapel

# Check if Chapel is available
check-chapel:
    #!/usr/bin/env bash
    if command -v chpl &> /dev/null; then
        echo "✓ Chapel available: $(chpl --version)"
    else
        echo "✗ Chapel not found"
        echo "  ECHIDNA will use sequential search (no Chapel needed)"
    fi
```

**Developer experience**:
```bash
# Regular developer (no Chapel)
just build    # ✓ Works! (sequential search)
just test     # ✓ Works! (all tests except Chapel)

# Chapel developer
just check-chapel          # Check if Chapel installed
just build-chapel          # Build with Chapel support
just test-chapel           # Test Chapel integration
```

---

### 6. Documentation Separation

**Main README.md** (Chapel optional):
```markdown
# ECHIDNA

Neurosymbolic theorem proving platform.

## Quick Start

```bash
# Install (no Chapel needed)
cargo install echidna

# Run
echidna prove "forall n, n + 0 = n"
```

## Optional: Chapel Parallel Search

For 12x faster proof search, install Chapel:
```bash
# See CHAPEL.md for installation
just build-chapel
```
```

**CHAPEL.md** (separate file for Chapel devs):
```markdown
# Chapel Metalayer Developer Guide

## Prerequisites

- Chapel 2.2+ installed
- Rust 1.75+ installed

## Building Chapel Layer

```bash
cd crates/echidna-chapel
./build.sh
```

## Chapel Code Structure

- `chapel/parallel_proof_search.chpl` - Main parallel search
- `chapel/ffi.chpl` - C FFI exports
- `src/ffi.rs` - Rust FFI bindings

## Testing Chapel Integration

```bash
cargo test --features chapel -- --nocapture
```

## Contributing to Chapel Layer

See CONTRIBUTING-CHAPEL.md for guidelines.
```

**CONTRIBUTING.md** (makes Chapel optional clear):
```markdown
# Contributing to ECHIDNA

## I don't know Chapel - can I still contribute?

**Yes!** Chapel is completely optional.

Most development happens in:
- `src/rust/core/` - Core logic (Rust)
- `src/rust/provers/` - Prover backends (Rust)
- `src/julia/` - ML models (Julia)

You can add new provers, improve ML, fix bugs, etc. without
ever touching Chapel code.

## I know Chapel - how can I help?

See `crates/echidna-chapel/CONTRIBUTING-CHAPEL.md` for
Chapel-specific contribution guidelines.
```

---

### 7. CI/CD Matrix

**GitHub Actions** (test with and without Chapel):

```yaml
# .github/workflows/ci.yml
name: CI

on: [push, pull_request]

jobs:
  test-without-chapel:
    name: Test (No Chapel)
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable

      # Build without Chapel (default)
      - run: cargo build
      - run: cargo test

      # This should always pass (no Chapel dependency)

  test-with-chapel:
    name: Test (With Chapel)
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable

      # Install Chapel
      - name: Install Chapel
        run: |
          wget https://github.com/chapel-lang/chapel/releases/download/2.2.0/chapel-2.2.0-1.el9.x86_64.rpm
          sudo rpm -i chapel-2.2.0-1.el9.x86_64.rpm

      # Build with Chapel feature
      - run: cargo build --features chapel
      - run: cargo test --features chapel

      # Only runs if Chapel CI job enabled
      # (can skip for PRs that don't touch Chapel)
```

**Skip Chapel CI if not needed**:
```yaml
# .github/workflows/ci-chapel.yml
name: CI Chapel

on:
  push:
    paths:
      - 'crates/echidna-chapel/**'  # Only run if Chapel code changed
      - 'chapel_poc/**'

jobs:
  chapel-only:
    # ... Chapel-specific tests
```

---

### 8. API: Sequential vs Parallel Transparent

**Users don't need to know which strategy is used**:

```rust
// High-level API (strategy auto-selected)
use echidna::Echidna;

let echidna = Echidna::new();  // Auto-detects Chapel if available
let result = echidna.prove("forall n, n + 0 = n")?;

println!("Proof: {}", result.proof);
println!("Strategy used: {}", result.strategy);  // "Sequential" or "Chapel Parallel"
```

**Advanced users can force a strategy**:

```rust
// Force sequential (even if Chapel available)
let echidna = Echidna::builder()
    .strategy("Sequential")
    .build()?;

// Force Chapel (error if not available)
let echidna = Echidna::builder()
    .strategy("Chapel Parallel")
    .build()?;
```

---

## 9. Migration Path for Existing Code

**Before** (Chapel mixed into core):
```rust
// OLD (bad - Chapel mixed in)
pub fn prove(goal: &str) -> Result<Proof> {
    #[cfg(feature = "chapel")]
    {
        chapel_parallel_search(goal)
    }

    #[cfg(not(feature = "chapel"))]
    {
        sequential_search(goal)
    }
}
```

**After** (trait-based abstraction):
```rust
// NEW (good - strategy pattern)
pub fn prove(goal: &str) -> Result<Proof> {
    let selector = StrategySelector::auto();
    let strategy = selector.best();
    strategy.search(goal, &provers, timeout)
}
```

**Benefits**:
- No `#[cfg]` conditionals scattered everywhere
- Easy to add new strategies (Dask, Ray, Spark...)
- Clear separation of concerns
- Chapel developers work in isolated crate

---

## 10. Developer Personas

### Persona 1: Core Developer (No Chapel)

**Sarah** - Wants to add a new prover (Metamath)

**Experience**:
```bash
$ git clone echidna
$ cd echidna
$ just build        # ✓ Works! (no Chapel needed)
$ cargo test        # ✓ All core tests pass

# Add new prover
$ edit src/rust/provers/metamath.rs
$ cargo test provers::metamath  # ✓ Tests pass

# Contribution accepted - never touched Chapel!
```

### Persona 2: Chapel Specialist

**Bob** - Wants to optimize Chapel parallel search

**Experience**:
```bash
$ git clone echidna
$ cd echidna/crates/echidna-chapel

# Install Chapel
$ sudo dnf install chapel

# Work on Chapel code
$ edit chapel/parallel_proof_search.chpl
$ ./build.sh

# Test Chapel integration
$ cargo test --features chapel

# Contribution accepted - never touched core Rust!
```

### Persona 3: End User (No Development)

**Alice** - Just wants to prove theorems

**Experience**:
```bash
# Install from crates.io (no Chapel)
$ cargo install echidna

# Works out of the box
$ echidna prove "forall n, n + 0 = n"
✓ Proved! (strategy: Sequential, time: 2.3s)

# Optional: Install Chapel for speedup
$ sudo dnf install chapel
$ cargo install echidna --features chapel

$ echidna prove "forall n, n + 0 = n"
✓ Proved! (strategy: Chapel Parallel, time: 0.8s)
```

---

## 11. Testing Strategy

### Unit Tests (No Chapel Required)

```rust
// tests/proof_search_tests.rs
#[test]
fn test_sequential_search() {
    let strategy = SequentialSearch;
    let provers = mock_provers();
    let result = strategy.search("n + 0 = n", &provers, timeout).unwrap();
    assert!(result.success);
}

// Runs without --features chapel
```

### Integration Tests (Chapel Optional)

```rust
// tests/chapel_integration_tests.rs
#[cfg(feature = "chapel")]
mod chapel_tests {
    use echidna::chapel::ChapelParallelSearch;

    #[test]
    fn test_chapel_parallel() {
        let strategy = ChapelParallelSearch::new().unwrap();
        // ... test Chapel-specific features
    }
}

// Only runs with --features chapel
```

---

## 12. Documentation Examples

### Rust Docs (Chapel Optional)

```rust
/// Prove a theorem using available strategies.
///
/// # Example
///
/// ```
/// # use echidna::Echidna;
/// let echidna = Echidna::new();
/// let result = echidna.prove("forall n, n + 0 = n")?;
/// ```
///
/// # Performance
///
/// If built with `--features chapel`, this will use parallel
/// search across 12 provers. Otherwise, sequential search is used.
///
/// To force a specific strategy:
///
/// ```
/// # use echidna::Echidna;
/// let echidna = Echidna::builder()
///     .strategy("Sequential")  // Force sequential
///     .build()?;
/// ```
pub fn prove(&self, goal: &str) -> Result<Proof> {
    // ...
}
```

---

## 13. Performance Comparison (Auto-Logged)

**Users see which strategy was used**:

```bash
$ echidna prove "forall n m, n + m = m + n" --verbose

[INFO] Available strategies: Sequential
[INFO] Using strategy: Sequential
[INFO] Trying Coq... ✓ Success (2.3s)
✓ Proved!

# With Chapel installed:
$ echidna prove "forall n m, n + m = m + n" --verbose

[INFO] Available strategies: Sequential, Chapel Parallel
[INFO] Using strategy: Chapel Parallel
[INFO] Trying 12 provers in parallel...
[INFO]   ✓ Coq succeeded (1.2s)
[INFO]   ✓ Lean succeeded (1.5s)
[INFO]   ✓ Agda succeeded (1.8s)
✓ Proved! (best: Coq, 1.2s)
```

---

## 14. Justfile Targets Summary

```justfile
# Core (no Chapel)
build           # Build without Chapel (default)
test            # Test without Chapel
check           # Lint/format check

# Chapel (optional)
build-chapel    # Build with Chapel support
test-chapel     # Test Chapel integration
check-chapel    # Check if Chapel is available
bench-chapel    # Benchmark parallel vs sequential

# Documentation
docs            # Generate docs (Chapel optional sections marked)
docs-chapel     # Generate Chapel-specific docs
```

---

## Conclusion

**Chapel is now a performance plugin, not a core dependency.**

✅ **Core developers** - Work in Rust, never touch Chapel
✅ **Chapel developers** - Work in `crates/echidna-chapel/`, isolated
✅ **End users** - Install without Chapel, opt-in for performance
✅ **CI/CD** - Test both with and without Chapel
✅ **Documentation** - Clear separation of core vs Chapel docs

**No developer is blocked by lack of Chapel knowledge.**

The system falls back gracefully to sequential search if Chapel is unavailable, and transparently uses parallel search if it is available.

---

*ECHIDNA Chapel Pluggability Design*
*Co-Authored-By: Claude Sonnet 4.5 <noreply@anthropic.com>*
