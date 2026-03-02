# Supported Provers

echidnabot supports a wide range of theorem provers through ECHIDNA Core.

## Tier 1 — Full Support

These provers have complete integration with all echidnabot features.

### Coq

**Files:** `.v`

The Calculus of Inductive Constructions. Coq is a formal proof management system with a rich type theory and tactic language.

```toml
[provers.coq]
enabled = true
timeout = 120
flags = ["-R", ".", "MyProject", "-Q", "theories", "Theories"]
```

**Features:**
- ✓ File verification
- ✓ Error location (line/column)
- ✓ Tactic suggestions (ML)
- ✓ Dependency analysis

### Lean 4

**Files:** `.lean`

A functional programming language and theorem prover with a powerful metaprogramming framework.

```toml
[provers.lean4]
enabled = true
lake = true  # Use Lake build system
mathlib = false  # Import Mathlib
```

**Features:**
- ✓ File verification
- ✓ Lake project support
- ✓ Mathlib integration
- ✓ Error location
- ✓ Tactic suggestions

### Agda

**Files:** `.agda`, `.lagda`, `.lagda.md`, `.lagda.rst`, `.lagda.tex`

A dependently typed functional programming language with a focus on interactive development.

```toml
[provers.agda]
enabled = true
flags = ["--safe", "--without-K"]
```

**Features:**
- ✓ File verification
- ✓ Literate Agda support
- ✓ Error location
- ✓ Hole suggestions

### Isabelle/HOL

**Files:** `.thy`

A generic proof assistant with a focus on higher-order logic.

```toml
[provers.isabelle]
enabled = true
logic = "HOL"
session = "MySession"
```

**Features:**
- ✓ Theory verification
- ✓ Session management
- ✓ Error location

### Z3 / SMT-LIB

**Files:** `.smt2`

An efficient SMT solver for satisfiability and validity checking.

```toml
[provers.z3]
enabled = true
timeout = 60
```

**Features:**
- ✓ SMT-LIB 2 format
- ✓ Sat/Unsat results
- ✓ Model output
- ✓ Proof output

### CVC5

**Files:** `.smt2`, `.cvc5`

A modern SMT solver with support for quantifiers and theories.

```toml
[provers.cvc5]
enabled = true
incremental = true
```

## Tier 2 — Basic Support

These provers have verification support but may lack advanced features.

### Metamath

**Files:** `.mm`

A minimal proof verification system with a simple substitution-based logic.

```toml
[provers.metamath]
enabled = true
```

**Features:**
- ✓ File verification
- ✓ Error location
- ○ No tactic suggestions

### HOL Light

**Files:** `.ml`

An interactive theorem prover for classical higher-order logic.

```toml
[provers.hollight]
enabled = true
```

### Mizar

**Files:** `.miz`

A language for writing formal mathematical proofs.

```toml
[provers.mizar]
enabled = true
```

## Tier 3 — Planned

These provers are on the roadmap but not yet supported.

| Prover | Files | Status |
|--------|-------|--------|
| PVS | `.pvs` | Planned |
| ACL2 | `.lisp` | Planned |
| HOL4 | `.sml` | Planned |
| Twelf | `.elf` | Planned |
| Dedukti | `.dk` | Planned |

## Configuration Examples

### Multi-Prover Setup

```toml
[provers]
# Enable specific provers
enabled = ["coq", "lean4", "agda"]

# Coq configuration
[provers.coq]
timeout = 180
flags = ["-R", "src", "MyProject"]

# Lean 4 with Lake
[provers.lean4]
lake = true
mathlib = true

# Agda with safe mode
[provers.agda]
flags = ["--safe"]
```

### File Pattern Matching

```toml
[files]
# Only verify specific directories
include = [
  "theories/**/*.v",
  "proofs/**/*.lean",
  "specs/**/*.agda"
]

# Exclude test fixtures
exclude = [
  "test/fixtures/**",
  "examples/broken/**"
]
```

### Per-File Prover Override

echidnabot detects provers by file extension. For ambiguous cases:

```toml
[files.overrides]
"src/smt/*.smt2" = "cvc5"  # Use CVC5 instead of Z3
```

## Adding New Provers

To request support for a new prover:

1. Open an issue at [hyperpolymath/echidnabot](https://github.com/hyperpolymath/echidnabot/issues)
2. Include:
   - Prover name and website
   - File extensions
   - Verification command
   - Error format (if known)
3. Consider contributing to [ECHIDNA Core](https://github.com/hyperpolymath/echidna)

## Prover-Specific Notes

### Coq

- Use `-R` and `-Q` flags for library paths
- `_CoqProject` files are respected
- Large developments may need increased timeout

### Lean 4

- Lake projects: set `lake = true`
- For Mathlib: set `mathlib = true`
- Lake.toml/lakefile.lean must be valid

### Agda

- Standard library import: use appropriate `--include-path`
- Cubical Agda: add `--cubical` to flags
- Literate formats fully supported

### Z3

- Use `(set-option :produce-proofs true)` for proof output
- Timeouts apply per-query, not per-file
- Incremental mode for large files
