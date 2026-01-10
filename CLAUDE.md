# CLAUDE.md

This document provides guidelines and context for working with Claude Code on the ECHIDNA project.

## Project Overview

**ECHIDNA** (Extensible Cognitive Hybrid Intelligence for Deductive Neural Assistance) is a neurosymbolic theorem proving platform supporting 12 theorem provers with aspect tagging, OpenCyc, and DeepProbLog integration.

**Repository**: https://github.com/hyperpolymath/echidna

## Repository Structure

```
echidna/
├── .git/              # Git repository
├── CLAUDE.md          # This file
├── src/               # Source code
│   ├── rust/          # Rust core/FFI/WASM
│   ├── julia/         # Julia ML components
│   ├── rescript/      # ReScript+Deno UI
│   └── mercury/       # Mercury/Logtalk logic (optional)
├── templates/         # RSR/CCCP compliance templates
├── scripts/           # Automation scripts
├── docs/              # Documentation
├── tests/             # Test suite
└── Justfile           # Primary build system
```

## Working with Claude Code

### General Guidelines

1. **Code Quality**: Maintain high code quality standards with proper error handling, tests, and documentation
2. **Git Workflow**: Follow conventional commit messages and keep commits atomic
3. **Security**: Be vigilant about security vulnerabilities (XSS, SQL injection, command injection, etc.)
4. **Dependencies**: Document all dependencies and their purposes

### Development Workflow

When working on features or fixes:

1. Create feature branches with descriptive names (prefix with `claude/` for Claude Code branches)
2. Write clear, concise commit messages
3. Test changes thoroughly before committing
4. Update documentation as needed

### Commit Message Format

Follow conventional commit format:
- `feat:` - New features
- `fix:` - Bug fixes
- `docs:` - Documentation changes
- `refactor:` - Code refactoring
- `test:` - Adding or updating tests
- `chore:` - Maintenance tasks

Example: `feat: add user authentication module`

### Code Style

- Use consistent formatting throughout the codebase
- Include comments for complex logic
- Keep functions small and focused
- Use meaningful variable and function names

### Testing

- Write tests for new features
- Ensure existing tests pass before committing
- Include both unit and integration tests where appropriate
- Run `cargo test` before committing Rust changes

### Documentation

- Update README.adoc for user-facing changes
- Document API endpoints and interfaces
- Include inline comments for complex algorithms
- Keep this CLAUDE.md updated with project-specific guidelines

## Project-Specific Context

### Tech Stack

**4-Language Architecture** (use as few languages as necessary):
- **Julia**: Machine learning components (replaces Python - NO PYTHON ALLOWED)
- **Rust**: Core logic, FFI, WASM compilation
- **ReScript + Deno**: User interface
- **Mercury/Logtalk**: Optional logic reservoir

**Prover Support** (12 Total - ALL IMPLEMENTED):
- **Tier 1 (6)**: Agda, Coq/Rocq, Lean, Isabelle, Z3, CVC5
- **Tier 2 (3)**: Metamath, HOL Light, Mizar
- **Tier 3 (2)**: PVS, ACL2
- **Tier 4 (1)**: HOL4

### Key Dependencies

**Development Tools**:
- Justfile (PRIMARY build system, not Make)
- Podman (not Docker)
- GitHub Actions CI/CD
- Trivy (security scanning)

**Quality Checkers**:
- REUSE (license compliance)
- Aqua.jl (dependency security)
- JET.jl (static analysis)
- Coverage.jl (test coverage)

**Integrations**:
- OpenCyc ontology
- DeepProbLog probabilistic logic

### Architecture

**12-Prover System**: Based on "Big Six" theorem provers covering >70% of standard theorems.

**Key Components**:
- `src/rust/provers/mod.rs`: ProverBackend trait and factory
- `src/rust/provers/*.rs`: Individual prover implementations
- `src/rust/core/`: Core types (Term, ProofState, Tactic, etc.)
- `src/rust/agent/`: Agentic proof search
- Aspect tagging system
- Neural solver integration
- Universal prover abstraction layer

### Current Status

**Completed**:
- ✅ All 12 prover backends implemented
- ✅ 99 unit tests passing
- ✅ 38 integration tests passing
- ✅ RSR/CCCP compliance templates
- ✅ Complete Rust trait system

**In Progress**:
- Neural/ML integration (Julia components)
- UI implementation (ReScript + Deno)

## Useful Commands

```bash
# Build System (Justfile is PRIMARY)
just build              # Build the project
just test               # Run tests
just check              # Run all quality checkers

# Cargo commands
cargo build             # Build Rust code
cargo test              # Run all tests
cargo test --lib        # Run unit tests only
cargo test --test integration_tests  # Run integration tests

# Container Management (Podman, not Docker)
podman build -f Containerfile .   # Build container
podman run echidna                # Run container

# Quality Checks
reuse lint                        # License compliance
cargo clippy                      # Rust lints
cargo fmt --check                 # Format check
```

## Resources

- [RSR/CCCP Compliance](https://rhodium-standard.org) - Rhodium Standard Repository
- [Palimpsest License v0.6](https://palimpsest.license)

## Notes for Claude Code

### Priorities

1. Code correctness and security
2. Clear, maintainable code
3. Comprehensive testing
4. Thorough documentation

### Constraints

- Always verify file paths before operations
- Use parallel tool calls when operations are independent
- Prefer specialized tools over bash commands for file operations
- Use the Task tool for complex, multi-step operations

### Special Considerations

**Critical Constraints**:
- **NO PYTHON** - use Julia for ML/data, Rust for systems, ReScript for apps
- **RSR/CCCP Compliance Required** - follow Rhodium Standard Repository guidelines
- **Justfile PRIMARY** - never use Make or other build systems
- **Podman not Docker** - always use Podman for containers
- **Dual Licensing**: MIT + Palimpsest v0.6

**Development Priority Order**:
1. Neural/ML integration with Julia
2. UI implementation with ReScript + Deno
3. Additional test coverage
4. Performance optimization

---

**Last Updated**: 2026-01-10
**Maintained By**: ECHIDNA Project Team
