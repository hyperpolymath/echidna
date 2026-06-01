<!--
SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
SPDX-License-Identifier: MPL-2.0
SPDX-FileCopyrightText: 2024-2025 ECHIDNA Project Contributors
-->

# Security Policy

## Supported Versions

ECHIDNA is in active development. The current major version (`2.x`)
on `main` receives security updates; pre-`1.0` lineages are not
supported. The on-disk version lives in
[`Cargo.toml`](Cargo.toml) and [`CHANGELOG.md`](CHANGELOG.md); this
file deliberately does not pin a version number to avoid drift.

| Lineage | Supported          |
| ------- | ------------------ |
| 2.x (`main`) | :white_check_mark: |
| 1.x          | :white_check_mark: (security only) |
| < 1.0        | :x: |

## Security Principles

ECHIDNA follows these security principles:

1. **Defense in Depth**: Multiple layers of security controls
2. **Least Privilege**: Minimal necessary permissions
3. **Secure by Default**: Safe default configurations
4. **Fail Securely**: Graceful degradation on errors
5. **Complete Mediation**: All access requests are checked
6. **Transparency**: Open communication about security issues

## Reporting a Vulnerability

We take the security of ECHIDNA seriously. If you believe you have found a security vulnerability, please report it to us as described below.

### Where to Report

**DO NOT** report security vulnerabilities through public GitHub
issues, GitLab issues, the issue tracker, or any other public
channel.

Preferred route — **GitHub Security Advisories** (private, encrypted,
auditable):

* https://github.com/hyperpolymath/echidna/security/advisories/new

Email fallback (use only if GitHub is unavailable to you):

* j.d.a.jewell@open.ac.uk (maintainer; PGP key
  `4A03639C1EB1F86C7F0C97A91835A14A2867091E` published on
  https://keys.openpgp.org)

### What to Include

Please include the following information in your report:

- Type of vulnerability (e.g., buffer overflow, SQL injection, XSS, etc.)
- Full paths of source file(s) related to the vulnerability
- Location of the affected source code (tag/branch/commit or direct URL)
- Any special configuration required to reproduce the issue
- Step-by-step instructions to reproduce the issue
- Proof-of-concept or exploit code (if possible)
- Impact of the issue, including how an attacker might exploit it

### Response Timeline

- **Initial Response**: Within 48 hours of report
- **Status Update**: Within 7 days with initial assessment
- **Patch Development**: Timeline provided based on severity
- **Public Disclosure**: Coordinated with reporter after patch release

### Security Disclosure Process

1. **Report Received**: Security team acknowledges receipt
2. **Assessment**: Team assesses severity and impact
3. **Development**: Patch is developed and tested
4. **Notification**: Security advisory prepared
5. **Release**: Patch released with advisory
6. **Recognition**: Reporter credited (if desired)

## Security Best Practices

### For Users

1. **Keep Updated**: Always use the latest stable version
2. **Verify Downloads**: Check signatures and checksums
3. **Review Configs**: Audit security-related configurations
4. **Monitor Logs**: Watch for suspicious activity
5. **Report Issues**: Report any security concerns promptly

### For Contributors

1. **Input Validation**: Always validate and sanitize inputs
2. **Output Encoding**: Properly encode outputs to prevent injection
3. **Authentication**: Use strong authentication mechanisms
4. **Authorization**: Implement proper access controls
5. **Cryptography**: Use well-tested cryptographic libraries
6. **Dependencies**: Keep dependencies updated and audited
7. **Secrets**: Never commit secrets or credentials
8. **Code Review**: All code must be reviewed before merging

## Security Features

### Current Security Measures

- **REUSE Compliance**: All code properly licensed and attributed
- **Trivy Scanning**: Automated vulnerability scanning via CI/CD
- **Aqua.jl**: Julia dependency security analysis
- **Cargo Audit**: Rust dependency vulnerability checking
- **Podman**: Container isolation with rootless mode support
- **SPDX Headers**: Clear license and copyright information

### Planned Security Enhancements

- **Code Signing**: Digital signatures for releases
- **SBOM Generation**: Software Bill of Materials for dependencies
- **Fuzzing**: Automated fuzz testing for parsers
- **SAST/DAST**: Static and dynamic security analysis
- **Dependency Pinning**: Locked dependency versions
- **Security Hardening**: Container and binary hardening

## Vulnerability Severity

We use the CVSS (Common Vulnerability Scoring System) v3.1 to assess severity:

| Score | Severity | Response Time |
|-------|----------|---------------|
| 9.0-10.0 | Critical | 24 hours |
| 7.0-8.9  | High     | 7 days   |
| 4.0-6.9  | Medium   | 30 days  |
| 0.1-3.9  | Low      | 90 days  |

## Security Updates

Security updates are released as:

- **Critical**: Immediate patch release
- **High**: Next patch release (within 7 days)
- **Medium**: Next minor release (within 30 days)
- **Low**: Next major/minor release (within 90 days)

## Security Advisories

Security advisories are published at:

- **GitHub Security Advisories**:
  https://github.com/hyperpolymath/echidna/security/advisories
- **GitHub Releases** (security patches are tagged accordingly):
  https://github.com/hyperpolymath/echidna/releases
- **GitHub Releases atom feed**:
  <https://github.com/hyperpolymath/echidna/releases.atom>

## Scope

### In Scope

The following are in scope for security reports:

- **Core libraries**: Rust core, Julia ML layer, Idris2 ABI,
  Zig FFI bridge, AffineScript / ReScript UI components
- **Prover backends**: every `ProverKind` variant wired through the
  dispatch pipeline — Tier-1 core through Tier-3 niche. The live
  membership list is `ProverKind::all()` in
  `src/rust/provers/mod.rs`; the human-readable mirror is
  [`docs/PROVER_COUNT.md`](docs/PROVER_COUNT.md).
- **Trust-hardening pipeline**: solver integrity, certificate
  checking, axiom tracking, sandboxing, mutation testing, Pareto
  ranking, Bayesian confidence — wired in
  `src/rust/dispatch.rs`.
- **Build system**: Justfile, CI/CD workflows under
  `.github/workflows/`
- **Containers**: `Containerfile`, `.containerization/Containerfile.wave3`,
  Podman configurations
- **Dependencies**: third-party libraries and tools

### Out of Scope

The following are typically not accepted:

- Denial of Service (DoS) without proven impact
- Social engineering attacks
- Issues in third-party dependencies (report to upstream)
- Theoretical vulnerabilities without PoC
- Issues requiring physical access
- Issues in unsupported versions

## Threat Model

### Assets

- **Source Code**: Intellectual property and implementation
- **User Data**: Proof scripts and theorem libraries
- **Credentials**: API keys and authentication tokens
- **Build Artifacts**: Compiled binaries and containers

### Threats

- **Code Injection**: Malicious code execution via prover input
- **Data Exfiltration**: Unauthorized access to user proofs
- **Supply Chain**: Compromised dependencies
- **Container Escape**: Breaking out of Podman containers
- **Denial of Service**: Resource exhaustion attacks

### Mitigations

- Input validation and sanitization
- Principle of least privilege
- Dependency security scanning
- Container security hardening
- Rate limiting and resource quotas

## Security Tooling

### Required Tools

- **Trivy**: Container and filesystem vulnerability scanning
- **cargo-audit**: Rust dependency auditing
- **Aqua.jl**: Julia package security analysis
- **REUSE**: License compliance verification

### Recommended Tools

- **cargo-clippy**: Rust linter with security checks
- **JET.jl**: Julia static analysis
- **Semgrep**: Pattern-based security scanning
- **Bandit**: Security linting (if Python used - should not be!)

## Contact

For security-related questions or concerns:

- **GitHub Security Advisories**:
  https://github.com/hyperpolymath/echidna/security/advisories/new
- **Email**: j.d.a.jewell@open.ac.uk (maintainer)
- **PGP key**: `4A03639C1EB1F86C7F0C97A91835A14A2867091E`
  — fetch via `gpg --recv-keys 4A03639C1EB1F86C7F0C97A91835A14A2867091E`
  or from <https://keys.openpgp.org/search?q=j.d.a.jewell@open.ac.uk>
- **GitHub**: [@hyperpolymath](https://github.com/hyperpolymath)

## Acknowledgments

We thank the following researchers and security professionals for responsibly disclosing vulnerabilities:

- *No vulnerabilities reported yet*

---

**Document lineage**: revisions tracked via `git log SECURITY.md`;
versioned alongside the project (see [`CHANGELOG.md`](CHANGELOG.md)).
This file is intentionally count-free and version-free in prose to
avoid R5b drift against [`Cargo.toml`](Cargo.toml).
