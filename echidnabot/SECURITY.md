# Security Policy

## Supported Versions

The following versions of echidnabot are currently supported with security updates:

| Version | Supported          |
| ------- | ------------------ |
| 0.1.x   | :white_check_mark: |

## Reporting a Vulnerability

We take security seriously. If you discover a security vulnerability in echidnabot, please report it responsibly:

### How to Report

1. **Email**: Send details to security@hyperpolymath.org
2. **Encryption**: Use our GPG key at https://hyperpolymath.org/gpg/security.asc
3. **Do NOT** open a public GitHub issue for security vulnerabilities

### What to Include

- Description of the vulnerability
- Steps to reproduce
- Potential impact assessment
- Suggested fix (if any)

### Response Timeline

- **Initial acknowledgment**: Within 48 hours
- **Status update**: Within 7 days
- **Resolution target**: Within 30 days for critical issues

### What to Expect

- If the vulnerability is accepted, we will:
  - Work on a fix and coordinate disclosure timing with you
  - Credit you in the security advisory (unless you prefer anonymity)
  - Release a patched version as soon as practical

- If the vulnerability is declined, we will:
  - Provide a clear explanation of why
  - Suggest alternative resources if applicable

## Security Measures

echidnabot implements the following security measures:

- **Webhook Verification**: HMAC-SHA256 signature verification for all webhooks
- **Least-Privilege Access**: Read-only repository access for cloning, minimal write access for check runs
- **Sandboxed Execution**: echidnabot delegates proof verification to ECHIDNA Core; it never executes provers directly
- **Secrets Management**: Integration with Vault/SOPS for secure secret handling
- **No Weak Cryptography**: SHA-256+ only; no MD5 or SHA-1 for security purposes
- **TLS Everywhere**: All external communications use HTTPS/TLS

## Security Scanning

This project uses:
- CodeQL for static analysis
- TruffleHog for secret detection
- OpenSSF Scorecard for security metrics
- ClusterFuzzLite for fuzzing

## References

- [security.txt](/.well-known/security.txt)
- [ARCHITECTURE.adoc](docs/ARCHITECTURE.adoc) - Security considerations section
