# Security Policy

We take security seriously. We appreciate your efforts to responsibly disclose vulnerabilities and will make every effort to acknowledge your contributions.

## Table of Contents

- [Reporting a Vulnerability](#reporting-a-vulnerability)
- [What to Include](#what-to-include)
- [Response Timeline](#response-timeline)
- [Disclosure Policy](#disclosure-policy)
- [Scope](#scope)
- [Safe Harbour](#safe-harbour)
- [Recognition](#recognition)
- [Security Updates](#security-updates)
- [Security Best Practices](#security-best-practices)

---

## Reporting a Vulnerability

### Preferred Method: GitHub Security Advisories

The preferred method for reporting security vulnerabilities is through GitHub's Security Advisory feature:

1. Navigate to [Report a Vulnerability](https://github.com/hyperpolymath/template-repo/security/advisories/new)
2. Click **"Report a vulnerability"**
3. Complete the form with as much detail as possible
4. Submit — we'll receive a private notification

This method ensures:

- End-to-end encryption of your report
- Private discussion space for collaboration
- Coordinated disclosure tooling
- Automatic credit when the advisory is published

### Alternative: GitHub Issues (Non-Sensitive)

For non-sensitive security concerns that don't require confidential disclosure, you may open a regular GitHub issue with the `security` label.

> **⚠️ Important:** Do not report security vulnerabilities through public GitHub issues, pull requests, discussions, or social media.

---

## What to Include

A good vulnerability report helps us understand and reproduce the issue quickly.

### Required Information

- **Description**: Clear explanation of the vulnerability
- **Impact**: What an attacker could achieve (confidentiality, integrity, availability)
- **Affected versions**: Which versions/commits are affected
- **Reproduction steps**: Detailed steps to reproduce the issue

### Helpful Additional Information

- **Proof of concept**: Code, scripts, or screenshots demonstrating the vulnerability
- **Attack scenario**: Realistic attack scenario showing exploitability
- **CVSS score**: Your assessment of severity (use [CVSS 3.1 Calculator](https://www.first.org/cvss/calculator/3.1))
- **CWE ID**: Common Weakness Enumeration identifier if known
- **Suggested fix**: If you have ideas for remediation
- **References**: Links to related vulnerabilities, research, or advisories

### Example Report Structure

```markdown
## Summary
[One-sentence description of the vulnerability]

## Vulnerability Type
[e.g., SQL Injection, XSS, SSRF, Path Traversal, etc.]

## Affected Component
[File path, function name, API endpoint, etc.]

## Affected Versions
[Version range or specific commits]

## Severity Assessment
- CVSS 3.1 Score: [X.X]
- CVSS Vector: [CVSS:3.1/AV:X/AC:X/PR:X/UI:X/S:X/C:X/I:X/A:X]

## Description
[Detailed technical description]

## Steps to Reproduce
1. [First step]
2. [Second step]
3. [...]

## Proof of Concept
[Code, curl commands, screenshots, etc.]

## Impact
[What can an attacker achieve?]

## Suggested Remediation
[Optional: your ideas for fixing]

## References
[Links to related issues, CVEs, research]
```

---

## Response Timeline

We commit to the following response times:

| Stage | Timeframe | Description |
|-------|-----------|-------------|
| **Initial Response** | 48 hours | We acknowledge receipt and confirm we're investigating |
| **Triage** | 7 days | We assess severity, confirm the vulnerability, and estimate timeline |
| **Status Update** | Every 7 days | Regular updates on remediation progress |
| **Resolution** | 90 days | Target for fix development and release (complex issues may take longer) |
| **Disclosure** | 90 days | Public disclosure after fix is available (coordinated with you) |

> **Note:** These are targets, not guarantees. Complex vulnerabilities may require more time. We'll communicate openly about any delays.

---

## Disclosure Policy

We follow **coordinated disclosure** (also known as responsible disclosure):

1. **You report** the vulnerability privately
2. **We acknowledge** and begin investigation
3. **We develop** a fix and prepare a release
4. **We coordinate** disclosure timing with you
5. **We publish** security advisory and fix simultaneously
6. **You may publish** your research after disclosure

### Our Commitments

- We will not take legal action against researchers who follow this policy
- We will work with you to understand and resolve the issue
- We will credit you in the security advisory (unless you prefer anonymity)
- We will notify you before public disclosure
- We will publish advisories with sufficient detail for users to assess risk

### Your Commitments

- Report vulnerabilities promptly after discovery
- Give us reasonable time to address the issue before disclosure
- Do not access, modify, or delete data beyond what's necessary to demonstrate the vulnerability
- Do not degrade service availability (no DoS testing on production)
- Do not share vulnerability details with others until coordinated disclosure

### Disclosure Timeline

```
Day 0          You report vulnerability
Day 1-2        We acknowledge receipt
Day 7          We confirm vulnerability and share initial assessment
Day 7-90       We develop and test fix
Day 90         Coordinated public disclosure
               (earlier if fix is ready; later by mutual agreement)
```

If we cannot reach agreement on disclosure timing, we default to 90 days from your initial report.

---

## Scope

### In Scope ✅

The following are within scope for security research:

- This repository (`hyperpolymath/template-repo`) and all its code
- Official releases and packages published from this repository
- Documentation that could lead to security issues
- Build and deployment configurations in this repository
- Dependencies (report here, we'll coordinate with upstream)

### Out of Scope ❌

The following are **not** in scope:

- Third-party services we integrate with (report directly to them)
- Social engineering attacks against maintainers
- Physical security
- Denial of service attacks against production infrastructure
- Spam, phishing, or other non-technical attacks
- Issues already reported or publicly known
- Theoretical vulnerabilities without proof of concept

### Qualifying Vulnerabilities

We're particularly interested in:

- Remote code execution
- SQL injection, command injection, code injection
- Authentication/authorisation bypass
- Cross-site scripting (XSS) and cross-site request forgery (CSRF)
- Server-side request forgery (SSRF)
- Path traversal / local file inclusion
- Information disclosure (credentials, PII, secrets)
- Cryptographic weaknesses
- Deserialisation vulnerabilities
- Memory safety issues (buffer overflows, use-after-free, etc.)
- Supply chain vulnerabilities (dependency confusion, etc.)
- Significant logic flaws

### Non-Qualifying Issues

The following generally do not qualify as security vulnerabilities:

- Missing security headers on non-sensitive pages
- Clickjacking on pages without sensitive actions
- Self-XSS (requires victim to paste code)
- Missing rate limiting (unless it enables a specific attack)
- Username/email enumeration (unless high-risk context)
- Missing cookie flags on non-sensitive cookies
- Software version disclosure
- Verbose error messages (unless exposing secrets)
- Best practice deviations without demonstrable impact

---

## Safe Harbour

We support security research conducted in good faith.

### Our Promise

If you conduct security research in accordance with this policy:

- ✅ We will not initiate legal action against you
- ✅ We will not report your activity to law enforcement
- ✅ We will work with you in good faith to resolve issues
- ✅ We consider your research authorised under the Computer Fraud and Abuse Act (CFAA), UK Computer Misuse Act, and similar laws
- ✅ We waive any potential claim against you for circumvention of security controls

### Good Faith Requirements

To qualify for safe harbour, you must:

- Comply with this security policy
- Report vulnerabilities promptly
- Avoid privacy violations (do not access others' data)
- Avoid service degradation (no destructive testing)
- Not exploit vulnerabilities beyond proof-of-concept
- Not use vulnerabilities for profit (beyond bug bounties where offered)

> **⚠️ Important:** This safe harbour does not extend to third-party systems. Always check their policies before testing.

---

## Recognition

We believe in recognising security researchers who help us improve.

### Hall of Fame

Researchers who report valid vulnerabilities will be acknowledged in our [Security Acknowledgments](SECURITY-ACKNOWLEDGMENTS.md) (unless they prefer anonymity).

Recognition includes:

- Your name (or chosen alias)
- Link to your website/profile (optional)
- Brief description of the vulnerability class
- Date of report

### What We Offer

- ✅ Public credit in security advisories
- ✅ Acknowledgment in release notes
- ✅ Entry in our Hall of Fame
- ✅ Reference/recommendation letter upon request (for significant findings)

### What We Don't Currently Offer

- ❌ Monetary bug bounties
- ❌ Hardware or swag
- ❌ Paid security research contracts

> **Note:** We're a community project with limited resources. Your contributions help everyone who uses this software.

---

## Security Updates

### Receiving Updates

To stay informed about security updates:

- **Watch this repository**: Click "Watch" → "Custom" → Select "Security alerts"
- **GitHub Security Advisories**: Published at [Security Advisories](https://github.com/hyperpolymath/template-repo/security/advisories)
- **Release notes**: Security fixes noted in [CHANGELOG](CHANGELOG.md)

### Update Policy

| Severity | Response |
|----------|----------|
| **Critical/High** | Patch release as soon as fix is ready |
| **Medium** | Included in next scheduled release (or earlier) |
| **Low** | Included in next scheduled release |

### Supported Versions

<!-- Adjust this table to match your actual version support policy -->

| Version | Supported | Notes |
|---------|-----------|-------|
| `main` branch | ✅ Yes | Latest development |
| Latest release | ✅ Yes | Current stable |
| Previous minor release | ✅ Yes | Security fixes backported |
| Older versions | ❌ No | Please upgrade |

---

## Security Best Practices

When using template-repo, we recommend:

### General

- Keep dependencies up to date
- Use the latest stable release
- Subscribe to security notifications
- Review configuration against security documentation
- Follow principle of least privilege

### For Contributors

- Never commit secrets, credentials, or API keys
- Use signed commits (`git config commit.gpgsign true`)
- Review dependencies before adding them
- Run security linters locally before pushing
- Report any concerns about existing code

---

## Additional Resources

- [Security Advisories](https://github.com/hyperpolymath/template-repo/security/advisories)
- [Changelog](CHANGELOG.md)
- [Contributing Guidelines](CONTRIBUTING.md)
- [CVE Database](https://cve.mitre.org/)
- [CVSS Calculator](https://www.first.org/cvss/calculator/3.1)

---

## Contact

| Purpose | Contact |
|---------|---------|
| **Security issues** | [Report via GitHub](https://github.com/hyperpolymath/template-repo/security/advisories/new) |
| **General questions** | [GitHub Discussions](https://github.com/hyperpolymath/template-repo/discussions) |
| **Other enquiries** | See [README](README.md) for contact information |

---

## Policy Changes

This security policy may be updated from time to time. Significant changes will be:

- Committed to this repository with a clear commit message
- Noted in the changelog
- Announced via GitHub Discussions (for major changes)

---

*Thank you for helping keep template-repo and its users safe.* 🛡️

---

<sub>Last updated: 2025 · Policy version: 1.0.0</sub>
