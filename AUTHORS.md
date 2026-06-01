<!--
SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
SPDX-License-Identifier: MPL-2.0
SPDX-FileCopyrightText: 2024-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->

# Authors and Contributors

This file lists the authors and contributors to the ECHIDNA project.
The authoritative running list lives in the git history — `git shortlog
-sne` will produce a deduplicated, frequency-sorted view at any commit.

## Maintainers

| Name | Role | Contact |
|---|---|---|
| Jonathan D.A. Jewell | Lead Maintainer | [@hyperpolymath](https://github.com/hyperpolymath), `j.d.a.jewell@open.ac.uk` |

See [`MAINTAINERS.adoc`](MAINTAINERS.adoc) for the maintainer
responsibility model and the path to becoming a maintainer.

## Contributors

Code, documentation, infrastructure, review, issue triage. The
deduplicated running list is in the git history:

```bash
git shortlog -sne
```

We recognise all forms of contribution including but not limited to:

- Code contributions
- Documentation improvements
- Bug reports and testing
- Feature suggestions
- Community support
- Translations
- Design and artwork
- Infrastructure and tooling

## Special Thanks

- **The theorem-proving community** — for the foundations and the
  ongoing maintenance of the backends ECHIDNA integrates with
  (Coq/Rocq, Lean, Agda, Isabelle, Idris2, F*, HOL Light, Mizar,
  PVS, ACL2, HOL4, Z3, CVC5, Vampire, E Prover, and the long tail
  in [`docs/PROVER_COUNT.md`](docs/PROVER_COUNT.md)).
- **The Rhodium Standard Repository (RSR/CCCP)** — for the
  compliance template that this repo extends; see
  [`RSR_COMPLIANCE.adoc`](RSR_COMPLIANCE.adoc).

## How to be added

If you've contributed to ECHIDNA and would like to be acknowledged
beyond the git history, open an issue or PR on
[GitHub](https://github.com/hyperpolymath/echidna/issues) with the
attribution you would like.

## License of contributions

Source files are licensed per the SPDX header at the top of each
file; the project root [`LICENSE`](LICENSE) and the per-tree
[`.reuse/dep5`](.reuse/dep5) catalogue together describe the
authoritative position. By contributing you agree to license your
contribution under the licence noted on the file you touch (or the
project default for new files).

The documentation surface is intentionally `MPL-2.0` — see
[`feedback_echidna_license_docs_mpl_intentional`](https://github.com/hyperpolymath/echidna/issues?q=license)
for the deliberation.

## Contact

- **GitHub Issues**: <https://github.com/hyperpolymath/echidna/issues>
- **Security**: see [`SECURITY.md`](SECURITY.md) — use GitHub
  Security Advisories for vulnerabilities, not public issues.

---

*This file is intentionally count-free and date-free in prose. The
git history is the running timeline; the canonical attribution
surface is `git shortlog -sne`.*
