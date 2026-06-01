<!--
  SPDX-License-Identifier: MPL-2.0
  SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

  CONTRIBUTING.adoc is canonical (RSR convention). This Markdown file
  is a thin pointer for renderers and tools that prefer .md.
-->

# Contributing

Please read [`CONTRIBUTING.adoc`](CONTRIBUTING.adoc) for the full
contribution guidelines — what is accepted, what is not, the commit
and PR conventions, the test layout, the documentation surface map,
and the licence / SPDX policy. GitHub renders AsciiDoc directly.

If a quick orientation is enough:

- **Before you start**: read [`README.adoc`](README.adoc),
  [`RSR_COMPLIANCE.adoc`](RSR_COMPLIANCE.adoc), and
  [`CLAUDE.md`](CLAUDE.md) (if you are using an AI agent).
- **Local setup**: see [`QUICKSTART-DEV.adoc`](QUICKSTART-DEV.adoc).
- **Tests**: `cargo test --lib`, `cargo test --tests`, and
  `idris2 --build src/abi/echidnaabi.ipkg` for the ABI surface.
- **Commits**: Conventional Commits, GPG-signed, atomic.
- **PRs**: branch off `main`, rebase don't merge, fill the
  template, auto-merge once green.
- **Banned**: Python outside `salt/`, Dockerfiles (use Podman +
  `Containerfile`), Make (use Justfile), `believe_me` /
  `assert_total` / `unsafePerformIO` / `prim__crash` in `src/abi/`,
  bare `unsafe {}` without `// SAFETY:` in Rust.
