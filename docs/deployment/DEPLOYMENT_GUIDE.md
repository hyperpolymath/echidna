<!--
SPDX-License-Identifier: CC-BY-SA-4.0
SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->

# ECHIDNA Deployment Guide — superseded

**Status: superseded 2026-07-29. Do not follow this document.**

The previous contents described a v0.1.0 deployment dated 2025-11-22 whose
next step was "deploy to GitLab", alongside a `zotero-voyant-export` migration
unrelated to how ECHIDNA is deployed. It also quoted a fixed prover count,
which the repository's canonical-reference policy forbids in prose. Following
it would send an operator somewhere the project no longer goes.

Current documentation:

| You want to | Read |
|---|---|
| Understand where everything runs | [`docs/HOSTING.md`](../HOSTING.md) |
| Deploy the API to a server | [`deploy/hetzner/README.adoc`](../../deploy/hetzner/README.adoc) |
| Call the deployed API | [`site/docs/api/core.md`](../../site/docs/api/core.md) |
| Machine-readable topology | [`.machine_readable/deployment.a2ml`](../../.machine_readable/deployment.a2ml) |
| Canonical prover counts | [`docs/PROVER_COUNT.md`](../PROVER_COUNT.md) |

This stub is kept rather than deleted so existing links do not dead-end.
