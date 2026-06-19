<!-- SPDX-License-Identifier: MPL-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
# Git hooks

Governance hooks for ECHIDNA — the RSR `hooks/` requirement (pre-commit
enforcement). Each wraps the same `just` gate CI runs, so commits and pushes
fail fast on the same checks.

| Hook | Runs | Covers |
|------|------|--------|
| `pre-commit` | `just pre-commit` | fmt-check + lint (REUSE/SPDX + rustfmt + clippy) + test |
| `pre-push`   | `just validate-rsr` | RSR compliance gate (RSR-H12) |

## Enable

Hooks are opt-in. Point git at this directory once per clone:

```bash
git config core.hooksPath hooks
```

Disable with `git config --unset core.hooksPath`. Each hook no-ops with a
warning if `just` is not on PATH, so a missing toolchain never hard-blocks a
commit.
