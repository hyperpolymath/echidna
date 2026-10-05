<!--
SPDX-License-Identifier: CC-BY-SA-4.0
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->
## Summary

<!-- Briefly describe what this PR does and why. Link to related issues with "Closes #N". -->

## Changes

<!-- List the key changes introduced by this PR. -->

-

## RSR Quality Checklist

<!-- Check all that apply. PRs that fail required checks will not be merged. -->

### Required

- [ ] Tests pass (`just test` or equivalent)
- [ ] Code is formatted (`just fmt` or equivalent)
- [ ] Linter is clean (no new warnings or errors)
- [ ] No banned language patterns (no , no npm/bun, no Go/Python)
- [ ] No `unsafe` blocks without `// SAFETY:` comments
- [ ] No banned functions (`believe_me`, `unsafeCoerce`, `Obj.magic`, `Admitted`, `sorry`)
- [ ] SPDX license headers present on all new/modified source files
- [ ] No secrets, credentials, or `.env` files included

### As Applicable

- [ ] Repo deed (`*_chora.deed`) `(status)` / `(maturity)` updated (if project state changed)
- [ ] Repo deed `(ecosystem)` updated (if integrations changed)
- [ ] Repo deed `(meta)` and/or `docs/decisions/` updated (if architectural decisions changed)
- [ ] `docs/status/ROADMAP.adoc` updated (if milestones or next actions changed)
- [ ] Documentation updated for user-facing changes
- [ ] `TOPOLOGY.md` updated (if architecture changed)
- [ ] `CHANGELOG` or release notes updated
- [ ] New dependencies reviewed for license compatibility (MPL-2.0 / MPL-2.0)
- [ ] ABI/FFI changes validated (`src/interface/abi/` and `src/interface/ffi/` consistent)

## Testing

<!-- Describe how you tested these changes. -->

## Screenshots

<!-- If applicable, add screenshots or terminal output demonstrating the change. -->
