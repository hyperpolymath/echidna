<!-- SPDX-License-Identifier: MPL-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
<!-- Deposited report: Hypatia alert classification for echidna, 2026-06-06 -->

# Hypatia Alert Classification Report

Repository: `hyperpolymath/echidna`

Date: 2026-06-06

This deposited report classifies the non-Dependabot code-scanning state seen in
`echidna`. It separates scanner/reporting debris from real repository work, and
it records which work should be handled by existing systems, extended systems,
or human/specialist review.

## Open Alert Count

GitHub code scanning showed 249 open alerts.

| Bucket | Count | Classification | Route |
| --- | ---: | --- | --- |
| Hypatia `code_scanning_alerts/CSA001` self-echo | 27 | Reporting debris | Standards/Hypatia SARIF fix, then clear stale alerts |
| Structural stale refs: `SD022`, `SD007` | 28 | Lifecycle hygiene | PR-only documentation/state cleanup |
| Workflow and Scorecard control-plane hygiene | 51 | CI/security control | Existing PR machinery, conservative batching |
| ReScript migration findings | 73 | Language migration | Batch by subsystem, PR-only |
| Runtime crash/availability code safety | 45 | Source risk | Context-aware PRs, no blind rewrites |
| FFI/proof/memory-safety findings | 22 | High-risk source/proof boundary | Specialist review, proof route, report-only by default |
| Environment/report-only findings | 3 | Control-plane topology | Observe, model, and route manually |

## Findings Expected To Dissolve

The 27 `code_scanning_alerts/CSA001` alerts are not source work in `echidna`.
They should dissolve after:

1. the standards reusable SARIF converter stops uploading `code_scanning_alerts`
   meta-findings;
2. the next authoritative Hypatia run uploads an empty or reduced Hypatia SARIF
   result set for that rule family;
3. stale GitHub code-scanning alerts clear or are dismissed with rationale.

Related issue: <https://github.com/hyperpolymath/standards/issues/378>

## Real Work Buckets

### Workflow and Scorecard Hygiene

These are mostly easy or existing-system work. They include missing
`timeout-minutes`, Scorecard token-permission issues, and specific workflow
audit findings such as CodeQL language coverage and secret-action gates.

Recommended handling:

- set proportional timeouts, not a universal 10-minute value;
- let Scorecard/CodeQL work already in flight finish before duplicating work;
- use PR-only mode;
- verify workflows with focused CI.

Related issue: <https://github.com/hyperpolymath/echidna/issues/241>

### ReScript Migration

The 73 migration findings should be treated as one language-migration campaign,
not 73 isolated defects.

Recommended handling:

- group by API and subtree;
- preserve deliberate externals and FFI bindings with local rationale;
- batch migration work by subsystem;
- avoid whole-tree automatic rewrites without build verification.

Related issue: <https://github.com/hyperpolymath/echidna/issues/240>

### Structural Drift

The 28 structural findings are stale references in docs and machine-readable
state. They are low-risk when the canonical replacement path is known.

Recommended handling:

- map each old path to a current path or tombstone;
- keep machine-readable state parseable;
- update references in PR-only mode.

Related issue: <https://github.com/hyperpolymath/echidna/issues/242>

### Runtime Code Safety

The unwrap, expect, panic, and lock-unwrap findings are plausible source-risk
signals. Some may be test-only or invariant-protected; others need proper error
propagation.

Recommended handling:

- separate tests and fixtures from production paths;
- replace production panics with typed errors only where behavior is preserved;
- avoid replacing `unwrap()` with default values that could corrupt prover
  state.

Related issue: <https://github.com/hyperpolymath/echidna/issues/239>

### FFI, Memory, And Proof Boundary

The unsafe block, raw pointer, `mem_forget`, Zig pointer cast, and Agda
postulate findings are high-risk. They should not be auto-fixed from pattern
matching alone.

Recommended handling:

- route to echidnabot or proof review;
- require focused tests or proof obligations;
- use report-only unless a proven recipe exists.

Related issue: <https://github.com/hyperpolymath/echidna/issues/239>

## Summary By Action Class

| Action class | Count | Notes |
| --- | ---: | --- |
| Dissolve as stale/reporting debris | 27 | Self-echo SARIF artifacts |
| Trivial/easy existing-system PR work | 79 | Workflow/Scorecard plus structural docs/state |
| Readily accommodated by extended system | 118 | ReScript migration plus runtime code-safety with context |
| High risk, specialist review only | 22 | FFI/proof/memory boundary |
| Report-only environment topology | 3 | Needs environment self-modeling |

## Ordering

The safe order is:

1. Fix the self-echo reporting path and clear stale alert debris.
2. Let relevant in-flight GitHub Actions, CodeQL, Scorecard, and Dependabot
   work finish when it covers the same class.
3. Apply workflow and structural hygiene PRs.
4. Run the ReScript migration campaign by subsystem.
5. Triage runtime code-safety paths.
6. Hold FFI/proof/memory-safety items for specialist review.

Doing this out of order can create more work than it removes. For example,
rewriting source before clearing stale SARIF debris makes alert counts look
worse, and blind workflow timeout edits can break formal or live-prover jobs.

## Portfolio Note

For `Git in the Time of NeSy Agency`, this report is an example of repository
portfolio triage: the useful unit is not a raw alert, but a classified work
order with route, cost, risk, and expected class-collapse.
