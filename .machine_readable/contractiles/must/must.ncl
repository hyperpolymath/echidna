# SPDX-License-Identifier: MPL-2.0
# Must — invariants runner
#
# Pairs with: Mustfile.a2ml (same directory)
# Verb:       must (invariant assertion — release-blocking)
# Semantics:  every check is a hard gate. A single failure blocks merge.
#             Echidna's Physical-State invariants: LICENSE/README presence,
#             no banned hardcoded developer paths in source, no Dockerfile
#             (Containerfile only — RSR-H15), no Makefile (Justfile only —
#             RSR-H14).
# CLI:        `contractile must run` → reads Mustfile.a2ml, evaluates each check,
#             emits pass/fail verdict per item, exits non-zero if any failed.
#
# This file is the *schema + runner* that the `contractile` CLI loads alongside
# Mustfile.a2ml. Anything else in this directory is human-only notes/archive
# and MUST be ignored by machines.
#
# Base: ../_base.ncl provides pedigree_schema, run_defaults, probe_schema.
# See: docs/CONTRACTILE-SPEC.adoc

let base = import "../_base.ncl" in

{
  pedigree = base.pedigree_schema & {
    contractile_verb = "must",
    semantics = "invariant",
    security = {
      leash = 'Kennel,
      trust_level = "read-only verification",
      allow_network = false,
      allow_filesystem_write = false,
      allow_subprocess = true,    # verification probes may shell out (e.g. grep, test -f)
    },
    metadata = {
      name = "must-runner",
      version = "1.0.0",
      description = "Evaluates every Physical-State invariant in the adjacent Mustfile.a2ml as a hard gate for the Echidna neurosymbolic theorem-proving platform.",
      paired_xfile = "Mustfile.a2ml",
      author = "Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>",
    },
  },

  # Contract schema — the shape every Mustfile.a2ml must satisfy.
  # Used by `contractile must typecheck Mustfile.a2ml`.
  schema = {
    invariants
      | Array {
          id | String,
          description | String,
          # TODO: migrate to base.probe_schema (structured probe) when CLI supports it
          probe | String,                          # shell command; exit 0 = pass
          # status_core values: 'declared, 'verified, 'failing — must does NOT extend the core trio
          status | [| 'declared, 'verified, 'failing |] | default = 'declared,
          severity | [| 'critical, 'high, 'medium |] | default = 'critical,
          notes | String | optional,
          fix | String | optional,
        },
  },

  # Runner behaviour — consumed by the contractile CLI dispatcher.
  # Inherits from base.run_defaults; on_any_fail is the hard-gate default.
  run = base.run_defaults & {
    on_any_fail = "exit-nonzero",     # hard gate — single failure blocks merge
    report_format = "a2ml",           # emit a2ml report, not json
    emit_summary = true,
  },
}
