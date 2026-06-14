# SPDX-License-Identifier: MPL-2.0
# Intend — north-star runner (verb is `intend`, file is `Intentfile.a2ml`)
#
# Pairs with: Intentfile.a2ml (same directory)
# Verb:       intend
# Semantics:  Declares BOTH concrete committed next-actions ([[intents]]) and
#             horizon aspirations ([[wishes]]) for ECHIDNA — the trust-hardened
#             neurosymbolic theorem-proving platform. Not a gate — reports
#             progress toward declared intents and lists wishes by horizon.
#             Status progressions:
#               intents: 'declared → 'in_progress → 'done | 'deferred | 'retired
#               wishes:  'declared → 'in_progress → 'achieved | 'abandoned
# CLI:        `contractile intend run`       → print status table (both sections)
#             `contractile intend progress`  → diff declared-vs-observed (intents)
#             `contractile intend horizon`   → group wishes by near/mid/far
#
# History:    Absorbed the deprecated `lust` contractile's [[wishes]] schema
#             2026-04-18. `lust/` dir removed estate-wide. intend was the FIRST
#             trident instance in the estate.
#
# Anything else in this directory is human-only notes/archive; machines ignore.
#
# Base: ../_base.ncl provides pedigree_schema, run_defaults, probe_schema.
# See: docs/CONTRACTILE-SPEC.adoc

let base = import "../_base.ncl" in

{
  pedigree = base.pedigree_schema & {
    contractile_verb = "intend",
    semantics = "north-star (commitments + aspirations)",
    security = {
      leash = 'Kennel,
      trust_level = "read-only reporting",
      allow_network = false,
      allow_filesystem_write = false,
      allow_subprocess = true,      # probe commands may shell out (intents only; wishes never probe)
    },
    metadata = {
      name = "intend-runner",
      version = "2.0.0",
      description = "Reports progress toward ECHIDNA's committed next-actions and lists horizon aspirations (trust-hardened neurosymbolic proving, prover backends, VeriSimDB recording, Hypatia learning loop). Non-gating. Absorbed `lust` semantics 2026-04-18.",
      paired_xfile = "Intentfile.a2ml",
      author = "Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>",
    },
  },

  schema = {
    intents
      | Array {
          id | String,
          description | String,
          # TODO: migrate to base.probe_schema (structured probe) when CLI supports it
          probe | String | optional,     # shell command that indicates done-ness
          status | [| 'declared, 'in_progress, 'done, 'deferred, 'retired |] | default = 'declared,
          notes | String | optional,
          target_date | String | optional,
        },
    wishes
      | Array {
          id | String,
          description | String,
          horizon | [| 'near, 'mid, 'far |] | default = 'mid,
          why | String | optional,
          status | [| 'declared, 'in_progress, 'achieved, 'abandoned |] | default = 'declared,
          notes | String | optional,
        }
      | optional,
  },

  # Runner behaviour — inherits from base.run_defaults.
  # intend never blocks; it is a report only.
  # emit_diff is intent-specific (declared vs observed probes).
  # emit_grouped_by_horizon renders wishes grouped by near/mid/far.
  run = base.run_defaults & {
    on_pass = "continue",
    on_any_fail = "continue",         # never blocks; it's a report
    report_format = "a2ml",
    emit_summary = true,
    emit_diff = true,                 # declared vs observed (intents)
    emit_grouped_by_horizon = true,   # wishes grouped by horizon (absorbed from lust)
  },
}
