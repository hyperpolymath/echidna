# SPDX-License-Identifier: PMPL-1.0-or-later
# Adjust — accessibility runner
#
# Pairs with: Adjustfile.a2ml (same directory)
# Verb:       adjust
# Semantics:  accessibility compliance (WCAG 2.1 AA baseline). Gating where
#             a deterministic fix exists; advisory where human review needed.
# CLI:        `contractile adjust check` → run all probes, list violations
#             `contractile adjust fix`   → apply deterministic fixes where defined
#
# Anything else in this directory is human-only notes/archive; machines ignore.
#
# Base: ../_base.ncl provides pedigree_schema, run_defaults, probe_schema.
# See: docs/CONTRACTILE-SPEC.adoc

let base = import "../_base.ncl" in

{
  pedigree = base.pedigree_schema & {
    contractile_verb = "adjust",
    semantics = "accessibility compliance",
    security = {
      leash = 'Kennel,
      trust_level = "fixes allowed where deterministic",
      allow_network = false,
      allow_filesystem_write = true,    # `adjust fix` may write (deterministic patches only)
      allow_subprocess = true,
    },
    metadata = {
      name = "adjust-runner",
      version = "1.0.0",
      description = "Evaluates accessibility requirements from Adjustfile.a2ml. Fixes deterministic items; flags the rest for human review.",
      paired_xfile = "Adjustfile.a2ml",
      author = "Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>",
    },
  },

  schema = {
    requirements
      | Array {
          id | String,
          description | String,
          # TODO: migrate to base.probe_schema (structured probe) when CLI supports it
          probe | String,
          # status_core values: 'declared, 'verified, 'failing; adjust adds 'partial
          status | [| 'declared, 'partial, 'verified, 'failing |] | default = 'declared,
          compliance | String | optional,       # e.g. "WCAG 2.1 AA"
          notes | String | optional,
          fix | String | optional,              # deterministic fix command (optional)
        },
  },

  # Runner behaviour — inherits from base.run_defaults.
  # adjust is advisory (continue-with-warnings) not a hard gate.
  # auto_fix_when_available is adjust-specific.
  run = base.run_defaults & {
    on_any_fail = "continue-with-warnings",   # accessibility is progress-tracked, not a hard gate by default
    report_format = "a2ml",
    emit_summary = true,
    auto_fix_when_available = true,
  },
}
