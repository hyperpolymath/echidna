# SPDX-License-Identifier: MPL-2.0
# Dust — fine-grained recovery / broom-and-pan cleanup runner
#
# Pairs with: Dustfile.a2ml (same directory)
# Verb:       dust
# Semantics:  fine-grained recovery (broom-and-pan: pick up tiny leftover state).
#             Where bust rolls back a broken commit and adjust migrates to a new
#             upstream version, dust cleans the small dusty remnants — stale
#             branches, orphan caches, dropped /tmp worktrees, half-merged stash
#             entries, leftover process pids. Advisory by default; destructive
#             actions are gated behind `--apply` + per-item approval (dry-run
#             default). Audit-trail preservation: nothing is swept without a
#             documented rollback path.
# CLI:        `contractile dust find`            → list recovery candidates (D###)
#             `contractile dust sweep`           → dry-run the cleanup recipes
#             `contractile dust sweep --apply`   → actually clean (gated)
#
# Anything else in this directory is human-only notes/archive; machines ignore.
#
# Base: ../_base.ncl provides pedigree_schema, run_defaults, probe_schema.
# See: docs/CONTRACTILE-SPEC.adoc

let base = import "../_base.ncl" in

{
  pedigree = base.pedigree_schema & {
    contractile_verb = "dust",
    semantics = "rollback / recovery / deprecation / audit-trail preservation",
    security = {
      leash = 'Yard,
      trust_level = "proposes broom-and-pan cleanup; --apply + per-item approval required to execute",
      allow_network = false,
      allow_filesystem_write = true,      # --apply mode writes (prunes worktrees, removes pids/caches)
      allow_subprocess = true,
      destructive_mode_requires_flag = "--apply",
    },
    metadata = {
      name = "dust-runner",
      version = "1.0.0",
      description = "Identifies and optionally cleans the D### fine-grained recovery candidates listed in Dustfile.a2ml (stale branches, orphan caches, dropped /tmp worktrees, half-merged stashes, leftover pids). Idempotent + reversible; clean repo => no-op. Destructive mode gated behind --apply + per-item approval; dry-run default.",
      paired_xfile = "Dustfile.a2ml",
      author = "Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>",
    },
  },

  schema = {
    recovery_candidates
      | Array {
          id | String,                     # D### error-code namespace (e.g. "D011-tmp-agent-worktrees")
          description | String,
          target | String,                 # branch / path / cache / pid / worktree being swept
          reason | String,                 # why it's a recovery candidate
          severity | String | optional,    # Dustfile severities are uniformly "low" (broom-and-pan)
          # TODO: migrate to base.probe_schema (structured probe) when CLI supports it
          probe | String | optional,       # command that confirms it's still present + sweepable
          dust | String | optional,        # the cleanup recipe (one dust action per recipe)
          reversible | String | optional,  # how the action is undone (re-fetch, rebuild, re-create)
          # dust has a non-standard status progression (no 'verified):
          #   'declared → 'proposed → 'approved → 'removed
          status | [| 'declared, 'proposed, 'approved, 'removed |] | default = 'declared,
          approver | String | optional,    # who signed off (for 'approved / 'removed)
          excluded | String | optional,    # sacred-exclusion note (active worktrees / production artefacts)
          notes | String | optional,
        },
  },

  # Runner behaviour — inherits from base.run_defaults.
  # dust is advisory; apply_requires_approval is dust-specific.
  run = base.run_defaults & {
    on_any_fail = "continue-with-warnings",
    report_format = "a2ml",
    emit_summary = true,
    apply_requires_approval = true,       # only 'approved items get swept, even with --apply
  },
}
