K9!
# SPDX-License-Identifier: MPL-2.0
# dust.k9.ncl — K9 trust-tier component of the dust trident
# Author: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# Pairs with: Dustfile.a2ml (declaration) + dust.ncl (runner).
#
# Verb:       dust            (fine-grained recovery / broom-and-pan cleanup)
# Tier:       Yard            (audit + structural checks; destructive
#                              actions gated behind --apply flag +
#                              explicit per-item approval)
# Authority:  advisory        (continue-with-warnings)
#
# dust is the broom-and-pan + audit-trail verb for echidna. It picks up the
# tiny leftover state that release-gating verbs ignore: stale local/remote
# branches (D001/D002), dangling + /tmp agent worktrees (D010/D011), cargo /
# julia / podman / chapel cache bloat (D020-D023), orphan pid + status files
# (D030/D031), prior-run training artefacts (D040-D042), and source dust —
# untracked TODOs, unused imports, dead code (D050-D052). Where bust declares
# "broken, don't run", dust describes how to safely undo / retire / roll back
# the small remnants. Complement to bust — bust marks the dead end, dust
# describes the exit ramp.
#
# Cardinality: ONE dust trident per repo.
#
# Failure-mode focus: dust is the audit-trail preservation verb —
# defends against E1 refactor stampede (check audit trail still
# intact) and against silent removal (anything swept must have a
# rollback path; anything retired must preserve the evidence of its
# previous existence — e.g. D040-D042 archive rather than delete; the
# PR is the durable record for D001/D002; git history covers D050-D052).

let base_k9 = import "../k9/template-hunt.k9.ncl" in
let base    = import "../_base.ncl" in

{
  pedigree = base_k9.pedigree_schema & {
    contractile_verb = "dust",
    paired_xfile     = "../dust/Dustfile.a2ml",
    paired_runner    = "../dust/dust.ncl",

    tier      = 'Yard,
    authority = 'advisory,

    metadata = {
      name = "dust-k9",
      version = "1.0.0",
      description = "Fine-grained recovery + broom-and-pan + audit-trail runner. Sixth and final trident instance — completes the full verb set. Sweeps the D### remnant namespace; every action idempotent + reversible.",
      paired_xfile = "Dustfile.a2ml",
      paired_runner = "dust.ncl",
      author = "Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>",
    },

    security = {
      leash = 'Yard,
      trust_level = "audit-trail verification + structural checks",
      allow_network = false,
      # dust is the verb that ACTUALLY wants filesystem write — to
      # execute declared broom-and-pan cleanup (prune worktrees, remove
      # orphan pids/caches, archive prior-run artefacts) — but only
      # behind explicit --apply flag + per-item approval. Default is dry-run.
      allow_filesystem_write_conditional = true,
      allow_subprocess = true,
      destructive_action_gating = {
        default_mode = 'dry_run,
        requires_flag = "--apply",
        requires_per_item_approval = true,
        approval_mechanism = 'explicit_user_signature,
        # echidna-specific: the exclusion list is sacred. Active worktrees
        # + production artefacts are NEVER swept even with --apply.
        sacred_exclusions = [
          "/tmp/echidna-saturation",        # other Claude's territory
          "/tmp/echidna-training-*",        # active training artefacts
          "models/neural/best_model",       # canonical model — keep
          "models/neural/final_model",      # canonical model — keep
          "models/neural/gnn_ranker",       # canonical model — keep
          "training_data/proof_states_*.jsonl",  # load-bearing JSONL-fallback path
        ],
      },
    },
  },

  variance_schema = {
    entry_id     | String,
    reason       | String,
    approved_by  | String,
    scope        | String,
    expires      | String,
    review_notes | String | optional,
    rollback_path_preserved | Bool,    # dust-specific: did the variance preserve rollback?
  },

  execution = {
    triggers = [ 'session_close, 'on_demand ],

    per_recovery = {
      verify_rollback_path_documented = true,    # each D### declares `reversible:`
      verify_audit_trail_preserved = true,       # archive-not-delete for D040-D042
      verify_idempotent = true,                   # re-running on clean repo => no-op
      respect_variance = true,
      respect_sacred_exclusions = true,           # D011 exclusion list is sacred
      on_rollback_path_missing = 'warn,          # advisory, not block
      on_audit_trail_broken = 'warn,             # advisory, not block
      on_sacred_exclusion_touched = 'refuse,     # never sweep an excluded path
      # dust-specific: flag any sweep that has been requested but lacks a
      # documented reversible path, or that combines destructive ops
      # (narrow-blast-radius: one dust action per recipe).
      flag_unsafe_recovery = true,
      flag_combined_destructive_ops = true,
    },

    evidence_sinks = [
      { kind = 'verisimdb, table = "contractile_executions",
        schema = "contractile_execution_v1",
        aux_tables = [ "dust_recovery_history" ] },
      { kind = 'drift_log, path = ".machine_readable/6a2/DRIFT.a2ml",
        append_only = true },
    ],

    on_close = {
      re_verify_all_recovery_paths = true,
      diff_against_last_ratification = true,
      emit_drift_entries_for_missing_rollback = true,
      emit_drift_entries_for_broken_audit_trail = true,
      surface_expired_variances = true,
      # dust is advisory — does NOT block session close.
      block_session_close_on_any_drift = false,
    },

    on_open = {
      render_summary = 'plain_language,
      include_drift_log_from_last_close = true,
      include_active_variances = true,
      include_recent_anchors = true,
      anchor_lookback_weeks = 8,

      negotiation = {
        required = true,
        ai_required_inputs = [
          'timeline_realism,
          'industry_standards,
          'audience_feasibility,
          'resulting_invariants,
          'ecosystem_dependencies,
        ],
        user_engagement_required = true,
        user_engagement_mode = 'per_input_response,
        specification_translation = {
          ai_produces_spec_form = true,
          user_reviews_in_domain_language = true,
          schema_authoring_is_ai_responsibility = true,
          translation_faithfulness_auditable = true,
        },
      },

      accountability_pledge = {
        required = true,
        parties = [
          {
            role = 'user,
            pledge = "I have reviewed the declared D### recovery recipes and their reversible paths. I accept accountability for preserving audit trails when sweeping leftover state, and for ensuring every swept item has a documented rollback path (re-fetch, rebuild, or archive). I will not silently delete evidence of prior state, and I will keep the sacred exclusion list intact.",
            signature_required = true,
          },
          {
            role = 'ai_agent,
            pledge = "I will verify audit-trail preservation and a documented reversible path in any broom-and-pan cleanup I perform; I will refuse silent deletion of prior-state evidence; I will archive (not delete) load-bearing training artefacts; I will never touch the sacred exclusion list; I will operate in dry-run mode by default and require explicit --apply + per-item approval for destructive actions; I will keep blast radius narrow (one dust action per recipe).",
            signature_required = true,
          },
        ],
        signed_record_destination = ".machine_readable/6a2/ratification-<session-id>.a2ml",
        must_precede_work = true,
      },

      ratification_record_shape = {
        includes_negotiation_transcript = true,
        includes_both_pledges = true,
        includes_recovery_schedule = true,
        signed = true,
        dated = true,
        session_id = 'required,
        contract_hash = 'required,
      },
    },
  },

  failure_mode_defenses = [
    'A1_enthusiasm_capture,
    'C2_capability_collapse,        # sweep without rollback path = capability collapse
    'D5_sycophancy,                 # AI won't agree to silent deletion / touching exclusions
    'E1_refactor_stampede,          # audit trail preservation check
    'E2_cosmetic_churn,
    'F1_across_session_forgetting,  # recovery history tracked cross-session
  ],
}
