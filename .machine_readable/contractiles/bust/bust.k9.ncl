# SPDX-License-Identifier: PMPL-1.0-or-later
# bust.k9.ncl — K9 trust-tier component of the bust trident
# Author: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# Pairs with: Bustfile.a2ml (declaration) + bust.ncl (runner).
#
# Verb:       bust            (error handling + failure recovery)
# Tier:       Hunt            (capability: subprocess probes may shell out;
#                              may inject failures into system-under-test)
# Authority:  blocking        (fail-on-violation; part of must/trust/bust triple)
#
# bust is the failure-mode verb. Declared failure modes MUST have working
# recovery paths. If a failure mode lacks recovery, or the recovery fails
# under drill, bust blocks the repo (hard gate). No undeclared failure modes
# are permitted; every detected failure must be in Bustfile.
#
# Cardinality: ONE bust trident per repo.
#
# Failure-mode focus: bust catches missing-recovery-path failures
# (G2 no rollback on partial write) and broken-recovery failures
# (G1 recovery timeout, G3 recovery partial-success). Complements must
# (invariant) and trust (cleanliness) as the third blocking verb in the
# (Hunt, blocking) triple.

let base_k9 = import "../k9/template-hunt.k9.ncl" in
let base    = import "../_base.ncl" in

{
  pedigree = base_k9.pedigree_schema & {
    contractile_verb = "bust",
    paired_xfile     = "../bust/Bustfile.a2ml",
    paired_runner    = "../bust/bust.ncl",

    tier      = 'Hunt,
    authority = 'blocking,

    metadata = {
      name = "bust-k9",
      version = "1.0.0",
      description = "Failure-mode injection and recovery verification. Third trident instance. (Hunt, blocking) authority pattern.",
      paired_xfile = "Bustfile.a2ml",
      paired_runner = "bust.ncl",
      author = "Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>",
    },

    security = {
      leash = 'Hunt,
      trust_level = "controlled failure injection; scoped to system-under-test",
      allow_network = false,
      allow_filesystem_write = true,      # drills may write transient state (tmp dirs, test DBs)
      allow_subprocess = true,
      injection_scope = 'system_under_test_only,
    },
  },

  variance_schema = {
    entry_id           | String,
    reason             | String,
    approved_by        | String,
    scope              | String,
    expires            | String,
    review_notes       | String | optional,
    # bust-specific: which failure mode the variance exempts
    failure_mode_exempted | String,
    recovery_accepted_as | String,       # "partial" | "deferred" | "unavailable"
  },

  execution = {
    triggers = [ 'session_close, 'on_demand, 'pre_push ],

    per_failure_mode = {
      inject_failure = true,
      record_recovery_outcome = true,
      respect_variance = true,
      # bust-specific authority: failure without recovery blocks merge.
      on_missing_recovery = 'block_session_close,
      on_recovery_failed = 'block_session_close,
      on_recovery_partial = 'block_session_close_and_escalate,
      record_recovery_times = true,      # feeds performance tier
    },

    evidence_sinks = [
      { kind = 'verisimdb, table = "contractile_executions",
        schema = "contractile_execution_v1",
        aux_tables = [ "bust_recovery_times" ] },
      { kind = 'failure_log, path = ".machine_readable/6a2/FAILURES.a2ml",
        append_only = true },
    ],

    on_close = {
      re_drill_all_failure_modes = true,
      diff_against_last_ratification = true,
      emit_failure_entries_for_recovery_broken = true,
      surface_expired_variances = true,
      # bust is blocking — breaks session close on any unverified recovery.
      block_session_close_on_any_unverified_recovery = true,
    },

    on_open = {
      render_summary = 'plain_language,
      include_failure_log_from_last_close = true,
      include_active_variances = true,
      include_recent_anchors = true,
      anchor_lookback_weeks = 8,
      include_recovery_performance_trend = true,

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
            pledge = "I have reviewed the failure modes and recovery paths. I accept accountability for covering all failure modes; any undeclared failure mode found in production is a shortcoming of the declared Bustfile.",
            signature_required = true,
          },
          {
            role = 'ai_agent,
            pledge = "I will block merges if any failure mode lacks a recovery path or if recovery fails under drill. I will refuse undeclared failure modes and require amendments to Bustfile, not workarounds.",
            signature_required = true,
          },
        ],
        signed_record_destination = ".machine_readable/6a2/ratification-<session-id>.a2ml",
        must_precede_work = true,
      },

      ratification_record_shape = {
        includes_negotiation_transcript = true,
        includes_both_pledges = true,
        includes_failure_modes_snapshot = true,
        signed = true,
        dated = true,
        session_id = 'required,
        contract_hash = 'required,
      },
    },
  },

  failure_mode_defenses = [
    'G1_recovery_timeout,
    'G2_no_rollback,
    'G3_partial_recovery,             # bust tracks recovery success, not just attempt
    'C3_helpfulness_inflation,         # helpful additions that add failure modes untracked
    'C4_modernization_drift,           # change to error handling needs Bustfile entry
  ],
}
