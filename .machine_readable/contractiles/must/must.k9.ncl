K9!
# SPDX-License-Identifier: MPL-2.0
# must.k9.ncl — K9 trust-tier component of the must trident
# Author: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# Pairs with: Mustfile.a2ml (declaration) + must.ncl (runner).
# Trident completeness is a hard precondition — a repo shipping
# Mustfile without this file AND its runner is an invalid trident;
# the contractile CLI's verify gate refuses partial publication.
#
# Verb:       must            (invariant assertion — release-blocking)
# Tier:       Hunt-read-only  (capability: subprocess probes shell out
#                              for grep/test/file-check; no mutation;
#                              no network; no write)
# Authority:  blocking        (HARD GATE — the canonical gating verb)
#
# must is the concrete + persistent verb — release-blocking invariants
# that must hold. Complement to trust (concrete + ephemeral). Together
# must + trust + bust form the (Hunt, blocking) triple in the contractile
# set.
#
# For Echidna — a trust-hardened neurosymbolic theorem-proving platform
# (Rust core + Julia ML + Idris2 ABI + Zig FFI + optional Chapel) — the
# Physical-State invariants ground the repo's UX Manifesto baseline:
# LICENSE/README presence, no banned hardcoded developer paths leaking
# into source, Containerfile-not-Dockerfile (RSR-H15), Justfile-not-
# Makefile (RSR-H14). These are exactly the invariants a ~128-backend
# proof platform must not silently erode as backends and migrations churn.
#
# Cardinality: ONE must trident per repo.
#
# Failure-mode focus: must is the primary catchment for subtle
# invariant-erosion drift. Where trust catches "turn off the firewall"
# (outrageous), must catches "the LICENSE file that was required is now
# missing" / "a banned hardcoded path has reappeared in a new prover
# backend" / "a Dockerfile crept back in" (subtle). Key defense against
# A5 (commercial fabrication of success "facts" — invariants ground truth
# against marketing copy about prover counts) and D1 (lore fabrication
# about what the repo contains).

let base_k9 = import "../k9/template-hunt.k9.ncl" in
let base    = import "../_base.ncl" in

{
  pedigree = base_k9.pedigree_schema & {
    contractile_verb = "must",
    paired_xfile     = "../must/Mustfile.a2ml",
    paired_runner    = "../must/must.ncl",

    # α two-axis: Hunt tier (subprocess for grep/test/etc.) but
    # restricted to read-only operations. Blocking authority because
    # must is the canonical gating verb.
    tier      = 'Hunt,
    authority = 'blocking,

    metadata = {
      name = "must-k9",
      version = "1.0.0",
      description = "Evaluates release-blocking Physical-State invariants as a hard gate for Echidna. Completes the (Hunt, blocking) triple with trust + bust; complements trust (ephemeral blocking) with persistent invariant blocking.",
      paired_xfile = "Mustfile.a2ml",
      paired_runner = "must.ncl",
      author = "Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>",
    },

    security = {
      leash = 'Hunt,
      trust_level = "read-only invariant verification with subprocess",
      allow_network = false,
      allow_filesystem_write = false,
      allow_subprocess = true,
      probe_scope = 'read_only,              # must probes NEVER mutate
      # Hunt-tier files must declare whether a cryptographic signature
      # is required. The must trident runs in CI on every PR; signatures
      # are enforced at the trident-runner layer, not in-band.
      signature_required = true,
      probe_kinds_allowed = [
        'file_existence,
        'pattern_presence,
        'pattern_absence,
        'schema_match,
        'version_equality,
        'count_threshold,
      ],
      probe_kinds_denied = [
        'network_call,
        'filesystem_mutation,
        'external_api,
        'exploit_attempt,          # that's trust's safe_hacking territory
      ],
    },
  },

  # -------------------------------------------------------------------
  # Variance schema — trust-style severity acknowledgement.
  # Because must is BLOCKING, variances carry real weight. Critical-
  # severity invariants can only be varied by maintainer-or-above.
  # -------------------------------------------------------------------
  variance_schema = {
    entry_id     | String,   # which invariant id the variance applies to
    reason       | String,
    approved_by  | String,   # maintainer or above for critical-severity
    scope        | String,   # path glob | session-id | "until-<date>"
    expires      | String,   # absolute date; must variances cannot be open-ended
    review_notes | String | optional,
    severity_acknowledged     | [| 'critical, 'high, 'medium |],
    waived_consequence_description | String,  # plain language — what breaking the invariant actually does
  },

  execution = {
    triggers = [ 'session_close, 'on_demand, 'pre_push, 'pre_merge ],

    # Per-invariant execution. Failed invariant = blocked merge.
    per_invariant = {
      run_probe = true,
      record_outcome = true,
      respect_variance = true,    # active variance suppresses the gate
      on_unmet = 'fail,           # BLOCKING
      severity_escalation = 'honour,
      # Subtle-erosion defense: track per-invariant trend over sessions.
      # An invariant that passes once and then starts failing in a
      # later session without explicit amendment = suspect drift;
      # surface as high-priority drift log entry. Especially relevant as
      # Echidna churns prover backends, the ReScript→AffineScript UI
      # migration, and the npm→Deno migration.
      track_per_session_trend = true,
      flag_suspicious_regressions = true,
    },

    evidence_sinks = [
      {
        kind   = 'verisimdb,
        table  = "contractile_executions",
        schema = "contractile_execution_v1",
        aux_tables = [ "must_invariant_history" ],  # per-invariant trend record
      },
      {
        kind        = 'drift_log,
        path        = ".machine_readable/6a2/DRIFT.a2ml",
        append_only = true,
      },
    ],

    # Session-close hook — re-evaluate all invariants. Block close on
    # critical drift (same policy as trust + bust).
    on_close = {
      re_execute_all_invariants = true,
      diff_against_last_ratification = true,
      emit_drift_entries_for_new_failures = true,
      surface_expired_variances = true,
      # Critical must drift blocks session close — consistent with trust.
      block_session_close_on_critical_drift = true,
      # Must-specific: if a previously-passing invariant is now failing
      # without an associated variance or amendment, that's suspected
      # silent regression — surface prominently at next session open.
      flag_silent_regression = true,
    },

    # -----------------------------------------------------------------
    # Session-open hook — NEGOTIATION + RATIFICATION + ACCOUNTABILITY
    # (inherited from intend.k9.ncl v2.0.0 + trust.k9.ncl extensions)
    # -----------------------------------------------------------------
    on_open = {
      # --- Context presentation ---
      render_summary = 'plain_language,
      include_drift_log_from_last_close = true,
      include_active_variances = true,
      include_recent_anchors = true,
      anchor_lookback_weeks = 8,

      # Must-specific: surface any silent regressions flagged at last
      # close so they can't quietly persist across sessions.
      include_silent_regressions = true,

      # --- Negotiation phase (five mandatory inputs) ---
      negotiation = {
        required = true,
        ai_required_inputs = [
          'timeline_realism,
          'industry_standards,      # what invariants derive from external standards (RSR/CCCP)
          'audience_feasibility,    # who is the invariant protecting
          'resulting_invariants,    # what NEW must entries result from the work
          'ecosystem_dependencies,  # what the invariants depend on
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

      # --- Accountability pledge ---
      # Must's pledge parallels trust's but around invariants rather
      # than threat model. User pledges not to disable invariants to
      # unblock merges; AI pledges to hold the line on declared
      # invariants even against enthusiastic scope expansion.
      accountability_pledge = {
        required = true,
        parties = [
          {
            role = 'user,
            pledge = "I have reviewed the declared invariants and the consequences of breaching them. I accept accountability for meeting these invariants and understand that failed invariants block merges. I will raise a variance (with severity acknowledgement) or an amendment rather than disabling a probe to unblock a merge.",
            signature_required = true,
          },
          {
            role = 'ai_agent,
            pledge = "I will hold the declared invariants. I will refuse to weaken probes to unblock merges; I will refuse scope-creep suggestions that would remove an invariant silently; I will surface silent regressions at session close; I will require variance-with-severity or amendment for any legitimate scope shift, not quiet probe disablement.",
            signature_required = true,
          },
        ],
        signed_record_destination = ".machine_readable/6a2/ratification-<session-id>.a2ml",
        must_precede_work = true,
      },

      ratification_record_shape = {
        includes_negotiation_transcript = true,
        includes_both_pledges = true,
        includes_invariant_summary = true,       # must-specific
        signed = true,
        dated = true,
        session_id = 'required,
        contract_hash = 'required,
      },
    },
  },

  # -------------------------------------------------------------------
  # Failure-mode defenses — must's specialisation is subtle-invariant
  # erosion. Overlaps with trust + bust on blocking authority but focused
  # on persistent invariants rather than ephemeral transactional state or
  # failure-recovery paths.
  # -------------------------------------------------------------------
  failure_mode_defenses = [
    # Category A — enthusiasm capture
    'A1_enthusiasm_capture,          # scope breach via blocking authority
    'A5_grandiose_scale_hype,        # invariants are ground truth vs prover-count hype
    # Category C — scope/capability erosion
    'C1_scope_creep,                 # feature-adjacent changes flagged if they break invariants
    'C2_capability_collapse,         # invariant removal requires amendment
    'C3_helpfulness_inflation,       # added features must respect declared invariants
    # Category D — epistemic failures
    'D1_lore_fabrication,            # invariants are verifiable truth, not AI-recollection
    'D2_completeness_illusion,       # invariant probe must cite behavioural check, not build-success
    'D3_test_theatre,                # invariants require real verification not mock-passing
    'D4_error_hiding,                # on_unmet = 'fail makes hiding impossible
    # Category E — refactor/churn
    'E1_refactor_stampede,           # refactor must preserve invariants
    'E3_premature_abstraction,       # abstraction must not violate invariants
    # Category F — session drift
    'F1_across_session_forgetting,   # track_per_session_trend catches re-introduction
  ],
}
