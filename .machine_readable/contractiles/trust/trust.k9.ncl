K9!
# SPDX-License-Identifier: MPL-2.0
# trust.k9.ncl — K9 trust-tier component of the trust trident
# Author: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# Pairs with: Trustfile.a2ml (declaration) + trust.ncl (runner).
# Trident completeness is a hard precondition — a repo shipping
# Trustfile without this file AND its runner is an invalid trident;
# the contractile CLI's verify gate refuses partial publication.
#
# Verb:       trust           (security + provenance + safe-hacking)
# Tier:       Hunt            (capability: subprocess probes may shell out;
#                              active probes in safe_hacking section run real
#                              fuzz/injection/auth-bypass/sandbox-escape attempts
#                              scoped to the repo)
# Authority:  blocking        (HARD GATE — fail-on-violation; part of the
#                              must/trust/bust triple)
#
# trust is the security + provenance + safe-hacking verb. Where must says
# "this MUST hold" and bust says "every failure mode MUST have working
# recovery", trust says "this MUST verify clean": no proof leaves the
# dispatcher without axiom-tracking, integrity, and sandboxing; no
# supply-chain SHA goes unpinned; no banned token enters the Idris2 ABI.
# Failed verification = failed CI = blocked merge. trust is the verb that
# states allowed/denied agent actions and the dispatcher trust boundary.
#
# Cardinality: ONE trust trident per repo.
#
# echidna-bespoke focus: trust catches threat-model misclassification (B1)
# and the "turn off the firewall" capability-collapse (C2) directly — a
# dispatch path emitting a result without axiom tracking (T030), a removed
# sandbox (T040), a stripped `%default total` (T050), or a believe_me
# smuggled into src/abi/ (T051) are all TRUST VIOLATIONS that block. Error
# namespace T### maps 1:1 onto Trustfile.a2ml sections (Integrity /
# Provenance / Supply-Chain / Dispatcher-Trust / Sandbox / ABI-Trust).
# Licence findings (T001) are FLAG-ONLY: never auto-edit — see
# [[feedback_no_automated_licence_edits]].

let base_k9 = import "../k9/template-hunt.k9.ncl" in
let base    = import "../_base.ncl" in

{
  pedigree = base_k9.pedigree_schema & {
    contractile_verb = "trust",
    paired_xfile     = "../trust/Trustfile.a2ml",
    paired_runner    = "../trust/trust.ncl",

    # Hunt-capable (active probes shell out; safe-hacking section runs real
    # fuzz/injection/auth-bypass/sandbox-escape attempts scoped to the repo)
    # AND blocking-authority (failed verification = failed CI). Completes the
    # (Hunt, blocking) triple with must + bust.
    tier      = 'Hunt,
    authority = 'blocking,

    metadata = {
      name = "trust-k9",
      version = "1.0.0",
      description = "Executes T### security/provenance/supply-chain verifications + authorised safe-hacking probes for echidna. HARD GATE: failed verification blocks merge. Primary defense against threat-model misclassification and 'turn off the firewall' capability-collapse (dispatcher trust boundary, solver sandbox, Idris2 ABI totality). Implements negotiation-ratification-accountability protocol inherited from the intend/adjust k9 pattern.",
      paired_xfile = "Trustfile.a2ml",
      paired_runner = "trust.ncl",
      author = "Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>",
    },

    security = {
      leash = 'Hunt,
      trust_level = "verification + authorised-probe + hard-gate",
      allow_network = false,            # verifications offline by default
      allow_filesystem_write = false,   # evidence sinks are indirected
      allow_subprocess = true,
      authorised_probes_only = true,    # probe section explicitly lists allowed targets + probe classes
      probe_scope_enforcement = 'this_repo_only,  # probes NEVER hit external systems
      # echidna-bespoke: the dispatcher trust boundary trust enforces.
      dispatcher_trust_boundary = "no-proof-emits-without-axiom-track-integrity-sandbox",
      error_namespace = "T###",
      # Hunt-tier files must declare whether a cryptographic signature is
      # required. trust trident runs in CI on every PR; signatures are
      # enforced at the trident-runner layer, not in-band.
      signature_required = true,
    },
  },

  # -------------------------------------------------------------------
  # Variance schema — P-shape scoped exceptions per verification.
  # Because trust is BLOCKING authority, variances on trust entries are
  # SIGNIFICANTLY more consequential than variances on adjust (advisory)
  # entries — the variance approver MUST be the repo maintainer or above
  # for critical-severity entries (T001/T002/T010/T020/T030/T040/T050/T051).
  # -------------------------------------------------------------------
  variance_schema = {
    entry_id     | String,   # which T### verification / probe id
    reason       | String,
    approved_by  | String,   # maintainer or above for critical entries
    scope        | String,   # path glob | session-id | "until-<date>"
    expires      | String,   # absolute date; trust variances cannot be open-ended
    review_notes | String | optional,
    # trust-specific guardrails:
    severity_acknowledged | [| 'critical, 'high, 'medium, 'low |],
    waived_risk_description | String,  # plain language — what is being accepted
  },

  # -------------------------------------------------------------------
  # Execution policy
  # -------------------------------------------------------------------
  execution = {
    # pre_push + pre_commit on anything touching security-adjacent files
    # (dispatch.rs, executor/, integrity/, src/abi/, .github/workflows/)
    # + session_close (drift check) + on_demand.
    triggers = [ 'session_close, 'on_demand, 'pre_push, 'pre_commit_security_adjacent ],

    # Per-verification execution. Failed verification = blocked merge.
    per_verification = {
      run_probe = true,
      record_outcome = true,
      respect_variance = true,    # active variance suppresses the gate
      on_unmet = 'fail,           # BLOCKING — the opposite of adjust's advisory drift-log
      severity_escalation = 'honour,  # critical > high > medium > low in gate decisions
    },

    # Per-safe-hacking-probe execution. If a probe FINDS what it was supposed
    # to prevent finding (e.g. injection succeeds, solver escapes its sandbox,
    # auth-bypass works), that's an EXPLOIT demonstration — hard fail.
    per_probe = {
      run_probe = true,
      record_outcome = true,
      honour_expected_outcome = true,
      on_unexpected_exploit_success = 'fail,  # exploit found where it shouldn't be
      scope_enforcement = 'this_repo_only,    # never touch external systems
      timeout_honouring = 'strict,
    },

    # Evidence sinks — BOTH written, every execution. VeriSimDB is the
    # queryable proof-attempt / contractile-execution store for echidna.
    evidence_sinks = [
      {
        kind   = 'verisimdb,
        table  = "contractile_executions",
        schema = "contractile_execution_v1",
        # trust-specific sub-tables for verification + probe outcomes (threat-model audit)
        aux_tables = [ "trust_verifications", "trust_probes" ],
      },
      {
        kind        = 'drift_log,
        path        = ".machine_readable/6a2/DRIFT.a2ml",
        append_only = true,
      },
    ],

    # Session-close hook — re-verify EVERYTHING, re-run probes, diff against
    # last ratification. The "turn off the firewall" scenario (sandbox removed,
    # axiom tracker disabled, %default total stripped) must be caught here if
    # it wasn't caught at pre-push.
    on_close = {
      re_execute_all_verifications = true,
      re_run_all_safe_hacking_probes = true,
      diff_against_last_ratification = true,
      emit_drift_entries_for_new_failures = true,
      surface_expired_variances = true,
      # trust-specific: if any blocking-severity verification is newly failing,
      # session close is BLOCKED from completing.
      block_session_close_on_critical_drift = true,
    },

    # -----------------------------------------------------------------
    # Session-open hook — NEGOTIATION + RATIFICATION + ACCOUNTABILITY
    # (inherited shape from the intend/adjust k9 pattern; trust-specific
    # threat-model foregrounding below)
    # -----------------------------------------------------------------
    on_open = {
      # --- Context presentation ---
      render_summary = 'plain_language,    # metaphor-capture defense
      include_drift_log_from_last_close = true,
      include_active_variances = true,
      include_recent_anchors = true,
      anchor_lookback_weeks = 8,

      # trust-specific: the threat model is rendered FIRST, before any
      # negotiation, so the adversary and stakes are fresh in both minds.
      # Directly defends against B1 (threat-model misclassification) — for
      # echidna the stakes are an UNSOUND PROOF leaving the dispatcher
      # (axiom smuggled in, sandbox bypassed, ABI totality stripped).
      threat_model_foregrounding = {
        required = true,
        render_adversaries = true,   # untrusted solver binary, malicious proof artifact, supply-chain action
        render_stakes = true,        # unsound proof emitted = trust violation
        render_compliance_regimes = true,
        render_audience_sensitivity = true,
        # If the AI is about to suggest a trust-weakening action (disable a
        # sandbox, relax axiom tracking, drop a SHA pin), it must re-render
        # the threat model before the suggestion lands.
        re_render_before_weakening_suggestion = true,
      },

      # --- Negotiation phase (five mandatory inputs) ---
      negotiation = {
        required = true,
        ai_required_inputs = [
          'timeline_realism,
          'industry_standards,        # for echidna: solver-soundness practice, supply-chain SLSA, SHA-pinning
          'audience_feasibility,      # who is the adversary? (untrusted solver / proof artifact / action)
          'resulting_invariants,      # which T### entries the work creates/amends
          'ecosystem_dependencies,    # BLAKE3/SHAKE3, Podman/bwrap, Idris2 totality, GPG signing infra
        ],
        user_engagement_required = true,
        user_engagement_mode = 'per_input_response,
        specification_translation = {
          ai_produces_spec_form = true,
          user_reviews_in_domain_language = true,
          schema_authoring_is_ai_responsibility = true,
          translation_faithfulness_auditable = true,
          # trust-specific: the AI renders sandbox policy, integrity hash
          # choice, axiom danger levels in domain language ("solvers run in
          # bubblewrap, binaries BLAKE3-verified, Reject-level axioms blocked")
          # rather than forcing the user into Nickel-schema authoring.
        },
      },

      # --- Accountability pledge (both parties, explicit) ---
      # trust's pledge is MORE stringent than adjust's because the authority
      # is blocking. Accepting accountability here means accepting that
      # security-affecting decisions have blocking consequence.
      accountability_pledge = {
        required = true,
        parties = [
          {
            role = 'user,
            pledge = "I have reviewed the threat model, the declared T### trust obligations, and the dispatcher trust boundary (no proof emits without axiom-tracking, integrity, and sandboxing). I accept accountability for meeting these obligations and understand that failed verification will block merges until resolved or varied. I will not attempt to disable a verification, sandbox, or the axiom tracker to unblock a merge; I will raise a variance or amendment instead. Licence findings (T001) are handled manually, per-file — never auto-edited.",
            signature_required = true,
          },
          {
            role = 'ai_agent,
            pledge = "I will hold the line on declared T### trust obligations. I will refuse to 'disable' verifications, solver sandboxing, axiom tracking, or ABI totality to unblock merges; I will refuse security-weakening suggestions that contradict the threat model even when the user is enthusiastic; I will surface drift at session close; I will re-render the threat model before proposing any weakening action. I will NEVER auto-edit a licence header (T001 is flag-only). If a legitimate scope shift demands security reduction, I will require a variance with severity acknowledgement or an amendment, not silent acceptance.",
            signature_required = true,
          },
        ],
        signed_record_destination = ".machine_readable/6a2/ratification-<session-id>.a2ml",
        must_precede_work = true,
      },

      ratification_record_shape = {
        includes_negotiation_transcript = true,
        includes_both_pledges = true,
        includes_threat_model_snapshot = true,   # trust-specific
        signed = true,
        dated = true,
        session_id = 'required,
        contract_hash = 'required,
      },
    },
  },

  # -------------------------------------------------------------------
  # Failure-mode defenses — trust is the widest-coverage verb.
  # See feedback_ai_failure_mode_catalog.md for the full catalog.
  # -------------------------------------------------------------------
  failure_mode_defenses = [
    # Category A — enthusiasm / narrative capture
    'A1_enthusiasm_capture,            # scope breach blocks via blocking authority
    'A2_metaphor_capture,              # render_summary + re_render_before_weakening
    # Category B — threat-model misclassification (trust's flagship defense)
    'B1_threat_model_misclass,         # threat_model_foregrounding = required
    'B2_audience_sensitivity_collapse, # audience_feasibility in negotiation
    'B3_compliance_prior_drift,        # industry_standards in negotiation
    # Category C — scope/capability erosion (the "firewall off" scenario)
    'C2_capability_collapse,           # blocking gate prevents silent sandbox/axiom-track removal
    'C3_helpfulness_inflation,         # trust-affecting changes need variance/amendment
    'C4_modernization_drift,           # unrequested crypto-lib / solver upgrade caught
    # Category D — epistemic failures
    'D4_error_hiding,                  # on_unmet = 'fail makes hiding impossible
    'D5_sycophancy,                    # pledge forces AI to hold line against enthusiasm
    'D6_false_pessimism,               # negotiation requires AI to cite constraint, not assert impossibility
    # Category E — refactor/churn
    'E4_cargo_cult_security,           # probes VERIFY the claimed protection actually runs (sandbox, integrity)
    # Category F — session drift
    'F1_across_session_forgetting,     # on_open reads last-ratification, drift log, recent ANCHORs
  ],
}
