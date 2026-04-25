# SPDX-License-Identifier: PMPL-1.0-or-later
# (MPL-2.0 is automatic legal fallback until PMPL is formally recognised)
#
# _base.ncl — Shared contractile base
#
# Provides four named schema fragments imported by every verb runner:
#
#   pedigree_schema   — canonical pedigree block shape
#   status_core_doc   — documentation of the shared status trio (String list)
#   probe_schema      — target structured probe form (spec only; verb files
#                       still use probe | String with TODO comments)
#   run_defaults      — default runner behaviour
#
# Usage in a verb runner:
#
#   let base = import "../_base.ncl" in
#   {
#     pedigree = base.pedigree_schema & {
#       contractile_verb = "must",
#       semantics = "invariant",
#       security = {
#         leash = 'Kennel,
#         trust_level = "read-only verification",
#         allow_network = false,
#         allow_filesystem_write = false,
#         allow_subprocess = true,
#       },
#       metadata = {
#         name = "must-runner",
#         version = "1.0.0",
#         description = "...",
#         paired_xfile = "Mustfile.a2ml",
#         author = "Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>",
#       },
#     },
#     schema = { ... },
#     run = base.run_defaults & { on_any_fail = "exit-nonzero" },
#   }
#
# See: docs/CONTRACTILE-SPEC.adoc §Shared Base

{
  # -------------------------------------------------------------------------
  # pedigree_schema
  #
  # The canonical shape of the `pedigree` block required in every verb runner.
  # Verb runners merge this with their verb-specific values using Nickel's `&`
  # (right-priority merge). Override contractile_verb, semantics, security.*,
  # and metadata.* in each verb.
  # -------------------------------------------------------------------------
  pedigree_schema = {
    schema_version | String | default = "1.0.0",
    contractile_verb | String | default = "UNSET",   # MUST override in verb
    semantics | String | default = "UNSET",           # MUST override in verb
    security = {
      leash | [| 'Kennel, 'Yard, 'Hunt |] | default = 'Kennel,
      trust_level | String | default = "UNSET",       # MUST override in verb
      allow_network | Bool | default = false,
      allow_filesystem_write | Bool | default = false,
      allow_subprocess | Bool | default = true,
      # verb-specific additional security fields go in the verb's merge override:
      # e.g. authorised_probes_only (trust), injection_scope (bust),
      #      destructive_mode_requires_flag (dust)
    },
    metadata = {
      name | String | default = "UNSET",              # MUST override in verb
      version | String | default = "1.0.0",
      description | String | default = "UNSET",       # MUST override in verb
      paired_xfile | String | default = "UNSET",      # MUST override in verb
      author | String | default = "Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>",
    },
  },

  # -------------------------------------------------------------------------
  # status_core_doc
  #
  # Documents the minimum shared status values present in every verb's status
  # enum: declared, verified, failing.
  #
  # Nickel does not support structural enum extension, so verb files reproduce
  # their full enum verbatim in `schema`. This field serves as documentation
  # and for tooling that introspects the base.
  #
  # Verbs that extend status_core (i.e. all except must + trust):
  #   adjust:  + 'partial
  #   bust:    + 'drilled
  #   dust:    'declared, 'proposed, 'approved, 'removed  (non-standard)
  #   intend:  intents: 'declared, 'in_progress, 'done, 'deferred, 'retired
  #            wishes:  'declared, 'in_progress, 'achieved, 'abandoned
  #            (the wishes schema was absorbed from the deprecated `lust`
  #             verb 2026-04-18; lust/ dir removed estate-wide)
  #
  # See: docs/CONTRACTILE-SPEC.adoc §Per-Verb Extension
  # -------------------------------------------------------------------------
  status_core_doc = "status_core values: declared | verified | failing — extended per verb",

  # -------------------------------------------------------------------------
  # probe_schema
  #
  # The TARGET structured probe form. See: docs/CONTRACTILE-SPEC.adoc §Probe
  #
  # IMPORTANT: This is a spec-only definition. Existing verb runner files still
  # use `probe | String` with a `# TODO: migrate to probe_schema` comment.
  # This is a breaking change; migration happens when the CLI supports both
  # forms.
  #
  # Adopters writing new xfiles should prefer the structured form:
  #   probe = {
  #     command = "test -f my-file",
  #     timeout_seconds = 60,
  #     allowed_exit_codes = [0],
  #     permission_class = 'read_only,
  #   }
  # -------------------------------------------------------------------------
  probe_schema = {
    command | String,
    timeout_seconds | Number | default = 300,
    allowed_exit_codes | Array Number | default = [0],
    permission_class
      | [| 'read_only, 'filesystem_write, 'subprocess, 'network |]
      | default = 'read_only,
  },

  # -------------------------------------------------------------------------
  # run_defaults
  #
  # Default runner behaviour. Verb runners merge this with verb-specific
  # overrides using Nickel's `&` (right-priority merge).
  #
  # Most verbs override on_any_fail:
  #   "exit-nonzero"          : hard gate  (must, trust, bust, adjust-gating)
  #   "continue-with-warnings": advisory   (dust, adjust)
  #   "continue"              : never gate (intend — covers both intents and wishes)
  # -------------------------------------------------------------------------
  run_defaults = {
    on_pass = "continue",
    on_any_fail = "exit-nonzero",
    report_format = "a2ml",
    emit_summary = true,
  },
}
