# SPDX-License-Identifier: MPL-2.0
# Trust — security + provenance + safe-hacking runner
#
# Pairs with: Trustfile.a2ml (same directory)
# Verb:       trust
# Semantics:  integrity / provenance / supply-chain / dispatcher-trust /
#             sandbox / ABI-trust verification (Trustfile T### namespace)
#             PLUS a declared "safe hacking + testing" section — authorised
#             offensive probes (fuzz, injection, auth-bypass, chaos) scoped
#             to the repo under test, NEVER touching external systems.
#             States what the agent / CI is ALLOWED to do, the trust
#             boundary, and what must be verifiable before any proof leaves
#             the dispatcher.
# CLI:        `contractile trust verify` → run all verifications (read-only)
#             `contractile trust probe`  → run declared safe-hacking probes
#
# Anything else in this directory is human-only notes/archive; machines ignore.
#
# Base: ../_base.ncl provides pedigree_schema, run_defaults, probe_schema.
# See: docs/CONTRACTILE-SPEC.adoc

let base = import "../_base.ncl" in

{
  pedigree = base.pedigree_schema & {
    contractile_verb = "trust",
    semantics = "security + provenance + safe-hacking",
    security = {
      leash = 'Hunt,
      trust_level = "verification + authorised-probe + hard-gate",
      allow_network = false,            # verifications are offline by default
      allow_filesystem_write = false,   # trust writes NOTHING (evidence sinks indirected)
      allow_subprocess = true,
      authorised_probes_only = true,    # safe_hacking section must explicitly list allowed targets + classes
      probe_scope_enforcement = 'this_repo_only,  # probes NEVER hit external systems
      # echidna-bespoke: trust states the dispatcher trust boundary — no proof
      # result leaves dispatch.rs without axiom-tracking + integrity + sandboxing.
      dispatcher_trust_boundary = "no-proof-emits-without-axiom-track-integrity-sandbox",
      error_namespace = "T###",
    },
    metadata = {
      name = "trust-runner",
      version = "1.0.0",
      description = "Evaluates the Trustfile.a2ml T### security/provenance/supply-chain obligations plus authorised safe-hacking probes. All probes are scoped to the repo under test; never hits external systems. Hard-gates: failed verification blocks merge.",
      paired_xfile = "Trustfile.a2ml",
      author = "Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>",
    },
  },

  schema = {
    verifications
      | Array {
          id | String,                    # T### error-code (e.g. "T001-license-content")
          description | String,
          # TODO: migrate to base.probe_schema (structured probe) when CLI supports it
          probe | String,                 # read-only; exit 0 = pass
          # status_core values: 'declared, 'verified, 'failing
          status | [| 'declared, 'verified, 'failing |] | default = 'declared,
          # trust uses all four severity levels (mirrors Trustfile severity:)
          severity | [| 'critical, 'high, 'medium, 'low |] | default = 'high,
          # echidna-bespoke: which Trustfile section the T### entry belongs to
          section | [| 'integrity, 'provenance, 'supply_chain, 'dispatcher_trust, 'sandbox, 'abi_trust |] | optional,
          recovery | String | optional,   # mirrors Trustfile `recovery:` (never auto-edit licences)
          notes | String | optional,
        },

    # Safe-hacking + testing section. Each probe here is an ACTIVELY EXECUTED
    # test — fuzz runs, chaos probes, auth-bypass attempts, injection tests,
    # solver-sandbox escape attempts. All scoped to the current repo.
    safe_hacking
      | {
          scope | String,                 # e.g. "this-repo-only" / "localhost"
          allowed_probe_classes
            | Array [| 'fuzz, 'property_test, 'chaos, 'auth_bypass, 'injection, 'timing, 'sandbox_escape |]
            | default = [],
          probes
            | Array {
                id | String,
                class | [| 'fuzz, 'property_test, 'chaos, 'auth_bypass, 'injection, 'timing, 'sandbox_escape |],
                description | String,
                # TODO: migrate to base.probe_schema (structured probe) when CLI supports it
                probe | String,             # command to run the probe
                expected_outcome | [| 'probe_blocks_attempt, 'probe_finds_no_issue |],
                timeout_seconds | Number | default = 300,
                notes | String | optional,
              }
            | default = [],
        }
      | default = { scope = "this-repo-only", allowed_probe_classes = [], probes = [] },
  },

  # Runner behaviour — inherits from base.run_defaults.
  # trust is BLOCKING (must + trust + bust triple); has an extra field for
  # unexpected safe-hacking outcomes.
  run = base.run_defaults & {
    on_any_fail = "exit-nonzero",       # hard gate on verifications
    safe_hacking_on_unexpected_outcome = "exit-nonzero",  # probe found what it shouldn't = block
    report_format = "a2ml",
    emit_summary = true,
  },
}
