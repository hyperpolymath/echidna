K9!
# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
# K9 Kennel-level guard: echidna project metadata and proof-system invariants
# Security Level: Kennel (data-only, no execution)
# No signature required

{
  pedigree = {
    schema_version = "1.0.0",
    component_type = "proof-tool-metadata",
    security = {
      leash = 'Kennel,
      trust_level = "data-only",
      allow_network = false,
      allow_filesystem_write = false,
      allow_subprocess = false,
    },
    metadata = {
      name = "echidna-metadata",
      version = "2.1.0",
      description = "Echidna: neurosymbolic theorem proving platform — project invariants",
      author = "Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>",
    },
  },

  # Project configuration
  config = {
    # Proof system invariants (CRITICAL)
    proof_system = {
      # Dangerous proof bypasses that must NEVER appear in proofs
      forbidden_proof_patterns = [
        "believe_me",
        "assert_total",
        "Admitted",
        "sorry",
        "unsafeCoerce",
        "Obj.magic",
        "postulate",
      ],
      # All proofs must be complete (no Admitted/sorry)
      admitted_count_max = 0,
    },

    # Multi-prover support requirements
    supported_provers = [
      "coq",
      "lean4",
      "idris2",
      "agda",
    ],

    # Safety invariants
    safety = {
      forbidden_patterns = [
        "unwrap()",
        "expect()",
        "todo!()",
        "unimplemented!()",
      ],
    },

    # Test requirements
    tests = {
      min_unit_tests = 50,
      integration_tests_required = true,
      proof_verification_required = true,
    },

    # Build configuration
    build = {
      edition = "2021",
      msrv = "1.75",
    },

    # Language policy
    banned_files = ["Makefile", "Dockerfile"],
    banned_languages = ["python", "typescript", "javascript", "go"],
  },

  # RSR compliance
  rsr = {
    explainme = true,
    ai_manifest = true,
    machine_readable = true,
    spdx_headers_required = true,
    security_md_required = true,
    idris2_abi = true,
    zig_ffi = true,
  },
}
