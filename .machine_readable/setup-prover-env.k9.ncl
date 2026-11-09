K9!
# SPDX-License-Identifier: MPL-2.0
# setup-prover-env.k9.ncl — ECHIDNA prover environment setup (Hunt level)
#
# K9 contract v1.0.0 (D173). This component provisions theorem provers
# through the repository's two sanctioned paths only:
#
#   1. Guix (PRIMARY): manifests/live-provers.scm. That manifest records
#      which provers Guix packages and which it does not; it is the
#      authority, not this file.
#   2. The sealed-container escape hatch for the not-in-Guix tail:
#      .containerization/Containerfile.wave3, built by `just
#      container-build-tier3`.
#
# It replaces an earlier version that was not valid Nickel (top-level
# bindings without an enclosing record), named a fixed list of 12 provers
# (docs/PROVER_COUNT.adoc is the only count), installed through sudo
# apt/dnf, cabal and opam, piped an unpinned elan install script from
# `master` into `sh`, and carried the string
# "PLACEHOLDER-SIGNATURE-REQUIRED-FOR-HUNT" where a signature belongs.
#
# WARNING: this component executes shell commands. It is 'Hunt, so a host
# runs it only with all five Hunt preconditions met, a verified signature
# among them. The signature block below is a claim until the owner signs this
# file; until then the validator reports it 'Present_Unverified (K9-C001) and
# Hunt stays unauthorised.
#
# Usage:
#   k9-validate.sh --strict --layer L2 .machine_readable/setup-prover-env.k9.ncl
#   k9-svc run .machine_readable/setup-prover-env.k9.ncl install-all

{
  pedigree = {
    schema_version = "1.0.0",
    component_type = "prover-env-setup",

    metadata = {
      name = "setup-prover-env",
      version = "2.0.0",
      description = "Provision ECHIDNA's live theorem provers through the Guix manifest and the Wave-3 sealed containers",
      author = "Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>",
    },

    security = {
      leash = 'Hunt,
      trust_level = "controlled-execution",
      allow_network = true,
      allow_filesystem_write = true,
      allow_subprocess = true,
      signature_required = true,
      # Default-deny: every flag above is paid for here (contract §8.4).
      capabilities = [
        "net.fetch",
        "fs.write",
        "process.spawn",
        "container.run",
      ],
    },

    warnings = [
      "This is a Hunt-level component: it executes shell commands and changes the system.",
      "Guix resolving a package does not show that the prover runs or that any proof passes.",
      "A signature block being present is not a signature being verified.",
    ],

    side_effects = [
      "runs `guix package -m manifests/live-provers.scm`, which fetches substitutes or sources and writes the Guix store and the user's default profile",
      "runs `just container-build-tier3`, which builds the Tier-3 prover images from .containerization/Containerfile.wave3 with podman and fetches their base images",
      "runs `just doctor`, which only reads the toolchain",
    ],

    # Ed25519, presence only (K9-S009). The signing step adds payload_hash
    # and signature; verification is K9-C001 (L3).
    signature = {
      algorithm = "Ed25519",
      key_id = "primary",
    },
  },

  config = {
    # Which sanctioned path(s) to run.
    use_guix = true,
    use_sealed_containers = false,   # heavier; builds every Tier-3 image
    run_doctor = true,
  },

  # Recipes are an execution surface, which is why the leash is 'Hunt
  # (K9-S011). Each delegates to a pinned, repository-owned surface; none
  # downloads anything itself.
  recipes = {
    check-prerequisites = {
      description = "Confirm the tools the sanctioned paths need are present",
      commands = [
        "command -v just >/dev/null 2>&1 || { echo 'just not found'; exit 1; }",
        "command -v guix >/dev/null 2>&1 || echo 'guix not found: the Guix path will be skipped'",
        "command -v podman >/dev/null 2>&1 || echo 'podman not found: the sealed-container path will be skipped'",
      ],
    },
    install-guix = {
      description = "Install the Guix-packaged provers listed in manifests/live-provers.scm",
      dependencies = ["check-prerequisites"],
      commands = ["guix package -m manifests/live-provers.scm"],
    },
    install-containers = {
      description = "Build the non-proprietary Tier-3 sealed prover containers",
      dependencies = ["check-prerequisites"],
      commands = ["just container-build-tier3"],
    },
    doctor = {
      description = "Report which tools are present (read-only)",
      commands = ["just doctor"],
    },
    install-all = {
      description = "Run every enabled path, then report",
      dependencies = ["check-prerequisites", "install-guix", "doctor"],
      commands = ["echo 'Sealed containers are built separately: run the install-containers recipe.'"],
    },
  },
}
