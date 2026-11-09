K9!
# SPDX-License-Identifier: MPL-2.0
# deploy.k9.ncl — ECHIDNA deployment component (Hunt level)
#
# k9-svc deployment component, K9 contract v1.0.0 (D173). The structure
# follows rsr-template-repo build/container/stapeln/deploy.k9.ncl.in, with
# ECHIDNA's own values filled in.
#
# WARNING: this component executes shell commands. It is 'Hunt, so a host
# runs it only with all five Hunt preconditions met, a verified signature
# among them. The signature block below is a claim until the owner signs this
# file; until then the validator reports it 'Present_Unverified (K9-C001) and
# Hunt stays unauthorised. (This replaces the earlier
# "PLACEHOLDER-SIGNATURE-REQUIRED-FOR-HUNT" string and "sha256:placeholder"
# checksum, which looked like values but were not.)
#
# Usage:
#   k9-validate.sh --strict --layer L2 container/deploy.k9.ncl
#   k9-svc validate container/deploy.k9.ncl
#   k9-svc deploy container/deploy.k9.ncl --env production

{
  pedigree = {
    schema_version = "1.0.0",
    component_type = "deployment",

    metadata = {
      name = "echidna-deploy",
      version = "1.5.0",
      description = "ECHIDNA deployment component (Hunt level)",
    },

    # Target environment (extension field; contract §5.5).
    target = {
      os = 'Linux,
      is_edge = false,
      requires_podman = true,
      min_memory_mb = 512,
    },

    security = {
      leash = 'Hunt,
      trust_level = "controlled-execution",
      allow_network = true,
      allow_filesystem_write = true,
      allow_subprocess = true,
      signature_required = true,
      # Default-deny: every flag above is paid for here (contract §8.4), plus
      # the deploy and rollback actions the scripts below perform.
      capabilities = [
        "net.fetch",
        "fs.write",
        "process.spawn",
        "container.run",
        "deploy.apply",
        "rollback.apply",
      ],
    },

    warnings = [
      "This is a Hunt-level component: it executes shell commands and changes the system.",
      "Review the deployment scripts before running it.",
      "A signature block being present is not a signature being verified.",
      "Authorise Hunt explicitly: k9-svc authorize container/deploy.k9.ncl",
    ],

    side_effects = [
      "spawns container/ct-build.sh, which builds the image",
      "pulls and pushes ghcr.io/hyperpolymath/echidna images",
      "starts, updates and stops the echidna stack with selur-compose, else podman compose over container/compose.toml",
      "publishes the service on port 8081",
    ],

    # Ed25519, presence only (K9-S009). The signing step adds payload_hash
    # and signature; verification is K9-C001 (L3).
    signature = {
      algorithm = "Ed25519",
      key_id = "primary",
    },
  },

  # Deployment configuration
  deployment = {
    environments = {
      dev = {
        replicas = 1,
        memory = "256Mi",
        cpu = "100m",
        image_tag = "dev",
      },
      staging = {
        replicas = 2,
        memory = "512Mi",
        cpu = "250m",
        image_tag = "staging",
      },
      production = {
        replicas = 3,
        memory = "1Gi",
        cpu = "500m",
        image_tag = "latest",
      },
    },

    container = {
      image = "ghcr.io/hyperpolymath/echidna",
      port = 8081,
      # Process-level readiness only: /api/health reports that this HTTP process
      # responds. It does not check dispatcher, solver or dependent-service
      # readiness. Consumers that gate traffic on those dependencies need their
      # own checks; this probe cannot establish that stronger contract.
      health_check = "/api/health",
      readiness_check = "/api/health",
    },

    strategy = {
      type = "rolling",
      max_surge = 1,
      max_unavailable = 0,
    },
  },

  # Deployment scripts (executed at Hunt level)
  scripts = {
    pre_deploy = m%"
#!/bin/sh
set -eu
echo "K9: Pre-deployment validation for echidna..."
cd container && selur-compose verify || podman compose --file compose.toml config
echo "K9: Validation passed."
"%,

    deploy = m%"
#!/bin/sh
set -eu
ENV="${1:-dev}"
echo "K9: Deploying echidna to $ENV environment..."
cd container
./ct-build.sh
selur-compose up --detach || podman compose --file compose.toml up --detach
echo "K9: Deployment to $ENV complete."
"%,

    rollback = m%"
#!/bin/sh
set -eu
echo "K9: Rolling back echidna deployment..."
cd container
selur-compose down || podman compose --file compose.toml down
echo "K9: Rollback complete."
"%,
  },

  # Just recipes: an execution surface, which is why the leash is 'Hunt
  # (K9-S011).
  recipes = {
    install = {
      description = "Build the container image",
      commands = ["just container-build"],
    },
    validate = {
      description = "Verify the compose configuration",
      commands = ["just container-verify"],
    },
    deploy = {
      description = "Start the container stack",
      commands = ["just container-up"],
    },
    migrate = {
      description = "Rebuild the image and restart the stack",
      commands = ["just container-build", "just container-up"],
    },
  },
}
