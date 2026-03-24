# SPDX-License-Identifier: PMPL-1.0-or-later
# deploy.k9.ncl — ECHIDNA deployment component (Hunt level)

let component_pedigree = {
  metadata = {
    name = "echidna-deploy",
    version = "1.5.0",
    breed = "application/vnd.k9+nickel",
    magic_number = "K9!",
    description = "ECHIDNA deployment component (Hunt level)",
  },
  target = {
    os = 'Linux,
    is_edge = false,
    requires_podman = true,
    min_memory_mb = 512,
  },
  security = {
    trust_level = 'Hunt,
    allow_network = true,
    allow_filesystem_write = true,
    allow_subprocess = true,
    signature = "PLACEHOLDER-SIGNATURE-REQUIRED-FOR-HUNT",
  },
  validation = {
    checksum = "sha256:placeholder",
    pedigree_version = "1.0.0",
    hunt_authorized = false,
  },
  recipes = {
    install = "just container-build",
    validate = "just container-verify",
    deploy = "just container-up",
    migrate = "just container-build && just container-up",
  },
} in

let deployment = {
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
    health_check = "/health",
    readiness_check = "/ready",
  },
  strategy = {
    type = "rolling",
    max_surge = 1,
    max_unavailable = 0,
  },
} in

let scripts = {
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
} in

{
  pedigree = component_pedigree,
  deployment = deployment,
  scripts = scripts,
  required_level = 'Hunt,
}
