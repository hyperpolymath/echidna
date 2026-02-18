K9!
# SPDX-License-Identifier: PMPL-1.0-or-later
# K9 Hunt-level template: Full execution with Just recipes
# Security Level: Hunt (full system access)
# ⚠️ SIGNATURE REQUIRED - Review carefully before use

{
  pedigree = {
    schema_version = "1.0.0",
    component_type = "build-and-deploy",
    security = {
      leash = 'Hunt,
      trust_level = "full-system-access",
      allow_network = true,
      allow_filesystem_write = true,
      allow_subprocess = true,
      signature_required = true,
    },
    metadata = {
      name = "echidna-hunt",
      version = "1.5.0",
      description = "ECHIDNA build, test, and deployment orchestration via K9 hunt-level contractile",
      author = "Jonathan D.A. Jewell <jonathan.jewell@open.ac.uk>",
    },
    warnings = [
      "This component has full system access",
      "Only run from trusted sources with verified signatures",
      "Review all Just recipes before execution",
      "Use dry-run mode first: ./must --dry-run run your-file.k9.ncl",
    ],
    side_effects = [
      "Creates target/release/echidna binary via cargo build",
      "Executes just build, just test, cargo clippy",
      "Network access for cargo dependency resolution",
    ],
  },

  # Configuration with contracts (Yard-level validation)
  config = {
    # Add your configuration here with appropriate contracts
    target_dir
      | String
      | std.string.NonEmpty
      = "/tmp/k9-output",

    dry_run | Bool = false,

    # Add more config as needed
  },

  # Just recipes for execution
  # These run when: ./must run your-file.k9.ncl
  recipes = {
    # Main entry point (runs by default)
    default = {
      recipe = "main-task",
      description = "Build and test ECHIDNA",
    },

    # Define your recipes here
    "main-task" = {
      dependencies = ["check-prerequisites"],
      commands = [
        "just build",
        "just test",
        "echo '✓ ECHIDNA build and test complete'",
      ],
    },

    "check-prerequisites" = {
      description = "Verify required tools and permissions",
      commands = [
        "command -v cargo || (echo 'ERROR: cargo not found' && exit 1)",
        "command -v just || (echo 'ERROR: just not found' && exit 1)",
        "echo '✓ Prerequisites checked'",
      ],
    },

    # Add more recipes as needed
    "build" = {
      description = "Build ECHIDNA release binary",
      commands = [
        "cargo build --release --bin echidna",
      ],
    },

    "deploy" = {
      description = "Build container image and seal",
      dependencies = ["build"],
      commands = [
        "podman build -f .containerization/Containerfile -t echidna:latest .",
        "selur seal echidna:latest",
        "cerro-torre sign echidna:latest",
      ],
    },

    "clean" = {
      description = "Clean up build artefacts",
      commands = [
        "echo '⚠️  This will delete build artefacts - waiting 3 seconds...'",
        "sleep 3",
        "cargo clean",
      ],
    },
  },

  # Validation (Yard-level checks before Hunt execution)
  validation = {
    check_target_dir = std.string.length config.target_dir > 0,
    # Add more validation as needed
  },
}

# Usage:
# 1. Test with dry-run: ./must --dry-run run template-hunt.k9.ncl
# 2. Review dry-run output carefully
# 3. Sign the component: ./must sign template-hunt.k9.ncl
# 4. Distribute with signature: template-hunt.k9.ncl.sig
# 5. Users verify and run: ./must verify && ./must run template-hunt.k9.ncl
#
# Security checklist:
# ✓ All TODO items filled in
# ✓ side_effects documented accurately
# ✓ Commands reviewed for safety
# ✓ No hardcoded secrets or credentials
# ✓ Proper error handling in recipes
# ✓ Tested in dry-run mode
# ✓ Component signed with trusted key
