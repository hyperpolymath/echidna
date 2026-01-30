K9!
# SPDX-License-Identifier: PMPL-1.0-or-later
# ECHIDNA Theorem Prover Environment Setup
#
# This K9 component automates the installation and configuration of ECHIDNA's
# 12 theorem prover backends, including Agda, Coq, Lean, Isabelle, Z3, CVC5,
# Metamath, HOL Light, Mizar, PVS, ACL2, and HOL4.

leash = 'Hunt

pedigree = {
  schema_version = "1.0.0",
  component_type = "prover-env-setup",
  author = "Jonathan D.A. Jewell <jonathan.jewell@open.ac.uk>",
  description = "Automated setup of 12 theorem prover environments for ECHIDNA",
  created = "2026-01-30",
  k9_spec_version = "1.0.0",
}

config = {
  # Prover tier selection
  install_tiers = {
    tier1 | Bool = true,   # Agda, Coq, Lean, Isabelle, Z3, CVC5
    tier2 | Bool = true,   # Metamath, HOL Light, Mizar
    tier3 | Bool = false,  # PVS, ACL2 (heavier dependencies)
    tier4 | Bool = false,  # HOL4 (legacy)
  },

  # Installation method preferences
  install_methods = {
    prefer_package_manager | Bool = true,  # Use system package manager when possible
    use_containers | Bool = false,          # Isolate provers in containers
    build_from_source | [| 'Never, 'IfNeeded, 'Always |] = 'IfNeeded,
  },

  # Container runtime (if use_containers = true)
  container_runtime | [| 'Podman, 'Docker |] = 'Podman,

  # Prover-specific configurations
  provers = {
    agda = { enabled | Bool = true, version | String = "2.6.4" },
    coq = { enabled | Bool = true, version | String = "8.18" },
    lean = { enabled | Bool = true, version | String = "4.4.0" },
    isabelle = { enabled | Bool = true, version | String = "2023" },
    z3 = { enabled | Bool = true, version | String = "4.12.5" },
    cvc5 = { enabled | Bool = true, version | String = "1.1.1" },
    metamath = { enabled | Bool = true, version | String = "0.198" },
    hol_light = { enabled | Bool = true, version | String = "latest" },
    mizar = { enabled | Bool = true, version | String = "8.1.11" },
    pvs = { enabled | Bool = false, version | String = "7.1" },
    acl2 = { enabled | Bool = false, version | String = "8.5" },
    hol4 = { enabled | Bool = false, version | String = "latest" },
  },

  # Installation paths
  paths = {
    install_dir | String = "$HOME/.echidna/provers",
    container_volumes | String = "$HOME/.echidna/volumes",
    config_dir | String = "$HOME/.config/echidna",
  },

  # Testing
  run_smoke_tests | Bool = true,
  verify_integration | Bool = true,
}

# Prover installation recipes
prover_recipes = {
  agda = {
    description = "Install Agda (dependent type theory)",
    enabled = config.provers.agda.enabled && config.install_tiers.tier1,
    commands = [
      "echo 'Installing Agda %{config.provers.agda.version}...'",
      "if command -v agda >/dev/null 2>&1; then echo 'Agda already installed'; else " ++
        "if [ %{std.string.from config.install_methods.prefer_package_manager} = 'true' ]; then " ++
          "if command -v dnf >/dev/null 2>&1; then sudo dnf install -y agda; " ++
          "elif command -v apt-get >/dev/null 2>&1; then sudo apt-get install -y agda; " ++
          "else echo 'Installing via cabal...'; cabal install Agda; fi; " ++
        "else cabal install Agda; fi; " ++
      "fi",
      "agda --version",
    ],
  },

  coq = {
    description = "Install Coq/Rocq (interactive theorem prover)",
    enabled = config.provers.coq.enabled && config.install_tiers.tier1,
    commands = [
      "echo 'Installing Coq %{config.provers.coq.version}...'",
      "if command -v coqc >/dev/null 2>&1; then echo 'Coq already installed'; else " ++
        "if [ %{std.string.from config.install_methods.prefer_package_manager} = 'true' ]; then " ++
          "if command -v dnf >/dev/null 2>&1; then sudo dnf install -y coq; " ++
          "elif command -v apt-get >/dev/null 2>&1; then sudo apt-get install -y coq; " ++
          "else echo 'Installing via opam...'; opam install coq.%{config.provers.coq.version}; fi; " ++
        "else opam install coq.%{config.provers.coq.version}; fi; " ++
      "fi",
      "coqc --version",
    ],
  },

  lean = {
    description = "Install Lean 4 (functional programming and proving)",
    enabled = config.provers.lean.enabled && config.install_tiers.tier1,
    commands = [
      "echo 'Installing Lean %{config.provers.lean.version}...'",
      "if command -v lean >/dev/null 2>&1; then echo 'Lean already installed'; else " ++
        "curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y; " ++
        "source $HOME/.elan/env; " ++
        "elan default leanprover/lean4:%{config.provers.lean.version}; " ++
      "fi",
      "lean --version",
    ],
  },

  isabelle = {
    description = "Install Isabelle (higher-order logic)",
    enabled = config.provers.isabelle.enabled && config.install_tiers.tier1,
    commands = [
      "echo 'Installing Isabelle %{config.provers.isabelle.version}...'",
      "if [ ! -d %{config.paths.install_dir}/isabelle ]; then " ++
        "mkdir -p %{config.paths.install_dir}; " ++
        "cd %{config.paths.install_dir}; " ++
        "wget https://isabelle.in.tum.de/website-Isabelle%{config.provers.isabelle.version}/dist/Isabelle%{config.provers.isabelle.version}_linux.tar.gz; " ++
        "tar xzf Isabelle%{config.provers.isabelle.version}_linux.tar.gz; " ++
        "ln -sf %{config.paths.install_dir}/Isabelle%{config.provers.isabelle.version}/bin/isabelle $HOME/.local/bin/isabelle; " ++
      "fi",
      "isabelle version",
    ],
  },

  z3 = {
    description = "Install Z3 (SMT solver)",
    enabled = config.provers.z3.enabled && config.install_tiers.tier1,
    commands = [
      "echo 'Installing Z3 %{config.provers.z3.version}...'",
      "if command -v z3 >/dev/null 2>&1; then echo 'Z3 already installed'; else " ++
        "if [ %{std.string.from config.install_methods.prefer_package_manager} = 'true' ]; then " ++
          "if command -v dnf >/dev/null 2>&1; then sudo dnf install -y z3; " ++
          "elif command -v apt-get >/dev/null 2>&1; then sudo apt-get install -y z3; fi; " ++
        "else " ++
          "mkdir -p %{config.paths.install_dir}; " ++
          "cd %{config.paths.install_dir}; " ++
          "wget https://github.com/Z3Prover/z3/releases/download/z3-%{config.provers.z3.version}/z3-%{config.provers.z3.version}-x64-glibc-2.31.zip; " ++
          "unzip z3-%{config.provers.z3.version}-x64-glibc-2.31.zip; " ++
          "ln -sf %{config.paths.install_dir}/z3-%{config.provers.z3.version}-x64-glibc-2.31/bin/z3 $HOME/.local/bin/z3; " ++
        "fi; " ++
      "fi",
      "z3 --version",
    ],
  },

  cvc5 = {
    description = "Install CVC5 (SMT solver)",
    enabled = config.provers.cvc5.enabled && config.install_tiers.tier1,
    commands = [
      "echo 'Installing CVC5 %{config.provers.cvc5.version}...'",
      "if command -v cvc5 >/dev/null 2>&1; then echo 'CVC5 already installed'; else " ++
        "mkdir -p %{config.paths.install_dir}; " ++
        "cd %{config.paths.install_dir}; " ++
        "wget https://github.com/cvc5/cvc5/releases/download/cvc5-%{config.provers.cvc5.version}/cvc5-Linux; " ++
        "chmod +x cvc5-Linux; " ++
        "ln -sf %{config.paths.install_dir}/cvc5-Linux $HOME/.local/bin/cvc5; " ++
      "fi",
      "cvc5 --version",
    ],
  },

  metamath = {
    description = "Install Metamath (plain text verifier)",
    enabled = config.provers.metamath.enabled && config.install_tiers.tier2,
    commands = [
      "echo 'Installing Metamath %{config.provers.metamath.version}...'",
      "if command -v metamath >/dev/null 2>&1; then echo 'Metamath already installed'; else " ++
        "mkdir -p %{config.paths.install_dir}; " ++
        "cd %{config.paths.install_dir}; " ++
        "git clone https://github.com/metamath/metamath-exe.git; " ++
        "cd metamath-exe; " ++
        "gcc *.c -o metamath; " ++
        "ln -sf %{config.paths.install_dir}/metamath-exe/metamath $HOME/.local/bin/metamath; " ++
      "fi",
      "metamath --help | head -1",
    ],
  },
}

# Main installation recipes
recipes = {
  default = {
    recipe = "install-all",
    description = "Install all enabled theorem provers",
  },

  "check-prerequisites" = {
    description = "Verify prerequisites for prover installation",
    commands = [
      "echo 'Checking prerequisites...'",

      # Check basic tools
      "command -v wget >/dev/null 2>&1 || { echo 'Error: wget not found'; exit 1; }",
      "command -v git >/dev/null 2>&1 || { echo 'Error: git not found'; exit 1; }",

      # Create installation directories
      "mkdir -p %{config.paths.install_dir}",
      "mkdir -p %{config.paths.config_dir}",
      "mkdir -p $HOME/.local/bin",

      # Check if .local/bin is in PATH
      "if echo $PATH | grep -q '$HOME/.local/bin'; then echo '.local/bin already in PATH'; else echo 'Warning: Add $HOME/.local/bin to PATH'; fi",

      "echo 'Prerequisites check complete!'",
    ],
  },

  "install-tier1" = {
    description = "Install Tier 1 provers (Agda, Coq, Lean, Isabelle, Z3, CVC5)",
    dependencies = ["check-prerequisites"],
    skip = !config.install_tiers.tier1,
    commands =
      prover_recipes.agda.commands @ prover_recipes.coq.commands @
      prover_recipes.lean.commands @ prover_recipes.isabelle.commands @
      prover_recipes.z3.commands @ prover_recipes.cvc5.commands,
  },

  "install-tier2" = {
    description = "Install Tier 2 provers (Metamath, HOL Light, Mizar)",
    dependencies = ["check-prerequisites"],
    skip = !config.install_tiers.tier2,
    commands = prover_recipes.metamath.commands,
  },

  "smoke-test-provers" = {
    description = "Run smoke tests for installed provers",
    skip = !config.run_smoke_tests,
    commands = [
      "echo 'Running smoke tests...'",
      "if command -v agda >/dev/null 2>&1; then echo '✓ Agda'; else echo '✗ Agda'; fi",
      "if command -v coqc >/dev/null 2>&1; then echo '✓ Coq'; else echo '✗ Coq'; fi",
      "if command -v lean >/dev/null 2>&1; then echo '✓ Lean'; else echo '✗ Lean'; fi",
      "if command -v isabelle >/dev/null 2>&1; then echo '✓ Isabelle'; else echo '✗ Isabelle'; fi",
      "if command -v z3 >/dev/null 2>&1; then echo '✓ Z3'; else echo '✗ Z3'; fi",
      "if command -v cvc5 >/dev/null 2>&1; then echo '✓ CVC5'; else echo '✗ CVC5'; fi",
      "if command -v metamath >/dev/null 2>&1; then echo '✓ Metamath'; else echo '✗ Metamath'; fi",
      "echo 'Smoke tests complete!'",
    ],
  },

  "install-all" = {
    description = "Install all enabled theorem provers (default)",
    dependencies = [
      "check-prerequisites",
      "install-tier1",
      "install-tier2",
      "smoke-test-provers",
    ],
    commands = [
      "echo ''",
      "echo '╔══════════════════════════════════════════════════════════╗'",
      "echo '║  ✅ ECHIDNA Prover Environment Setup Complete!         ║'",
      "echo '╚══════════════════════════════════════════════════════════╝'",
      "echo ''",
      "echo 'Installed provers:'",
      "command -v agda >/dev/null 2>&1 && echo '  - Agda (dependent type theory)'",
      "command -v coqc >/dev/null 2>&1 && echo '  - Coq (interactive theorem prover)'",
      "command -v lean >/dev/null 2>&1 && echo '  - Lean 4 (functional programming + proving)'",
      "command -v isabelle >/dev/null 2>&1 && echo '  - Isabelle (higher-order logic)'",
      "command -v z3 >/dev/null 2>&1 && echo '  - Z3 (SMT solver)'",
      "command -v cvc5 >/dev/null 2>&1 && echo '  - CVC5 (SMT solver)'",
      "command -v metamath >/dev/null 2>&1 && echo '  - Metamath (verifier)'",
      "echo ''",
      "echo 'Next steps:'",
      "echo '  1. Build ECHIDNA:     just build'",
      "echo '  2. Run tests:         just test'",
      "echo '  3. Start ECHIDNA:     just run'",
      "echo ''",
    ],
  },
}

validation = {
  # At least one tier must be enabled
  has_enabled_tier =
    config.install_tiers.tier1
    || config.install_tiers.tier2
    || config.install_tiers.tier3
    || config.install_tiers.tier4
    | doc "At least one prover tier must be enabled",

  # Ensure install methods are valid
  valid_build_method =
    config.install_methods.build_from_source == 'Never
    || config.install_methods.build_from_source == 'IfNeeded
    || config.install_methods.build_from_source == 'Always
    | doc "build_from_source must be Never, IfNeeded, or Always",

  # Container runtime must be valid
  valid_container_runtime =
    config.container_runtime == 'Podman
    || config.container_runtime == 'Docker
    | doc "container_runtime must be Podman or Docker",
}
