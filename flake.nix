# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
{
  description = "ECHIDNA - Neurosymbolic theorem proving platform with 30 prover backends";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, flake-utils, rust-overlay }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        overlays = [ (import rust-overlay) ];
        pkgs = import nixpkgs { inherit system overlays; };

        rustToolchain = pkgs.rust-bin.stable.latest.default.override {
          extensions = [ "rust-src" "rust-analyzer" "clippy" "rustfmt" ];
        };

        buildDeps = with pkgs; [
          pkg-config
          openssl
        ];

        devTools = with pkgs; [
          just
          cargo-edit
          cargo-audit
          cargo-outdated
          cargo-tarpaulin
          cargo-deny
          cargo-watch
          jq
        ];

        # Runtime prover dependencies (minimal — devShell default)
        proverDeps = with pkgs; [
          z3
          cvc5
          idris2
        ];

        # Live-prover CI dependencies — mirror of manifests/live-provers.scm
        # (Guix is PRIMARY per project CLAUDE.md; this flake is the fallback
        # path for contributors without Guix and for cases where nixpkgs has a
        # package Guix upstream doesn't yet — e.g. lean4, dafny.)
        #
        # Tiering mirrors ~/Desktop/ECHIDNA-PRODUCTION-WIRING-PLAN.md.
        liveProverDeps = with pkgs; [
          # --- Tier 1 — trivial (every PR)
          z3                # SMT, deep wiring
          cvc5              # SMT (nixpkgs has cvc5; Guix has cvc4 as stand-in)
          alt-ergo          # SMT
          vampire           # first-order ATP
          eprover           # first-order ATP
          spass             # first-order ATP
          glpk              # LP/MIP constraint solver (glpsol)
          minizinc          # constraint modelling
          chuffed           # CP solver (FlatZinc)
          # --- Tier 2 — build-from-source / larger deps (nightly)
          coq               # Coq/Rocq
          agda              # dependent-type proof assistant
          idris2            # dependent-type proof assistant
          isabelle          # HOL proof assistant
          why3              # auto-active verifier
          lean4             # Lean 4 — NOT in Guix upstream, so this is primary path
          dafny             # Dafny — NOT in Guix (dotnet dep), so this is primary
          # hol-light       # uncomment when nixpkgs attribute stable
          # tlaps           # uncomment when nixpkgs attribute stable
          # fstar           # uncomment when nixpkgs attribute stable
          # --- Harness prerequisites
          which
          coreutils
        ];

      in {
        # Development shell (minimal — for day-to-day work)
        devShells.default = pkgs.mkShell {
          buildInputs = [ rustToolchain ] ++ buildDeps ++ devTools ++ proverDeps;

          shellHook = ''
            export RUST_LOG=echidna=debug,info
            echo "ECHIDNA development environment"
            echo ""
            echo "Commands:"
            echo "  just build       - Build debug"
            echo "  just test        - Run unit tests"
            echo "  just test-all    - Run all tests"
            echo "  just lint        - Run clippy"
            echo "  just pre-commit  - All checks"
          '';
        };

        # Live-prover development shell — mirrors manifests/live-provers.scm.
        # Use when running the live-prover test suite locally without Guix:
        #   nix develop .#live-provers -c cargo test --test live_prover_suite --features live-provers
        devShells.live-provers = pkgs.mkShell {
          buildInputs = [ rustToolchain ] ++ buildDeps ++ devTools ++ liveProverDeps;
          shellHook = ''
            export RUST_LOG=echidna=debug,info
            export ECHIDNA_LIVE_PROVERS=1
            echo "ECHIDNA live-prover environment (Nix fallback; Guix is primary)"
            echo ""
            echo "Run:"
            echo "  cargo test --test live_prover_suite --features live-provers"
          '';
        };

        # Main package
        packages.default = pkgs.rustPlatform.buildRustPackage {
          pname = "echidna";
          version = "1.5.0";

          src = ./.;
          cargoLock.lockFile = ./Cargo.lock;

          nativeBuildInputs = with pkgs; [ pkg-config ];
          buildInputs = with pkgs; [ openssl ];

          # Only run unit tests (integration tests need provers)
          checkPhase = ''
            cargo test --lib
          '';

          meta = with pkgs.lib; {
            description = "Neurosymbolic theorem proving platform with 30 prover backends";
            homepage = "https://github.com/hyperpolymath/echidna";
            license = licenses.free; # PMPL-1.0-or-later (https://github.com/hyperpolymath/palimpsest-license)
            mainProgram = "echidna";
          };
        };

        # Container image (OCI)
        packages.container = pkgs.dockerTools.buildLayeredImage {
          name = "echidna";
          tag = "latest";

          contents = [
            self.packages.${system}.default
            pkgs.cacert
            pkgs.z3
            pkgs.cvc5
            pkgs.idris2
          ];

          config = {
            Cmd = [ "/bin/echidna" "--help" ];
            Env = [
              "RUST_LOG=info"
            ];
            ExposedPorts = {
              "8081/tcp" = {};
            };
          };
        };

        # CI checks
        packages.ci = pkgs.stdenv.mkDerivation {
          name = "echidna-ci";
          src = ./.;

          nativeBuildInputs = [ rustToolchain pkgs.pkg-config ];
          buildInputs = with pkgs; [ openssl ];

          buildPhase = ''
            export HOME=$TMPDIR
            cargo fmt --check
            cargo clippy -- -D warnings
            cargo test --lib
          '';

          installPhase = ''
            mkdir -p $out
            echo "CI checks passed" > $out/result
          '';
        };
      }
    );
}
