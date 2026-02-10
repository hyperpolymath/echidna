# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell <jonathan.jewell@open.ac.uk>
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

        # Runtime prover dependencies
        proverDeps = with pkgs; [
          z3
          cvc5
          idris2
        ];

      in {
        # Development shell
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
              "8080/tcp" = {};
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
