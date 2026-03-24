# SPDX-License-Identifier: PMPL-1.0
# SPDX-FileCopyrightText: 2025 hyperpolymath
{
  description = "ECHIDNABOT - Proof-aware CI bot for theorem verification";

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

        # Build dependencies
        buildDeps = with pkgs; [
          pkg-config
          openssl
          sqlite
          postgresql
        ];

        # Development tools
        devTools = with pkgs; [
          just
          cargo-edit
          cargo-audit
          cargo-outdated
          cargo-tarpaulin
          cargo-deny
          cargo-watch
          cargo-deb
          cargo-generate-rpm
          jq
          sqlx-cli
        ];

      in {
        # Development shell
        devShells.default = pkgs.mkShell {
          buildInputs = [ rustToolchain ] ++ buildDeps ++ devTools;

          shellHook = ''
            export DATABASE_URL="sqlite:./dev.db"
            export RUST_LOG=echidnabot=debug,info
            echo "ECHIDNABOT development environment"
            echo ""
            echo "Commands:"
            echo "  cargo run              - Start the bot"
            echo "  cargo test             - Run tests"
            echo "  sqlx database create   - Create database"
            echo "  sqlx migrate run       - Run migrations"
          '';
        };

        # Main package
        packages.default = pkgs.rustPlatform.buildRustPackage {
          pname = "echidnabot";
          version = "0.1.0";

          src = ./.;
          cargoLock.lockFile = ./Cargo.lock;

          nativeBuildInputs = with pkgs; [ pkg-config ];
          buildInputs = with pkgs; [ openssl sqlite postgresql ];

          # Disable tests that require network/database
          checkPhase = ''
            cargo test --lib
          '';

          meta = with pkgs.lib; {
            description = "Proof-aware CI bot for theorem verification";
            homepage = "https://github.com/hyperpolymath/echidnabot";
            license = licenses.free; # PMPL-1.0-or-later (https://github.com/hyperpolymath/palimpsest-license)
            mainProgram = "echidnabot";
          };
        };

        # SQLite-only variant (minimal deps)
        packages.sqlite = pkgs.rustPlatform.buildRustPackage {
          pname = "echidnabot-sqlite";
          version = "0.1.0";

          src = ./.;
          cargoLock.lockFile = ./Cargo.lock;

          nativeBuildInputs = with pkgs; [ pkg-config ];
          buildInputs = with pkgs; [ openssl sqlite ];

          # Build with SQLite only (default features)
          cargoBuildFlags = [ ];

          meta = with pkgs.lib; {
            description = "ECHIDNABOT with SQLite backend (minimal)";
            homepage = "https://github.com/hyperpolymath/echidnabot";
            license = licenses.free; # PMPL-1.0-or-later (https://github.com/hyperpolymath/palimpsest-license)
            mainProgram = "echidnabot";
          };
        };

        # CI checks
        packages.ci = pkgs.stdenv.mkDerivation {
          name = "echidnabot-ci";
          src = ./.;

          nativeBuildInputs = [ rustToolchain pkgs.pkg-config ];
          buildInputs = with pkgs; [ openssl sqlite ];

          buildPhase = ''
            export HOME=$TMPDIR
            cargo fmt --check
            cargo clippy -- -D warnings
            cargo test --lib
            cargo audit
          '';

          installPhase = ''
            mkdir -p $out
            echo "CI checks passed" > $out/result
          '';
        };

        # Container image (OCI)
        packages.container = pkgs.dockerTools.buildLayeredImage {
          name = "echidnabot";
          tag = "latest";

          contents = [
            self.packages.${system}.default
            pkgs.cacert
          ];

          config = {
            Cmd = [ "/bin/echidnabot" ];
            Env = [
              "RUST_LOG=info"
            ];
            ExposedPorts = {
              "8081/tcp" = {};
            };
          };
        };
      }
    );
}
