# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2024-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# ECHIDNA Minimal Container Image
#
# Includes: echidna binary + Z3 + Lean 4
# For all provers + Julia ML: use .containerization/Containerfile.full
#
# Build:  podman build -f Containerfile -t echidna:latest .
# Run:    podman run --rm echidna:latest --version
# Or:     just container-build

# =============================================================================
# Stage 1: Rust Builder
# =============================================================================
FROM cgr.dev/chainguard/wolfi-base@sha256:9c2092b053779e14c82fb50f77b37bcc38b7d2c83972352d5813280f9d035b03 AS rust-builder

RUN apk add --no-cache \
    rust \
    build-base \
    pkgconf \
    openssl-dev

WORKDIR /build

COPY Cargo.toml Cargo.lock ./
COPY src/rust ./src/rust
COPY src/interfaces ./src/interfaces
# The root `echidna` package is a Cargo workspace whose members include
# crates/* (echidna-core, -core-spark, -mcp, -wire, typed_wasm). Cargo
# loads every member manifest when building the bin, so the crates/ tree
# must be in the build context too — omitting it fails the build with
# `failed to read /build/crates/echidna-core/Cargo.toml`.
COPY crates ./crates
# Root Cargo.toml declares explicit [[bench]] targets (proof_benchmarks,
# routing_benchmarks at benches/*.rs). Cargo validates every declared
# target when it parses the manifest — even for `--bin echidna` — so the
# benches/ sources must exist in the build context or parse fails with
# `can't find 'proof_benchmarks' bench`. (tests/ and examples/ are
# auto-discovered and tolerate absence, so they are intentionally not copied.)
COPY benches ./benches

# Keep the output binary, then remove compilation intermediates in this same
# layer. Committing the full target tree exhausts small hosted build runners.
RUN cargo build --locked --release --bin echidna && \
    install -D -m 0755 target/release/echidna /out/echidna && \
    cargo clean

# =============================================================================
# Stage 2: Prover Installer (Z3 from official release, Lean via elan)
# =============================================================================
FROM cgr.dev/chainguard/wolfi-base@sha256:9c2092b053779e14c82fb50f77b37bcc38b7d2c83972352d5813280f9d035b03 AS prover-installer

RUN apk add --no-cache \
    curl \
    ca-certificates \
    gzip \
    unzip \
    bash

WORKDIR /tmp

# Install Z3 from official GitHub release
RUN curl --proto '=https' --proto-redir '=https' -fsSL --connect-timeout 20 --max-time 180 --retry 3 \
    "https://github.com/Z3Prover/z3/releases/download/z3-4.13.4/z3-4.13.4-x64-glibc-2.35.zip" -o z3.zip && \
    echo '93f91f9c6f4a00a041c19fc7a74adc1f441c8244ce70d486e19abcd89c6a014b  z3.zip' | sha256sum -c - && \
    unzip -q z3.zip && \
    mkdir -p /opt/z3/bin && \
    cp z3-4.13.4-x64-glibc-2.35/bin/z3 /opt/z3/bin/ && \
    chmod +x /opt/z3/bin/z3 && \
    rm -rf z3.zip z3-4.13.4-x64-glibc-2.35

# Use the same verified installer and pinned Lean version as the live gate.
COPY scripts/ci/install-lean.sh /tmp/install-lean.sh
RUN ELAN_HOME=/opt/elan bash /tmp/install-lean.sh

# =============================================================================
# Stage 3: Runtime Image (chainguard)
# =============================================================================
FROM cgr.dev/chainguard/wolfi-base@sha256:9c2092b053779e14c82fb50f77b37bcc38b7d2c83972352d5813280f9d035b03

LABEL maintainer="Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>"
LABEL org.opencontainers.image.source="https://github.com/hyperpolymath/echidna"
LABEL org.opencontainers.image.description="ECHIDNA - Extensible Cognitive Hybrid Intelligence for Deductive Neural Assistance"
LABEL org.opencontainers.image.licenses="MPL-2.0"
LABEL org.opencontainers.image.version="1.5.0"
LABEL org.opencontainers.image.vendor="hyperpolymath"

RUN apk add --no-cache \
    ca-certificates \
    libssl3 \
    gmp \
    libstdc++

WORKDIR /app

COPY --from=rust-builder /out/echidna /app/bin/echidna
COPY --from=prover-installer /opt/z3/bin/z3 /app/bin/z3
COPY --from=prover-installer /opt/elan /opt/elan

ENV ELAN_HOME="/opt/elan"
ENV PATH="/app/bin:/opt/elan/bin:${PATH}"
ENV ECHIDNA_PROVER_PATH="/opt"

RUN mkdir -p /app/proofs /app/config /app/logs

EXPOSE 8081

HEALTHCHECK --interval=30s --timeout=10s --start-period=5s --retries=3 \
    CMD ["/app/bin/echidna", "--version"]

ENTRYPOINT ["/app/bin/echidna"]
CMD ["--help"]
