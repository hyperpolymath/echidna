# SPDX-License-Identifier: PMPL-1.0-or-later
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
FROM cgr.dev/chainguard/wolfi-base:latest AS rust-builder

RUN apk add --no-cache \
    rust \
    build-base \
    pkgconf \
    openssl-dev

WORKDIR /build

COPY Cargo.toml Cargo.lock ./
COPY src/rust ./src/rust
COPY src/interfaces ./src/interfaces

RUN cargo build --release --bin echidna

# =============================================================================
# Stage 2: Prover Installer (Z3 from official release, Lean via elan)
# =============================================================================
FROM cgr.dev/chainguard/wolfi-base:latest AS prover-installer

RUN apk add --no-cache \
    curl \
    ca-certificates \
    gzip \
    unzip \
    bash

WORKDIR /tmp

# Install Z3 from official GitHub release
RUN curl -fsSL "https://github.com/Z3Prover/z3/releases/download/z3-4.13.4/z3-4.13.4-x64-glibc-2.35.zip" \
    -o z3.zip && \
    unzip -q z3.zip && \
    mkdir -p /opt/z3/bin && \
    cp z3-4.13.4-x64-glibc-2.35/bin/z3 /opt/z3/bin/ && \
    chmod +x /opt/z3/bin/z3 && \
    rm -rf z3.zip z3-4.13.4-x64-glibc-2.35

# Install Lean 4 via elan
RUN curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | \
    bash -s -- -y --default-toolchain stable && \
    . "$HOME/.elan/env" && \
    lean --version

# =============================================================================
# Stage 3: Runtime Image (chainguard)
# =============================================================================
FROM cgr.dev/chainguard/wolfi-base:latest

LABEL maintainer="Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>"
LABEL org.opencontainers.image.source="https://github.com/hyperpolymath/echidna"
LABEL org.opencontainers.image.description="ECHIDNA - Extensible Cognitive Hybrid Intelligence for Deductive Neural Assistance"
LABEL org.opencontainers.image.licenses="PMPL-1.0-or-later"
LABEL org.opencontainers.image.version="1.5.0"
LABEL org.opencontainers.image.vendor="hyperpolymath"

RUN apk add --no-cache \
    ca-certificates \
    libssl3 \
    gmp \
    libstdc++

WORKDIR /app

COPY --from=rust-builder /build/target/release/echidna /app/bin/echidna
COPY --from=prover-installer /opt/z3/bin/z3 /app/bin/z3
COPY --from=prover-installer /root/.elan /opt/elan

ENV PATH="/app/bin:/opt/elan/toolchains/stable/bin:${PATH}"
ENV ECHIDNA_PROVER_PATH="/opt"

RUN mkdir -p /app/proofs /app/config /app/logs

EXPOSE 8081

HEALTHCHECK --interval=30s --timeout=10s --start-period=5s --retries=3 \
    CMD ["/app/bin/echidna", "--version"]

ENTRYPOINT ["/app/bin/echidna"]
CMD ["--help"]
