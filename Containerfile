# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2024-2025 Jonathan D.A. Jewell <jonathan.jewell@open.ac.uk>
#
# ECHIDNA Container Build Redirect
#
# The canonical Containerfiles are in .containerization/:
#   .containerization/Containerfile       - Minimal (Z3, CVC5, Lean, Idris2)
#   .containerization/Containerfile.full  - All Tier 1-4 provers + Julia
#
# Build with:
#   podman build -f .containerization/Containerfile -t echidna:latest .
#   podman build -f .containerization/Containerfile.full -t echidna:full .
#
# Seal:  selur seal echidna:latest
# Sign:  cerro-torre sign echidna:latest
#
# Or use:
#   just container-build
#   just container-build-full
#
# This file exists for compatibility with tools that expect a root Containerfile.
# It builds the minimal image using chainguard base images.

# =============================================================================
# Stage 1: Rust Builder
# =============================================================================
FROM cgr.dev/chainguard/wolfi-base:latest AS rust-builder

RUN apk add --no-cache \
    rust \
    cargo \
    build-base \
    pkgconf \
    openssl-dev

WORKDIR /build

COPY Cargo.toml Cargo.lock ./
COPY src/rust ./src/rust
COPY src/interfaces ./src/interfaces

RUN cargo build --release --bin echidna

# =============================================================================
# Stage 2: Idris2 Builder
# =============================================================================
FROM cgr.dev/chainguard/wolfi-base:latest AS idris2-builder

RUN apk add --no-cache \
    curl \
    ca-certificates \
    tar \
    gzip \
    gmp-dev

WORKDIR /build

RUN curl -fsSL "https://github.com/idris-lang/Idris2/releases/download/v0.8.0/Idris2-0.8.0-Linux-x86_64.tar.gz" \
    -o /tmp/idris2.tar.gz && \
    mkdir -p /opt/idris2 && \
    tar -xzf /tmp/idris2.tar.gz -C /opt/idris2 --strip-components=1 && \
    rm /tmp/idris2.tar.gz

COPY src/idris /build/idris
RUN export PATH="/opt/idris2/bin:$PATH" && \
    export IDRIS2_PREFIX="/opt/idris2" && \
    cd /build/idris && \
    idris2 --build echidna-validator.ipkg || true

# =============================================================================
# Stage 3: Prover Installer
# =============================================================================
FROM cgr.dev/chainguard/wolfi-base:latest AS prover-installer

RUN apk add --no-cache \
    z3 \
    curl \
    ca-certificates

RUN curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | \
    sh -s -- -y --default-toolchain stable && \
    . "$HOME/.elan/env" && \
    lean --version

# =============================================================================
# Stage 4: Runtime Image (chainguard)
# =============================================================================
FROM cgr.dev/chainguard/wolfi-base:latest

LABEL maintainer="Jonathan D.A. Jewell <jonathan.jewell@open.ac.uk>"
LABEL org.opencontainers.image.source="https://github.com/hyperpolymath/echidna"
LABEL org.opencontainers.image.description="ECHIDNA - Extensible Cognitive Hybrid Intelligence for Deductive Neural Assistance"
LABEL org.opencontainers.image.licenses="PMPL-1.0-or-later"
LABEL org.opencontainers.image.version="1.5.0"
LABEL org.opencontainers.image.vendor="hyperpolymath"

RUN apk add --no-cache \
    ca-certificates \
    libssl3 \
    gmp \
    z3

WORKDIR /app

COPY --from=rust-builder /build/target/release/echidna /app/bin/echidna
COPY --from=idris2-builder /opt/idris2 /opt/idris2
COPY --from=idris2-builder /build/idris/build/exec/echidna-validator /app/bin/echidna-validator
COPY --from=prover-installer /root/.elan /opt/elan

ENV PATH="/app/bin:/opt/idris2/bin:/opt/elan/toolchains/stable/bin:${PATH}"
ENV IDRIS2_PREFIX="/opt/idris2"
ENV ECHIDNA_PROVER_PATH="/opt"

RUN mkdir -p /app/proofs /app/config /app/logs

EXPOSE 8080

HEALTHCHECK --interval=30s --timeout=10s --start-period=5s --retries=3 \
    CMD ["/app/bin/echidna", "--version"]

ENTRYPOINT ["/app/bin/echidna"]
CMD ["--help"]
