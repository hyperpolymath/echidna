# SPDX-License-Identifier: PMPL-1.0
# Build stage
FROM docker.io/library/rust:1.83-slim AS builder

WORKDIR /build

# Install build dependencies
RUN apt-get update && apt-get install -y --no-install-recommends \
    pkg-config \
    libsqlite3-dev \
    && rm -rf /var/lib/apt/lists/*

# Copy source
COPY . .

# Build release binary
RUN cargo build --release

# Runtime stage
FROM cgr.dev/chainguard/wolfi-base:latest

LABEL org.opencontainers.image.source="https://github.com/hyperpolymath/echidnabot"
LABEL org.opencontainers.image.description="Proof-aware CI bot that orchestrates ECHIDNA for theorem proof verification"
LABEL org.opencontainers.image.licenses="PMPL-1.0-or-later"

# Install runtime dependencies
RUN apk add --no-cache sqlite-libs ca-certificates

# Copy binary from builder
COPY --from=builder /build/target/release/echidnabot /usr/local/bin/echidnabot

# Create non-root user
RUN adduser -D -u 1000 echidna
USER echidna

WORKDIR /home/echidna

EXPOSE 8080

ENTRYPOINT ["/usr/local/bin/echidnabot"]
