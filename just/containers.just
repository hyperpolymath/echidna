# SPDX-License-Identifier: MPL-2.0
# Imported by the root Justfile (hotspot split); recipes moved verbatim.

# ── Tier-3 prover containers (Wave-3) ────────────────────────────────────────
# All nine targets live in ONE consolidated multi-target Containerfile.wave3.
# The Rust core is compiled once (shared `rust-builder` stage) and every prover
# image is a `--target`; podman caches the shared stage across builds on a host.

# Build all non-proprietary Tier-3 prover containers (skip imandra — licence required)
container-build-tier3: container-build-tamarin container-build-proverif container-build-metamath \
    container-build-twelf container-build-or-tools container-build-scip \
    container-build-hol4 container-build-acl2

container-build-tamarin:
    podman build -f .containerization/Containerfile.wave3 --target tamarin -t echidna:tamarin .

container-build-proverif:
    podman build -f .containerization/Containerfile.wave3 --target proverif -t echidna:proverif .

container-build-metamath:
    podman build -f .containerization/Containerfile.wave3 --target metamath -t echidna:metamath .

container-build-twelf:
    podman build -f .containerization/Containerfile.wave3 --target twelf -t echidna:twelf .

container-build-or-tools:
    podman build -f .containerization/Containerfile.wave3 --target or-tools -t echidna:or-tools .

container-build-scip:
    podman build -f .containerization/Containerfile.wave3 --target scip -t echidna:scip .

container-build-hol4:
    podman build -f .containerization/Containerfile.wave3 --target hol4 -t echidna:hol4 .

container-build-acl2:
    podman build -f .containerization/Containerfile.wave3 --target acl2 -t echidna:acl2 .

# Build imandra stub (proprietary; real binary requires a signed licence — see Containerfile.wave3 imandra target)
container-build-imandra:
    podman build -f .containerization/Containerfile.wave3 --target imandra -t echidna:imandra .

# Run echidna container
container-run *ARGS:
    podman run --rm -it echidna:latest {{ARGS}}
