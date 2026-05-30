<!-- SPDX-License-Identifier: MPL-2.0 -->

# 2026-05-30 — Chapel PIC rebuild from source for `--library --dynamic`

ADR-style addendum to [2026-05-30-chapel-rehabilitation.md][rehab].
Documents the procedure and constraints for replacing the apt-shipped
Chapel runtime with a position-independent variant so the metalayer can
be linked as a shared library instead of a static archive.

[rehab]: ./2026-05-30-chapel-rehabilitation.md

## Status

Documented. Procedure is `just chapel-pic-from-source`; **not** invoked
from any CI workflow because the build is ~30 min wall and ~5 GB disk,
which would dominate the Chapel CI budget for negligible runtime gain
until L2.5 multi-locale work needs the shared-library form.

## Context

The rehabilitation PR (#146) chose `--library --static` for
`chapel-build` because the apt-distributed Chapel deb only ships one
runtime variant — `lib_pic-none`:

```
/usr/lib/chapel/2.8/runtime/lib/linux64/gnu/x86_64/loc-flat/
  comm-none/tasks-qthreads/launch-smp/tmr-generic/unwind-system/
  mem-jemalloc/atomics-cstdlib/lib_pic-none/san-none/libchpllaunch.a
```

`chpl --library --dynamic` requires a `lib_pic-pic/` variant in the
same path tree; without it, the link of `libchpl.a` into a `.so` fails
with:

```
relocation R_X86_64_TPOFF32 against symbol `chpl_task_root_uniqueId'
can not be used when making a shared object; recompile with -fPIC
```

The same constraint applies to the conda-forge `chapel` package, which
also ships only the non-PIC runtime variant as of 2.8.0.

The only way to obtain a PIC runtime is to build Chapel from the
release source with `CHPL_LIB_PIC=pic` set at `make` time. The variant
ends up at the parallel `lib_pic-pic/` path and is auto-discovered by
`chpl --library --dynamic` at link time.

## Decision

Ship a documented, reproducible Justfile recipe that performs the
source rebuild on demand, but do **not** invoke it from CI and do **not**
change the canonical `chapel-build` recipe. Local developers and the
eventual L2.5 multi-locale workflow can opt in via `just chapel-pic-from-source`.

Rationale:

- The PIC rebuild is a one-shot ~30 min operation per CI runner, which
  cannot be amortised across PRs without a registry-pushed container
  image — see follow-up below.
- The static-library form (`--library --static`) is correct for the
  current Rust-link path; Rust binaries already embed the Chapel
  runtime by linking against `libechidna_chapel.a`. Switching to
  `.so` linkage gains separability of the Chapel runtime but adds
  packaging complexity (now two artifacts to ship and version).
- The PIC form is only **required** for L2.5 (multi-locale Chapel
  dispatch under PGAS), where the runtime needs to be loadable from
  multiple Chapel-distinct executables. That work is gated on L1
  Cap'n Proto, so the PIC runtime is a precondition we can satisfy
  asynchronously when L2.5 starts.

## Procedure

```bash
just chapel-pic-from-source
```

Equivalent to:

```bash
mkdir -p ~/.cache/echidna/chapel-pic && cd ~/.cache/echidna/chapel-pic

# Source — 2.8.0 matches the local development install. Adjust if
# CI moves to a newer point release.
curl -fL https://github.com/chapel-lang/chapel/releases/download/2.8.0/chapel-2.8.0.tar.gz \
    -o chapel-2.8.0.tar.gz
tar xf chapel-2.8.0.tar.gz
cd chapel-2.8.0

# PIC runtime variant — the single env var that drives the additional
# `lib_pic-pic/` subtree under `runtime/lib/.../`. LLVM is the default
# back end on 2.8+; the apt deb also uses LLVM, so we match.
export CHPL_LIB_PIC=pic
export CHPL_LLVM=bundled        # match apt deb
export CHPL_HOME=$PWD
source util/setchplenv.bash

# Build. This step is ~25-35 min wall on a 4-core x86_64 box.
make -j$(nproc)

# Verify the PIC variant landed.
find lib -name 'lib_pic-pic' -type d | head -1
```

After this completes, `chpl` from `$CHPL_HOME/bin/linux64-x86_64/chpl`
can produce shared-library output:

```bash
$CHPL_HOME/bin/linux64-x86_64/chpl \
    --library --dynamic -I ../zig_ffi \
    -o libechidna_chapel parallel_proof_search.chpl chapel_ffi_exports.chpl
```

## Tradeoffs

| Aspect | `--library --static` (current default) | `--library --dynamic` (PIC rebuild) |
|---|---|---|
| Build time, cold | ~10 s | ~30 min (one-time) + ~10 s |
| Build time, warm | ~10 s | ~10 s |
| Disk footprint | runtime in libchpl.a (~30 MB) | runtime in libchpl.so (~30 MB) + source tree (~5 GB) |
| Rust link | static archive into executable | dynamic load at runtime |
| Multi-process sharing | each process embeds runtime | runtime shared across processes |
| L2.5 multi-locale | does not support | required |

## Follow-up

A registry-pushed Containerfile that pre-builds the PIC runtime would
amortise the 30 min cost across CI runs, but requires:

- A `Containerfile.chapel-pic` under `.containerization/`.
- A registry destination (ghcr.io/hyperpolymath/echidna-chapel-pic:2.8.0).
- A CI job to build + push on chapel version bumps.

Tracked as a Wave-3 follow-up issue; the current PR does **not** add
the container path because it would duplicate the in-flight L1 Cap'n
Proto schema work and risk image-tag drift if Chapel point-releases
between now and L2.5 starting.

## Verification

The recipe is not executed in CI for the reasons above. Local
verification (one-time, by anyone who wants `--dynamic` linkage) is:

```bash
just chapel-pic-from-source
# Confirm:
find ~/.cache/echidna/chapel-pic/chapel-2.8.0/lib -name 'lib_pic-pic' -type d
# Expected output: at least one path containing `lib_pic-pic/`.
```
