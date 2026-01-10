# SPDX-License-Identifier: PMPL-1.0
FROM gcr.io/oss-fuzz-base/base-builder-rust@sha256:73c1d5648db54100639339d411a5d192cbc8bf413ee91e843a07cf6f0e319dc7

COPY . $SRC/echidna
WORKDIR $SRC/echidna

COPY .clusterfuzzlite/build.sh $SRC/
