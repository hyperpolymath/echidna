# SPDX-License-Identifier: MPL-2.0
# Imported by the root Justfile (hotspot split); recipes moved verbatim.

# ── SPARK axiom-policy layer ─────────────────────────────────

# Step 1: compile Ada/SPARK to static library (requires GNAT + GNATprove)
build-spark-ada:
    gprbuild -P src/ada/spark/echidna_spark.gpr -j0
    @echo "SPARK library built at lib/spark/libechidna_spark.a"

# Step 2: run GNATprove to formally verify the SPARK contracts
prove-spark:
    gnatprove -P src/ada/spark/echidna_spark.gpr --level=2 \
        --prover=z3,cvc5,altergo --timeout=30 --report=fail -j0
    @echo "GNATprove: all SPARK contracts discharged"

# Step 3: compile Zig bridge (links against libechidna_spark.a)
build-spark-zig: build-spark-ada
    cd src/zig && zig build -Dspark=true -Doptimize=ReleaseSafe
    @echo "SPARK Zig bridge built at src/zig/zig-out/lib/libechidna_spark_zig.a"

# Step 4: build Rust with SPARK feature enabled
build-spark: build-spark-zig
    cargo build --features spark
    @echo "Rust+SPARK build complete"

# Full SPARK pipeline: prove → build → test
spark-all: prove-spark build-spark-zig
    cargo test --features spark -- spark
    @echo "SPARK layer: proved, built, tested"

# Cross-check: run both Rust and SPARK enforce_policy, assert agreement
verify-spark-crosscheck: build-spark
    cargo test --features spark -- crosscheck
    @echo "SPARK/Rust crosscheck passed"
