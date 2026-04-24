// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later

const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // ========================================================================
    // SPARK axiom-policy bridge (optional — requires libechidna_spark.a)
    //
    // Build order:
    //   1. gprbuild -P src/ada/spark/echidna_spark.gpr
    //      → lib/spark/libechidna_spark.a
    //   2. zig build -Dspark (this step)
    //      → zig-out/lib/libechidna_spark_zig.a
    //   3. cargo build --features spark
    //      → links both libraries into the Rust binary
    //
    // Enabled with -Dspark=true (default: false so no-SPARK machines compile)
    // ========================================================================
    const build_spark = b.option(bool, "spark", "Build SPARK axiom-policy bridge") orelse false;

    if (build_spark) {
        const spark_lib_dir = b.pathFromRoot("../../lib/spark");

        const spark_static = b.addStaticLibrary(.{
            .name = "echidna_spark_zig",
            .root_source_file = b.path("ffi/axiom_spark_bridge.zig"),
            .target = target,
            .optimize = optimize,
        });

        spark_static.linkLibC();
        // Link against the GPRbuild-produced SPARK runtime library
        spark_static.addLibraryPath(.{ .cwd_relative = spark_lib_dir });
        spark_static.linkSystemLibrary("echidna_spark");
        // GNAT runtime (required by all Ada programs)
        spark_static.linkSystemLibrary("gnat");

        b.installArtifact(spark_static);
    }

    // ========================================================================
    // Static Library (for linking into Rust)
    // ========================================================================
    const static_lib = b.addStaticLibrary(.{
        .name = "echidna_ffi",
        .root_source_file = b.path("ffi/echidna_ffi.zig"),
        .target = target,
        .optimize = optimize,
    });

    // Link libc for C ABI compatibility
    static_lib.linkLibC();

    // Install the static library
    b.installArtifact(static_lib);

    // ========================================================================
    // Shared Library (for dynamic loading)
    // ========================================================================
    const shared_lib = b.addSharedLibrary(.{
        .name = "echidna_ffi",
        .root_source_file = b.path("ffi/echidna_ffi.zig"),
        .target = target,
        .optimize = optimize,
    });

    shared_lib.linkLibC();
    b.installArtifact(shared_lib);

    // ========================================================================
    // C Header Generation
    // ========================================================================
    // Note: Zig doesn't auto-generate C headers, but we provide one manually
    // See: ffi/echidna_ffi.h

    // ========================================================================
    // Tests
    // ========================================================================
    const unit_tests = b.addTest(.{
        .root_source_file = b.path("ffi/echidna_ffi.zig"),
        .target = target,
        .optimize = optimize,
    });

    const run_unit_tests = b.addRunArtifact(unit_tests);

    const test_step = b.step("test", "Run unit tests");
    test_step.dependOn(&run_unit_tests.step);

    // ========================================================================
    // Documentation
    // ========================================================================
    const docs = b.addStaticLibrary(.{
        .name = "echidna_ffi",
        .root_source_file = b.path("ffi/echidna_ffi.zig"),
        .target = target,
        .optimize = optimize,
    });

    const install_docs = b.addInstallDirectory(.{
        .source_dir = docs.getEmittedDocs(),
        .install_dir = .prefix,
        .install_subdir = "docs",
    });

    const docs_step = b.step("docs", "Generate documentation");
    docs_step.dependOn(&install_docs.step);
}
