// {{PROJECT}} FFI Build Configuration
// SPDX-License-Identifier: AGPL-3.0-or-later

const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // Shared library (.so, .dylib, .dll)
    const lib = b.addSharedLibrary(.{
        .name = "{{project}}",
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });

    // Set version
    lib.version = .{ .major = 0, .minor = 1, .patch = 0 };

    // Static library (.a)
    const lib_static = b.addStaticLibrary(.{
        .name = "{{project}}",
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });

    // Install artifacts
    b.installArtifact(lib);
    b.installArtifact(lib_static);

    // Generate header file for C compatibility
    const header = b.addInstallHeader(
        b.path("include/{{project}}.h"),
        "{{project}}.h",
    );
    b.getInstallStep().dependOn(&header.step);

    // Unit tests
    const lib_tests = b.addTest(.{
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });

    const run_lib_tests = b.addRunArtifact(lib_tests);

    const test_step = b.step("test", "Run library tests");
    test_step.dependOn(&run_lib_tests.step);

    // Integration tests
    const integration_tests = b.addTest(.{
        .root_source_file = b.path("test/integration_test.zig"),
        .target = target,
        .optimize = optimize,
    });

    integration_tests.linkLibrary(lib);

    const run_integration_tests = b.addRunArtifact(integration_tests);

    const integration_test_step = b.step("test-integration", "Run integration tests");
    integration_test_step.dependOn(&run_integration_tests.step);

    // Documentation
    const docs = b.addTest(.{
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = .Debug,
    });

    const docs_step = b.step("docs", "Generate documentation");
    docs_step.dependOn(&b.addInstallDirectory(.{
        .source_dir = docs.getEmittedDocs(),
        .install_dir = .prefix,
        .install_subdir = "docs",
    }).step);

    // Benchmark (if needed)
    const bench = b.addExecutable(.{
        .name = "{{project}}-bench",
        .root_source_file = b.path("bench/bench.zig"),
        .target = target,
        .optimize = .ReleaseFast,
    });

    bench.linkLibrary(lib);

    const run_bench = b.addRunArtifact(bench);

    const bench_step = b.step("bench", "Run benchmarks");
    bench_step.dependOn(&run_bench.step);
}
