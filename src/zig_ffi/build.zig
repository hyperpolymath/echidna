// SPDX-License-Identifier: PMPL-1.0-or-later
// ECHIDNA Zig FFI Build Configuration

const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // Build shared library for FFI
    const lib = b.addSharedLibrary(.{
        .name = "echidna_chapel_ffi",
        .root_source_file = b.path("chapel_bridge.zig"),
        .target = target,
        .optimize = optimize,
    });

    // Link with C (required for Chapel interop)
    lib.linkLibC();

    // Set version
    lib.version = .{ .major = 1, .minor = 0, .patch = 0 };

    // Install artifacts
    b.installArtifact(lib);

    // Static library (alternative)
    const lib_static = b.addStaticLibrary(.{
        .name = "echidna_chapel_ffi",
        .root_source_file = b.path("chapel_bridge.zig"),
        .target = target,
        .optimize = optimize,
    });

    lib_static.linkLibC();
    b.installArtifact(lib_static);

    // Unit tests
    const lib_tests = b.addTest(.{
        .root_source_file = b.path("chapel_bridge.zig"),
        .target = target,
        .optimize = optimize,
    });

    lib_tests.linkLibC();

    const run_lib_tests = b.addRunArtifact(lib_tests);

    const test_step = b.step("test", "Run FFI tests");
    test_step.dependOn(&run_lib_tests.step);

    // Documentation
    const docs = b.addTest(.{
        .root_source_file = b.path("chapel_bridge.zig"),
        .target = target,
        .optimize = .Debug,
    });

    const docs_step = b.step("docs", "Generate documentation");
    docs_step.dependOn(&b.addInstallDirectory(.{
        .source_dir = docs.getEmittedDocs(),
        .install_dir = .prefix,
        .install_subdir = "docs",
    }).step);
}
