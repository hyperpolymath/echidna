// SPDX-License-Identifier: PMPL-1.0-or-later
// ECHIDNA Zig FFI Build Configuration
// Compatible with Zig 0.14+/0.15+

const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // Build shared library for FFI
    const lib = b.addLibrary(.{
        .name = "echidna_chapel_ffi",
        .root_module = b.createModule(.{
            .root_source_file = b.path("chapel_bridge.zig"),
            .target = target,
            .optimize = optimize,
            .link_libc = true,
        }),
        .linkage = .dynamic,
    });
    // Chapel C headers are in the same directory
    lib.root_module.addIncludePath(b.path("."));

    // Install artifacts
    b.installArtifact(lib);

    // Static library (alternative)
    const lib_static = b.addLibrary(.{
        .name = "echidna_chapel_ffi",
        .root_module = b.createModule(.{
            .root_source_file = b.path("chapel_bridge.zig"),
            .target = target,
            .optimize = optimize,
            .link_libc = true,
        }),
        .linkage = .static,
    });
    lib_static.root_module.addIncludePath(b.path("."));

    b.installArtifact(lib_static);

    // Unit tests (link against stubs when Chapel not available)
    const lib_tests = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("chapel_bridge.zig"),
            .target = target,
            .optimize = optimize,
            .link_libc = true,
        }),
    });
    lib_tests.root_module.addIncludePath(b.path("."));
    lib_tests.addCSourceFile(.{ .file = b.path("chapel_stubs.c") });

    const run_lib_tests = b.addRunArtifact(lib_tests);

    const test_step = b.step("test", "Run FFI tests");
    test_step.dependOn(&run_lib_tests.step);
}
