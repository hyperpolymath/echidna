// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later
//
// ECHIDNA FFI Build Configuration (Zig 0.15.2)
//
// Builds:
//   - libechidna_ffi.so  (shared library for V-lang / other consumers)
//   - libechidna_ffi.a   (static library)
//   - Unit tests (standalone, no Rust linkage required)
//
// When libechidna.so is available, pass -Drust-lib-path=<dir> to link against it.

const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // Optional: path to directory containing libechidna.so (Rust output)
    const rust_lib_path = b.option([]const u8, "rust-lib-path", "Path to directory containing libechidna.so");

    // ---------------------------------------------------------------
    // Root module (shared across library and test targets)
    // ---------------------------------------------------------------
    const root_module = b.createModule(.{
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });

    if (rust_lib_path) |rpath| {
        root_module.addLibraryPath(.{ .cwd_relative = rpath });
        root_module.linkSystemLibrary("echidna", .{});
    }

    // ---------------------------------------------------------------
    // Shared library: libechidna_ffi.so / .dylib / .dll
    // ---------------------------------------------------------------
    const lib_shared = b.addLibrary(.{
        .name = "echidna_ffi",
        .root_module = root_module,
        .linkage = .dynamic,
        .version = .{ .major = 1, .minor = 5, .patch = 0 },
    });

    b.installArtifact(lib_shared);

    // ---------------------------------------------------------------
    // Static library: libechidna_ffi.a
    // ---------------------------------------------------------------
    const static_module = b.createModule(.{
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });

    if (rust_lib_path) |rpath| {
        static_module.addLibraryPath(.{ .cwd_relative = rpath });
        static_module.linkSystemLibrary("echidna", .{});
    }

    const lib_static = b.addLibrary(.{
        .name = "echidna_ffi",
        .root_module = static_module,
        .linkage = .static,
    });

    b.installArtifact(lib_static);

    // ---------------------------------------------------------------
    // Unit tests (standalone — no Rust linkage needed)
    // ---------------------------------------------------------------
    const test_module = b.createModule(.{
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });

    const lib_tests = b.addTest(.{
        .root_module = test_module,
    });

    const run_lib_tests = b.addRunArtifact(lib_tests);

    const test_step = b.step("test", "Run unit tests (standalone, no Rust linkage)");
    test_step.dependOn(&run_lib_tests.step);

    // ---------------------------------------------------------------
    // Integration tests (require libechidna.so)
    // ---------------------------------------------------------------
    const integ_module = b.createModule(.{
        .root_source_file = b.path("test/integration_test.zig"),
        .target = target,
        .optimize = optimize,
    });

    if (rust_lib_path) |rpath| {
        integ_module.addLibraryPath(.{ .cwd_relative = rpath });
        integ_module.linkSystemLibrary("echidna", .{});
    }

    const integration_tests = b.addTest(.{
        .root_module = integ_module,
    });

    integration_tests.linkLibrary(lib_shared);

    const run_integration_tests = b.addRunArtifact(integration_tests);

    const integration_test_step = b.step("test-integration", "Run integration tests (requires libechidna.so)");
    integration_test_step.dependOn(&run_integration_tests.step);
}
