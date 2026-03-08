// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: PMPL-1.0-or-later
//
// ECHIDNA FFI Build Configuration (Zig 0.15.2)
//
// Builds:
//   - libechidna_ffi.so     (shared library for V-lang / other consumers)
//   - libechidna_ffi.a      (static library)
//   - libechidna_overlay.so (Tor/IPFS/Ethereum overlay networks)
//   - libechidna_overlay.a  (static overlay library)
//   - Unit tests (standalone, no Rust linkage required)
//   - Overlay tests (Tor, IPFS, Ethereum)
//   - Integration tests (link against libechidna_ffi.so)
//   - Overlay integration tests (link against libechidna_overlay.so)
//   - Benchmark executable (link against libechidna_ffi.so)
//   - Overlay benchmark executable (link against libechidna_overlay.so)
//
// When libechidna.so is available, pass -Drust-lib-path=<dir> to link against it.

const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // Optional: path to directory containing libechidna.so (Rust output)
    const rust_lib_path = b.option([]const u8, "rust-lib-path", "Path to directory containing libechidna.so");

    // Top-level test step (all unit tests aggregate here)
    const test_step = b.step("test", "Run all unit tests (standalone, no Rust linkage)");

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
    // FFI unit tests (standalone — no Rust linkage needed)
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
    test_step.dependOn(&run_lib_tests.step);

    // ---------------------------------------------------------------
    // Overlay module: libechidna_overlay.so (Tor, IPFS, Ethereum)
    // ---------------------------------------------------------------
    const overlay_module = b.createModule(.{
        .root_source_file = b.path("src/overlay.zig"),
        .target = target,
        .optimize = optimize,
    });

    const lib_overlay = b.addLibrary(.{
        .name = "echidna_overlay",
        .root_module = overlay_module,
        .linkage = .dynamic,
        .version = .{ .major = 1, .minor = 0, .patch = 0 },
    });

    b.installArtifact(lib_overlay);

    const lib_overlay_static = b.addLibrary(.{
        .name = "echidna_overlay",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/overlay.zig"),
            .target = target,
            .optimize = optimize,
        }),
        .linkage = .static,
    });

    b.installArtifact(lib_overlay_static);

    // Overlay unit tests
    const overlay_test_module = b.createModule(.{
        .root_source_file = b.path("src/overlay.zig"),
        .target = target,
        .optimize = optimize,
    });

    const overlay_tests = b.addTest(.{
        .root_module = overlay_test_module,
    });

    const run_overlay_tests = b.addRunArtifact(overlay_tests);

    const overlay_test_step = b.step("test-overlay", "Run overlay (Tor/IPFS/Ethereum) unit tests");
    overlay_test_step.dependOn(&run_overlay_tests.step);

    // Overlay tests also run under `zig build test`
    test_step.dependOn(&run_overlay_tests.step);

    // ---------------------------------------------------------------
    // Integration tests (link against libechidna_ffi.so)
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

    integ_module.link_libc = true;

    const integration_tests = b.addTest(.{
        .root_module = integ_module,
    });

    integration_tests.linkLibrary(lib_shared);

    const run_integration_tests = b.addRunArtifact(integration_tests);

    const integration_test_step = b.step("test-integration", "Run integration tests (links libechidna_ffi.so)");
    integration_test_step.dependOn(&run_integration_tests.step);

    // ---------------------------------------------------------------
    // Benchmark executable (links against libechidna_ffi.so)
    // ---------------------------------------------------------------
    const bench_module = b.createModule(.{
        .root_source_file = b.path("test/benchmark.zig"),
        .target = target,
        .optimize = .ReleaseFast,
    });

    if (rust_lib_path) |rpath| {
        bench_module.addLibraryPath(.{ .cwd_relative = rpath });
        bench_module.linkSystemLibrary("echidna", .{});
    }

    bench_module.link_libc = true;

    const benchmark_exe = b.addExecutable(.{
        .name = "echidna_benchmark",
        .root_module = bench_module,
    });

    benchmark_exe.linkLibrary(lib_shared);

    b.installArtifact(benchmark_exe);

    const run_benchmark = b.addRunArtifact(benchmark_exe);

    const benchmark_step = b.step("benchmark", "Build and run the FFI benchmark suite");
    benchmark_step.dependOn(&run_benchmark.step);

    // ---------------------------------------------------------------
    // Overlay integration tests (link against libechidna_overlay.so)
    // ---------------------------------------------------------------
    const overlay_integ_module = b.createModule(.{
        .root_source_file = b.path("test/overlay_integration_test.zig"),
        .target = target,
        .optimize = optimize,
    });

    overlay_integ_module.link_libc = true;

    const overlay_integration_tests = b.addTest(.{
        .root_module = overlay_integ_module,
    });

    overlay_integration_tests.linkLibrary(lib_overlay);

    const run_overlay_integration_tests = b.addRunArtifact(overlay_integration_tests);

    const overlay_integration_test_step = b.step("test-overlay-integration", "Run overlay integration tests (links libechidna_overlay.so)");
    overlay_integration_test_step.dependOn(&run_overlay_integration_tests.step);

    // ---------------------------------------------------------------
    // Overlay benchmark executable (links against libechidna_overlay.so)
    // ---------------------------------------------------------------
    const overlay_bench_module = b.createModule(.{
        .root_source_file = b.path("test/overlay_benchmark.zig"),
        .target = target,
        .optimize = .ReleaseFast,
    });

    overlay_bench_module.link_libc = true;

    const overlay_benchmark_exe = b.addExecutable(.{
        .name = "echidna_overlay_benchmark",
        .root_module = overlay_bench_module,
    });

    overlay_benchmark_exe.linkLibrary(lib_overlay);

    b.installArtifact(overlay_benchmark_exe);

    const run_overlay_benchmark = b.addRunArtifact(overlay_benchmark_exe);

    const overlay_benchmark_step = b.step("benchmark-overlay", "Build and run the overlay benchmark suite");
    overlay_benchmark_step.dependOn(&run_overlay_benchmark.step);

    // ---------------------------------------------------------------
    // BoJ client module: libechidna_boj.so
    // ---------------------------------------------------------------
    const boj_module = b.createModule(.{
        .root_source_file = b.path("src/boj.zig"),
        .target = target,
        .optimize = optimize,
    });

    const lib_boj = b.addLibrary(.{
        .name = "echidna_boj",
        .root_module = boj_module,
        .linkage = .dynamic,
        .version = .{ .major = 0, .minor = 2, .patch = 0 },
    });
    b.installArtifact(lib_boj);

    const lib_boj_static = b.addLibrary(.{
        .name = "echidna_boj",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/boj.zig"),
            .target = target,
            .optimize = optimize,
        }),
        .linkage = .static,
    });
    b.installArtifact(lib_boj_static);

    // BoJ unit tests
    const boj_test_module = b.createModule(.{
        .root_source_file = b.path("src/boj.zig"),
        .target = target,
        .optimize = optimize,
    });
    const boj_tests = b.addTest(.{ .root_module = boj_test_module });
    const run_boj_tests = b.addRunArtifact(boj_tests);
    const boj_test_step = b.step("test-boj", "Run BoJ client unit tests");
    boj_test_step.dependOn(&run_boj_tests.step);
    test_step.dependOn(&run_boj_tests.step);

    // ---------------------------------------------------------------
    // TypeLL client module: libechidna_typell.so
    // ---------------------------------------------------------------
    const typell_module = b.createModule(.{
        .root_source_file = b.path("src/typell.zig"),
        .target = target,
        .optimize = optimize,
    });

    const lib_typell = b.addLibrary(.{
        .name = "echidna_typell",
        .root_module = typell_module,
        .linkage = .dynamic,
        .version = .{ .major = 0, .minor = 1, .patch = 0 },
    });
    b.installArtifact(lib_typell);

    const lib_typell_static = b.addLibrary(.{
        .name = "echidna_typell",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/typell.zig"),
            .target = target,
            .optimize = optimize,
        }),
        .linkage = .static,
    });
    b.installArtifact(lib_typell_static);

    // TypeLL unit tests
    const typell_test_module = b.createModule(.{
        .root_source_file = b.path("src/typell.zig"),
        .target = target,
        .optimize = optimize,
    });
    const typell_tests = b.addTest(.{ .root_module = typell_test_module });
    const run_typell_tests = b.addRunArtifact(typell_tests);
    const typell_test_step = b.step("test-typell", "Run TypeLL client unit tests");
    typell_test_step.dependOn(&run_typell_tests.step);
    test_step.dependOn(&run_typell_tests.step);

    // ---------------------------------------------------------------
    // Tentacles module: libechidna_tentacles.so
    // ---------------------------------------------------------------
    const tentacles_module = b.createModule(.{
        .root_source_file = b.path("src/tentacles.zig"),
        .target = target,
        .optimize = optimize,
    });

    const lib_tentacles = b.addLibrary(.{
        .name = "echidna_tentacles",
        .root_module = tentacles_module,
        .linkage = .dynamic,
        .version = .{ .major = 1, .minor = 0, .patch = 0 },
    });
    b.installArtifact(lib_tentacles);

    const lib_tentacles_static = b.addLibrary(.{
        .name = "echidna_tentacles",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/tentacles.zig"),
            .target = target,
            .optimize = optimize,
        }),
        .linkage = .static,
    });
    b.installArtifact(lib_tentacles_static);

    // Tentacles unit tests
    const tentacles_test_module = b.createModule(.{
        .root_source_file = b.path("src/tentacles.zig"),
        .target = target,
        .optimize = optimize,
    });
    const tentacles_tests = b.addTest(.{ .root_module = tentacles_test_module });
    const run_tentacles_tests = b.addRunArtifact(tentacles_tests);
    const tentacles_test_step = b.step("test-tentacles", "Run Tentacles unit tests");
    tentacles_test_step.dependOn(&run_tentacles_tests.step);
    test_step.dependOn(&run_tentacles_tests.step);

    // ---------------------------------------------------------------
    // Pure Zig overlay tests (native @import, no C-ABI overhead)
    // ---------------------------------------------------------------
    const native_test_module = b.createModule(.{
        .root_source_file = b.path("test/overlay_native_test.zig"),
        .target = target,
        .optimize = optimize,
    });

    native_test_module.addImport("overlay", overlay_module);

    const native_tests = b.addTest(.{
        .root_module = native_test_module,
    });

    const run_native_tests = b.addRunArtifact(native_tests);

    const native_test_step = b.step("test-overlay-native", "Run pure Zig overlay tests (native @import, no C-ABI)");
    native_test_step.dependOn(&run_native_tests.step);

    // ---------------------------------------------------------------
    // Pure Zig core tests (native @import, no C-ABI overhead)
    // ---------------------------------------------------------------
    const core_native_test_module = b.createModule(.{
        .root_source_file = b.path("test/core_native_test.zig"),
        .target = target,
        .optimize = optimize,
    });

    core_native_test_module.addImport("core", root_module);

    const core_native_tests = b.addTest(.{
        .root_module = core_native_test_module,
    });

    const run_core_native_tests = b.addRunArtifact(core_native_tests);

    const core_native_test_step = b.step("test-core-native", "Run pure Zig core tests (native @import, no C-ABI)");
    core_native_test_step.dependOn(&run_core_native_tests.step);
}
