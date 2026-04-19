// SPDX-License-Identifier: PMPL-1.0-or-later
// ECHIDNA Zig FFI Build Configuration
// Compatible with Zig 0.14+/0.15+

const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // Whether to bundle chapel_stubs.c into the produced libraries.
    //
    // Default = true so the resulting static/shared library resolves every
    // `chapel_*` symbol on its own — Rust's `cargo build --features chapel`
    // then links cleanly without a Chapel install in sight.
    //
    // Pass `-Dstubs=false` when linking against the real libechidna_chapel
    // (built from chapel_poc/); the Chapel-compiled symbols take the place
    // of the stubs.
    const stubs = b.option(bool, "stubs", "Bundle chapel_stubs.c so chapel_* symbols resolve without Chapel") orelse true;

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
    if (stubs) {
        // -fno-sanitize=undefined: Zig defaults UBSan on for C, pulling in
        // __ubsan_* that Rust's linker cannot resolve. Stubs are trivial;
        // skip UBSan.
        lib.addCSourceFile(.{ .file = b.path("chapel_stubs.c"), .flags = &.{"-fno-sanitize=undefined"} });
    }

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
    if (stubs) {
        lib_static.addCSourceFile(.{ .file = b.path("chapel_stubs.c"), .flags = &.{"-fno-sanitize=undefined"} });
    }

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
