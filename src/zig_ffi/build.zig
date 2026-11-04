// SPDX-License-Identifier: MPL-2.0
// ECHIDNA Zig FFI Build Configuration
// Compatible with Zig 0.14

const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});
    const stubs = b.option(bool, "stubs", "Bundle Chapel-unavailable stubs") orelse true;
    const options = b.addOptions();
    options.addOption(bool, "chapel_stubs", stubs);

    // A real bridge is a static archive with Chapel references. The final
    // consumer links libechidna_chapel.a and the compiler-selected runtime.
    // Do not produce a nominal real shared object with unresolved symbols:
    // the packaged Chapel runtime is non-PIC.
    if (stubs) {
        const shared = b.addLibrary(.{
            .name = "echidna_chapel_ffi",
            .root_module = b.createModule(.{
                .root_source_file = b.path("chapel_bridge.zig"),
                .target = target,
                .optimize = optimize,
                .link_libc = true,
            }),
            .linkage = .dynamic,
        });
        shared.bundle_compiler_rt = true;
        shared.root_module.addIncludePath(b.path("."));
        shared.root_module.addOptions("chapel_options", options);
        shared.addCSourceFile(.{
            .file = b.path("chapel_stubs.c"),
            .flags = &.{"-fno-sanitize=undefined"},
        });
        b.installArtifact(shared);
    }

    const archive = b.addLibrary(.{
        .name = "echidna_chapel_ffi",
        .root_module = b.createModule(.{
            .root_source_file = b.path("chapel_bridge.zig"),
            .target = target,
            .optimize = optimize,
            .link_libc = true,
        }),
        .linkage = .static,
    });
    // Rust consumes this archive, so bundle Zig's compiler-rt instead of
    // requiring a separate Zig runtime at the final non-Zig link.
    archive.bundle_compiler_rt = true;
    archive.root_module.addIncludePath(b.path("."));
    archive.root_module.addOptions("chapel_options", options);
    if (stubs) {
        archive.addCSourceFile(.{
            .file = b.path("chapel_stubs.c"),
            .flags = &.{"-fno-sanitize=undefined"},
        });
    }
    b.installArtifact(archive);

    // Install mode metadata next to the archive. Cargo checks an explicitly
    // requested mode and real-runtime tests still check actual behavior.
    const generated = b.addWriteFiles();
    const mode = generated.add("echidna_chapel_ffi.mode", if (stubs) "stubs\n" else "real\n");
    const install_mode = b.addInstallLibFile(mode, "echidna_chapel_ffi.mode");
    b.getInstallStep().dependOn(&install_mode.step);

    // Independent bridge unit tests always exercise unavailable-stub behavior.
    const test_options = b.addOptions();
    test_options.addOption(bool, "chapel_stubs", true);
    const lib_tests = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("chapel_bridge.zig"),
            .target = target,
            .optimize = optimize,
            .link_libc = true,
        }),
    });
    lib_tests.root_module.addIncludePath(b.path("."));
    lib_tests.root_module.addOptions("chapel_options", test_options);
    lib_tests.addCSourceFile(.{ .file = b.path("chapel_stubs.c") });
    const run_lib_tests = b.addRunArtifact(lib_tests);
    const test_step = b.step("test", "Run FFI tests with explicit Chapel stubs");
    test_step.dependOn(&run_lib_tests.step);

    // Exercise real OS-thread ownership and shutdown ordering independently
    // of the deliberately unavailable Chapel stubs.
    const owner_tests = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("runtime_owner.zig"),
            .target = target,
            .optimize = optimize,
            .link_libc = true,
        }),
    });
    const run_owner_tests = b.addRunArtifact(owner_tests);
    test_step.dependOn(&run_owner_tests.step);
}
