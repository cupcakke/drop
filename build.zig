const std = @import("std");
pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});
    const gpu_enabled = b.option(bool, "gpu", "Enable GPU/CUDA via Futhark CUDA backend") orelse false;
    const futhark_gpu_c = b.path("src/hw/accel/main_gpu.c");
    const futhark_include = b.path("src/hw/accel");
    const futhark_gpu_step = b.addSystemCommand(&.{
        "futhark", "cuda", "--library",
        "src/hw/accel/main.fut",
        "-o",      "src/hw/accel/main_gpu",
    });
    if (gpu_enabled) {
        const distributed_futhark_exe = b.addExecutable(.{
            .name = "jaide-distributed-futhark",
            .root_source_file = b.path("src/main_distributed_futhark.zig"),
            .target = target,
            .optimize = optimize,
        });
        distributed_futhark_exe.linkLibC();
        distributed_futhark_exe.addCSourceFile(.{ .file = futhark_gpu_c, .flags = &.{"-O2"} });
        distributed_futhark_exe.addIncludePath(futhark_include);
        distributed_futhark_exe.addIncludePath(.{ .cwd_relative = "/usr/local/cuda/include" });
        distributed_futhark_exe.addLibraryPath(.{ .cwd_relative = "/usr/local/cuda/lib64" });
        distributed_futhark_exe.addLibraryPath(.{ .cwd_relative = "/usr/local/cuda/lib64/stubs" });
        distributed_futhark_exe.linkSystemLibrary("cuda");
        distributed_futhark_exe.linkSystemLibrary("cudart");
        distributed_futhark_exe.linkSystemLibrary("nvrtc");
        distributed_futhark_exe.linkSystemLibrary("nccl");
        distributed_futhark_exe.linkSystemLibrary("m");
        distributed_futhark_exe.linkSystemLibrary("pthread");
        distributed_futhark_exe.linkSystemLibrary("dl");
        distributed_futhark_exe.root_module.addOptions("build_options", b.createModule(.{
            .root_source_file = b.path("src/build.zig"),
            .target = target,
            .optimize = optimize,
        }));
        distributed_futhark_exe.step.dependOn(&futhark_gpu_step.step);
        b.installArtifact(distributed_futhark_exe);
    }
}
