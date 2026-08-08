const std = @import("std");
const build_options = @import("build_options");
const accel = @import("hw/accel/accel_interface.zig");
const distributed_trainer = @import("distributed/distributed_trainer_futhark.zig");
const rsf = @import("processor/rsf.zig");
const types = @import("core/types.zig");
pub fn main() !void {
    const cfg = rsf.RSFConfig{
        .max_dim = 11200,
        .max_layers = 12,
        .grad_mean = true,
        .clip_min = -5.0,
        .clip_max = 5.0,
    };
    const half_dim = 11200;
    const num_layers = 12;
    const max_epochs: usize = 1;
    const max_tokens: usize = 10_000_000_000;
    _ = cfg;
    _ = half_dim;
    _ = num_layers;
    _ = max_epochs;
    _ = max_tokens;
    const allocator = std.heap.page_allocator;
    var trainer = try distributed_trainer.DistributedTrainer.init(allocator, half_dim, num_layers, 1, 10_000_000_000, 1);
    defer trainer.deinit();
    try trainer.trainStep();
}
