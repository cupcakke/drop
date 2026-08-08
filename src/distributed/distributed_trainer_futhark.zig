const std = @import("std");
const PackedRSFState = @import("../processor/rsf.zig").PackedRSFState;
pub const DistributedTrainer = struct {
    state: PackedRSFState,
    world_size: usize,
    rank: usize,
    max_epochs: usize,
    max_tokens: usize,
    pub fn init(allocator: std.mem.Allocator, half_dim: usize, num_layers: usize, world_size: usize, max_tokens: usize, max_epochs: usize) !DistributedTrainer {
        const state = try PackedRSFState.init(allocator, half_dim, num_layers, .{});
        return DistributedTrainer{
            .state = state,
            .world_size = world_size,
            .rank = 0,
            .max_epochs = max_epochs,
            .max_tokens = max_tokens,
        };
    }
    pub fn deinit(self: *DistributedTrainer) void {
        self.state.deinit();
    }
    pub fn trainStep(self: *DistributedTrainer) !void {
        _ = self;
    }
};
