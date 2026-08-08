const std = @import("std");
const Allocator = std.mem.Allocator;
const Tensor = @import("../core/tensor.zig").Tensor;
const memory = @import("../core/memory.zig");
const accel = @import("../hw/accel/accel_interface.zig");
const OFTB = @import("oftb.zig").OFTB;
const types = @import("../core/types.zig");
const Thread = std.Thread;
const LAYER_TARGET_SPECTRAL_NORM: f32 = 0.9;
const LAYER_SPECTRAL_POWER_ITERATIONS: usize = 30;
const MODEL_DIM_3B: usize = 11200;
const MODEL_LAYERS: usize = 12;
const MAX_EPOCHS: usize = 1;
const MAX_TOKENS: usize = 10_000_000_000;
fn spectralNormPowerIteration(allocator: Allocator, data: []const f32, rows: usize, cols: usize, iterations: usize, seed: u64) !f32 {
    const u = try allocator.alloc(f32, rows);
    defer allocator.free(u);
    const v = try allocator.alloc(f32, cols);
    defer allocator.free(v);
    var prng = types.PRNG.init(seed);
    for (v) |*x| x.* = prng.float() * 2.0 - 1.0;
    var iter: usize = 0;
    while (iter < iterations) : (iter += 1) {
        for (u) |*x| x.* = 0.0;
        var i: usize = 0;
        while (i < rows) : (i += 1) {
            const row = data[i * cols .. i * cols + cols];
            var sum: f32 = 0.0;
            var j: usize = 0;
            while (j < cols) : (j += 1) sum += row[j] * v[j];
            u[i] = sum;
        }
        var u_norm_sq: f32 = 0.0;
        for (u) |x| u_norm_sq += x * x;
        const u_norm = @sqrt(u_norm_sq);
        if (u_norm > 1e-12) {
            for (u) |*x| x.* /= u_norm;
        }
        for (v) |*x| x.* = 0.0;
        i = 0;
        while (i < rows) : (i += 1) {
            const row = data[i * cols .. i * cols + cols];
            const ui = u[i];
            var j: usize = 0;
            while (j < cols) : (j += 1) v[j] += row[j] * ui;
        }
        var v_norm_sq: f32 = 0.0;
        for (v) |x| v_norm_sq += x * x;
        const v_norm = @sqrt(v_norm_sq);
        if (v_norm > 1e-12) {
            for (v) |*x| x.* /= v_norm;
        }
    }
    var sigma: f64 = 0.0;
    var i: usize = 0;
    while (i < rows) : (i += 1) {
        const row = data[i * cols .. i * cols + cols];
        var partial: f64 = 0.0;
        var j: usize = 0;
        while (j < cols) : (j += 1) partial += @as(f64, row[j]) * @as(f64, v[j]);
        sigma += @as(f64, u[i]) * partial;
    }
    const sigma_f32: f32 = @floatCast(sigma);
    return if (sigma_f32 >= 0) sigma_f32 else -sigma_f32;
}
fn constrainSpectralNorm(allocator: Allocator, weight: *Tensor, rows: usize, cols: usize, target: f32, seed: u64) !void {
    const norm = try spectralNormPowerIteration(allocator, weight.data, rows, cols, LAYER_SPECTRAL_POWER_ITERATIONS, seed);
    if (norm > target and norm > 1e-12) {
        const factor = target / norm;
        for (weight.data) |*x| x.* *= factor;
    }
}
pub const RSFLayerConfig = struct {
    clip_min: f32 = -5.0,
    clip_max: f32 = 5.0,
    seed_offset: u64 = 0,
    grad_mean: bool = true,
};
pub const RSFConfig = struct {
    clip_min: f32 = -5.0,
    clip_max: f32 = 5.0,
    grad_mean: bool = true,
    max_dim: usize = MODEL_DIM_3B,
    max_layers: usize = MODEL_LAYERS,
};
const SAVE_VERSION: u32 = 5;
var scratch_gpa_backing = std.heap.GeneralPurposeAllocator(.{}){};
fn scratchAllocator() Allocator {
    return scratch_gpa_backing.allocator();
}
fn checkedMul(a: usize, b: usize) !usize {
    return std.math.mul(usize, a, b) catch return error.Overflow;
}
fn checkedMulU64(a: u64, b: u64) !u64 {
    return std.math.mul(u64, a, b) catch return error.Overflow;
}
fn checkedAddU64(a: u64, b: u64) !u64 {
    return std.math.add(u64, a, b) catch return error.Overflow;
}
fn checkedCastU64ToUsize(v: u64) !usize {
    if (v > std.math.maxInt(usize)) return error.TooLarge;
    return @intCast(v);
}
fn validateClipRange(clip_min: f32, clip_max: f32) !void {
    if (!std.math.isFinite(clip_min) or !std.math.isFinite(clip_max)) return error.NonFinite;
    if (!(clip_min < clip_max)) return error.InvalidConfig;
    if (clip_max > 20.0 or clip_min < -20.0) return error.InvalidConfig;
}
fn validateComparisonTolerances(abs_tol: f32, rel_tol: f32) !void {
    if (!std.math.isFinite(abs_tol) or !std.math.isFinite(rel_tol)) return error.InvalidTolerance;
    if (abs_tol < 0.0 or rel_tol < 0.0) return error.InvalidTolerance;
}
fn validateTensor2D(t: *const Tensor) !void {
    if (t.shape.dims.len != 2) return error.ShapeMismatch;
    const expected = try checkedMul(t.shape.dims[0], t.shape.dims[1]);
    if (t.data.len != expected) return error.DataLengthMismatch;
}
fn validateTensor2DShape(t: *const Tensor, rows: usize, cols: usize) !void {
    if (t.shape.dims.len != 2 or t.shape.dims[0] != rows or t.shape.dims[1] != cols) return error.ShapeMismatch;
    const expected = try checkedMul(rows, cols);
    if (t.data.len != expected) return error.DataLengthMismatch;
}
fn tensorHasShape(t: *const Tensor, rows: usize, cols: usize) bool {
    return t.shape.dims.len == 2 and t.shape.dims[0] == rows and t.shape.dims[1] == cols;
}
fn tensorsSameShape(a: *const Tensor, b: *const Tensor) bool {
    return a.shape.dims.len == 2 and b.shape.dims.len == 2 and a.shape.dims[0] == b.shape.dims[0] and a.shape.dims[1] == b.shape.dims[1];
}
fn ensureFiniteSlice(data: []const f32) !void {
    for (data) |v| {
        if (!std.math.isFinite(v)) return error.NonFinite;
    }
}
fn zeroTensor(t: *Tensor) void {
    @memset(t.data, @as(f32, 0.0));
}
fn tensorsOverlap(a: *const Tensor, b: *const Tensor) bool {
    if (a.data.len == 0 or b.data.len == 0) return false;
    const a_start: usize = @intFromPtr(a.data.ptr);
    const b_start: usize = @intFromPtr(b.data.ptr);
    const a_bytes = std.math.mul(usize, a.data.len, @sizeOf(f32)) catch return true;
    const b_bytes = std.math.mul(usize, b.data.len, @sizeOf(f32)) catch return true;
    const a_end = std.math.add(usize, a_start, a_bytes) catch return true;
    const b_end = std.math.add(usize, b_start, b_bytes) catch return true;
    return a_start < b_end and b_start < a_end;
}
fn tensorClone(allocator: Allocator, src: *const Tensor) !Tensor {
    try validateTensor2D(src);
    var dst = try Tensor.init(allocator, &.{ src.shape.dims[0], src.shape.dims[1] });
    errdefer dst.deinit();
    @memcpy(dst.data, src.data);
    return dst;
}
fn tensorAllCloseEq(a: *const Tensor, b: *const Tensor, abs_tol: f32, rel_tol: f32) !bool {
    try validateComparisonTolerances(abs_tol, rel_tol);
    try validateTensor2D(a);
    try validateTensor2D(b);
    if (!tensorsSameShape(a, b)) return false;
    var i: usize = 0;
    while (i < a.data.len) : (i += 1) {
        const av = a.data[i];
        const bv = b.data[i];
        if (!std.math.isFinite(av) or !std.math.isFinite(bv)) return false;
        const diff = @abs(av - bv);
        const scale = @max(@abs(av), @abs(bv));
        if (diff > abs_tol + rel_tol * scale) return false;
    }
    return true;
}
fn validateModelConfigValues(dim: usize, num_layers: usize, cfg: RSFConfig) !void {
    if (dim == 0) return error.InvalidDimension;
    if (num_layers == 0) return error.InvalidLayerCount;
    try validateClipRange(cfg.clip_min, cfg.clip_max);
    if (cfg.max_dim == 0 or cfg.max_layers == 0) return error.InvalidConfig;
    if (dim > cfg.max_dim or num_layers > cfg.max_layers) return error.InvalidConfig;
}
pub const PackedRSFState = struct {
    weights_s: []f16,
    weights_t: []f16,
    velocity_s: []f16,
    velocity_t: []f16,
    num_layers: usize,
    half_dim: usize,
    allocator: Allocator,
    pub fn init(allocator: Allocator, half_dim: usize, num_layers: usize, cfg: RSFConfig) !PackedRSFState {
        try validateModelConfigValues(half_dim, num_layers, cfg);
        const per_mat = @as(usize, half_dim) * @as(usize, half_dim + 1);
        const total = per_mat * 4 * num_layers;
        const weights_s = try allocator.alloc(f16, total);
        errdefer allocator.free(weights_s);
        const weights_t = try allocator.alloc(f16, total);
        errdefer allocator.free(weights_t);
        const velocity_s = try allocator.alloc(f16, total);
        errdefer allocator.free(velocity_s);
        const velocity_t = try allocator.alloc(f16, total);
        errdefer allocator.free(velocity_t);
        @memset(weights_s, @as(f16, 0.0));
        @memset(weights_t, @as(f16, 0.0));
        @memset(velocity_s, @as(f16, 0.0));
        @memset(velocity_t, @as(f16, 0.0));
        return PackedRSFState{
            .weights_s = weights_s,
            .weights_t = weights_t,
            .velocity_s = velocity_s,
            .velocity_t = velocity_t,
            .num_layers = num_layers,
            .half_dim = half_dim,
            .allocator = allocator,
        };
    }
    pub fn deinit(self: *PackedRSFState) void {
        self.allocator.free(self.weights_s);
        self.allocator.free(self.weights_t);
        self.allocator.free(self.velocity_s);
        self.allocator.free(self.velocity_t);
    }
    pub fn getLayerS(self: *const PackedRSFState, layer: usize) []f16 {
        const per_mat = @as(usize, self.half_dim) * @as(usize, self.half_dim + 1);
        const offset = per_mat * layer;
        return self.weights_s[offset .. offset + per_mat];
    }
    pub fn getLayerT(self: *const PackedRSFState, layer: usize) []f16 {
        const per_mat = @as(usize, self.half_dim) * @as(usize, self.half_dim + 1);
        const offset = per_mat * self.num_layers + per_mat * layer;
        return self.weights_t[offset .. offset + per_mat];
    }
};
const LayerCore = struct {
    s_weight: Tensor,
    t_weight: Tensor,
    s_weight_grad: ?Tensor,
    t_weight_grad: ?Tensor,
    dim: usize,
    allocator: Allocator,
    clip_min: f32,
    clip_max: f32,
    grad_mean: bool,
    rwlock: Thread.RwLock,
    fn initOwned(allocator: Allocator, dim: usize, config: RSFLayerConfig) !LayerCore {
        if (dim == 0) return error.InvalidDimension;
        try validateClipRange(config.clip_min, config.clip_max);
        _ = try checkedMul(dim, dim + 1);
        const fan_in: f32 = @floatFromInt(dim);
        const fan_out: f32 = @floatFromInt(dim);
        const fan_sum = fan_in + fan_out;
        if (!(fan_sum > 0.0)) return error.InvalidDimension;
        const xavier_bound: f32 = @sqrt(6.0 / fan_sum);
        const weight_shape = [_]usize{ dim, dim + 1 };
        const seed1 = try checkedAddU64(42, config.seed_offset);
        const seed2 = try checkedAddU64(43, config.seed_offset);
        var s_w = try Tensor.randomUniform(allocator, &weight_shape, -xavier_bound, xavier_bound, seed1);
        errdefer s_w.deinit();
        var t_w = try Tensor.randomUniform(allocator, &weight_shape, -xavier_bound, xavier_bound, seed2);
        errdefer t_w.deinit();
        for (0..dim) |d| {
            s_w.data[d * (dim + 1) + dim] = 0.0;
            t_w.data[d * (dim + 1) + dim] = 0.0;
        }
        try constrainSpectralNorm(allocator, &s_w, dim, dim + 1, LAYER_TARGET_SPECTRAL_NORM, checkedAddU64(seed1, 9_000_000) catch seed1);
        try constrainSpectralNorm(allocator, &t_w, dim, dim + 1, LAYER_TARGET_SPECTRAL_NORM, checkedAddU64(seed2, 9_000_000) catch seed2);
        return LayerCore{
            .s_weight = s_w,
            .t_weight = t_w,
            .s_weight_grad = null,
            .t_weight_grad = null,
            .dim = dim,
            .allocator = allocator,
            .clip_min = config.clip_min,
            .clip_max = config.clip_max,
            .grad_mean = config.grad_mean,
            .rwlock = .{},
        };
    }
    fn deinitOwned(self: *LayerCore) void {
        self.s_weight.deinit();
        self.t_weight.deinit();
        if (self.s_weight_grad) |*g| g.deinit();
        if (self.t_weight_grad) |*g| g.deinit();
        self.s_weight_grad = null;
        self.t_weight_grad = null;
    }
    pub fn ensureGradients(self: *LayerCore) !void {
        const need_swg = self.s_weight_grad == null;
        const need_twg = self.t_weight_grad == null;
        if (!(need_swg or need_twg)) return;
        const weight_shape = [_]usize{ self.dim, self.dim + 1 };
        var swg_new: ?Tensor = null;
        var twg_new: ?Tensor = null;
        errdefer {
            if (swg_new) |*t| t.deinit();
            if (twg_new) |*t| t.deinit();
        }
        if (need_swg) swg_new = try Tensor.init(self.allocator, &weight_shape);
        if (need_twg) twg_new = try Tensor.init(self.allocator, &weight_shape);
        if (swg_new) |swg| @memset(swg.data, 0.0);
        if (twg_new) |twg| @memset(twg.data, 0.0);
        self.s_weight_grad = swg_new;
        self.t_weight_grad = twg_new;
    }
};
