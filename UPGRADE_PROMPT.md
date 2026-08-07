# JAIDE Triple-Signal 8-GPU Training Upgrade

I want to upgrade the JAIDE training system so that every training step produces three gradient signals (forward prediction, reconstruction, combined embedding), and the system runs across 8 GPUs on a single Modal node, so that a model capable of structured response generation converges within 1–2 hours of GPU time.

---

## Constraints

- The JAIDE architecture is RSF (Reversible Sparse Flow) + OFTB (Orthogonal Fixed-basis Transform). It contains no transformers, CNNs, RNNs, or perceptrons. No external model weights are used.
- All Zig code must compile with `zig build -Dgpu=true -Doptimize=ReleaseSafe` using Zig 0.14.1.
- All Futhark code must compile with `futhark cuda --library` using Futhark 0.26.4.
- No placeholder, mock, simulated, or stub code. Every function must be complete and correct.
- The JAIDE naming constraint is in effect: standard ML/DL jargon words (neural, neuron, layer [as a concept name], weight [as a noun in identifiers], gradient [as a noun in identifiers], etc.) must not appear in new identifier names. Use architecture-specific terms: `rsf`, `oftb`, `accel`, `layer_index`, `flow`, `spectral`, `delta`.

---

## Architecture Background

`weights_s` and `weights_t` for each RSF layer are `[half][half+1]f16` where `half = model_dim / 2`. With `model_dim=5120`, each matrix is `[2560][2561]f16`.

The forward pass for one RSF layer computes:
```
y1 = x1 * exp(clamp(ws_body @ x2 + ws_bias))   // scale stream
y2 = x2 + wt_body @ y1 + wt_bias               // translate stream
```

The inverse (`batch_rsf_inverse`, already implemented in `src/hw/accel/main.fut` at line 167) computes exactly:
```
x2 = y2 - wt_body @ y1 - wt_bias
x1 = y1 / exp(clamp(ws_body @ x2 + ws_bias))
```

OFTB is an orthogonal butterfly transform. `batch_oftb_forward` and `batch_oftb_backward` are exact inverses of each other (already implemented).

The current `trainingStep` in `src/hw/accel/accel_interface.zig` (function at line 700):
1. Runs the full forward stack (all layers, each RSF then OFTB).
2. Computes masked MSE loss via `futhark_entry_batch_compute_loss_masked`.
3. Seeds the gradient via `futhark_entry_compute_initial_grad_l2_masked`.
4. Runs the full backward stack in reverse: for each layer, calls `futhark_entry_batch_oftb_backward`, `futhark_entry_batch_rsf_inverse`, `futhark_entry_batch_oftb_backward` again on the gradient, `futhark_entry_batch_gradients_full`, then `sfdUpdateMat` for weight update.
5. At the end of the backward loop, `current_act` holds the reconstructed input `x_hat = f^{-1}(y)` across the full stack, and `grad_out` holds the gradient of the forward loss with respect to the reconstructed input.
6. Returns `TrainingStepResult { loss: f16, input_gradient: FutharkArray3DF16 }`.

**Key insight exploited by this upgrade:** At the end of the backward loop in step 5, `current_act` is already the full-stack reconstruction of the original input. Computing `MSE(current_act, inputs)` is one additional Futhark call — zero extra layer passes. The reconstruction gradient with respect to the embedding is `2 * alpha * (x_hat - x) / valid_token_count`, which can be added to `grad_out` before returning it as `input_gradient`. This gives the embedding update a combined signal from both the forward prediction loss and the reconstruction consistency loss, at the cost of one kernel call per step.

---

## File 1: `src/hw/accel/main.fut`

Add the following entry after the existing `compute_initial_grad_l2_masked` entry (line 233). Do not modify any existing entries.

```futhark
-- Adds the reconstruction gradient (alpha * 2 * (reconstructed - original) / count)
-- to an existing gradient tensor, masked by sequence lengths.
-- reconstructed: the full-stack inverse output (x_hat)
-- original: the original input to the forward stack (x)
-- Modifies forward_grad in-place by accumulation.
entry batch_add_reconstruction_grad_masked [batch_size][seq_len][d]
  (forward_grad: [batch_size][seq_len][d]f16)
  (reconstructed: [batch_size][seq_len][d]f16)
  (original: [batch_size][seq_len][d]f16)
  (lengths: [batch_size]i64)
  (alpha: f16)
  : *[batch_size][seq_len][d]f16 =
  let valid_tokens = i64.sum (map (\length -> i64.max 0 (i64.min seq_len length)) lengths)
  let count_f16 = f16.i64 (if valid_tokens > 0 then valid_tokens * d else 1)
  in map2 (\length bi ->
    let fg = forward_grad[bi]
    let rc = reconstructed[bi]
    let og = original[bi]
    in map (\j ->
      let active = j < i64.max 0 (i64.min seq_len length)
      in map3 (\f r o ->
        if active then
          let diff = r f16.- o
          let safe_diff = if f16.isnan diff || f16.isinf diff
                          then f16.i32 0
                          else f16.max (f16.f32 (-100.0)) (f16.min (f16.f32 100.0) diff)
          in f f16.+ alpha f16.* (f16.f32 2.0) f16.* safe_diff f16./ count_f16
        else f
      ) fg[j] rc[j] og[j]
    ) (iota seq_len)
  ) lengths (iota batch_size)

-- Computes MSE reconstruction loss between the full-stack inverse output and
-- the original input, masked by sequence lengths.
entry batch_compute_reconstruction_loss_masked [batch_size][seq_len][d]
  (reconstructed: [batch_size][seq_len][d]f16)
  (original: [batch_size][seq_len][d]f16)
  (lengths: [batch_size]i64)
  : f16 =
  let squared_diff_f32 = map2 (\length bi ->
    let rc = reconstructed[bi]
    let og = original[bi]
    in map (\j ->
      let active = j < i64.max 0 (i64.min seq_len length)
      in map2 (\r o ->
        if active then
          let diff = f32.f16 r - f32.f16 o
          in if f32.isnan diff || f32.isinf diff then 0f32 else diff * diff
        else 0f32
      ) rc[j] og[j]
    ) (iota seq_len)
  ) lengths (iota batch_size)
  let valid_tokens = i64.sum (map (\length -> i64.max 0 (i64.min seq_len length)) lengths)
  let count = valid_tokens * d
  let total = f32.sum (flatten (flatten squared_diff_f32))
  let safe_total = if f32.isnan total || f32.isinf total then 0f32 else total
  in if count <= 0
     then f16.i32 0
     else f16.f32 (safe_total / f32.i64 count)
```

---

## File 2: `src/hw/accel/accel_interface.zig`

### 2a. Extend `TrainingStepResult` (currently at line 546)

Replace:
```zig
pub const TrainingStepResult = struct {
    loss: f16,
    input_gradient: FutharkArray3DF16,
};
```
With:
```zig
pub const TrainingStepResult = struct {
    loss: f16,
    reconstruction_loss: f16,
    input_gradient: FutharkArray3DF16,
};
```

### 2b. Change `trainingStep` signature (currently at line 700)

Replace the current signature:
```zig
pub fn trainingStep(
    self: *Self,
    inputs: *FutharkArray3DF16,
    targets: *FutharkArray3DF16,
    sequence_lengths: []const usize,
    learning_rate: f16,
    momentum: f16,
) AccelError!TrainingStepResult
```
With:
```zig
pub fn trainingStep(
    self: *Self,
    inputs: *FutharkArray3DF16,
    targets: *FutharkArray3DF16,
    sequence_lengths: []const usize,
    learning_rate: f16,
    momentum: f16,
    reconstruction_alpha: f16,
) AccelError!TrainingStepResult
```

### 2c. After the backward loop and before returning

The backward loop currently ends at the block beginning with `if (current_act_owned) {` (line 959 in the pre-edit file). After `grad_out` and `current_act` are fully computed at the end of the backward loop and before any existing cleanup of `current_act`, insert the following logic:

```zig
// Reconstruction loss: MSE between the full-stack inverse output (current_act)
// and the original inputs. current_act at this point equals f^{-1}(y) computed
// for free during the backward stack traversal.
var recon_loss_bits: u16 = 0;
const recon_result = futhark.futhark_entry_batch_compute_reconstruction_loss_masked(
    self.ctx.ctx,
    &recon_loss_bits,
    current_act,
    inputs.arr,
    lengths_array.arr,
);
if (recon_result != 0) {
    const error_string = futhark.futhark_context_get_error(self.ctx.ctx);
    if (error_string) |message| std.debug.print(
        "[Futhark batch_compute_reconstruction_loss_masked error] {s}\n",
        .{std.mem.span(message)},
    );
    // Non-fatal: reconstruction loss failure does not abort training.
    recon_loss_bits = 0;
}
const reconstruction_loss: f16 = @bitCast(recon_loss_bits);

// If reconstruction_alpha > 0, add reconstruction gradient to grad_out.
// This augments the embedding gradient signal at zero extra layer-pass cost.
const recon_alpha_bits: u16 = @bitCast(reconstruction_alpha);
const recon_alpha_nonzero = recon_alpha_bits != 0 and !std.math.isNan(reconstruction_alpha);
if (recon_alpha_nonzero and grad_out != null and current_act != null) {
    var combined_grad: ?*futhark.struct_futhark_f16_3d = null;
    const add_recon_result = futhark.futhark_entry_batch_add_reconstruction_grad_masked(
        self.ctx.ctx,
        &combined_grad,
        grad_out,
        current_act,
        inputs.arr,
        lengths_array.arr,
        reconstruction_alpha,
    );
    if (add_recon_result == 0 and combined_grad != null) {
        if (grad_out) |g| _ = futhark.futhark_free_f16_3d(self.ctx.ctx, g);
        grad_out = combined_grad;
    } else {
        std.debug.print("[trainingStep] WARN: batch_add_reconstruction_grad_masked failed, using forward grad only\n", .{});
        if (combined_grad) |g| _ = futhark.futhark_free_f16_3d(self.ctx.ctx, g);
    }
}
```

### 2d. Change the return statement of `trainingStep`

The current return (after `grad_out` is wrapped into a `FutharkArray3DF16`) is:
```zig
return TrainingStepResult{
    .loss = loss,
    .input_gradient = ...,
};
```
Change to:
```zig
return TrainingStepResult{
    .loss = loss,
    .reconstruction_loss = reconstruction_loss,
    .input_gradient = ...,
};
```

### 2e. Update the one call site of `trainingStep` in `distributed_trainer_futhark.zig` (line 1871)

Add the new `reconstruction_alpha` argument. Its value is read from `self.config.reconstruction_alpha` cast to f16. The caller computes the effective alpha based on `self.global_step` and phase thresholds — see File 3 below.

---

## File 3: `src/distributed/distributed_trainer_futhark.zig`

### 3a. Extend `TrainerConfig` (line 137)

After `relational_pass_interval: usize = 50,`, add:
```zig
reconstruction_alpha: f32 = 0.3,
phase_a_steps: u64 = 500,
phase_b_steps: u64 = 2000,
```

`phase_a_steps`: number of steps during which the reconstruction signal is used with `reconstruction_alpha=1.0` and forward loss is computed but its gradient is NOT added to the embedding update (pure reconstruction phase). During Phase A, `effective_reconstruction_alpha = 1.0`.

`phase_b_steps`: after Phase A, for the next `phase_b_steps` steps, both signals are active. `effective_reconstruction_alpha` linearly ramps from `1.0` down to `config.reconstruction_alpha`. After Phase A + Phase B, `effective_reconstruction_alpha = config.reconstruction_alpha` for all remaining steps.

### 3b. Extend the local `StepResult` struct inside `distributed_trainer_futhark.zig`

Locate the existing `StepResult` definition (it has fields `loss: f32` and `sample_weight: f64`). Add:
```zig
reconstruction_loss: f32,
```

### 3c. Modify `trainStepFuthark` (line 1685)

Inside `trainStepFuthark`, before the call to `self.accelerator.trainingStep`, compute the effective reconstruction alpha:

```zig
const step_for_phase = self.global_step;
const effective_reconstruction_alpha: f32 = blk: {
    if (step_for_phase < self.config.phase_a_steps) {
        break :blk 1.0;
    } else if (step_for_phase < self.config.phase_a_steps + self.config.phase_b_steps) {
        const ramp_steps = self.config.phase_b_steps;
        const elapsed = step_for_phase - self.config.phase_a_steps;
        const t = @as(f32, @floatFromInt(elapsed)) / @as(f32, @floatFromInt(ramp_steps));
        break :blk 1.0 - t * (1.0 - self.config.reconstruction_alpha);
    } else {
        break :blk self.config.reconstruction_alpha;
    }
};
const effective_reconstruction_alpha_f16 = try checkedF32ToF16(
    @max(0.0, @min(1.0, effective_reconstruction_alpha)),
);
```

Pass `effective_reconstruction_alpha_f16` to `self.accelerator.trainingStep(...)`.

Change the call to use the new signature and capture `reconstruction_loss`:
```zig
var training_result = try self.accelerator.trainingStep(
    &tensors.inputs,
    &tensors.targets,
    real_sequence_lengths,
    learning_rate,
    momentum,
    effective_reconstruction_alpha_f16,
);
```

After the call, extract `reconstruction_loss` from `training_result.reconstruction_loss` and reduce it across ranks the same way `local_loss` is reduced:
```zig
const local_reconstruction_loss: f32 = @floatCast(training_result.reconstruction_loss);
var reduced_reconstruction_loss = local_reconstruction_loss;
if (self.coordinator.world_size > 1) {
    var global_recon_loss = [1]f32{local_reconstruction_loss * local_fraction};
    try self.allReduceFloat32Values(global_recon_loss[0..]);
    reduced_reconstruction_loss = global_recon_loss[0];
}
if (!std.math.isFinite(reduced_reconstruction_loss)) reduced_reconstruction_loss = 0.0;
```

Return `StepResult{ .loss = reduced_loss, .reconstruction_loss = reduced_reconstruction_loss, .sample_weight = ... }`.

### 3d. Modify `trainEpoch` logging (line 1358)

Replace:
```zig
std.debug.print("[Step {d}] Loss: {d:.6}\n", .{ self.global_step, step_result.loss });
```
With:
```zig
std.debug.print("[Step {d}] Loss: {d:.6} | Recon: {d:.6}\n", .{
    self.global_step,
    step_result.loss,
    step_result.reconstruction_loss,
});
```

---

## File 4: `src/main_distributed_futhark.zig`

### 4a. Parse three new environment variables

After the existing `JAIDE_RELATIONAL_PASS_INTERVAL` parsing block (ends around line 925), add parsing for the following three env vars. Use the exact same pattern (getEnvVarOwned → parse → validate → defer free):

**`JAIDE_RECONSTRUCTION_ALPHA`** → `f32`, default `0.3`. Must satisfy `value >= 0.0 and value <= 1.0`. If parsing fails or value is out of range, print error and return `error.InvalidConfig`.

**`JAIDE_PHASE_A_STEPS`** → `u64`, default `500`. Must be `>= 0`. If parsing fails, print error and return `error.InvalidConfig`.

**`JAIDE_PHASE_B_STEPS`** → `u64`, default `2000`. Must be `>= 0`. If parsing fails, print error and return `error.InvalidConfig`.

### 4b. Pass new values to `TrainerConfig`

At the point where `TrainerConfig` is initialized (locate by searching for `TrainerConfig{` in main_distributed_futhark.zig), add:
```zig
.reconstruction_alpha = reconstruction_alpha,
.phase_a_steps = phase_a_steps,
.phase_b_steps = phase_b_steps,
```

---

## File 5: `scripts/modal_status_bench.py`

### 5a. New top-level constants (after line 49, before `app = modal.App(APP_NAME)`)

```python
NUM_GPUS = int(os.environ.get("JAIDE_BENCH_NUM_GPUS", "8"))
RECONSTRUCTION_ALPHA = os.environ.get("JAIDE_BENCH_RECONSTRUCTION_ALPHA", "0.3")
PHASE_A_STEPS = int(os.environ.get("JAIDE_BENCH_PHASE_A_STEPS", "500"))
PHASE_B_STEPS = int(os.environ.get("JAIDE_BENCH_PHASE_B_STEPS", "2000"))
```

### 5b. Change existing defaults

Change line 38: `GPU_SPEC = os.environ.get("JAIDE_BENCH_GPU", "B200+:8")`
Change line 43: `BATCH_SIZE = int(os.environ.get("JAIDE_BENCH_BATCH", "64"))`
Change line 45: `SAMPLE_CAP = int(os.environ.get("JAIDE_BENCH_SAMPLE_CAP", "2000000"))`

### 5c. Add `_run_multirank` function

Add a new top-level function `_run_multirank` between the existing `_run` and `_write_report` functions:

```python
def _run_multirank(
    cmd: List[str],
    cwd: str,
    base_env: Dict[str, str],
    num_gpus: int,
    nccl_id_path: str,
    timeout: int,
) -> Tuple[int, str, float]:
    """
    Spawns `num_gpus` subprocesses of `cmd`, one per rank. Each subprocess
    receives WORLD_SIZE, RANK, LOCAL_RANK set to the corresponding rank index.
    Rank 0 generates the NCCL unique ID via file exchange (the binary handles
    this internally). All ranks' stdout/stderr are interleaved into a single
    combined output string with per-rank prefixes. Returns (combined_rc, combined_out, elapsed).
    combined_rc is 0 only if all ranks exit 0.
    """
    import selectors as _sel

    if num_gpus <= 0:
        raise ValueError("num_gpus must be >= 1")

    t0 = time.monotonic()
    deadline = t0 + timeout

    for stale in [nccl_id_path, nccl_id_path + ".ready"]:
        p = Path(stale)
        if p.exists():
            p.unlink()

    procs: List[subprocess.Popen] = []
    rank_envs: List[Dict[str, str]] = []

    for rank_idx in range(num_gpus):
        env = base_env.copy()
        env["WORLD_SIZE"] = str(num_gpus)
        env["RANK"] = str(rank_idx)
        env["LOCAL_RANK"] = str(rank_idx)
        env["JAIDE_NCCL_ID_PATH"] = nccl_id_path
        rank_envs.append(env)

    selector = _sel.DefaultSelector()
    output_chunks: List[bytes] = []
    timed_out = False
    fd_to_rank: Dict[int, int] = {}

    try:
        for rank_idx in range(num_gpus):
            proc = subprocess.Popen(
                cmd,
                cwd=cwd,
                env=rank_envs[rank_idx],
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                stdin=subprocess.DEVNULL,
                bufsize=0,
                start_new_session=True,
            )
            if proc.stdout is None:
                for p in procs:
                    _terminate_process_group(p)
                raise RuntimeError(f"rank {rank_idx} stdout pipe not created")
            procs.append(proc)
            selector.register(proc.stdout, _sel.EVENT_READ)
            fd_to_rank[proc.stdout.fileno()] = rank_idx

        while True:
            now = time.monotonic()
            if now >= deadline:
                timed_out = True
                for proc in procs:
                    _terminate_process_group(proc)
                break

            all_done = all(p.poll() is not None for p in procs)
            if all_done:
                for rank_idx, proc in enumerate(procs):
                    if proc.stdout:
                        remaining = proc.stdout.read()
                        if remaining:
                            prefix = f"[rank {rank_idx}] ".encode()
                            output_chunks.append(prefix + remaining)
                break

            events = selector.select(timeout=min(1.0, deadline - now))
            for key, _ in events:
                try:
                    chunk = os.read(key.fd, 65536)
                except OSError:
                    chunk = b""
                if not chunk:
                    selector.unregister(key.fileobj)
                    continue
                rank_idx = fd_to_rank.get(key.fd, -1)
                prefix = f"[rank {rank_idx}] ".encode()
                lines = chunk.splitlines(keepends=True)
                for line in lines:
                    output_chunks.append(prefix + line)
                sys.stdout.buffer.write(chunk)
                sys.stdout.buffer.flush()

        for proc in procs:
            if proc.poll() is None:
                proc.wait()

    finally:
        selector.close()
        for proc in procs:
            if proc.stdout:
                proc.stdout.close()

    dt = time.monotonic() - t0
    combined_out = b"".join(output_chunks).decode("utf-8", errors="replace")
    returncodes = [p.returncode for p in procs]
    combined_rc = 0 if all(rc == 0 for rc in returncodes) else max(
        (rc for rc in returncodes if rc != 0), default=1
    )
    _log(f"multirank complete: ranks={num_gpus} rcs={returncodes} dt={dt:.2f}s")
    if timed_out:
        raise subprocess.TimeoutExpired(cmd, timeout, output=combined_out.encode("utf-8"))
    return combined_rc, combined_out, dt
```

### 5d. Modify `run_gpu_train_and_infer` function

Inside `run_gpu_train_and_infer`, in the block that sets up `train_env` (currently lines 504–534), make the following changes:

1. Change `train_env["WORLD_SIZE"] = "1"` to `train_env["WORLD_SIZE"] = str(NUM_GPUS)`.
2. Remove `train_env["RANK"] = "0"` — rank is now set per-process inside `_run_multirank`.
3. Keep `train_env["MASTER_ADDR"] = "127.0.0.1"` and `train_env["MASTER_PORT"] = "29500"`.
4. Add after the existing JAIDE_* var block:
```python
train_env["JAIDE_RECONSTRUCTION_ALPHA"] = RECONSTRUCTION_ALPHA
train_env["JAIDE_PHASE_A_STEPS"] = str(PHASE_A_STEPS)
train_env["JAIDE_PHASE_B_STEPS"] = str(PHASE_B_STEPS)
```

5. Replace the existing single-process `_run` call for training (currently `rc_c, out_c, _ = _run([str(distributed_bin)], ...)`) with:
```python
rc_c, out_c, _ = _run_multirank(
    cmd=[str(distributed_bin)],
    cwd=project_dir,
    base_env=train_env,
    num_gpus=NUM_GPUS,
    nccl_id_path="/tmp/jaide_nccl_id",
    timeout=72000,
)
```

### 5e. Update `main()` local_entrypoint validation

After the existing validation block (lines 732–749), add:

```python
if NUM_GPUS <= 0:
    raise ValueError("JAIDE_BENCH_NUM_GPUS must be a positive integer")
try:
    _recon_alpha_val = float(RECONSTRUCTION_ALPHA)
    if not (0.0 <= _recon_alpha_val <= 1.0):
        raise ValueError()
except ValueError:
    raise ValueError("JAIDE_BENCH_RECONSTRUCTION_ALPHA must be a float in [0.0, 1.0]")
if PHASE_A_STEPS < 0:
    raise ValueError("JAIDE_BENCH_PHASE_A_STEPS must be >= 0")
if PHASE_B_STEPS < 0:
    raise ValueError("JAIDE_BENCH_PHASE_B_STEPS must be >= 0")
```

---

## Futhark C Binding Requirements

After adding the two new entries to `main.fut`, the Futhark CUDA compiler generates corresponding C function declarations in the output header. These follow the naming pattern:
- `futhark_entry_batch_add_reconstruction_grad_masked`
- `futhark_entry_batch_compute_reconstruction_loss_masked`

In `src/hw/accel/accel_interface.zig`, add `extern fn` declarations for both using the same pattern as the existing `futhark_entry_batch_compute_loss_masked` declaration. The signatures follow Futhark's generated C API convention: each array parameter becomes a `?*futhark.struct_futhark_f16_Nd` pointer, scalar `f16` parameters become `u16` (bit-cast), and output arrays are written via pointer-to-pointer.

Locate the section in `accel_interface.zig` where Futhark entry function declarations appear (search for `extern fn futhark_entry_batch_compute_loss_masked`) and add the two new declarations adjacent to it, following the exact same declaration style used for the existing entries.

---

## Success Criteria

1. `zig build -Dgpu=true -Doptimize=ReleaseSafe` completes with zero errors and zero warnings.
2. `futhark cuda --library src/hw/accel/main.fut -o src/hw/accel/main_gpu` completes with zero errors.
3. `uv run modal run --detach scripts/modal_status_bench.py` launches 8 GPU processes on a single node. All 8 ranks initialize NCCL successfully and produce `[Rank N] GPU coordinator initialized` log lines for N in 0..7.
4. Each training step log line contains both `Loss:` and `Recon:` fields.
5. During Phase A (first 500 steps): `Recon:` value decreases monotonically or is stable. `Loss:` may not decrease — this is expected.
6. After Phase A + Phase B (after step 2500): both `Loss:` and `Recon:` decrease over training.
7. Checkpoint is written to `/checkpoints/model.ckpt` at end of training (existing `saveCheckpoint` call unchanged).
8. `checkpoint_volume.commit()` is called exactly once after training completes (existing behavior, unchanged).
9. Effective batch size across 8 GPUs is 8 × 64 = 512 samples per step.
10. Total GPU training time for 1 epoch over 2,000,000 samples at batch 512 is within 1–2 hours on 8× B200 GPUs.
