pub const cudaError_t = c_uint;
pub const cudaSuccess: cudaError_t = 0;
pub const cudaErrorInvalidValue: cudaError_t = 1;
pub const cudaErrorMemoryAllocation: cudaError_t = 2;
pub const cudaErrorInitializationError: cudaError_t = 3;
pub const cudaErrorLaunchFailure: cudaError_t = 4;
pub const cudaErrorLaunchTimeout: cudaError_t = 6;
pub const cudaErrorLaunchOutOfResources: cudaError_t = 7;
pub const cudaErrorInvalidDeviceFunction: cudaError_t = 8;
pub const cudaErrorInvalidConfiguration: cudaError_t = 9;
pub const cudaErrorInvalidDevice: cudaError_t = 10;
pub const cudaErrorInvalidMemcpyDirection: cudaError_t = 21;

pub const cudaHostAllocDefault: c_uint = 0;
pub const cudaHostAllocPortable: c_uint = 1;
pub const cudaHostAllocMapped: c_uint = 2;
pub const cudaHostAllocWriteCombined: c_uint = 4;

pub const cudaMemcpyHostToHost: c_uint = 0;
pub const cudaMemcpyHostToDevice: c_uint = 1;
pub const cudaMemcpyDeviceToHost: c_uint = 2;
pub const cudaMemcpyDeviceToDevice: c_uint = 3;
pub const cudaMemcpyDefault: c_uint = 4;

pub const cudaStream_t = ?*anyopaque;

pub const CudaError = error{
    InvalidValue,
    MemoryAllocation,
    InitializationError,
    LaunchFailure,
    LaunchTimeout,
    LaunchOutOfResources,
    InvalidDeviceFunction,
    InvalidConfiguration,
    InvalidDevice,
    InvalidMemcpyDirection,
    HostAllocFailed,
    Unknown,
};

const RealApi = struct {
    pub extern "c" fn cudaHostAlloc(ptr: *?*anyopaque, size: usize, flags: c_uint) cudaError_t;
    pub extern "c" fn cudaFreeHost(ptr: ?*anyopaque) cudaError_t;
    pub extern "c" fn cudaMalloc(devPtr: *?*anyopaque, size: usize) cudaError_t;
    pub extern "c" fn cudaFree(devPtr: ?*anyopaque) cudaError_t;
    pub extern "c" fn cudaMemcpy(dst: ?*anyopaque, src: ?*const anyopaque, count: usize, kind: c_uint) cudaError_t;
    pub extern "c" fn cudaMemcpyAsync(dst: ?*anyopaque, src: ?*const anyopaque, count: usize, kind: c_uint, stream: cudaStream_t) cudaError_t;
    pub extern "c" fn cudaMemset(devPtr: ?*anyopaque, value: c_int, count: usize) cudaError_t;
    pub extern "c" fn cudaDeviceSynchronize() cudaError_t;
    pub extern "c" fn cudaStreamSynchronize(stream: cudaStream_t) cudaError_t;
    pub extern "c" fn cudaGetLastError() cudaError_t;
    pub extern "c" fn cudaPeekAtLastError() cudaError_t;
    pub extern "c" fn cudaGetErrorString(err: cudaError_t) [*:0]const u8;
    pub extern "c" fn cudaGetErrorName(err: cudaError_t) [*:0]const u8;
    pub extern "c" fn cudaStreamCreate(pStream: *cudaStream_t) cudaError_t;
    pub extern "c" fn cudaStreamDestroy(stream: cudaStream_t) cudaError_t;
    pub extern "c" fn cudaGetDeviceCount(count: *c_int) cudaError_t;
    pub extern "c" fn cudaSetDevice(device: c_int) cudaError_t;
    pub extern "c" fn cudaGetDevice(device: *c_int) cudaError_t;
};

/// CUDA symbols are declared unconditionally, but callers must keep use sites
/// behind a compile-time `gpu_enabled` branch.  This avoids linking fabricated
/// CPU-only CUDA implementations while retaining the real CUDA ABI for GPU
/// builds.

pub const cudaHostAlloc = RealApi.cudaHostAlloc;
pub const cudaFreeHost = RealApi.cudaFreeHost;
pub const cudaMalloc = RealApi.cudaMalloc;
pub const cudaFree = RealApi.cudaFree;
pub const cudaMemcpy = RealApi.cudaMemcpy;
pub const cudaMemcpyAsync = RealApi.cudaMemcpyAsync;
pub const cudaMemset = RealApi.cudaMemset;
pub const cudaDeviceSynchronize = RealApi.cudaDeviceSynchronize;
pub const cudaStreamSynchronize = RealApi.cudaStreamSynchronize;
pub const cudaGetLastError = RealApi.cudaGetLastError;
pub const cudaPeekAtLastError = RealApi.cudaPeekAtLastError;
pub const cudaGetErrorString = RealApi.cudaGetErrorString;
pub const cudaGetErrorName = RealApi.cudaGetErrorName;
pub const cudaStreamCreate = RealApi.cudaStreamCreate;
pub const cudaStreamDestroy = RealApi.cudaStreamDestroy;
pub const cudaGetDeviceCount = RealApi.cudaGetDeviceCount;
pub const cudaSetDevice = RealApi.cudaSetDevice;
pub const cudaGetDevice = RealApi.cudaGetDevice;
