#include "utils.h"

__global__ void float_to_half(const float* in, __half* out, int n) {
    int i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i < n) {
        out[i] = __float2half(in[i]);
    }
}

__global__ void half_to_float(const __half* in, float* out, int n) {
    int i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i < n) {
        out[i] = __half2float(in[i]);
    }
} 