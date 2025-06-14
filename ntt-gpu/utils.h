#ifndef UTILS_H
#define UTILS_H

#include <cuda_fp16.h>

__global__ void float_to_half(const float* in, __half* out, int n);
__global__ void half_to_float(const __half* in, float* out, int n);

#endif 