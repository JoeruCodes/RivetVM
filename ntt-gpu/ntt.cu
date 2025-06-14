#include <iostream>
#include <vector>
#include <cmath>
#include <cassert>
#include <mma.h>
#include <cuda_fp16.h>
#include <iomanip>
#include "ntt.h"
#include "utils.h"

using namespace nvcuda;


const int WMMA_M = 16;
const int WMMA_N = 16;
const int WMMA_K = 16;


__device__ __forceinline__ float fast_fmod(float val, int p) {
    
    
    
    return val - p * floorf(val / p);
}


__global__ void fused_ntt_stage(const __half* matrix_in, 
                                __half* matrix_out, 
                                const __half* ntt_matrix, 
                                const __half* twiddles, 
                                int n1, int n2,
                                bool do_twiddle,
                                bool transpose_out,
                                int p) {
    int batch = blockIdx.z;

    
    
    const int in_rows = n1;
    const int in_cols = n2;
    const int out_rows = transpose_out ? n2 : n1;
    const int out_cols = transpose_out ? n1 : n2;
    
    int out_tile_row = blockIdx.y * WMMA_M;
    int out_tile_col = blockIdx.x * WMMA_N;

    
    
    
    
    
    int src_tile_row = out_tile_row;
    int src_tile_col = out_tile_col;
    
    if (out_tile_row >= out_rows || out_tile_col >= out_cols) return;

    
    
    
    
    
    
    const int mat_mul_size = transpose_out ? n1 : n2; 

    wmma::fragment<wmma::matrix_a, WMMA_M, WMMA_N, WMMA_K, __half, wmma::row_major> a_frag;
    wmma::fragment<wmma::matrix_b, WMMA_M, WMMA_N, WMMA_K, __half, wmma::row_major> b_frag;
    wmma::fragment<wmma::accumulator, WMMA_M, WMMA_N, WMMA_K, float> acc_frag;
    wmma::fragment<wmma::accumulator, WMMA_M, WMMA_N, WMMA_K, __half> res_frag;
    
    wmma::fill_fragment(acc_frag, 0.0f);

    
    for (int k_tile = 0; k_tile < mat_mul_size; k_tile += WMMA_K) {
        
        const __half* ntt_tile_ptr = ntt_matrix + out_tile_row * mat_mul_size + k_tile;
        wmma::load_matrix_sync(a_frag, ntt_tile_ptr, mat_mul_size);
        
        
        const int batch_offset_in = batch * in_rows * in_cols;
        const __half* input_tile_ptr = matrix_in + batch_offset_in + k_tile * in_cols + src_tile_col;
        wmma::load_matrix_sync(b_frag, input_tile_ptr, in_cols);

        wmma::mma_sync(acc_frag, a_frag, b_frag, acc_frag);
    }

    
    if (do_twiddle) {
        wmma::fragment<wmma::matrix_a, WMMA_M, WMMA_N, WMMA_K, __half, wmma::row_major> twiddle_frag;
        const __half* twiddle_tile_ptr = twiddles + src_tile_row * in_cols + src_tile_col;
        wmma::load_matrix_sync(twiddle_frag, twiddle_tile_ptr, in_cols);

        for (int i = 0; i < acc_frag.num_elements; i++) {
            float val = fast_fmod(acc_frag.x[i], p);
            float twiddle = __half2float(twiddle_frag.x[i]);
            val = fast_fmod(val * twiddle, p);
            res_frag.x[i] = __float2half(val);
        }
    } else {
        for (int i = 0; i < acc_frag.num_elements; i++) {
            res_frag.x[i] = __float2half(fast_fmod(acc_frag.x[i], p));
        }
    }
    
    
    const int batch_offset_out = batch * out_rows * out_cols;
    __half* output_tile_ptr = matrix_out + batch_offset_out + out_tile_row * out_cols + out_tile_col;

    if (transpose_out) {
        wmma::store_matrix_sync(output_tile_ptr, res_frag, out_cols, wmma::mem_col_major);
    } else {
        wmma::store_matrix_sync(output_tile_ptr, res_frag, out_cols, wmma::mem_row_major);
    }
}

__global__ void scale_kernel(__half* data, float scale_factor, int n_total, int p) {
    int i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i < n_total) {
        float val = __half2float(data[i]);
        val = fast_fmod(val * scale_factor, p);
        data[i] = __float2half(val);
    }
}



long long modPow(long long base, long long exp, long long modulus) {
    long long res = 1;
    base %= modulus;
    while (exp > 0) {
        if (exp % 2 == 1) res = (res * base) % modulus;
        base = (base * base) % modulus;
        exp /= 2;
    }
    return res;
}

void six_step_ntt_gpu_internal(__half* d_data, int batch_size, bool inverse, __half* d_ntt_matrix_n1, __half* d_ntt_matrix_n2, __half* d_twiddles, int p, unsigned int n, unsigned int n1, unsigned int n2) {
    
    __half *d_temp1;
    cudaMalloc(&d_temp1, batch_size * n * sizeof(__half));

    dim3 grid_2d_1(n2/WMMA_N, n1/WMMA_M, batch_size);
    dim3 grid_2d_2(n1/WMMA_N, n2/WMMA_M, batch_size);
    dim3 block_2d(32, 1); 

    
    fused_ntt_stage<<<grid_2d_1, block_2d>>>(d_data, d_temp1, d_ntt_matrix_n1, d_twiddles, n1, n2, true, true, p);

    
    fused_ntt_stage<<<grid_2d_2, block_2d>>>(d_temp1, d_data, d_ntt_matrix_n2, nullptr, n2, n1, false, true, p);

    cudaFree(d_temp1);
}



extern "C" {

GpuNttTables* create_ntt_tables(unsigned int p, unsigned int w_n, unsigned int n) {
    if (p > 2048) {
        
        std::cerr << "Error: Prime must be <= 2048 for GPU NTT." << std::endl;
        return nullptr;
    }
    float n_sqrt_f = sqrtf(n);
    unsigned int n1 = n_sqrt_f;
    unsigned int n2 = n_sqrt_f;
    if (n1 * n2 != n || n1 % WMMA_M != 0 || n2 % WMMA_N != 0) {
        std::cerr << "Error: For WMMA NTT, n must be a perfect square and its sqrt must be a multiple of 16." << std::endl;
        return nullptr;
    }

    GpuNttTables* tables = new GpuNttTables();
    tables->p = p;
    tables->n = n;
    tables->n1 = n1;
    tables->n2 = n2;

    cudaMalloc(&tables->d_ntt_matrix_n1, n1*n1*sizeof(__half));
    cudaMalloc(&tables->d_ntt_matrix_n2, n2*n2*sizeof(__half));
    cudaMalloc(&tables->d_twiddles, n*sizeof(__half));
    cudaMalloc(&tables->d_intt_matrix_n1, n1*n1*sizeof(__half));
    cudaMalloc(&tables->d_intt_matrix_n2, n2*n2*sizeof(__half));
    cudaMalloc(&tables->d_itwiddles, n*sizeof(__half));
    
    std::vector<float> h_ntt_matrix_n1_f(n1*n1), h_ntt_matrix_n2_f(n2*n2), h_twiddles_f(n);
    std::vector<float> h_intt_matrix_n1_f(n1*n1), h_intt_matrix_n2_f(n2*n2), h_itwiddles_f(n);

    long long w1 = modPow(w_n, n/n1, p);
    for(int i=0; i<n1; ++i) for (int j=0; j<n1; ++j) h_ntt_matrix_n1_f[i*n1+j] = modPow(w1, (long long)i*j, p);
    long long w2 = modPow(w_n, n/n2, p);
    for(int i=0; i<n2; ++i) for (int j=0; j<n2; ++j) h_ntt_matrix_n2_f[i*n2+j] = modPow(w2, (long long)i*j, p);
    for (int i=0; i<n1; ++i) for (int j=0; j<n2; ++j) h_twiddles_f[i*n2+j] = modPow(w_n, (long long)i*j, p);
    
    long long iw1 = modPow(w1, p-2, p);
    for(int i=0; i<n1; ++i) for (int j=0; j<n1; ++j) h_intt_matrix_n1_f[i*n1+j] = modPow(iw1, (long long)i*j, p);
    long long iw2 = modPow(w2, p-2, p);
    for(int i=0; i<n2; ++i) for (int j=0; j<n2; ++j) h_intt_matrix_n2_f[i*n2+j] = modPow(iw2, (long long)i*j, p);
    for (int i=0; i<n1; ++i) for (int j=0; j<n2; ++j) h_itwiddles_f[i*n2+j] = modPow(w_n, p-1-(((long long)i*j)%(p-1)), p);

    float *d_tmp_f;
    cudaMalloc(&d_tmp_f, n*sizeof(float)); 
    cudaMemcpy(d_tmp_f, h_ntt_matrix_n1_f.data(), n1*n1*sizeof(float), cudaMemcpyHostToDevice);
    float_to_half<<<(n1*n1+255)/256, 256>>>(d_tmp_f, tables->d_ntt_matrix_n1, n1*n1);
    cudaMemcpy(d_tmp_f, h_ntt_matrix_n2_f.data(), n2*n2*sizeof(float), cudaMemcpyHostToDevice);
    float_to_half<<<(n2*n2+255)/256, 256>>>(d_tmp_f, tables->d_ntt_matrix_n2, n2*n2);
    cudaMemcpy(d_tmp_f, h_twiddles_f.data(), n*sizeof(float), cudaMemcpyHostToDevice);
    float_to_half<<<(n+255)/256, 256>>>(d_tmp_f, tables->d_twiddles, n);
    
    cudaMemcpy(d_tmp_f, h_intt_matrix_n1_f.data(), n1*n1*sizeof(float), cudaMemcpyHostToDevice);
    float_to_half<<<(n1*n1+255)/256, 256>>>(d_tmp_f, tables->d_intt_matrix_n1, n1*n1);
    cudaMemcpy(d_tmp_f, h_intt_matrix_n2_f.data(), n2*n2*sizeof(float), cudaMemcpyHostToDevice);
    float_to_half<<<(n2*n2+255)/256, 256>>>(d_tmp_f, tables->d_intt_matrix_n2, n2*n2);
    cudaMemcpy(d_tmp_f, h_itwiddles_f.data(), n*sizeof(float), cudaMemcpyHostToDevice);
    float_to_half<<<(n+255)/256, 256>>>(d_tmp_f, tables->d_itwiddles, n);
    cudaFree(d_tmp_f);

    return tables;
}

void destroy_ntt_tables(GpuNttTables* tables) {
    if (tables) {
        cudaFree(tables->d_ntt_matrix_n1);
        cudaFree(tables->d_ntt_matrix_n2);
        cudaFree(tables->d_twiddles);
        cudaFree(tables->d_intt_matrix_n1);
        cudaFree(tables->d_intt_matrix_n2);
        cudaFree(tables->d_itwiddles);
        delete tables;
    }
}

void ntt_gpu(GpuNttTables* tables, void* data, unsigned int batch_size, bool inverse) {
    if (!tables || !data) return;

    __half* d_data = static_cast<__half*>(data);
    unsigned int n = tables->n;
    
    if (inverse) {
        six_step_ntt_gpu_internal(d_data, batch_size, true, tables->d_intt_matrix_n1, tables->d_intt_matrix_n2, tables->d_itwiddles, tables->p, n, tables->n1, tables->n2);
        unsigned int n_inv = modPow(n, tables->p - 2, tables->p);
        scale_kernel<<<(batch_size * n + 255) / 256, 256>>>(d_data, n_inv, batch_size * n, tables->p);
    } else {
        six_step_ntt_gpu_internal(d_data, batch_size, false, tables->d_ntt_matrix_n1, tables->d_ntt_matrix_n2, tables->d_twiddles, tables->p, n, tables->n1, tables->n2);
    }
}

} 




__global__ void fused_tiled_stage1(const unsigned int* matrix_in,
                                   unsigned int* matrix_out,
                                   const unsigned int* ntt_matrix_n1,
                                   const unsigned int* twiddles,
                                   unsigned int p,
                                   unsigned int n, unsigned int n1, unsigned int n2) {
    extern __shared__ unsigned int in_col[];

    int j = blockIdx.x; 
    int b = blockIdx.y; 
    int i = threadIdx.x; 

    
    if (i < n1) {
        in_col[i] = matrix_in[b * n + i * n2 + j];
    }
    __syncthreads();

    if (i < n1) {
        
        unsigned long long sum = 0;
        for (int k = 0; k < n1; k++) {
            sum += (unsigned long long)ntt_matrix_n1[i * n1 + k] * in_col[k];
        }
        unsigned int y_val = sum % p;

        
        unsigned int twiddle_val = twiddles[i * n2 + j];
        unsigned int z_val = ((unsigned long long)y_val * twiddle_val) % p;

        
        matrix_out[b * n + j * n1 + i] = z_val;
    }
}

__global__ void fused_tiled_stage2(const unsigned int* matrix_in,
                                   unsigned int* matrix_out,
                                   const unsigned int* ntt_matrix_n2,
                                   unsigned int p,
                                   unsigned int n, unsigned int n1, unsigned int n2) {
    extern __shared__ unsigned int in_col[];

    int j = blockIdx.x; 
    int b = blockIdx.y; 
    int i = threadIdx.x; 
    
    
    if (i < n2) {
        in_col[i] = matrix_in[b * n + i * n1 + j];
    }
    __syncthreads();

    if (i < n2) {
        
        unsigned long long sum = 0;
        for (int k = 0; k < n2; k++) {
            sum += (unsigned long long)ntt_matrix_n2[i * n2 + k] * in_col[k];
        }
        unsigned int a_val = sum % p;

        
        matrix_out[b * n + j * n2 + i] = a_val;
    }
}

__global__ void scale_kernel_int(unsigned int* data, unsigned int scale_factor, int n_total, unsigned int p) {
    int i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i < n_total) {
        data[i] = ((unsigned long long)data[i] * scale_factor) % p;
    }
}

void six_step_ntt_gpu_tiled(unsigned int* d_data, int batch_size, bool inverse, GpuNttTablesInt* tables) {
    unsigned int n = tables->n;
    unsigned int n1 = tables->n1;
    unsigned int n2 = tables->n2;
    
    unsigned int* d_temp;
    cudaMalloc(&d_temp, batch_size * n * sizeof(unsigned int));

    const unsigned int* ntt_mat_n1 = inverse ? tables->d_intt_matrix_n1 : tables->d_ntt_matrix_n1;
    const unsigned int* ntt_mat_n2 = inverse ? tables->d_intt_matrix_n2 : tables->d_ntt_matrix_n2;
    const unsigned int* twiddles = inverse ? tables->d_itwiddles : tables->d_twiddles;
    
    
    dim3 grid1(n2, batch_size);
    dim3 block1(n1);
    fused_tiled_stage1<<<grid1, block1, n1 * sizeof(unsigned int)>>>(d_data, d_temp, ntt_mat_n1, twiddles, tables->p, n, n1, n2);

    
    dim3 grid2(n1, batch_size);
    dim3 block2(n2);
    fused_tiled_stage2<<<grid2, block2, n2 * sizeof(unsigned int)>>>(d_temp, d_data, ntt_mat_n2, tables->p, n, n1, n2);

    cudaFree(d_temp);
}

extern "C" {

GpuNttTablesInt* create_ntt_tables_int(unsigned int p, unsigned int w_n, unsigned int n) {
    float n_sqrt_f = sqrtf(n);
    unsigned int n1 = n_sqrt_f;
    unsigned int n2 = n_sqrt_f;
    if (n1 * n2 != n) {
        std::cerr << "Error: For tiled NTT, n must be a perfect square." << std::endl;
        return nullptr;
    }
    
    GpuNttTablesInt* tables = new GpuNttTablesInt();
    tables->p = p;
    tables->n = n;
    tables->n1 = n1;
    tables->n2 = n2;

    cudaMalloc(&tables->d_ntt_matrix_n1, n1*n1*sizeof(unsigned int));
    cudaMalloc(&tables->d_ntt_matrix_n2, n2*n2*sizeof(unsigned int));
    cudaMalloc(&tables->d_twiddles, n*sizeof(unsigned int));
    cudaMalloc(&tables->d_intt_matrix_n1, n1*n1*sizeof(unsigned int));
    cudaMalloc(&tables->d_intt_matrix_n2, n2*n2*sizeof(unsigned int));
    cudaMalloc(&tables->d_itwiddles, n*sizeof(unsigned int));
    
    std::vector<unsigned int> h_ntt_matrix_n1(n1*n1), h_ntt_matrix_n2(n2*n2), h_twiddles(n);
    std::vector<unsigned int> h_intt_matrix_n1(n1*n1), h_intt_matrix_n2(n2*n2), h_itwiddles(n);

    long long w1 = modPow(w_n, n/n1, p);
    for(int i=0; i<n1; ++i) for (int j=0; j<n1; ++j) h_ntt_matrix_n1[i*n1+j] = modPow(w1, (long long)i*j, p);
    long long w2 = modPow(w_n, n/n2, p);
    for(int i=0; i<n2; ++i) for (int j=0; j<n2; ++j) h_ntt_matrix_n2[i*n2+j] = modPow(w2, (long long)i*j, p);
    for (int i=0; i<n1; ++i) for (int j=0; j<n2; ++j) h_twiddles[i*n2+j] = modPow(w_n, (long long)i*j, p);
    
    long long iw1 = modPow(w1, p-2, p);
    for(int i=0; i<n1; ++i) for (int j=0; j<n1; ++j) h_intt_matrix_n1[i*n1+j] = modPow(iw1, (long long)i*j, p);
    long long iw2 = modPow(w2, p-2, p);
    for(int i=0; i<n2; ++i) for (int j=0; j<n2; ++j) h_intt_matrix_n2[i*n2+j] = modPow(iw2, (long long)i*j, p);
    for (int i=0; i<n1; ++i) for (int j=0; j<n2; ++j) h_itwiddles[i*n2+j] = modPow(w_n, p-1-(((long long)i*j)%(p-1)), p);
    
    cudaMemcpy(tables->d_ntt_matrix_n1, h_ntt_matrix_n1.data(), n1*n1*sizeof(unsigned int), cudaMemcpyHostToDevice);
    cudaMemcpy(tables->d_ntt_matrix_n2, h_ntt_matrix_n2.data(), n2*n2*sizeof(unsigned int), cudaMemcpyHostToDevice);
    cudaMemcpy(tables->d_twiddles, h_twiddles.data(), n*sizeof(unsigned int), cudaMemcpyHostToDevice);
    cudaMemcpy(tables->d_intt_matrix_n1, h_intt_matrix_n1.data(), n1*n1*sizeof(unsigned int), cudaMemcpyHostToDevice);
    cudaMemcpy(tables->d_intt_matrix_n2, h_intt_matrix_n2.data(), n2*n2*sizeof(unsigned int), cudaMemcpyHostToDevice);
    cudaMemcpy(tables->d_itwiddles, h_itwiddles.data(), n*sizeof(unsigned int), cudaMemcpyHostToDevice);

    return tables;
}

void destroy_ntt_tables_int(GpuNttTablesInt* tables) {
    if (tables) {
        cudaFree(tables->d_ntt_matrix_n1);
        cudaFree(tables->d_ntt_matrix_n2);
        cudaFree(tables->d_twiddles);
        cudaFree(tables->d_intt_matrix_n1);
        cudaFree(tables->d_intt_matrix_n2);
        cudaFree(tables->d_itwiddles);
        delete tables;
    }
}

void ntt_gpu_int(GpuNttTablesInt* tables, void* data, unsigned int batch_size, bool inverse) {
    if (!tables || !data) return;

    unsigned int* d_data = static_cast<unsigned int*>(data);
    unsigned int n = tables->n;
    
    six_step_ntt_gpu_tiled(d_data, batch_size, inverse, tables);
    
    if (inverse) {
        unsigned int n_inv = modPow(n, tables->p - 2, tables->p);
        scale_kernel_int<<<(batch_size * n + 255) / 256, 256>>>(d_data, n_inv, batch_size * n, tables->p);
    }
}

} 





__uint128_t modPow128(__uint128_t base, __uint128_t exp, __uint128_t modulus) {
    __uint128_t res = 1;
    base %= modulus;
    while (exp > 0) {
        if (exp % 2 == 1) res = (res * base) % modulus;
        base = (base * base) % modulus;
        exp /= 2;
    }
    return res;
}

__global__ void fused_tiled_stage1_u128(const __uint128_t* matrix_in,
                                        __uint128_t* matrix_out,
                                        const __uint128_t* ntt_matrix_n1,
                                        const __uint128_t* twiddles,
                                        __uint128_t p,
                                        unsigned int n, unsigned int n1, unsigned int n2) {
    extern __shared__ __uint128_t in_col_u128[];

    int j = blockIdx.x;
    int b = blockIdx.y;
    int i = threadIdx.x;

    if (i < n1) {
        in_col_u128[i] = matrix_in[b * n + i * n2 + j];
    }
    __syncthreads();

    if (i < n1) {
        __uint128_t sum = 0;
        for (int k = 0; k < n1; k++) {
            sum = (sum + ntt_matrix_n1[i * n1 + k] * in_col_u128[k]);
             if (sum >= p) sum %= p; 
        }
        sum %= p;

        __uint128_t twiddle_val = twiddles[i * n2 + j];
        __uint128_t z_val = (sum * twiddle_val) % p;

        matrix_out[b * n + j * n1 + i] = z_val;
    }
}

__global__ void fused_tiled_stage2_u128(const __uint128_t* matrix_in,
                                        __uint128_t* matrix_out,
                                        const __uint128_t* ntt_matrix_n2,
                                        __uint128_t p,
                                        unsigned int n, unsigned int n1, unsigned int n2) {
    extern __shared__ __uint128_t in_col_u128[];

    int j = blockIdx.x;
    int b = blockIdx.y;
    int i = threadIdx.x;
    
    if (i < n2) {
        in_col_u128[i] = matrix_in[b * n + i * n1 + j];
    }
    __syncthreads();

    if (i < n2) {
        __uint128_t sum = 0;
        for (int k = 0; k < n2; k++) {
            sum = (sum + ntt_matrix_n2[i * n2 + k] * in_col_u128[k]);
            if (sum >= p) sum %= p;
        }
        __uint128_t a_val = sum % p;

        matrix_out[b * n + j * n2 + i] = a_val;
    }
}

__global__ void scale_kernel_u128(__uint128_t* data, __uint128_t scale_factor, int n_total, __uint128_t p) {
    int i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i < n_total) {
        data[i] = (data[i] * scale_factor) % p;
    }
}

void six_step_ntt_gpu_tiled_u128(void* d_data, int batch_size, bool inverse, GpuNttTablesU128* tables) {
    unsigned int n = tables->n;
    unsigned int n1 = tables->n1;
    unsigned int n2 = tables->n2;

    __uint128_t* d_temp;
    cudaMalloc(&d_temp, batch_size * n * sizeof(__uint128_t));

    const __uint128_t* ntt_mat_n1 = inverse ? tables->d_intt_matrix_n1 : tables->d_ntt_matrix_n1;
    const __uint128_t* ntt_mat_n2 = inverse ? tables->d_intt_matrix_n2 : tables->d_ntt_matrix_n2;
    const __uint128_t* twiddles = inverse ? tables->d_itwiddles : tables->d_twiddles;
    
    dim3 grid1(n2, batch_size);
    dim3 block1(n1);
    fused_tiled_stage1_u128<<<grid1, block1, n1 * sizeof(__uint128_t)>>>(static_cast<__uint128_t*>(d_data), d_temp, ntt_mat_n1, twiddles, tables->p, n, n1, n2);

    dim3 grid2(n1, batch_size);
    dim3 block2(n2);
    fused_tiled_stage2_u128<<<grid2, block2, n2 * sizeof(__uint128_t)>>>(d_temp, static_cast<__uint128_t*>(d_data), ntt_mat_n2, tables->p, n, n1, n2);

    cudaFree(d_temp);
}


extern "C" {

GpuNttTablesU128* create_ntt_tables_u128(unsigned long long p_lo, unsigned long long p_hi, unsigned long long w_n_lo, unsigned long long w_n_hi, unsigned int n) {
    float n_sqrt_f = sqrtf(n);
    unsigned int n1 = n_sqrt_f;
    unsigned int n2 = n_sqrt_f;
    if (n1 * n2 != n) {
        std::cerr << "Error: For tiled U128 NTT, n must be a perfect square." << std::endl;
        return nullptr;
    }

    GpuNttTablesU128* tables = new GpuNttTablesU128();
    tables->p = (((__uint128_t)p_hi) << 64) | p_lo;
    __uint128_t w_n = (((__uint128_t)w_n_hi) << 64) | w_n_lo;
    tables->n = n;
    tables->n1 = n1;
    tables->n2 = n2;

    cudaMalloc(&tables->d_ntt_matrix_n1, n1*n1*sizeof(__uint128_t));
    cudaMalloc(&tables->d_ntt_matrix_n2, n2*n2*sizeof(__uint128_t));
    cudaMalloc(&tables->d_twiddles, n*sizeof(__uint128_t));
    cudaMalloc(&tables->d_intt_matrix_n1, n1*n1*sizeof(__uint128_t));
    cudaMalloc(&tables->d_intt_matrix_n2, n2*n2*sizeof(__uint128_t));
    cudaMalloc(&tables->d_itwiddles, n*sizeof(__uint128_t));
    
    std::vector<__uint128_t> h_ntt_matrix_n1(n1*n1), h_ntt_matrix_n2(n2*n2), h_twiddles(n);
    std::vector<__uint128_t> h_intt_matrix_n1(n1*n1), h_intt_matrix_n2(n2*n2), h_itwiddles(n);

    __uint128_t p = tables->p;
    __uint128_t w1 = modPow128(w_n, n/n1, p);
    for(int i=0; i<n1; ++i) for (int j=0; j<n1; ++j) h_ntt_matrix_n1[i*n1+j] = modPow128(w1, (__uint128_t)i*j, p);
    __uint128_t w2 = modPow128(w_n, n/n2, p);
    for(int i=0; i<n2; ++i) for (int j=0; j<n2; ++j) h_ntt_matrix_n2[i*n2+j] = modPow128(w2, (__uint128_t)i*j, p);
    for (int i=0; i<n1; ++i) for (int j=0; j<n2; ++j) h_twiddles[i*n2+j] = modPow128(w_n, (__uint128_t)i*j, p);
    
    __uint128_t iw1 = modPow128(w1, p-2, p);
    for(int i=0; i<n1; ++i) for (int j=0; j<n1; ++j) h_intt_matrix_n1[i*n1+j] = modPow128(iw1, (__uint128_t)i*j, p);
    __uint128_t iw2 = modPow128(w2, p-2, p);
    for(int i=0; i<n2; ++i) for (int j=0; j<n2; ++j) h_intt_matrix_n2[i*n2+j] = modPow128(iw2, (__uint128_t)i*j, p);
    for (int i=0; i<n1; ++i) for (int j=0; j<n2; ++j) h_itwiddles[i*n2+j] = modPow128(w_n, p-1-(((__uint128_t)i*j)%(p-1)), p);
    
    cudaMemcpy(tables->d_ntt_matrix_n1, h_ntt_matrix_n1.data(), n1*n1*sizeof(__uint128_t), cudaMemcpyHostToDevice);
    cudaMemcpy(tables->d_ntt_matrix_n2, h_ntt_matrix_n2.data(), n2*n2*sizeof(__uint128_t), cudaMemcpyHostToDevice);
    cudaMemcpy(tables->d_twiddles, h_twiddles.data(), n*sizeof(__uint128_t), cudaMemcpyHostToDevice);
    cudaMemcpy(tables->d_intt_matrix_n1, h_intt_matrix_n1.data(), n1*n1*sizeof(__uint128_t), cudaMemcpyHostToDevice);
    cudaMemcpy(tables->d_intt_matrix_n2, h_intt_matrix_n2.data(), n2*n2*sizeof(__uint128_t), cudaMemcpyHostToDevice);
    cudaMemcpy(tables->d_itwiddles, h_itwiddles.data(), n*sizeof(__uint128_t), cudaMemcpyHostToDevice);

    return tables;
}

void destroy_ntt_tables_u128(GpuNttTablesU128* tables) {
    if (tables) {
        cudaFree(tables->d_ntt_matrix_n1);
        cudaFree(tables->d_ntt_matrix_n2);
        cudaFree(tables->d_twiddles);
        cudaFree(tables->d_intt_matrix_n1);
        cudaFree(tables->d_intt_matrix_n2);
        cudaFree(tables->d_itwiddles);
        delete tables;
    }
}

void ntt_gpu_u128(GpuNttTablesU128* tables, void* data, unsigned int batch_size, bool inverse) {
    if (!tables || !data) return;
    
    six_step_ntt_gpu_tiled_u128(data, batch_size, inverse, tables);
    
    if (inverse) {
        __uint128_t n = tables->n;
        __uint128_t n_inv = modPow128(n, tables->p - 2, tables->p);
        scale_kernel_u128<<<(batch_size * n + 255) / 256, 256>>>(static_cast<__uint128_t*>(data), n_inv, batch_size * n, tables->p);
    }
}

} 
