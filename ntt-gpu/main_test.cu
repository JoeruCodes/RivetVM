#include <iostream>
#include <vector>
#include <cmath>
#include <cassert>
#include <cuda_fp16.h>
#include <cuda_runtime.h>
#include <iomanip>
#include "ntt.h"
#include "utils.h"


const int BATCH_SIZE = 128;


__global__ void int_to_float(const unsigned int* in, float* out, int n) {
    int i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i < n) {
        out[i] = static_cast<float>(in[i]);
    }
}

void check_cuda_error(const char* message) {
    cudaDeviceSynchronize();
    cudaError_t err = cudaGetLastError();
    if (err != cudaSuccess) {
        std::cerr << "CUDA Error after " << message << ": " << cudaGetErrorString(err) << std::endl;
        exit(1);
    }
}

int main() {
    
    const int N_TEST = 256;
    const int P = 769; 
    const int W_256_P = 562; 

    std::cout << "Initializing GPU NTT tables for P=" << P << " and N=" << N_TEST << std::endl;
    GpuNttTables* tables = create_ntt_tables(P, W_256_P, N_TEST);
    if (!tables) {
        std::cerr << "Failed to create NTT tables." << std::endl;
        return 1;
    }

    
    std::vector<unsigned int> h_data(BATCH_SIZE * N_TEST);
    for (int b = 0; b < BATCH_SIZE; ++b) {
        for (int i = 0; i < N_TEST; ++i) {
            h_data[b*N_TEST+i] = i; 
        }
    }

    
    
    
    unsigned int* d_data_int;
    float* d_data_f;
    __half* d_data_h;
    cudaMalloc(&d_data_int, BATCH_SIZE * N_TEST * sizeof(unsigned int));
    cudaMalloc(&d_data_f, BATCH_SIZE * N_TEST * sizeof(float));
    cudaMalloc(&d_data_h, BATCH_SIZE * N_TEST * sizeof(__half));

    cudaMemcpy(d_data_int, h_data.data(), BATCH_SIZE * N_TEST * sizeof(unsigned int), cudaMemcpyHostToDevice);
    int_to_float<<<(BATCH_SIZE * N_TEST + 255)/256, 256>>>(d_data_int, d_data_f, BATCH_SIZE * N_TEST);
    float_to_half<<<(BATCH_SIZE * N_TEST + 255)/256, 256>>>(d_data_f, d_data_h, BATCH_SIZE * N_TEST);
    check_cuda_error("initial data transfer and conversion");

    
    cudaEvent_t start, stop;
    cudaEventCreate(&start);
    cudaEventCreate(&stop);

    std::cout << "\nPerforming NTT Benchmark..." << std::endl;
    
    
    ntt_gpu(tables, d_data_h, BATCH_SIZE, false);

    cudaEventRecord(start);
    int num_runs = 100;
    for (int i = 0; i < num_runs; ++i) {
        ntt_gpu(tables, d_data_h, BATCH_SIZE, false);
    }
    cudaEventRecord(stop);
    cudaEventSynchronize(stop);
    
    float milliseconds = 0;
    cudaEventElapsedTime(&milliseconds, start, stop);
    float avg_ms = milliseconds / num_runs;

    
    
    
    
    
    double n1 = tables->n1;
    double n2 = tables->n2;
    double ntt_flops_per_batch = 2.0 * n2 * n1 * n1 + 
                                 n1 * n2 + 
                                 2.0 * n1 * n2 * n2;

    double total_flops = (double)BATCH_SIZE * ntt_flops_per_batch;
    double gflops = total_flops / (avg_ms * 1e6);

    std::cout << std::fixed << std::setprecision(3);
    std::cout << "NTT GPU time: " << avg_ms << " ms" << std::endl;
    std::cout << "NTT GFLOPS: " << gflops << std::endl;
    check_cuda_error("benchmark run");

    
    destroy_ntt_tables(tables);
    cudaFree(d_data_int);
    cudaFree(d_data_f);
    cudaFree(d_data_h);
    cudaEventDestroy(start);
    cudaEventDestroy(stop);


    
    std::cout << "\n\n--- Integer Implementation Benchmark ---" << std::endl;
    const int P_INT = 65537; 
    const int W_256_P_INT = 17; 

    std::cout << "Initializing GPU NTT tables for P=" << P_INT << " and N=" << N_TEST << std::endl;
    GpuNttTablesInt* tables_int = create_ntt_tables_int(P_INT, W_256_P_INT, N_TEST);
    if (!tables_int) {
        std::cerr << "Failed to create integer NTT tables." << std::endl;
        return 1;
    }

    
    unsigned int* d_data_int_bench;
    cudaMalloc(&d_data_int_bench, BATCH_SIZE * N_TEST * sizeof(unsigned int));
    cudaMemcpy(d_data_int_bench, h_data.data(), BATCH_SIZE * N_TEST * sizeof(unsigned int), cudaMemcpyHostToDevice);
    check_cuda_error("integer data transfer");

    
    cudaEvent_t start_int, stop_int;
    cudaEventCreate(&start_int);
    cudaEventCreate(&stop_int);

    std::cout << "\nPerforming Integer NTT Benchmark..." << std::endl;
    
    
    ntt_gpu_int(tables_int, d_data_int_bench, BATCH_SIZE, false);

    cudaEventRecord(start_int);
    for (int i = 0; i < num_runs; ++i) {
        ntt_gpu_int(tables_int, d_data_int_bench, BATCH_SIZE, false);
    }
    cudaEventRecord(stop_int);
    cudaEventSynchronize(stop_int);
    
    cudaEventElapsedTime(&milliseconds, start_int, stop_int);
    avg_ms = milliseconds / num_runs;

    
    
    
    double n1_int = tables_int->n1;
    double n2_int = tables_int->n2;
    double total_iops = (double)BATCH_SIZE * (2.0 * n2_int * n1_int * n1_int + n1_int * n2_int + 2.0 * n1_int * n2_int * n2_int);

    std::cout << std::fixed << std::setprecision(3);
    std::cout << "Integer NTT GPU time: " << avg_ms << " ms" << std::endl;
    std::cout << "Integer NTT GIOPS: " << total_iops / (avg_ms * 1e6) << std::endl;
    check_cuda_error("integer benchmark run");

    
    destroy_ntt_tables_int(tables_int);
    cudaFree(d_data_int_bench);
    cudaEventDestroy(start_int);
    cudaEventDestroy(stop_int);


    
    std::cout << "\n\n--- U128 Implementation Benchmark ---" << std::endl;
    
    
    
    
    
    unsigned long long p128_lo = 2305843009213693951ULL; 
    unsigned long long p128_hi = 0;
    unsigned long long w128_lo = 3344444555666778ULL;
    unsigned long long w128_hi = 0;

    __uint128_t p_u128 = (((__uint128_t)p128_hi) << 64) | p128_lo;
    
    std::cout << "Initializing GPU NTT tables for 128-bit prime..." << std::endl;
    GpuNttTablesU128* tables_u128 = create_ntt_tables_u128(p128_lo, p128_hi, w128_lo, w128_hi, N_TEST);
    if (!tables_u128) {
        std::cerr << "Failed to create u128 NTT tables." << std::endl;
        return 1;
    }

    
    std::vector<__uint128_t> h_data_u128(BATCH_SIZE * N_TEST);
    for (int b = 0; b < BATCH_SIZE; ++b) {
        for (int i = 0; i < N_TEST; ++i) {
            h_data_u128[b*N_TEST+i] = i; 
        }
    }
    __uint128_t* d_data_u128_bench;
    cudaMalloc(&d_data_u128_bench, BATCH_SIZE * N_TEST * sizeof(__uint128_t));
    cudaMemcpy(d_data_u128_bench, h_data_u128.data(), BATCH_SIZE * N_TEST * sizeof(__uint128_t), cudaMemcpyHostToDevice);
    check_cuda_error("u128 data transfer");

    
    cudaEvent_t start_u128, stop_u128;
    cudaEventCreate(&start_u128);
    cudaEventCreate(&stop_u128);

    std::cout << "\nPerforming U128 NTT Benchmark..." << std::endl;
    
    
    ntt_gpu_u128(tables_u128, d_data_u128_bench, BATCH_SIZE, false);

    cudaEventRecord(start_u128);
    for (int i = 0; i < num_runs; ++i) {
        ntt_gpu_u128(tables_u128, d_data_u128_bench, BATCH_SIZE, false);
    }
    cudaEventRecord(stop_u128);
    cudaEventSynchronize(stop_u128);
    
    cudaEventElapsedTime(&milliseconds, start_u128, stop_u128);
    avg_ms = milliseconds / num_runs;

    double n1_u128 = tables_u128->n1;
    double n2_u128 = tables_u128->n2;
    double total_iops_u128 = (double)BATCH_SIZE * (2.0 * n2_u128 * n1_u128 * n1_u128 + n1_u128 * n2_u128 + 2.0 * n1_u128 * n2_u128 * n2_u128);

    std::cout << std::fixed << std::setprecision(3);
    std::cout << "U128 NTT GPU time: " << avg_ms << " ms" << std::endl;
    std::cout << "U128 NTT GIOPS: " << total_iops_u128 / (avg_ms * 1e6) << std::endl;
    check_cuda_error("u128 benchmark run");

    
    destroy_ntt_tables_u128(tables_u128);
    cudaFree(d_data_u128_bench);
    cudaEventDestroy(start_u128);
    cudaEventDestroy(stop_u128);

    return 0;
} 