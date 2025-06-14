#ifndef NTT_H
#define NTT_H

#include <cuda_fp16.h>
#include "utils.h"


struct GpuNttTables {
    __half *d_ntt_matrix_n1, *d_ntt_matrix_n2, *d_twiddles;
    __half *d_intt_matrix_n1, *d_intt_matrix_n2, *d_itwiddles;
    unsigned int p;
    unsigned int n, n1, n2;
};

struct GpuNttTablesInt {
    unsigned int *d_ntt_matrix_n1, *d_ntt_matrix_n2, *d_twiddles;
    unsigned int *d_intt_matrix_n1, *d_intt_matrix_n2, *d_itwiddles;
    unsigned int p;
    unsigned int n, n1, n2;
};

struct GpuNttTablesU128 {
    __uint128_t *d_ntt_matrix_n1, *d_ntt_matrix_n2, *d_twiddles;
    __uint128_t *d_intt_matrix_n1, *d_intt_matrix_n2, *d_itwiddles;
    __uint128_t p;
    unsigned int n, n1, n2;
};

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Pre-computes the NTT/INTT tables for a given prime and transform size.
 * 
 * @param p The prime modulus. Must be of the form k*n + 1.
 * @param w_n The n-th primitive root of unity for the prime p.
 * @param n The transform size. Must be a power of 2 and a perfect square.
 * @return A pointer to the opaque GpuNttTables struct, or NULL on failure.
 */
GpuNttTables* create_ntt_tables(unsigned int p, unsigned int w_n, unsigned int n);

/**
 * @brief Destroys the pre-computed NTT tables and frees GPU memory.
 * 
 * @param tables Pointer to the tables created by create_ntt_tables.
 */
void destroy_ntt_tables(GpuNttTables* tables);

/**
 * @brief Performs a batched Number Theoretic Transform (NTT) on the GPU.
 * 
 * @param tables Pointer to the pre-computed tables.
 * @param data Pointer to the input/output data array on the GPU.
 * @param batch_size The number of NTTs to perform.
 * @param inverse If true, performs an inverse NTT.
 */
void ntt_gpu(GpuNttTables* tables, void* data, unsigned int batch_size, bool inverse);




/**
 * @brief Pre-computes the NTT/INTT tables for a given prime using integer arithmetic.
 * 
 * @param p The prime modulus. Must be of the form k*n + 1.
 * @param w_n The n-th primitive root of unity for the prime p.
 * @param n The transform size. Must be a power of 2 and a perfect square.
 * @return A pointer to the opaque GpuNttTablesInt struct, or NULL on failure.
 */
GpuNttTablesInt* create_ntt_tables_int(unsigned int p, unsigned int w_n, unsigned int n);

/**
 * @brief Destroys the pre-computed integer NTT tables and frees GPU memory.
 * 
 * @param tables Pointer to the tables created by create_ntt_tables_int.
 */
void destroy_ntt_tables_int(GpuNttTablesInt* tables);

/**
 * @brief Performs a batched Number Theoretic Transform (NTT) on the GPU using integer arithmetic.
 * 
 * @param tables Pointer to the pre-computed integer tables.
 * @param data Pointer to the input/output data array (unsigned int type) on the GPU.
 * @param batch_size The number of NTTs to perform.
 * @param inverse If true, performs an inverse NTT.
 */
void ntt_gpu_int(GpuNttTablesInt* tables, void* data, unsigned int batch_size, bool inverse);




/**
 * @brief Pre-computes the NTT/INTT tables for a 128-bit prime.
 * 
 * @param p_lo Lower 64 bits of the prime modulus.
 * @param p_hi Upper 64 bits of the prime modulus.
 * @param w_n_lo Lower 64 bits of the n-th primitive root of unity.
 * @param w_n_hi Upper 64 bits of the n-th primitive root of unity.
 * @param n The transform size. Must be a power of 2 and a perfect square.
 * @return A pointer to the opaque GpuNttTablesU128 struct, or NULL on failure.
 */
GpuNttTablesU128* create_ntt_tables_u128(unsigned long long p_lo, unsigned long long p_hi, unsigned long long w_n_lo, unsigned long long w_n_hi, unsigned int n);

/**
 * @brief Destroys the pre-computed 128-bit NTT tables and frees GPU memory.
 * 
 * @param tables Pointer to the tables created by create_ntt_tables_u128.
 */
void destroy_ntt_tables_u128(GpuNttTablesU128* tables);

/**
 * @brief Performs a batched NTT on the GPU using 128-bit integer arithmetic.
 * 
 * @param tables Pointer to the pre-computed 128-bit tables.
 * @param data Pointer to the input/output data array (__uint128_t type) on the GPU.
 * @param batch_size The number of NTTs to perform.
 * @param inverse If true, performs an inverse NTT.
 */
void ntt_gpu_u128(GpuNttTablesU128* tables, void* data, unsigned int batch_size, bool inverse);


#ifdef __cplusplus
}
#endif

#endif 