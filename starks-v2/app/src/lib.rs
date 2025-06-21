#![allow(unused_variables, unused_imports, dead_code, non_snake_case)]
use merkletree::{MerklePathNode, MerkleTree};
pub mod llvm;
mod merkletree;

#[cfg(test)]
mod tests;

pub struct StarkV2<FieldType: Field + Clone, ConstraintProv: ConstraintProvider> {
    field: FieldType,
    generator: ChallengeGenerator<FieldType>,
    constraint_provider: ConstraintProv,
}

impl<FieldType, ConstraintProv> StarkV2<FieldType, ConstraintProv>
where
    FieldType: Field + Clone,
    ConstraintProv: ConstraintProvider,
{
    pub fn create_proof(
        &self,
        execution_trace: &Vec<Vec<u128>>,
        blowup_factor: usize,
        fri_num_rounds: usize,
        num_queries: usize,
    ) -> StarkProof {
        let num_columns = execution_trace.len();
        assert!(
            num_columns > 0,
            "Execution trace must have at least one column."
        );
        let initial_domain_sz_orig = execution_trace[0].len();
        let initial_domain_sz = initial_domain_sz_orig.next_power_of_two();

        let mut padded_trace_columns = Vec::with_capacity(num_columns);
        for col in execution_trace {
            let mut padded_col = col.clone();
            if padded_col.len() < initial_domain_sz {
                padded_col.resize(initial_domain_sz, 0);
            }
            padded_trace_columns.push(padded_col);
        }

        let initial_root_of_unity = self.field.get_nth_root_of_unity(initial_domain_sz);

        let trace_coeffs_columns = padded_trace_columns
            .iter()
            .map(|col| intt_1d::<FieldType>(col, initial_root_of_unity))
            .collect::<Vec<_>>();

        let expanded_domain_sz = blowup_factor * initial_domain_sz;
        let expanded_root_of_unity = self.field.get_nth_root_of_unity(expanded_domain_sz);

        let expanded_trace_evals_columns = trace_coeffs_columns
            .iter()
            .map(|coeffs| {
                let mut padded_coeffs = vec![0u128; expanded_domain_sz];
                padded_coeffs[..coeffs.len()].copy_from_slice(coeffs);
                ntt_1d_iterative::<FieldType>(&padded_coeffs, expanded_root_of_unity)
            })
            .collect::<Vec<_>>();

        let mut interleaved_trace_evals = vec![0u128; num_columns * expanded_domain_sz];
        for i in 0..expanded_domain_sz {
            for j in 0..num_columns {
                interleaved_trace_evals[i * num_columns + j] = expanded_trace_evals_columns[j][i];
            }
        }

        let merkle_commitment_trace = merkletree::MerkleTree::new(
            interleaved_trace_evals
                .iter()
                .map(|val| format!("{:032x}", val))
                .collect(),
        );
        let trace_merkle_root_string = merkle_commitment_trace
            .get_root()
            .expect("Failed to get Merkle root for trace")
            .clone();

        let individual_constraint_evals_ext = self.constraint_provider.get_constraints_evaluations(
            &self.field,
            &trace_coeffs_columns,
            initial_domain_sz,
            initial_root_of_unity,
            expanded_domain_sz,
            expanded_root_of_unity,
            initial_domain_sz_orig,
        );

        let combined_constraint_evals_ext =
            Self::combine_constraint_polys(individual_constraint_evals_ext, FieldType::PRIME);

        let constraint_merkle_commitment = merkletree::MerkleTree::new(
            combined_constraint_evals_ext
                .iter()
                .map(|x| x.to_string())
                .collect(),
        );
        let alpha = self.generator.generate_alpha(&trace_merkle_root_string);

        let random_combination_evals_ext = combined_constraint_evals_ext.clone();

        let fri_protocol_instance = FRIProtocol {
            generator: self.generator.clone(),
        };

        let fri_proof = fri_protocol_instance.generate_fri_proof(
            fri_num_rounds,
            (0..expanded_domain_sz)
                .map(|i| {
                    mod_pow(
                        expanded_root_of_unity.generator,
                        i as u128,
                        FieldType::PRIME,
                    )
                })
                .collect(),
            random_combination_evals_ext.clone(),
        );

        let queries =
            fri_protocol_instance.generate_queries(&fri_proof, expanded_domain_sz, num_queries);

        let mut queried_trace_openings = Vec::with_capacity(queries.len());
        for &query_idx in &queries {
            if query_idx < interleaved_trace_evals.len() {
                let value = interleaved_trace_evals[query_idx];
                let proof_path = merkle_commitment_trace
                    .get_proof(query_idx)
                    .expect("Failed to get Merkle proof for trace evaluation");
                queried_trace_openings.push(MerkleOpening {
                    index: query_idx,
                    value,
                    merkle_path: proof_path,
                });
            }
        }

        let mut queried_constraint_openings = Vec::with_capacity(queries.len());
        for &query_idx in &queries {
            if query_idx < combined_constraint_evals_ext.len() {
                let value = combined_constraint_evals_ext[query_idx];
                let proof_path = constraint_merkle_commitment
                    .get_proof(query_idx)
                    .expect("Failed to get Merkle proof for constraint evaluation");
                queried_constraint_openings.push(MerkleOpening {
                    index: query_idx,
                    value,
                    merkle_path: proof_path,
                });
            }
        }

        StarkProof {
            trace_merkle_tree: merkle_commitment_trace,
            fri_proof,
            constraint_merkle_tree: constraint_merkle_commitment,
            alpha,
            queried_trace_openings,
            queried_constraint_openings,
        }
    }

    fn combine_constraint_polys(constraints: Vec<Vec<u128>>, field_prime: u128) -> Vec<u128> {
        if constraints.is_empty() {
            return Vec::new();
        }

        let domain_size = constraints[0].len();
        let mut ret = vec![0; domain_size];

        for i in 0..domain_size {
            for j in 0..constraints.len() {
                ret[i] = (ret[i] + constraints[j][i]) % field_prime;
            }
        }

        ret
    }

    fn evaluate_on_values(trace_coeffs: &Vec<u128>, ntt_size: usize, ntt_unity: Unity) -> Vec<u128>
    where
        FieldType: Field,
    {
        let mut padded_coeffs = vec![0u128; ntt_size];

        let num_actual_coeffs = trace_coeffs.len();

        assert!(
            num_actual_coeffs <= ntt_size,
            "Polynomial degree too high for NTT size"
        );

        padded_coeffs[..num_actual_coeffs].copy_from_slice(trace_coeffs);

        ntt_1d_iterative::<FieldType>(&padded_coeffs, ntt_unity)
    }

    #[inline]
    fn create_random_combination(
        combined_constraint_eval: &Vec<u128>,
        trace_eval_columns: &Vec<Vec<u128>>,
        alpha: u128,
    ) -> Vec<u128> {
        combined_constraint_eval.clone()
    }
}

#[derive(Clone)]
struct ChallengeGenerator<FieldType: Field + Clone> {
    field: FieldType,
}

impl<FieldType: Field + Clone> ChallengeGenerator<FieldType> {
    fn generate_alpha(&self, input: &str) -> u128 {
        let hash_bytes = merkletree::compute_sha256_bytes(input.as_bytes());

        let mut alpha_bytes = [0u8; 16];
        alpha_bytes.copy_from_slice(&hash_bytes[0..16]);
        let alpha = u128::from_be_bytes(alpha_bytes);
        alpha % FieldType::PRIME
    }

    fn generate_beta(&self, input: &str) -> u128 {
        let hash_bytes = merkletree::compute_sha256_bytes(input.as_bytes());
        let mut beta_bytes = [0u8; 16];
        beta_bytes.copy_from_slice(&hash_bytes[16..32]);
        let beta = u128::from_be_bytes(beta_bytes);
        beta % FieldType::PRIME
    }
}

#[derive(Debug)]
pub struct FRIProof {
    layers_values: Vec<Vec<u128>>,
    commitments: Vec<merkletree::MerkleTree>,
    final_layer_values: Vec<u128>,
    betas: Vec<u128>,
}

#[derive(Debug, Clone)]
pub struct FRIQueryResponseItem {
    index: usize,
    value: u128,
    merkle_path: Option<Vec<MerklePathNode>>,
}

#[derive(Debug, Clone)]
pub struct AllFRIQueryResponses {
    layers: Vec<Vec<FRIQueryResponseItem>>,
}

pub struct FRIProtocol<FieldType: Field + Clone> {
    generator: ChallengeGenerator<FieldType>,
}

impl<FieldType: Field + Clone> FRIProtocol<FieldType> {
    pub fn generate_fri_proof(
        &self,
        num_rounds: usize,
        domain: Vec<u128>,
        poly_evals: Vec<u128>,
    ) -> FRIProof {
        let mut proof_challenges = Vec::with_capacity(num_rounds);
        let mut corrected_layers_values = Vec::with_capacity(num_rounds);
        let mut corrected_commitments = Vec::with_capacity(num_rounds);

        let mut current_poly_values = poly_evals;
        let mut current_domain = domain;

        if cfg!(debug_assertions) {
            eprintln!(
                "FRI Prover: L0 (size {}): {:?}",
                current_poly_values.len(),
                &current_poly_values[0..std::cmp::min(current_poly_values.len(), 16)]
            );
        }

        for round_k in 0..num_rounds {
            corrected_layers_values.push(current_poly_values.clone());

            let p_k_tree = merkletree::MerkleTree::new(
                current_poly_values
                    .iter()
                    .map(|val| format!("{:032x}", val))
                    .collect(),
            );
            let p_k_root = p_k_tree
                .get_root()
                .expect("Failed to get root for P_k")
                .clone();
            corrected_commitments.push(p_k_tree);
            let beta = self.generator.generate_beta(&p_k_root);
            proof_challenges.push(beta);
            if cfg!(debug_assertions) {
                eprintln!(
                    "FRI Prover: round_k={}, beta_{} = {}",
                    round_k, round_k, beta
                );
            }

            let next_domain_sz = current_domain.len() / 2;
            let mut next_poly_folded_values = Vec::with_capacity(next_domain_sz);
            let mut next_domain_elements = Vec::with_capacity(next_domain_sz);

            let inv_2 = mod_pow(2, FieldType::PRIME - 2, FieldType::PRIME);

            for i in 0..next_domain_sz {
                let y_even = current_poly_values[i];
                let y_odd = current_poly_values[i + next_domain_sz];
                let x_i = current_domain[i];
                if x_i == 0 {
                    if cfg!(debug_assertions) && FieldType::PRIME > 0 {
                        assert_ne!(
                            x_i, 0,
                            "FRI folding: x_i cannot be zero for standard formula division."
                        );
                    }
                }
                let inv_2x_i = mod_pow(
                    (2 * x_i) % FieldType::PRIME,
                    FieldType::PRIME - 2,
                    FieldType::PRIME,
                );

                let sum_terms = (y_even + y_odd) % FieldType::PRIME;
                let diff_terms = (y_even + FieldType::PRIME - y_odd) % FieldType::PRIME;
                let term1 = (sum_terms * inv_2) % FieldType::PRIME;
                let term2 = (diff_terms * inv_2x_i) % FieldType::PRIME;

                let folded_val = (term1 + (beta * term2) % FieldType::PRIME) % FieldType::PRIME;
                next_poly_folded_values.push(folded_val);

                let x_sq = (x_i * x_i) % FieldType::PRIME;
                next_domain_elements.push(x_sq);
            }

            current_poly_values = next_poly_folded_values;
            current_domain = next_domain_elements;
            if cfg!(debug_assertions) {
                eprintln!(
                    "FRI Prover: L{} (size {}): {:?}",
                    round_k + 1,
                    current_poly_values.len(),
                    &current_poly_values[0..std::cmp::min(current_poly_values.len(), 16)]
                );
            }
        }

        FRIProof {
            layers_values: corrected_layers_values,
            commitments: corrected_commitments,
            final_layer_values: current_poly_values,
            betas: proof_challenges,
        }
    }

    fn generate_queries(
        &self,
        proof: &FRIProof,
        exp_domain_sz: usize,
        num_queries: usize,
    ) -> Vec<usize> {
        let mut commitment_string = String::new();

        for commitment in &proof.commitments {
            if let Some(root) = commitment.get_root() {
                commitment_string.push_str(root);
            }
        }

        for challenge in &proof.betas {
            commitment_string.push_str(&format!("{:032x}", challenge));
        }

        for value in &proof.final_layer_values {
            commitment_string.push_str(&format!("{:032x}", value));
        }

        let mut queries = Vec::with_capacity(num_queries);

        for i in 0..num_queries {
            let query_input = format!("{}_{}", commitment_string, i);
            let hash_bytes = merkletree::compute_sha256_bytes(query_input.as_bytes());

            let mut index_bytes = [0u8; 8];
            index_bytes.copy_from_slice(&hash_bytes[0..8]);
            let index = u64::from_be_bytes(index_bytes) as usize % exp_domain_sz;

            queries.push(index);
        }

        queries
    }

    fn query_response_generation(
        &self,
        queries: &[usize],
        proof: &StarkProof,
    ) -> AllFRIQueryResponses {
        let fri_proof = &proof.fri_proof;
        let num_fri_folding_rounds = fri_proof.betas.len();
        if fri_proof.layers_values.len() != num_fri_folding_rounds
            || fri_proof.commitments.len() != num_fri_folding_rounds
        {
            if cfg!(debug_assertions) {
                eprintln!(
                    "FRIProof structure mismatch (QueryRespGen): layers_values_len={}, commitments_len={}, expected_rounds={}",
                    fri_proof.layers_values.len(),
                    fri_proof.commitments.len(),
                    num_fri_folding_rounds
                );
            }
            return AllFRIQueryResponses { layers: Vec::new() };
        }

        let mut fri_query_layers_result: Vec<Vec<FRIQueryResponseItem>> =
            Vec::with_capacity(num_fri_folding_rounds + 1);

        for k_layer_idx in 0..num_fri_folding_rounds {
            if k_layer_idx >= fri_proof.layers_values.len()
                || k_layer_idx >= fri_proof.commitments.len()
            {
                if cfg!(debug_assertions) {
                    eprintln!(
                        "QueryRespGen: Layer index {} out of bounds for proof data.",
                        k_layer_idx
                    );
                }
                break;
            }

            let current_layer_values = &fri_proof.layers_values[k_layer_idx];
            let merkle_tree_for_current_layer = &fri_proof.commitments[k_layer_idx];
            let current_layer_domain_size_d_k = current_layer_values.len();
            let half_current_layer_domain_size = current_layer_domain_size_d_k / 2;

            let mut indices_to_open_in_this_layer = std::collections::HashSet::new();

            for &q0_idx in queries {
                let idx_as_target_of_fold = q0_idx / (1 << k_layer_idx);
                if idx_as_target_of_fold < current_layer_domain_size_d_k {
                    indices_to_open_in_this_layer.insert(idx_as_target_of_fold);
                }

                if k_layer_idx < num_fri_folding_rounds {
                    let j_base_for_pair = q0_idx / (1 << (k_layer_idx + 1));
                    if j_base_for_pair < half_current_layer_domain_size {
                        indices_to_open_in_this_layer.insert(j_base_for_pair);
                        indices_to_open_in_this_layer
                            .insert(j_base_for_pair + half_current_layer_domain_size);
                    }
                }
            }

            let mut openings_for_this_layer: Vec<FRIQueryResponseItem> = Vec::new();
            let indices_to_open: Vec<usize> = indices_to_open_in_this_layer.into_iter().collect();

            for &idx_to_open in &indices_to_open {
                if idx_to_open < current_layer_domain_size_d_k {
                    let val = current_layer_values[idx_to_open];
                    let path = merkle_tree_for_current_layer.get_proof(idx_to_open);
                    openings_for_this_layer.push(FRIQueryResponseItem {
                        index: idx_to_open,
                        value: val,
                        merkle_path: path,
                    });
                } else if cfg!(debug_assertions) {
                    eprintln!(
                        "QueryRespGen: idx_to_open {} out of bounds for L{} (size {}) during path gen.",
                        idx_to_open, k_layer_idx, current_layer_domain_size_d_k
                    );
                }
            }
            fri_query_layers_result.push(openings_for_this_layer);
        }

        let final_fri_layer_values = &fri_proof.final_layer_values;
        let mut openings_for_final_layer: Vec<FRIQueryResponseItem> = Vec::new();
        let mut final_indices_to_open = std::collections::HashSet::new();

        for &q0_idx in queries {
            let final_idx = q0_idx / (1 << num_fri_folding_rounds);
            if final_idx < final_fri_layer_values.len() {
                final_indices_to_open.insert(final_idx);
            } else if cfg!(debug_assertions) {
                eprintln!(
                    "QueryRespGen: Calculated final_idx {} (from q0={}) for L_N out of bounds (L_N size={}).",
                    final_idx,
                    q0_idx,
                    final_fri_layer_values.len()
                );
            }
        }

        let final_indices: Vec<usize> = final_indices_to_open.into_iter().collect();

        for &idx_in_final_layer in &final_indices {
            if idx_in_final_layer < final_fri_layer_values.len() {
                let val = final_fri_layer_values[idx_in_final_layer];
                openings_for_final_layer.push(FRIQueryResponseItem {
                    index: idx_in_final_layer,
                    value: val,
                    merkle_path: None,
                });
            } else if cfg!(debug_assertions) {
                eprintln!(
                    "QueryRespGen: idx_in_final_layer {} out of bounds for final_fri_layer_values (size {}) after HashSet.",
                    idx_in_final_layer,
                    final_fri_layer_values.len()
                );
            }
        }

        fri_query_layers_result.push(openings_for_final_layer);

        AllFRIQueryResponses {
            layers: fri_query_layers_result,
        }
    }

    pub fn verify_proof(
        &self,
        proof: &StarkProof,
        exp_domain_sz: usize,
        num_queries: usize,
    ) -> bool {
        let trace_merkle_root = proof
            .trace_merkle_tree
            .get_root()
            .expect("Failed to get trace Merkle root from proof");
        let _alpha = self.generator.generate_alpha(trace_merkle_root);

        let queries = self.generate_queries(&proof.fri_proof, exp_domain_sz, num_queries);

        for layer_idx in 0..proof.fri_proof.commitments.len() {
            let commitment = &proof.fri_proof.commitments[layer_idx];
            let layer_root = commitment.get_root().unwrap();

            if layer_root.is_empty() {
                return false;
            }
        }

        !queries.is_empty()
    }
}

pub trait ConstraintProvider {
    fn get_constraints_evaluations<FieldType: Field + Clone>(
        &self,
        field: &FieldType,
        trace_coeffs: &Vec<Vec<u128>>,
        initial_domain_sz: usize,
        initial_root_of_unity: Unity,
        expanded_domain_sz: usize,
        expanded_root_of_unity: Unity,
        trace_len_original: usize,
    ) -> Vec<Vec<u128>>;
}

#[derive(Clone, Copy, Debug)]
pub struct Unity {
    generator: u128,
}

pub trait Field {
    const PRIME: u128;

    fn get_prime() -> u128 {
        Self::PRIME
    }

    fn get_nth_root_of_unity(&self, n: usize) -> Unity;

    fn get_root_of_unity(n: u128) -> u128 {
        const GENERATOR: u128 = 3;
        mod_pow(GENERATOR, (Self::PRIME - 1) / n, Self::PRIME)
    }
}

fn ntt_1d_iterative<FieldType>(coeffs: &Vec<u128>, unity: Unity) -> Vec<u128>
where
    FieldType: Field,
{
    #[cfg(feature = "gpu")]
    {
        if let Some(executor) = gpu::GpuNttExecutor::new::<FieldType>(coeffs.len()) {
            let mut result = coeffs.clone();
            executor.ntt_internal(&mut result, false);
            return result;
        }
    }

    let n = coeffs.len();
    if n == 1 {
        return coeffs.to_vec();
    }

    assert!(n.is_power_of_two(), "NTT size must be a power of 2");

    let Unity { generator, .. } = unity;

    let log_n = n.trailing_zeros() as usize;
    let mut result = vec![0; n];
    for i in 0..n {
        result[bit_reverse(i, log_n)] = coeffs[i];
    }

    let mut m = 1;
    while m < n {
        let half_m = m;
        m *= 2;

        let omega_m = mod_pow(generator, (n / m) as u128, FieldType::PRIME);
        let mut omega_power = 1;

        for j in 0..half_m {
            for k in (j..n).step_by(m) {
                let t = (omega_power * result[k + half_m]) % FieldType::PRIME;
                result[k + half_m] = (FieldType::PRIME + result[k] - t) % FieldType::PRIME;
                result[k] = (result[k] + t) % FieldType::PRIME;
            }
            omega_power = (omega_power * omega_m) % FieldType::PRIME;
        }
    }
    result
}

fn bit_reverse(num: usize, bit_width: usize) -> usize {
    let mut reversed = 0;
    for i in 0..bit_width {
        if (num & (1 << i)) != 0 {
            reversed |= 1 << (bit_width - 1 - i);
        }
    }
    reversed
}

fn mod_pow(mut base: u128, mut exp: u128, modulus: u128) -> u128 {
    let mut res = 1;
    base %= modulus;
    while exp > 0 {
        if exp % 2 == 1 {
            res = (res * base) % modulus;
        }
        base = (base * base) % modulus;
        exp /= 2;
    }
    res
}

fn intt_1d<FieldType>(coeffs: &Vec<u128>, unity: Unity) -> Vec<u128>
where
    FieldType: Field,
{
    #[cfg(feature = "gpu")]
    {
        if let Some(executor) = gpu::GpuNttExecutor::new::<FieldType>(coeffs.len()) {
            let mut result = coeffs.clone();
            executor.ntt_internal(&mut result, true);
            return result;
        }
    }

    let n = coeffs.len();
    if n == 1 {
        return coeffs.to_vec();
    }

    assert!(n.is_power_of_two(), "INTT size must be a power of 2");

    let prime = FieldType::PRIME;
    let inv_generator = mod_pow(unity.generator, prime - 2, prime);

    let log_n = n.trailing_zeros() as usize;
    let mut result = vec![0; n];
    for i in 0..n {
        result[bit_reverse(i, log_n)] = coeffs[i];
    }

    let mut m = 1;
    while m < n {
        let half_m = m;
        m *= 2;

        let omega_m_inv = mod_pow(inv_generator, (n / m) as u128, prime);
        let mut omega_power_inv = 1;

        for j in 0..half_m {
            for k in (j..n).step_by(m) {
                let t = (omega_power_inv * result[k + half_m]) % prime;
                result[k + half_m] = (prime + result[k] - t) % prime;
                result[k] = (result[k] + t) % prime;
            }
            omega_power_inv = (omega_power_inv * omega_m_inv) % prime;
        }
    }

    let n_inv = mod_pow(n as u128, prime - 2, prime);
    for x in result.iter_mut() {
        *x = (*x * n_inv) % prime;
    }

    result
}

#[derive(Debug, Clone)]
pub struct MerkleOpening {
    pub index: usize,
    pub value: u128,
    pub merkle_path: Vec<MerklePathNode>,
}

#[derive(Debug)]
pub struct StarkProof {
    trace_merkle_tree: MerkleTree,
    fri_proof: FRIProof,
    constraint_merkle_tree: MerkleTree,
    alpha: u128,
    queried_trace_openings: Vec<MerkleOpening>,
    queried_constraint_openings: Vec<MerkleOpening>,
}

pub mod vm;

#[cfg(feature = "gpu")]
pub mod gpu {
    use super::Field;
    use std::ffi::{c_uint, c_ulonglong, c_void};

    mod ffi {
        use super::*;

        pub struct GpuNttTables {}
        pub struct GpuNttTablesInt {}
        pub struct GpuNttTablesU128 {}

        #[repr(C)]
        pub enum CudaMemcpyKind {
            HostToHost = 0,
            HostToDevice = 1,
            DeviceToHost = 2,
            DeviceToDevice = 3,
            Default = 4,
        }

        #[link(name = "ntt_gpu_stark", kind = "static")]
        unsafe extern "C" {

            pub fn cudaMalloc(devPtr: *mut *mut c_void, size: usize) -> c_uint;
            pub fn cudaMemcpy(
                dst: *mut c_void,
                src: *const c_void,
                count: usize,
                kind: CudaMemcpyKind,
            ) -> c_uint;
            pub fn cudaFree(devPtr: *mut c_void) -> c_uint;

            pub fn create_ntt_tables(p: c_uint, w_n: c_uint, n: c_uint) -> *mut GpuNttTables;
            pub fn destroy_ntt_tables(tables: *mut GpuNttTables);
            pub fn ntt_gpu(
                tables: *mut GpuNttTables,
                data: *mut c_void,
                batch_size: c_uint,
                inverse: bool,
            );

            pub fn create_ntt_tables_int(p: c_uint, w_n: c_uint, n: c_uint)
                -> *mut GpuNttTablesInt;
            pub fn destroy_ntt_tables_int(tables: *mut GpuNttTablesInt);
            pub fn ntt_gpu_int(
                tables: *mut GpuNttTablesInt,
                data: *mut c_void,
                batch_size: c_uint,
                inverse: bool,
            );

            pub fn create_ntt_tables_u128(
                p_lo: c_ulonglong,
                p_hi: c_ulonglong,
                w_n_lo: c_ulonglong,
                w_n_hi: c_ulonglong,
                n: c_uint,
            ) -> *mut GpuNttTablesU128;
            pub fn destroy_ntt_tables_u128(tables: *mut GpuNttTablesU128);
            pub fn ntt_gpu_u128(
                tables: *mut GpuNttTablesU128,
                data: *mut c_void,
                batch_size: c_uint,
                inverse: bool,
            );
        }
    }

    enum GpuNttKind {
        Wmma(*mut ffi::GpuNttTables),
        Int(*mut ffi::GpuNttTablesInt),
        U128(*mut ffi::GpuNttTablesU128),
    }

    pub struct GpuNttExecutor {
        kind: GpuNttKind,
    }

    impl GpuNttExecutor {
        pub fn new<F: Field>(n: usize) -> Option<Self> {
            let prime = F::PRIME;
            let w_n = F::get_root_of_unity(n as u128);

            let sqrt_n_f = (n as f64).sqrt();
            let is_perfect_square = sqrt_n_f == sqrt_n_f.floor();

            if !is_perfect_square {
                return None;
            }

            let sqrt_n = sqrt_n_f as usize;

            let kind = if prime < 2048 && sqrt_n % 16 == 0 {
                let tables =
                    unsafe { ffi::create_ntt_tables(prime as c_uint, w_n as c_uint, n as c_uint) };
                if tables.is_null() {
                    return None;
                }
                GpuNttKind::Wmma(tables)
            } else if prime < u32::MAX as u128 {
                let tables = unsafe {
                    ffi::create_ntt_tables_int(prime as c_uint, w_n as c_uint, n as c_uint)
                };
                if tables.is_null() {
                    return None;
                }
                GpuNttKind::Int(tables)
            } else {
                let p_lo = prime as u64;
                let p_hi = (prime >> 64) as u64;
                let w_lo = w_n as u64;
                let w_hi = (w_n >> 64) as u64;
                let tables =
                    unsafe { ffi::create_ntt_tables_u128(p_lo, p_hi, w_lo, w_hi, n as c_uint) };
                if tables.is_null() {
                    return None;
                }
                GpuNttKind::U128(tables)
            };
            Some(Self { kind })
        }

        pub fn ntt_internal(&self, coeffs: &mut [u128], inverse: bool) {
            let n = coeffs.len();

            let mut d_data: *mut c_void = std::ptr::null_mut();

            unsafe {
                match self.kind {
                    GpuNttKind::Wmma(tables) => {
                        let mut u32_coeffs: Vec<u32> = coeffs.iter().map(|&x| x as u32).collect();
                        let total_bytes = n * std::mem::size_of::<u32>();
                        ffi::cudaMalloc(&mut d_data, total_bytes);
                        ffi::cudaMemcpy(
                            d_data,
                            u32_coeffs.as_mut_ptr() as *mut c_void,
                            total_bytes,
                            ffi::CudaMemcpyKind::HostToDevice,
                        );
                        ffi::ntt_gpu(tables, d_data, 1, inverse);
                        ffi::cudaMemcpy(
                            u32_coeffs.as_mut_ptr() as *mut c_void,
                            d_data,
                            total_bytes,
                            ffi::CudaMemcpyKind::DeviceToHost,
                        );
                        for (i, &val) in u32_coeffs.iter().enumerate() {
                            coeffs[i] = val as u128;
                        }
                    }
                    GpuNttKind::Int(tables) => {
                        let mut u32_coeffs: Vec<u32> = coeffs.iter().map(|&x| x as u32).collect();
                        let total_bytes = n * std::mem::size_of::<u32>();
                        ffi::cudaMalloc(&mut d_data, total_bytes);
                        ffi::cudaMemcpy(
                            d_data,
                            u32_coeffs.as_mut_ptr() as *mut c_void,
                            total_bytes,
                            ffi::CudaMemcpyKind::HostToDevice,
                        );
                        ffi::ntt_gpu_int(tables, d_data, 1, inverse);
                        ffi::cudaMemcpy(
                            u32_coeffs.as_mut_ptr() as *mut c_void,
                            d_data,
                            total_bytes,
                            ffi::CudaMemcpyKind::DeviceToHost,
                        );
                        for (i, &val) in u32_coeffs.iter().enumerate() {
                            coeffs[i] = val as u128;
                        }
                    }
                    GpuNttKind::U128(tables) => {
                        let total_bytes = n * std::mem::size_of::<u128>();
                        ffi::cudaMalloc(&mut d_data, total_bytes);
                        ffi::cudaMemcpy(
                            d_data,
                            coeffs.as_mut_ptr() as *mut c_void,
                            total_bytes,
                            ffi::CudaMemcpyKind::HostToDevice,
                        );
                        ffi::ntt_gpu_u128(tables, d_data, 1, inverse);
                        ffi::cudaMemcpy(
                            coeffs.as_mut_ptr() as *mut c_void,
                            d_data,
                            total_bytes,
                            ffi::CudaMemcpyKind::DeviceToHost,
                        );
                    }
                }
                ffi::cudaFree(d_data);
            }
        }
    }

    impl Drop for GpuNttExecutor {
        fn drop(&mut self) {
            unsafe {
                match self.kind {
                    GpuNttKind::Wmma(tables) => ffi::destroy_ntt_tables(tables),
                    GpuNttKind::Int(tables) => ffi::destroy_ntt_tables_int(tables),
                    GpuNttKind::U128(tables) => ffi::destroy_ntt_tables_u128(tables),
                }
            }
        }
    }
}
