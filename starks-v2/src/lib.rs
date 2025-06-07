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
    pub fn create_proof_1d(
        &self,
        execution_trace: Vec<u128>,
        blowup_factor: usize,
        fri_num_rounds: usize,
        num_queries: usize,
    ) -> StarkProof {
        let initial_domain_sz_orig = execution_trace.len();
        let initial_domain_sz = initial_domain_sz_orig.next_power_of_two();

        let mut padded_trace = execution_trace.clone();
        if padded_trace.len() < initial_domain_sz {
            padded_trace.resize(initial_domain_sz, 0);
        }

        let initial_root_of_unity = self.field.get_nth_root_of_unity(initial_domain_sz);
        let _initial_domain_points = (0..initial_domain_sz)
            .into_iter()
            .map(|i| mod_pow(initial_root_of_unity.generator, i as u128, FieldType::PRIME))
            .collect::<Vec<_>>();
        let trace_coeffs = intt_1d::<FieldType>(&execution_trace, initial_root_of_unity);
        let expanded_domain_sz = blowup_factor * initial_domain_sz;
        let expanded_root_of_unity = self.field.get_nth_root_of_unity(expanded_domain_sz);
        let expanded_domain = (0..expanded_domain_sz)
            .into_iter()
            .map(|i| {
                mod_pow(
                    expanded_root_of_unity.generator,
                    i as u128,
                    FieldType::PRIME,
                )
            })
            .collect::<Vec<_>>();

        let expanded_trace_evals =
            Self::evaluate_on_values(&trace_coeffs, expanded_domain_sz, expanded_root_of_unity);

        let merkle_commitment_trace = merkletree::MerkleTree::new(
            expanded_trace_evals
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
            &trace_coeffs,
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

        let random_combination_evals_ext = Self::create_random_combination(
            &combined_constraint_evals_ext,
            &expanded_trace_evals,
            alpha,
        );

        let fri_protocol_instance = FRIProtocol {
            generator: self.generator.clone(),
        };

        let fri_proof = fri_protocol_instance.generate_fri_proof(
            fri_num_rounds,
            expanded_domain,
            random_combination_evals_ext.clone(),
        );

        let queries =
            fri_protocol_instance.generate_queries(&fri_proof, expanded_domain_sz, num_queries);

        let mut queried_trace_openings = Vec::with_capacity(queries.len());
        for &query_idx in &queries {
            if query_idx < expanded_trace_evals.len() {
                let value = expanded_trace_evals[query_idx];
                let proof_path = merkle_commitment_trace
                    .get_proof(query_idx)
                    .expect("Failed to get Merkle proof for trace evaluation");
                queried_trace_openings.push(MerkleOpening {
                    index: query_idx,
                    value,
                    merkle_path: proof_path,
                });
            } else {
                if cfg!(debug_assertions) {
                    eprintln!(
                        "Prover: Query index {} out of bounds for expanded_trace_evals (len {})",
                        query_idx,
                        expanded_trace_evals.len()
                    );
                }
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
            } else {
                if cfg!(debug_assertions) {
                    eprintln!(
                        "Prover: Query index {} out of bounds for combined_constraint_evals_ext (len {})",
                        query_idx,
                        combined_constraint_evals_ext.len()
                    );
                }
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
        trace_eval: &Vec<u128>,
        alpha: u128,
    ) -> Vec<u128> {
        (0..trace_eval.len())
            .into_iter()
            .map(|i| {
                (trace_eval[i] + (alpha * combined_constraint_eval[i]) % FieldType::PRIME)
                    % FieldType::PRIME
            })
            .collect::<Vec<_>>()
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
        let queries = self.generate_queries(&proof.fri_proof, exp_domain_sz, num_queries);
        let query_responses_struct = self.query_response_generation(&queries, &proof);

        let trace_root_string = match proof.trace_merkle_tree.get_root() {
            Some(r) => r.clone(),
            None => {
                if cfg!(debug_assertions) {
                    eprintln!("Trace Merkle tree has no root.");
                }
                return false;
            }
        };
        let computed_alpha = self.generator.generate_alpha(&trace_root_string);
        if computed_alpha != proof.alpha {
            if cfg!(debug_assertions) {
                eprintln!(
                    "Alpha mismatch: computed {}, proof {}",
                    computed_alpha, proof.alpha
                );
            }
            return false;
        }

        let num_fri_folding_rounds = proof.fri_proof.betas.len();

        if query_responses_struct.layers.len() < num_fri_folding_rounds {
            if cfg!(debug_assertions) {
                eprintln!(
                    "FRI Verifier: Not enough layers in query_responses_struct. Expected at least {}, got {}.",
                    num_fri_folding_rounds,
                    query_responses_struct.layers.len()
                );
            }
            return false;
        }

        for round_idx in 0..num_fri_folding_rounds {
            let layer_openings = &query_responses_struct.layers[round_idx];
            if round_idx >= proof.fri_proof.commitments.len() {
                if cfg!(debug_assertions) {
                    eprintln!(
                        "FRI Verifier: Missing Merkle tree for layer {} in proof.",
                        round_idx
                    );
                }
                return false;
            }
            let merkle_tree_for_layer_k = &proof.fri_proof.commitments[round_idx];

            let expected_merkle_root = match merkle_tree_for_layer_k.get_root() {
                Some(r) => r,
                None => {
                    if cfg!(debug_assertions) {
                        eprintln!(
                            "FRI Verifier: Merkle tree for FRI layer {} has no root.",
                            round_idx
                        );
                    }
                    return false;
                }
            };

            for item in layer_openings {
                match &item.merkle_path {
                    Some(path) => {
                        let leaf_data_unhashed = format!("{:032x}", item.value);
                        if !merkletree::MerkleTree::verify_proof(
                            &leaf_data_unhashed,
                            path,
                            expected_merkle_root,
                        ) {
                            if cfg!(debug_assertions) {
                                eprintln!(
                                    "FRI Verifier: Merkle proof verification failed for layer {}, index {}, value {}",
                                    round_idx, item.index, item.value
                                );
                            }
                            return false;
                        }
                    }
                    None => {
                        if cfg!(debug_assertions) {
                            eprintln!(
                                "FRI Verifier: Missing Merkle path for layer {} (which should have one), index {}.",
                                round_idx, item.index
                            );
                        }
                        return false;
                    }
                }
            }
        }

        let inv_2 = mod_pow(2, FieldType::PRIME - 2, FieldType::PRIME);
        let initial_expanded_root = self
            .generator
            .field
            .get_nth_root_of_unity(exp_domain_sz)
            .generator;

        if query_responses_struct.layers.len() < num_fri_folding_rounds + 1 {
            if cfg!(debug_assertions) {
                eprintln!(
                    "FRI Verifier (Consistency): Not enough layers in query_responses_struct. Expected at least {}, got {}.",
                    num_fri_folding_rounds + 1,
                    query_responses_struct.layers.len()
                );
            }
            return false;
        }

        for &initial_query_idx_l0 in &queries {
            for k_fold in 0..num_fri_folding_rounds {
                let layer_k_openings = &query_responses_struct.layers[k_fold];
                let layer_k_plus_1_openings = &query_responses_struct.layers[k_fold + 1];
                let j_idx = initial_query_idx_l0 / (1 << (k_fold + 1));

                let actual_val_in_lk_plus_1 = match layer_k_plus_1_openings
                    .iter()
                    .find(|item| item.index == j_idx)
                    .map(|item| item.value)
                {
                    Some(val) => val,
                    None => {
                        if cfg!(debug_assertions) {
                            eprintln!(
                                "FRI Verifier (Consistency): L_{}[{}] (derived from L0 idx {}, k_fold {}) not found in query responses for L_{}. Provided indices: {:?}",
                                k_fold + 1,
                                j_idx,
                                initial_query_idx_l0,
                                k_fold,
                                k_fold + 1,
                                layer_k_plus_1_openings
                                    .iter()
                                    .map(|item| item.index)
                                    .collect::<Vec<_>>()
                            );
                        }
                        return false;
                    }
                };

                if k_fold >= proof.fri_proof.layers_values.len() {
                    if cfg!(debug_assertions) {
                        eprintln!(
                            "FRI Verifier (Consistency): Missing L_k values for layer {}. (proof.fri_proof.layers_values index out of bounds)",
                            k_fold
                        );
                    }
                    return false;
                }
                let layer_k_domain_size_d_k = proof.fri_proof.layers_values[k_fold].len();
                let even_partner_idx_in_lk = j_idx;
                let odd_partner_idx_in_lk = j_idx + layer_k_domain_size_d_k / 2;

                let y_even_opt = layer_k_openings
                    .iter()
                    .find(|item| item.index == even_partner_idx_in_lk)
                    .map(|item| item.value);
                let y_odd_opt = layer_k_openings
                    .iter()
                    .find(|item| item.index == odd_partner_idx_in_lk)
                    .map(|item| item.value);

                let (y_even, y_odd) = match (y_even_opt, y_odd_opt) {
                    (Some(ye), Some(yo)) => (ye, yo),
                    _ => {
                        if cfg!(debug_assertions) {
                            eprintln!(
                                "FRI Verifier (Consistency): In L{}, could not find pair L_k[{}] ({:?}) or L_k[{}] ({:?}) needed for L0 idx {}. Target L_{}[{}]. Queried L_k indices: {:?}",
                                k_fold,
                                even_partner_idx_in_lk,
                                y_even_opt.is_some(),
                                odd_partner_idx_in_lk,
                                y_odd_opt.is_some(),
                                initial_query_idx_l0,
                                k_fold + 1,
                                j_idx,
                                layer_k_openings
                                    .iter()
                                    .map(|item| item.index)
                                    .collect::<Vec<_>>()
                            );
                        }
                        return false;
                    }
                };

                if k_fold >= proof.fri_proof.betas.len() {
                    if cfg!(debug_assertions) {
                        eprintln!(
                            "FRI Verifier (Consistency): Missing beta_{} in proof.",
                            k_fold
                        );
                    }
                    return false;
                }
                let beta_k = proof.fri_proof.betas[k_fold];

                let domain_k_generator =
                    mod_pow(initial_expanded_root, 1 << k_fold, FieldType::PRIME);
                let x_val = mod_pow(domain_k_generator, j_idx as u128, FieldType::PRIME);

                if x_val == 0 {
                    if cfg!(debug_assertions) && FieldType::PRIME > 0 {
                        eprintln!(
                            "FRI Verifier (Consistency): x_val is 0, cannot compute (2x_val)^-1. k_fold={}, j_idx={}",
                            k_fold, j_idx
                        );
                    }
                    return false;
                }
                let inv_2x_val = mod_pow(
                    (2 * x_val) % FieldType::PRIME,
                    FieldType::PRIME - 2,
                    FieldType::PRIME,
                );

                let sum_terms = (y_even + y_odd) % FieldType::PRIME;
                let diff_terms = (y_even + FieldType::PRIME - y_odd) % FieldType::PRIME;

                let term1 = (sum_terms * inv_2) % FieldType::PRIME;
                let term2 = (diff_terms * inv_2x_val) % FieldType::PRIME;

                let calculated_folded_value =
                    (term1 + (beta_k * term2) % FieldType::PRIME) % FieldType::PRIME;

                if calculated_folded_value != actual_val_in_lk_plus_1 {
                    if cfg!(debug_assertions) {
                        let k_plus_1 = k_fold + 1;
                        eprintln!(
                            "FRI Verifier (Folding Mismatch): L{} -> L{}",
                            k_fold, k_plus_1
                        );
                        eprintln!(
                            "  L0 query idx: {}, Target L_{}[{}] (j_idx)",
                            initial_query_idx_l0, k_plus_1, j_idx
                        );
                        eprintln!(
                            "  Pair from L_k: L_k[{}]={}, L_k[{}]={}",
                            even_partner_idx_in_lk, y_even, odd_partner_idx_in_lk, y_odd
                        );
                        eprintln!("  beta_{} = {}", k_fold, beta_k);
                        eprintln!(
                            "  Calculated L_{}[{}] = {}",
                            k_plus_1, j_idx, calculated_folded_value
                        );
                        eprintln!(
                            "  Actual L_{}[{}] from proof = {}",
                            k_plus_1, j_idx, actual_val_in_lk_plus_1
                        );
                    }
                    return false;
                }
            }
        }

        if query_responses_struct.layers.len() <= num_fri_folding_rounds {
            if cfg!(debug_assertions) {
                eprintln!(
                    "FRI Verifier (Final Layer): Final layer missing from query_responses_struct. Expected layer index {}, got {} layers.",
                    num_fri_folding_rounds,
                    query_responses_struct.layers.len()
                );
            }
            return false;
        }
        let final_layer_openings = &query_responses_struct.layers[num_fri_folding_rounds];

        if !proof.fri_proof.final_layer_values.is_empty() {
            let first_val_from_proof_final_layer = proof.fri_proof.final_layer_values[0];
            if !proof
                .fri_proof
                .final_layer_values
                .iter()
                .all(|&v| v == first_val_from_proof_final_layer)
            {
                if cfg!(debug_assertions) {
                    eprintln!(
                        "FRI Verifier: Final layer (L_N) values *in proof.fri_proof.final_layer_values* are not all identical. Values: {:?}",
                        proof.fri_proof.final_layer_values
                    );
                }
                return false;
            }

            if !final_layer_openings.is_empty() {
                let first_queried_final_val = final_layer_openings[0].value;
                if first_queried_final_val != first_val_from_proof_final_layer {
                    if cfg!(debug_assertions) {
                        eprintln!(
                            "FRI Verifier: First queried L_N value ({}) does not match constant value from proof.fri_proof.final_layer_values ({}).",
                            first_queried_final_val, first_val_from_proof_final_layer
                        );
                    }
                    return false;
                }
                if !final_layer_openings
                    .iter()
                    .all(|item| item.value == first_queried_final_val)
                {
                    if cfg!(debug_assertions) {
                        eprintln!(
                            "FRI Verifier: *Queried* L_N values are not all identical. Values: {:?}",
                            final_layer_openings
                                .iter()
                                .map(|item| item.value)
                                .collect::<Vec<_>>()
                        );
                    }
                    return false;
                }
            } else if num_queries > 0 {
                if cfg!(debug_assertions) {
                    eprintln!(
                        "FRI Verifier: No L_N openings found in query_responses_struct despite num_queries > 0."
                    );
                }
            }
        } else if num_queries > 0 && !final_layer_openings.is_empty() {
            let first_queried_final_val = final_layer_openings[0].value;
            if !final_layer_openings
                .iter()
                .all(|item| item.value == first_queried_final_val)
            {
                if cfg!(debug_assertions) {
                    eprintln!(
                        "FRI Verifier: *Queried* L_N values are not all identical (proof.fri_proof.final_layer_values was empty). Values: {:?}",
                        final_layer_openings
                            .iter()
                            .map(|item| item.value)
                            .collect::<Vec<_>>()
                    );
                }
                return false;
            }
        }

        let trace_merkle_root = match proof.trace_merkle_tree.get_root() {
            Some(r) => r,
            None => {
                if cfg!(debug_assertions) {
                    eprintln!("STARK Verifier: Trace Merkle tree has no root.");
                }
                return false;
            }
        };
        let constraint_merkle_root = match proof.constraint_merkle_tree.get_root() {
            Some(r) => r,
            None => {
                if cfg!(debug_assertions) {
                    eprintln!("STARK Verifier: Constraint Merkle tree has no root.");
                }
                return false;
            }
        };

        for &query_idx_zi in &queries {
            let p_at_zi = match query_responses_struct
                .layers
                .get(0)
                .and_then(|l0_response_layer| {
                    l0_response_layer
                        .iter()
                        .find(|item| item.index == query_idx_zi)
                        .map(|item| item.value)
                }) {
                Some(val) => val,
                None => {
                    if cfg!(debug_assertions) {
                        eprintln!(
                            "STARK Verifier: P(z_i={}) not found in FRI L0 responses. L0 queried indices: {:?}",
                            query_idx_zi,
                            query_responses_struct
                                .layers
                                .get(0)
                                .map(|l| l.iter().map(|i| i.index).collect::<Vec<_>>())
                                .unwrap_or_default()
                        );
                    }
                    return false;
                }
            };

            let (t_at_zi, t_path) = match proof
                .queried_trace_openings
                .iter()
                .find(|item| item.index == query_idx_zi)
            {
                Some(item) => (item.value, &item.merkle_path),
                None => {
                    if cfg!(debug_assertions) {
                        eprintln!(
                            "STARK Verifier: T(z_i={}) opening not found in proof.queried_trace_openings.",
                            query_idx_zi
                        );
                    }
                    return false;
                }
            };
            let t_leaf_data_str = format!("{:032x}", t_at_zi);
            if !merkletree::MerkleTree::verify_proof(&t_leaf_data_str, t_path, trace_merkle_root) {
                if cfg!(debug_assertions) {
                    eprintln!(
                        "STARK Verifier: Merkle proof verification failed for T(z_i={}).",
                        query_idx_zi
                    );
                }
                return false;
            }

            let (c_at_zi, c_path) = match proof
                .queried_constraint_openings
                .iter()
                .find(|item| item.index == query_idx_zi)
            {
                Some(item) => (item.value, &item.merkle_path),
                None => {
                    if cfg!(debug_assertions) {
                        eprintln!(
                            "STARK Verifier: C(z_i={}) opening not found in proof.queried_constraint_openings.",
                            query_idx_zi
                        );
                    }
                    return false;
                }
            };
            let c_leaf_data_str = c_at_zi.to_string();
            if !merkletree::MerkleTree::verify_proof(
                &c_leaf_data_str,
                c_path,
                constraint_merkle_root,
            ) {
                if cfg!(debug_assertions) {
                    eprintln!(
                        "STARK Verifier: Merkle proof verification failed for C(z_i={}).",
                        query_idx_zi
                    );
                }
                return false;
            }

            let expected_p_at_zi =
                (t_at_zi + (proof.alpha * c_at_zi) % FieldType::PRIME) % FieldType::PRIME;
            if p_at_zi != expected_p_at_zi {
                if cfg!(debug_assertions) {
                    eprintln!(
                        "STARK Verifier: Polynomial identity check failed for z_i = {}.",
                        query_idx_zi
                    );
                    eprintln!("  P(z_i) = {}", p_at_zi);
                    eprintln!("  T(z_i) = {}", t_at_zi);
                    eprintln!("  C(z_i) = {}", c_at_zi);
                    eprintln!("  alpha = {}", proof.alpha);
                    eprintln!(
                        "  Expected P(z_i) = (T(z_i) + alpha * C(z_i)) % PRIME = {}",
                        expected_p_at_zi
                    );
                }
                return false;
            }
        }

        true
    }
}

pub trait ConstraintProvider {
    fn get_constraints_evaluations<FieldType: Field + Clone>(
        &self,
        field: &FieldType,
        trace_coeffs: &Vec<u128>,
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
}

fn ntt_1d_iterative<FieldType>(coeffs: &Vec<u128>, unity: Unity) -> Vec<u128>
where
    FieldType: Field,
{
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
