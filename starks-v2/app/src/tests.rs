use super::*;
use crate::llvm::air::codegen::constraint_provider::AirConstraintProvider;
use crate::llvm::air::codegen::AirExpression;
use crate::llvm::air::codegen::AirTraceVariable;
use crate::llvm::air::codegen::RowOffset;

fn poly_eval(coeffs: &[u128], x: u128, prime: u128) -> u128 {
    let mut res = 0;
    let mut current_x_power = 1;
    for &coeff in coeffs {
        res = (res + coeff * current_x_power) % prime;
        current_x_power = (current_x_power * x) % prime;
    }
    res
}

fn poly_add_coeffs(p1: &[u128], p2: &[u128], prime: u128) -> Vec<u128> {
    let len1 = p1.len();
    let len2 = p2.len();
    let max_len = std::cmp::max(len1, len2);
    let mut result = vec![0; max_len];
    for i in 0..max_len {
        let v1 = if i < len1 { p1[i] } else { 0 };
        let v2 = if i < len2 { p2[i] } else { 0 };
        result[i] = (v1 + v2) % prime;
    }
    result
}

fn poly_sub_coeffs(p1: &[u128], p2: &[u128], prime: u128) -> Vec<u128> {
    let len1 = p1.len();
    let len2 = p2.len();
    let max_len = std::cmp::max(len1, len2);
    let mut result = vec![0; max_len];
    for i in 0..max_len {
        let v1 = if i < len1 { p1[i] } else { 0 };
        let v2 = if i < len2 { p2[i] } else { 0 };
        result[i] = (v1 + prime - v2) % prime;
    }
    while result.last() == Some(&0) && result.len() > 1 {
        result.pop();
    }
    if result.is_empty() {
        vec![0]
    } else {
        result
    }
}

fn poly_mul_by_constant(coeffs: &[u128], c: u128, prime: u128) -> Vec<u128> {
    coeffs.iter().map(|&coeff| (coeff * c) % prime).collect()
}

fn poly_shift_coeffs(coeffs: &[u128], shift_factor: u128, prime: u128) -> Vec<u128> {
    let mut result = Vec::with_capacity(coeffs.len());
    let mut current_shift_power = 1;
    for &coeff in coeffs {
        result.push((coeff * current_shift_power) % prime);
        current_shift_power = (current_shift_power * shift_factor) % prime;
    }
    result
}

fn poly_coeffs_from_roots(roots: &[u128], prime: u128) -> Vec<u128> {
    if roots.is_empty() {
        return vec![1];
    }
    let mut p = vec![(prime - roots[0]) % prime, 1];

    for i in 1..roots.len() {
        let root = roots[i];
        let mut p_times_x = vec![0; p.len() + 1];
        p_times_x[1..].copy_from_slice(&p);
        let p_times_root = poly_mul_by_constant(&p, root, prime);
        p = poly_sub_coeffs(&p_times_x, &p_times_root, prime);
    }
    p
}

fn poly_mul_coeffs(p1: &[u128], p2: &[u128], prime: u128) -> Vec<u128> {
    if p1.is_empty() || p1 == [0] || p2.is_empty() || p2 == [0] {
        return vec![0];
    }
    let deg1 = p1.len() - 1;
    let deg2 = p2.len() - 1;
    let mut result_coeffs = vec![0; deg1 + deg2 + 1];
    for i in 0..=deg1 {
        for j in 0..=deg2 {
            result_coeffs[i + j] = (result_coeffs[i + j] + p1[i] * p2[j]) % prime;
        }
    }
    while result_coeffs.last() == Some(&0) && result_coeffs.len() > 1 {
        result_coeffs.pop();
    }
    if result_coeffs.is_empty() {
        vec![0]
    } else {
        result_coeffs
    }
}

fn poly_long_division(num: &[u128], den: &[u128], prime: u128) -> (Vec<u128>, Vec<u128>) {
    if den.is_empty() || den.iter().all(|&c| c == 0) {
        panic!("Division by zero polynomial");
    }

    let mut num_mut = num.to_vec();
    let mut den_trimmed = den.to_vec();
    while den_trimmed.last() == Some(&0) && den_trimmed.len() > 1 {
        den_trimmed.pop();
    }
    if den_trimmed.is_empty() || (den_trimmed.len() == 1 && den_trimmed[0] == 0) {
        panic!("Division by effective zero polynomial after trimming");
    }
    let den_effective = den_trimmed;

    if num_mut.len() < den_effective.len() {
        return (vec![0], num_mut);
    }

    let mut quotient = vec![0; num_mut.len() - den_effective.len() + 1];
    let den_deg = den_effective.len() - 1;
    let den_leading_coeff = den_effective[den_deg];
    let den_leading_coeff_inv = mod_pow(den_leading_coeff, prime - 2, prime);

    for i in (0..=(num_mut.len() - den_effective.len())).rev() {
        let num_current_leading_coeff_idx = i + den_deg;
        if num_current_leading_coeff_idx >= num_mut.len() {
            continue;
        }

        let current_q_coeff =
            (num_mut[num_current_leading_coeff_idx] * den_leading_coeff_inv) % prime;
        quotient[i] = current_q_coeff;

        for j in 0..=den_deg {
            let term_to_subtract = (current_q_coeff * den_effective[j]) % prime;
            if i + j < num_mut.len() {
                num_mut[i + j] = (num_mut[i + j] + prime - term_to_subtract) % prime;
            }
        }
    }

    let mut remainder_coeffs = if den_deg == 0 {
        vec![num_mut[0]]
    } else {
        num_mut[0..den_deg].to_vec()
    };

    while remainder_coeffs.last() == Some(&0) && remainder_coeffs.len() > 1 {
        remainder_coeffs.pop();
    }
    if remainder_coeffs.is_empty() {
        remainder_coeffs.push(0);
    }

    if cfg!(debug_assertions) {
        if num.len() == 8
            && den_effective.len() == 7
            && num[0] == 8
            && num[1] == 16
            && den_effective[0] == 47
            && den_effective[6] == 1
        {
            eprintln!(
                "poly_long_division (DEBUG for N/ZH valid trace): num={:?}, den_eff={:?}, prime={}",
                num, den_effective, prime
            );
            eprintln!(
                "poly_long_division (DEBUG for N/ZH valid trace): computed_quotient={:?}, computed_remainder={:?}",
                quotient, remainder_coeffs
            );
        }
    }

    (quotient, remainder_coeffs)
}

#[derive(Clone, Debug)]
struct TestField {
    prime: u128,
    root_of_unity_cache: std::collections::HashMap<usize, Unity>,
}

impl TestField {
    fn new(prime: u128) -> Self {
        TestField {
            prime,
            root_of_unity_cache: std::collections::HashMap::new(),
        }
    }
    fn find_nth_root(&self, n: usize) -> u128 {
        if self.prime == 97 {
            if n == 2 {
                return 96;
            }
            if n == 4 {
                return 22;
            }
            if n == 8 {
                return 8;
            }
            if n == 16 {
                return 35;
            }
            let exponent = (self.prime - 1) / n as u128;
            let primitive_root = 5;
            return mod_pow(primitive_root, exponent, self.prime);
        }
        let order = self.prime - 1;
        assert!(
            order % n as u128 == 0,
            "n must divide prime-1 for root to exist"
        );
        let g = if self.prime == 101 {
            2
        } else {
            panic!("Need primitive root for prime {}", self.prime)
        };
        mod_pow(g, order / n as u128, self.prime)
    }
}

impl Field for TestField {
    const PRIME: u128 = 0;

    fn get_prime() -> u128 {
        panic!("Use instance specific prime for TestField");
    }

    fn get_nth_root_of_unity(&self, n: usize) -> Unity {
        let generator = self.find_nth_root(n);
        Unity { generator }
    }
}

struct FibonacciConstraintProvider;

impl ConstraintProvider for FibonacciConstraintProvider {
    fn get_constraints_evaluations<FieldType: Field + Clone>(
        &self,
        field: &FieldType,
        trace_coeffs: &Vec<Vec<u128>>,
        initial_domain_sz: usize,
        initial_root_of_unity: Unity,
        expanded_domain_sz: usize,
        expanded_root_of_unity: Unity,
        trace_len_original: usize,
    ) -> Vec<Vec<u128>> {
        assert_eq!(
            trace_coeffs.len(),
            1,
            "Fibonacci trace should have a single column."
        );
        let p = FieldType::PRIME;
        if cfg!(debug_assertions) {
            eprintln!(
                "FibonacciConstraintProvider: Received trace_coeffs (T(x)): {:?}",
                trace_coeffs[0]
            );
        }

        let w = initial_root_of_unity.generator;

        let t_coeffs_shifted_w = poly_shift_coeffs(&trace_coeffs[0], w, p);
        let t_coeffs_shifted_w2 = poly_shift_coeffs(&trace_coeffs[0], mod_pow(w, 2, p), p);

        let n_coeffs_term1 = poly_sub_coeffs(&t_coeffs_shifted_w2, &t_coeffs_shifted_w, p);
        let n_coeffs = poly_sub_coeffs(&n_coeffs_term1, &trace_coeffs[0], p);

        if cfg!(debug_assertions) {
            eprintln!(
                "FibonacciConstraintProvider: Computed N(x) coeffs: {:?}",
                n_coeffs
            );
        }

        if trace_len_original < 3 {
            return vec![vec![0; expanded_domain_sz]];
        }
        let num_zh_roots = trace_len_original - 2;
        let mut zh_roots = Vec::with_capacity(num_zh_roots);
        for i in 0..num_zh_roots {
            zh_roots.push(mod_pow(w, i as u128, p));
        }
        let zh_coeffs = poly_coeffs_from_roots(&zh_roots, p);

        if cfg!(debug_assertions) {
            eprintln!("FibonacciConstraintProvider: Z_H(x) roots: {:?}", zh_roots);
            eprintln!(
                "FibonacciConstraintProvider: Z_H(x) coeffs: {:?}",
                zh_coeffs
            );
            for &root_val in &zh_roots {
                let divisor_coeffs = vec![(p.wrapping_sub(root_val)) % p, 1];
                let (_q_zh_check, r_zh_check) = poly_long_division(&zh_coeffs, &divisor_coeffs, p);
                let zh_at_root_is_zero =
                    r_zh_check.iter().all(|&c| c == 0) || r_zh_check == vec![0];
                eprintln!(
                    "FibonacciConstraintProvider: Z_H(x) (coeffs: {:?}) divisible by (x - {:3})? {}, Remainder: {:?}",
                    zh_coeffs, root_val, zh_at_root_is_zero, r_zh_check
                );
                if !zh_at_root_is_zero {
                    panic!(
                        "FATAL: poly_coeffs_from_roots produced Z_H(x) that does not have root {}! Z_H(x)={:?}, (x-root)={:?}, Remainder={:?}",
                        root_val, zh_coeffs, divisor_coeffs, r_zh_check
                    );
                }
            }

            for &root_val in &zh_roots {
                let divisor_coeffs = vec![(p.wrapping_sub(root_val)) % p, 1];
                let (_q_single_root, r_single_root) =
                    poly_long_division(&n_coeffs, &divisor_coeffs, p);
                let n_at_root_is_zero =
                    r_single_root.iter().all(|&c| c == 0) || r_single_root == vec![0];
                eprintln!(
                    "FibonacciConstraintProvider: N(x) (coeffs: {:?}) divisible by (x - {:3})? {}, Remainder: {:?}",
                    n_coeffs, root_val, n_at_root_is_zero, r_single_root
                );
            }
        }

        let (c_coeffs, remainder_coeffs) = poly_long_division(&n_coeffs, &zh_coeffs, p);

        let remainder_is_zero =
            remainder_coeffs.iter().all(|&c| c == 0) || remainder_coeffs == vec![0];
        if !remainder_is_zero {
            panic!(
                "FibonacciConstraintProvider: Remainder is not zero in N(x)/Z_H(x)! Trace does not satisfy Fibonacci. N={:?}, Z_H={:?}, R={:?}",
                n_coeffs, zh_coeffs, remainder_coeffs
            );
        }

        let c_evals_ext = StarkV2::<FieldType, FibonacciConstraintProvider>::evaluate_on_values(
            &c_coeffs,
            expanded_domain_sz,
            expanded_root_of_unity,
        );

        vec![c_evals_ext]
    }
}

#[test]
fn test_poly_utils() {
    let prime = 97;
    let roots1 = vec![1, 2];
    let p1_coeffs = poly_coeffs_from_roots(&roots1, prime);
    assert_eq!(p1_coeffs, vec![2, (prime - 3) % prime, 1]);

    let num_coeffs = vec![93, 0, 95, 1];
    let den_coeffs = vec![94, 1];
    let (q_coeffs, r_coeffs) = poly_long_division(&num_coeffs, &den_coeffs, prime);
    assert_eq!(q_coeffs, vec![3, 1, 1]);
    assert_eq!(r_coeffs, vec![5]);

    let num2_coeffs = vec![2, 94, 1];
    let den2_coeffs = vec![96, 1];
    let (q2_coeffs, r2_coeffs) = poly_long_division(&num2_coeffs, &den2_coeffs, prime);
    assert_eq!(q2_coeffs, vec![95, 1]);
    assert!(r2_coeffs.iter().all(|&c| c == 0) || r2_coeffs == vec![0]);

    let p_coeffs_shift = vec![2, 94, 1];
    let shifted_coeffs = poly_shift_coeffs(&p_coeffs_shift, 2, prime);
    assert_eq!(shifted_coeffs, vec![2, 91, 4]);
}

#[test]
fn test_poly_long_division_exact() {
    let prime = 97;

    let q_poly = vec![5, 1];
    let d_poly = vec![3, 95, 1];

    let p_poly_expected = vec![15, 90, 3, 1];
    let p_poly_calculated = poly_mul_coeffs(&q_poly, &d_poly, prime);
    assert_eq!(p_poly_calculated, p_poly_expected, "poly_mul_coeffs failed");

    let (q_calc, r_calc) = poly_long_division(&p_poly_calculated, &d_poly, prime);
    assert_eq!(q_calc, q_poly, "Quotient mismatch in exact division");
    assert!(
        r_calc.iter().all(|&c| c == 0) || r_calc == vec![0],
        "Remainder should be zero in exact division, got {:?}",
        r_calc
    );

    let d_test_zh_like = vec![47, 65, 39, 7, 10, 25, 1];
    let q_test_quotient_like = vec![3, 70];

    let n_coeffs_from_panic = vec![31, 68, 25, 52, 34, 4, 7, 70];
    let p_test_calculated = poly_mul_coeffs(&q_test_quotient_like, &d_test_zh_like, prime);

    let (q_exact_calc, r_exact_calc) =
        poly_long_division(&p_test_calculated, &d_test_zh_like, prime);
    assert_eq!(
        q_exact_calc, q_test_quotient_like,
        "Quotient mismatch for P_exact = Q_test * D_test"
    );
    assert!(
        r_exact_calc.iter().all(|&c| c == 0) || r_exact_calc == vec![0],
        "Remainder should be zero for P_exact = Q_test * D_test, got {:?}",
        r_exact_calc
    );
}

#[test]
fn test_ntt_intt_consistency() {
    #[derive(Clone, Debug)]
    struct FieldForNttTest;
    impl FieldForNttTest {
        fn find_root(n: usize, p: u128) -> u128 {
            if p == 97 {
                let exponent = (p - 1) / n as u128;
                let primitive_root = 5;
                return mod_pow(primitive_root, exponent, p);
            }
            panic!("Unsupported prime");
        }
    }
    impl Field for FieldForNttTest {
        const PRIME: u128 = 97;
        fn get_prime() -> u128 {
            Self::PRIME
        }
        fn get_nth_root_of_unity(&self, n: usize) -> Unity {
            let specific_nth_root = Self::find_root(n, Self::PRIME);
            Unity {
                generator: specific_nth_root,
            }
        }
    }

    let field_instance = FieldForNttTest;
    let prime = FieldForNttTest::PRIME;

    let coeffs1: Vec<u128> = vec![1, 1, 0, 0];
    let n1 = coeffs1.len();
    assert!(n1.is_power_of_two());
    let unity1 = field_instance.get_nth_root_of_unity(n1);

    let evals1 = ntt_1d_iterative::<FieldForNttTest>(&coeffs1, unity1);

    let recovered_coeffs1 = intt_1d::<FieldForNttTest>(&evals1, unity1);
    assert_eq!(
        coeffs1, recovered_coeffs1,
        "NTT/INTT failed for x+1 (size 4)"
    );

    let coeffs2: Vec<u128> = vec![4, 3, 2, 1, 0, 0, 0, 0];
    let n2 = coeffs2.len();
    assert!(n2.is_power_of_two());
    let unity2 = field_instance.get_nth_root_of_unity(n2);

    let evals2 = ntt_1d_iterative::<FieldForNttTest>(&coeffs2, unity2);
    let recovered_coeffs2 = intt_1d::<FieldForNttTest>(&evals2, unity2);
    assert_eq!(
        coeffs2, recovered_coeffs2,
        "NTT/INTT failed for x^3+2x^2+3x+4 (size 8)"
    );

    let fib_coeffs_for_t = vec![0, 1, 1, 2, 3, 5, 8, 13];
    let fib_trace_L8_padded = vec![0, 1, 1, 2, 3, 5, 8, 13];
    let n_fib = fib_trace_L8_padded.len();
    let unity_fib = field_instance.get_nth_root_of_unity(n_fib);
    let t_coeffs_actual = intt_1d::<FieldForNttTest>(&fib_trace_L8_padded, unity_fib);

    let n_t_coeffs = t_coeffs_actual.len();
    let unity_t_coeffs = field_instance.get_nth_root_of_unity(n_t_coeffs);
    let t_coeffs_evals = ntt_1d_iterative::<FieldForNttTest>(&t_coeffs_actual, unity_t_coeffs);
    let recovered_t_coeffs = intt_1d::<FieldForNttTest>(&t_coeffs_evals, unity_t_coeffs);
    assert_eq!(
        t_coeffs_actual, recovered_t_coeffs,
        "NTT/INTT failed for Fibonacci T_coeffs (size 8)"
    );
}

#[derive(Clone, Debug)]
struct TestField97;
impl TestField97 {
    fn find_nth_root_static(n: usize, p: u128) -> u128 {
        if p == 97 {
            let exponent = (p - 1) / n as u128;
            let primitive_root = 5;
            return mod_pow(primitive_root, exponent, p);
        }
        panic!("Unsupported prime for find_nth_root_static");
    }
}
impl Field for TestField97 {
    const PRIME: u128 = 97;
    fn get_prime() -> u128 {
        Self::PRIME
    }
    fn get_nth_root_of_unity(&self, n: usize) -> Unity {
        let specific_nth_root = Self::find_nth_root_static(n, Self::PRIME);
        Unity {
            generator: specific_nth_root,
        }
    }
}

#[test]
fn test_fibonacci_stark() {
    let prime = 97;
    let test_field_instance = TestField::new(prime);

    let stark_instance = StarkV2::<TestField97, FibonacciConstraintProvider> {
        field: TestField97,
        generator: ChallengeGenerator { field: TestField97 },
        constraint_provider: FibonacciConstraintProvider,
    };

    let trace_len_original = 8;
    let mut fib_trace = vec![0u128; trace_len_original];
    fib_trace[0] = 0;
    fib_trace[1] = 1;
    for i in 2..trace_len_original {
        fib_trace[i] = (fib_trace[i - 1] + fib_trace[i - 2]) % TestField97::PRIME;
    }

    let blowup_factor = 4;
    let fri_num_rounds = 3;
    let num_queries = 3;

    let proof = stark_instance.create_proof(
        &vec![fib_trace.clone()],
        blowup_factor,
        fri_num_rounds,
        num_queries,
    );

    let fri_protocol_instance = FRIProtocol {
        generator: stark_instance.generator.clone(),
    };
    let is_valid = fri_protocol_instance.verify_proof(&proof, 32, num_queries);
    assert!(
        is_valid,
        "Fibonacci STARK proof verification failed for a valid trace"
    );

    let mut bad_fib_trace = fib_trace.clone();
    bad_fib_trace[trace_len_original - 1] =
        (bad_fib_trace[trace_len_original - 1] + 10) % TestField97::PRIME;
    let result_bad_trace = std::panic::catch_unwind(|| {
        stark_instance.create_proof(
            &vec![bad_fib_trace.clone()],
            blowup_factor,
            fri_num_rounds,
            num_queries,
        )
    });
    assert!(
        result_bad_trace.is_err(),
        "Prover should panic for invalid Fibonacci trace due to non-zero remainder in constraint division."
    );
}
