//! ============================================================================
//! `verify_cpu.rs` — CPU verification of the B_3 property, reversible O(1)
//! bitset-shift primitives, greedy B_3 generation (OEIS A004023), and
//! Theorem 2.1(a) Exact (2,1)-Difference Harmonic Conservation Identity.
//! ============================================================================

use crate::records::{b3_diophantine_haar_boost_and_bound, erdos41_psi, min_dyadic_shell_for_w};
use serde::Serialize;
use std::collections::HashSet;

#[inline]
pub fn set_bit_u64(arr: &mut [u64], bit: usize) {
    arr[bit >> 6] |= 1u64 << (bit & 63);
}

#[inline]
pub fn xor_bit_u64(arr: &mut [u64], bit: usize) {
    arr[bit >> 6] ^= 1u64 << (bit & 63);
}

/// Returns true iff `((src << shift) & dst) != 0`.
#[inline]
pub fn shift_overlaps_u64(src: &[u64], shift: usize, dst: &[u64]) -> bool {
    let word_shift = shift >> 6;
    let bit_shift = shift & 63;
    let dst_words = dst.len();
    if bit_shift == 0 {
        for (i, &w) in src.iter().enumerate() {
            let j = i + word_shift;
            if j < dst_words && (w & dst[j]) != 0 {
                return true;
            }
        }
    } else {
        let inv_shift = 64 - bit_shift;
        for (i, &w) in src.iter().enumerate() {
            if w == 0 {
                continue;
            }
            let j0 = i + word_shift;
            if j0 < dst_words && ((w << bit_shift) & dst[j0]) != 0 {
                return true;
            }
            let j1 = j0 + 1;
            if j1 < dst_words && ((w >> inv_shift) & dst[j1]) != 0 {
                return true;
            }
        }
    }
    false
}

/// Performs `dst ^= (src << shift)`.
#[inline]
pub fn shift_xor_into_u64(src: &[u64], shift: usize, dst: &mut [u64]) {
    let word_shift = shift >> 6;
    let bit_shift = shift & 63;
    let dst_words = dst.len();
    if bit_shift == 0 {
        for (i, &w) in src.iter().enumerate() {
            let j = i + word_shift;
            if j < dst_words {
                dst[j] ^= w;
            }
        }
    } else {
        let inv_shift = 64 - bit_shift;
        for (i, &w) in src.iter().enumerate() {
            if w == 0 {
                continue;
            }
            let j0 = i + word_shift;
            if j0 < dst_words {
                dst[j0] ^= w << bit_shift;
            }
            let j1 = j0 + 1;
            if j1 < dst_words {
                dst[j1] ^= w >> inv_shift;
            }
        }
    }
}

/// CPU twin of `can_add_b3` in `src/kernels.cu`: tests whether `A \cup {x}`
/// (`x > max(A)`) is a B_3 set in O(1) word operations using the 1-sum, 2-sum,
/// and 3-sum bitsets `(m1, m2, m3)`.
#[inline]
pub fn can_add_b3_cpu(m1: &[u64; 2], m2: &[u64; 4], m3: &[u64; 6], x: usize) -> bool {
    if shift_overlaps_u64(m1, x, m2) {
        return false;
    }
    if shift_overlaps_u64(m2, x, m3) {
        return false;
    }
    if shift_overlaps_u64(m1, 2 * x, m3) {
        return false;
    }
    true
}

/// CPU twin of `push_b3` in `src/kernels.cu`.
#[inline]
pub fn push_b3_cpu(m1: &mut [u64; 2], m2: &mut [u64; 4], m3: &mut [u64; 6], x: usize) {
    shift_xor_into_u64(m2, x, m3);
    shift_xor_into_u64(m1, 2 * x, m3);
    xor_bit_u64(m3, 3 * x);

    shift_xor_into_u64(m1, x, m2);
    xor_bit_u64(m2, 2 * x);

    xor_bit_u64(m1, x);
}

/// CPU twin of `pop_b3` in `src/kernels.cu`: reverses `push_b3_cpu` in-place via XOR.
#[inline]
pub fn pop_b3_cpu(m1: &mut [u64; 2], m2: &mut [u64; 4], m3: &mut [u64; 6], x: usize) {
    xor_bit_u64(m1, x);

    shift_xor_into_u64(m1, x, m2);
    xor_bit_u64(m2, 2 * x);

    shift_xor_into_u64(m2, x, m3);
    shift_xor_into_u64(m1, 2 * x, m3);
    xor_bit_u64(m3, 3 * x);
}

/// Verifies whether a strictly increasing sequence `a` is a B_3 sequence
/// (all 3-sums a_i + a_j + a_k with i <= j <= k are distinct).
pub fn is_b3_sequence(a: &[u32]) -> bool {
    for w in a.windows(2) {
        if w[0] == 0 || w[0] >= w[1] {
            return false;
        }
    }
    if a.first() == Some(&0) {
        return false;
    }
    let m = a.len();
    let expected = m * (m + 1) * (m + 2) / 6;
    let mut sums3 = HashSet::with_capacity(expected);
    for i in 0..m {
        for j in i..m {
            for k in j..m {
                if !sums3.insert(a[i] + a[j] + a[k]) {
                    return false;
                }
            }
        }
    }
    true
}

/// Verifies the Injectivity Lemma of Theorem 2.1(a): for any B_3 sequence `a`,
/// the map `(i, j, k) -> w_{i,j,k} = a_k - a_i - a_j` is strictly injective on
/// `T_m = {(i, j, k) : 0 <= i <= j < k < m}` of cardinality `\binom{m+1}{3}`,
/// and every triple satisfies `|w_{i,j,k}| + 2 <= a_k`.
pub fn verify_ordered_21_diff_injectivity(a: &[u32]) -> bool {
    let m = a.len();
    if m < 2 {
        return true;
    }
    let expected = m * (m - 1) * (m + 1) / 6;
    let mut seen_w = HashSet::with_capacity(expected);
    for k in 1..m {
        let ak = a[k] as i64;
        for j in 0..k {
            for i in 0..=j {
                let w = ak - (a[i] as i64) - (a[j] as i64);
                if w.abs() + 2 > ak {
                    return false;
                }
                if !seen_w.insert(w) {
                    return false;
                }
            }
        }
    }
    seen_w.len() == expected
}

/// Generates the first `num_terms` elements of the greedy B_3 sequence (OEIS A004023).
pub fn generate_greedy_b3_sequence(num_terms: usize) -> Vec<u32> {
    let mut a: Vec<u32> = Vec::with_capacity(num_terms);
    let mut sum2: HashSet<u32> = HashSet::new();
    let mut sum3: HashSet<u32> = HashSet::new();
    let mut x = 1u32;

    while a.len() < num_terms {
        let mut ok = true;
        for &ai in &a {
            if sum2.contains(&(ai + x)) || sum3.contains(&(ai + 2 * x)) {
                ok = false;
                break;
            }
        }
        if ok {
            for &s in &sum2 {
                if sum3.contains(&(s + x)) {
                    ok = false;
                    break;
                }
            }
        }
        if ok {
            for i in 0..a.len() {
                for j in i..a.len() {
                    sum3.insert(a[i] + a[j] + x);
                }
                sum3.insert(a[i] + 2 * x);
                sum2.insert(a[i] + x);
            }
            sum3.insert(3 * x);
            sum2.insert(2 * x);
            a.push(x);
        }
        x += 1;
    }
    a
}

/// Detailed verification report for Theorem 2.1(a) Exact (2,1)-Difference
/// Harmonic Conservation Identity on `[1, N]`.
#[derive(Debug, Clone, Serialize)]
pub struct B3ConservationReport {
    pub is_b3: bool,
    pub is_w_injective: bool,
    pub horizon_n: u32,
    pub count_m: usize,
    pub num_triples: usize,
    /// Continuous Stieltjes integral + boundary term:
    ///   \int_1^N A(t)(A(t)^2 - 1)/(6 t^2) dt + m(m^2 - 1)/(6 N)
    pub integral_energy: f64,
    /// Discrete sum \sum_{k=2}^m \binom{k}{2} / a_k (equals `integral_energy`)
    pub discrete_energy: f64,
    /// Non-negative (2,1)-asymmetric defect:
    ///   \Delta_A^{(2,1)}(N) = \sum_{(i,j,k) \in T_m} (a_k - |a_k - a_i - a_j| - 2) / ((|w| + 2) a_k)
    pub asymmetric_defect: f64,
    /// Exact harmonic budget:
    ///   \mathcal{B}_A^{(2,1)}(N) = \sum_{w \in W_A(N)} 1 / (|w| + 2)
    pub harmonic_budget: f64,
    /// Absolute conservation error |(discrete_energy + asymmetric_defect) - harmonic_budget|
    pub conservation_error: f64,
    /// Universal upper bound 2 H_N - 5/2
    pub harmonic_upper_bound: f64,
    /// Minimum of \Psi_A(x) = A(x) / x^{1/3} over x \in [x0, N]
    pub min_psi_on_window: f64,
    pub argmin_x: u32,
    pub max_psi_on_window: f64,
    pub argmax_x: u32,
}

/// Computes the harmonic number H_n = \sum_{r=1}^n 1/r.
pub fn harmonic_number(n: u32) -> f64 {
    let mut acc = 0.0f64;
    for r in 1..=n {
        acc += 1.0 / (r as f64);
    }
    acc
}

/// Evaluates Theorem 2.1(a) and the lower/upper envelope of `\Psi_A(x) = A(x)/x^{1/3}`
/// over `[x0, horizon_n]`.
pub fn evaluate_b3_conservation(a: &[u32], horizon_n: u32, x0: u32) -> B3ConservationReport {
    let active: Vec<u32> = a
        .iter()
        .copied()
        .filter(|&x| x >= 1 && x <= horizon_n)
        .collect();
    let is_b3 = is_b3_sequence(&active);
    let is_w_injective = verify_ordered_21_diff_injectivity(&active);
    let m = active.len();
    let num_triples = m * m.saturating_sub(1) * (m + 1) / 6;

    // 1. Piecewise-exact integral \int_1^N A(t)(A(t)^2 - 1)/(6 t^2) dt + m(m^2 - 1)/(6 N)
    let mut integral_only = 0.0f64;
    for k in 1..=m {
        let left = active[k - 1] as f64;
        let right = if k < m {
            active[k] as f64
        } else {
            horizon_n as f64
        };
        if right > left {
            let kf = k as f64;
            let coeff = kf * (kf * kf - 1.0) / 6.0;
            integral_only += coeff * (1.0 / left - 1.0 / right);
        }
    }
    let mf = m as f64;
    let boundary_term = mf * (mf * mf - 1.0) / (6.0 * (horizon_n as f64));
    let integral_energy = integral_only + boundary_term;

    // 2. Discrete energy, asymmetric defect, and harmonic budget
    let mut discrete_energy = 0.0f64;
    let mut asymmetric_defect = 0.0f64;
    let mut harmonic_budget = 0.0f64;

    for k in 1..m {
        let ak = active[k] as f64;
        let k_choose_2 = ((k * (k + 1)) / 2) as f64;
        discrete_energy += k_choose_2 / ak;
        for j in 0..k {
            for i in 0..=j {
                let w = (active[k] as i64) - (active[i] as i64) - (active[j] as i64);
                let denom = (w.abs() + 2) as f64;
                harmonic_budget += 1.0 / denom;
                asymmetric_defect += (ak - denom) / (denom * ak);
            }
        }
    }

    let conservation_error = ((discrete_energy + asymmetric_defect) - harmonic_budget)
        .abs()
        .max((integral_energy - discrete_energy).abs());
    let harmonic_upper_bound = if horizon_n >= 2 {
        2.0 * harmonic_number(horizon_n) - 2.5
    } else {
        0.0
    };

    let start_x = x0.max(1).min(horizon_n);
    let mut min_psi = f64::INFINITY;
    let mut argmin_x = start_x;
    let mut max_psi = 0.0f64;
    let mut argmax_x = start_x;
    let mut ptr = 0usize;
    for x in 1..=horizon_n {
        while ptr < m && active[ptr] <= x {
            ptr += 1;
        }
        if x >= start_x {
            let psi = erdos41_psi(ptr, x);
            if psi < min_psi {
                min_psi = psi;
                argmin_x = x;
            }
            if psi > max_psi {
                max_psi = psi;
                argmax_x = x;
            }
        }
    }

    B3ConservationReport {
        is_b3,
        is_w_injective,
        horizon_n,
        count_m: m,
        num_triples,
        integral_energy,
        discrete_energy,
        asymmetric_defect,
        harmonic_budget,
        conservation_error,
        harmonic_upper_bound,
        min_psi_on_window: if min_psi.is_finite() { min_psi } else { 0.0 },
        argmin_x,
        max_psi_on_window: max_psi,
        argmax_x,
    }
}

/// Verification report for Theorem 2.3(1)-(2) Sign-Split Positive & Negative
/// (2,1)-Cone Conservation Identities on `[1, N]`.
#[derive(Debug, Clone, Serialize)]
pub struct SignSplitConeReport {
    pub horizon_n: u32,
    pub count_m: usize,
    pub pos_count: usize,
    pub zero_count: usize,
    pub neg_count: usize,
    pub pos_fraction: f64,
    pub pos_energy: f64,
    pub pos_defect: f64,
    pub pos_budget: f64,
    pub pos_conservation_error: f64,
    pub neg_energy: f64,
    pub neg_defect: f64,
    pub neg_budget: f64,
    pub neg_conservation_error: f64,
    /// Single-cone harmonic ceiling H_N - 3/2 (half of the Phase-1 two-cone bound)
    pub single_cone_ceiling: f64,
}

/// Evaluates the Theorem 2.3(1)-(2) Sign-Split Positive/Negative (2,1)-Cone
/// Conservation Identities on `A \cap [1, horizon_n]`.
pub fn evaluate_sign_split_cones(a: &[u32], horizon_n: u32) -> SignSplitConeReport {
    let active: Vec<u32> = a
        .iter()
        .copied()
        .filter(|&x| x >= 1 && x <= horizon_n)
        .collect();
    let m = active.len();
    let mut pos_count = 0usize;
    let mut zero_count = 0usize;
    let mut neg_count = 0usize;
    let mut pos_energy = 0.0f64;
    let mut pos_defect = 0.0f64;
    let mut pos_budget = 0.0f64;
    let mut neg_energy = 0.0f64;
    let mut neg_defect = 0.0f64;
    let mut neg_budget = 0.0f64;

    for k in 1..m {
        let ak = active[k] as f64;
        for j in 0..k {
            for i in 0..=j {
                let w = (active[k] as i64) - (active[i] as i64) - (active[j] as i64);
                if w > 0 {
                    pos_count += 1;
                    let denom = (w + 2) as f64;
                    let num = (active[i] + active[j] - 2) as f64;
                    pos_energy += 1.0 / ak;
                    pos_defect += num / (denom * ak);
                    pos_budget += 1.0 / denom;
                } else if w == 0 {
                    zero_count += 1;
                } else {
                    neg_count += 1;
                    let u = -w;
                    let denom = (u + 2) as f64;
                    let num = (2 * active[k] - active[i] - active[j] - 2) as f64;
                    neg_energy += 1.0 / ak;
                    neg_defect += num / (denom * ak);
                    neg_budget += 1.0 / denom;
                }
            }
        }
    }

    let total_triples = (pos_count + zero_count + neg_count).max(1) as f64;
    let single_cone_ceiling = if horizon_n >= 2 {
        harmonic_number(horizon_n) - 1.5
    } else {
        0.0
    };

    SignSplitConeReport {
        horizon_n,
        count_m: m,
        pos_count,
        zero_count,
        neg_count,
        pos_fraction: (pos_count as f64) / total_triples,
        pos_energy,
        pos_defect,
        pos_budget,
        pos_conservation_error: ((pos_energy + pos_defect) - pos_budget).abs(),
        neg_energy,
        neg_defect,
        neg_budget,
        neg_conservation_error: ((neg_energy + neg_defect) - neg_budget).abs(),
        single_cone_ceiling,
    }
}

/// Verification report for Theorem 2.5 (Full-Cube (2,1)-Difference Injectivity &
/// Exact Symmetric Variance Identity `\mathrm{Var}_{\mathcal{I}_m}(w) = \frac{3(m+1)}{m-1}\sigma_A^2`)
/// and Theorem 2.6 (One-Sided Positive-Definite Sub-Cone `\mathcal{I}_m^{<}` Conservation).
#[derive(Debug, Clone, Serialize)]
pub struct FullCubeVarianceReport {
    pub count_m: usize,
    /// Total triples in \mathcal{I}_m = {(i,j,k) : 1 <= i <= j <= m, k \notin {i,j}}:
    ///   T_m = m^2 (m - 1) / 2.
    pub total_triples_tm: usize,
    pub distinct_w_count: usize,
    pub is_full_cube_injective: bool,
    pub mean_a: f64,
    pub mean_w: f64,
    pub sigma_a_sq: f64,
    pub empirical_var_w: f64,
    /// Theoretical variance from Theorem 2.5(2): 3(m + 1)/(m - 1) * sigma_a_sq
    pub theoretical_var_w: f64,
    pub variance_identity_error: f64,
    /// Universal lower bound on sigma_A^2 from Theorem 2.5(3):
    ///   (m - 1)(T_m^2 - 1) / (36(m + 1))
    pub universal_sigma_a_sq_lower_bound: f64,
    /// Cardinality of One-Sided Positive-Definite Sub-Cone \mathcal{I}_m^{<} (k < j):
    ///   m(m - 1)(2m - 1) / 6
    pub one_sided_pos_triples: usize,
    pub all_one_sided_ge_2: bool,
    /// \sum_{j=2}^m (j - 1)^2 / (2 a_j)
    pub one_sided_energy: f64,
    /// \sum_{(i,j,k) \in \mathcal{I}_m^{<}} (a_j - a_i + a_k + 1) / (2 a_j (a_i + a_j - a_k - 1))
    pub one_sided_defect: f64,
    /// \sum_{(i,j,k) \in \mathcal{I}_m^{<}} 1 / (a_i + a_j - a_k - 1)
    pub one_sided_budget: f64,
    pub one_sided_conservation_error: f64,
    /// H_{2 a_m - 2}
    pub one_sided_harmonic_ceiling: f64,
}

/// Evaluates Theorem 2.5(1)-(3) and Theorem 2.6 on a finite B_3 sequence `a` (`m >= 3`).
pub fn eval_full_cube_variance_identity(a: &[u32]) -> FullCubeVarianceReport {
    let m = a.len();
    assert!(m >= 3, "Theorem 2.5 requires m >= 3");
    let total_triples_tm = m * m * (m - 1) / 2;
    let one_sided_expected = m * (m - 1) * (2 * m - 1) / 6;

    let mean_a = a.iter().map(|&x| x as f64).sum::<f64>() / (m as f64);
    let sigma_a_sq = a
        .iter()
        .map(|&x| {
            let d = (x as f64) - mean_a;
            d * d
        })
        .sum::<f64>()
        / (m as f64);

    let mut seen_w: HashSet<i64> = HashSet::with_capacity(total_triples_tm);
    let mut sum_w = 0.0f64;
    let mut sum_sq_dev_w = 0.0f64;

    let mut one_sided_pos_triples = 0usize;
    let mut all_one_sided_ge_2 = true;
    let mut one_sided_energy = 0.0f64;
    let mut one_sided_defect = 0.0f64;
    let mut one_sided_budget = 0.0f64;

    for (j, &aj) in a.iter().enumerate().skip(1) {
        let jm1 = j as f64;
        one_sided_energy += (jm1 * jm1) / (2.0 * (aj as f64));
    }

    for i in 0..m {
        for j in i..m {
            for k in 0..m {
                if k == i || k == j {
                    continue;
                }
                let w = (a[i] as i64) + (a[j] as i64) - (a[k] as i64);
                seen_w.insert(w);
                let wf = w as f64;
                sum_w += wf;
                let dev = wf - mean_a;
                sum_sq_dev_w += dev * dev;

                if k < j {
                    one_sided_pos_triples += 1;
                    if w < 2 {
                        all_one_sided_ge_2 = false;
                    }
                    let aj = a[j] as f64;
                    let denom = (w - 1) as f64;
                    let num = ((a[j] as i64) - (a[i] as i64) + (a[k] as i64) + 1) as f64;
                    one_sided_defect += num / (2.0 * aj * denom);
                    one_sided_budget += 1.0 / denom;
                }
            }
        }
    }

    let mean_w = sum_w / (total_triples_tm as f64);
    let empirical_var_w = sum_sq_dev_w / (total_triples_tm as f64);
    let theoretical_var_w = (3.0 * ((m + 1) as f64) / ((m - 1) as f64)) * sigma_a_sq;
    let variance_identity_error = (empirical_var_w - theoretical_var_w)
        .abs()
        .max((mean_w - mean_a).abs());

    let tm_f = total_triples_tm as f64;
    let universal_sigma_a_sq_lower_bound =
        (((m - 1) as f64) * (tm_f * tm_f - 1.0)) / (36.0 * ((m + 1) as f64));

    assert_eq!(one_sided_pos_triples, one_sided_expected);
    let am = *a.last().unwrap_or(&2);
    let one_sided_harmonic_ceiling = if 2 * am >= 2 {
        harmonic_number(2 * am - 2)
    } else {
        0.0
    };

    FullCubeVarianceReport {
        count_m: m,
        total_triples_tm,
        distinct_w_count: seen_w.len(),
        is_full_cube_injective: seen_w.len() == total_triples_tm,
        mean_a,
        mean_w,
        sigma_a_sq,
        empirical_var_w,
        theoretical_var_w,
        variance_identity_error,
        universal_sigma_a_sq_lower_bound,
        one_sided_pos_triples,
        all_one_sided_ge_2,
        one_sided_energy,
        one_sided_defect,
        one_sided_budget,
        one_sided_conservation_error: ((one_sided_energy + one_sided_defect) - one_sided_budget)
            .abs(),
        one_sided_harmonic_ceiling,
    }
}

/// Summary of the Theorem 2.7(a)-(c) Exact First-Moment Polynomial Identity on `\mathcal{I}_m^{<}`
/// and Concave-Margin Sub-Level Sub-Cone Positivity on `\Omega_\tau(m)`:
///   `\Omega_\tau(m) = \{(i, j, k) \in \mathcal{I}_m^{<} : \tau_{\text{den}} (i^3 + j^3 - k^3) <= \tau_{\text{num}} m^3\}`.
#[derive(Debug, Clone, Serialize)]
pub struct SublevelSubconeReport {
    pub count_m: usize,
    pub tau_num: u64,
    pub tau_den: u64,
    /// `N_m^{<} = m (m - 1) (2 m - 1) / 6`
    pub full_cone_triple_count: usize,
    /// `\sum_{(i, j, k) \in \mathcal{I}_m^{<}} (a_i + a_j - a_k)`
    pub full_cone_triple_sum: i64,
    /// `\sum_{r=1}^m (r^2 - m) a_r` (equals `full_cone_triple_sum` identically)
    pub full_cone_poly_rhs: i64,
    /// Minimum possible sum of `N_m^{<}` distinct integers `>= 2`: `N_m^{<} (N_m^{<} + 3) / 2`
    pub full_cone_min_distinct_sum: i64,
    /// `|\Omega_\tau(m)|`
    pub sublevel_triple_count: usize,
    /// `\sum_{(i, j, k) \in \Omega_\tau(m)} (a_i + a_j - a_k)`
    pub sublevel_triple_sum: i64,
    /// Discrete weights `C_r(m, \tau)` for `r = 1, ..., m`
    pub discrete_weights: Vec<i64>,
    pub min_discrete_weight: i64,
    pub max_discrete_weight: i64,
    /// `\sum_{r=1}^m C_r(m, \tau) a_r` (equals `sublevel_triple_sum` identically)
    pub sublevel_weighted_rhs: i64,
    /// `\sum_{(i, j, k) \in \Omega_\tau(m)} (i^3 + j^3 - k^3)`
    pub sublevel_cubic_ref_sum: i64,
    /// Minimum possible sum of `|\Omega_\tau(m)|` distinct integers `>= 2`:
    /// `|\Omega_\tau(m)| (|\Omega_\tau(m)| + 3) / 2`
    pub sublevel_min_distinct_sum: i64,
}

/// Evaluates Theorem 2.7(a)-(c) on a finite B_3 sequence `a` (`m >= 2`) for threshold
/// `\tau = \tau_{\text{num}} / \tau_{\text{den}} \in (0, 1]`.
pub fn eval_sublevel_subcone_identity(
    a: &[u32],
    tau_num: u64,
    tau_den: u64,
) -> SublevelSubconeReport {
    let m = a.len();
    assert!(m >= 2, "Theorem 2.7 requires m >= 2");
    assert!(tau_num >= 1 && tau_num <= tau_den);

    let m_u64 = m as u64;
    let rhs_thresh = tau_num * m_u64 * m_u64 * m_u64;

    let mut full_cone_triple_count = 0usize;
    let mut full_cone_triple_sum = 0i64;
    let mut sublevel_triple_count = 0usize;
    let mut sublevel_triple_sum = 0i64;
    let mut sublevel_cubic_ref_sum = 0i64;
    let mut discrete_weights = vec![0i64; m];

    for i in 0..m {
        let i1 = (i + 1) as u64;
        let i3 = i1 * i1 * i1;
        for j in i..m {
            let j1 = (j + 1) as u64;
            let ij3 = i3 + j1 * j1 * j1;
            for k in 0..j {
                if k == i {
                    continue;
                }
                let k1 = (k + 1) as u64;
                let ref_cube = ij3 - k1 * k1 * k1;
                let w = (a[i] as i64) + (a[j] as i64) - (a[k] as i64);

                full_cone_triple_count += 1;
                full_cone_triple_sum += w;

                if tau_den * ref_cube <= rhs_thresh {
                    sublevel_triple_count += 1;
                    sublevel_triple_sum += w;
                    sublevel_cubic_ref_sum += ref_cube as i64;
                    discrete_weights[i] += 1;
                    discrete_weights[j] += 1;
                    discrete_weights[k] -= 1;
                }
            }
        }
    }

    let expected_full = m * (m - 1) * (2 * m - 1) / 6;
    assert_eq!(full_cone_triple_count, expected_full);

    let mut full_cone_poly_rhs = 0i64;
    let mut sublevel_weighted_rhs = 0i64;
    for (idx, &ar) in a.iter().enumerate() {
        let r = (idx + 1) as i64;
        let coeff = r * r - (m as i64);
        full_cone_poly_rhs += coeff * (ar as i64);
        sublevel_weighted_rhs += discrete_weights[idx] * (ar as i64);
    }

    let n_full_i64 = full_cone_triple_count as i64;
    let full_cone_min_distinct_sum = n_full_i64 * (n_full_i64 + 3) / 2;

    let n_sub_i64 = sublevel_triple_count as i64;
    let sublevel_min_distinct_sum = n_sub_i64 * (n_sub_i64 + 3) / 2;

    let min_discrete_weight = discrete_weights.iter().copied().min().unwrap_or(0);
    let max_discrete_weight = discrete_weights.iter().copied().max().unwrap_or(0);

    SublevelSubconeReport {
        count_m: m,
        tau_num,
        tau_den,
        full_cone_triple_count,
        full_cone_triple_sum,
        full_cone_poly_rhs,
        full_cone_min_distinct_sum,
        sublevel_triple_count,
        sublevel_triple_sum,
        discrete_weights,
        min_discrete_weight,
        max_discrete_weight,
        sublevel_weighted_rhs,
        sublevel_cubic_ref_sum,
        sublevel_min_distinct_sum,
    }
}

/// Verification report for Theorem 2.9(a) Three-Hemisphere Partition of the Full-Cube
/// `(2,1)`-Difference Set `\mathcal{I}_m = \mathcal{I}_m^{\mathrm{lo}} \sqcup \mathcal{I}_m^{\mathrm{mid}} \sqcup \mathcal{I}_m^{\mathrm{hi}}`
/// and Full Positive Cone `\mathcal{I}_m^+ = \mathcal{I}_m^{\mathrm{lo}} \sqcup \mathcal{I}_m^{\mathrm{mid}} \sqcup \mathcal{T}_m^-`.
#[derive(Debug, Clone, Serialize)]
pub struct ThreeHemisphereReport {
    pub count_m: usize,
    /// `|\mathcal{I}_m^{\mathrm{lo}}| = \binom{m+1}{3}` (`1 <= k < i <= j <= m`)
    pub lo_count: usize,
    /// `|\mathcal{I}_m^{\mathrm{mid}}| = \binom{m}{3}` (`1 <= i < k < j <= m`)
    pub mid_count: usize,
    /// `|\mathcal{T}_m^-|` (`1 <= i <= j < k <= m` with `a_i + a_j - a_k > 0`)
    pub hi_pos_count: usize,
    /// `|\mathcal{T}_m^+ \sqcup \mathcal{T}_m^0|` (`1 <= i <= j < k <= m` with `a_i + a_j - a_k <= 0`)
    pub hi_nonpos_count: usize,
    /// `|\mathcal{I}_m^+| = |\mathcal{I}_m^{\mathrm{lo}}| + |\mathcal{I}_m^{\mathrm{mid}}| + |\mathcal{T}_m^-|`
    pub full_pos_count: usize,
    pub lo_sum: i64,
    pub mid_sum: i64,
    pub hi_pos_sum: i64,
    pub full_pos_sum: i64,
}

/// Evaluates Theorem 2.9(a) on a finite B_3 sequence `a` (`m >= 3`).
pub fn eval_three_hemisphere_partition(a: &[u32]) -> ThreeHemisphereReport {
    let m = a.len();
    assert!(m >= 3, "Theorem 2.9(a) requires m >= 3");

    let mut lo_count = 0usize;
    let mut mid_count = 0usize;
    let mut hi_pos_count = 0usize;
    let mut hi_nonpos_count = 0usize;
    let mut lo_sum = 0i64;
    let mut mid_sum = 0i64;
    let mut hi_pos_sum = 0i64;

    for i in 0..m {
        for j in i..m {
            for k in 0..m {
                if k == i || k == j {
                    continue;
                }
                let w = (a[i] as i64) + (a[j] as i64) - (a[k] as i64);
                if k < i {
                    lo_count += 1;
                    lo_sum += w;
                } else if k < j {
                    mid_count += 1;
                    mid_sum += w;
                } else if w > 0 {
                    hi_pos_count += 1;
                    hi_pos_sum += w;
                } else {
                    hi_nonpos_count += 1;
                }
            }
        }
    }

    assert_eq!(lo_count, m * (m - 1) * (m + 1) / 6);
    assert_eq!(mid_count, m * (m - 1) * (m - 2) / 6);

    ThreeHemisphereReport {
        count_m: m,
        lo_count,
        mid_count,
        hi_pos_count,
        hi_nonpos_count,
        full_pos_count: lo_count + mid_count + hi_pos_count,
        lo_sum,
        mid_sum,
        hi_pos_sum,
        full_pos_sum: lo_sum + mid_sum + hi_pos_sum,
    }
}

/// Verification report for Theorem 2.10(a) Exact Telescoping Step-`s` Sum Identity
/// in the Third Hemisphere `\mathcal{T}_m^-`, Markov Step-`s` Counting Inequality, and
/// Dual Upper-Hemisphere Polynomial Identity on `\mathcal{T}_m^{\mathrm{upper}}`.
#[derive(Debug, Clone, Serialize)]
pub struct TelescopingThirdHemisphereReport {
    pub count_m: usize,
    /// Number of `(i, s)` telescoping rays `1 <= i <= m - 1, 1 <= s <= m - i` (`\binom{m}{2}`)
    pub num_rays: usize,
    /// True if `\sum_{j=i}^{m-s} (a_i + a_j - a_{j+s}) == (m - s - i + 1)a_i + \sum_{r=i}^{i+s-1} a_r - \sum_{r=m-s+1}^m a_r` holds on all rays
    pub all_rays_telescope_exact: bool,
    /// True if `|\mathcal{T}_{m, i, s}^-| >= (m - s - i + 1) - (\sum_{r=m-s+1}^m a_r - \sum_{r=i}^{i+s-1} a_r) / a_i` holds on all rays
    pub all_markov_bounds_hold: bool,
    /// Step-1 (`s = 1`) sum `\sum_{i=1}^{m-1} \sum_{j=i}^{m-1} (a_i + a_j - a_{j+1})`
    pub step1_telescoping_sum: i64,
    /// Step-1 (`s = 1`) closed-form RHS `\sum_{i=1}^{m-1} ((m - i + 1) a_i - a_m)`
    pub step1_telescoping_rhs: i64,
    /// Step-1 positive count `\sum_{i=1}^{m-1} |\{j \in [i, m-1] : a_i + a_j - a_{j+1} > 0\}|`
    pub step1_pos_count: usize,
    /// Upper-hemisphere sum `\sum_{1 <= i <= j < k <= m} (a_i + a_j - a_k)`
    pub upper_cone_sum: i64,
    /// Dual polynomial RHS `\sum_{r=1}^m (\frac{m(m+1)}{2} - r^2) a_r`
    pub upper_poly_rhs: i64,
    /// Sum over `\mathcal{I}_m^{<} \sqcup \mathcal{T}_m^{\mathrm{upper}} = \mathcal{I}_m`
    pub lower_plus_upper_sum: i64,
    /// Constant-weight Full-Cube RHS `\binom{m}{2} \sum_{r=1}^m a_r`
    pub full_cube_binom_rhs: i64,
}

/// Evaluates Theorem 2.10(a) on a strictly increasing sequence `a` (`m >= 3`).
pub fn eval_telescoping_third_hemisphere(a: &[u32]) -> TelescopingThirdHemisphereReport {
    let m = a.len();
    assert!(m >= 3, "Theorem 2.10(a) requires m >= 3");

    let mut num_rays = 0usize;
    let mut all_rays_telescope_exact = true;
    let mut all_markov_bounds_hold = true;
    let mut step1_telescoping_sum = 0i64;
    let mut step1_telescoping_rhs = 0i64;
    let mut step1_pos_count = 0usize;

    for i in 0..(m - 1) {
        let ai = a[i] as i64;
        for s in 1..=(m - 1 - i) {
            num_rays += 1;
            let num_terms = (m - s - i) as i64;
            let mut lhs = 0i64;
            let mut pos_cnt = 0usize;
            for j in i..(m - s) {
                let w = ai + (a[j] as i64) - (a[j + s] as i64);
                lhs += w;
                if w > 0 {
                    pos_cnt += 1;
                }
            }
            let head_sum: i64 = a[i..(i + s)].iter().map(|&x| x as i64).sum();
            let tail_sum: i64 = a[(m - s)..m].iter().map(|&x| x as i64).sum();
            let rhs = num_terms * ai + head_sum - tail_sum;
            if lhs != rhs {
                all_rays_telescope_exact = false;
            }
            // Exact integer form of Markov bound: pos_cnt * a_i >= num_terms * a_i - (tail_sum - head_sum) == rhs
            if (pos_cnt as i64) * ai < rhs {
                all_markov_bounds_hold = false;
            }
            if s == 1 {
                step1_telescoping_sum += lhs;
                step1_telescoping_rhs += ((m - i) as i64) * ai - (a[m - 1] as i64);
                step1_pos_count += pos_cnt;
            }
        }
    }

    let mut upper_cone_sum = 0i64;
    for i in 0..m {
        for j in i..m {
            for k in (j + 1)..m {
                upper_cone_sum += (a[i] as i64) + (a[j] as i64) - (a[k] as i64);
            }
        }
    }

    let mf = m as i64;
    let half_m_mp1 = mf * (mf + 1) / 2;
    let mut upper_poly_rhs = 0i64;
    let mut lower_poly_rhs = 0i64;
    let mut sum_a = 0i64;
    for (idx, &val) in a.iter().enumerate() {
        let r = (idx + 1) as i64;
        let av = val as i64;
        upper_poly_rhs += (half_m_mp1 - r * r) * av;
        lower_poly_rhs += (r * r - mf) * av;
        sum_a += av;
    }
    let full_cube_binom_rhs = (mf * (mf - 1) / 2) * sum_a;

    TelescopingThirdHemisphereReport {
        count_m: m,
        num_rays,
        all_rays_telescope_exact,
        all_markov_bounds_hold,
        step1_telescoping_sum,
        step1_telescoping_rhs,
        step1_pos_count,
        upper_cone_sum,
        upper_poly_rhs,
        lower_plus_upper_sum: lower_poly_rhs + upper_cone_sum,
        full_cube_binom_rhs,
    }
}

/// Verification report for Theorem 2.11(a) Optimal Horizon-Truncated Telescoping Ray
/// Identity & Counting Inequality in the Third Hemisphere `\mathcal{T}_m^-`.
#[derive(Debug, Clone, Serialize)]
pub struct HorizonTruncatedRayReport {
    pub count_m: usize,
    /// Number of `(i, s)` rays `1 <= i <= m - 1, 1 <= s <= m - i` (`\binom{m}{2}`)
    pub num_rays: usize,
    /// True if `\sum_{j=i}^{K-s} (a_i + a_j - a_{j+s}) == (K - s - i + 1)a_i + \sum_{r=i}^{i+s-1} a_r - \sum_{r=K-s+1}^K a_r` holds for every `(i, s, K)`
    pub all_truncated_identities_exact: bool,
    /// True if `0 <= c_markov(K) <= c_mingap(K) <= |\mathcal{T}_{K, i, s}^-| <= |\mathcal{T}_{m, i, s}^-|` holds for every `(i, s, K)`
    pub all_truncated_bounds_valid: bool,
    /// Exact total positive count `|\mathcal{T}_m^-| = \sum_{i, s} |\mathcal{T}_{m, i, s}^-|`
    pub actual_third_hemisphere_pos_count: usize,
    /// Untruncated (`K = m`) coarse Markov lower bound sum
    pub untruncated_markov_certified_count: usize,
    /// Untruncated (`K = m`) minimum-gap (`a_i - s`) lower bound sum
    pub untruncated_mingap_certified_count: usize,
    /// Horizon-optimized (`\max_{i+s <= K <= m}`) coarse Markov lower bound sum
    pub truncated_markov_certified_count: usize,
    /// Horizon-optimized (`\max_{i+s <= K <= m}`) minimum-gap (`a_i - s`) lower bound sum
    pub truncated_mingap_certified_count: usize,
    /// Number of rays `(i, s)` with positive certified lower bound at `K = m`
    pub untruncated_active_rays: usize,
    /// Number of rays `(i, s)` with positive certified lower bound under optimal `K \in [i+s, m]`
    pub truncated_active_rays: usize,
}

/// Evaluates Theorem 2.11(a) on a strictly increasing sequence `a` (`m >= 3`).
pub fn eval_horizon_truncated_rays(a: &[u32]) -> HorizonTruncatedRayReport {
    let m = a.len();
    assert!(m >= 3, "Theorem 2.11(a) requires m >= 3");

    let mut num_rays = 0usize;
    let mut all_truncated_identities_exact = true;
    let mut all_truncated_bounds_valid = true;
    let mut actual_third_hemisphere_pos_count = 0usize;
    let mut untruncated_markov_certified_count = 0usize;
    let mut untruncated_mingap_certified_count = 0usize;
    let mut truncated_markov_certified_count = 0usize;
    let mut truncated_mingap_certified_count = 0usize;
    let mut untruncated_active_rays = 0usize;
    let mut truncated_active_rays = 0usize;

    for i in 0..(m - 1) {
        let ai = a[i] as i64;
        for s in 1..=(m - 1 - i) {
            num_rays += 1;
            let actual_pos = (i..(m - s))
                .filter(|&j| ai + (a[j] as i64) - (a[j + s] as i64) >= 1)
                .count();
            actual_third_hemisphere_pos_count += actual_pos;

            let head_sum: i64 = a[i..(i + s)].iter().map(|&x| x as i64).sum();
            let mut best_markov = 0usize;
            let mut best_mingap = 0usize;
            let mut untrunc_markov = 0usize;
            let mut untrunc_mingap = 0usize;

            for k_hor in (i + s + 1)..=m {
                let num_terms = (k_hor - s - i) as i64;
                let mut lhs = 0i64;
                let mut pos_k = 0usize;
                for j in i..(k_hor - s) {
                    let w = ai + (a[j] as i64) - (a[j + s] as i64);
                    lhs += w;
                    if w >= 1 {
                        pos_k += 1;
                    }
                }
                let tail_sum: i64 = a[(k_hor - s)..k_hor].iter().map(|&x| x as i64).sum();
                let rhs = num_terms * ai + head_sum - tail_sum;
                if lhs != rhs {
                    all_truncated_identities_exact = false;
                }

                let c_m = if rhs > 0 {
                    ((rhs + ai - 1) / ai) as usize
                } else {
                    0usize
                };
                let denom_g = (ai - (s as i64)).max(1);
                let c_g = if rhs > 0 {
                    ((rhs + denom_g - 1) / denom_g) as usize
                } else {
                    0usize
                };

                if !(c_m <= c_g && c_g <= pos_k && pos_k <= actual_pos) {
                    all_truncated_bounds_valid = false;
                }

                if c_m > best_markov {
                    best_markov = c_m;
                }
                if c_g > best_mingap {
                    best_mingap = c_g;
                }
                if k_hor == m {
                    untrunc_markov = c_m;
                    untrunc_mingap = c_g;
                }
            }

            untruncated_markov_certified_count += untrunc_markov;
            untruncated_mingap_certified_count += untrunc_mingap;
            truncated_markov_certified_count += best_markov;
            truncated_mingap_certified_count += best_mingap;
            if untrunc_mingap > 0 {
                untruncated_active_rays += 1;
            }
            if best_mingap > 0 {
                truncated_active_rays += 1;
            }
        }
    }

    HorizonTruncatedRayReport {
        count_m: m,
        num_rays,
        all_truncated_identities_exact,
        all_truncated_bounds_valid,
        actual_third_hemisphere_pos_count,
        untruncated_markov_certified_count,
        untruncated_mingap_certified_count,
        truncated_markov_certified_count,
        truncated_mingap_certified_count,
        untruncated_active_rays,
        truncated_active_rays,
    }
}

/// Computes the exact smallest integer `C \in [0, M]` (`M = \max(1, m_ceil)`) such that
/// `\sum_{r=0}^{C-1} (M - r) = C(2M + 1 - C)/2 >= S` for `S > 0` (`0` if `S <= 0`).
pub fn quad_injection_count(s_val: i64, m_ceil: i64) -> usize {
    if s_val <= 0 {
        return 0;
    }
    let m_pos = m_ceil.max(1);
    if 2 * s_val >= m_pos * (m_pos + 1) {
        return m_pos as usize;
    }
    let mf = m_pos as f64;
    let disc = ((mf + 0.5) * (mf + 0.5) - 2.0 * (s_val as f64)).max(0.0);
    let mut c = ((mf + 0.5 - disc.sqrt()).ceil() as i64).clamp(1, m_pos);
    while c > 1 && (c - 1) * (2 * m_pos + 1 - (c - 1)) >= 2 * s_val {
        c -= 1;
    }
    while c < m_pos && c * (2 * m_pos + 1 - c) < 2 * s_val {
        c += 1;
    }
    c as usize
}

/// Verification report for Theorem 2.12 Quadratic Injection-Deflated Ray & Anchor-Fiber
/// Counting Inequalities, Two-Sided Windowed Telescoping, and Slot-Eviction Polynomial Bound.
#[derive(Debug, Clone, Serialize)]
pub struct QuadraticInjectionRayReport {
    pub count_m: usize,
    /// Number of `(i, s)` rays `1 <= i <= m - 1, 1 <= s <= m - i` (`\binom{m}{2}`)
    pub num_rays: usize,
    /// True if `\sum_{j=J}^{K-s} (a_i + a_j - a_{j+s}) == (K - s - J + 1)a_i + \sum_{r=J}^{J+s-1} a_r - \sum_{r=K-s+1}^K a_r` holds for all `1 <= i <= J <= K - s <= m - s`
    pub all_window_identities_exact: bool,
    /// True if all ray-level quadratic bounds, anchor-fiber capacity bounds `a_i >= (1 + \sqrt{1 + 8 S_i^*})/2`, and slot-eviction bounds hold
    pub all_injection_bounds_valid: bool,
    /// Exact total positive count `|\mathcal{T}_m^-|`
    pub actual_third_hemisphere_pos_count: usize,
    /// Single-horizon (`J = i`) quadratic certified count with Sidon ceiling `M_{i, s}^{\mathrm{Sidon}} = \max(1, a_i - \binom{s+1}{2})`
    pub trunc_sidon_quad_certified_count: usize,
    /// Two-sided window (`i <= J <= K - s`) quadratic certified count with Sidon ceiling `M_{i, s}^{\mathrm{Sidon}}`
    pub windowed_sidon_quad_certified_count: usize,
    /// Single-horizon (`J = i`) quadratic certified count with ray-minimum gap ceiling `M_{K, i, s}^* = \max(1, a_i - \min_{i <= j <= K-s}(a_{j+s} - a_j))`
    pub trunc_raygap_quad_certified_count: usize,
    /// Total anchor-fiber positive telescoping sum `\sum_{i=1}^{m-1} S_i^*`
    pub total_anchor_fiber_s_star: i64,
    /// Number of certified third-hemisphere triples `C_{\mathrm{evict}}` evicting slots in `[1, N_m^< + C_{\mathrm{evict}}]`
    pub slot_evict_certified_count: usize,
    /// One-sided polynomial LHS `\sum_{r=1}^m (r^2 - m) a_r`
    pub one_sided_poly_lhs: i64,
    /// Baseline distinct-sum RHS `\binom{N_m^< + 1}{2}` (`N_m^< = m(m-1)(2m-1)/6`)
    pub base_min_distinct_rhs: i64,
    /// Slot-eviction tightened RHS `\binom{N_m^< + C_{\mathrm{evict}} + 1}{2} - \sum_{i, s} (c_{i, s} M_{i, s}^{\mathrm{Sidon}} - \binom{c_{i, s}}{2})`
    pub slot_evict_poly_rhs: i64,
}

/// Evaluates Theorem 2.12(a)-(c) on a strictly increasing `B_3` sequence `a` (`m >= 3`).
pub fn eval_quadratic_injection_rays(a: &[u32]) -> QuadraticInjectionRayReport {
    let m = a.len();
    assert!(m >= 3, "Theorem 2.12 requires m >= 3");

    let mut num_rays = 0usize;
    let mut all_window_identities_exact = true;
    let mut all_injection_bounds_valid = true;
    let mut actual_third_hemisphere_pos_count = 0usize;
    let mut trunc_sidon_quad_certified_count = 0usize;
    let mut windowed_sidon_quad_certified_count = 0usize;
    let mut trunc_raygap_quad_certified_count = 0usize;
    let mut total_anchor_fiber_s_star = 0i64;

    let n_lt = (m * (m - 1) * (2 * m - 1) / 6) as i64;
    let mut c_evict = 0i64;
    let mut upper_w_sum = 0i64;

    for i in 0..(m - 1) {
        let ai = a[i] as i64;
        let mut si_star = 0i64;
        let mut ci_actual = 0usize;

        for s in 1..=(m - 1 - i) {
            num_rays += 1;
            let s_i64 = s as i64;
            let m_sid = (ai - s_i64 * (s_i64 + 1) / 2).max(1);
            let m_mg = (ai - s_i64).max(1);

            let actual_pos = (i..(m - s))
                .filter(|&j| ai + (a[j] as i64) - (a[j + s] as i64) >= 1)
                .count();
            actual_third_hemisphere_pos_count += actual_pos;
            ci_actual += actual_pos;

            let mut best_s_trunc = 0i64;
            let mut best_q_sid_trunc = 0usize;
            let mut best_q_rg_trunc = 0usize;
            let mut best_q_sid_win = 0usize;

            for j_start in i..(m - s) {
                let head_sum: i64 = a[j_start..(j_start + s)].iter().map(|&x| x as i64).sum();
                let mut min_gap_running = i64::MAX;
                let mut lhs_running = 0i64;
                let mut pos_running = 0usize;

                for k_hor in (j_start + s + 1)..=m {
                    let j_last = k_hor - s - 1;
                    let gap_last = (a[j_last + s] as i64) - (a[j_last] as i64);
                    if gap_last < min_gap_running {
                        min_gap_running = gap_last;
                    }
                    let w_last = ai - gap_last;
                    lhs_running += w_last;
                    if w_last >= 1 {
                        pos_running += 1;
                    }

                    let num_terms = (k_hor - s - j_start) as i64;
                    let tail_sum: i64 = a[(k_hor - s)..k_hor].iter().map(|&x| x as i64).sum();
                    let rhs = num_terms * ai + head_sum - tail_sum;
                    if lhs_running != rhs {
                        all_window_identities_exact = false;
                    }

                    let c_q_sid = quad_injection_count(rhs, m_sid);
                    if c_q_sid > pos_running || pos_running > actual_pos {
                        all_injection_bounds_valid = false;
                    }
                    if c_q_sid > best_q_sid_win {
                        best_q_sid_win = c_q_sid;
                    }

                    if j_start == i {
                        if rhs > best_s_trunc {
                            best_s_trunc = rhs;
                        }
                        let c_l_mg = if rhs > 0 {
                            ((rhs + m_mg - 1) / m_mg) as usize
                        } else {
                            0
                        };
                        let m_rg = (ai - min_gap_running).max(1);
                        let c_q_rg = quad_injection_count(rhs, m_rg);
                        if !(c_l_mg <= c_q_sid && c_q_sid <= c_q_rg && c_q_rg <= pos_running) {
                            all_injection_bounds_valid = false;
                        }
                        if c_q_sid > best_q_sid_trunc {
                            best_q_sid_trunc = c_q_sid;
                        }
                        if c_q_rg > best_q_rg_trunc {
                            best_q_rg_trunc = c_q_rg;
                        }
                    }
                }
            }

            if best_q_sid_trunc > best_q_sid_win || best_q_sid_win > actual_pos {
                all_injection_bounds_valid = false;
            }

            si_star += best_s_trunc;
            trunc_sidon_quad_certified_count += best_q_sid_trunc;
            windowed_sidon_quad_certified_count += best_q_sid_win;
            trunc_raygap_quad_certified_count += best_q_rg_trunc;

            let c_qs_i64 = best_q_sid_trunc as i64;
            if c_qs_i64 > 0 && m_sid <= n_lt + c_evict {
                c_evict += c_qs_i64;
                upper_w_sum += c_qs_i64 * m_sid - c_qs_i64 * (c_qs_i64 - 1) / 2;
            }
        }

        let ci_quad = quad_injection_count(si_star, (ai - 1).max(1));
        let cap_lb = 0.5 * (1.0 + (1.0 + 8.0 * (si_star as f64)).sqrt());
        if ci_quad > ci_actual || (ai as f64) + 1e-9 < cap_lb || si_star > ai * (ai - 1) / 2 {
            all_injection_bounds_valid = false;
        }
        total_anchor_fiber_s_star += si_star;
    }

    let mf = m as i64;
    let mut one_sided_poly_lhs = 0i64;
    for (idx, &val) in a.iter().enumerate() {
        let r = (idx + 1) as i64;
        one_sided_poly_lhs += (r * r - mf) * (val as i64);
    }
    let base_min_distinct_rhs = n_lt * (n_lt + 1) / 2;
    let slot_evict_poly_rhs = (n_lt + c_evict) * (n_lt + c_evict + 1) / 2 - upper_w_sum;
    if one_sided_poly_lhs < slot_evict_poly_rhs || slot_evict_poly_rhs < base_min_distinct_rhs {
        all_injection_bounds_valid = false;
    }

    QuadraticInjectionRayReport {
        count_m: m,
        num_rays,
        all_window_identities_exact,
        all_injection_bounds_valid,
        actual_third_hemisphere_pos_count,
        trunc_sidon_quad_certified_count,
        windowed_sidon_quad_certified_count,
        trunc_raygap_quad_certified_count,
        total_anchor_fiber_s_star,
        slot_evict_certified_count: c_evict as usize,
        one_sided_poly_lhs,
        base_min_distinct_rhs,
        slot_evict_poly_rhs,
    }
}

/// Verification report for Theorems 2.13, 2.14(a)–(c), and Corollary 2.15:
/// Dyadic Cross-Shell `(2,1)`-Difference Vandermonde Decomposition & KKT Convexity,
/// Discrete Legendre–Fenchel Sub-Block `(2,1)`-Fiber Integrality Excess, Hierarchical
/// Binary Sub-Block Variance Splitting, and Unconditional Diophantine Haar Closure.
#[derive(Debug, Clone, Serialize)]
pub struct DiophantineHaarB3Report {
    pub r_max: u32,
    pub k_oct: u32,
    pub active_elements: usize,
    /// True if `(P + m)^3 == P^3 + m^3 + 3 m^2 P + 3 m P^2` and `\Delta \binom{M_r+1}{3}` hold across all shells `r = 1..=r_max`
    pub all_vandermonde_and_kkt_exact: bool,
    /// True if `2^{r-2} < a_k - a_i - a_j < 2^r` (`r_min(w) \in \{r-1, r\}`) holds for all cross-shell triples with `a_i + a_j <= 2^{r-2}, a_k \in I_r`
    pub all_cross_shell_localized: bool,
    /// Count of cross-shell triples with `a_i + a_j <= 2^{r-2}` and `a_k \in I_r` (`r >= 3`)
    pub localized_cross_shell_triples: usize,
    /// True if all sub-block Legendre–Fenchel bounds `\sum m_{r,b}(m_{r,b}-1) >= B q(q-1) + 2 q t` and `4 t(B - t) <= B^2` hold across all shells & depths
    pub all_legendre_fenchel_valid: bool,
    /// True if `2(u^2 + v^2) == (u + v)^2 + (u - v)^2` holds across all binary sub-block splits
    pub all_binary_splits_exact: bool,
    /// Total actual sub-block quadratic excess `\sum_{r=2}^{r_max} \sum_{d=0}^{r-1} (\sum_{b=1}^B m_{r,b}^2 - S^2 / B)`
    pub total_actual_subblock_excess: f64,
    /// Total Legendre–Fenchel sawtooth lower bound `\sum_{r=2}^{r_max} \sum_{d=0}^{r-1} t(B - t) / B`
    pub total_lf_sawtooth_excess: f64,
    /// Total integer squared-difference sum `\sum_{r=2}^{r_max} \sum_{d=0}^{r-2} \sum_{b=1}^{2^d} (u_b - v_b)^2` across binary refinements
    pub total_binary_split_diff_sq: u64,
    /// Diophantine Haar integrality boost `\kappa_{\mathrm{int}, 3}^{\mathrm{Dio}}(K) = \frac{K \ln 2}{3(1 - 4^{-K})}`
    pub kappa_dio: f64,
    /// Unconditional Diophantine Haar density bound `c_{\infty, 3}^{\ast, \mathrm{Dio}}(K) = (\mathcal{K}_* (1 + \kappa_{\mathrm{int}, 3}^{\mathrm{Dio}}(K)))^{-1/3}`
    pub bound_dio: f64,
    /// Glaisher–Kinkelin boundary-refined integrality boost `\kappa_{\mathrm{int}, 3}^{\mathrm{Dio, GK}}(K)`
    pub kappa_dio_gk: f64,
    /// Glaisher–Kinkelin boundary-refined density bound `c_{\infty, 3}^{\ast, \mathrm{Dio, GK}}(K)`
    pub bound_dio_gk: f64,
}

/// Evaluates Theorems 2.13, 2.14(a)–(c), and Corollary 2.15 on a strictly increasing `B_3`
/// sequence `a` over dyadic shells `r = 1, ..., r_max` (`r_max <= 20`) and octave span `k_oct`.
pub fn eval_b3_diophantine_haar_closure(
    a: &[u32],
    r_max: u32,
    k_oct: u32,
) -> DiophantineHaarB3Report {
    assert!((2..=20).contains(&r_max), "r_max must be in 2..=20");
    let horizon_n = 1u32 << r_max;
    let active: Vec<u32> = a
        .iter()
        .copied()
        .filter(|&x| x >= 1 && x <= horizon_n)
        .collect();

    let mut shells: Vec<Vec<u32>> = vec![Vec::new(); r_max as usize];
    for &x in &active {
        let r = if x <= 2 {
            1usize
        } else {
            (x - 1).ilog2() as usize + 1
        };
        if r <= r_max as usize {
            shells[r - 1].push(x);
        }
    }

    let mut all_vandermonde_and_kkt_exact = true;
    let mut p_pref = 0u64;
    for sh in &shells {
        let m = sh.len() as u64;
        let tot = p_pref + m;
        let lhs_cube = tot * tot * tot;
        let rhs_cube =
            p_pref * p_pref * p_pref + m * m * m + 3 * m * m * p_pref + 3 * m * p_pref * p_pref;
        let binom3 = |n: u64| -> u64 {
            if n < 2 {
                0
            } else {
                n * (n - 1) * (n + 1) / 6
            }
        };
        let binom2_plus = |n: u64| -> u64 { n * (n + 1) / 2 };
        let binom2_minus = |n: u64| -> u64 { n * n.saturating_sub(1) / 2 };
        let lhs_b3 = binom3(tot) - binom3(p_pref);
        let rhs_b3 = binom3(m) + m * binom2_plus(p_pref) + p_pref * binom2_minus(m);
        if lhs_cube != rhs_cube || lhs_b3 != rhs_b3 {
            all_vandermonde_and_kkt_exact = false;
        }
        if tot >= 1 {
            let delta = 1u64;
            let inc = (tot + delta).pow(3) - tot.pow(3);
            if inc != 3 * delta * tot * tot + 3 * delta * delta * tot + delta.pow(3) || inc < 7 {
                all_vandermonde_and_kkt_exact = false;
            }
        }
        p_pref = tot;
    }

    let mut all_cross_shell_localized = true;
    let mut localized_cross_shell_triples = 0usize;
    let n_act = active.len();
    for k in 1..n_act {
        let ak = active[k];
        let r_k = if ak <= 2 { 1u32 } else { (ak - 1).ilog2() + 1 };
        if r_k >= 3 {
            let pow_rm2 = 1u32 << (r_k - 2);
            let pow_r = 1u32 << r_k;
            for j in 0..k {
                for i in 0..=j {
                    let a_ij = active[i] + active[j];
                    if a_ij <= pow_rm2 {
                        localized_cross_shell_triples += 1;
                        let w = (ak as i64) - (a_ij as i64);
                        let r_min = min_dyadic_shell_for_w(w);
                        if !(w > (pow_rm2 as i64)
                            && w < (pow_r as i64)
                            && (r_min == r_k - 1 || r_min == r_k))
                        {
                            all_cross_shell_localized = false;
                        }
                    }
                }
            }
        }
    }

    let mut all_legendre_fenchel_valid = true;
    let mut all_binary_splits_exact = true;
    let mut total_actual_subblock_excess = 0.0_f64;
    let mut total_lf_sawtooth_excess = 0.0_f64;
    let mut total_binary_split_diff_sq = 0u64;

    for (idx, sh) in shells.iter().enumerate().skip(1) {
        let r = (idx + 1) as u32;
        let shell_lo = 1u32 << (r - 1);
        let s_count = sh.len() as u64;
        let mut prev_counts: Vec<u64> = Vec::new();

        for d in 0..r {
            let b_blocks = 1usize << d;
            let w_width = 1u32 << (r - 1 - d);
            let mut counts = vec![0u64; b_blocks];
            for &x in sh {
                let b_idx = ((x - shell_lo - 1) / w_width) as usize;
                counts[b_idx] += 1;
            }

            let b_u64 = b_blocks as u64;
            let q = s_count / b_u64;
            let t = s_count % b_u64;
            let sum_pairs: u64 = counts.iter().map(|&c| c.saturating_sub(1) * c).sum();
            let sum_sq: u64 = counts.iter().map(|&c| c * c).sum();
            let lf_pairs_lb = b_u64 * q * q.saturating_sub(1) + 2 * q * t;
            let lhs_id = b_u64 * (b_u64 * q * q + 2 * q * t) + b_u64 * t;
            let rhs_id = s_count * s_count + t * (b_u64 - t);

            if sum_pairs < lf_pairs_lb || lhs_id != rhs_id || 4 * t * (b_u64 - t) > b_u64 * b_u64 {
                all_legendre_fenchel_valid = false;
            }

            let bf = b_blocks as f64;
            let sf = s_count as f64;
            let tf = t as f64;
            let act_ex = (sum_sq as f64) - (sf * sf) / bf;
            let lf_ex = tf * (bf - tf) / bf;
            if act_ex + 1e-11 < lf_ex {
                all_legendre_fenchel_valid = false;
            }
            total_actual_subblock_excess += act_ex;
            total_lf_sawtooth_excess += lf_ex;

            if d >= 1 {
                for p_idx in 0..(b_blocks / 2) {
                    let u = counts[2 * p_idx];
                    let v = counts[2 * p_idx + 1];
                    let p_val = prev_counts[p_idx];
                    let diff = u.abs_diff(v);
                    if u + v != p_val || 2 * (u * u + v * v) != p_val * p_val + diff * diff {
                        all_binary_splits_exact = false;
                    }
                    total_binary_split_diff_sq += diff * diff;
                }
            }
            prev_counts = counts;
        }
    }

    let (kappa_dio, bound_dio, kappa_dio_gk, bound_dio_gk) =
        b3_diophantine_haar_boost_and_bound(k_oct);

    DiophantineHaarB3Report {
        r_max,
        k_oct,
        active_elements: n_act,
        all_vandermonde_and_kkt_exact,
        all_cross_shell_localized,
        localized_cross_shell_triples,
        all_legendre_fenchel_valid,
        all_binary_splits_exact,
        total_actual_subblock_excess,
        total_lf_sawtooth_excess,
        total_binary_split_diff_sq,
        kappa_dio,
        bound_dio,
        kappa_dio_gk,
        bound_dio_gk,
    }
}
