//! ============================================================================
//! `exact.rs` — Hybrid CPU + GPU Reversible O(1) Bitset-Shift Branch-and-Bound
//! for Exact B_3 Rulers F_3(N) (OEIS A051912) and the Maximin Cubic Lower-Envelope
//! B_3 Problem \mu_3^*(x_0, N).
//! ============================================================================

use crate::gpu::Gpu;
use crate::records::{build_subadditive_b3_cap_table, erdos41_psi, exact_f3_capacity};
use crate::verify_cpu::{can_add_b3_cpu, pop_b3_cpu, push_b3_cpu};
use anyhow::Result;
use cudarc::driver::PushKernelArg;
use rayon::prelude::*;
use serde::Serialize;

#[derive(Debug, Clone)]
pub struct B3PrefixState {
    pub m1: [u64; 2],
    pub m2: [u64; 4],
    pub m3: [u64; 6],
    pub len: u32,
    pub last_x: u32,
}

#[derive(Debug, Clone, Serialize)]
pub struct PrefixB3Outcome {
    pub max_len: u32,
    pub best_m1: [u64; 2],
    pub nodes_visited: u64,
}

#[derive(Debug, Clone, Serialize)]
pub struct ExactF3Result {
    pub n_max: u32,
    pub split_x: u32,
    pub max_cardinality: u32,
    pub witness: Vec<u32>,
    pub total_prefixes: usize,
    pub total_nodes: u64,
}

#[derive(Debug, Clone, Serialize)]
pub struct MaximinB3Result {
    pub n_max: u32,
    pub x0: u32,
    pub mu3_star: f64,
    pub witness: Vec<u32>,
    pub greedy_prefix: Vec<u32>,
    pub greedy_min_psi: f64,
    pub total_nodes: u64,
}

/// Decodes a 128-bit `m1` mask into a sorted vector of 1-indexed integers.
pub fn decode_m1_mask(m1: &[u64; 2]) -> Vec<u32> {
    let mut out = Vec::new();
    for (word_idx, &w) in m1.iter().enumerate() {
        let mut bits = w;
        while bits != 0 {
            let tz = bits.trailing_zeros() as usize;
            out.push((word_idx * 64 + tz) as u32);
            bits &= bits - 1;
        }
    }
    out
}

/// Enumerates all valid B_3 prefixes on `{1, ..., split_x}` containing `1`
/// (by translation invariance every non-empty B_3 subset of `{1, ..., N}` can
/// be shifted so `a_1 = 1`) that satisfy `A(u) >= req_prefix[u]` for `1 <= u <= split_x`.
pub fn enumerate_b3_prefixes(split_x: u32, req_prefix: &[u8]) -> Vec<B3PrefixState> {
    assert!((1..=120).contains(&split_x));
    let mut out = Vec::new();
    let mut m1 = [0u64; 2];
    let mut m2 = [0u64; 4];
    let mut m3 = [0u64; 6];
    push_b3_cpu(&mut m1, &mut m2, &mut m3, 1);

    #[allow(clippy::too_many_arguments)]
    fn dfs_enum(
        x: u32,
        split_x: u32,
        cur_len: u32,
        last_x: u32,
        m1: &mut [u64; 2],
        m2: &mut [u64; 4],
        m3: &mut [u64; 6],
        req_prefix: &[u8],
        out: &mut Vec<B3PrefixState>,
    ) {
        if x > split_x {
            if cur_len >= req_prefix[split_x as usize] as u32 {
                out.push(B3PrefixState {
                    m1: *m1,
                    m2: *m2,
                    m3: *m3,
                    len: cur_len,
                    last_x,
                });
            }
            return;
        }

        if cur_len < req_prefix[(x - 1) as usize] as u32 {
            return;
        }

        // Branch 1: include x if valid B_3 extension
        if can_add_b3_cpu(m1, m2, m3, x as usize) {
            push_b3_cpu(m1, m2, m3, x as usize);
            dfs_enum(x + 1, split_x, cur_len + 1, x, m1, m2, m3, req_prefix, out);
            pop_b3_cpu(m1, m2, m3, x as usize);
        }

        // Branch 2: skip x
        dfs_enum(x + 1, split_x, cur_len, last_x, m1, m2, m3, req_prefix, out);
    }

    dfs_enum(
        2, split_x, 1, 1, &mut m1, &mut m2, &mut m3, req_prefix, &mut out,
    );
    out
}

/// Exact CPU twin of `k_dfs_b3_ruler` in `src/kernels.cu`: runs iterative
/// reversible XOR bitset-shift DFS from a single prefix state.
pub fn extend_b3_dfs_cpu(
    prefix: &B3PrefixState,
    n_max: u32,
    split_x: u32,
    req_prefix: &[u8],
    b3_cap: &[u8],
) -> PrefixB3Outcome {
    let mut m1 = prefix.m1;
    let mut m2 = prefix.m2;
    let mut m3 = prefix.m3;
    let base_len = prefix.len as usize;
    let start_x = (split_x + 1).max(prefix.last_x + 1) as usize;
    let n_max_usize = n_max as usize;

    let mut best_len = 0u32;
    let mut best_m1 = [0u64; 2];
    let mut nodes = 0u64;

    let mut prefix_ok = true;
    for &req in &req_prefix[(split_x as usize)..=n_max_usize] {
        if base_len < req as usize {
            prefix_ok = false;
            break;
        }
    }
    if prefix_ok {
        best_len = base_len as u32;
        best_m1 = m1;
    }

    let mut added_x = [0u8; 16];
    let mut next_try = [0u8; 16];
    let mut depth: isize = 0;
    next_try[0] = start_x as u8;

    while depth >= 0 {
        let d = depth as usize;
        let cur_len = base_len + d;
        let x = next_try[d] as usize;

        if x > n_max_usize {
            depth -= 1;
            if depth >= 0 {
                pop_b3_cpu(&mut m1, &mut m2, &mut m3, added_x[depth as usize] as usize);
            }
            continue;
        }

        next_try[d] = (x + 1) as u8;

        if cur_len < req_prefix[x - 1] as usize {
            depth -= 1;
            if depth >= 0 {
                pop_b3_cpu(&mut m1, &mut m2, &mut m3, added_x[depth as usize] as usize);
            }
            continue;
        }

        let max_possible = cur_len + b3_cap[n_max_usize - x + 1] as usize;
        if max_possible < req_prefix[n_max_usize] as usize || max_possible <= best_len as usize {
            depth -= 1;
            if depth >= 0 {
                pop_b3_cpu(&mut m1, &mut m2, &mut m3, added_x[depth as usize] as usize);
            }
            continue;
        }

        nodes += 1;

        if can_add_b3_cpu(&m1, &m2, &m3, x) {
            let new_len = cur_len + 1;
            push_b3_cpu(&mut m1, &mut m2, &mut m3, x);

            if new_len > best_len as usize {
                let mut tail_ok = true;
                for &req in &req_prefix[x..=n_max_usize] {
                    if new_len < req as usize {
                        tail_ok = false;
                        break;
                    }
                }
                if tail_ok {
                    best_len = new_len as u32;
                    best_m1 = m1;
                }
            }

            if x < n_max_usize && d + 1 < 16 {
                added_x[d] = x as u8;
                depth += 1;
                next_try[d + 1] = (x + 1) as u8;
            } else {
                pop_b3_cpu(&mut m1, &mut m2, &mut m3, x);
            }
        }
    }

    PrefixB3Outcome {
        max_len: best_len,
        best_m1,
        nodes_visited: nodes,
    }
}

/// Evaluates all prefixes in parallel on CPU via Rayon.
pub fn solve_b3_prefixes_cpu(
    prefixes: &[B3PrefixState],
    n_max: u32,
    split_x: u32,
    req_prefix: &[u8],
    b3_cap: &[u8],
) -> Vec<PrefixB3Outcome> {
    prefixes
        .par_iter()
        .map(|p| extend_b3_dfs_cpu(p, n_max, split_x, req_prefix, b3_cap))
        .collect()
}

/// Evaluates all prefixes in parallel on the GPU using `k_dfs_b3_ruler`.
pub fn solve_b3_prefixes_gpu(
    gpu: &Gpu,
    prefixes: &[B3PrefixState],
    n_max: u32,
    split_x: u32,
    req_prefix: &[u8],
    b3_cap: &[u8],
) -> Result<Vec<PrefixB3Outcome>> {
    let n_prefixes = prefixes.len();
    if n_prefixes == 0 {
        return Ok(Vec::new());
    }

    let mut h_m1 = Vec::with_capacity(n_prefixes * 2);
    let mut h_m2 = Vec::with_capacity(n_prefixes * 4);
    let mut h_m3 = Vec::with_capacity(n_prefixes * 6);
    let mut h_len = Vec::with_capacity(n_prefixes);
    let mut h_last = Vec::with_capacity(n_prefixes);

    for p in prefixes {
        h_m1.extend_from_slice(&p.m1);
        h_m2.extend_from_slice(&p.m2);
        h_m3.extend_from_slice(&p.m3);
        h_len.push(p.len);
        h_last.push(p.last_x);
    }

    let d_m1 = gpu.stream.clone_htod(&h_m1)?;
    let d_m2 = gpu.stream.clone_htod(&h_m2)?;
    let d_m3 = gpu.stream.clone_htod(&h_m3)?;
    let d_len = gpu.stream.clone_htod(&h_len)?;
    let d_last = gpu.stream.clone_htod(&h_last)?;
    let d_req = gpu.stream.clone_htod(req_prefix)?;
    let d_cap = gpu.stream.clone_htod(b3_cap)?;

    let mut d_out_len = gpu.stream.alloc_zeros::<u32>(n_prefixes)?;
    let mut d_out_m1 = gpu.stream.alloc_zeros::<u64>(n_prefixes * 2)?;
    let mut d_out_nodes = gpu.stream.alloc_zeros::<u64>(n_prefixes)?;

    let n_pref_u32 = n_prefixes as u32;
    let cfg = gpu.launch_cfg(n_pref_u32);

    unsafe {
        gpu.stream
            .launch_builder(&gpu.fn_dfs_b3_ruler)
            .arg(&d_m1)
            .arg(&d_m2)
            .arg(&d_m3)
            .arg(&d_len)
            .arg(&d_last)
            .arg(&n_pref_u32)
            .arg(&n_max)
            .arg(&split_x)
            .arg(&d_req)
            .arg(&d_cap)
            .arg(&mut d_out_len)
            .arg(&mut d_out_m1)
            .arg(&mut d_out_nodes)
            .launch(cfg)?;
    }

    let out_len = gpu.stream.clone_dtoh(&d_out_len)?;
    let out_m1 = gpu.stream.clone_dtoh(&d_out_m1)?;
    let out_nodes = gpu.stream.clone_dtoh(&d_out_nodes)?;

    let mut results = Vec::with_capacity(n_prefixes);
    for i in 0..n_prefixes {
        results.push(PrefixB3Outcome {
            max_len: out_len[i],
            best_m1: [out_m1[i * 2], out_m1[i * 2 + 1]],
            nodes_visited: out_nodes[i],
        });
    }
    Ok(results)
}

/// Exhaustively computes the exact B_3 capacity `F_3(n_max)` and an explicit
/// optimal B_3 ruler witness in `{1, ..., n_max}`.
pub fn solve_exact_f3(n_max: u32, split_x: u32, gpu: Option<&Gpu>) -> Result<ExactF3Result> {
    assert!((2..=120).contains(&n_max));
    let split = split_x.min(n_max - 1).max(1);
    let req_prefix = vec![0u8; (n_max + 1) as usize];
    let b3_cap = build_subadditive_b3_cap_table(n_max as usize);
    let prefixes = enumerate_b3_prefixes(split, &req_prefix);

    let outcomes = if let Some(g) = gpu {
        solve_b3_prefixes_gpu(g, &prefixes, n_max, split, &req_prefix, &b3_cap)?
    } else {
        solve_b3_prefixes_cpu(&prefixes, n_max, split, &req_prefix, &b3_cap)
    };

    let mut best_len = 0u32;
    let mut best_m1 = [0u64; 2];
    let mut total_nodes = 0u64;

    for o in &outcomes {
        total_nodes += o.nodes_visited;
        if o.max_len > best_len {
            best_len = o.max_len;
            best_m1 = o.best_m1;
        }
    }

    Ok(ExactF3Result {
        n_max,
        split_x: split,
        max_cardinality: best_len,
        witness: decode_m1_mask(&best_m1),
        total_prefixes: prefixes.len(),
        total_nodes,
    })
}

/// Solves the exact Maximin Cubic Lower-Envelope B_3 Problem on `[1, n_max]`:
///   \mu_3^*(x_0, n_max) = \max_{A \subseteq [n_max] B_3} \min_{x \in [x_0, n_max]} A(x) / x^{1/3}.
/// Since `A(x) \in {1, ..., F_3(n_max)}` and `x \in {x_0, ..., n_max}`, the optimal
/// threshold `\tau = \mu_3^*(x_0, n_max)` belongs to the finite rational-root grid
/// `{m / x^{1/3} : 1 <= m <= F_3(n_max), x_0 <= x <= n_max}`.
pub fn solve_maximin_b3_envelope(
    n_max: u32,
    x0: u32,
    split_x: u32,
    gpu: Option<&Gpu>,
) -> Result<MaximinB3Result> {
    assert!(x0 >= 1 && x0 <= n_max && n_max <= 120);
    let split = split_x.min(n_max - 1).max(1);
    let max_k = exact_f3_capacity(n_max) as usize;
    let b3_cap = build_subadditive_b3_cap_table(n_max as usize);

    // Collect all candidate threshold values \tau = m / x^{1/3}
    let mut candidates: Vec<f64> = Vec::new();
    for m in 1..=max_k {
        for x in x0..=n_max {
            candidates.push(erdos41_psi(m, x));
        }
    }
    candidates.sort_by(|a, b| a.partial_cmp(b).unwrap());
    candidates.dedup_by(|a, b| (*a - *b).abs() < 1e-12);

    let mut lo = 0usize;
    let mut hi = candidates.len();
    let mut best_tau = 0.0f64;
    let mut best_witness = vec![1u32];
    let mut total_nodes = 0u64;

    while lo < hi {
        let mid = (lo + hi) / 2;
        let tau = candidates[mid];

        // Build integer prefix-floor profile req_prefix[x] = ceil((tau - 1e-12) * x^{1/3})
        let mut req_prefix = vec![0u8; (n_max + 1) as usize];
        let mut possible = true;
        for x in x0..=n_max {
            let needed = ((tau - 1e-12) * (x as f64).cbrt()).ceil() as usize;
            if needed > max_k {
                possible = false;
                break;
            }
            req_prefix[x as usize] = needed as u8;
        }
        // Monotonize req_prefix
        for x in 1..=(n_max as usize) {
            if req_prefix[x] < req_prefix[x - 1] {
                req_prefix[x] = req_prefix[x - 1];
            }
        }

        let mut found_m1 = None;
        if possible {
            let prefixes = enumerate_b3_prefixes(split, &req_prefix);
            let outcomes = if let Some(g) = gpu {
                solve_b3_prefixes_gpu(g, &prefixes, n_max, split, &req_prefix, &b3_cap)?
            } else {
                solve_b3_prefixes_cpu(&prefixes, n_max, split, &req_prefix, &b3_cap)
            };
            for o in &outcomes {
                total_nodes += o.nodes_visited;
                if o.max_len > 0 && found_m1.is_none() {
                    found_m1 = Some(o.best_m1);
                }
            }
        }

        if let Some(m1) = found_m1 {
            best_tau = tau;
            best_witness = decode_m1_mask(&m1);
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    // Recompute exact min_{x \in [x0, n_max]} \Psi_A(x) on best_witness
    let mut exact_min = f64::INFINITY;
    let mut ptr = 0usize;
    for x in 1..=n_max {
        while ptr < best_witness.len() && best_witness[ptr] <= x {
            ptr += 1;
        }
        if x >= x0 {
            exact_min = exact_min.min(erdos41_psi(ptr, x));
        }
    }
    if exact_min.is_finite() {
        best_tau = exact_min;
    }

    // Compare against greedy B_3 prefix (OEIS A004023) on [1, n_max]
    let greedy_prefix: Vec<u32> = crate::records::OEIS_A004023_FIRST_30
        .iter()
        .copied()
        .filter(|&v| v <= n_max)
        .collect();
    let mut greedy_min_psi = f64::INFINITY;
    let mut g_ptr = 0usize;
    for x in 1..=n_max {
        while g_ptr < greedy_prefix.len() && greedy_prefix[g_ptr] <= x {
            g_ptr += 1;
        }
        if x >= x0 {
            greedy_min_psi = greedy_min_psi.min(erdos41_psi(g_ptr, x));
        }
    }

    Ok(MaximinB3Result {
        n_max,
        x0,
        mu3_star: best_tau,
        witness: best_witness,
        greedy_prefix,
        greedy_min_psi,
        total_nodes,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::records::{
        b3_diophantine_haar_boost_and_bound, build_bose_chowla_block_sequence,
        construct_bose_chowla_b3, cubic_beta_positive_cone_area, diophantine_haar_integral,
        eta_fermat_asymptotic_constants, eta_fermat_sublevel_cone_volume,
        evaluate_dyadic_b3_shells, evaluate_intrashell_negative_cone_shells,
        exact_haar_sawtooth_antideriv, fermat_cone_integral_closed_form,
        horizon_truncated_continuum_integrals, odd_bp_diophantine_haar_bound,
        odd_bp_fermat_majorized_volume_and_bound, odd_bp_inner_antideriv,
        odd_bp_inner_antideriv_to_one_smooth, odd_bp_sublevel_volume_and_bound,
        one_sided_fermat_cone_volume, quantile_envelope_max_variance_kappa_star,
        quantile_envelope_stationary_point_t_star, regular_density_upper_bound_at_eps,
        sawtooth_period_integral, slot_eviction_continuum_bound, sublevel_laurent_alpha_beta,
        sublevel_subcone_first_moment_s_infty, sublevel_subcone_marginal_weight_wl,
        sublevel_subcone_vol_and_moment_at_l, sublevel_subcone_volume_k_star,
        sublevel_subcone_volume_k_star_smooth, sublevel_vol_and_moment_laurent,
        unconditional_liminf_bound_one_sided_fermat_laplace,
        unconditional_liminf_bound_sublevel_subcone, unconditional_liminf_bound_variance,
        GLAISHER_KINKELIN_C_GK, OEIS_A004023_FIRST_30, OPTIMAL_B3_RULERS,
    };
    use crate::verify_cpu::{
        eval_b3_diophantine_haar_closure, eval_full_cube_variance_identity,
        eval_horizon_truncated_rays, eval_quadratic_injection_rays, eval_sublevel_subcone_identity,
        eval_telescoping_third_hemisphere, eval_three_hemisphere_partition,
        evaluate_b3_conservation, evaluate_sign_split_cones, generate_greedy_b3_sequence,
        is_b3_sequence, verify_ordered_21_diff_injectivity,
    };

    #[test]
    fn test_greedy_b3_matches_oeis_a004023() {
        let gen = generate_greedy_b3_sequence(20);
        assert_eq!(&gen[..], &OEIS_A004023_FIRST_30[..20]);
        assert!(is_b3_sequence(&OEIS_A004023_FIRST_30));
        assert!(verify_ordered_21_diff_injectivity(&OEIS_A004023_FIRST_30));
    }

    #[test]
    fn test_optimal_b3_rulers_and_theorem_2_1_conservation() {
        for rec in OPTIMAL_B3_RULERS.iter() {
            assert_eq!(rec.witness.len(), rec.k);
            assert_eq!(*rec.witness.last().unwrap(), rec.min_n);
            assert!(is_b3_sequence(rec.witness));
            assert!(verify_ordered_21_diff_injectivity(rec.witness));

            let rep = evaluate_b3_conservation(rec.witness, rec.min_n.max(2), 1);
            assert!(rep.is_b3);
            assert!(rep.is_w_injective);
            assert!(rep.asymmetric_defect >= -1e-15);
            assert!(
                rep.conservation_error < 1e-12,
                "Conservation error {} too large for k={}",
                rep.conservation_error,
                rec.k
            );
            assert!(rep.harmonic_budget <= rep.harmonic_upper_bound + 1e-12);
        }
    }

    #[test]
    fn test_theorem_2_1_dyadic_shells_and_equality_at_r1() {
        // At R = 1 (N = 2), A = {1, 2} achieves exact equality: LHS = 1/2 = R - 1/2.
        let cert_r1 = evaluate_dyadic_b3_shells(&[1, 2], 1);
        assert!((cert_r1.shell_lhs - 0.5).abs() < 1e-12);
        assert!((cert_r1.weighted_w_sum - 0.5).abs() < 1e-12);
        assert!((cert_r1.ceiling_r_minus_half - 0.5).abs() < 1e-12);

        for r in 2..=14 {
            let cert = evaluate_dyadic_b3_shells(&OEIS_A004023_FIRST_30, r);
            assert!(cert.resonance_reinforcement >= -1e-12);
            assert!(
                (cert.shell_lhs + cert.resonance_reinforcement - cert.weighted_w_sum).abs() < 1e-12
            );
            assert!(cert.weighted_w_sum <= cert.ceiling_r_minus_half + 1e-12);
        }
    }

    #[test]
    fn test_theorem_2_2_bose_chowla_and_pigeonhole_gap_compression() {
        for &p in &[2u32, 3, 5, 7, 11] {
            let bc = construct_bose_chowla_b3(p);
            assert_eq!(bc.compressed_set.len(), p as usize);
            assert!(is_b3_sequence(&bc.raw_shifted));
            assert!(is_b3_sequence(&bc.compressed_set));
            assert!(verify_ordered_21_diff_injectivity(&bc.compressed_set));
            assert!(
                bc.max_modular_gap >= p * p,
                "Pigeonhole modular gap {} < p^2 = {}",
                bc.max_modular_gap,
                p * p
            );
            assert!(
                bc.compressed_span_n <= p * p * p - p * p,
                "Compressed span {} > p^3 - p^2",
                bc.compressed_span_n
            );
        }

        let (spliced, epochs) = build_bose_chowla_block_sequence(&[2, 3, 5]);
        assert!(is_b3_sequence(&spliced));
        assert!(verify_ordered_21_diff_injectivity(&spliced));
        assert_eq!(epochs.len(), 3);
        assert!(epochs[0].burst_psi > epochs[1].desert_psi);
    }

    #[test]
    fn test_reversible_xor_bitset_shift_invariance() {
        let mut m1 = [0u64; 2];
        let mut m2 = [0u64; 4];
        let mut m3 = [0u64; 6];
        let seq = [1usize, 2, 8, 51, 60, 79, 83];

        let mut snapshots = Vec::new();
        for &x in &seq {
            snapshots.push((m1, m2, m3));
            assert!(can_add_b3_cpu(&m1, &m2, &m3, x));
            push_b3_cpu(&mut m1, &mut m2, &mut m3, x);
        }
        for (&x, &(s1, s2, s3)) in seq.iter().zip(snapshots.iter()).rev() {
            pop_b3_cpu(&mut m1, &mut m2, &mut m3, x);
            assert_eq!(m1, s1);
            assert_eq!(m2, s2);
            assert_eq!(m3, s3);
        }
    }

    #[test]
    fn test_exact_f3_solver_cpu_matches_oeis_a051912() {
        for &(n, expected_k) in &[(5u32, 3u32), (11, 3), (12, 4), (23, 4), (24, 5)] {
            let res = solve_exact_f3(n, 5.min(n - 1), None).unwrap();
            assert_eq!(res.max_cardinality, expected_k, "Mismatch at N={n}");
            assert!(is_b3_sequence(&res.witness));
        }
    }

    #[test]
    fn test_theorem_2_3_sign_split_cones_and_intrashell_exclusivity() {
        for r in [2u32, 4, 6, 8, 10, 12, 14] {
            let n = 1u32 << r;
            let cone = evaluate_sign_split_cones(&OEIS_A004023_FIRST_30, n);
            let full = evaluate_b3_conservation(&OEIS_A004023_FIRST_30, n, 1);
            assert!(cone.zero_count <= 1);
            assert_eq!(
                cone.pos_count + cone.zero_count + cone.neg_count,
                full.num_triples
            );
            assert!(cone.pos_conservation_error < 1e-12);
            assert!(cone.neg_conservation_error < 1e-12);
            assert!(cone.pos_budget <= cone.single_cone_ceiling + 1e-12);
            assert!(cone.neg_budget <= cone.single_cone_ceiling + 1e-12);

            let intra = evaluate_intrashell_negative_cone_shells(&OEIS_A004023_FIRST_30, r);
            assert!(intra.all_intrashell_in_negative_cone);
            assert!(intra.intrashell_dyadic_lhs <= intra.negative_cone_dyadic_sum + 1e-12);
            assert!(intra.negative_cone_dyadic_sum <= intra.half_ceiling + 1e-12);
        }

        // Also verify on all Bose-Chowla compressed sets (which are denser within a single shell)
        for &p in &[3u32, 5, 7, 11] {
            let bc = construct_bose_chowla_b3(p);
            let r = (bc.compressed_span_n.ilog2() + 1).max(2);
            let intra = evaluate_intrashell_negative_cone_shells(&bc.compressed_set, r);
            assert!(intra.all_intrashell_in_negative_cone);
            assert!(intra.intrashell_dyadic_lhs <= intra.negative_cone_dyadic_sum + 1e-12);
            assert!(intra.negative_cone_dyadic_sum <= intra.half_ceiling + 1e-12);
        }
    }

    #[test]
    fn test_theorem_2_4_cubic_beta_and_fermat_cone_integral() {
        let area = cubic_beta_positive_cone_area();
        assert!((area - 0.441_659_687_6).abs() < 1e-9);
        assert!(area / 0.5 > 0.8833 && area / 0.5 < 0.8834);

        // Verify monotonic divergence of I_+(eps) as eps -> 0^+ and vanishing of c_max(eps)
        let i_1e1 = fermat_cone_integral_closed_form(1e-1);
        let i_1e3 = fermat_cone_integral_closed_form(1e-3);
        let i_1e6 = fermat_cone_integral_closed_form(1e-6);
        let i_1e12 = fermat_cone_integral_closed_form(1e-12);
        assert!(i_1e1 < i_1e3 && i_1e3 < i_1e6 && i_1e6 < i_1e12);
        assert!(regular_density_upper_bound_at_eps(1e-12) < 0.72);
    }

    #[test]
    fn test_theorem_2_5_full_cube_variance_and_theorem_2_6_one_sided_cone() {
        // 1. Verify Theorem 2.5(1)-(3) and Theorem 2.6 across prefixes of OEIS A004023
        for m in [3usize, 5, 8, 12, 16, 20, 25, 30] {
            let rep = eval_full_cube_variance_identity(&OEIS_A004023_FIRST_30[..m]);
            assert_eq!(rep.total_triples_tm, m * m * (m - 1) / 2);
            assert!(rep.is_full_cube_injective);
            assert_eq!(rep.distinct_w_count, rep.total_triples_tm);
            assert!(rep.variance_identity_error < 1e-8 * rep.theoretical_var_w.max(1.0));
            assert!(rep.sigma_a_sq >= rep.universal_sigma_a_sq_lower_bound - 1e-9);
            assert_eq!(rep.one_sided_pos_triples, m * (m - 1) * (2 * m - 1) / 6);
            assert!(rep.all_one_sided_ge_2);
            assert!(rep.one_sided_conservation_error < 1e-12);
            assert!(rep.one_sided_budget <= rep.one_sided_harmonic_ceiling + 1e-12);
        }

        // 2. Verify on all optimal B_3 rulers k = 3..10 (OEIS A051912) and Bose–Chowla sets
        for rec in OPTIMAL_B3_RULERS.iter().skip(2) {
            let rep = eval_full_cube_variance_identity(rec.witness);
            assert!(rep.is_full_cube_injective);
            assert!(rep.variance_identity_error < 1e-10 * rep.theoretical_var_w.max(1.0));
            assert!(rep.sigma_a_sq >= rep.universal_sigma_a_sq_lower_bound - 1e-9);
            assert!(rep.all_one_sided_ge_2);
            assert!(rep.one_sided_conservation_error < 1e-12);
            assert!(rep.one_sided_budget <= rep.one_sided_harmonic_ceiling + 1e-12);
        }
        for &p in &[3u32, 5, 7, 11] {
            let bc = construct_bose_chowla_b3(p);
            let rep = eval_full_cube_variance_identity(&bc.compressed_set);
            assert!(rep.is_full_cube_injective);
            assert!(rep.variance_identity_error < 1e-9 * rep.theoretical_var_w.max(1.0));
            assert!(rep.sigma_a_sq >= rep.universal_sigma_a_sq_lower_bound - 1e-9);
            assert!(rep.all_one_sided_ge_2);
            assert!(rep.one_sided_conservation_error < 1e-12);
            assert!(rep.one_sided_budget <= rep.one_sided_harmonic_ceiling + 1e-12);
        }

        // 3. Verify stationary point t_*^4 + 2 t_*^3 - 1 = 0, kappa_*, and unconditional liminf bounds
        let t_star = quantile_envelope_stationary_point_t_star();
        assert!((t_star.powi(4) + 2.0 * t_star.powi(3) - 1.0).abs() < 1e-15);
        assert!((t_star - 0.716_672_749_282_286_6).abs() < 1e-12);
        let kappa_star = quantile_envelope_max_variance_kappa_star();
        assert!((kappa_star - 0.095_110_939_533_083_3).abs() < 1e-12);
        let c_var = unconditional_liminf_bound_variance();
        let c_fermat_laplace = unconditional_liminf_bound_one_sided_fermat_laplace();
        assert!((c_var - 1.546_792_866_9).abs() < 1e-9);
        assert!((c_fermat_laplace - 1.531_201_967_9).abs() < 1e-9);
        assert!(c_fermat_laplace < c_var && c_var < 4.0_f64.cbrt());
        assert!((one_sided_fermat_cone_volume() - 0.278_549_616_1).abs() < 1e-9);
    }

    #[test]
    fn test_theorem_2_7_sublevel_subcone_and_beta_gamma_bound() {
        // 1. Verify Part (a) exact polynomial identity \sum_{I_m^<} (a_i+a_j-a_k) == \sum_{r=1}^m (r^2-m)a_r
        //    and Part (b) discrete weights C_r(m, \tau) >= 0 across prefixes of OEIS A004023
        for m in [10usize, 15, 20, 25, 30] {
            for &(tau_num, tau_den) in &[(1u64, 1u64), (1, 2), (1, 4), (1, 8)] {
                let rep =
                    eval_sublevel_subcone_identity(&OEIS_A004023_FIRST_30[..m], tau_num, tau_den);
                assert_eq!(rep.full_cone_triple_count, m * (m - 1) * (2 * m - 1) / 6);
                assert_eq!(rep.full_cone_triple_sum, rep.full_cone_poly_rhs);
                assert!(rep.full_cone_triple_sum >= rep.full_cone_min_distinct_sum);
                assert_eq!(rep.sublevel_triple_sum, rep.sublevel_weighted_rhs);
                assert!(rep.sublevel_triple_sum >= rep.sublevel_min_distinct_sum);
                assert!(
                    rep.min_discrete_weight >= 0,
                    "Negative discrete weight {} at m={}, tau={}/{}",
                    rep.min_discrete_weight,
                    m,
                    tau_num,
                    tau_den
                );
            }
        }

        // 2. Verify continuous marginal weight W_L(U) > 0 across U in (0, L]
        for &l in &[1.0_f64, 1.5, 2.0, 3.0, 5.0] {
            for k in 1..=16 {
                let u = l * (k as f64) / 16.0;
                let (_wx, _wy, _wz, wl) = sublevel_subcone_marginal_weight_wl(u, l);
                assert!(wl > -1e-9, "Expected W_L(U) >= 0 at L={l}, U={u}, got {wl}");
            }
        }

        // 3. Verify monotone convergence of finite-L bound (2 S(\Omega_L^*) / Vol(\Omega_L^*)^2)^{1/3}
        //    and exact asymptotic constant K_*^{-1/3} = 1.1998559643 < 2^{1/3}
        let (_v1, _s1, b1) = sublevel_subcone_vol_and_moment_at_l(1.0);
        let (_v2, _s2, b2) = sublevel_subcone_vol_and_moment_at_l(2.0);
        let (_v3, _s3, b3) = sublevel_subcone_vol_and_moment_at_l(3.0);
        let (_v5, _s5, b5) = sublevel_subcone_vol_and_moment_at_l(5.0);
        let k_star = sublevel_subcone_volume_k_star();
        let s_infty = sublevel_subcone_first_moment_s_infty();
        let b_infty = unconditional_liminf_bound_sublevel_subcone();

        assert!((k_star - 0.578_912_138_720_754_3).abs() < 1e-8);
        assert!((s_infty - 0.5 * k_star).abs() < 1e-15);
        assert!((b_infty - 1.199_855_964_300_271).abs() < 1e-8);
        assert!(b1 > b2 && b2 > b3 && b3 > b5 && b5 > b_infty);
        assert!(b3 < 2.0_f64.cbrt());
        assert!(b_infty < 1.20 && b_infty < 2.0_f64.cbrt());
    }

    #[test]
    fn test_theorem_2_8_variational_laurent_and_odd_bp() {
        // 1. Verify exact rational Laurent coefficients (\alpha_n, \beta_n = (3n+1)/(3n+4)\alpha_n)
        let expected_alpha = [
            1.0 / 4.0,
            1.0 / 56.0,
            1.0 / 196.0,
            1.0 / 455.0,
            11.0 / 9464.0,
        ];
        let expected_beta = [
            1.0 / 7.0,
            1.0 / 80.0,
            5.0 / 1274.0,
            1.0 / 560.0,
            22.0 / 22477.0,
        ];
        for n in 1..=5 {
            let (a_n, b_n) = sublevel_laurent_alpha_beta(n);
            assert!((a_n - expected_alpha[n - 1]).abs() < 1e-15);
            assert!((b_n - expected_beta[n - 1]).abs() < 1e-15);
        }

        // 2. Verify high-accuracy agreement between exact quadrature and 25-term Laurent expansion
        for &l in &[1.5_f64, 2.0, 3.0, 5.0] {
            let (v_num, s_num, b_num) = sublevel_subcone_vol_and_moment_at_l(l);
            let (v_laur, s_laur, b_laur) = sublevel_vol_and_moment_laurent(l, 25);
            assert!((v_num - v_laur).abs() < 1e-6);
            assert!((s_num - s_laur).abs() < 1e-6);
            assert!((b_num - b_laur).abs() < 1e-6);
        }

        // 3. Verify odd-order B_p projective Fermat sub-cone volumes and bounds (p = 3, 5, 7)
        let (k3, b3, _, _) = odd_bp_sublevel_volume_and_bound(3, 16);
        assert!((k3 - 0.578_912_138_720_754_3).abs() < 1e-8);
        assert!((b3 - 1.199_855_964_300_271).abs() < 1e-8);

        let (k5_ord, b5_ord, k5_prod, b5_prod) = odd_bp_sublevel_volume_and_bound(5, 32);
        assert!((k5_ord - 0.053725).abs() < 4e-4);
        assert!((b5_ord - 1.794587).abs() < 3e-3);
        assert!((k5_prod - 0.073021).abs() < 4e-4);
        assert!((b5_prod - 1.687761).abs() < 3e-3);

        let (k7_ord, b7_ord, k7_prod, b7_prod) = odd_bp_sublevel_volume_and_bound(7, 12);
        assert!((k7_ord - 0.003193).abs() < 3e-4);
        assert!((b7_ord - 2.2727).abs() < 3e-2);
        assert!((k7_prod - 0.008584).abs() < 5e-4);
        assert!((b7_prod - 1.9733).abs() < 3e-2);
    }

    #[test]
    fn test_theorem_2_9_full_hypercube_digamma_and_eta_fermat() {
        // 1. Verify Three-Hemisphere Partition on OEIS A004023 prefixes (Theorem 2.9(a))
        for &m in &[10usize, 16, 22, 30] {
            let rep = eval_three_hemisphere_partition(&OEIS_A004023_FIRST_30[..m]);
            assert_eq!(rep.lo_count, m * (m - 1) * (m + 1) / 6);
            assert_eq!(rep.mid_count, m * (m - 1) * (m - 2) / 6);
            assert_eq!(rep.lo_count + rep.mid_count, m * (m - 1) * (2 * m - 1) / 6);
            assert_eq!(
                rep.lo_count + rep.mid_count + rep.hi_pos_count + rep.hi_nonpos_count,
                m * m * (m - 1) / 2
            );
        }

        // 2. Verify globally smooth C^\infty formula for K_* and hemisphere split (Theorem 2.9(b))
        let (k_lo, k_mid, k_smooth) = sublevel_subcone_volume_k_star_smooth();
        let k_sing = sublevel_subcone_volume_k_star();
        assert!((k_smooth - 0.578_912_138_720_754_3).abs() < 1e-9);
        assert!((k_smooth - k_sing).abs() < 1e-7);
        assert!((k_lo - 0.133_160_803_968).abs() < 1e-7);
        assert!((k_mid - 0.445_751_334_753).abs() < 1e-7);

        // 3. Verify one-parameter \eta-Fermat sub-level cone family K_*(\eta) (Theorem 2.9(c))
        let (c_log, c_0) = eta_fermat_asymptotic_constants();
        assert!((c_log - 0.098_146_597_238).abs() < 1e-9);
        assert!((c_0 - 0.589_833_727_041).abs() < 1e-7);

        let (khi_1, ktot_1, b_1) = eta_fermat_sublevel_cone_volume(1.0);
        let (_, ktot_05, b_05) = eta_fermat_sublevel_cone_volume(0.5);
        let (_, ktot_001, b_001) = eta_fermat_sublevel_cone_volume(0.01);
        let (_, ktot_1e6, b_1e6) = eta_fermat_sublevel_cone_volume(1e-6);
        assert!(khi_1.abs() < 1e-15);
        assert!((ktot_1 - k_smooth).abs() < 1e-15);
        assert!(ktot_1 < ktot_05 && ktot_05 < ktot_001 && ktot_001 < ktot_1e6);
        assert!(b_1 > b_05 && b_05 > b_001 && b_001 > b_1e6);
        assert!(ktot_001 > 1.0 && b_001 < 1.0);
        let asymp_1e6 = c_log * (1e6_f64).ln() + c_0;
        assert!((ktot_1e6 - asymp_1e6).abs() < 1e-4);
    }

    #[test]
    fn test_theorem_2_10_telescoping_third_hemisphere_and_bp_fermat_majorized() {
        // 1. Verify Theorem 2.10(a) step-s telescoping identity, Markov bound, and dual upper-cone polynomial
        for m in [6usize, 12, 22, 30] {
            let sub = &OEIS_A004023_FIRST_30[..m];
            let rep = eval_telescoping_third_hemisphere(sub);
            assert_eq!(rep.num_rays, m * (m - 1) / 2);
            assert!(rep.all_rays_telescope_exact);
            assert!(rep.all_markov_bounds_hold);
            assert_eq!(rep.step1_telescoping_sum, rep.step1_telescoping_rhs);
            assert_eq!(rep.upper_cone_sum, rep.upper_poly_rhs);
            assert_eq!(rep.lower_plus_upper_sum, rep.full_cube_binom_rhs);
        }

        let bc7 = construct_bose_chowla_b3(7);
        let rep_bc7 = eval_telescoping_third_hemisphere(&bc7.compressed_set);
        assert!(rep_bc7.all_rays_telescope_exact);
        assert!(rep_bc7.all_markov_bounds_hold);
        assert_eq!(rep_bc7.step1_telescoping_sum, rep_bc7.step1_telescoping_rhs);
        assert_eq!(rep_bc7.upper_cone_sum, rep_bc7.upper_poly_rhs);
        assert_eq!(rep_bc7.lower_plus_upper_sum, rep_bc7.full_cube_binom_rhs);

        // 2. Verify Theorem 2.10(b) cancellation-free cyclotomic antiderivative
        for &p in &[3usize, 5, 7] {
            for &delta in &[0.05_f64, 0.35, 1.25] {
                for &z_lo in &[0.0_f64, 0.25, 0.75] {
                    let s_val = odd_bp_inner_antideriv_to_one_smooth(p, delta, z_lo);
                    let d_val = odd_bp_inner_antideriv(p, delta, z_lo, 1.0);
                    assert!((s_val - d_val).abs() < 1e-13);
                }
            }
            // Test ultra-small delta = 1e-14 where naive 1.0 - 1.0/A loses digits
            let tiny_val = odd_bp_inner_antideriv_to_one_smooth(p, 1e-14, 0.2);
            assert!(tiny_val.is_finite() && tiny_val > 0.0);
        }

        // 3. Verify Pole-Free Fermat-Majorized Region III volumes for B_5 and B_7
        let (r3_5, k_ferm_5, b_ferm_5, r3_prod_5, k_pferm_5, b_pferm_5) =
            odd_bp_fermat_majorized_volume_and_bound(5, 48);
        let (k_ord_5, b_ord_5, k_prod_5, b_prod_5) = odd_bp_sublevel_volume_and_bound(5, 48);
        assert!((r3_5 - 0.0014018).abs() < 1e-5);
        assert!(k_ferm_5 > k_ord_5 && b_ferm_5 < b_ord_5);
        assert!((b_ferm_5 - 1.78539).abs() < 2e-3);
        assert!((r3_prod_5 - 0.0026616).abs() < 2e-5);
        assert!(k_pferm_5 > k_prod_5 && b_pferm_5 < b_prod_5);
        assert!((b_pferm_5 - 1.6757).abs() < 2e-3);

        let (r3_7, k_ferm_7, b_ferm_7, r3_prod_7, k_pferm_7, b_pferm_7) =
            odd_bp_fermat_majorized_volume_and_bound(7, 10);
        let (k_ord_7, b_ord_7, k_prod_7, b_prod_7) = odd_bp_sublevel_volume_and_bound(7, 10);
        assert!(r3_7 > 0.0001 && r3_prod_7 > 0.0004);
        assert!(k_ferm_7 > k_ord_7 && b_ferm_7 < b_ord_7);
        assert!(k_pferm_7 > k_prod_7 && b_pferm_7 < b_prod_7);
    }

    #[test]
    fn test_theorem_2_11_horizon_truncated_rays_and_am_gm_cutoff() {
        // 1. Verify Theorem 2.11(a) on OEIS A004023 prefixes m in {12, 22, 30}
        let rep12 = eval_horizon_truncated_rays(&OEIS_A004023_FIRST_30[..12]);
        assert!(rep12.all_truncated_identities_exact && rep12.all_truncated_bounds_valid);
        assert_eq!(rep12.actual_third_hemisphere_pos_count, 11);
        assert_eq!(rep12.untruncated_mingap_certified_count, 3);
        assert_eq!(rep12.truncated_mingap_certified_count, 8);
        assert_eq!(rep12.untruncated_active_rays, 3);
        assert_eq!(rep12.truncated_active_rays, 7);

        let rep22 = eval_horizon_truncated_rays(&OEIS_A004023_FIRST_30[..22]);
        assert!(rep22.all_truncated_identities_exact && rep22.all_truncated_bounds_valid);
        assert_eq!(rep22.actual_third_hemisphere_pos_count, 80);
        assert_eq!(rep22.untruncated_mingap_certified_count, 34);
        assert_eq!(rep22.truncated_mingap_certified_count, 50);
        assert_eq!(rep22.untruncated_active_rays, 16);
        assert_eq!(rep22.truncated_active_rays, 28);

        let rep30 = eval_horizon_truncated_rays(&OEIS_A004023_FIRST_30);
        assert!(rep30.all_truncated_identities_exact && rep30.all_truncated_bounds_valid);
        assert_eq!(rep30.actual_third_hemisphere_pos_count, 214);
        assert_eq!(rep30.untruncated_mingap_certified_count, 83);
        assert_eq!(rep30.truncated_mingap_certified_count, 126);
        assert_eq!(rep30.untruncated_active_rays, 30);
        assert_eq!(rep30.truncated_active_rays, 56);

        let bc7 = construct_bose_chowla_b3(7);
        let rep_bc7 = eval_horizon_truncated_rays(&bc7.compressed_set);
        assert!(rep_bc7.all_truncated_identities_exact && rep_bc7.all_truncated_bounds_valid);
        assert!(
            rep_bc7.truncated_mingap_certified_count >= rep_bc7.untruncated_mingap_certified_count
        );

        // 2. Verify Theorem 2.11(b)-(c) continuum AM-GM cutoff integrals 1/(6p(p+1)) and 1/(2p(p+3)(2p+1))
        let (ex_norm_3, ex_raw_3, quad_norm_3, untrunc_3) =
            horizon_truncated_continuum_integrals(3, 512);
        assert!((ex_norm_3 - 1.0 / 72.0).abs() < 1e-15);
        assert!((ex_raw_3 - 1.0 / 252.0).abs() < 1e-15);
        assert!((quad_norm_3 - ex_norm_3).abs() < 1e-6);
        assert!((untrunc_3 - 0.012_130_102_225).abs() < 1e-9);
        assert!(ex_norm_3 > untrunc_3 * 1.14);

        let (ex_norm_5, ex_raw_5, quad_norm_5, untrunc_5) =
            horizon_truncated_continuum_integrals(5, 512);
        assert!((ex_norm_5 - 1.0 / 180.0).abs() < 1e-15);
        assert!((ex_raw_5 - 1.0 / 880.0).abs() < 1e-15);
        assert!((quad_norm_5 - ex_norm_5).abs() < 1e-6);
        assert!(ex_norm_5 > untrunc_5);

        let (ex_norm_7, ex_raw_7, quad_norm_7, untrunc_7) =
            horizon_truncated_continuum_integrals(7, 512);
        assert!((ex_norm_7 - 1.0 / 336.0).abs() < 1e-15);
        assert!((ex_raw_7 - 1.0 / 2100.0).abs() < 1e-15);
        assert!((quad_norm_7 - ex_norm_7).abs() < 1e-6);
        assert!(ex_norm_7 > untrunc_7);
    }

    #[test]
    fn test_theorem_2_12_quadratic_injection_and_windowed_rays() {
        // 1. Verify Theorem 2.12(a)-(c) on OEIS A004023 prefixes m in {12, 22, 30}
        let rep12 = eval_quadratic_injection_rays(&OEIS_A004023_FIRST_30[..12]);
        assert!(rep12.all_window_identities_exact && rep12.all_injection_bounds_valid);
        assert_eq!(rep12.actual_third_hemisphere_pos_count, 11);
        assert_eq!(rep12.trunc_sidon_quad_certified_count, 8);
        assert_eq!(rep12.trunc_raygap_quad_certified_count, 11);
        assert_eq!(rep12.slot_evict_certified_count, 6);
        assert_eq!(rep12.one_sided_poly_lhs, 335_345);
        assert_eq!(rep12.base_min_distinct_rhs, 128_271);
        assert_eq!(rep12.slot_evict_poly_rhs, 129_793);

        let rep22 = eval_quadratic_injection_rays(&OEIS_A004023_FIRST_30[..22]);
        assert!(rep22.all_window_identities_exact && rep22.all_injection_bounds_valid);
        assert_eq!(rep22.actual_third_hemisphere_pos_count, 80);
        assert_eq!(rep22.trunc_sidon_quad_certified_count, 50);
        assert_eq!(rep22.trunc_raygap_quad_certified_count, 67);
        assert_eq!(rep22.slot_evict_certified_count, 23);
        assert_eq!(rep22.one_sided_poly_lhs, 25_093_137);
        assert_eq!(rep22.base_min_distinct_rhs, 5_483_016);
        assert_eq!(rep22.slot_evict_poly_rhs, 5_523_707);

        let rep30 = eval_quadratic_injection_rays(&OEIS_A004023_FIRST_30);
        assert!(rep30.all_window_identities_exact && rep30.all_injection_bounds_valid);
        assert_eq!(rep30.actual_third_hemisphere_pos_count, 214);
        assert_eq!(rep30.trunc_sidon_quad_certified_count, 126);
        assert_eq!(rep30.trunc_raygap_quad_certified_count, 172);
        assert_eq!(rep30.total_anchor_fiber_s_star, 1_510_090);
        assert_eq!(rep30.slot_evict_certified_count, 50);
        assert_eq!(rep30.one_sided_poly_lhs, 242_565_637);
        assert_eq!(rep30.base_min_distinct_rhs, 36_598_290);
        assert_eq!(rep30.slot_evict_poly_rhs, 36_827_084);

        // 2. Verify strict improvement of two-sided windowed telescoping (J >= i) over J = i on Bose–Chowla sets
        let bc5 = construct_bose_chowla_b3(5);
        let rep_bc5_raw = eval_quadratic_injection_rays(&bc5.raw_shifted);
        assert!(rep_bc5_raw.all_window_identities_exact && rep_bc5_raw.all_injection_bounds_valid);
        assert_eq!(rep_bc5_raw.actual_third_hemisphere_pos_count, 2);
        assert_eq!(rep_bc5_raw.trunc_sidon_quad_certified_count, 1);
        assert_eq!(rep_bc5_raw.windowed_sidon_quad_certified_count, 2);

        let bc7 = construct_bose_chowla_b3(7);
        let rep_bc7_raw = eval_quadratic_injection_rays(&bc7.raw_shifted);
        assert!(rep_bc7_raw.all_window_identities_exact && rep_bc7_raw.all_injection_bounds_valid);
        assert_eq!(rep_bc7_raw.actual_third_hemisphere_pos_count, 12);
        assert_eq!(rep_bc7_raw.trunc_sidon_quad_certified_count, 9);
        assert_eq!(rep_bc7_raw.windowed_sidon_quad_certified_count, 11);

        let bc11 = construct_bose_chowla_b3(11);
        let rep_bc11_comp = eval_quadratic_injection_rays(&bc11.compressed_set);
        assert!(
            rep_bc11_comp.all_window_identities_exact && rep_bc11_comp.all_injection_bounds_valid
        );
        assert_eq!(rep_bc11_comp.actual_third_hemisphere_pos_count, 83);
        assert_eq!(rep_bc11_comp.trunc_sidon_quad_certified_count, 56);
        assert_eq!(rep_bc11_comp.windowed_sidon_quad_certified_count, 59);

        // 3. Verify continuum Slot-Eviction Polynomial Bound c_3^evict = 4375 / 12384
        let (c_ev3, b_ev3, c_base3, b_base3) = slot_eviction_continuum_bound(3);
        assert!((c_ev3 - 4375.0 / 12384.0).abs() < 1e-15);
        assert!((c_base3 - 1.0 / 3.0).abs() < 1e-15);
        assert!((b_ev3 - 1.414_580_375_002_984).abs() < 1e-12);
        assert!(c_ev3 > c_base3 && b_ev3 < b_base3);

        for &p in &[5usize, 7] {
            let (c_ev, b_ev, c_base, b_base) = slot_eviction_continuum_bound(p);
            assert!(c_ev > c_base && b_ev < b_base);
        }
    }

    #[test]
    fn test_theorems_2_13_2_14_and_corollary_2_15_diophantine_haar_closure() {
        // 1. Verify Theorems 2.13 & 2.14(a)-(b) across OEIS A004023, optimal B_3 rulers, and Bose-Chowla sets
        for &r_max in &[6u32, 10, 14, 16] {
            let rep = eval_b3_diophantine_haar_closure(&OEIS_A004023_FIRST_30, r_max, 8);
            assert!(rep.all_vandermonde_and_kkt_exact);
            assert!(rep.all_cross_shell_localized);
            assert!(rep.all_legendre_fenchel_valid);
            assert!(rep.all_binary_splits_exact);
            assert!(rep.total_actual_subblock_excess >= rep.total_lf_sawtooth_excess - 1e-11);
        }
        for rec in OPTIMAL_B3_RULERS.iter().skip(2) {
            let r_max = (rec.min_n.ilog2() + 1).max(2);
            let rep = eval_b3_diophantine_haar_closure(rec.witness, r_max, 16);
            assert!(rep.all_vandermonde_and_kkt_exact);
            assert!(rep.all_cross_shell_localized);
            assert!(rep.all_legendre_fenchel_valid);
            assert!(rep.all_binary_splits_exact);
            assert!(rep.total_actual_subblock_excess >= rep.total_lf_sawtooth_excess - 1e-11);
        }
        for &p in &[5u32, 7, 11] {
            let bc = construct_bose_chowla_b3(p);
            let r_max = (bc.compressed_span_n.ilog2() + 1).max(2);
            let rep = eval_b3_diophantine_haar_closure(&bc.compressed_set, r_max, 16);
            assert!(rep.all_vandermonde_and_kkt_exact);
            assert!(rep.all_cross_shell_localized);
            assert!(rep.all_legendre_fenchel_valid);
            assert!(rep.all_binary_splits_exact);
            assert!(rep.total_actual_subblock_excess >= rep.total_lf_sawtooth_excess - 1e-11);
        }

        // 2. Verify Theorem 2.14(c) hyperfactorial sawtooth antiderivative F_Haar(M) == \sum_{m=0}^{M-1} I_m
        let mut sum_im = 0.0_f64;
        for m in 0..32u64 {
            let f_m = exact_haar_sawtooth_antideriv(m as f64);
            assert!((f_m - sum_im).abs() < 1e-12, "Mismatch at M = {m}");
            sum_im += sawtooth_period_integral(m);
        }
        for &m in &[16u64, 64, 256, 1024] {
            let f_exact = exact_haar_sawtooth_antideriv(m as f64);
            let mf = m as f64;
            let f_asymp = (1.0 / 6.0) * mf.ln() + GLAISHER_KINKELIN_C_GK + 1.0 / (360.0 * mf * mf);
            assert!((f_exact - f_asymp).abs() < 1e-8);
        }

        // 3. Verify logarithmic Haar integral F_Haar(2^K) >= (K \ln 2) / 6 + C_GK and I_K(2^K) == F_Haar(2^K) - 1/2
        for &k_oct in &[1u32, 4, 8, 16, 32] {
            let mu_1 = 2.0_f64.powi(k_oct as i32);
            let f_full = exact_haar_sawtooth_antideriv(mu_1);
            let i_k = diophantine_haar_integral(mu_1, k_oct);
            let lb = (k_oct as f64) * 2.0_f64.ln() / 6.0 + GLAISHER_KINKELIN_C_GK;
            assert!(f_full >= lb - 1e-12);
            assert!((i_k - (f_full - 0.5)).abs() < 1e-12);
        }

        // 4. Verify Corollary 2.15 unconditional Diophantine Haar density curve c_{\infty,3}^{*,Dio}(K) -> 0
        let (k0, b0, _, _) = b3_diophantine_haar_boost_and_bound(0);
        let (k4, b4, _, bgk4) = b3_diophantine_haar_boost_and_bound(4);
        let (k8, b8, _, bgk8) = b3_diophantine_haar_boost_and_bound(8);
        let (k16, b16, _, bgk16) = b3_diophantine_haar_boost_and_bound(16);
        let (k32, b32, _, bgk32) = b3_diophantine_haar_boost_and_bound(32);
        let (k64, b64, _, bgk64) = b3_diophantine_haar_boost_and_bound(64);
        let (_, b1024, _, _) = b3_diophantine_haar_boost_and_bound(1024);

        assert_eq!(k0, 0.0);
        assert!((b0 - 1.199_855_964_3).abs() < 1e-8);
        assert!(k4 > 0.0 && k8 > k4 && k16 > k8 && k32 > k16 && k64 > k32);
        assert!(b0 > b4 && b4 > b8 && b8 > b16 && b16 > b32 && b32 > b64 && b64 > b1024);
        // Sub-Bose-Chowla threshold (< 1.00) broken at K = 4; < 0.85 broken at K = 8; < 0.59 at K = 32 (GK); < 0.50 at K = 64
        assert!((b4 - 0.964_066_326_1).abs() < 1e-8 && b4 < 1.0);
        assert!((b8 - 0.846_436_542_0).abs() < 1e-8 && b8 < 0.85);
        assert!((b16 - 0.716_465_950_4).abs() < 1e-8);
        assert!((b32 - 0.590_400_718_1).abs() < 1e-8);
        assert!((bgk32 - 0.568_759_971_1).abs() < 1e-8 && bgk32 < 0.59);
        assert!((b64 - 0.478_293_665_6).abs() < 1e-8 && b64 < 0.50);
        assert!(bgk4 < b4 && bgk8 < b8 && bgk16 < b16 && bgk64 < b64);
        assert!(b1024 < 0.20);

        // 5. Verify odd-Bp Diophantine Haar closure (p = 5, 7)
        let (_, b5_0, bp5_0) = odd_bp_diophantine_haar_bound(5, 0, 16);
        let (_, b5_128, bp5_128) = odd_bp_diophantine_haar_bound(5, 128, 16);
        assert!(b5_128 < 1.0 && bp5_128 < 1.0 && b5_128 < b5_0 && bp5_128 < bp5_0);
    }

    #[test]
    #[ignore = "requires CUDA GPU"]
    fn test_gpu_cpu_bit_exact_parity() {
        let gpu = Gpu::init(0, "compute_80").expect("Failed to init CUDA GPU");

        // 1. Verify bit-for-bit parity of k_dfs_b3_ruler vs extend_b3_dfs_cpu at N = 30
        let n_max = 30u32;
        let split_x = 7u32;
        let req_prefix = vec![0u8; (n_max + 1) as usize];
        let b3_cap = build_subadditive_b3_cap_table(n_max as usize);
        let prefixes = enumerate_b3_prefixes(split_x, &req_prefix);

        let cpu_out = solve_b3_prefixes_cpu(&prefixes, n_max, split_x, &req_prefix, &b3_cap);
        let gpu_out =
            solve_b3_prefixes_gpu(&gpu, &prefixes, n_max, split_x, &req_prefix, &b3_cap).unwrap();

        assert_eq!(cpu_out.len(), gpu_out.len());
        for (i, (c, g)) in cpu_out.iter().zip(gpu_out.iter()).enumerate() {
            assert_eq!(c.max_len, g.max_len, "max_len mismatch at prefix {i}");
            assert_eq!(c.best_m1, g.best_m1, "best_m1 mismatch at prefix {i}");
            assert_eq!(
                c.nodes_visited, g.nodes_visited,
                "nodes_visited mismatch at prefix {i}"
            );
        }

        // 2. Verify k_eval_b3_conservation on GPU vs CPU
        let bc7 = construct_bose_chowla_b3(7);
        let max_m = 16usize;
        let mut h_sets = vec![0u32; 2 * max_m];
        for (idx, &v) in OEIS_A004023_FIRST_30[..12].iter().enumerate() {
            h_sets[idx] = v;
        }
        for (idx, &v) in bc7.compressed_set.iter().enumerate() {
            h_sets[max_m + idx] = v;
        }
        let h_lengths = vec![12u32, bc7.compressed_set.len() as u32];
        let d_sets = gpu.stream.clone_htod(&h_sets).unwrap();
        let d_lengths = gpu.stream.clone_htod(&h_lengths).unwrap();
        let mut d_energy = gpu.stream.alloc_zeros::<f64>(2).unwrap();
        let mut d_defect = gpu.stream.alloc_zeros::<f64>(2).unwrap();
        let mut d_budget = gpu.stream.alloc_zeros::<f64>(2).unwrap();
        let mut d_is_b3 = gpu.stream.alloc_zeros::<u32>(2).unwrap();

        let n_sets_u32 = 2u32;
        let max_m_u32 = max_m as u32;
        let horizon_n = 2000u32;
        let cfg = gpu.launch_cfg(n_sets_u32);
        unsafe {
            gpu.stream
                .launch_builder(&gpu.fn_eval_b3_conservation)
                .arg(&d_sets)
                .arg(&d_lengths)
                .arg(&n_sets_u32)
                .arg(&max_m_u32)
                .arg(&horizon_n)
                .arg(&mut d_energy)
                .arg(&mut d_defect)
                .arg(&mut d_budget)
                .arg(&mut d_is_b3)
                .launch(cfg)
                .unwrap();
        }
        let g_energy = gpu.stream.clone_dtoh(&d_energy).unwrap();
        let g_defect = gpu.stream.clone_dtoh(&d_defect).unwrap();
        let g_budget = gpu.stream.clone_dtoh(&d_budget).unwrap();
        let g_is_b3 = gpu.stream.clone_dtoh(&d_is_b3).unwrap();

        let rep0 = evaluate_b3_conservation(&OEIS_A004023_FIRST_30[..12], horizon_n, 1);
        let rep1 = evaluate_b3_conservation(&bc7.compressed_set, horizon_n, 1);

        assert_eq!(g_is_b3, vec![1, 1]);
        assert!((g_energy[0] - rep0.discrete_energy).abs() < 1e-12);
        assert!((g_defect[0] - rep0.asymmetric_defect).abs() < 1e-12);
        assert!((g_budget[0] - rep0.harmonic_budget).abs() < 1e-12);
        assert!((g_energy[1] - rep1.discrete_energy).abs() < 1e-12);
        assert!((g_defect[1] - rep1.asymmetric_defect).abs() < 1e-12);
        assert!((g_budget[1] - rep1.harmonic_budget).abs() < 1e-12);

        // 3. Verify k_eval_b3_sign_cones on GPU vs CPU (Theorem 2.3)
        let mut d_pos_e = gpu.stream.alloc_zeros::<f64>(2).unwrap();
        let mut d_pos_d = gpu.stream.alloc_zeros::<f64>(2).unwrap();
        let mut d_pos_b = gpu.stream.alloc_zeros::<f64>(2).unwrap();
        let mut d_neg_e = gpu.stream.alloc_zeros::<f64>(2).unwrap();
        let mut d_neg_d = gpu.stream.alloc_zeros::<f64>(2).unwrap();
        let mut d_neg_b = gpu.stream.alloc_zeros::<f64>(2).unwrap();
        let mut d_pos_c = gpu.stream.alloc_zeros::<u32>(2).unwrap();
        let mut d_zero_c = gpu.stream.alloc_zeros::<u32>(2).unwrap();
        let mut d_neg_c = gpu.stream.alloc_zeros::<u32>(2).unwrap();

        unsafe {
            gpu.stream
                .launch_builder(&gpu.fn_eval_b3_sign_cones)
                .arg(&d_sets)
                .arg(&d_lengths)
                .arg(&n_sets_u32)
                .arg(&max_m_u32)
                .arg(&horizon_n)
                .arg(&mut d_pos_e)
                .arg(&mut d_pos_d)
                .arg(&mut d_pos_b)
                .arg(&mut d_neg_e)
                .arg(&mut d_neg_d)
                .arg(&mut d_neg_b)
                .arg(&mut d_pos_c)
                .arg(&mut d_zero_c)
                .arg(&mut d_neg_c)
                .launch(cfg)
                .unwrap();
        }
        let g_pos_b = gpu.stream.clone_dtoh(&d_pos_b).unwrap();
        let g_neg_b = gpu.stream.clone_dtoh(&d_neg_b).unwrap();
        let g_pos_c = gpu.stream.clone_dtoh(&d_pos_c).unwrap();
        let g_zero_c = gpu.stream.clone_dtoh(&d_zero_c).unwrap();
        let g_neg_c = gpu.stream.clone_dtoh(&d_neg_c).unwrap();

        let cone0 = evaluate_sign_split_cones(&OEIS_A004023_FIRST_30[..12], horizon_n);
        let cone1 = evaluate_sign_split_cones(&bc7.compressed_set, horizon_n);
        assert_eq!(g_pos_c[0] as usize, cone0.pos_count);
        assert_eq!(g_zero_c[0] as usize, cone0.zero_count);
        assert_eq!(g_neg_c[0] as usize, cone0.neg_count);
        assert!((g_pos_b[0] - cone0.pos_budget).abs() < 1e-12);
        assert!((g_neg_b[0] - cone0.neg_budget).abs() < 1e-12);
        assert!((g_pos_b[1] - cone1.pos_budget).abs() < 1e-12);
        assert!((g_neg_b[1] - cone1.neg_budget).abs() < 1e-12);

        // 4. Verify k_eval_b3_full_cube on GPU vs CPU (Theorem 2.5 & Theorem 2.6)
        let mut d_tot_t = gpu.stream.alloc_zeros::<u32>(2).unwrap();
        let mut d_one_t = gpu.stream.alloc_zeros::<u32>(2).unwrap();
        let mut d_mean_w = gpu.stream.alloc_zeros::<f64>(2).unwrap();
        let mut d_var_w = gpu.stream.alloc_zeros::<f64>(2).unwrap();
        let mut d_th_var_w = gpu.stream.alloc_zeros::<f64>(2).unwrap();
        let mut d_one_b = gpu.stream.alloc_zeros::<f64>(2).unwrap();

        unsafe {
            gpu.stream
                .launch_builder(&gpu.fn_eval_b3_full_cube)
                .arg(&d_sets)
                .arg(&d_lengths)
                .arg(&n_sets_u32)
                .arg(&max_m_u32)
                .arg(&mut d_tot_t)
                .arg(&mut d_one_t)
                .arg(&mut d_mean_w)
                .arg(&mut d_var_w)
                .arg(&mut d_th_var_w)
                .arg(&mut d_one_b)
                .launch(cfg)
                .unwrap();
        }
        let g_tot_t = gpu.stream.clone_dtoh(&d_tot_t).unwrap();
        let g_one_t = gpu.stream.clone_dtoh(&d_one_t).unwrap();
        let g_mean_w = gpu.stream.clone_dtoh(&d_mean_w).unwrap();
        let g_var_w = gpu.stream.clone_dtoh(&d_var_w).unwrap();
        let g_th_var_w = gpu.stream.clone_dtoh(&d_th_var_w).unwrap();
        let g_one_b = gpu.stream.clone_dtoh(&d_one_b).unwrap();

        let fc0 = eval_full_cube_variance_identity(&OEIS_A004023_FIRST_30[..12]);
        let fc1 = eval_full_cube_variance_identity(&bc7.compressed_set);
        assert_eq!(g_tot_t[0] as usize, fc0.total_triples_tm);
        assert_eq!(g_one_t[0] as usize, fc0.one_sided_pos_triples);
        assert!((g_mean_w[0] - fc0.mean_w).abs() < 1e-12);
        assert!((g_var_w[0] - fc0.empirical_var_w).abs() < 1e-8);
        assert!((g_th_var_w[0] - fc0.theoretical_var_w).abs() < 1e-8);
        assert!((g_one_b[0] - fc0.one_sided_budget).abs() < 1e-12);
        assert_eq!(g_tot_t[1] as usize, fc1.total_triples_tm);
        assert_eq!(g_one_t[1] as usize, fc1.one_sided_pos_triples);
        assert!((g_var_w[1] - fc1.theoretical_var_w).abs() < 1e-8);
        assert!((g_one_b[1] - fc1.one_sided_budget).abs() < 1e-12);

        // 5. Verify k_eval_sublevel_subcone_weights on GPU vs CPU (Theorem 2.7)
        let tau_num = 1u64;
        let tau_den = 2u64;
        let mut d_full_t = gpu.stream.alloc_zeros::<u32>(2).unwrap();
        let mut d_full_sum = gpu.stream.alloc_zeros::<i64>(2).unwrap();
        let mut d_full_rhs = gpu.stream.alloc_zeros::<i64>(2).unwrap();
        let mut d_sub_t = gpu.stream.alloc_zeros::<u32>(2).unwrap();
        let mut d_sub_sum = gpu.stream.alloc_zeros::<i64>(2).unwrap();
        let mut d_sub_ref = gpu.stream.alloc_zeros::<i64>(2).unwrap();
        let mut d_weights = gpu.stream.alloc_zeros::<i64>(2 * max_m).unwrap();
        let mut d_min_w = gpu.stream.alloc_zeros::<i64>(2).unwrap();

        unsafe {
            gpu.stream
                .launch_builder(&gpu.fn_eval_sublevel_subcone_weights)
                .arg(&d_sets)
                .arg(&d_lengths)
                .arg(&n_sets_u32)
                .arg(&max_m_u32)
                .arg(&tau_num)
                .arg(&tau_den)
                .arg(&mut d_full_t)
                .arg(&mut d_full_sum)
                .arg(&mut d_full_rhs)
                .arg(&mut d_sub_t)
                .arg(&mut d_sub_sum)
                .arg(&mut d_sub_ref)
                .arg(&mut d_weights)
                .arg(&mut d_min_w)
                .launch(cfg)
                .unwrap();
        }
        let g_full_t = gpu.stream.clone_dtoh(&d_full_t).unwrap();
        let g_full_sum = gpu.stream.clone_dtoh(&d_full_sum).unwrap();
        let g_full_rhs = gpu.stream.clone_dtoh(&d_full_rhs).unwrap();
        let g_sub_t = gpu.stream.clone_dtoh(&d_sub_t).unwrap();
        let g_sub_sum = gpu.stream.clone_dtoh(&d_sub_sum).unwrap();
        let g_sub_ref = gpu.stream.clone_dtoh(&d_sub_ref).unwrap();
        let g_weights = gpu.stream.clone_dtoh(&d_weights).unwrap();
        let g_min_w = gpu.stream.clone_dtoh(&d_min_w).unwrap();

        let sc0 = eval_sublevel_subcone_identity(&OEIS_A004023_FIRST_30[..12], tau_num, tau_den);
        let sc1 = eval_sublevel_subcone_identity(&bc7.compressed_set, tau_num, tau_den);

        assert_eq!(g_full_t[0] as usize, sc0.full_cone_triple_count);
        assert_eq!(g_full_sum[0], sc0.full_cone_triple_sum);
        assert_eq!(g_full_rhs[0], sc0.full_cone_poly_rhs);
        assert_eq!(g_sub_t[0] as usize, sc0.sublevel_triple_count);
        assert_eq!(g_sub_sum[0], sc0.sublevel_triple_sum);
        assert_eq!(g_sub_ref[0], sc0.sublevel_cubic_ref_sum);
        assert_eq!(g_min_w[0], sc0.min_discrete_weight);
        assert_eq!(&g_weights[0..12], &sc0.discrete_weights[..]);

        assert_eq!(g_full_t[1] as usize, sc1.full_cone_triple_count);
        assert_eq!(g_full_sum[1], sc1.full_cone_triple_sum);
        assert_eq!(g_full_rhs[1], sc1.full_cone_poly_rhs);
        assert_eq!(g_sub_t[1] as usize, sc1.sublevel_triple_count);
        assert_eq!(g_sub_sum[1], sc1.sublevel_triple_sum);
        assert_eq!(g_sub_ref[1], sc1.sublevel_cubic_ref_sum);
        assert_eq!(g_min_w[1], sc1.min_discrete_weight);
        assert_eq!(
            &g_weights[max_m..(max_m + bc7.compressed_set.len())],
            &sc1.discrete_weights[..]
        );

        // 6. Verify k_eval_bp_projective_fermat on GPU vs CPU (Theorem 2.8)
        let n_grid_p5 = 24u32;
        let n_laurent = 10u32;
        let mut d_slice_ord = gpu.stream.alloc_zeros::<f64>(n_grid_p5 as usize).unwrap();
        let mut d_slice_prod = gpu.stream.alloc_zeros::<f64>(n_grid_p5 as usize).unwrap();
        let mut d_alpha = gpu.stream.alloc_zeros::<f64>(n_laurent as usize).unwrap();
        let mut d_beta = gpu.stream.alloc_zeros::<f64>(n_laurent as usize).unwrap();

        let cfg_p5 = gpu.launch_cfg(n_grid_p5);
        unsafe {
            gpu.stream
                .launch_builder(&gpu.fn_eval_bp_projective_fermat)
                .arg(&n_grid_p5)
                .arg(&n_laurent)
                .arg(&mut d_slice_ord)
                .arg(&mut d_slice_prod)
                .arg(&mut d_alpha)
                .arg(&mut d_beta)
                .launch(cfg_p5)
                .unwrap();
        }
        let g_slice_ord = gpu.stream.clone_dtoh(&d_slice_ord).unwrap();
        let g_slice_prod = gpu.stream.clone_dtoh(&d_slice_prod).unwrap();
        let g_alpha = gpu.stream.clone_dtoh(&d_alpha).unwrap();
        let g_beta = gpu.stream.clone_dtoh(&d_beta).unwrap();

        for idx in 0..(n_laurent as usize) {
            let (c_alpha, c_beta) = sublevel_laurent_alpha_beta(idx + 1);
            assert!((g_alpha[idx] - c_alpha).abs() < 1e-15);
            assert!((g_beta[idx] - c_beta).abs() < 1e-15);
        }

        let g_vol_ord: f64 = g_slice_ord.iter().sum();
        let g_vol_prod: f64 = g_slice_prod.iter().sum();
        let (c_vol_ord, _, c_vol_prod, _) = odd_bp_sublevel_volume_and_bound(5, n_grid_p5 as usize);
        assert!((g_vol_ord - c_vol_ord).abs() < 1e-12);
        assert!((g_vol_prod - c_vol_prod).abs() < 1e-12);

        // 7. Verify k_eval_three_hemisphere_cone on GPU vs CPU (Theorem 2.9)
        let mut d_lo_cnt = gpu.stream.alloc_zeros::<u32>(2).unwrap();
        let mut d_mid_cnt = gpu.stream.alloc_zeros::<u32>(2).unwrap();
        let mut d_hi_pos_cnt = gpu.stream.alloc_zeros::<u32>(2).unwrap();
        let mut d_hi_nonpos = gpu.stream.alloc_zeros::<u32>(2).unwrap();
        let mut d_lo_sum = gpu.stream.alloc_zeros::<i64>(2).unwrap();
        let mut d_mid_sum = gpu.stream.alloc_zeros::<i64>(2).unwrap();
        let mut d_hi_pos_sum = gpu.stream.alloc_zeros::<i64>(2).unwrap();

        unsafe {
            gpu.stream
                .launch_builder(&gpu.fn_eval_three_hemisphere_cone)
                .arg(&d_sets)
                .arg(&d_lengths)
                .arg(&n_sets_u32)
                .arg(&max_m_u32)
                .arg(&mut d_lo_cnt)
                .arg(&mut d_mid_cnt)
                .arg(&mut d_hi_pos_cnt)
                .arg(&mut d_hi_nonpos)
                .arg(&mut d_lo_sum)
                .arg(&mut d_mid_sum)
                .arg(&mut d_hi_pos_sum)
                .launch(cfg)
                .unwrap();
        }
        let g_lo_cnt = gpu.stream.clone_dtoh(&d_lo_cnt).unwrap();
        let g_mid_cnt = gpu.stream.clone_dtoh(&d_mid_cnt).unwrap();
        let g_hi_pos_cnt = gpu.stream.clone_dtoh(&d_hi_pos_cnt).unwrap();
        let g_hi_nonpos = gpu.stream.clone_dtoh(&d_hi_nonpos).unwrap();
        let g_lo_sum = gpu.stream.clone_dtoh(&d_lo_sum).unwrap();
        let g_mid_sum = gpu.stream.clone_dtoh(&d_mid_sum).unwrap();
        let g_hi_pos_sum = gpu.stream.clone_dtoh(&d_hi_pos_sum).unwrap();

        let th0 = eval_three_hemisphere_partition(&OEIS_A004023_FIRST_30[..12]);
        let th1 = eval_three_hemisphere_partition(&bc7.compressed_set);

        assert_eq!(g_lo_cnt[0] as usize, th0.lo_count);
        assert_eq!(g_mid_cnt[0] as usize, th0.mid_count);
        assert_eq!(g_hi_pos_cnt[0] as usize, th0.hi_pos_count);
        assert_eq!(g_hi_nonpos[0] as usize, th0.hi_nonpos_count);
        assert_eq!(g_lo_sum[0], th0.lo_sum);
        assert_eq!(g_mid_sum[0], th0.mid_sum);
        assert_eq!(g_hi_pos_sum[0], th0.hi_pos_sum);

        assert_eq!(g_lo_cnt[1] as usize, th1.lo_count);
        assert_eq!(g_mid_cnt[1] as usize, th1.mid_count);
        assert_eq!(g_hi_pos_cnt[1] as usize, th1.hi_pos_count);
        assert_eq!(g_hi_nonpos[1] as usize, th1.hi_nonpos_count);
        assert_eq!(g_lo_sum[1], th1.lo_sum);
        assert_eq!(g_mid_sum[1], th1.mid_sum);
        assert_eq!(g_hi_pos_sum[1], th1.hi_pos_sum);

        // 8. Verify k_eval_telescoping_third_hemisphere on GPU vs CPU (Theorem 2.10)
        let mut d_all_exact = gpu.stream.alloc_zeros::<u32>(2).unwrap();
        let mut d_step1_sum = gpu.stream.alloc_zeros::<i64>(2).unwrap();
        let mut d_step1_rhs = gpu.stream.alloc_zeros::<i64>(2).unwrap();
        let mut d_step1_pos = gpu.stream.alloc_zeros::<u32>(2).unwrap();
        let mut d_upper_sum = gpu.stream.alloc_zeros::<i64>(2).unwrap();
        let mut d_upper_rhs = gpu.stream.alloc_zeros::<i64>(2).unwrap();
        let mut d_r3_ord = gpu.stream.alloc_zeros::<f64>(n_grid_p5 as usize).unwrap();
        let mut d_r3_prod = gpu.stream.alloc_zeros::<f64>(n_grid_p5 as usize).unwrap();

        unsafe {
            gpu.stream
                .launch_builder(&gpu.fn_eval_telescoping_third_hemisphere)
                .arg(&d_sets)
                .arg(&d_lengths)
                .arg(&n_sets_u32)
                .arg(&max_m_u32)
                .arg(&n_grid_p5)
                .arg(&mut d_all_exact)
                .arg(&mut d_step1_sum)
                .arg(&mut d_step1_rhs)
                .arg(&mut d_step1_pos)
                .arg(&mut d_upper_sum)
                .arg(&mut d_upper_rhs)
                .arg(&mut d_r3_ord)
                .arg(&mut d_r3_prod)
                .launch(cfg_p5)
                .unwrap();
        }
        let g_all_exact = gpu.stream.clone_dtoh(&d_all_exact).unwrap();
        let g_step1_sum = gpu.stream.clone_dtoh(&d_step1_sum).unwrap();
        let g_step1_rhs = gpu.stream.clone_dtoh(&d_step1_rhs).unwrap();
        let g_step1_pos = gpu.stream.clone_dtoh(&d_step1_pos).unwrap();
        let g_upper_sum = gpu.stream.clone_dtoh(&d_upper_sum).unwrap();
        let g_upper_rhs = gpu.stream.clone_dtoh(&d_upper_rhs).unwrap();
        let g_r3_ord = gpu.stream.clone_dtoh(&d_r3_ord).unwrap();
        let g_r3_prod = gpu.stream.clone_dtoh(&d_r3_prod).unwrap();

        let tel0 = eval_telescoping_third_hemisphere(&OEIS_A004023_FIRST_30[..12]);
        let tel1 = eval_telescoping_third_hemisphere(&bc7.compressed_set);

        assert_eq!(g_all_exact, vec![1, 1]);
        assert_eq!(g_step1_sum[0], tel0.step1_telescoping_sum);
        assert_eq!(g_step1_rhs[0], tel0.step1_telescoping_rhs);
        assert_eq!(g_step1_pos[0] as usize, tel0.step1_pos_count);
        assert_eq!(g_upper_sum[0], tel0.upper_cone_sum);
        assert_eq!(g_upper_rhs[0], tel0.upper_poly_rhs);

        assert_eq!(g_step1_sum[1], tel1.step1_telescoping_sum);
        assert_eq!(g_step1_rhs[1], tel1.step1_telescoping_rhs);
        assert_eq!(g_step1_pos[1] as usize, tel1.step1_pos_count);
        assert_eq!(g_upper_sum[1], tel1.upper_cone_sum);
        assert_eq!(g_upper_rhs[1], tel1.upper_poly_rhs);

        let g_r3_vol_ord: f64 = g_r3_ord.iter().sum();
        let g_r3_vol_prod: f64 = g_r3_prod.iter().sum();
        let (c_r3_ord, _, _, c_r3_prod, _, _) =
            odd_bp_fermat_majorized_volume_and_bound(5, n_grid_p5 as usize);
        assert!((g_r3_vol_ord - c_r3_ord).abs() < 1e-12);
        assert!((g_r3_vol_prod - c_r3_prod).abs() < 1e-12);

        // 9. Verify k_eval_horizon_truncated_rays on GPU vs CPU (Theorem 2.11)
        let n_grid_u = 128u32;
        let mut d_ht_ok = gpu.stream.alloc_zeros::<u32>(2).unwrap();
        let mut d_ht_act_pos = gpu.stream.alloc_zeros::<u32>(2).unwrap();
        let mut d_ht_um = gpu.stream.alloc_zeros::<u32>(2).unwrap();
        let mut d_ht_ug = gpu.stream.alloc_zeros::<u32>(2).unwrap();
        let mut d_ht_tm = gpu.stream.alloc_zeros::<u32>(2).unwrap();
        let mut d_ht_tg = gpu.stream.alloc_zeros::<u32>(2).unwrap();
        let mut d_ht_urays = gpu.stream.alloc_zeros::<u32>(2).unwrap();
        let mut d_ht_trays = gpu.stream.alloc_zeros::<u32>(2).unwrap();
        let mut d_u_slice_p3 = gpu.stream.alloc_zeros::<f64>(n_grid_u as usize).unwrap();
        let mut d_u_slice_p5 = gpu.stream.alloc_zeros::<f64>(n_grid_u as usize).unwrap();

        let cfg_ht = gpu.launch_cfg(n_grid_u);
        unsafe {
            gpu.stream
                .launch_builder(&gpu.fn_eval_horizon_truncated_rays)
                .arg(&d_sets)
                .arg(&d_lengths)
                .arg(&n_sets_u32)
                .arg(&max_m_u32)
                .arg(&n_grid_u)
                .arg(&mut d_ht_ok)
                .arg(&mut d_ht_act_pos)
                .arg(&mut d_ht_um)
                .arg(&mut d_ht_ug)
                .arg(&mut d_ht_tm)
                .arg(&mut d_ht_tg)
                .arg(&mut d_ht_urays)
                .arg(&mut d_ht_trays)
                .arg(&mut d_u_slice_p3)
                .arg(&mut d_u_slice_p5)
                .launch(cfg_ht)
                .unwrap();
        }
        let g_ht_ok = gpu.stream.clone_dtoh(&d_ht_ok).unwrap();
        let g_ht_act_pos = gpu.stream.clone_dtoh(&d_ht_act_pos).unwrap();
        let g_ht_um = gpu.stream.clone_dtoh(&d_ht_um).unwrap();
        let g_ht_ug = gpu.stream.clone_dtoh(&d_ht_ug).unwrap();
        let g_ht_tm = gpu.stream.clone_dtoh(&d_ht_tm).unwrap();
        let g_ht_tg = gpu.stream.clone_dtoh(&d_ht_tg).unwrap();
        let g_ht_urays = gpu.stream.clone_dtoh(&d_ht_urays).unwrap();
        let g_ht_trays = gpu.stream.clone_dtoh(&d_ht_trays).unwrap();
        let g_u_slice_p3 = gpu.stream.clone_dtoh(&d_u_slice_p3).unwrap();
        let g_u_slice_p5 = gpu.stream.clone_dtoh(&d_u_slice_p5).unwrap();

        let ht0 = eval_horizon_truncated_rays(&OEIS_A004023_FIRST_30[..12]);
        let ht1 = eval_horizon_truncated_rays(&bc7.compressed_set);

        assert_eq!(g_ht_ok, vec![1, 1]);
        assert_eq!(
            g_ht_act_pos[0] as usize,
            ht0.actual_third_hemisphere_pos_count
        );
        assert_eq!(g_ht_um[0] as usize, ht0.untruncated_markov_certified_count);
        assert_eq!(g_ht_ug[0] as usize, ht0.untruncated_mingap_certified_count);
        assert_eq!(g_ht_tm[0] as usize, ht0.truncated_markov_certified_count);
        assert_eq!(g_ht_tg[0] as usize, ht0.truncated_mingap_certified_count);
        assert_eq!(g_ht_urays[0] as usize, ht0.untruncated_active_rays);
        assert_eq!(g_ht_trays[0] as usize, ht0.truncated_active_rays);

        assert_eq!(
            g_ht_act_pos[1] as usize,
            ht1.actual_third_hemisphere_pos_count
        );
        assert_eq!(g_ht_um[1] as usize, ht1.untruncated_markov_certified_count);
        assert_eq!(g_ht_ug[1] as usize, ht1.untruncated_mingap_certified_count);
        assert_eq!(g_ht_tm[1] as usize, ht1.truncated_markov_certified_count);
        assert_eq!(g_ht_tg[1] as usize, ht1.truncated_mingap_certified_count);
        assert_eq!(g_ht_urays[1] as usize, ht1.untruncated_active_rays);
        assert_eq!(g_ht_trays[1] as usize, ht1.truncated_active_rays);

        let g_int_p3: f64 = g_u_slice_p3.iter().sum();
        let g_int_p5: f64 = g_u_slice_p5.iter().sum();
        let (_, _, c_int_p3, _) = horizon_truncated_continuum_integrals(3, n_grid_u as usize);
        let (_, _, c_int_p5, _) = horizon_truncated_continuum_integrals(5, n_grid_u as usize);
        assert!((g_int_p3 - c_int_p3).abs() < 1e-12);
        assert!((g_int_p5 - c_int_p5).abs() < 1e-12);

        // 10. Verify k_eval_quadratic_injection_rays on GPU vs CPU (Theorem 2.12)
        let mut d_qi_ok = gpu.stream.alloc_zeros::<u32>(2).unwrap();
        let mut d_qi_act = gpu.stream.alloc_zeros::<u32>(2).unwrap();
        let mut d_qi_tsid = gpu.stream.alloc_zeros::<u32>(2).unwrap();
        let mut d_qi_wsid = gpu.stream.alloc_zeros::<u32>(2).unwrap();
        let mut d_qi_trg = gpu.stream.alloc_zeros::<u32>(2).unwrap();
        let mut d_qi_sistar = gpu.stream.alloc_zeros::<i64>(2).unwrap();
        let mut d_qi_evcnt = gpu.stream.alloc_zeros::<u32>(2).unwrap();
        let mut d_qi_plhs = gpu.stream.alloc_zeros::<i64>(2).unwrap();
        let mut d_qi_brhs = gpu.stream.alloc_zeros::<i64>(2).unwrap();
        let mut d_qi_erhs = gpu.stream.alloc_zeros::<i64>(2).unwrap();

        unsafe {
            gpu.stream
                .launch_builder(&gpu.fn_eval_quadratic_injection_rays)
                .arg(&d_sets)
                .arg(&d_lengths)
                .arg(&n_sets_u32)
                .arg(&max_m_u32)
                .arg(&mut d_qi_ok)
                .arg(&mut d_qi_act)
                .arg(&mut d_qi_tsid)
                .arg(&mut d_qi_wsid)
                .arg(&mut d_qi_trg)
                .arg(&mut d_qi_sistar)
                .arg(&mut d_qi_evcnt)
                .arg(&mut d_qi_plhs)
                .arg(&mut d_qi_brhs)
                .arg(&mut d_qi_erhs)
                .launch(cfg)
                .unwrap();
        }
        let g_qi_ok = gpu.stream.clone_dtoh(&d_qi_ok).unwrap();
        let g_qi_act = gpu.stream.clone_dtoh(&d_qi_act).unwrap();
        let g_qi_tsid = gpu.stream.clone_dtoh(&d_qi_tsid).unwrap();
        let g_qi_wsid = gpu.stream.clone_dtoh(&d_qi_wsid).unwrap();
        let g_qi_trg = gpu.stream.clone_dtoh(&d_qi_trg).unwrap();
        let g_qi_sistar = gpu.stream.clone_dtoh(&d_qi_sistar).unwrap();
        let g_qi_evcnt = gpu.stream.clone_dtoh(&d_qi_evcnt).unwrap();
        let g_qi_plhs = gpu.stream.clone_dtoh(&d_qi_plhs).unwrap();
        let g_qi_brhs = gpu.stream.clone_dtoh(&d_qi_brhs).unwrap();
        let g_qi_erhs = gpu.stream.clone_dtoh(&d_qi_erhs).unwrap();

        let qi0 = eval_quadratic_injection_rays(&OEIS_A004023_FIRST_30[..12]);
        let qi1 = eval_quadratic_injection_rays(&bc7.compressed_set);

        assert_eq!(g_qi_ok, vec![1, 1]);
        assert_eq!(g_qi_act[0] as usize, qi0.actual_third_hemisphere_pos_count);
        assert_eq!(g_qi_tsid[0] as usize, qi0.trunc_sidon_quad_certified_count);
        assert_eq!(
            g_qi_wsid[0] as usize,
            qi0.windowed_sidon_quad_certified_count
        );
        assert_eq!(g_qi_trg[0] as usize, qi0.trunc_raygap_quad_certified_count);
        assert_eq!(g_qi_sistar[0], qi0.total_anchor_fiber_s_star);
        assert_eq!(g_qi_evcnt[0] as usize, qi0.slot_evict_certified_count);
        assert_eq!(g_qi_plhs[0], qi0.one_sided_poly_lhs);
        assert_eq!(g_qi_brhs[0], qi0.base_min_distinct_rhs);
        assert_eq!(g_qi_erhs[0], qi0.slot_evict_poly_rhs);

        assert_eq!(g_qi_act[1] as usize, qi1.actual_third_hemisphere_pos_count);
        assert_eq!(g_qi_tsid[1] as usize, qi1.trunc_sidon_quad_certified_count);
        assert_eq!(
            g_qi_wsid[1] as usize,
            qi1.windowed_sidon_quad_certified_count
        );
        assert_eq!(g_qi_trg[1] as usize, qi1.trunc_raygap_quad_certified_count);
        assert_eq!(g_qi_sistar[1], qi1.total_anchor_fiber_s_star);
        assert_eq!(g_qi_evcnt[1] as usize, qi1.slot_evict_certified_count);
        assert_eq!(g_qi_plhs[1], qi1.one_sided_poly_lhs);
        assert_eq!(g_qi_brhs[1], qi1.base_min_distinct_rhs);
        assert_eq!(g_qi_erhs[1], qi1.slot_evict_poly_rhs);

        // 11. Verify k_eval_b3_diophantine_haar_closure on GPU vs CPU (Theorems 2.13, 2.14 & Corollary 2.15)
        let r_max_dh = 11u32;
        let n_k_dh = 65u32;
        let (_, _, k_star_dh) = sublevel_subcone_volume_k_star_smooth();
        let mut d_dh_ok = gpu.stream.alloc_zeros::<u32>(2).unwrap();
        let mut d_dh_loc = gpu.stream.alloc_zeros::<u32>(2).unwrap();
        let mut d_dh_act_ex = gpu.stream.alloc_zeros::<f64>(2).unwrap();
        let mut d_dh_lf_ex = gpu.stream.alloc_zeros::<f64>(2).unwrap();
        let mut d_dh_diff_sq = gpu.stream.alloc_zeros::<u64>(2).unwrap();
        let mut d_dh_im = gpu.stream.alloc_zeros::<f64>(n_k_dh as usize).unwrap();
        let mut d_dh_kdio = gpu.stream.alloc_zeros::<f64>(n_k_dh as usize).unwrap();
        let mut d_dh_bdio = gpu.stream.alloc_zeros::<f64>(n_k_dh as usize).unwrap();
        let mut d_dh_bgk = gpu.stream.alloc_zeros::<f64>(n_k_dh as usize).unwrap();

        let cfg_dh = gpu.launch_cfg(n_k_dh);
        unsafe {
            gpu.stream
                .launch_builder(&gpu.fn_eval_b3_diophantine_haar_closure)
                .arg(&d_sets)
                .arg(&d_lengths)
                .arg(&n_sets_u32)
                .arg(&max_m_u32)
                .arg(&r_max_dh)
                .arg(&n_k_dh)
                .arg(&k_star_dh)
                .arg(&mut d_dh_ok)
                .arg(&mut d_dh_loc)
                .arg(&mut d_dh_act_ex)
                .arg(&mut d_dh_lf_ex)
                .arg(&mut d_dh_diff_sq)
                .arg(&mut d_dh_im)
                .arg(&mut d_dh_kdio)
                .arg(&mut d_dh_bdio)
                .arg(&mut d_dh_bgk)
                .launch(cfg_dh)
                .unwrap();
        }
        let g_dh_ok = gpu.stream.clone_dtoh(&d_dh_ok).unwrap();
        let g_dh_loc = gpu.stream.clone_dtoh(&d_dh_loc).unwrap();
        let g_dh_act_ex = gpu.stream.clone_dtoh(&d_dh_act_ex).unwrap();
        let g_dh_lf_ex = gpu.stream.clone_dtoh(&d_dh_lf_ex).unwrap();
        let g_dh_diff_sq = gpu.stream.clone_dtoh(&d_dh_diff_sq).unwrap();
        let g_dh_im = gpu.stream.clone_dtoh(&d_dh_im).unwrap();
        let g_dh_kdio = gpu.stream.clone_dtoh(&d_dh_kdio).unwrap();
        let g_dh_bdio = gpu.stream.clone_dtoh(&d_dh_bdio).unwrap();
        let g_dh_bgk = gpu.stream.clone_dtoh(&d_dh_bgk).unwrap();

        let dh0 = eval_b3_diophantine_haar_closure(&OEIS_A004023_FIRST_30[..12], r_max_dh, 16);
        let dh1 = eval_b3_diophantine_haar_closure(&bc7.compressed_set, r_max_dh, 16);

        assert_eq!(g_dh_ok, vec![1, 1]);
        assert_eq!(g_dh_loc[0] as usize, dh0.localized_cross_shell_triples);
        assert_eq!(g_dh_loc[1] as usize, dh1.localized_cross_shell_triples);
        assert!((g_dh_act_ex[0] - dh0.total_actual_subblock_excess).abs() < 1e-12);
        assert!((g_dh_lf_ex[0] - dh0.total_lf_sawtooth_excess).abs() < 1e-12);
        assert_eq!(g_dh_diff_sq[0], dh0.total_binary_split_diff_sq);
        assert!((g_dh_act_ex[1] - dh1.total_actual_subblock_excess).abs() < 1e-12);
        assert!((g_dh_lf_ex[1] - dh1.total_lf_sawtooth_excess).abs() < 1e-12);
        assert_eq!(g_dh_diff_sq[1], dh1.total_binary_split_diff_sq);

        for k_idx in 0..(n_k_dh as usize) {
            let im_cpu = sawtooth_period_integral(k_idx as u64);
            let (kd_cpu, bd_cpu, _, bgk_cpu) = b3_diophantine_haar_boost_and_bound(k_idx as u32);
            assert!((g_dh_im[k_idx] - im_cpu).abs() < 1e-14);
            assert!((g_dh_kdio[k_idx] - kd_cpu).abs() < 1e-12);
            assert!((g_dh_bdio[k_idx] - bd_cpu).abs() < 1e-12);
            assert!((g_dh_bgk[k_idx] - bgk_cpu).abs() < 1e-12);
        }
    }
}
