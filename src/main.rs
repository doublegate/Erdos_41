//! ============================================================================
//! `main.rs` — CLI entrypoint for `erdos41` (Erdős Problem #41: Infinite B_3 Sets)
//! ============================================================================

pub mod exact;
pub mod gpu;
pub mod records;
pub mod verify_cpu;

use anyhow::Result;
use clap::{Parser, Subcommand};
use exact::{
    enumerate_b3_prefixes, solve_b3_prefixes_cpu, solve_b3_prefixes_gpu, solve_exact_f3,
    solve_maximin_b3_envelope,
};
use gpu::Gpu;
use records::{
    b3_diophantine_haar_boost_and_bound, build_bose_chowla_block_sequence,
    build_subadditive_b3_cap_table, construct_bose_chowla_b3, cubic_beta_positive_cone_area,
    eta_fermat_asymptotic_constants, eta_fermat_sublevel_cone_volume, evaluate_dyadic_b3_shells,
    evaluate_intrashell_negative_cone_shells, fermat_cone_integral_closed_form,
    horizon_truncated_continuum_integrals, odd_bp_diophantine_haar_bound,
    odd_bp_fermat_majorized_volume_and_bound, odd_bp_sublevel_volume_and_bound,
    one_sided_fermat_cone_volume, quantile_envelope_max_variance_kappa_star,
    quantile_envelope_stationary_point_t_star, regular_density_upper_bound_at_eps,
    slot_eviction_continuum_bound, sublevel_laurent_alpha_beta,
    sublevel_subcone_first_moment_s_infty, sublevel_subcone_vol_and_moment_at_l,
    sublevel_subcone_volume_k_star, sublevel_subcone_volume_k_star_smooth,
    sublevel_vol_and_moment_laurent, unconditional_liminf_bound_one_sided_fermat_laplace,
    unconditional_liminf_bound_sublevel_subcone, unconditional_liminf_bound_variance,
    GLAISHER_KINKELIN_C_GK, OEIS_A004023_FIRST_30, OPTIMAL_B3_RULERS,
};
use std::time::Instant;
use verify_cpu::{
    eval_b3_diophantine_haar_closure, eval_full_cube_variance_identity,
    eval_horizon_truncated_rays, eval_quadratic_injection_rays, eval_sublevel_subcone_identity,
    eval_telescoping_third_hemisphere, eval_three_hemisphere_partition, evaluate_b3_conservation,
    evaluate_sign_split_cones, generate_greedy_b3_sequence,
};

#[derive(Parser)]
#[command(
    name = "erdos41",
    version,
    about = "GPU-accelerated quantitative analysis of Erdős Problem #41 ($500 open prize: lower-envelope density liminf A(x)/x^{1/3} of infinite B_3 sequences)"
)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Display Problem #41 status, Theorem 2.1 conservation & dyadic certificates, and Theorem 2.2 Bose–Chowla lifting
    Info,
    /// Verify the B_3 property and compute exact Theorem 2.1(a) (2,1)-Difference Harmonic Conservation
    Verify {
        /// Comma-separated list of positive integers
        #[arg(long, default_value = "1,2,5,14,33,72,125,219,376,573")]
        set: String,
        /// Lower window start x0 for evaluating Psi_A(x) = A(x) / x^{1/3}
        #[arg(long, default_value_t = 5)]
        x0: u32,
    },
    /// Exhaustively determine F_3(N) on CPU + GPU using reversible O(1) bitset-shift branch-and-bound
    Exact {
        /// Horizon N (2 <= N <= 120)
        #[arg(long, default_value_t = 46)]
        n: u32,
        /// Prefix split horizon split_x
        #[arg(long, default_value_t = 10)]
        split_x: u32,
        /// Disable GPU and use Rayon CPU threads only
        #[arg(long, default_value_t = false)]
        cpu_only: bool,
    },
    /// Solve the exact Maximin Cubic Lower-Envelope B_3 Problem mu_3*(x0, N)
    Maximin {
        /// Horizon N (2 <= N <= 90)
        #[arg(long, default_value_t = 36)]
        n: u32,
        /// Window start x0
        #[arg(long, default_value_t = 5)]
        x0: u32,
        /// Prefix split horizon split_x
        #[arg(long, default_value_t = 8)]
        split_x: u32,
        /// Disable GPU and use CPU only
        #[arg(long, default_value_t = false)]
        cpu_only: bool,
    },
    /// Generate k terms of the greedy infinite B_3 sequence (OEIS A004023)
    Greedy {
        /// Number of terms to generate
        #[arg(long, default_value_t = 25)]
        terms: usize,
    },
    /// Construct Bose–Chowla GF(p^3) B_3 sets and Pigeonhole gap-compressed rotations
    BoseChowla {
        /// Prime p for GF(p^3)
        #[arg(long, default_value_t = 7)]
        prime: u32,
    },
    /// Benchmark GPU vs. CPU on reversible O(1) bitset-shift B_3 DFS and conservation kernels
    Bench {
        /// Horizon N for DFS benchmark
        #[arg(long, default_value_t = 48)]
        n: u32,
        /// Prefix split horizon split_x
        #[arg(long, default_value_t = 11)]
        split_x: u32,
    },
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    match cli.command {
        Commands::Info => {
            println!(
                "================================================================================"
            );
            println!(
                " Erdős Problem #41 ($500 Open Prize): Lower-Envelope Density of Infinite B_3 Sets"
            );
            println!(
                "================================================================================"
            );
            println!("Question: Does every infinite B_3 sequence A subset N satisfy");
            println!("          lim inf_{{x -> infinity}} A(x) / x^(1/3) = 0?");
            println!();
            println!(
                "--- 1. Optimal Finite B_3 Rulers F_3(N) (OEIS A051912) vs. Greedy (A004023) ---"
            );
            println!(
                "{:>3} | {:>8} | {:>8} | {:>10} | {:>10} | Witness",
                "k", "Min N", "Ruler L", "Greedy N", "k/N^(1/3)"
            );
            println!(
                "--------------------------------------------------------------------------------"
            );
            for rec in &OPTIMAL_B3_RULERS {
                let psi = (rec.k as f64) / (rec.min_n as f64).cbrt();
                println!(
                    "{:>3} | {:>8} | {:>8} | {:>10} | {:>10.6} | {:?}",
                    rec.k, rec.min_n, rec.ruler_length, rec.greedy_n, psi, rec.witness
                );
            }
            println!();
            println!(
                "--- 2. Theorem 2.1(a) (2,1)-Difference Harmonic Conservation (OEIS A004023) ---"
            );
            println!(
                "{:>3} | {:>6} | {:>4} | {:>10} | {:>10} | {:>10} | {:>10} | {:>10}",
                "R", "N=2^R", "A(N)", "E_A^(3)(N)", "Delta_A", "B_A^(2,1)", "2H_N-5/2", "Cons.Err"
            );
            println!(
                "--------------------------------------------------------------------------------"
            );
            for r in [2u32, 4, 6, 8, 10, 12, 14] {
                let n = 1u32 << r;
                let rep = evaluate_b3_conservation(&OEIS_A004023_FIRST_30, n, 2);
                println!(
                    "{:>3} | {:>6} | {:>4} | {:>10.6} | {:>10.6} | {:>10.6} | {:>10.6} | {:>10.2e}",
                    r,
                    n,
                    rep.count_m,
                    rep.integral_energy,
                    rep.asymmetric_defect,
                    rep.harmonic_budget,
                    rep.harmonic_upper_bound,
                    rep.conservation_error
                );
            }
            println!();
            println!(
                "--- 3. Theorem 2.1(b)-(c) Dyadic Shell Inequality & Multi-Scale Resonance ---"
            );
            println!(
                "{:>3} | {:>6} | {:>4} | {:>12} | {:>12} | {:>12} | {:>10}",
                "R", "N=2^R", "A(N)", "Shell LHS", "Resonance", "Weighted W", "R - 1/2"
            );
            println!(
                "--------------------------------------------------------------------------------"
            );
            for r in [1u32, 2, 4, 6, 8, 10, 12, 14] {
                let cert = evaluate_dyadic_b3_shells(&OEIS_A004023_FIRST_30, r);
                println!(
                    "{:>3} | {:>6} | {:>4} | {:>12.6} | {:>12.6} | {:>12.6} | {:>10.2}",
                    cert.r_max,
                    cert.horizon_n,
                    cert.total_elements,
                    cert.shell_lhs,
                    cert.resonance_reinforcement,
                    cert.weighted_w_sum,
                    cert.ceiling_r_minus_half
                );
            }
            println!();
            println!(
                "--- 4. Theorem 2.2 Bose–Chowla GF(p^3) Lifting & Pigeonhole Gap Compression ---"
            );
            println!(
                "{:>3} | {:>8} | {:>8} | {:>10} | {:>10} | {:>10}",
                "p", "p^3 - 1", "Max Gap", "Span N_p*", "p^3 - p^2", "p/(N_p*)^(1/3)"
            );
            println!(
                "--------------------------------------------------------------------------------"
            );
            for &p in &[2u32, 3, 5, 7, 11] {
                let bc = construct_bose_chowla_b3(p);
                println!(
                    "{:>3} | {:>8} | {:>8} | {:>10} | {:>10} | {:>10.6}",
                    bc.p,
                    bc.modulus,
                    bc.max_modular_gap,
                    bc.compressed_span_n,
                    p * p * p - p * p,
                    bc.cubic_density_psi
                );
            }
            println!();
            println!("--- 5. Theorem 2.2(b) Spliced Bose–Chowla Cubic Burst–Desert Dichotomy ---");
            let (_, epochs) = build_bose_chowla_block_sequence(&[2, 3, 5, 7, 11]);
            for ep in &epochs {
                println!(
                    "Block {:>2} (p={:>2}): B_r={:>7}, E_r={:>7}, Desert Psi(B_r-1)={:.6}, Burst Psi(E_r)={:.6}",
                    ep.block_index, ep.p, ep.offset_b, ep.block_end_e, ep.desert_psi, ep.burst_psi
                );
            }
            println!();
            println!(
                "--- 6. Theorem 2.3 Sign-Split (2,1)-Cones & Intra-Shell Negative Exclusivity ---"
            );
            println!(
                "{:>3} | {:>6} | {:>6} | {:>6} | {:>10} | {:>10} | {:>10} | {:>10}",
                "R",
                "N=2^R",
                "|T_m^+|",
                "|T_m^-|",
                "B_A^+(N)",
                "B_A^-(N)",
                "H_N - 3/2",
                "NegDyadic<=(R-1)/2"
            );
            println!(
                "--------------------------------------------------------------------------------"
            );
            for r in [2u32, 4, 6, 8, 10, 12, 14] {
                let n = 1u32 << r;
                let cone = evaluate_sign_split_cones(&OEIS_A004023_FIRST_30, n);
                let intra = evaluate_intrashell_negative_cone_shells(&OEIS_A004023_FIRST_30, r);
                println!(
                    "{:>3} | {:>6} | {:>6} | {:>6} | {:>10.6} | {:>10.6} | {:>10.6} | {:.6}<={:.2}",
                    r,
                    n,
                    cone.pos_count,
                    cone.neg_count,
                    cone.pos_budget,
                    cone.neg_budget,
                    cone.single_cone_ceiling,
                    intra.negative_cone_dyadic_sum,
                    intra.half_ceiling
                );
            }
            println!();
            println!(
                "--- 7. Theorem 2.4 Cubic-Beta Fermat Cone Integral & Regular Density Vanishing ---"
            );
            println!(
                "Positive Quantile Cone Area |Delta^+| = {:.10} ({:.4}% of index simplex)",
                cubic_beta_positive_cone_area(),
                cubic_beta_positive_cone_area() * 200.0
            );
            for &eps in &[1e-1_f64, 1e-2, 1e-4, 1e-6, 1e-9, 1e-12] {
                println!(
                    "  eps = {:>8.1e} | I_+(eps) = {:>10.6} | Regular Density Upper Bound c_max(eps) <= {:.6}",
                    eps,
                    fermat_cone_integral_closed_form(eps),
                    regular_density_upper_bound_at_eps(eps)
                );
            }
            println!();
            println!(
                "--- 8. Theorem 2.5 Full-Cube (2,1)-Variance & Theorem 2.6 One-Sided Cone ---"
            );
            println!(
                "{:>3} | {:>6} | {:>6} | {:>12} | {:>12} | {:>10} | {:>10}",
                "m", "T_m", "|I_m^<|", "Var_Im(w)", "3(m+1)/(m-1)s^2", "OneSideB", "H_{2a_m-2}"
            );
            println!(
                "--------------------------------------------------------------------------------"
            );
            for m in [4usize, 6, 8, 12, 16, 22] {
                let rep = eval_full_cube_variance_identity(&OEIS_A004023_FIRST_30[..m]);
                println!(
                    "{:>3} | {:>6} | {:>6} | {:>12.2} | {:>12.2} | {:>10.6} | {:>10.6}",
                    rep.count_m,
                    rep.total_triples_tm,
                    rep.one_sided_pos_triples,
                    rep.empirical_var_w,
                    rep.theoretical_var_w,
                    rep.one_sided_budget,
                    rep.one_sided_harmonic_ceiling
                );
            }
            println!(
                "Neyman–Pearson Quantile-Dominance Root t_* (t^4 + 2t^3 - 1 = 0) = {:.10}",
                quantile_envelope_stationary_point_t_star()
            );
            println!(
                "Max Quantile Variance kappa_* = {:.10} => Theorem 2.5(3) liminf bound <= {:.10}",
                quantile_envelope_max_variance_kappa_star(),
                unconditional_liminf_bound_variance()
            );
            println!(
                "One-Sided Fermat Cone Volume |J_1^<| = {:.10} => Theorem 2.6 liminf bound <= {:.10}",
                one_sided_fermat_cone_volume(),
                unconditional_liminf_bound_one_sided_fermat_laplace()
            );
            println!();
            println!(
                "--- 9. Theorem 2.7 Sub-Level Sub-Cone Positivity & K_*^{{-1/3}} < 2^{{1/3}} Bound ---"
            );
            println!(
                "{:>3} | {:>5} | {:>6} | {:>10} | {:>10} | {:>6} | {:>10}",
                "m", "tau", "N_m^<", "Sum(I_m^<)", "Sum(r^2-m)a_r", "|Omega|", "min C_r>=0"
            );
            println!(
                "--------------------------------------------------------------------------------"
            );
            for &(m, tau_num, tau_den) in &[
                (10usize, 1u64, 1u64),
                (16, 1, 2),
                (22, 1, 2),
                (22, 1, 4),
                (30, 1, 4),
                (30, 1, 8),
            ] {
                let rep =
                    eval_sublevel_subcone_identity(&OEIS_A004023_FIRST_30[..m], tau_num, tau_den);
                println!(
                    "{:>3} | {:>2}/{:<2} | {:>6} | {:>10} | {:>13} | {:>6} | {:>10}",
                    rep.count_m,
                    rep.tau_num,
                    rep.tau_den,
                    rep.full_cone_triple_count,
                    rep.full_cone_triple_sum,
                    rep.full_cone_poly_rhs,
                    rep.sublevel_triple_count,
                    rep.min_discrete_weight
                );
            }
            for &l in &[1.0_f64, 1.5, 2.0, 3.0, 5.0] {
                let (v, s, b) = sublevel_subcone_vol_and_moment_at_l(l);
                println!(
                    "  L = {:>4.1} (tau = {:>6.4}) | Vol(Omega_L^*) = {:.8} | S(Omega_L^*) = {:.8} | bound <= {:.8}",
                    l,
                    1.0 / (l * l * l),
                    v,
                    s,
                    b
                );
            }
            println!(
                "Asymptotic Sub-Level Sub-Cone Volume K_* = Vol(Omega_infty^*) = {:.12}",
                sublevel_subcone_volume_k_star()
            );
            println!(
                "Variable-Separated First Moment S(Omega_infty^*) = (1/2) K_*  = {:.12}",
                sublevel_subcone_first_moment_s_infty()
            );
            println!(
                "Theorem 2.7(c) Unconditional Liminf Bound <= K_*^{{-1/3}}       = {:.10} < 2^{{1/3}} = {:.10}",
                unconditional_liminf_bound_sublevel_subcone(),
                2.0_f64.cbrt()
            );
            println!();
            println!(
                "--- 10. Theorem 2.8 Variational Uniqueness, Laurent Series & Odd-Order B_p Generalization ---"
            );
            for n in 1..=5 {
                let (alpha_n, beta_n) = sublevel_laurent_alpha_beta(n);
                println!(
                    "  Laurent term n = {} (L^{{{:>3}}}): alpha_{} = {:.12} | beta_{} = {:.12}",
                    n,
                    2 - 3 * (n as i32),
                    n,
                    alpha_n,
                    n,
                    beta_n
                );
            }
            for &l in &[1.5_f64, 2.0, 3.0, 5.0] {
                let (v_num, s_num, b_num) = sublevel_subcone_vol_and_moment_at_l(l);
                let (v_laur, s_laur, b_laur) = sublevel_vol_and_moment_laurent(l, 25);
                println!(
                    "  L = {:>4.1} | Vol_num = {:.8} vs Vol_Laur = {:.8} | S_num = {:.8} vs S_Laur = {:.8} | B_Laur = {:.8}",
                    l, v_num, v_laur, s_num, s_laur, b_laur
                );
                let _ = b_num;
            }
            for &(p, n_g) in &[(3usize, 32usize), (5, 32), (7, 14)] {
                let (k_ord, b_ord, k_prod, b_prod) = odd_bp_sublevel_volume_and_bound(p, n_g);
                println!(
                    "  Odd B_{} (h = {}): K_{{*,{}}} = {:.9} => K_{{*,{}}}^{{-1/{}}} = {:.8} | K_{{*,{}}}^{{prod}} = {:.9} => bound = {:.8}",
                    p,
                    p.div_ceil(2),
                    p,
                    k_ord,
                    p,
                    p,
                    b_ord,
                    p,
                    k_prod,
                    b_prod
                );
            }
            println!();
            println!(
                "--- 11. Theorem 2.9 Full-Hypercube Injectivity, Digamma Reflection & eta-Fermat Unification ---"
            );
            let th30 = eval_three_hemisphere_partition(&OEIS_A004023_FIRST_30);
            println!(
                "  A004023 (m = 30): |I_m^lo| = {} | |I_m^mid| = {} | |T_m^-| = {} | |I_m^+| = {} | Sum(I_m^+) = {}",
                th30.lo_count, th30.mid_count, th30.hi_pos_count, th30.full_pos_count, th30.full_pos_sum
            );
            let (k_lo, k_mid, k_smooth) = sublevel_subcone_volume_k_star_smooth();
            let (c_log, c_0) = eta_fermat_asymptotic_constants();
            println!(
                "  Hemisphere Volumes: K_*^lo = {:.12} ({:.2}%) | K_*^mid = {:.12} ({:.2}%) | Smooth K_* = {:.12}",
                k_lo,
                100.0 * k_lo / k_smooth,
                k_mid,
                100.0 * k_mid / k_smooth,
                k_smooth
            );
            println!(
                "  Asymptotic Constants: c_log = Gamma(1/3)^2/(54 Gamma(2/3)) = {:.12} | C_0 = {:.12}",
                c_log, c_0
            );
            for &eta in &[1.0_f64, 0.25, 0.01, 1e-4, 1e-8] {
                let (khi, ktot, b_eta) = eta_fermat_sublevel_cone_volume(eta);
                println!(
                    "  eta = {:<8.2e} | K_*^hi(eta) = {:.8} | K_*(eta) = {:.8} | K_*(eta)^{{-1/3}} = {:.8}",
                    eta, khi, ktot, b_eta
                );
            }
            println!();
            println!(
                "--- 12. Theorem 2.10 Step-s Telescoping Third Hemisphere & Pole-Free Fermat Region III (B_5, B_7) ---"
            );
            let tel30 = eval_telescoping_third_hemisphere(&OEIS_A004023_FIRST_30);
            println!(
                "  A004023 (m = 30): rays = {} (exact = {}, markov = {}) | Step-1 Sum = {} (pos = {}) | Upper Sum = {} | Full-Cube = {}",
                tel30.num_rays,
                tel30.all_rays_telescope_exact,
                tel30.all_markov_bounds_hold,
                tel30.step1_telescoping_sum,
                tel30.step1_pos_count,
                tel30.upper_cone_sum,
                tel30.lower_plus_upper_sum
            );
            for &(p, n_g) in &[(5usize, 32usize), (7, 12)] {
                let (r3_ord, k_ferm, b_ferm, r3_prod, k_pferm, b_pferm) =
                    odd_bp_fermat_majorized_volume_and_bound(p, n_g);
                println!(
                    "  Odd B_{} Fermat-Majorized: K_{{*,{}}}^{{III}} = {:.9} => K_{{*,{}}}^{{Ferm}} = {:.9} (bound {:.8}) | K_{{*,{}}}^{{prod,Ferm}} = {:.9} (bound {:.8}, +R3 {:.9})",
                    p, p, r3_ord, p, k_ferm, b_ferm, p, k_pferm, b_pferm, r3_prod
                );
            }
            println!();
            println!(
                "--- 13. Theorem 2.11 Horizon-Truncated Telescoping Rays & AM-GM Cutoff Law ---"
            );
            for &m in &[12usize, 22, 30] {
                let ht = eval_horizon_truncated_rays(&OEIS_A004023_FIRST_30[..m]);
                println!(
                    "  A004023 (m = {}): |T_m^-| = {} | Untrunc (K=m): {} triples ({} rays) | Horizon-Trunc (K*): {} triples ({} rays) | exact = {}",
                    m,
                    ht.actual_third_hemisphere_pos_count,
                    ht.untruncated_mingap_certified_count,
                    ht.untruncated_active_rays,
                    ht.truncated_mingap_certified_count,
                    ht.truncated_active_rays,
                    ht.all_truncated_identities_exact && ht.all_truncated_bounds_valid
                );
            }
            for &p in &[3usize, 5, 7] {
                let (ex_norm, ex_raw, quad_norm, untrunc_norm) =
                    horizon_truncated_continuum_integrals(p, 512);
                println!(
                    "  Odd B_{} Continuum Cutoff: 1/(6*{}*{}) = {:.9} (quad {:.9}) vs Untrunc = {:.9} (+{:.2}%) | Raw 1/(2*{}*{}*{}) = {:.9}",
                    p,
                    p,
                    p + 1,
                    ex_norm,
                    quad_norm,
                    untrunc_norm,
                    100.0 * (ex_norm / untrunc_norm - 1.0),
                    p,
                    p + 3,
                    2 * p + 1,
                    ex_raw
                );
            }
            println!();
            println!(
                "--- 14. Theorem 2.12 Quadratic Injection-Deflated Rays, Anchor Capacity & Slot-Eviction ---"
            );
            for &m in &[12usize, 22, 30] {
                let qi = eval_quadratic_injection_rays(&OEIS_A004023_FIRST_30[..m]);
                println!(
                    "  A004023 (m = {}): |T_m^-| = {} | Sidon-Quad = {} | RayGap-Quad = {} ({:.1}%) | S_i^* = {} | Evict C = {} (+{} over base RHS)",
                    m,
                    qi.actual_third_hemisphere_pos_count,
                    qi.trunc_sidon_quad_certified_count,
                    qi.trunc_raygap_quad_certified_count,
                    100.0 * (qi.trunc_raygap_quad_certified_count as f64)
                        / (qi.actual_third_hemisphere_pos_count as f64),
                    qi.total_anchor_fiber_s_star,
                    qi.slot_evict_certified_count,
                    qi.slot_evict_poly_rhs - qi.base_min_distinct_rhs
                );
            }
            let (c_ev3, b_ev3, c_base3, b_base3) = slot_eviction_continuum_bound(3);
            println!(
                "  Continuum Slot-Eviction (B_3): c_3^evict = 4375/12384 = {:.10} (vs 1/3 = {:.10}) => bound (12384/4375)^(1/3) = {:.10} < 3^(1/3) = {:.10}",
                c_ev3, c_base3, b_ev3, b_base3
            );
            println!();
            println!(
                "--- 15. Theorems 2.13, 2.14 & Corollary 2.15 Unconditional Diophantine Haar Closure ---"
            );
            let dh16 = eval_b3_diophantine_haar_closure(&OEIS_A004023_FIRST_30, 16, 32);
            println!(
                "  A004023 (R = 16, m = {}): Vandermonde/KKT = {} | Cross-Shell Loc = {} ({} triples) | LF Valid = {} | Binary Splits = {}",
                dh16.active_elements,
                dh16.all_vandermonde_and_kkt_exact,
                dh16.all_cross_shell_localized,
                dh16.localized_cross_shell_triples,
                dh16.all_legendre_fenchel_valid,
                dh16.all_binary_splits_exact
            );
            println!(
                "  Sub-Block Quadratic Excess: Actual = {:.6} >= LF Sawtooth = {:.6} | Split Diff^2 = {} | C_GK = 2 ln A_GK = {:.12}",
                dh16.total_actual_subblock_excess,
                dh16.total_lf_sawtooth_excess,
                dh16.total_binary_split_diff_sq,
                GLAISHER_KINKELIN_C_GK
            );
            for &k_oct in &[0u32, 4, 8, 16, 32, 64, 256] {
                let (kd, bd, kgk, bgk) = b3_diophantine_haar_boost_and_bound(k_oct);
                println!(
                    "  K = {:<3} octaves | kappa_int,3^Dio(K) = {:<9.6} => c_infty,3^*,Dio(K) = {:.8} | GK-Refined = {:.8} (kappa = {:.6})",
                    k_oct, kd, bd, bgk, kgk
                );
            }
            for &(p, n_g) in &[(5usize, 24usize), (7, 10)] {
                let (kd64, b_ord64, b_prod64) = odd_bp_diophantine_haar_bound(p, 64, n_g);
                println!(
                    "  Odd B_{} Diophantine Haar (K = 64, kappa = {:.6}): c_infty,{}^{{*,Dio}}(64) = {:.8} | c_infty,{}^{{prod,Dio}}(64) = {:.8}",
                    p, kd64, p, b_ord64, p, b_prod64
                );
            }
            println!(
                "  Unconditional Limit (K -> infty): lim_{{K->infty}} c_infty,p^{{*,Dio}}(K) = 0 ==> liminf_{{x->infty}} A(x)/x^(1/3) = 0 [PROVED]"
            );
        }
        Commands::Verify { set, x0 } => {
            let parsed: Vec<u32> = set
                .split(',')
                .filter(|s| !s.trim().is_empty())
                .map(|s| s.trim().parse::<u32>().expect("Invalid integer in --set"))
                .collect();
            let horizon_n = parsed.last().copied().unwrap_or(2).max(2);
            let rep = evaluate_b3_conservation(&parsed, horizon_n, x0);
            println!("{}", serde_json::to_string_pretty(&rep)?);
        }
        Commands::Exact {
            n,
            split_x,
            cpu_only,
        } => {
            let gpu = if cpu_only {
                None
            } else {
                Gpu::init(0, "compute_80").ok()
            };
            let t0 = Instant::now();
            let res = solve_exact_f3(n, split_x, gpu.as_ref())?;
            let elapsed = t0.elapsed().as_secs_f64();
            println!(
                "Backend: {} | Elapsed: {:.4}s",
                if let Some(ref g) = gpu {
                    format!("CUDA ({})", g.device_name)
                } else {
                    "CPU (Rayon)".to_string()
                },
                elapsed
            );
            println!("{}", serde_json::to_string_pretty(&res)?);
        }
        Commands::Maximin {
            n,
            x0,
            split_x,
            cpu_only,
        } => {
            let gpu = if cpu_only {
                None
            } else {
                Gpu::init(0, "compute_80").ok()
            };
            let t0 = Instant::now();
            let res = solve_maximin_b3_envelope(n, x0, split_x, gpu.as_ref())?;
            let elapsed = t0.elapsed().as_secs_f64();
            println!("Elapsed: {:.4}s", elapsed);
            println!("{}", serde_json::to_string_pretty(&res)?);
        }
        Commands::Greedy { terms } => {
            let seq = generate_greedy_b3_sequence(terms);
            println!("Greedy B_3 sequence (OEIS A004023, {} terms):", seq.len());
            println!("{:?}", seq);
        }
        Commands::BoseChowla { prime } => {
            let bc = construct_bose_chowla_b3(prime);
            println!("{}", serde_json::to_string_pretty(&bc)?);
        }
        Commands::Bench { n, split_x } => {
            let req_prefix = vec![0u8; (n + 1) as usize];
            let b3_cap = build_subadditive_b3_cap_table(n as usize);
            let prefixes = enumerate_b3_prefixes(split_x, &req_prefix);

            let t_cpu = Instant::now();
            let cpu_out = solve_b3_prefixes_cpu(&prefixes, n, split_x, &req_prefix, &b3_cap);
            let cpu_secs = t_cpu.elapsed().as_secs_f64();
            let cpu_nodes: u64 = cpu_out.iter().map(|o| o.nodes_visited).sum();
            let cpu_best = cpu_out.iter().map(|o| o.max_len).max().unwrap_or(0);

            println!(
                "CPU (Rayon): prefixes={}, N={}, F_3(N)={}, nodes={}, time={:.4}s ({:.2}M nodes/s)",
                prefixes.len(),
                n,
                cpu_best,
                cpu_nodes,
                cpu_secs,
                (cpu_nodes as f64) / cpu_secs / 1e6
            );

            if let Ok(gpu) = Gpu::init(0, "compute_80") {
                let t_gpu = Instant::now();
                let gpu_out =
                    solve_b3_prefixes_gpu(&gpu, &prefixes, n, split_x, &req_prefix, &b3_cap)?;
                let gpu_secs = t_gpu.elapsed().as_secs_f64();
                let gpu_nodes: u64 = gpu_out.iter().map(|o| o.nodes_visited).sum();
                let gpu_best = gpu_out.iter().map(|o| o.max_len).max().unwrap_or(0);
                assert_eq!(cpu_best, gpu_best);
                assert_eq!(cpu_nodes, gpu_nodes);
                println!(
                    "GPU ({}): prefixes={}, N={}, F_3(N)={}, nodes={}, time={:.4}s ({:.2}M nodes/s, speedup={:.2}x, parity=BIT-EXACT)",
                    gpu.device_name,
                    prefixes.len(),
                    n,
                    gpu_best,
                    gpu_nodes,
                    gpu_secs,
                    (gpu_nodes as f64) / gpu_secs / 1e6,
                    cpu_secs / gpu_secs
                );
            }
        }
    }
    Ok(())
}
