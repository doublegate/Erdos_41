#!/usr/bin/env python3
"""
Phase 9 Symbolic, High-Precision & Discrete Verification Suite for Erdős Problem #41:
Theorem 2.12 — Quadratic Injection-Deflated Ray & Anchor-Fiber Counting Inequalities in [1, a_i - 1],
Anchor-Slot Capacity Inequality a_i >= (1 + sqrt(1 + 8 * S_i^*)) / 2, Two-Sided Windowed [J, K-s]
Telescoping Ray Identity, and Third-Hemisphere Slot-Eviction Polynomial Bound (4375 / 12384).
"""

import math
import sympy as sp
import mpmath as mp


def quad_count_exact(s_val: int, m_ceil: int) -> int:
    """Smallest integer C in [0, M] such that C * (2*M + 1 - C) >= 2 * S for S > 0 (0 if S <= 0)."""
    if s_val <= 0:
        return 0
    m_pos = max(1, m_ceil)
    if 2 * s_val >= m_pos * (m_pos + 1):
        return m_pos
    disc = (m_pos + 0.5) ** 2 - 2.0 * s_val
    c = max(1, min(m_pos, int(math.ceil(m_pos + 0.5 - math.sqrt(max(0.0, disc))))))
    while c > 1 and (c - 1) * (2 * m_pos + 1 - (c - 1)) >= 2 * s_val:
        c -= 1
    while c < m_pos and c * (2 * m_pos + 1 - c) < 2 * s_val:
        c += 1
    return c


def verify_part_a_quadratic_injection_and_ray_deflation():
    print("[1/3] Verifying Theorem 2.12(a): Quadratic Injection-Deflated Ray Bound & Ray-Min-Gap Deflation...")
    C, M, S, r = sp.symbols("C M S r", positive=True)

    # 1. Symbolic sum of the C largest distinct integers in {1, ..., M}:
    #    \sum_{r=0}^{C-1} (M - r) = C*(M + 1/2) - C^2 / 2
    sum_top_c = sp.summation(M - r, (r, 0, C - 1))
    quad_rhs = C * (M + sp.Rational(1, 2)) - C**2 / 2
    assert sp.simplify(sum_top_c - quad_rhs) == 0

    # 2. Symbolic proof that M + 1/2 - sqrt((M + 1/2)^2 - 2*S) >= S / M for all S >= M > 0:
    #    (M + 1/2 - S/M)^2 - ((M + 1/2)^2 - 2*S) == S * (S - M) / M^2
    diff_sq = (M + sp.Rational(1, 2) - S / M) ** 2 - ((M + sp.Rational(1, 2)) ** 2 - 2 * S)
    assert sp.simplify(diff_sq - S * (S - M) / M**2) == 0

    # 3. Verify exact discrete condition where c_quad(S, M) >= C > C - 1 = ceil(S / M):
    #    Whenever C >= 3 and (C - 1)*M - binom(C - 1, 2) < S <= min((C - 1)*M, binom(M + 1, 2))
    for m_val in range(3, 18):
        max_sum = m_val * (m_val + 1) // 2
        for c_val in range(3, m_val + 1):
            lo = (c_val - 1) * m_val - (c_val - 1) * (c_val - 2) // 2 + 1
            hi = min((c_val - 1) * m_val, max_sum)
            for s_val in range(lo, hi + 1):
                c_q = quad_count_exact(s_val, m_val)
                c_l = (s_val + m_val - 1) // m_val
                assert c_q >= c_val > c_l
                if s_val > (c_val - 2) * m_val and s_val <= c_val * m_val - c_val * (c_val - 1) // 2:
                    assert c_q == c_val and c_l == c_val - 1

    # 4. Discrete verification on OEIS A004023 prefixes m in {12, 22, 30}:
    #    Compare Theorem 2.11 linear min-gap (8, 50, 126) vs Theorem 2.12 ray-min-gap quadratic deflation (11, 67, 172)
    a30 = [
        1, 2, 5, 14, 33, 72, 125, 219, 376, 573, 745, 1209, 1557, 2442, 3098,
        4048, 5298, 6704, 7839, 10987, 12332, 15465, 19144, 24546, 28974, 34406,
        37769, 45864, 50877, 61372,
    ]
    expected_a004023 = {
        12: (11, 8, 8, 11),
        22: (80, 50, 50, 67),
        30: (214, 126, 126, 172),
    }

    for m, exp in expected_a004023.items():
        seq = a30[:m]
        act_tot = 0
        lin_mg_tot = 0
        quad_sid_tot = 0
        quad_raygap_tot = 0

        for i in range(m - 1):
            ai = seq[i]
            for s in range(1, m - i):
                terms = [ai + seq[j] - seq[j + s] for j in range(i, m - s)]
                pos_vals = [w for w in terms if w >= 1]
                # Verify all positive differences on the ray are distinct integers in [1, a_i - binom(s+1, 2)]
                assert len(pos_vals) == len(set(pos_vals))
                m_sid = max(1, ai - s * (s + 1) // 2)
                for w in pos_vals:
                    assert 1 <= w <= m_sid

                act = len(pos_vals)
                act_tot += act

                best_lin_mg = 0
                best_quad_sid = 0
                best_quad_rg = 0
                m_mg = max(1, ai - s)

                for k_hor in range(i + s + 1, m + 1):
                    sub = terms[: k_hor - s - i]
                    s_k = (k_hor - s - i) * ai + sum(seq[i : i + s]) - sum(seq[k_hor - s : k_hor])
                    assert s_k == sum(sub)
                    if s_k > 0:
                        c_l = (s_k + m_mg - 1) // m_mg
                        c_qs = quad_count_exact(s_k, m_sid)
                        min_gap_k = min(seq[j + s] - seq[j] for j in range(i, k_hor - s))
                        m_rg = max(1, ai - min_gap_k)
                        c_qrg = quad_count_exact(s_k, m_rg)
                        pos_k = sum(1 for w in sub if w >= 1)
                        assert 0 <= c_l <= c_qs <= c_qrg <= pos_k <= act
                        best_lin_mg = max(best_lin_mg, c_l)
                        best_quad_sid = max(best_quad_sid, c_qs)
                        best_quad_rg = max(best_quad_rg, c_qrg)

                lin_mg_tot += best_lin_mg
                quad_sid_tot += best_quad_sid
                quad_raygap_tot += best_quad_rg

        got = (act_tot, lin_mg_tot, quad_sid_tot, quad_raygap_tot)
        assert got == exp, f"Mismatch at m={m}: got {got}, expected {exp}"

    print(
        "      PASS: Quadratic injection-deflated ray bound, Sidon step-s ceiling a_i - binom(s+1,2), "
        "and ray-min-gap deflation (m=12: 11/11; m=22: 67/80 vs 50/80; m=30: 172/214 vs 126/214) verified."
    )


def verify_part_b_anchor_fiber_and_capacity_inequality():
    print("[2/3] Verifying Theorem 2.12(b): Anchor-Fiber Quadratic Bound, Capacity Inequality & Continuum Profile...")
    ai_sym, ci_sym, si_sym, u = sp.symbols("a_i C_i S_i u", positive=True)

    # 1. Symbolic Anchor-Fiber sum of C_i largest integers in {1, ..., a_i - 1}:
    #    \sum_{r=1}^{C_i} (a_i - r) = C_i*(a_i - 1/2) - C_i^2 / 2 <= binom(a_i, 2)
    r = sp.Symbol("r", integer=True)
    fiber_max_sum = sp.summation(ai_sym - r, (r, 1, ci_sym))
    expected_fiber_sum = ci_sym * (ai_sym - sp.Rational(1, 2)) - ci_sym**2 / 2
    assert sp.simplify(fiber_max_sum - expected_fiber_sum) == 0

    # At C_i = a_i - 1, the maximum possible sum is a_i*(a_i - 1)/2 = binom(a_i, 2):
    max_cap = sp.simplify(expected_fiber_sum.subs(ci_sym, ai_sym - 1))
    assert sp.simplify(max_cap - ai_sym * (ai_sym - 1) / 2) == 0

    # Solving a_i^2 - a_i - 2*S_i >= 0 for a_i > 0 gives a_i >= (1 + sqrt(1 + 8*S_i)) / 2:
    roots = sp.solve(ai_sym**2 - ai_sym - 2 * si_sym, ai_sym)
    pos_root = [rt for rt in roots if rt.subs(si_sym, 1) > 0][0]
    assert sp.simplify(pos_root - (1 + sp.sqrt(1 + 8 * si_sym)) / 2) == 0

    # 2. Symbolic continuum anchor-fiber profile for p = 3:
    #    f_norm(u) = u^2*(1 - u)/6 peaks at u* = 2/3 with value 2/81;
    #    f_raw(u)  = u^5*(1 - u)/6 peaks at u** = 5/6 with value 3125/279936.
    f_norm = u**2 * (1 - u) / 6
    f_raw = u**5 * (1 - u) / 6
    u_star_norm = sp.solve(sp.diff(f_norm, u), u)[0]
    u_star_raw = sp.solve(sp.diff(f_raw, u), u)[0]
    assert u_star_norm == sp.Rational(2, 3)
    assert f_norm.subs(u, u_star_norm) == sp.Rational(2, 81)
    assert u_star_raw == sp.Rational(5, 6)
    assert f_raw.subs(u, u_star_raw) == sp.Rational(3125, 279936)

    # 3. Verify Anchor-Fiber injectivity in {1, ..., a_i - 1} and Anchor-Slot Capacity Inequality on A004023 (m=30)
    a30 = [
        1, 2, 5, 14, 33, 72, 125, 219, 376, 573, 745, 1209, 1557, 2442, 3098,
        4048, 5298, 6704, 7839, 10987, 12332, 15465, 19144, 24546, 28974, 34406,
        37769, 45864, 50877, 61372,
    ]
    m = 30
    total_si_star = 0
    for i in range(m - 1):
        ai = a30[i]
        fiber_pos_vals = []
        si_star = 0
        for s in range(1, m - i):
            terms = [ai + a30[j] - a30[j + s] for j in range(i, m - s)]
            fiber_pos_vals.extend(w for w in terms if w >= 1)
            best_s = max([0] + [sum(terms[:end]) for end in range(1, len(terms) + 1)])
            si_star += best_s
        # All positive third-hemisphere differences at anchor i across ALL steps s >= 1 are distinct in [1, a_i - 1]
        assert len(fiber_pos_vals) == len(set(fiber_pos_vals))
        for w in fiber_pos_vals:
            assert 1 <= w <= ai - 1
        ci_actual = len(fiber_pos_vals)
        ci_quad = quad_count_exact(si_star, max(1, ai - 1))
        cap_lb = 0.5 * (1.0 + math.sqrt(1.0 + 8.0 * si_star))
        assert si_star <= sum(ai - r for r in range(1, ci_actual + 1)) <= ai * (ai - 1) // 2
        assert ci_quad <= ci_actual
        assert ai >= cap_lb - 1e-12
        total_si_star += si_star

    assert total_si_star == 1510090

    print(
        f"      PASS: Anchor-fiber injectivity in [1, a_i - 1], capacity inequality a_i >= (1 + sqrt(1 + 8*S_i^*))/2 "
        f"(total S_i^* = {total_si_star}), and continuum fiber peaks (u* = 2/3 -> 2/81, u** = 5/6 -> 3125/279936) verified."
    )


def verify_part_c_two_sided_windows_and_slot_eviction():
    print("[3/3] Verifying Theorem 2.12(c): Two-Sided Windowed Telescoping & Slot-Eviction Bound (4375/12384)...")
    a = sp.IndexedBase("a")

    # 1. Symbolic verification of Two-Sided Windowed Telescoping Identity for all 1 <= i <= J <= K - s <= m - s
    for m_val in (6, 9, 11):
        for i_val in range(1, m_val):
            for s_val in range(1, m_val - i_val + 1):
                for j_start in range(i_val, m_val - s_val + 1):
                    for k_val in range(j_start + s_val, m_val + 1):
                        lhs = sum(a[i_val] + a[j] - a[j + s_val] for j in range(j_start, k_val - s_val + 1))
                        rhs = (
                            (k_val - s_val - j_start + 1) * a[i_val]
                            + sum(a[r] for r in range(j_start, j_start + s_val))
                            - sum(a[r] for r in range(k_val - s_val + 1, k_val + 1))
                        )
                        assert sp.simplify(lhs - rhs) == 0

    # 2. Verify strict improvement of Two-Sided Windowed Telescoping (J >= i) over single-horizon (J = i)
    #    on Bose–Chowla affine-modular B_3 sets (p = 5, 7, 11)
    bose_chowla_sets = {
        "p5_raw": ([1, 14, 34, 103, 119], 2, 1, 2),
        "p7_raw": ([1, 13, 43, 146, 150, 231, 280], 12, 9, 11),
        "p11_compressed": ([1, 32, 122, 346, 380, 456, 486, 602, 763, 785, 859], 83, 56, 59),
    }
    for label, (seq, exp_act, exp_trunc, exp_win) in bose_chowla_sets.items():
        m = len(seq)
        act_tot = 0
        trunc_tot = 0
        win_tot = 0
        for i in range(m - 1):
            ai = seq[i]
            for s in range(1, m - i):
                m_sid = max(1, ai - s * (s + 1) // 2)
                terms = [ai + seq[j] - seq[j + s] for j in range(i, m - s)]
                act = sum(1 for w in terms if w >= 1)
                act_tot += act
                best_trunc = 0
                for k_hor in range(i + s + 1, m + 1):
                    s_k = (k_hor - s - i) * ai + sum(seq[i : i + s]) - sum(seq[k_hor - s : k_hor])
                    best_trunc = max(best_trunc, quad_count_exact(s_k, m_sid))
                best_win = 0
                for j_start in range(i, m - s):
                    for k_hor in range(j_start + s + 1, m + 1):
                        s_jk = (k_hor - s - j_start) * ai + sum(seq[j_start : j_start + s]) - sum(seq[k_hor - s : k_hor])
                        assert s_jk == sum(ai + seq[j] - seq[j + s] for j in range(j_start, k_hor - s))
                        best_win = max(best_win, quad_count_exact(s_jk, m_sid))
                assert best_trunc <= best_win <= act
                trunc_tot += best_trunc
                win_tot += best_win
        assert (act_tot, trunc_tot, win_tot) == (exp_act, exp_trunc, exp_win), f"Failed on {label}"
        assert win_tot > trunc_tot

    # 3. Verify Discrete & Continuum Third-Hemisphere Slot-Eviction Polynomial Bound
    a30 = [
        1, 2, 5, 14, 33, 72, 125, 219, 376, 573, 745, 1209, 1557, 2442, 3098,
        4048, 5298, 6704, 7839, 10987, 12332, 15465, 19144, 24546, 28974, 34406,
        37769, 45864, 50877, 61372,
    ]
    expected_evict = {
        12: (335345, 128271, 129793, 6, 1522),
        22: (25093137, 5483016, 5523707, 23, 40691),
        30: (242565637, 36598290, 36827084, 50, 228794),
    }
    for m, (exp_lhs, exp_base, exp_evict, exp_c, exp_gain) in expected_evict.items():
        seq = a30[:m]
        n_lt = m * (m - 1) * (2 * m - 1) // 6
        poly_lhs = sum(((r + 1) ** 2 - m) * seq[r] for r in range(m))
        base_rhs = n_lt * (n_lt + 1) // 2
        c_evict = 0
        upper_w_sum = 0
        for i in range(m - 1):
            ai = seq[i]
            for s in range(1, m - i):
                m_sid = max(1, ai - s * (s + 1) // 2)
                terms = [ai + seq[j] - seq[j + s] for j in range(i, m - s)]
                best_s = max([0] + [sum(terms[:end]) for end in range(1, len(terms) + 1)])
                c_q = quad_count_exact(best_s, m_sid)
                if c_q > 0 and m_sid <= n_lt + c_evict:
                    c_evict += c_q
                    upper_w_sum += c_q * m_sid - c_q * (c_q - 1) // 2
        evict_rhs = (n_lt + c_evict) * (n_lt + c_evict + 1) // 2 - upper_w_sum
        gain = evict_rhs - base_rhs
        assert (poly_lhs, base_rhs, evict_rhs, c_evict, gain) == (exp_lhs, exp_base, exp_evict, exp_c, exp_gain)
        assert poly_lhs >= evict_rhs > base_rhs

    # Continuum universal odd-B_p slot-eviction constant:
    # (1/(p+3) + 1/(2*p*(p+3)*(2*p+1))) * c >= (1/2) * (1/3 + 1/(6*p*(p+1)))^2
    p_sym, c_sym = sp.symbols("p c", positive=True)
    lhs_c = (sp.Rational(1, 1) / (p_sym + 3) + sp.Rational(1, 1) / (2 * p_sym * (p_sym + 3) * (2 * p_sym + 1))) * c_sym
    rhs_c = sp.Rational(1, 2) * (sp.Rational(1, 3) + sp.Rational(1, 1) / (6 * p_sym * (p_sym + 1))) ** 2
    c_evict_formula = sp.factor(sp.solve(sp.Eq(lhs_c, rhs_c), c_sym)[0])
    expected_formula = (p_sym + 3) * (2 * p_sym + 1) * (2 * p_sym**2 + 2 * p_sym + 1) ** 2 / (
        36 * p_sym * (p_sym + 1) ** 2 * (4 * p_sym**2 + 2 * p_sym + 1)
    )
    assert sp.simplify(c_evict_formula - expected_formula) == 0
    c3_exact = c_evict_formula.subs(p_sym, 3)
    assert c3_exact == sp.Rational(4375, 12384)

    mp.mp.dps = 50
    b_evict_3 = float((mp.mpf(12384) / mp.mpf(4375)) ** (mp.mpf(1) / 3))
    b_base_3 = float(mp.mpf(3) ** (mp.mpf(1) / 3))
    assert abs(b_evict_3 - 1.4145803750029842) < 1e-12
    assert b_evict_3 < b_base_3

    print(
        f"      PASS: Two-sided windowed telescoping identity, Bose–Chowla gains (p=7: 11/12 vs 9/12; p=11: 59/83 vs 56/83), "
        f"and Slot-Eviction bound c >= 4375/12384 ((12384/4375)^(1/3) = {b_evict_3:.10f} < 3^(1/3) = {b_base_3:.10f}) verified."
    )


if __name__ == "__main__":
    print("==========================================================================")
    print(" Erdős Problem #41 — Phase 9 Quadratic Injection & Windowed Ray Suite")
    print("==========================================================================")
    verify_part_a_quadratic_injection_and_ray_deflation()
    verify_part_b_anchor_fiber_and_capacity_inequality()
    verify_part_c_two_sided_windows_and_slot_eviction()
    print("==========================================================================")
    print(" ALL PHASE 9 SYMBOLIC, HIGH-PRECISION & DISCRETE CHECKS PASSED.")
    print("==========================================================================")
