/-
Copyright 2026 Lucas Parobek.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

# Erdős Problem #41 — Lean 4 Formal Verification Suite
Paper: "Unconditional Diophantine Haar Closure, Exact (2,1)-Difference Harmonic Conservation,
        Projective Fermat Sub-Level Cones, and O(1) GPU Branch-and-Bound for Erdős Problem #41"
        (Parobek, 2026)
Repo:  https://github.com/doublegate/Erdos_41

Status (2026-11-03): Erdős Problem #41 is open. The manuscript [Pa26] has been withdrawn after an
independent review found its decisive step (Theorem 4.2, the "Diophantine Haar closure") invalid;
see the repository README.

This self-contained Lean 4 module (16 theorems, zero `sorry`s, zero custom axioms) proves
elementary identities and inequalities over `ℕ` (closed by `omega`, `ac_rfl`, `simp`) and checks
by `decide` that specific finite lists are B₃ sets. No declaration mentions an infinite set, the
counting function `A(x)`, a liminf, or the closure step, so none of them verifies the
corresponding manuscript theorem. The descriptions below record the role each lemma was meant to
play in [Pa26] (Theorems 2.1 through 2.14 and Section 3).
-/

namespace Erdos41

local notation "ℕ" => Nat

/-! ## 1. Theorem 2.1(1)–(2): Exact (2,1)-Difference Harmonic Conservation Numerator Identities -/

/--
**Theorem 2.1(1)–(2) & Theorem 2.3(2) (Sign-Split (2,1)-Difference Harmonic Conservation Numerators):**
For any positive integers `1 ≤ a_i ≤ a_j < a_k`,
- on the Positive Cone (`a_i + a_j ≤ a_k`, where `w = a_k - a_i - a_j ≥ 0` and `a_i + a_j ≥ 2`),
  `(a_k - a_i - a_j + 2) + (a_i + a_j - 2) = a_k`;
- on the Negative Cone (`a_k ≤ a_i + a_j ≤ 2 a_k - 2`, where `d = a_i + a_j - a_k ≥ 0`),
  `(a_i + a_j - a_k + 2) + (2 a_k - a_i - a_j - 2) = a_k`.
Dividing by `(|a_k - a_i - a_j| + 2) a_k` closes the exact non-asymptotic `(2,1)`-Difference
Harmonic Conservation Identity `E_A^{(3)}(N) + Δ_A^{(2,1)}(N) = B_A^{(2,1)}(N)`.
-/
theorem erdos_41.variants.b3_harmonic_conservation_numerator (a_i a_j a_k : ℕ)
    (hi : 1 ≤ a_i) (hij : a_i ≤ a_j) (hjk : a_j < a_k) :
    (a_i + a_j ≤ a_k → (a_k - a_i - a_j + 2) + (a_i + a_j - 2) = a_k) ∧
    (a_k ≤ a_i + a_j → (a_i + a_j - a_k + 2) + (2 * a_k - a_i - a_j - 2) = a_k) := by
  omega

/-! ## 2. Theorem 2.2(1): Bose–Chowla GF(p^3) Pigeonhole Gap-Compressed Span Bound -/

/--
**Theorem 2.2(1) (Bose–Chowla `GF(p^3)` Pigeonhole Gap-Compressed Span Bound):**
For any prime `p ≥ 2` and modular gap maximum `g_max ≤ p^3 - 1` satisfying the pigeonhole
inequality `p^3 - 1 ≤ p · g_max`, we have `p^2 ≤ g_max` and the gap-compressed
integer `B_3` span `N_p^* = p^3 - g_max` satisfies `N_p^* ≤ p^3 - p^2`.
-/
theorem erdos_41.variants.bose_chowla_pigeonhole_compressed_span (p g_max : ℕ)
    (hp : 2 ≤ p) (h_pigeon : p * (p * p) - 1 ≤ p * g_max) :
    p * p ≤ g_max ∧ p * (p * p) - g_max ≤ p * (p * p) - p * p := by
  have h_lt : ¬ (g_max < p * p) := by
    intro h_bad
    have h1 : g_max + 1 ≤ p * p := h_bad
    have h2 : p * (g_max + 1) ≤ p * (p * p) := Nat.mul_le_mul_left p h1
    rw [Nat.mul_add, Nat.mul_one] at h2
    omega
  omega

/-! ## 3. Theorem 2.3(3): Intra-Shell Triple Negative-Cone Exclusivity -/

/--
**Theorem 2.3(3) (Intra-Shell Negative-Cone Exclusivity), corrected form:**
In a dyadic shell `(H, 2H] ∩ ℕ` (`H = 2^(r-1) ≥ 2`), every triple
`H + 1 ≤ a_i ≤ a_j < a_k ≤ 2 H` satisfies `a_k < a_i + a_j` and `2 ≤ a_i + a_j - a_k ≤ 2 H - 2`,
so `w = a_k - a_i - a_j` lies in `[-(2H - 2), -2] = [-(2^r - 2), -2]`.
Correction (2026-11-03): the manuscript stated the stronger range `-(2^(r-1) - 2) ≤ w`, which is
false: `{22, 27, 31}` in the shell `(16, 32]` gives `w = 31 - 22 - 27 = -18 < -14`. This lemma
proves only the weaker, correct bound.
-/
theorem erdos_41.variants.intrashell_triple_negative_cone_localization (H a_i a_j a_k : ℕ)
    (hH : 2 ≤ H) (hi : H + 1 ≤ a_i) (hij : a_i ≤ a_j) (hjk : a_j < a_k) (hk : a_k ≤ 2 * H) :
    2 ≤ a_i + a_j - a_k ∧ a_i + a_j - a_k ≤ 2 * H - 2 := by
  omega

/-! ## 4. Theorem 2.5(2): Full-Cube (2,1)-Difference Symmetric Second-Moment Identity -/

/--
**Theorem 2.5(2) (Full-Cube `(2,1)`-Difference Second-Moment Combinatorial Identity):**
For every integer `m ≥ 3`, summing twice the diagonal deviation weight `2(5m - 1)` (from `i = j ≠ k`)
and twice the off-diagonal deviation weight `(3m - 1)(m - 2)` (from `i < j, k ∉ {i, j}`) yields
`2(5m - 1) + (3m - 1)(m - 2) = 3m(m + 1)`, proving the exact symmetric variance identity
`sum_{(i,j,k) ∈ I_m} (w(i, j; k) - a_bar)^2 = (3m(m + 1))/2 sum_{r=1..m} (a_r - a_bar)^2`.
-/
theorem erdos_41.variants.full_cube_second_moment_combinatorial_identity (m : ℕ) (hm : 3 ≤ m) :
    2 * (5 * m - 1) + (3 * m - 1) * (m - 2) = 3 * m * (m + 1) := by
  rcases Nat.exists_eq_add_of_le hm with ⟨d, rfl⟩
  change 2 * (5 * (3 + d) - 1) + (3 * (3 + d) - 1) * ((3 + d) - 2) = 3 * (3 + d) * ((3 + d) + 1)
  have h1 : 5 * (3 + d) - 1 = 14 + 5 * d := by omega
  have h2 : 3 * (3 + d) - 1 = 8 + 3 * d := by omega
  have h3 : (3 + d) - 2 = 1 + d := by omega
  have h4 : 3 * (3 + d) = 9 + 3 * d := by omega
  have h5 : (3 + d) + 1 = 4 + d := by omega
  rw [h1, h2, h3, h4, h5]
  simp [Nat.add_mul, Nat.mul_add]
  omega

/-! ## 5. Theorem 2.6 & Theorem 2.7(1): One-Sided Positive Sub-Cone First-Moment Polynomial Identity -/

/--
**Theorem 2.7(1) (Exact First-Moment Polynomial Occurrence Weight on `I_m^<`):**
For every index `r = a + 1 ≥ 1` and tail count `b = m - r ≥ 0` (so `m = a + b + 1`), in the
one-sided positive sub-cone `I_m^< = {(i, j, k) : 1 ≤ i ≤ j ≤ m, 1 ≤ k < j, k ≠ i}`,
twice the occurrence counts of index `r` as `i`, `j`, and `k` satisfy the exact polynomial identity
`(2 a + b(2 a + b)) + 2 a^2 + 2(a + b + 1) = b(2 a + b + 2) + 2(a + 1)^2`,
which establishes `sum_{(i,j,k) ∈ I_m^<} (a_i + a_j - a_k) = sum_{r=1..m} (r^2 - m) a_r`.
-/
theorem erdos_41.variants.one_sided_subcone_first_moment_weight (a b : ℕ) :
    (2 * a + b * (2 * a + b)) + 2 * (a * a) + 2 * (a + b + 1) =
      b * (2 * a + b + 2) + 2 * ((a + 1) * (a + 1)) := by
  simp only [Nat.add_mul, Nat.mul_add]
  ac_rfl

/-! ## 6. Theorem 2.8 & Theorem 2.9(1): Three-Hemisphere Partition of the Full-Cube (2,1)-Difference Set -/

/--
**Theorem 2.9(1) (Three-Hemisphere Cardinality Decomposition of `I_m^<` and `I_m`):**
For every integer `m ≥ 2`, the `6×`-scaled lower-hemisphere cardinality `6|I_m^lo| = m(m - 1)(m + 1)`
and middle-hemisphere cardinality `6|I_m^mid| = m(m - 1)(m - 2)` sum identically to
`6|I_m^<| = m(m - 1)(2m - 1)`, and adding the `6×`-scaled upper-hemisphere cardinality
`6|T_m^upper| = m(m - 1)(m + 1)` recovers `6|I_m| = 6 T_m = 3 m^2 (m - 1)`.
-/
theorem erdos_41.variants.three_hemisphere_cardinality_decomposition (m : ℕ) (hm : 2 ≤ m) :
    m * (m - 1) * (m + 1) + m * (m - 1) * (m - 2) = m * (m - 1) * (2 * m - 1) ∧
    m * (m - 1) * (2 * m - 1) + m * (m - 1) * (m + 1) = 3 * (m * m) * (m - 1) := by
  have h1 : (m + 1) + (m - 2) = 2 * m - 1 := by omega
  have h2 : (2 * m - 1) + (m + 1) = 3 * m := by omega
  constructor
  · rw [← Nat.mul_add, h1]
  · rw [← Nat.mul_add, h2]
    ac_rfl

/-! ## 7. Theorem 2.10(1): Dual Upper- and Lower-Hemisphere Polynomial Cancellation Identity -/

/--
**Theorem 2.10(1) (Dual Upper- plus Lower-Hemisphere Polynomial Cancellation Identity):**
For every `1 ≤ r ≤ m`, summing the doubled one-sided positive sub-cone polynomial weight
`(2 r^2 - 2 m)` of Theorem 2.7(1) and the doubled upper-hemisphere polynomial weight
`(m(m + 1) - 2 r^2)` of Theorem 2.10(1) cancels `± 2 r^2` identically to yield the constant
Full-Cube weight `m(m - 1) = 2C(m, 2)`:
`(2 r^2 + m(m + 1)) = (2 m + 2 r^2) + m(m - 1)`.
-/
theorem erdos_41.variants.upper_plus_lower_hemisphere_full_cube_sum (m r : ℕ) (hm : 1 ≤ m) :
    2 * (r * r) + m * (m + 1) = (2 * m + 2 * (r * r)) + m * (m - 1) := by
  rcases Nat.exists_eq_add_of_le hm with ⟨k, rfl⟩
  have h_sub : (1 + k) - 1 = k := by omega
  rw [h_sub]
  simp [Nat.add_mul, Nat.mul_add]
  omega

/-! ## 8. Theorem 2.11(2): Continuum AM-GM Cubic Cutoff Square Factorization -/

/--
**Theorem 2.11(2) (Exact Cubic AM-GM Cutoff Square Factorization):**
For every integer `t = d + 1 ≥ 1`, the 3-term AM-GM excess polynomial `2 t^3 - 3 t^2 + 1` factors
identically as the square `(t - 1)^2 (2 t + 1) = d^2 (2 d + 3)`:
`(t - 1)^2 (2 t + 1) + 3 t^2 = 2 t^3 + 1`,
certifying that `Φ(u, σ; κ^*(u, σ))/u^3 = (u(t - 1)^2(2t + 1))/3t^2 > 0`
for all `t > 1` (`σ ∈ (0, u/3)`).
-/
theorem erdos_41.variants.am_gm_cubic_cutoff_factorization (d : ℕ) :
    (d * d) * (2 * d + 3) + 3 * ((d + 1) * (d + 1)) =
      2 * ((d + 1) * (d + 1) * (d + 1)) + 1 := by
  have h_sq : (d + 1) * (d + 1) = d * d + 2 * d + 1 := by
    simp [Nat.add_mul, Nat.mul_add]
    omega
  rw [h_sq]
  have h_lhs : (d * d) * (2 * d + 3) + 3 * (d * d + 2 * d + 1) =
      2 * (d * d * d) + 6 * (d * d) + 6 * d + 3 := by
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_add]
    have h1 : (d * d) * (2 * d) = 2 * (d * d * d) := by ac_rfl
    have h2 : (d * d) * 3 = 3 * (d * d) := by ac_rfl
    rw [h1, h2]
    omega
  have h_rhs : 2 * ((d * d + 2 * d + 1) * (d + 1)) + 1 =
      2 * (d * d * d) + 6 * (d * d) + 6 * d + 3 := by
    rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, Nat.mul_one]
    have h3 : (2 * d) * d = 2 * (d * d) := by ac_rfl
    rw [h3]
    omega
  rw [h_lhs, h_rhs]

/-! ## 9. Theorem 2.12(1)–(2): Quadratic Injection-Deflated Ray Ceiling Identity -/

/--
**Theorem 2.12(1)–(2) (Quadratic Injection-Deflated Ray & Anchor-Fiber Sum Identity):**
For any positive integer ceiling `M` and distinct positive integer count `C ≤ M`, twice the
maximum sum `sum_{r=0..C-1} (M - r)` of `C` distinct integers in `{1, ..., M}` satisfies
`C(2 M + 1 - C) + C(C - 1) = 2 C M`, so `C(2 M + 1 - C) ≤ 2 C M` with strict deflation
`C(2 M + 1 - C) < 2 C M` whenever `C ≥ 2`.
-/
theorem erdos_41.variants.quadratic_injection_ray_sum_identity (M C : ℕ) (hC : C ≤ M) :
    C * (2 * M + 1 - C) + C * (C - 1) = 2 * (C * M) ∧
    C * (2 * M + 1 - C) ≤ 2 * (C * M) := by
  have h_eq : C * (2 * M + 1 - C) + C * (C - 1) = 2 * (C * M) := by
    cases C with
    | zero => simp
    | succ k =>
      have h_sub1 : (k + 1) - 1 = k := rfl
      have h_sub2 : 2 * M + 1 - (k + 1) = 2 * M - k := by omega
      rw [h_sub1, h_sub2, ← Nat.mul_add]
      have h_add : (2 * M - k) + k = 2 * M := by omega
      rw [h_add]
      ac_rfl
  exact ⟨h_eq, by omega⟩

/-! ## 10. Theorem 2.13(1): Cross-Shell (2,1)-Difference Vandermonde Decomposition & Localization -/

/--
**Theorem 2.13(1) (Dyadic Cross-Shell `(2,1)`-Difference Decomposition & Two-Shell Localization):**
For any prefix count `P = M_r-1` and shell count `m = m_r`, the cubed shell sum `(P + m)^3`
decomposes into the prefix cube `P^3`, intra-shell cube `m^3`, `(1,2)` cross-shell term `3 m^2 P`,
and `(2,1)` cross-shell term `3 m P^2`:
`(P + m)^3 = P^3 + m^3 + 3 m^2 P + 3 m P^2`,
and whenever `2 ≤ a_i + a_j ≤ 2^r-2` (`pow_rm2`) and `2 · 2^r-2 < a_k ≤ 4 · 2^r-2`,
the cross-shell `(2,1)`-difference satisfies `2^r-2 < a_k - (a_i + a_j) < 4 · 2^r-2 = 2^r`.
-/
theorem erdos_41.variants.dyadic_shell_21_vandermonde_decomposition (P m a_ij a_k pow_rm2 : ℕ)
    (hij_pos : 2 ≤ a_ij) (hij_hi : a_ij ≤ pow_rm2)
    (hk_lo : 2 * pow_rm2 < a_k) (hk_hi : a_k ≤ 4 * pow_rm2) :
    (P + m) * (P + m) * (P + m) =
      P * P * P + m * m * m + 3 * (m * m * P) + 3 * (m * (P * P)) ∧
    (pow_rm2 < a_k - a_ij ∧ a_k - a_ij < 4 * pow_rm2) := by
  refine ⟨?_, by omega⟩
  have h3a : 3 * (m * m * P) = m * m * P + m * m * P + m * m * P := by omega
  have h3b : 3 * (m * (P * P)) = m * (P * P) + m * (P * P) + m * (P * P) := by omega
  rw [h3a, h3b]
  simp only [Nat.add_mul, Nat.mul_add]
  ac_rfl

/-! ## 11. Theorem 2.13(2): KKT Cubic & Odd-Bp Shell-Increment Convexity -/

/--
**Theorem 2.13(2) (KKT Cubic & Odd-`B_p` Shell-Increment Positivity):**
For every odd order `p ≥ 3`, the `p`-th power of the dyadic shell-weight ratio satisfies
`2^p = 2 · 2^p-1 > 2^p-1` (`8 > 4` at `p = 3`, certifying `2^-r ρ_r^2 > 2^{-(r+1)} ρ_r+1^2`),
and for any prefix count `M ≥ 1` and positive integer mass shift `δ ≥ 1` from shell `r + 1`
into shell `r`, the cubed prefix count strictly increases by
`(M + δ)^3 - M^3 = 3 δ M^2 + 3 δ^2 M + δ^3 ≥ 7 > 0`,
certifying strict positivity of the KKT multipliers `λ_r > 0`.
-/
theorem erdos_41.variants.kkt_cubic_shell_increment_convexity (p M δ : ℕ)
    (hp : 3 ≤ p) (hM : 1 ≤ M) (hδ : 1 ≤ δ) :
    2 ^ (p - 1) < 2 ^ p ∧
    (M + δ) * (M + δ) * (M + δ) =
      M * M * M + δ * δ * δ + 3 * (δ * δ * M) + 3 * (δ * (M * M)) ∧
    M * M * M + 7 ≤ (M + δ) * (M + δ) * (M + δ) := by
  have hp_pow : 2 ^ (p - 1) < 2 ^ p := by
    rcases Nat.exists_eq_add_of_le hp with ⟨k, rfl⟩
    have h_sub : (3 + k) - 1 = 2 + k := by omega
    have h_add : 3 + k = (2 + k) + 1 := by omega
    rw [h_sub, h_add, Nat.pow_succ]
    have h_pos : 1 ≤ 2 ^ (2 + k) := Nat.one_le_pow (2 + k) 2 (by decide)
    omega
  have h_cube := (erdos_41.variants.dyadic_shell_21_vandermonde_decomposition M δ 2 5 2
    (by decide) (by decide) (by decide) (by decide)).1
  have h_ge1 : 1 ≤ δ * δ * δ := by
    have h2 : 1 ≤ δ * δ := Nat.mul_le_mul hδ hδ
    exact Nat.mul_le_mul h2 hδ
  have h_ge2 : 1 ≤ δ * δ * M := by
    have h2 : 1 ≤ δ * δ := Nat.mul_le_mul hδ hδ
    exact Nat.mul_le_mul h2 hM
  have h_ge3 : 1 ≤ δ * (M * M) := by
    have h2 : 1 ≤ M * M := Nat.mul_le_mul hM hM
    exact Nat.mul_le_mul hδ h2
  refine ⟨hp_pow, h_cube, by omega⟩

/-! ## 12. Theorem 2.14(a): Discrete Legendre–Fenchel (2,1)-Fiber Integrality Excess -/

/--
**Theorem 2.14(a) (Discrete Legendre–Fenchel Sub-Block `(2,1)`-Fiber Decomposition & Squared Identity):**
For any sub-block count `B ≥ 1` and shell occupancy `S = B q + t` with integer quotient `q` and
remainder `t ≤ B`, the minimum intra-sub-block ordered-pair count satisfies
`(B - t) q(q - 1) + t(q + 1)q = B q(q - 1) + 2 t q` and
`B(B q^2 + 2 t q) + B t = (B q + t)^2 + t(B - t)`,
separating the smooth quadratic energy `(B q + t)^2` from the strictly non-negative discrete
Legendre–Fenchel integrality excess `t(B - t) = B^2 θ(1 - θ)`.
-/
theorem erdos_41.variants.discrete_legendre_fenchel_b3_fiber_excess (B q t : ℕ)
    (ht : t ≤ B) :
    (B - t) * (q * (q - 1)) + t * ((q + 1) * q) = B * (q * (q - 1)) + 2 * (t * q) ∧
    B * (B * (q * q) + 2 * (t * q)) + B * t = (B * q + t) * (B * q + t) + t * (B - t) := by
  constructor
  · have h1 : (q + 1) * q = q * (q - 1) + 2 * q := by
      cases q with
      | zero => rfl
      | succ m =>
        change (m + 2) * (m + 1) = (m + 1) * m + 2 * (m + 1)
        rw [Nat.add_mul, Nat.mul_comm m (m + 1)]
    rw [h1, Nat.mul_add, ← Nat.add_assoc, ← Nat.add_mul, Nat.sub_add_cancel ht, Nat.mul_left_comm t 2 q]
  · have h_t : t * t + t * (B - t) = t * B := by
      rw [← Nat.mul_add, Nat.add_sub_cancel' ht]
    have h_expand : (B * q + t) * (B * q + t) = B * (B * (q * q) + 2 * (t * q)) + t * t := by
      calc
        (B * q + t) * (B * q + t)
          = (B * q) * (B * q) + (B * q) * t + (t * (B * q) + t * t) := by
            rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
        _ = B * (B * (q * q)) + B * (t * q) + B * (t * q) + t * t := by
            ac_rfl
        _ = B * (B * (q * q) + 2 * (t * q)) + t * t := by
            rw [Nat.two_mul, Nat.mul_add, Nat.mul_add, ← Nat.add_assoc]
    rw [h_expand, Nat.add_assoc, h_t, Nat.mul_comm t B]

/-! ## 13. Theorem 2.14(a): Quarter-Square Sawtooth Ceiling & Relative Integrality Scaling -/

/--
**Theorem 2.14(a) (Exact Quarter-Square Sawtooth Ceiling & Relative Integrality Scaling):**
For any sub-block count `B ≥ 1` and remainder `0 ≤ t ≤ B`, `4 t(B - t)` plus the single
ordinary squared difference `|2t - B|^2 = (2t - B)^2 + (B - 2t)^2` (under `ℕ` truncated subtraction) equals `B^2`, so
`4 t(B - t) ≤ B^2`. That integer identity and inequality are all this lemma proves. (In the
withdrawn manuscript it fed an "integrality excess" step; an independent review found that such
an excess cannot raise the relevant quadratic coefficient, so the lemma does not support the
closure argument.)
-/
theorem erdos_41.variants.normalized_integrality_excess_bound_b3 (B t : ℕ) (ht : t ≤ B) :
    4 * (t * (B - t)) + (2 * t - B) * (2 * t - B) + (B - 2 * t) * (B - 2 * t) = B * B ∧
    4 * (t * (B - t)) ≤ B * B := by
  have h_split : 2 * t ≤ B ∨ B ≤ 2 * t := Nat.le_total (2 * t) B
  rcases h_split with h_lo | h_hi
  · have h_zero : 2 * t - B = 0 := Nat.sub_eq_zero_of_le h_lo
    rw [h_zero]
    have h_sum : (B - 2 * t) + 2 * t = B := Nat.sub_add_cancel h_lo
    have h_alg : 4 * (t * (B - t)) + (B - 2 * t) * (B - 2 * t) = B * B := by
      calc
        4 * (t * (B - t)) + (B - 2 * t) * (B - 2 * t)
          = (2 * t) * (2 * (B - t)) + (B - 2 * t) * (B - 2 * t) := by
            have h4 : 4 * (t * (B - t)) = (2 * t) * (2 * (B - t)) := by
              calc
                4 * (t * (B - t)) = (2 * 2) * (t * (B - t)) := rfl
                _ = (2 * t) * (2 * (B - t)) := by ac_rfl
            rw [h4]
        _ = (2 * t) * ((B - 2 * t) + B) + (B - 2 * t) * (B - 2 * t) := by
            have h2 : 2 * (B - t) = (B - 2 * t) + B := by omega
            rw [h2]
        _ = (2 * t) * (B - 2 * t) + (2 * t) * B + (B - 2 * t) * (B - 2 * t) := by
            rw [Nat.mul_add]
        _ = ((B - 2 * t) + 2 * t) * (B - 2 * t) + (2 * t) * B := by
            rw [Nat.add_mul]
            omega
        _ = B * (B - 2 * t) + B * (2 * t) := by
            rw [h_sum, Nat.mul_comm (2 * t) B]
        _ = B * ((B - 2 * t) + 2 * t) := by
            rw [← Nat.mul_add]
        _ = B * B := by
            rw [h_sum]
    omega
  · have h_zero : B - 2 * t = 0 := Nat.sub_eq_zero_of_le h_hi
    rw [h_zero]
    have h_2t : (2 * t - B) + B = 2 * t := Nat.sub_add_cancel h_hi
    have h_alg : 4 * (t * (B - t)) + (2 * t - B) * (2 * t - B) = B * B := by
      calc
        4 * (t * (B - t)) + (2 * t - B) * (2 * t - B)
          = (2 * t) * (2 * (B - t)) + (2 * t - B) * (2 * t - B) := by
            have h4 : 4 * (t * (B - t)) = (2 * t) * (2 * (B - t)) := by
              calc
                4 * (t * (B - t)) = (2 * 2) * (t * (B - t)) := rfl
                _ = (2 * t) * (2 * (B - t)) := by ac_rfl
            rw [h4]
        _ = ((2 * t - B) + B) * (2 * (B - t)) + (2 * t - B) * (2 * t - B) := by
            rw [h_2t]
        _ = (2 * t - B) * (2 * (B - t)) + B * (2 * (B - t)) + (2 * t - B) * (2 * t - B) := by
            rw [Nat.add_mul]
        _ = (2 * t - B) * (2 * (B - t) + (2 * t - B)) + B * (2 * (B - t)) := by
            rw [Nat.mul_add]
            omega
        _ = (2 * t - B) * B + B * (2 * (B - t)) := by
            have h_in : 2 * (B - t) + (2 * t - B) = B := by omega
            rw [h_in]
        _ = B * ((2 * t - B) + 2 * (B - t)) := by
            rw [Nat.mul_comm (2 * t - B) B, ← Nat.mul_add]
        _ = B * B := by
            have h_in : (2 * t - B) + 2 * (B - t) = B := by omega
            rw [h_in]
    omega

/-! ## 14. Theorem 2.14(b)–(c): Hierarchical Binary Sub-Block Variance Splitting & Hyperfactorial Sawtooth Step -/

/--
**Theorem 2.14(b)–(c) (Binary Sub-Block Variance Refinement Identity & Hyperfactorial Sawtooth Abel Step):**
For any child sub-block occupancies `u, v ∈ ℕ` and integer period `m ≥ 1`,
`2(u^2 + v^2) = (u + v)^2 + |u - v|^2` (where `|u - v|^2 = (u - v)^2 + (v - u)^2` under `ℕ` truncated subtraction) and
`m(m + 1) - (m - 1)m = 2m`, together with `(u + v)^2 ≤ 2(u^2 + v^2)`.
These elementary identities are all this lemma proves. In particular it does not prove the
manuscript's sub-block variance refinement or any telescoping of `∫ {u}(1 - {u})/u` into
`2 ln H(M - 1)`; those were steps of the withdrawn closure argument.
-/
theorem erdos_41.variants.binary_subblock_variance_splitting_b3 (u v m : ℕ) (hm : 1 ≤ m) :
    2 * (u * u + v * v) =
      (u + v) * (u + v) + (u - v) * (u - v) + (v - u) * (v - u) ∧
    (u + v) * (u + v) ≤ 2 * (u * u + v * v) ∧
    m * (m + 1) - (m - 1) * m = 2 * m := by
  have h_abel : m * (m + 1) - (m - 1) * m = 2 * m := by
    cases m with
    | zero => omega
    | succ k =>
      simp [Nat.add_mul, Nat.mul_add]
      omega
  have h_le : u ≤ v ∨ v ≤ u := Nat.le_total u v
  rcases h_le with huv | hvu
  · have h_z : u - v = 0 := Nat.sub_eq_zero_of_le huv
    rw [h_z]
    have h_id : (u + v) * (u + v) + (v - u) * (v - u) = 2 * (u * u + v * v) := by
      have h_sub : u + (v - u) = v := Nat.add_sub_of_le huv
      calc
        (u + v) * (u + v) + (v - u) * (v - u)
          = (2 * u + (v - u)) * (2 * u + (v - u)) + (v - u) * (v - u) := by
            have h_s : u + v = 2 * u + (v - u) := by omega
            rw [h_s]
        _ = 4 * (u * u) + 4 * (u * (v - u)) + 2 * ((v - u) * (v - u)) := by
            have h_exp : (2 * u + (v - u)) * (2 * u + (v - u)) =
                4 * (u * u) + 4 * (u * (v - u)) + (v - u) * (v - u) := by
              calc
                (2 * u + (v - u)) * (2 * u + (v - u))
                  = (2 * u) * (2 * u) + (2 * u) * (v - u) + ((v - u) * (2 * u) + (v - u) * (v - u)) := by
                    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
                _ = 4 * (u * u) + 2 * (u * (v - u)) + 2 * (u * (v - u)) + (v - u) * (v - u) := by
                    have ha : (2 * u) * (2 * u) = (2 * 2) * (u * u) := by ac_rfl
                    have hb : (2 * u) * (v - u) = 2 * (u * (v - u)) := by ac_rfl
                    have hc : (v - u) * (2 * u) = 2 * (u * (v - u)) := by ac_rfl
                    rw [ha, hb, hc]
                    omega
                _ = 4 * (u * u) + 4 * (u * (v - u)) + (v - u) * (v - u) := by omega
            omega
        _ = 2 * (u * u + (u * u + 2 * (u * (v - u)) + (v - u) * (v - u))) := by omega
        _ = 2 * (u * u + v * v) := by
            have h_v2 : v * v = u * u + 2 * (u * (v - u)) + (v - u) * (v - u) := by
              calc
                v * v = (u + (v - u)) * (u + (v - u)) := by rw [h_sub]
                _ = u * u + u * (v - u) + ((v - u) * u + (v - u) * (v - u)) := by
                    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
                _ = u * u + 2 * (u * (v - u)) + (v - u) * (v - u) := by
                    rw [Nat.mul_comm (v - u) u]
                    omega
            rw [h_v2]
    exact ⟨by omega, by omega, h_abel⟩
  · have h_z : v - u = 0 := Nat.sub_eq_zero_of_le hvu
    rw [h_z]
    have h_id : (u + v) * (u + v) + (u - v) * (u - v) = 2 * (u * u + v * v) := by
      have h_sub : v + (u - v) = u := Nat.add_sub_of_le hvu
      calc
        (u + v) * (u + v) + (u - v) * (u - v)
          = (2 * v + (u - v)) * (2 * v + (u - v)) + (u - v) * (u - v) := by
            have h_s : u + v = 2 * v + (u - v) := by omega
            rw [h_s]
        _ = 4 * (v * v) + 4 * (v * (u - v)) + 2 * ((u - v) * (u - v)) := by
            have h_exp : (2 * v + (u - v)) * (2 * v + (u - v)) =
                4 * (v * v) + 4 * (v * (u - v)) + (u - v) * (u - v) := by
              calc
                (2 * v + (u - v)) * (2 * v + (u - v))
                  = (2 * v) * (2 * v) + (2 * v) * (u - v) + ((u - v) * (2 * v) + (u - v) * (u - v)) := by
                    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
                _ = 4 * (v * v) + 2 * (v * (u - v)) + 2 * (v * (u - v)) + (u - v) * (u - v) := by
                    have ha : (2 * v) * (2 * v) = (2 * 2) * (v * v) := by ac_rfl
                    have hb : (2 * v) * (u - v) = 2 * (v * (u - v)) := by ac_rfl
                    have hc : (u - v) * (2 * v) = 2 * (v * (u - v)) := by ac_rfl
                    rw [ha, hb, hc]
                    omega
                _ = 4 * (v * v) + 4 * (v * (u - v)) + (u - v) * (u - v) := by omega
            omega
        _ = 2 * ((v * v + 2 * (v * (u - v)) + (u - v) * (u - v)) + v * v) := by omega
        _ = 2 * (u * u + v * v) := by
            have h_u2 : u * u = v * v + 2 * (v * (u - v)) + (u - v) * (u - v) := by
              calc
                u * u = (v + (u - v)) * (v + (u - v)) := by rw [h_sub]
                _ = v * v + v * (u - v) + ((u - v) * v + (u - v) * (u - v)) := by
                    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
                _ = v * v + 2 * (v * (u - v)) + (u - v) * (u - v) := by
                    rw [Nat.mul_comm (u - v) v]
                    omega
            rw [h_u2]
    exact ⟨by omega, by omega, h_abel⟩

/-! ## 15 & 16. Decidable Kernel Verification of OEIS A004023 Greedy Prefix & OEIS A051912 Optimal B₃ Rulers -/

def isStrictlyIncreasing : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => (a < b) && isStrictlyIncreasing (b :: rest)

/-- Fixed-depth binary radix trie over `ℕ` for `O(N log(max A))` kernel-decidable duplicate detection. -/
inductive BitTrie where
  | empty : BitTrie
  | node : Bool → BitTrie → BitTrie → BitTrie

def BitTrie.insert (depth x : ℕ) (t : BitTrie) : Bool × BitTrie :=
  match depth with
  | 0 =>
    match t with
    | .empty => (true, .node true .empty .empty)
    | .node seen l r => (!seen, .node true l r)
  | d + 1 =>
    let bit := (x % 2 == 1)
    let x' := x / 2
    match t with
    | .empty =>
      if bit then
        let res := BitTrie.insert d x' .empty
        (res.1, .node false .empty res.2)
      else
        let res := BitTrie.insert d x' .empty
        (res.1, .node false res.2 .empty)
    | .node seen l r =>
      if bit then
        let res := BitTrie.insert d x' r
        (res.1, .node seen l res.2)
      else
        let res := BitTrie.insert d x' l
        (res.1, .node seen res.2 r)

def hasNoDuplicatesAux : List ℕ → BitTrie → Bool
  | [], _ => true
  | x :: rest, t =>
    let res := BitTrie.insert 12 x t
    res.1 && hasNoDuplicatesAux rest res.2

def hasNoDuplicates (l : List ℕ) : Bool :=
  hasNoDuplicatesAux l .empty

/-- All ordered 3-sums `a + b + c` (`a ≤ b ≤ c`) with fixed first element `a`. -/
def threeSumsWithFirst (a : ℕ) : List ℕ → List ℕ
  | [] => []
  | b :: rest => (b :: rest).map (fun c => a + b + c) ++ threeSumsWithFirst a rest

/-- All `C(|A|+2, 3)` ordered 3-sums `a_i + a_j + a_k` (`1 ≤ i ≤ j ≤ k ≤ |A|`). -/
def allOrderedThreeSums : List ℕ → List ℕ
  | [] => []
  | a :: rest => threeSumsWithFirst a (a :: rest) ++ allOrderedThreeSums rest

/-- Boolean `B_3` legality checker over a finite list of strictly increasing positive integers. -/
def isCertifiedB3 (A : List ℕ) : Bool :=
  (A.all (fun x => 1 ≤ x)) && isStrictlyIncreasing A && hasNoDuplicates (allOrderedThreeSums A)

/--
**Theorem 3.1 / Table 1 (Greedy `B_3` Sequence Prefix Verification — OEIS `A096772`):**
Machine-checked proof that the first 10 terms of the greedy infinite `B_3` sequence (OEIS `A096772`;
the manuscript's citation of `A004023` was wrong, as that sequence lists indices of prime repunits)
`[1, 2, 5, 14, 33, 72, 125, 219, 376, 573]` form a valid `B_3` sequence with all
`C(10 + 2, 3) = 220` ordered 3-sums pairwise distinct.
-/
def greedyB3Prefix10 : List ℕ := [1, 2, 5, 14, 33, 72, 125, 219, 376, 573]

set_option maxRecDepth 200000 in
theorem greedyB3Prefix10_is_b3 :
    isCertifiedB3 greedyB3Prefix10 = true ∧
    (allOrderedThreeSums greedyB3Prefix10).length = 220 := by
  decide

/--
**Theorem 3.1 / Table 1 (Finite `B_3` Witness Verification for `k ∈ {7, 8, 9, 10}`):**
Machine-checked proof that the following lists are `B_3` sets. Only the `B_3` property is checked.
Their claimed optimality (minimal span) is not verified here, despite the `optimal` in the names,
and the manuscript's Table 3 entries for `k = 3..7` are not `B_3` sets at all (for example,
`[1, 2, 4]` has `1 + 1 + 4 = 2 + 2 + 2`). The manuscript's `A051912` citation is also wrong, since
that sequence is the greedy `B_3` sequence shifted to start at 0. The witnesses:
- `A_7^* = [1, 2, 8, 51, 60, 79, 83]` on `{1, ..., 83}` (`L(7) = 82`, `C(9, 3) = 84` sums),
- `A_8^* = [1, 2, 33, 88, 103, 113, 132, 140]` on `{1, ..., 140}` (`L(8) = 139`, `C(10, 3) = 120` sums),
- `A_9^* = [1, 7, 38, 40, 119, 180, 201, 218, 227]` on `{1, ..., 227}` (`L(9) = 226`, `C(11, 3) = 165` sums), and
- `A_10^* = [1, 4, 11, 20, 35, 124, 193, 270, 334, 345]` on `{1, ..., 345}` (`L(10) = 344`, `C(12, 3) = 220` sums)
are valid `B_3` sequences with all ordered 3-sums pairwise distinct.
-/
def optimalB3RulerN83 : List ℕ := [1, 2, 8, 51, 60, 79, 83]
def optimalB3RulerN140 : List ℕ := [1, 2, 33, 88, 103, 113, 132, 140]
def optimalB3RulerN227 : List ℕ := [1, 7, 38, 40, 119, 180, 201, 218, 227]
def optimalB3RulerN345 : List ℕ := [1, 4, 11, 20, 35, 124, 193, 270, 334, 345]

set_option maxRecDepth 200000 in
theorem optimalB3RulerN345_is_b3 :
    isCertifiedB3 optimalB3RulerN345 = true ∧
    (allOrderedThreeSums optimalB3RulerN345).length = 220 ∧
    isCertifiedB3 optimalB3RulerN227 = true ∧
    (allOrderedThreeSums optimalB3RulerN227).length = 165 ∧
    isCertifiedB3 optimalB3RulerN140 = true ∧
    (allOrderedThreeSums optimalB3RulerN140).length = 120 ∧
    isCertifiedB3 optimalB3RulerN83 = true ∧
    (allOrderedThreeSums optimalB3RulerN83).length = 84 := by
  decide

end Erdos41
