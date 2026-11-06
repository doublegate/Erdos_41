/-
Copyright 2026 Lucas Parobek.
Licensed under the Apache License, Version 2.0.

Formalization of Theorem 1 of "A liminf bound for infinite B₃ sequences"
(`erdos41/b3_liminf/paper/b3_liminf.tex`):

  every infinite B₃ set `A` of positive integers satisfies
  `liminf_{x → ∞} A(x) / x^{1/3} ≤ 3^{1/3}`, where `A(x) = |A ∩ [1, x]|`.

The proof follows the paper (Lemmas 1–3 and Section 3), with 0-based indices:
the paper's `a_r` (`r ≥ 1`) is `a (r - 1)` here, and the paper's index set
`𝓘_m = {(i, j, k) : 1 ≤ i ≤ j ≤ m, 1 ≤ k < j, k ≠ i}` is `idx m` below,
whose elements are written `⟨j, i, k⟩` with `j < m`, `i ≤ j`, `k < j`, `k ≠ i`.

* Lemma 1 (`w_injOn`): `w(i, j, k) = a_i + a_j - a_k` is injective on `𝓘_m`, with values `≥ 1`.
* Lemma 2 (`sum_w_eq`, `card_idx`): `∑_{𝓘_m} w = ∑_{r ≤ m} (r² - m) a_r`, `|𝓘_m| = ∑_{j < m} j²`.
* Lemma 3 is inlined: the density hypothesis is `d · a_r ≤ (r + 1)³` for all large `r`.
* Theorem 1: `theorem1` (explicit form) and `theorem1_liminf` (with `Filter.liminf`).
* The window condition (R) (`CountR`): `countR_of_B3` shows every B₃ sequence satisfies it, and
  `seq_false_of_countR` proves the sequence form of Theorem 1 from (R) alone, via the sorting
  lemma `card_mul_succ_le_two_mul_sum_of_count`. This machine-checks, for Theorem 1, the
  observation behind Proposition 5.2: the argument uses `B₃` only through (R).

Theorem 2 of the paper (the constant `K^{-1/3} ≈ 1.19986`) is NOT formalized here.
-/
import Mathlib

open Finset Filter

namespace B3Liminf

/-- `A ⊆ ℕ` is a `B₃` set: a sum of three elements of `A` (repetition allowed) determines the
three summands up to order. -/
def IsB3 (A : Set ℕ) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, ∀ x' ∈ A, ∀ y' ∈ A, ∀ z' ∈ A,
    x + y + z = x' + y' + z' → ({x, y, z} : Multiset ℕ) = {x', y', z'}

/-- The counting function `A(x) = |A ∩ [1, x]|`. -/
noncomputable def countUpTo (A : Set ℕ) (x : ℕ) : ℕ := (A ∩ Set.Icc 1 x).ncard

/-! ### Elementary sums -/

/-- `N` distinct positive integers have sum at least `N(N + 1)/2`. -/
theorem card_mul_succ_le_two_mul_sum (S : Finset ℕ) (h0 : 0 ∉ S) :
    S.card * (S.card + 1) ≤ 2 * ∑ x ∈ S, x := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have h0s : 0 ∉ s := fun h => h0 (Finset.mem_insert_of_mem h)
    have ha0 : a ≠ 0 := fun h => h0 (h ▸ Finset.mem_insert_self a s)
    have hsub : s ⊆ Finset.Ioo 0 a := by
      intro x hx
      rw [Finset.mem_Ioo]
      exact ⟨Nat.pos_of_ne_zero (fun h => h0s (h ▸ hx)), hlt x hx⟩
    have hcard : s.card ≤ a - 1 := by
      simpa [Nat.card_Ioo] using Finset.card_le_card hsub
    have := ih h0s
    rw [Finset.card_insert_of_notMem ha, Finset.sum_insert ha]
    have hca : s.card + 1 ≤ a := by omega
    nlinarith

/-- The same bound for an injective positive function on a finite set. -/
theorem card_mul_succ_le_two_mul_sum_of_injOn {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℕ) (hinj : Set.InjOn f s) (hpos : ∀ x ∈ s, 1 ≤ f x) :
    s.card * (s.card + 1) ≤ 2 * ∑ x ∈ s, f x := by
  have h1 : ∑ x ∈ s, f x = ∑ y ∈ s.image f, y := by rw [Finset.sum_image hinj]
  have h2 : (s.image f).card = s.card := Finset.card_image_of_injOn hinj
  have h0 : 0 ∉ s.image f := by
    simp only [Finset.mem_image, not_exists, not_and]
    intro x hx hfx
    have := hpos x hx
    omega
  rw [h1, ← h2]
  exact card_mul_succ_le_two_mul_sum _ h0

/-- The bound `(★)` from the window condition alone: if at most `H` of the values `f t`
(`t ∈ s`) are `≤ H`, for every `H`, then `|s|(|s| + 1) ≤ 2 ∑ f`. (Sorting: the `n`-th smallest
value is at least `n`.) -/
theorem card_mul_succ_le_two_mul_sum_of_count {ι : Type*} [DecidableEq ι] (f : ι → ℕ) :
    ∀ s : Finset ι, (∀ H, (s.filter (fun t => f t ≤ H)).card ≤ H) →
      s.card * (s.card + 1) ≤ 2 * ∑ t ∈ s, f t := by
  intro s
  induction s using Finset.induction_on_max_value f with
  | empty => intro _; simp
  | insert a s ha hmax ih =>
    intro h
    have hs : ∀ H, (s.filter (fun t => f t ≤ H)).card ≤ H := fun H =>
      (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert a s))).trans (h H)
    have h1 := ih hs
    -- every element of `insert a s` has value `≤ f a`, so the whole set is counted at `H = f a`
    have hall : (insert a s).filter (fun t => f t ≤ f a) = insert a s := by
      apply Finset.filter_true_of_mem
      intro t ht
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact le_rfl
      · exact hmax t ht
    have hca : (insert a s).card ≤ f a := by
      have := h (f a); rwa [hall] at this
    rw [Finset.card_insert_of_notMem ha, Finset.sum_insert ha] at *
    nlinarith

/-- `∑_{r=1}^{m} r⁵ ≤ (m + 1)⁶ / 6`. -/
theorem sum_pow_five_le (m : ℕ) :
    ∑ r ∈ range m, ((r : ℝ) + 1) ^ 5 ≤ ((m : ℝ) + 1) ^ 6 / 6 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.sum_range_succ]
    push_cast
    set y : ℝ := (m : ℝ) + 1 with hy
    have hy0 : 0 ≤ y := by positivity
    have key : (y + 1) ^ 6 - (y ^ 6 + 6 * y ^ 5) = 15 * y ^ 4 + 20 * y ^ 3 + 15 * y ^ 2 + 6 * y + 1 := by
      ring
    have hpos : 0 ≤ 15 * y ^ 4 + 20 * y ^ 3 + 15 * y ^ 2 + 6 * y + 1 := by positivity
    have : (m : ℝ) + 1 + 1 = y + 1 := by rw [hy]
    rw [this]
    linarith

/-- `n³ ≤ 3 ∑_{j ≤ n} j²`. -/
theorem pow_three_le_three_mul_sum_sq (n : ℕ) :
    (n : ℝ) ^ 3 ≤ 3 * ∑ j ∈ range (n + 1), ((j * j : ℕ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast at ih ⊢
    have hn : (0 : ℝ) ≤ n := by positivity
    nlinarith

/-! ### The index set `𝓘_m` and Lemmas 1 and 2 -/

/-- The index set `𝓘_m`, as triples `⟨j, i, k⟩` with `j < m`, `i ≤ j`, `k < j`, `k ≠ i`. -/
def idx (m : ℕ) : Finset (Σ _ : ℕ, Σ _ : ℕ, ℕ) :=
  (range m).sigma fun j => (range (j + 1)).sigma fun i => (range j).erase i

theorem mem_idx {m : ℕ} {j i k : ℕ} :
    (⟨j, i, k⟩ : Σ _ : ℕ, Σ _ : ℕ, ℕ) ∈ idx m ↔ j < m ∧ i ≤ j ∧ k ≠ i ∧ k < j := by
  simp [idx, Finset.mem_sigma]

/-- `w(i, j, k) = a_i + a_j - a_k` on an index triple `⟨j, i, k⟩`. -/
def w (a : ℕ → ℕ) (t : Σ _ : ℕ, Σ _ : ℕ, ℕ) : ℕ := a t.2.1 + a t.1 - a t.2.2

theorem card_idx (m : ℕ) : (idx m).card = ∑ j ∈ range m, j * j := by
  rw [idx, Finset.card_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.card_sigma, Finset.sum_range_succ,
    Finset.erase_eq_of_notMem Finset.notMem_range_self, Finset.card_range]
  have : ∀ i ∈ range j, ((range j).erase i).card = j - 1 := fun i hi => by
    rw [Finset.card_erase_of_mem hi, Finset.card_range]
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, smul_eq_mul]
  cases j with
  | zero => simp
  | succ j => simp; ring

section Sequence

variable (a : ℕ → ℕ) (ha : StrictMono a) (h1 : 1 ≤ a 0)
  (hB : ∀ i j k i' j' k' : ℕ, a i + a j + a k = a i' + a j' + a k' →
    ({i, j, k} : Multiset ℕ) = {i', j', k'})

include ha h1 in
/-- Positivity part of Lemma 1: `w ≥ 1` on `𝓘_m`. -/
theorem one_le_w {m : ℕ} : ∀ t ∈ idx m, 1 ≤ w a t := by
  rintro ⟨j, i, k⟩ ht
  rw [mem_idx] at ht
  have hkj : a k < a j := ha ht.2.2.2
  have hi : a 0 ≤ a i := ha.monotone (Nat.zero_le i)
  simp only [w]
  omega

include ha hB in
/-- Lemma 1: `w` is injective on `𝓘_m`. -/
theorem w_injOn {m : ℕ} : Set.InjOn (w a) (idx m : Set (Σ _ : ℕ, Σ _ : ℕ, ℕ)) := by
  rintro ⟨j, i, k⟩ ht ⟨j', i', k'⟩ ht' hw
  rw [Finset.mem_coe, mem_idx] at ht ht'
  obtain ⟨-, hij, hki, hkj⟩ := ht
  obtain ⟨-, hij', hki', hkj'⟩ := ht'
  have hak : a k < a j := ha hkj
  have hak' : a k' < a j' := ha hkj'
  simp only [w] at hw
  have hsum : a i + a j + a k' = a i' + a j' + a k := by omega
  have hM := hB i j k' i' j' k hsum
  have m1 : k ∈ ({i, j, k'} : Multiset ℕ) := by rw [hM]; simp
  have m2 : k' ∈ ({i', j', k} : Multiset ℕ) := by rw [← hM]; simp
  have m3 : i ∈ ({i', j', k} : Multiset ℕ) := by rw [← hM]; simp
  have m4 : j ∈ ({i', j', k} : Multiset ℕ) := by rw [← hM]; simp
  have m5 : i' ∈ ({i, j, k'} : Multiset ℕ) := by rw [hM]; simp
  have m6 : j' ∈ ({i, j, k'} : Multiset ℕ) := by rw [hM]; simp
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at m1 m2 m3 m4 m5 m6
  have hi : i = i' := by omega
  have hj : j = j' := by omega
  have hk : k = k' := by omega
  subst hi hj hk
  rfl

/-- The contribution of the layer `j` (paper: `j + 1`) to `∑ w`. -/
theorem layer_sum (j : ℕ) :
    ∑ i ∈ range (j + 1), ∑ k ∈ (range j).erase i, ((a i : ℝ) + a j - a k) =
      ((j : ℝ) ^ 2 + j) * a j - ∑ k ∈ range j, (a k : ℝ) := by
  have h : ∀ i ∈ range j, ∑ k ∈ (range j).erase i, ((a i : ℝ) + a j - a k) =
      ∑ k ∈ range j, ((a i : ℝ) + a j - a k) - ((a i : ℝ) + a j - a i) :=
    fun i hi => Finset.sum_erase_eq_sub hi
  rw [Finset.sum_range_succ, Finset.sum_congr rfl h,
    Finset.erase_eq_of_notMem Finset.notMem_range_self]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, add_sub_cancel_left]
  rw [← Finset.mul_sum]
  ring

/-- Lemma 2, in the form used: `∑_{j < m} (layer j) = ∑_{r < m} ((r + 1)² - m) a_r`. -/
theorem layers_sum (m : ℕ) :
    ∑ j ∈ range m, ∑ i ∈ range (j + 1), ∑ k ∈ (range j).erase i, ((a i : ℝ) + a j - a k) =
      ∑ r ∈ range m, (((r : ℝ) + 1) ^ 2 - m) * a r := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, layer_sum, Finset.sum_range_succ (fun r => (((r : ℝ) + 1) ^ 2 - _) * a r)]
    have : ∑ r ∈ range m, (((r : ℝ) + 1) ^ 2 - ((m + 1 : ℕ) : ℝ)) * a r =
        ∑ r ∈ range m, (((r : ℝ) + 1) ^ 2 - m) * a r - ∑ r ∈ range m, (a r : ℝ) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      push_cast
      ring
    rw [this]
    push_cast
    ring

include ha in
/-- Lemma 2: `∑_{𝓘_m} w = ∑_{r < m} ((r + 1)² - m) a_r`. -/
theorem sum_w_eq (m : ℕ) :
    ((∑ t ∈ idx m, w a t : ℕ) : ℝ) = ∑ r ∈ range m, (((r : ℝ) + 1) ^ 2 - m) * a r := by
  rw [← layers_sum, idx, Nat.cast_sum, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkj : k < j := Finset.mem_range.1 (Finset.mem_of_mem_erase hk)
  have : a k ≤ a i + a j := (ha hkj).le.trans (Nat.le_add_left _ _)
  simp only [w]
  rw [Nat.cast_sub this]
  push_cast
  ring

/-- Existence of a large `n` with `3 (n + 2)⁶ < d n⁶`, for `d > 3`. -/
theorem exists_large (d : ℝ) (hd : 3 < d) (n₀ : ℕ) :
    ∃ n : ℕ, n₀ ≤ n ∧ 1 ≤ n ∧ 3 * ((n : ℝ) + 2) ^ 6 < d * (n : ℝ) ^ 6 := by
  have htend : Tendsto (fun n : ℕ => (1 + (2 : ℝ) / n) ^ 6) atTop (nhds 1) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).add
      (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ))).pow 6
    simpa using this
  have hev := htend.eventually_lt_const (by linarith : (1 : ℝ) < d / 3)
  obtain ⟨n, hlt, hn⟩ := (hev.and (eventually_ge_atTop (max n₀ 1))).exists
  refine ⟨n, le_of_max_le_left hn, le_of_max_le_right hn, ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  have hnpos : (0 : ℝ) < n := by linarith
  have : (1 + (2 : ℝ) / n) = ((n : ℝ) + 2) / n := by field_simp
  rw [this, div_pow, div_lt_iff₀ (by positivity)] at hlt
  linarith

/-- The window condition (R) of the paper, in finitary form: for every `m` and `H`, at most `H`
of the values `w(i, j, k) = a_i + a_j - a_k` over the index set `𝓘_m` are `≤ H`. -/
def CountR : Prop := ∀ m H : ℕ, ((idx m).filter (fun t => w a t ≤ H)).card ≤ H

include ha h1 hB in
/-- Lemma 1 gives (R): every `B₃` sequence satisfies the window condition. -/
theorem countR_of_B3 : CountR a := by
  intro m H
  have hinj : Set.InjOn (w a) ((idx m).filter (fun t => w a t ≤ H) : Set _) :=
    (w_injOn a ha hB).mono (by intro t ht; exact (Finset.mem_filter.1 ht).1)
  have hsub : ((idx m).filter (fun t => w a t ≤ H)).image (w a) ⊆ Finset.Icc 1 H := by
    intro v hv
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨htm, htH⟩ := Finset.mem_filter.1 ht
    exact Finset.mem_Icc.2 ⟨one_le_w a ha h1 t htm, htH⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Nat.card_Icc] at this
  omega

include ha in
/-- Theorem 1, sequence form, under the window condition (R) only: no strictly increasing sequence
of naturals satisfying (R) has `d · a_r ≤ (r + 1)³` for all large `r` with `d > 3`. This is the
Lean counterpart of the observation behind Proposition 5.2: the proof uses `B₃` only through (R). -/
theorem seq_false_of_countR (hR : CountR a) (d : ℝ) (hd : 3 < d) (r₀ : ℕ)
    (hden : ∀ r, r₀ ≤ r → d * a r ≤ ((r : ℝ) + 1) ^ 3) : False := by
  obtain ⟨n, hn₀, hn1, hlt⟩ := exists_large d hd ((r₀ + 1) ^ 2)
  set m := n + 1 with hm
  set N := (idx m).card with hN
  set S := ∑ t ∈ idx m, w a t with hS
  have hd0 : 0 < d := by linarith
  -- lower bound from (R)
  have hlow : N * (N + 1) ≤ 2 * S :=
    card_mul_succ_le_two_mul_sum_of_count (w a) (idx m) (hR m)
  have hlowR : (N : ℝ) * (N + 1) ≤ 2 * (S : ℝ) := by exact_mod_cast hlow
  -- upper bound from Lemma 2 and the density hypothesis
  have hterm : ∀ r ∈ range m, (((r : ℝ) + 1) ^ 2 - m) * a r ≤ ((r : ℝ) + 1) ^ 5 / d := by
    intro r _
    have har : (0 : ℝ) ≤ a r := by positivity
    by_cases hc : ((r : ℝ) + 1) ^ 2 ≤ m
    · have : (((r : ℝ) + 1) ^ 2 - m) * a r ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) har
      exact this.trans (by positivity)
    · push Not at hc
      have hmr : ((r₀ + 1) ^ 2 : ℕ) < ((r + 1) ^ 2 : ℕ) := by
        have : ((r₀ + 1) ^ 2 : ℕ) ≤ m := by omega
        exact_mod_cast (show (((r₀ + 1) ^ 2 : ℕ) : ℝ) < (((r + 1) ^ 2 : ℕ) : ℝ) by
          push_cast at this ⊢
          have : (((r₀ : ℝ) + 1) ^ 2) ≤ m := by exact_mod_cast this
          linarith)
      have hr : r₀ ≤ r := by
        have := (Nat.pow_lt_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).1 hmr
        omega
      have hden' := hden r hr
      have hc0 : 0 < ((r : ℝ) + 1) ^ 2 - m := by linarith
      have hcle : ((r : ℝ) + 1) ^ 2 - m ≤ ((r : ℝ) + 1) ^ 2 := by
        have : (0 : ℝ) ≤ m := by positivity
        linarith
      rw [le_div_iff₀ hd0]
      have e1 : (((r : ℝ) + 1) ^ 2 - m) * (d * a r) ≤ (((r : ℝ) + 1) ^ 2 - m) * ((r : ℝ) + 1) ^ 3 :=
        mul_le_mul_of_nonneg_left hden' hc0.le
      have e2 : (((r : ℝ) + 1) ^ 2 - m) * ((r : ℝ) + 1) ^ 3 ≤ ((r : ℝ) + 1) ^ 2 * ((r : ℝ) + 1) ^ 3 :=
        mul_le_mul_of_nonneg_right hcle (by positivity)
      nlinarith
  have hup : (S : ℝ) ≤ ((m : ℝ) + 1) ^ 6 / (6 * d) := by
    rw [hS, sum_w_eq a ha m]
    calc ∑ r ∈ range m, (((r : ℝ) + 1) ^ 2 - m) * a r
        ≤ ∑ r ∈ range m, ((r : ℝ) + 1) ^ 5 / d := Finset.sum_le_sum hterm
      _ = (∑ r ∈ range m, ((r : ℝ) + 1) ^ 5) / d := by rw [Finset.sum_div]
      _ ≤ (((m : ℝ) + 1) ^ 6 / 6) / d := by gcongr; exact sum_pow_five_le m
      _ = ((m : ℝ) + 1) ^ 6 / (6 * d) := by rw [div_div]
  -- the count `N = |𝓘_m|`
  have hNlow : (n : ℝ) ^ 3 ≤ 3 * (N : ℝ) := by
    have := pow_three_le_three_mul_sum_sq n
    rw [hN, card_idx, hm]
    push_cast at this ⊢
    exact this
  -- combine: d n⁶ ≤ 3 (n + 2)⁶
  have hmR : (m : ℝ) + 1 = (n : ℝ) + 2 := by rw [hm]; push_cast; ring
  rw [hmR] at hup
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hn3 : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
  have hsq : ((n : ℝ) ^ 3) ^ 2 ≤ (3 * (N : ℝ)) ^ 2 := pow_le_pow_left₀ hn3 hNlow 2
  have hN2 : 3 * d * (N : ℝ) ^ 2 ≤ ((n : ℝ) + 2) ^ 6 := by
    have : (N : ℝ) ^ 2 ≤ 2 * (S : ℝ) := by nlinarith
    have h6 : 2 * (S : ℝ) * (3 * d) ≤ ((n : ℝ) + 2) ^ 6 := by
      rw [le_div_iff₀ (by positivity)] at hup
      linarith
    nlinarith
  nlinarith


include ha h1 hB in
/-- Theorem 1, sequence form: no strictly increasing B₃ sequence of positive integers satisfies
`d · a_r ≤ (r + 1)³` for all large `r` with `d > 3`. -/
theorem seq_false (d : ℝ) (hd : 3 < d) (r₀ : ℕ)
    (hden : ∀ r, r₀ ≤ r → d * a r ≤ ((r : ℝ) + 1) ^ 3) : False :=
  seq_false_of_countR a ha (countR_of_B3 a ha h1 hB) d hd r₀ hden

end Sequence

/-! ### From sets to sequences -/

theorem countUpTo_nth {A : Set ℕ} (hA : A.Infinite) (h0 : 0 ∉ A) (r : ℕ) :
    countUpTo A (Nat.nth (· ∈ A) r) = r + 1 := by
  have hA' : (Set.ofPred (· ∈ A)).Infinite := hA
  have hmono := Nat.nth_strictMono hA'
  have hset : A ∩ Set.Icc 1 (Nat.nth (· ∈ A) r) = Nat.nth (· ∈ A) '' Set.Iic r := by
    ext x
    constructor
    · rintro ⟨hxA, hx1, hxr⟩
      have : x ∈ Set.range (Nat.nth (· ∈ A)) := by
        rw [Nat.range_nth_of_infinite hA']; exact hxA
      obtain ⟨n, rfl⟩ := this
      exact ⟨n, hmono.le_iff_le.1 hxr, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      have hmem : Nat.nth (· ∈ A) n ∈ A := Nat.nth_mem_of_infinite hA' n
      refine ⟨hmem, ?_, hmono.monotone hn⟩
      exact Nat.one_le_iff_ne_zero.2 fun h => h0 (h ▸ hmem)
  rw [countUpTo, hset, Set.ncard_image_of_injective _ hmono.injective, ← Finset.coe_Iic,
    Set.ncard_coe_finset, Nat.card_Iic]

/-- **Theorem 1** (explicit form). For every infinite `B₃` set `A` of positive integers and every
`d > 3`, there are arbitrarily large `x` with `A(x)³ < d x`. Equivalently
`liminf_{x → ∞} A(x) x^{-1/3} ≤ 3^{1/3}` (see `theorem1_liminf`). -/
theorem theorem1 (A : Set ℕ) (hA : A.Infinite) (h0 : 0 ∉ A) (hB : IsB3 A)
    (d : ℝ) (hd : 3 < d) (x₀ : ℕ) :
    ∃ x, x₀ ≤ x ∧ ((countUpTo A x : ℕ) : ℝ) ^ 3 < d * x := by
  by_contra hcon
  push Not at hcon
  have hA' : (Set.ofPred (· ∈ A)).Infinite := hA
  set a := Nat.nth (· ∈ A) with ha_def
  have ha : StrictMono a := Nat.nth_strictMono hA'
  have hmem : ∀ n, a n ∈ A := Nat.nth_mem_of_infinite hA'
  have h1 : 1 ≤ a 0 := Nat.one_le_iff_ne_zero.2 fun h => h0 (h ▸ hmem 0)
  have hBa : ∀ i j k i' j' k' : ℕ, a i + a j + a k = a i' + a j' + a k' →
      ({i, j, k} : Multiset ℕ) = {i', j', k'} := by
    intro i j k i' j' k' hs
    have := hB _ (hmem i) _ (hmem j) _ (hmem k) _ (hmem i') _ (hmem j') _ (hmem k') hs
    apply Multiset.map_injective ha.injective
    simpa using this
  refine seq_false a ha h1 hBa d hd x₀ fun r hr => ?_
  have hx : x₀ ≤ a r := hr.trans (ha.id_le r)
  have := hcon (a r) hx
  rw [ha_def, countUpTo_nth hA h0 r] at this
  push_cast at this
  exact this

/-- From `theorem1`: for every `c > 0` with `c³ > 3`, `A(x) / x^{1/3} ≤ c` for infinitely many `x`. -/
theorem frequently_div_root_le (A : Set ℕ) (hA : A.Infinite) (h0 : 0 ∉ A) (hB : IsB3 A)
    (c : ℝ) (hc0 : 0 < c) (hcube : 3 < c ^ 3) :
    ∃ᶠ x : ℕ in atTop, ((countUpTo A x : ℕ) : ℝ) / (x : ℝ) ^ ((1 : ℝ) / 3) ≤ c := by
  rw [Filter.frequently_atTop]
  intro x₀
  obtain ⟨x, hx, hlt⟩ := theorem1 A hA h0 hB (c ^ 3) hcube (max x₀ 1)
  refine ⟨x, le_of_max_le_left hx, ?_⟩
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast le_of_max_le_right hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hroot : (0 : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  have hpow : ((x : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = x := by
    rw [one_div]; exact_mod_cast Real.rpow_inv_natCast_pow hx0.le (by norm_num)
  rw [div_le_iff₀ hroot]
  have hlt' : ((countUpTo A x : ℕ) : ℝ) ^ 3 < (c * (x : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 := by
    rw [mul_pow, hpow]; exact hlt
  exact (lt_of_pow_lt_pow_left₀ 3 (by positivity) hlt').le

/-- **Theorem 1** (liminf form): `liminf_{x → ∞} A(x) / x^{1/3} ≤ 3^{1/3}`.

`Filter.liminf` in `ℝ` returns a junk value (`0`) when the function tends to `+∞`, so the
inequality alone would not exclude a liminf of `+∞`. The first conjunct (the function is
cobounded below, i.e. it is `≤ 2` infinitely often) rules that out; together with
nonnegativity it makes this `Filter.liminf` the true liminf. -/
theorem theorem1_liminf (A : Set ℕ) (hA : A.Infinite) (h0 : 0 ∉ A) (hB : IsB3 A) :
    IsCoboundedUnder (· ≥ ·) atTop
        (fun x : ℕ => ((countUpTo A x : ℕ) : ℝ) / (x : ℝ) ^ ((1 : ℝ) / 3)) ∧
      Filter.liminf (fun x : ℕ => ((countUpTo A x : ℕ) : ℝ) / (x : ℝ) ^ ((1 : ℝ) / 3)) atTop ≤
        (3 : ℝ) ^ ((1 : ℝ) / 3) := by
  have hbdd : IsBoundedUnder (· ≥ ·) atTop
      (fun x : ℕ => ((countUpTo A x : ℕ) : ℝ) / (x : ℝ) ^ ((1 : ℝ) / 3)) :=
    isBoundedUnder_of ⟨0, fun x => by positivity⟩
  refine ⟨IsCoboundedUnder.of_frequently_le (a := 2)
    (frequently_div_root_le A hA h0 hB 2 (by norm_num) (by norm_num)), ?_⟩
  apply le_of_forall_gt_imp_ge_of_dense
  intro c hc
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  have hc0 : 0 < c := h3pos.trans hc
  have hcube : (3 : ℝ) < c ^ 3 := by
    have h := pow_lt_pow_left₀ hc h3pos.le (by norm_num : (3 : ℕ) ≠ 0)
    have e : ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = 3 := by
      rw [one_div]; exact_mod_cast Real.rpow_inv_natCast_pow (by norm_num) (by norm_num)
    rwa [e] at h
  exact Filter.liminf_le_of_frequently_le (frequently_div_root_le A hA h0 hB c hc0 hcube) hbdd

end B3Liminf
