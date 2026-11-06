/-
Copyright 2026 Lucas Parobek.
Licensed under the Apache License, Version 2.0.

Non-vacuity check for `B3Liminf.theorem1`: its hypotheses are satisfiable. The powers of 4
form an infinite `B₃` set of positive integers, so `theorem1` applies to at least one set.
(For this set the conclusion is far from tight: `A(x) ≈ log₄ x`.)
-/
import B3Liminf.Theorem1

namespace B3Liminf

/-- Fewer than four powers `4^x` with `x < e` sum to less than `4^e`. -/
theorem sum_pow_four_lt (M : Multiset ℕ) (hcard : Multiset.card M ≤ 3) (e : ℕ)
    (h : ∀ x ∈ M, x < e) : (M.map (4 ^ ·)).sum < 4 ^ e := by
  rcases e with _ | e
  · have : M = 0 := Multiset.eq_zero_of_forall_notMem fun x hx => by have := h x hx; omega
    simp [this]
  · have hle : ∀ y ∈ M.map (4 ^ ·), y ≤ 4 ^ e := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hy
      exact Nat.pow_le_pow_right (by norm_num) (Nat.lt_succ_iff.1 (h x hx))
    have := Multiset.sum_le_card_nsmul _ _ hle
    rw [Multiset.card_map, smul_eq_mul] at this
    have h4 : 0 < 4 ^ e := by positivity
    rw [pow_succ]
    nlinarith

/-- Uniqueness of representation as a sum of at most three powers of 4. -/
theorem pow_four_sum_inj : ∀ (n : ℕ) (M M' : Multiset ℕ), Multiset.card M = n →
    Multiset.card M' = n → n ≤ 3 →
    (M.map (4 ^ ·)).sum = (M'.map (4 ^ ·)).sum → M = M' := by
  intro n
  induction n with
  | zero =>
    intro M M' hM hM' _ _
    rw [Multiset.card_eq_zero.1 hM, Multiset.card_eq_zero.1 hM']
  | succ n ih =>
    intro M M' hM hM' hn hsum
    have hne : M + M' ≠ 0 := by
      intro h
      have := congrArg Multiset.card h
      simp [hM] at this
    obtain ⟨e, he, hmax⟩ := Multiset.exists_max_image id hne
    simp only [id] at hmax
    -- the largest exponent occurs on both sides
    have both : e ∈ M ∧ e ∈ M' := by
      rcases Multiset.mem_add.1 he with heM | heM'
      · refine ⟨heM, ?_⟩
        by_contra hnot
        have hlt : ∀ x ∈ M', x < e := fun x hx =>
          lt_of_le_of_ne (hmax x (Multiset.mem_add.2 (Or.inr hx))) fun h => hnot (h ▸ hx)
        have h1 := sum_pow_four_lt M' (by omega) e hlt
        have h2 : 4 ^ e ≤ (M.map (4 ^ ·)).sum :=
          Multiset.le_sum_of_mem (Multiset.mem_map_of_mem _ heM)
        omega
      · refine ⟨?_, heM'⟩
        by_contra hnot
        have hlt : ∀ x ∈ M, x < e := fun x hx =>
          lt_of_le_of_ne (hmax x (Multiset.mem_add.2 (Or.inl hx))) fun h => hnot (h ▸ hx)
        have h1 := sum_pow_four_lt M (by omega) e hlt
        have h2 : 4 ^ e ≤ (M'.map (4 ^ ·)).sum :=
          Multiset.le_sum_of_mem (Multiset.mem_map_of_mem _ heM')
        omega
    obtain ⟨heM, heM'⟩ := both
    rw [← Multiset.cons_erase heM, ← Multiset.cons_erase heM'] at hsum ⊢
    simp only [Multiset.map_cons, Multiset.sum_cons] at hsum
    have hrest := ih (M.erase e) (M'.erase e)
      (by rw [Multiset.card_erase_of_mem heM, hM]; rfl)
      (by rw [Multiset.card_erase_of_mem heM', hM']; rfl) (by omega) (by omega)
    rw [hrest]

/-- The powers of 4 form a `B₃` set. -/
theorem isB3_pow_four : IsB3 (Set.range (4 ^ · : ℕ → ℕ)) := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ _ ⟨c, rfl⟩ _ ⟨a', rfl⟩ _ ⟨b', rfl⟩ _ ⟨c', rfl⟩ hs
  have key := pow_four_sum_inj 3 {a, b, c} {a', b', c'} (by simp) (by simp) le_rfl
    (by simpa [add_assoc] using hs)
  simpa using congrArg (Multiset.map (4 ^ · : ℕ → ℕ)) key

/-- **Non-vacuity.** The hypotheses of `theorem1` hold for the powers of 4. -/
theorem theorem1_hypotheses_satisfiable :
    (Set.range (4 ^ · : ℕ → ℕ)).Infinite ∧ 0 ∉ Set.range (4 ^ · : ℕ → ℕ) ∧
      IsB3 (Set.range (4 ^ · : ℕ → ℕ)) := by
  refine ⟨Set.infinite_range_of_injective (Nat.pow_right_injective (by norm_num : 2 ≤ 4)), ?_,
    isB3_pow_four⟩
  · rintro ⟨n, hn⟩
    exact absurd hn (by positivity)

end B3Liminf
