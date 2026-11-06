/-
Copyright 2026 Lucas Parobek.
Licensed under the Apache License, Version 2.0.

The near-solution count of Helm, "On B₃-sequences", Progr. Math. 139 (1996) 465–469, as used in
Section 5.2 of "A liminf bound for infinite B₃ sequences":

  `S^{(N)} = #{(a, b, c) ∈ A³ : a ≤ b < c, |a + b - c| ≤ N}`.

Helm writes `b ≤ c`, but his proof treats only `b < c`. Taken literally, the count is infinite for
every infinite `A` and every `N ≥ min A`, because the triples `(a, b, b)` have value `a` for every
`b ≥ a`. The paper uses `b < c`, and this file proves the
bound the paper states: for a B₃ set the values `a + b - c` of these triples are distinct, so the
set is finite and `S^{(N)} ≤ 2N + 1`, for every set `A` and every `N` (no infiniteness needed).
-/
import B3Liminf.Theorem1

namespace B3Liminf

/-- Helm's triples with `b < c`: `a ≤ b < c` in `A` and `-N ≤ a + b - c ≤ N`, the two-sided window
written without subtraction. A triple `(a, b, c)` is stored as `(a, b, c) : ℕ × ℕ × ℕ`. -/
def helmTriples (A : Set ℕ) (N : ℕ) : Set (ℕ × ℕ × ℕ) :=
  {t | t.1 ∈ A ∧ t.2.1 ∈ A ∧ t.2.2 ∈ A ∧ t.1 ≤ t.2.1 ∧ t.2.1 < t.2.2 ∧
    t.1 + t.2.1 ≤ t.2.2 + N ∧ t.2.2 ≤ t.1 + t.2.1 + N}

/-- The shifted value `a + b - c + N ∈ [0, 2N]` of a triple. -/
def helmValue (N : ℕ) (t : ℕ × ℕ × ℕ) : ℕ := t.1 + t.2.1 + N - t.2.2

/-- For a B₃ set, a triple in `helmTriples A N` is determined by its value `a + b - c`. -/
theorem helmValue_injOn {A : Set ℕ} (hA : IsB3 A) (N : ℕ) :
    Set.InjOn (helmValue N) (helmTriples A N) := by
  rintro ⟨a, b, c⟩ ⟨ha, hb, hc, hab, hbc, -, hcN⟩ ⟨a', b', c'⟩ ⟨ha', hb', hc', hab', hbc', -, hcN'⟩ hv
  dsimp only [helmValue] at hv ha hb hc hab hbc hcN ha' hb' hc' hab' hbc' hcN'
  have hsum : a + b + c' = a' + b' + c := by omega
  have hM := hA a ha b hb c' hc' a' ha' b' hb' c hc hsum
  have m1 : c ∈ ({a, b, c'} : Multiset ℕ) := by rw [hM]; simp
  have m2 : a ∈ ({a', b', c} : Multiset ℕ) := by rw [← hM]; simp
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at m1 m2
  have hcc : c = c' := by omega
  subst hcc
  have haa : a = a' := by omega
  have hbb : b = b' := by omega
  subst haa hbb
  rfl

/-- Every value lies in `[0, 2N]`. -/
theorem helmValue_lt {A : Set ℕ} {N : ℕ} :
    ∀ t ∈ helmTriples A N, helmValue N t ∈ Set.Iio (2 * N + 1) := by
  rintro ⟨a, b, c⟩ ⟨-, -, -, -, -, h1, -⟩
  dsimp only at h1
  simp only [helmValue, Set.mem_Iio]
  omega

/-- For a B₃ set, Helm's count (with `b < c`) is finite. -/
theorem helmTriples_finite {A : Set ℕ} (hA : IsB3 A) (N : ℕ) : (helmTriples A N).Finite :=
  Set.Finite.of_finite_image ((Set.finite_Iio (2 * N + 1)).subset
    (Set.image_subset_iff.mpr (fun t ht => helmValue_lt t ht))) (helmValue_injOn hA N)

/-- For a B₃ set, `S^{(N)} ≤ 2N + 1` (Section 5.2 of the paper). -/
theorem helm_count_le {A : Set ℕ} (hA : IsB3 A) (N : ℕ) :
    (helmTriples A N).ncard ≤ 2 * N + 1 := by
  have h := Set.ncard_le_ncard_of_injOn (helmValue N) helmValue_lt (helmValue_injOn hA N)
    (Set.finite_Iio (2 * N + 1))
  simpa [Set.ncard_eq_toFinset_card'] using h

end B3Liminf
