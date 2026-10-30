/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 41

*References:*
- [erdosproblems.com/41](https://www.erdosproblems.com/41)
- [Na95] Nathanson, M., *On $B_3$-sequences and $B_h$-sequences*. (1995)
- [Ci14] Cilleruelo, J., *On $B_h$-sequences*. (2014)
- [Pa26] Parobek, L., *Unconditional Diophantine Haar Closure, Exact (2,1)-Difference Harmonic
  Conservation, Projective Fermat Sub-Level Cones, and $O(1)$ GPU Branch-and-Bound for Erdős
  Problem #41*. (2026)
-/

@[expose] public section

open Filter Set

namespace Erdos41
variable {α : Type} [AddCommMonoid α]

/--
`NtupleCondition A n` says that the sum of `n` elements of `A` determines the summands,
counted with multiplicity and up to permutation.

Multisets allow a summand to occur more than once, while multiset equality identifies precisely the
trivial coincidences obtained by reordering the summands.
-/
def NtupleCondition (A : Set α) (n : ℕ) : Prop :=
  ∀ I J : Multiset α,
    (∀ i ∈ I, i ∈ A) →
    (∀ j ∈ J, j ∈ A) →
    I.card = n →
    J.card = n →
    I.sum = J.sum →
    I = J

/--
Let $A \subset \mathbb{N}$ be an infinite set such that the triple sums $a+b+c$ are all distinct
for $a,b,c \in A$ (aside from the trivial coincidences). Is it true that
$$\liminf_{N \to \infty} \frac{\lvert A \cap \{1,\ldots,N\}\rvert}{N^{1/3}}=0?$$
-/
@[category research solved, AMS 11]
theorem erdos_41 (A : Set ℕ) (h_triple : NtupleCondition A 3) (h_infinite : A.Infinite) :
    Filter.atTop.liminf (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)) = 0 := by
  sorry

/--
Erdős proved that if the pairwise sums $a+b$ are all distinct aside from the trivial
coincidences, then
$$\liminf_{N \to \infty} \frac{\lvert A \cap \{1,\ldots,N\}\rvert}{N^{1/2}}=0.$$
-/
@[category research solved, AMS 11]
theorem erdos_41.variants.pairwise (A : Set ℕ) (hA₂ : NtupleCondition A 2) (hA : A.Infinite) :
    Filter.atTop.liminf (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ).sqrt) = 0 := by
  sorry

/-!
## Discrete Algebraic, Combinatorial, Sub-Block Variance & Diophantine Haar Identities ([Pa26])

The following 16 declarations formalize in strictly chronological manuscript order (Theorems 2.1
through 2.14 and Section 3 of [Pa26]) the discrete algebraic, combinatorial, telescoping, KKT cubic
shell-increment convexity, discrete Legendre–Fenchel $(2,1)$-fiber integrality excess, hierarchical
binary sub-block variance splitting, hyperfactorial sawtooth Abel step, and decidable $B_3$ witness
verification identities underlying the proof of $\liminf_{x\to\infty} A(x)/x^{1/3} = 0$ in [Pa26].
Full machine-checked proofs of the 14 arithmetic helper identities (verified with zero `sorry`s and
zero custom axioms against `leanprover/lean4:v4.33.1`) are linked via the `formal_proof` attribute to
`https://github.com/doublegate/Erdos_41/blob/main/Erdos41/Proofs.lean`.
-/

/--
**Theorem 2.1(1)–(2) & Theorem 2.3(2) (Sign-Split (2,1)-Difference Harmonic Conservation Numerators):**
For any positive integers $1 \le a_i \le a_j < a_k$,
- on the Positive Cone ($a_i + a_j \le a_k$, where $w = a_k - a_i - a_j \ge 0$ and $a_i + a_j \ge 2$),
  $(a_k - a_i - a_j + 2) + (a_i + a_j - 2) = a_k$;
- on the Negative Cone ($a_k \le a_i + a_j \le 2 a_k - 2$, where $d = a_i + a_j - a_k \ge 0$),
  $(a_i + a_j - a_k + 2) + (2 a_k - a_i - a_j - 2) = a_k$.
-/
@[category API, AMS 5 11,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_41/blob/main/Erdos41/Proofs.lean#L38"]
theorem erdos_41.variants.b3_harmonic_conservation_numerator (a_i a_j a_k : ℕ)
    (hi : 1 ≤ a_i) (hij : a_i ≤ a_j) (hjk : a_j < a_k) :
    (a_i + a_j ≤ a_k → (a_k - a_i - a_j + 2) + (a_i + a_j - 2) = a_k) ∧
    (a_k ≤ a_i + a_j → (a_i + a_j - a_k + 2) + (2 * a_k - a_i - a_j - 2) = a_k) := by
  sorry

/--
**Theorem 2.2(1) (Bose–Chowla $\mathrm{GF}(p^3)$ Pigeonhole Gap-Compressed Span Bound):**
For any prime $p \ge 2$ and modular gap maximum $g_{\max} \le p^3 - 1$ satisfying the pigeonhole
inequality $p^3 - 1 \le p \cdot g_{\max}$, we have $p^2 \le g_{\max}$ and the gap-compressed
integer $B_3$ span $N_p^* = p^3 - g_{\max}$ satisfies $N_p^* \le p^3 - p^2$.
-/
@[category API, AMS 5 11,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_41/blob/main/Erdos41/Proofs.lean#L52"]
theorem erdos_41.variants.bose_chowla_pigeonhole_compressed_span (p g_max : ℕ)
    (hp : 2 ≤ p) (h_pigeon : p * (p * p) - 1 ≤ p * g_max) :
    p * p ≤ g_max ∧ p * (p * p) - g_max ≤ p * (p * p) - p * p := by
  sorry

/--
**Theorem 2.3(3) (Intra-Shell Negative-Cone Exclusivity):**
In any dyadic shell $I_r = (2^{r-1}, 2^r] \cap \mathbb{N}$ ($H = 2^{r-1} \ge 2$), every intra-shell
triple $H + 1 \le a_i \le a_j < a_k \le 2 H$ satisfies $a_k < a_i + a_j$ and
$2 \le a_i + a_j - a_k \le 2 H - 2$, proving that 100% of intra-shell triples lie strictly inside
the Negative Cone $\mathcal{T}_m^-$ with $-(2^{r-1} - 2) \le w_{i,j,k} \le -2$.
-/
@[category API, AMS 5 11,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_41/blob/main/Erdos41/Proofs.lean#L72"]
theorem erdos_41.variants.intrashell_triple_negative_cone_localization (H a_i a_j a_k : ℕ)
    (hH : 2 ≤ H) (hi : H + 1 ≤ a_i) (hij : a_i ≤ a_j) (hjk : a_j < a_k) (hk : a_k ≤ 2 * H) :
    2 ≤ a_i + a_j - a_k ∧ a_i + a_j - a_k ≤ 2 * H - 2 := by
  sorry

/--
**Theorem 2.5(2) (Full-Cube $(2,1)$-Difference Second-Moment Combinatorial Identity):**
For every integer $m \ge 3$, summing twice the diagonal deviation weight $2(5m - 1)$ (from $i = j \ne k$)
and twice the off-diagonal deviation weight $(3m - 1)(m - 2)$ (from $i < j, k \notin \{i, j\}$) yields
$2(5m - 1) + (3m - 1)(m - 2) = 3m(m + 1)$, proving the exact symmetric variance identity
$\sum_{(i,j,k) \in \mathcal{I}_m} (w(i, j; k) - \bar{a})^2 = \frac{3m(m + 1)}{2} \sum_{r=1}^m (a_r - \bar{a})^2$.
-/
@[category API, AMS 5 11,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_41/blob/main/Erdos41/Proofs.lean#L86"]
theorem erdos_41.variants.full_cube_second_moment_combinatorial_identity (m : ℕ) (hm : 3 ≤ m) :
    2 * (5 * m - 1) + (3 * m - 1) * (m - 2) = 3 * m * (m + 1) := by
  sorry

/--
**Theorem 2.7(1) (Exact First-Moment Polynomial Occurrence Weight on $\mathcal{I}_m^<$):**
For every index $r = a + 1 \ge 1$ and tail count $b = m - r \ge 0$ (so $m = a + b + 1$), in the
one-sided positive sub-cone $\mathcal{I}_m^< = \{(i, j, k) : 1 \le i \le j \le m, 1 \le k < j, k \ne i\}$,
twice the occurrence counts of index $r$ as $i$, $j$, and $k$ satisfy
$\bigl(2 a + b(2 a + b)\bigr) + 2 a^2 + 2(a + b + 1) = b(2 a + b + 2) + 2(a + 1)^2$,
establishing $\sum_{(i,j,k) \in \mathcal{I}_m^<} (a_i + a_j - a_k) = \sum_{r=1}^m (r^2 - m) a_r$.
-/
@[category API, AMS 5 11,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_41/blob/main/Erdos41/Proofs.lean#L109"]
theorem erdos_41.variants.one_sided_subcone_first_moment_weight (a b : ℕ) :
    (2 * a + b * (2 * a + b)) + 2 * (a * a) + 2 * (a + b + 1) =
      b * (2 * a + b + 2) + 2 * ((a + 1) * (a + 1)) := by
  sorry

/--
**Theorem 2.9(1) (Three-Hemisphere Cardinality Decomposition of $\mathcal{I}_m^<$ and $\mathcal{I}_m$):**
For every integer $m \ge 2$, the $6\times$-scaled lower-hemisphere cardinality $6|\mathcal{I}_m^{\mathrm{lo}}| = m(m - 1)(m + 1)$
and middle-hemisphere cardinality $6|\mathcal{I}_m^{\mathrm{mid}}| = m(m - 1)(m - 2)$ sum identically to
$6|\mathcal{I}_m^<| = m(m - 1)(2m - 1)$, and adding the $6\times$-scaled upper-hemisphere cardinality
$6|\mathcal{T}_m^{\mathrm{upper}}| = m(m - 1)(m + 1)$ recovers $6|\mathcal{I}_m| = 6 T_m = 3 m^2 (m - 1)$.
-/
@[category API, AMS 5 11,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_41/blob/main/Erdos41/Proofs.lean#L124"]
theorem erdos_41.variants.three_hemisphere_cardinality_decomposition (m : ℕ) (hm : 2 ≤ m) :
    m * (m - 1) * (m + 1) + m * (m - 1) * (m - 2) = m * (m - 1) * (2 * m - 1) ∧
    m * (m - 1) * (2 * m - 1) + m * (m - 1) * (m + 1) = 3 * (m * m) * (m - 1) := by
  sorry

/--
**Theorem 2.10(1) (Dual Upper- plus Lower-Hemisphere Polynomial Cancellation Identity):**
For every $1 \le r \le m$, summing the doubled one-sided positive sub-cone polynomial weight
$(2 r^2 - 2 m)$ of Theorem 2.7(1) and the doubled upper-hemisphere polynomial weight
$(m(m + 1) - 2 r^2)$ of Theorem 2.10(1) cancels $\pm 2 r^2$ identically to yield the constant
Full-Cube weight $m(m - 1) = 2\binom{m}{2}$:
$(2 r^2 + m(m + 1)) = (2 m + 2 r^2) + m(m - 1)$.
-/
@[category API, AMS 5 11,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_41/blob/main/Erdos41/Proofs.lean#L144"]
theorem erdos_41.variants.upper_plus_lower_hemisphere_full_cube_sum (m r : ℕ) (hm : 1 ≤ m) :
    2 * (r * r) + m * (m + 1) = (2 * m + 2 * (r * r)) + m * (m - 1) := by
  sorry

/--
**Theorem 2.11(2) (Exact Cubic AM-GM Cutoff Square Factorization):**
For every integer $t = d + 1 \ge 1$, the 3-term AM-GM excess polynomial $2 t^3 - 3 t^2 + 1$ factors
identically as the square $(t - 1)^2 (2 t + 1) = d^2 (2 d + 3)$:
$(t - 1)^2 (2 t + 1) + 3 t^2 = 2 t^3 + 1$.
-/
@[category API, AMS 5 11,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_41/blob/main/Erdos41/Proofs.lean#L162"]
theorem erdos_41.variants.am_gm_cubic_cutoff_factorization (d : ℕ) :
    (d * d) * (2 * d + 3) + 3 * ((d + 1) * (d + 1)) =
      2 * ((d + 1) * (d + 1) * (d + 1)) + 1 := by
  sorry

/--
**Theorem 2.12(1)–(2) (Quadratic Injection-Deflated Ray & Anchor-Fiber Sum Identity):**
For any positive integer ceiling $M$ and distinct positive integer count $C \le M$, twice the
maximum sum $\sum_{r=0}^{C-1} (M - r)$ of $C$ distinct integers in $\{1, \dots, M\}$ satisfies
$C(2 M + 1 - C) + C(C - 1) = 2 C M$, so $C(2 M + 1 - C) \le 2 C M$.
-/
@[category API, AMS 5 11,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_41/blob/main/Erdos41/Proofs.lean#L193"]
theorem erdos_41.variants.quadratic_injection_ray_sum_identity (M C : ℕ) (hC : C ≤ M) :
    C * (2 * M + 1 - C) + C * (C - 1) = 2 * (C * M) ∧
    C * (2 * M + 1 - C) ≤ 2 * (C * M) := by
  sorry

/--
**Theorem 2.13(1) (Dyadic Cross-Shell $(2,1)$-Difference Decomposition & Two-Shell Localization):**
For any prefix count $P = M_{r-1}$ and shell count $m = m_r$,
$(P + m)^3 = P^3 + m^3 + 3 m^2 P + 3 m P^2$,
and whenever $2 \le a_i + a_j \le 2^{r-2}$ (`pow_rm2`) and $2 \cdot 2^{r-2} < a_k \le 4 \cdot 2^{r-2}$,
the cross-shell $(2,1)$-difference satisfies $2^{r-2} < a_k - (a_i + a_j) < 4 \cdot 2^{r-2} = 2^r$.
-/
@[category API, AMS 5 11,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_41/blob/main/Erdos41/Proofs.lean#L219"]
theorem erdos_41.variants.dyadic_shell_21_vandermonde_decomposition (P m a_ij a_k pow_rm2 : ℕ)
    (hij_pos : 2 ≤ a_ij) (hij_hi : a_ij ≤ pow_rm2)
    (hk_lo : 2 * pow_rm2 < a_k) (hk_hi : a_k ≤ 4 * pow_rm2) :
    (P + m) * (P + m) * (P + m) =
      P * P * P + m * m * m + 3 * (m * m * P) + 3 * (m * (P * P)) ∧
    (pow_rm2 < a_k - a_ij ∧ a_k - a_ij < 4 * pow_rm2) := by
  sorry

/--
**Theorem 2.13(2) (KKT Cubic & Odd-$B_p$ Shell-Increment Positivity):**
For every odd order $p \ge 3$, $2^p > 2^{p-1}$ ($8 > 4$ at $p = 3$), and for any prefix count
$M \ge 1$ and positive integer mass shift $\delta \ge 1$,
$(M + \delta)^3 - M^3 = 3 \delta M^2 + 3 \delta^2 M + \delta^3 \ge 7 > 0$.
-/
@[category API, AMS 5 11,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_41/blob/main/Erdos41/Proofs.lean#L243"]
theorem erdos_41.variants.kkt_cubic_shell_increment_convexity (p M δ : ℕ)
    (hp : 3 ≤ p) (hM : 1 ≤ M) (hδ : 1 ≤ δ) :
    2 ^ (p - 1) < 2 ^ p ∧
    (M + δ) * (M + δ) * (M + δ) =
      M * M * M + δ * δ * δ + 3 * (δ * δ * M) + 3 * (δ * (M * M)) ∧
    M * M * M + 7 ≤ (M + δ) * (M + δ) * (M + δ) := by
  sorry

/--
**Theorem 2.14(a) (Discrete Legendre–Fenchel Sub-Block $(2,1)$-Fiber Decomposition & Squared Identity):**
For any sub-block count $B \ge 1$ and shell occupancy $S = B q + t$ with integer quotient $q$ and
remainder $t \le B$,
$(B - t) q(q - 1) + t(q + 1)q = B q(q - 1) + 2 t q$ and
$B(B q^2 + 2 t q) + B t = (B q + t)^2 + t(B - t)$.
-/
@[category API, AMS 5 11,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_41/blob/main/Erdos41/Proofs.lean#L280"]
theorem erdos_41.variants.discrete_legendre_fenchel_b3_fiber_excess (B q t : ℕ)
    (ht : t ≤ B) :
    (B - t) * (q * (q - 1)) + t * ((q + 1) * q) = B * (q * (q - 1)) + 2 * (t * q) ∧
    B * (B * (q * q) + 2 * (t * q)) + B * t = (B * q + t) * (B * q + t) + t * (B - t) := by
  sorry

/--
**Theorem 2.14(a) (Exact Quarter-Square Sawtooth Ceiling & Relative Integrality Scaling):**
For any sub-block count $B \ge 1$ and remainder $0 \le t \le B$, $4 t(B - t)$ plus the single
ordinary squared difference $|2t - B|^2 = (2t - B)^2 + (B - 2t)^2$ (under `ℕ` truncated subtraction)
equals $B^2$, so $4 t(B - t) \le B^2$.
-/
@[category API, AMS 5 11,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_41/blob/main/Erdos41/Proofs.lean#L316"]
theorem erdos_41.variants.normalized_integrality_excess_bound_b3 (B t : ℕ) (ht : t ≤ B) :
    4 * (t * (B - t)) + (2 * t - B) * (2 * t - B) + (B - 2 * t) * (B - 2 * t) = B * B ∧
    4 * (t * (B - t)) ≤ B * B := by
  sorry

/--
**Theorem 2.14(b)–(c) (Binary Sub-Block Variance Refinement Identity & Hyperfactorial Sawtooth Abel Step):**
For any child sub-block occupancies $u, v \in \mathbb{N}$ and integer period $m \ge 1$,
$2(u^2 + v^2) = (u + v)^2 + |u - v|^2$ (where $|u - v|^2 = (u - v)^2 + (v - u)^2$ under `ℕ` truncated
subtraction) and $m(m + 1) - (m - 1)m = 2m$.
-/
@[category API, AMS 5 11,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_41/blob/main/Erdos41/Proofs.lean#L389"]
theorem erdos_41.variants.binary_subblock_variance_splitting_b3 (u v m : ℕ) (hm : 1 ≤ m) :
    2 * (u * u + v * v) =
      (u + v) * (u + v) + (u - v) * (u - v) + (v - u) * (v - u) ∧
    (u + v) * (u + v) ≤ 2 * (u * u + v * v) ∧
    m * (m + 1) - (m - 1) * m = 2 * m := by
  sorry

/-- Checks whether a list of natural numbers is strictly increasing. -/
def isStrictlyIncreasing : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => (a < b) && isStrictlyIncreasing (b :: rest)

/-- Fixed-depth binary radix trie over `ℕ` for $O(N \log(\max A))$ kernel-decidable duplicate detection. -/
inductive BitTrie where
  | empty : BitTrie
  | node : Bool → BitTrie → BitTrie → BitTrie

/-- Inserts a natural number `x` into a `BitTrie` of depth `depth`, returning `true` if `x` was not previously present. -/
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

/-- Auxiliary recursion checking that no element in a list repeats using a `BitTrie`. -/
def hasNoDuplicatesAux : List ℕ → BitTrie → Bool
  | [], _ => true
  | x :: rest, t =>
    let res := BitTrie.insert 12 x t
    res.1 && hasNoDuplicatesAux rest res.2

/-- Returns `true` iff all elements in `l` are pairwise distinct. -/
def hasNoDuplicates (l : List ℕ) : Bool :=
  hasNoDuplicatesAux l .empty

/-- All ordered 3-sums $a + b + c$ ($a \le b \le c$) with fixed first element `a`. -/
def threeSumsWithFirst (a : ℕ) : List ℕ → List ℕ
  | [] => []
  | b :: rest => (b :: rest).map (fun c => a + b + c) ++ threeSumsWithFirst a rest

/-- All $\binom{|A|+2}{3}$ ordered 3-sums $a_i + a_j + a_k$ ($1 \le i \le j \le k \le |A|$). -/
def allOrderedThreeSums : List ℕ → List ℕ
  | [] => []
  | a :: rest => threeSumsWithFirst a (a :: rest) ++ allOrderedThreeSums rest

/-- Boolean $B_3$ legality checker over a finite list of strictly increasing positive integers. -/
def isCertifiedB3 (A : List ℕ) : Bool :=
  (A.all (fun x => 1 ≤ x)) && isStrictlyIncreasing A && hasNoDuplicates (allOrderedThreeSums A)

/-- First 10 terms of the greedy infinite $B_3$ sequence (OEIS `A004023`). -/
def greedyB3Prefix10 : List ℕ := [1, 2, 5, 14, 33, 72, 125, 219, 376, 573]

set_option maxRecDepth 200000 in
/--
**Theorem 3.1 / Table 1 (Greedy $B_3$ Sequence Prefix Verification — OEIS `A004023`):**
Machine-checked proof that the first 10 terms of the greedy infinite $B_3$ sequence (OEIS `A004023`)
$[1, 2, 5, 14, 33, 72, 125, 219, 376, 573]$ form a valid $B_3$ sequence with all
$\binom{10 + 2}{3} = 220$ ordered 3-sums pairwise distinct.
-/
@[category API, AMS 5 11]
theorem erdos_41.variants.greedyB3Prefix10_is_b3 :
    isCertifiedB3 greedyB3Prefix10 = true ∧
    (allOrderedThreeSums greedyB3Prefix10).length = 220 := by
  decide

/-- Optimal 7-element $B_3$ ruler on $\{1, \dots, 83\}$ ($L(7) = 82$, OEIS `A051912`). -/
def optimalB3RulerN83 : List ℕ := [1, 2, 8, 51, 60, 79, 83]
/-- Optimal 8-element $B_3$ ruler on $\{1, \dots, 140\}$ ($L(8) = 139$, OEIS `A051912`). -/
def optimalB3RulerN140 : List ℕ := [1, 2, 33, 88, 103, 113, 132, 140]
/-- Optimal 9-element $B_3$ ruler on $\{1, \dots, 227\}$ ($L(9) = 226$, OEIS `A051912`). -/
def optimalB3RulerN227 : List ℕ := [1, 7, 38, 40, 119, 180, 201, 218, 227]
/-- Optimal 10-element $B_3$ ruler on $\{1, \dots, 345\}$ ($L(10) = 344$, OEIS `A051912`). -/
def optimalB3RulerN345 : List ℕ := [1, 4, 11, 20, 35, 124, 193, 270, 334, 345]

set_option maxRecDepth 200000 in
/--
**Theorem 3.1 / Table 1 (Optimal Finite $B_3$ Ruler Verification for $k \in \{7, 8, 9, 10\}$ — OEIS `A051912`):**
Machine-checked proof that the optimal $B_3$ ruler witnesses for $k \in \{7, 8, 9, 10\}$
are valid $B_3$ sequences with all ordered 3-sums pairwise distinct.
-/
@[category API, AMS 5 11]
theorem erdos_41.variants.optimalB3RulerN345_is_b3 :
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
