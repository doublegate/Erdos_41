# B3Liminf: Lean 4 formalization of Theorem 1

This is a machine-checked proof of Theorem 1 of the draft paper
`../paper/b3_liminf.tex`. The theorem says that every infinite B₃ set A of
positive integers satisfies liminf A(x)/x^(1/3) ≤ 3^(1/3) ≈ 1.442.

Theorem 2 of the paper (the bound K^(−1/3) ≈ 1.19986) is not formalized. It
needs Davenport's lattice-point lemma, volumes of semialgebraic regions and a
verified interval-arithmetic certificate, none of which are available in
Mathlib.

## Build

```sh
lake --wfail build
```

This uses Lean `v4.33.1` and Mathlib `v4.33.1` (commit `0df444a`, pinned in
`lake-manifest.json`), the same as the other `erdos<N>` Lean projects. Point
`.lake/packages` at the shared cache to avoid a Mathlib rebuild:

```sh
ln -s ~/.cache/lean-shared/v4.33.1/packages .lake/packages
```

Building `B3Liminf.AxiomCheck` prints the axioms of every main result. They
should be only `propext`, `Classical.choice` and `Quot.sound`.

## What is proved

| Lean | Paper |
| --- | --- |
| `IsB3`, `countUpTo` | the definitions of a B₃ set (sums of three elements, repetition allowed, determine the summands) and A(x) = \|A ∩ [1, x]\| |
| `w_injOn`, `one_le_w` | Lemma 1 |
| `sum_w_eq`, `card_idx` | Lemma 2 |
| `seq_false` | Section 3 (proof of Theorem 1), with Lemma 3 inlined as the density hypothesis |
| `CountR`, `countR_of_B3`, `seq_false_of_countR`, `card_mul_succ_le_two_mul_sum_of_count` | the window condition (R) of Section 5: every B₃ sequence satisfies it, and the sequence form of Theorem 1 follows from (R) alone (sorting gives the bound (★)) |
| `theorem1` | Theorem 1: for every d > 3 there are arbitrarily large x with A(x)³ < d·x |
| `theorem1_liminf` | Theorem 1 with `Filter.liminf`, together with coboundedness (A(x)/x^(1/3) ≤ 2 infinitely often). Without that conjunct, Mathlib's junk value 0 for the liminf of a function tending to ∞ would make the inequality hold trivially |
| `theorem1_hypotheses_satisfiable` | non-vacuity: the powers of 4 are an infinite B₃ set of positive integers |
| `helmTriples`, `helmValue_injOn`, `helmTriples_finite`, `helm_count_le` (in `B3Liminf/HelmCount.lean`) | Section 5.2, the remark on Helm's count: for a B₃ set, the triples a ≤ b < c with \|a + b − c\| ≤ N have distinct values, so there are finitely many of them, at most 2N + 1. No infiniteness hypothesis is needed. |

Indices are 0-based. The paper's a_r (r ≥ 1) is `a (r - 1)`, and its index set
𝓘_m is `idx m`.

A passing build shows only that these Lean statements are proved. Whether they
say the same thing as the paper has to be checked by reading `IsB3`,
`countUpTo`, `theorem1`, `theorem1_liminf`, `CountR` and `seq_false_of_countR` in
`B3Liminf/Theorem1.lean`, and `helmTriples` and `helm_count_le` in
`B3Liminf/HelmCount.lean`, against the paper.
