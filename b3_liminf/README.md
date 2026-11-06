# A liminf bound for infinite B₃ sequences (2026-11)

This is a separate, newer paper on Erdős Problem #41, independent of the withdrawn manuscript in
`../paper/`. It proves that every infinite B₃ sequence A satisfies

- liminf A(x)/x^(1/3) ≤ 3^(1/3) ≈ 1.442 (Theorem 1, elementary, formally verified in Lean 4), and
- liminf A(x)/x^(1/3) ≤ K^(−1/3) ≈ 1.199856 (Theorem 2), where K = (1/3)∫₀¹∫₀¹ dt dz/(1 + t³ − z³).

**This does not resolve Erdős #41,** which asks for liminf = 0. As far as we know, these are the first
liminf constants for h = 3 below the bound inherited from Green's finite-set result,
(7/2)^(1/3) ≈ 1.518.

Section 5 shows that K^(−1/3) is the limit of the method. It is optimal both for the method and for the
hypotheses it uses. That section also compares the result with Helm's 1996 barrier for near-solution
counting.

## Contents

| Path | What it is |
| --- | --- |
| `paper/b3_liminf.tex`, `paper/b3_liminf.pdf` | The paper (9 pages) |
| `certify_w_directed.py` | Interval-arithmetic certificate (directed rounding, mpmath) for Lemma 5, the one computer-assisted step of Theorem 2. Run `python -I certify_w_directed.py 3000 400`, which takes about 5 minutes and certifies W₂ ≥ 0.27270 |
| `numeric_W_and_K.py` | Non-rigorous numerics for K and W_L, for orientation only |
| `check_identity_and_injectivity.py` | Checks Lemmas 1–2 on greedy B₃ prefixes |
| `lean/` | Lean 4 (v4.33.1) and Mathlib formalization. It covers Theorem 1, the window condition (R), the bound S^(N) ≤ 2N + 1 for Helm's count, and a non-vacuity check. Build with `cd lean && lake --wfail build`; see `lean/README.md` |

## Status

- **Preprint, not yet refereed.** Every argument was put through independent adversarial review before
  inclusion.
- The paper's final section declares how generative AI was used in the research and the writing.
- The paper is licensed CC BY 4.0 (`../LICENSE-PAPER`). The code is MIT or Apache-2.0, as for the rest
  of the repository.
