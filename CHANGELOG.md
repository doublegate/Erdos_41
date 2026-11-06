# Changelog

All notable changes to **Erdos_41** (`erdos41`) are documented in this file.
The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased] - 2026-11-06

### Added
- **`b3_liminf/`: the paper "A liminf bound for infinite B₃ sequences" (9 pages), with its ancillary files.**
  - **Results:** liminf A(x)/x^(1/3) ≤ 3^(1/3) for every infinite B₃ sequence (Theorem 1, formally verified in Lean 4), and ≤ K^(−1/3) ≈ 1.199856 (Theorem 2, with Lemma 5 certified in interval arithmetic by `certify_w_directed.py`).
  - **Section 5:** shows the method and its hypotheses are sharp, and compares the result with Helm's 1996 barrier.
  - **Lean project** (`b3_liminf/lean/`, Lean and Mathlib v4.33.1): covers Theorem 1, the window condition (R), S^(N) ≤ 2N + 1, and non-vacuity. `lake --wfail build` is clean; every audited result uses only `propext`, `Classical.choice` and `Quot.sound`.
  - **Scope:** this does not resolve Erdős #41.

### Changed
- `b3_liminf/paper/`: proofs now end with "q.e.d." rather than amsthm's open box, which readers took for a missing glyph. The text is otherwise unchanged.
- `b3_liminf/README.md`: notes that the preprint and its supplementary PDF are public on ResearchGate.
- The README status note no longer says the c ≤ 1.1999 bound depends on an unproved lemma (W(U) ≥ 0). That lemma is now certified (`b3_liminf/`). The README also has a note pointing to the new paper.

## 2026-11-03

### Withdrawn
- The claim that this repository resolves Erdős Problem #41 is **withdrawn**: the problem remains open. An independent review on 2026-11-03 found the main argument invalid. The README status note gives the specific errors and lists what still stands.
- Retitled the README and the `Cargo.toml` description, added the status note to the README, the companion explainer and `paper/manuscript.md`, and replaced the verifier's "PROVED"/"VERIFIED" status string with a neutral one. The manuscripts and PDFs are otherwise unchanged and await a full revision.

## [1.0.0] - 2026-10-27

### Added
- **Unconditional Diophantine Haar Sub-Block Variance Closure (`src/records.rs`, `src/verify_cpu.rs`, `src/kernels.cu`, `src/exact.rs`, `scripts/verify_phase10_diophantine_haar_b3.py`, `paper/anc/verify_erdos41_diophantine_haar.py`):**
  - Completed the 10-phase analytical and computational hierarchy (Theorems 2.1–2.14, Corollary 2.15, and Theorem 3.1) resolving **Erdős Problem #41** (500 USD prize) in the affirmative: $\liminf _ {x\to\infty} A(x)/x ^ {1/3} = 0$ for every infinite $B _ 3$ sequence $A \subseteq \mathbb{N}$ (and $\liminf _ {x\to\infty} A(x)/x ^ {1/(2h-1)} = 0$ for every odd order $p = 2h - 1 \ge 3$).
  - Proved and implemented **Theorem 2.13** (Exact Three-Type Dyadic Shell Vandermonde Decomposition $\binom{P+m+1}{3} - \binom{P+1}{3} \equiv \binom{m+1}{3} + m\binom{P+1}{2} + P\binom{m}{2}$ and Exact Hyperfactorial Sawtooth Antiderivative Identity $F _ {\mathrm{Haar}}(M) = \int _ 0 ^ M \frac{\lbrace u\rbrace(1-\lbrace u\rbrace)}{u}\,du = \frac{M ^ 2}{2} - M(M-1)\ln M + 2\ln H(M-1) = \frac{1}{6}\ln M + 2\ln A _ {\mathrm{GK}} + \frac{1}{360 M ^ 2} - \frac{1}{2520 M ^ 4} + \frac{1}{8400 M ^ 6} - O(M ^ {-8}){}$) and **Theorem 2.14 / Corollary 2.15** (Multi-Shell Diophantine Haar Variance Boost $\kappa _ {\mathrm{int}, 3} ^ {\mathrm{Dio}}(K) = \frac{K\ln 2}{3(1 - 4 ^ {-K})}$ and Unconditional Upper Bound $c _ {\infty, 3} ^ {\ast, \mathrm{Dio}}(K) = [\mathcal{K} _ \ast (1 + \kappa _ {\mathrm{int}, 3} ^ {\mathrm{Dio}}(K))] ^ {-1/3} \to 0$).
  - Added the 11th CUDA kernel `k_eval_b3_diophantine_haar_closure` in `src/kernels.cu` with bit-exact CPU/GPU parity verified in `src/exact.rs`.
  - Certified all 10 optimal $B _ 3$ rulers ($k = 1 \dots 10$, $N \le 345$, OEIS `A051912`) in `src/records.rs`, including $k = 8, N = 140$ (`[1, 2, 33, 88, 103, 113, 132, 140]`), $k = 9, N = 227$ (`[1, 7, 38, 40, 119, 180, 201, 218, 227]`), and $k = 10, N = 345$ (`[1, 4, 11, 20, 35, 124, 193, 270, 334, 345]`).
- **Standalone 16-Theorem Lean 4 (`v4.33.1`) Formal Verification Suite (`Erdos41/Proofs.lean`, `Erdos41/AxiomCheck.lean`, `FormalConjectures_41.lean`, `paper/anc/41.lean`):**
  - Added 16 machine-checked theorems (`#L38`–`#L564`) with 0 errors, 0 warnings (`lake --wfail build`), 0 `sorry`s, and standard axioms only (`greedyB3Prefix10_is_b3` and `optimalB3RulerN345_is_b3` verified on **zero axioms** via kernel `by decide` over a depth-12 binary radix trie `BitTrie` with strict positivity and sortedness checks in `isCertifiedB3`).
- **Companion Mathematical Explainer, Supplementary Verification Compendium & Manuscripts (`paper/`, `docs/`):**
  - Added 19-page `paper/manuscript.pdf` (`Parobek_2026-10-27_Erdos41_Unconditional_Diophantine_Haar_Closure_B3_Sequences.pdf`, `0` Overfull warnings, 4 `tcolorbox` visual callouts, Section 6 on Methodological Objections), 8-page `paper/Companion_Explainer_Erdos41.pdf` (`Parobek_2026-10-27_Erdos41_Companion_Mathematical_Explainer.pdf`), 20-page `paper/Supplementary_Verification_Suite_Erdos41.pdf` (`Parobek_2026-10-27_Erdos41_Supplementary_Verification_Suite.pdf`), `paper/Parobek_2026-10-27_Erdos41_Supplementary_Verification_Suite.zip`, `paper/ERDOS_41_tex_bib_figures.zip`, and `paper/arxiv_submission.tar.gz`.
  - Adopted Option A split licensing (`MIT OR Apache-2.0` for code/Lean/scripts; `CC BY 4.0` for manuscripts and figures, with patent and trademark rights reserved under Section 2(b)(2)).
