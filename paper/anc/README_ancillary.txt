==============================================================================
arXiv Ancillary Verification Files — Erdős Problem #41 (Parobek, 2026)
==============================================================================

Title: Unconditional Diophantine Haar Closure, Exact (2,1)-Difference Harmonic
       Conservation, Projective Fermat Sub-Level Cones, and O(1) GPU
       Branch-and-Bound for Erdős Problem #41
Author: Lucas Parobek (ORCID: 0009-0001-9526-6920)
Date:   October 27, 2026

Contents of `anc/`:
-------------------
1. `41.lean` (and `41.lean.txt` plain-text mirror for arXiv upload):
   Self-contained Lean 4 (`leanprover/lean4:v4.33.1`) formalization module
   containing 16 substantive, zero-`sorry`, zero-custom-axiom theorems covering:
   - Theorem 2.1(a)-(b) & Theorem 2.3: Sign-split (2,1)-difference harmonic
     conservation numerators and intra-shell Negative-Cone exclusivity;
   - Theorem 2.2: Bose–Chowla GF(p^3) pigeonhole gap-compressed span bound;
   - Theorem 2.5(b): Full-Cube (2,1)-difference symmetric second-moment identity;
   - Theorem 2.7(a): One-sided positive sub-cone polynomial weight r^2 - m;
   - Theorem 2.9(a): Three-hemisphere cardinality decomposition of I_m^< and I_m;
   - Theorem 2.10(a): Dual upper- plus lower-hemisphere polynomial cancellation;
   - Theorem 2.11(b): Continuum AM-GM cubic cutoff square factorization;
   - Theorem 2.12(a)-(b): Quadratic injection-deflated ray ceiling identity;
   - Theorem 2.13(a)-(b): Dyadic cross-shell (2,1)-difference Vandermonde
     decomposition, two-shell localization, and KKT cubic shell-increment
     convexity;
   - Theorem 2.14(a): Discrete Legendre–Fenchel sub-block (2,1)-fiber excess
     and quarter-square sawtooth ceiling;
   - Theorem 2.14(b)-(c): Binary sub-block variance splitting and hyperfactorial
     sawtooth Abel step;
   - Theorem 3.1 / Table 1: Kernel-decidable (`by decide`) verification of the
     OEIS A004023 greedy B_3 prefix (m = 10, 220 distinct 3-sums) and the
     OEIS A051912 optimal B_3 rulers for k in {7, 8, 9, 10} (N in {83, 140, 227, 345}).

2. `verify_erdos41_diophantine_haar.py`:
   Standalone 50-digit `mpmath` + `sympy` verification script checking all
   symbolic and numerical claims in Theorems 2.13, 2.14, and Corollary 2.15,
   and regenerating `diophantine_haar_certificates.json`.

3. `diophantine_haar_certificates.json`:
   Machine-readable JSON certificate containing 50-digit evaluations of K_*,
   A_GK, C_GK = 2 ln A_GK, the Diophantine Haar trajectory c_{infty,3}^{*,Dio}(K) -> 0,
   and exact optimal B_3 ruler witnesses for k = 1..10 (OEIS A051912).
