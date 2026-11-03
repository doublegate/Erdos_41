# How Erdős Problem #41 Was Cracked: A Plain-Language Companion Explainer and Theorem-by-Theorem Architecture Guide

> **Status (2026-11-03): the claimed resolution of Erdős Problem #41 described below is withdrawn; the problem remains open. See the status note in the repository [README](../README.md) for the specific errors and what still stands.**

**Author:** Lucas Parobek (`parobek@gmail.com`) · **Date:** October 27, 2026  
**Repository:** [https://github.com/doublegate/erdos41](https://github.com/doublegate/erdos41) · **Prize Status:** 500 USD Erdős Bounty (Unconditionally Resolved)

---

## 1. Purpose of This Companion Document

The primary research manuscript resolves **Erdős Problem #41** (500 USD prize) in the affirmative by proving that every infinite $B _ 3$ sequence $A \subseteq \mathbb{N}$ satisfies
$\displaystyle \liminf _ {x \to \infty} \frac{A(x)}{x ^ {1/3}} = 0$
(and more generally $\liminf _ {x \to \infty} A(x)/x ^ {1/(2h-1)} = 0$ for every odd order $p = 2h - 1 \ge 3$). This companion guide explains in plain terms:
1. **What Erdős Problem #41 asks** and why odd-order $B _ 3$ sequences resisted all classical even-order $B _ {2k}$ methods for 71 years (1955–2026);
2. **Why Nash's 1995 Kneser bound stalled at $2 ^ {1/3} \approx 1.259921$** and why the smooth continuum sub-level Fermat cone reaches its exact variational optimum at $\mathcal{K} _ \ast ^ {-1/3} \approx 1.199856$;
3. **What each theorem in the paper (Theorems 2.1–2.14, Corollary 2.15, and Theorem 3.1) accomplishes**; and
4. **Why the limit goes all the way to $0$** as the dyadic shell window $K \to \infty$ via the explicit Diophantine Haar trajectory $c _ {\infty, 3} ^ {\ast, \mathrm{Dio}}(K) = [\mathcal{K} _ \ast (1 + \frac{K\ln 2}{3(1 - 4 ^ {-K})})] ^ {-1/3} \to 0$.

---

## 2. The Even-vs-Odd Parity Mystery & The Two Walls

For *even* orders $h = 2k$ (Erdős 1955 for $h=2$, Nash 1989 for $h=4$, Jia 1993 for all $h=2k$), an equality of two $2k$-sums rearranges symmetrically into $(k\text{ elements}) - (k\text{ elements}){}$, so inside any dyadic shell $(2 ^ {r-1}, 2 ^ r]$ the leading offset $k \cdot 2 ^ {r-1}$ cancels identically on both sides. For $h = 3$, rearranging $a _ i + a _ j + a _ {k'} = a _ {i'} + a _ {j'} + a _ k$ leaves an **asymmetric $(2,1){}$-difference**
$\displaystyle w _ {i,j,k} := a _ k - a _ i - a _ j = a _ {k'} - a _ {i'} - a _ {j'},$
where one positive summand fights two negative summands, leaving a residual scale $\Theta(a _ k){}$.

Even when one optimizes over all measurable subsets $D \subseteq \mathcal{I} _ \infty ^ { \lt }$ of the positive-definite $(2,1){}$-difference cone under a smooth continuum approximation $a _ r \approx (r/c) ^ 3$ (**Theorems 2.7 and 2.8**), the scale-invariant functional $\mathcal{J}(D) = \mathrm{Vol}(D) ^ 2 / (2 S(D)){}$ attains its unique global maximum on the projective Fermat sub-level sub-cone $\Omega _ \infty ^ \ast = \lbrace X ^ 3 + Y ^ 3 - Z ^ 3 \le 1\rbrace$, giving the smooth Fermat barrier $\mathcal{K} _ \ast ^ {-1/3} \approx 1.1998559643 \lt 2 ^ {1/3} \approx 1.259921$.

**How Theorems 2.13–2.14 Break the Smooth Barrier to $0$:** An actual $B _ 3$ counting function $A(t) \in \mathbb{Z} _ {\ge 0}$ is an integer step function, not a smooth curve. Across each unit step $u \in [n, n+1]$, the fractional sawtooth deviation $\lbrace u\rbrace = u - \lfloor u \rfloor$ injects a strictly positive period integral $I _ n = (2n+1)\ln(1 + 1/n) - 2 \approx \frac{1}{6n}$. Summing over $1 \le n \le M - 1$ (**Theorem 2.13**) gives the exact hyperfactorial antiderivative
$\displaystyle F _ {\mathrm{Haar}}(M) := \int _ 0 ^ M \frac{\lbrace u\rbrace(1 - \lbrace u\rbrace)}{u}\,du = \frac{M ^ 2}{2} - M(M-1)\ln M + 2\ln H(M-1) = \frac{1}{6}\ln M + 2\ln A _ {\mathrm{GK}} + \frac{1}{360 M ^ 2} - O(M ^ {-4}).$
Integrating this orthogonal Diophantine Haar quantization variance over $K$ consecutive dyadic shells (**Theorem 2.14**) multiplies $\mathcal{K} _ \ast$ by $1 + \frac{K\ln 2}{3(1 - 4 ^ {-K})} \to \infty$, forcing $c _ {\infty, 3} ^ {\ast, \mathrm{Dio}}(K) \to 0$ as $K \to \infty$ (**Corollary 2.15**).

---

## 3. Summary Progression of Upper Bounds on $\liminf _ {x\to\infty} A(x)/x ^ {1/3}$

| Stage / Method | Theorem / Reference | Mathematical Mechanism | Upper Bound on $\liminf \Psi _ A(x){}$ |
| :--- | :--- | :--- | :---: |
| Classical Kneser Bound | Nash (1995) | Asymptotic density of sumsets | $2 ^ {1/3} \approx 1.259921$ |
| Full-Cube Variance | Theorem 2.5 | $\mathrm{Var} _ {\mathcal{I} _ m}(w) = \frac{3(m+1)}{m-1}\sigma _ A ^ 2$, root $t _ \ast ^ 4 + 2t _ \ast ^ 3 = 1$ | $(144\kappa _ \ast ) ^ {1/6} \approx 1.546793$ |
| One-Sided Fermat / Laplace | Theorem 2.6 | Sub-cone $\mathcal{I} _ m ^ \lt$ ($w \ge 2$) & Laplace–Abel | $\bigl(\frac{9}{\ln 2 + \pi/\sqrt{3}}\bigr) ^ {1/3} \approx 1.531202$ |
| First-Moment Polynomial | Theorem 2.7(1) | $\sum _ {\mathcal{I} _ m ^ \lt } w \equiv \sum (r ^ 2 - m)a _ r \ge \binom{N _ m ^ \lt + 1}{2}$ | $3 ^ {1/3} \approx 1.442250$ |
| Third-Hemisphere Slot Eviction | Theorem 2.12(3) | Horizon-truncated $1/72$ ray eviction in $[1, N _ m ^ \lt ]$ | $(12384/4375) ^ {1/3} \approx 1.414580$ |
| **Smooth Sub-Level Fermat Cone** | **Theorems 2.7(3)–2.8** | **Unique variational maximizer $\Omega _ \infty ^ \ast = \lbrace X ^ 3+Y ^ 3-Z ^ 3 \le 1\rbrace$** | **$\mathcal{K} _ \ast ^ {-1/3} \approx 1.199856 \lt 2 ^ {1/3}$** |
| Diophantine Haar ($K = 4$ shells) | Theorem 2.14 ($K = 4$) | 4-shell sawtooth boost $\kappa _ {\mathrm{int}, 3} ^ {\mathrm{Dio}}(4) = 0.927821$ | **$0.964066 \lt 1.00$** |
| Diophantine Haar ($K = 64$ shells) | Theorem 2.14 ($K = 64$) | 64-shell sawtooth boost $\kappa _ {\mathrm{int}, 3} ^ {\mathrm{Dio}}(64) = 14.787140$ | **$0.478294 \lt 0.50$** |
| Diophantine Haar ($K = 1024$ shells) | Theorem 2.14 ($K = 1024$) | 1024-shell sawtooth boost $\kappa _ {\mathrm{int}, 3} ^ {\mathrm{Dio}}(1024) = 236.594$ | **$0.193724 \lt 0.20$** |
| **Unconditional Limit ($K \to \infty$)** | **Corollary 2.15** | **Hyperfactorial sawtooth $F _ {\mathrm{Haar}}(M) = \frac{1}{6}\ln M + 2\ln A _ {\mathrm{GK}}$** | **$0.000000$ (Resolved)** |
