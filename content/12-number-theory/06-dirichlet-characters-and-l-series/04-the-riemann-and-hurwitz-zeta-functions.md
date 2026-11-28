---
title: The Riemann and Hurwitz zeta functions
kind: api
modules:
  - Mathlib.NumberTheory.LSeries.AbstractFuncEq
  - Mathlib.NumberTheory.LSeries.MellinEqDirichlet
  - Mathlib.NumberTheory.LSeries.HurwitzZeta
  - Mathlib.NumberTheory.LSeries.HurwitzZetaEven
  - Mathlib.NumberTheory.LSeries.HurwitzZetaOdd
  - Mathlib.NumberTheory.LSeries.HurwitzZetaValues
  - Mathlib.NumberTheory.LSeries.RiemannZeta
  - Mathlib.NumberTheory.LSeries.RiemannZetaLogDeriv
  - Mathlib.NumberTheory.LSeries.HardyZ
  - Mathlib.NumberTheory.LSeries.ZetaZeros
  - Mathlib.NumberTheory.LSeries.ZMod
  - Mathlib.NumberTheory.LSeries.DirichletContinuation
explains:
  E2: [WeakFEPair, WeakFEPair.functional_equation, HurwitzZeta.hurwitzZeta, HurwitzZeta.hurwitzZeta_one_sub, completedRiemannZeta_one_sub, riemannZeta_one_sub, riemannZeta_two_mul_nat, ZMod.LFunction, DirichletCharacter.IsPrimitive.completedLFunction_one_sub, hardyZ]
  E1: auto
families: []
requires: [V15, V18, V19]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The Riemann and Hurwitz zeta functions

### Overview

The series $\zeta(s) = \sum_{n \geq 1} n^{-s}$ converges only for $\operatorname{Re} s > 1$. Riemann showed that $\zeta$ extends to a meromorphic function on $\mathbb{C}$, with a single simple pole at $s = 1$, and that the completed function $\Lambda(s) = \pi^{-s/2}\Gamma(s/2)\zeta(s)$ satisfies $\Lambda(1 - s) = \Lambda(s)$. The method is a Mellin transform of a theta function, together with the functional equation of the theta function under $t \mapsto 1/t$.

The library does this once, in an abstract form, and then applies it to a whole family. The Hurwitz zeta function $\zeta(s, a) = \sum_{n \geq 0} (n + a)^{-s}$ depends on a parameter $a \in \mathbb{R}/\mathbb{Z}$. The Riemann zeta function is the case $a = 0$. The L-function of any function $\Phi$ on `ZMod N` is a linear combination of Hurwitz zeta functions, and the L-function of a Dirichlet character is the special case of a character. So the analytic continuation, the functional equation and the special values of all these functions come from the same source. Section 2 uses the results of this section for the nonvanishing of $L(\chi, s)$ on $\operatorname{Re} s = 1$, and Chapter 7 uses them for the primes in arithmetic progressions.

### The library around it

#### Abstract functional equations

The module `Mathlib.NumberTheory.LSeries.AbstractFuncEq` states the Hecke method for general functions. A `WeakFEPair E` consists of two functions $f, g : (0, \infty) \to E$, with $E$ a complex normed space, a weight $k > 0$, a root number $\varepsilon \neq 0$ and two constants $f_0, g_0 \in E$, such that

1. $f(1/x) = \varepsilon x^k g(x)$ for $x > 0$, which is the field `WeakFEPair.h_feq`;
2. $f(x) - f_0$ and $g(x) - g_0$ decay faster than each power of $x$ as $x \to \infty$.

The Mellin transform of $f - f_0$ converges for large $\operatorname{Re} s$. The structure gives its continuation `WeakFEPair.Λ`, and an entire function `WeakFEPair.Λ₀` with
$$\Lambda(s) = \Lambda_0(s) - \frac{f_0}{s} - \frac{\varepsilon g_0}{k - s}.$$
This is `WeakFEPair.Λ₀_eq`, and `WeakFEPair.differentiable_Λ₀` says that $\Lambda_0$ is entire. The pair with the roles of $f$ and $g$ exchanged is `WeakFEPair.symm`.

**Theorem.** For each $s \in \mathbb{C}$, $\Lambda_f(k - s) = \varepsilon\,\Lambda_g(s)$.

This is `WeakFEPair.functional_equation`, and `WeakFEPair.functional_equation₀` is the version for $\Lambda_0$. The residues at $s = 0$ and $s = k$ are `WeakFEPair.Λ_residue_zero` and `WeakFEPair.Λ_residue_k`. When $f_0 = g_0 = 0$ the pair is *strong*, `IsStrongFEPair`, and then $\Lambda$ itself is entire, by `IsStrongFEPair.differentiable_Λ`. The module `Mathlib.NumberTheory.LSeries.MellinEqDirichlet` connects Mellin transforms to Dirichlet series: if $F(t) = \sum_i a_i e^{-p_i t}$, then the Mellin transform of $F$ is $\Gamma(s)\sum_i a_i p_i^{-s}$, which is `hasSum_mellin`. The variants `hasSum_mellin_pi_mul` and `hasSum_mellin_pi_mul_sq` treat $e^{-\pi p_i t}$ and $e^{-\pi r_i^2 t}$, the form of theta functions.

#### Hurwitz zeta functions

The parameter $a$ lives in `UnitAddCircle`, the circle $\mathbb{R}/\mathbb{Z}$. The library first defines an even and an odd part, each from a theta kernel built with `jacobiTheta₂`:

| Lean name | Function, for $\operatorname{Re} s > 1$ |
|---|---|
| `HurwitzZeta.hurwitzZetaEven a s` | $\frac12\sum_{n \in \mathbb{Z}} \lvert n + a \rvert^{-s}$ |
| `HurwitzZeta.hurwitzZetaOdd a s` | $\frac12\sum_{n \in \mathbb{Z}} \operatorname{sgn}(n + a)\lvert n + a \rvert^{-s}$ |
| `HurwitzZeta.hurwitzZeta a s` | the sum of the two, $\sum_{n \geq 0}(n + a)^{-s}$ for $0 \leq a \leq 1$ |
| `HurwitzZeta.cosZeta a s` | $\sum_{n \geq 1}\cos(2\pi a n)n^{-s}$ |
| `HurwitzZeta.sinZeta a s` | $\sum_{n \geq 1}\sin(2\pi a n)n^{-s}$ |
| `HurwitzZeta.expZeta a s` | $\sum_{n \geq 1}e^{2\pi i a n}n^{-s}$, equal to `HurwitzZeta.cosZeta` plus $i$ times `HurwitzZeta.sinZeta` |

The defining series are recovered by `HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re` and `HurwitzZeta.hasSum_expZeta_of_one_lt_re`. The even part uses the pair `HurwitzZeta.hurwitzEvenFEPair a` with weight $1/2$, and the odd part uses `HurwitzZeta.hurwitzOddFEPair a` with weight $3/2$, which is strong. The completed functions `HurwitzZeta.completedHurwitzZetaEven` and `HurwitzZeta.completedHurwitzZetaOdd` are built from `WeakFEPair.Λ` at $s/2$ and $(s + 1)/2$, and their functional equations pair the Hurwitz functions with the cosine and sine functions.

**Theorem.** Away from $s = 1$, $\zeta(s, a)$ is differentiable, and $(s - 1)\zeta(s, a) \to 1$ as $s \to 1$. If $s \notin -\mathbb{N}$, and $a \neq 0$ or $s \neq 1$, then
$$\zeta(1 - s, a) = (2\pi)^{-s}\Gamma(s)\left(e^{-\pi i s/2}F(a, s) + e^{\pi i s/2}F(-a, s)\right),$$
with $F(a, s)$ = `HurwitzZeta.expZeta a s`.

These are `HurwitzZeta.differentiableAt_hurwitzZeta`, `HurwitzZeta.hurwitzZeta_residue_one` and `HurwitzZeta.hurwitzZeta_one_sub`. The dual formula is `HurwitzZeta.expZeta_one_sub`. The function `expZeta a` is entire for $a \neq 0$, by `HurwitzZeta.differentiable_expZeta_of_ne_zero`. The even and odd parts are recovered by `HurwitzZeta.hurwitzZetaEven_eq` and `HurwitzZeta.hurwitzZetaOdd_eq`.

#### The Riemann zeta function

`riemannZeta` is defined from `HurwitzZeta.hurwitzZetaEven 0`, and `completedRiemannZeta` is $\Lambda(s) = \Gamma_{\mathbb{R}}(s)\zeta(s)$ with $\Gamma_{\mathbb{R}}(s) = \pi^{-s/2}\Gamma(s/2)$, `Complex.Gammaℝ`. The relation is `riemannZeta_def_of_ne_zero`. The series is `zeta_eq_tsum_one_div_nat_cpow` for $\operatorname{Re} s > 1$, and `zeta_nat_eq_tsum_of_gt_one` is the version at an integer $k > 1$.

| Lean name | Statement |
|---|---|
| `differentiableAt_riemannZeta` | $\zeta$ is differentiable at each $s \neq 1$ |
| `completedRiemannZeta_eq` | $\Lambda(s) = \Lambda_0(s) - 1/s - 1/(1 - s)$ with $\Lambda_0$ entire |
| `completedRiemannZeta_one_sub` | $\Lambda(1 - s) = \Lambda(s)$ |
| `riemannZeta_one_sub` | $\zeta(1 - s) = 2(2\pi)^{-s}\Gamma(s)\cos(\pi s/2)\zeta(s)$ for $s \notin -\mathbb{N}$, $s \neq 1$ |
| `riemannZeta_zero` | $\zeta(0) = -1/2$ |
| `riemannZeta_neg_two_mul_nat_add_one` | the trivial zeros $\zeta(-2(n + 1)) = 0$ |
| `logDeriv_riemannZeta_one_sub` | the functional equation of $\zeta'/\zeta$, with the digamma function |

The value at $s = 1$ is a junk value of the definition, not a pole. The statement of the Riemann hypothesis is the proposition `RiemannHypothesis`: each zero of $\zeta$ that is not a trivial zero and is not $1$ has real part $1/2$. The module `Mathlib.NumberTheory.LSeries.ZetaZeros` defines the set of zeros `riemannZetaZeros`. It is closed and discrete, by `isClosed_riemannZetaZeros` and `isDiscrete_riemannZetaZeros`, so each compact set contains only finitely many zeros, `IsCompact.inter_riemannZetaZeros_finite`.

On the critical line, Hardy's function `hardyZ` is $Z(t) = \operatorname{Re}\Lambda(\frac12 + it)/\lvert\Gamma_{\mathbb{R}}(\frac12 + it)\rvert$. The functional equation makes $\Lambda(\frac12 + it)$ real, by `completedRiemannZeta_half_add_mul_I_im`. So $Z$ is a continuous real function with $\lvert Z(t)\rvert = \lvert\zeta(\frac12 + it)\rvert$, by `abs_hardyZ`, and its zeros are the zeros of $\zeta$ on the line, by `hardyZ_eq_zero_iff`. A change of sign of $Z$ thus proves a zero on the critical line.

#### Special values

The module `Mathlib.NumberTheory.LSeries.HurwitzZetaValues` computes the values at integers with Bernoulli numbers and polynomials.

**Theorem (Euler).** For $k \geq 1$,
$$\zeta(2k) = \frac{(-1)^{k+1}2^{2k-1}\pi^{2k}B_{2k}}{(2k)!}, \qquad \zeta(-k) = \frac{(-1)^k B_{k+1}}{k + 1}.$$

These are `riemannZeta_two_mul_nat` and `riemannZeta_neg_nat_eq_bernoulli`. The special cases `riemannZeta_two` and `riemannZeta_four` give $\pi^2/6$ and $\pi^4/90$. For the Hurwitz function, `HurwitzZeta.hurwitzZeta_neg_nat` gives $\zeta(-k, x) = -B_{k+1}(x)/(k + 1)$ for $x \in [0, 1]$, and `HurwitzZeta.cosZeta_two_mul_nat` and `HurwitzZeta.sinZeta_two_mul_nat_add_one` evaluate the Fourier series at positive integers.

#### L-functions on ZMod N

Let $\Phi :$ `ZMod N` $\to \mathbb{C}$. The module `Mathlib.NumberTheory.LSeries.ZMod` defines
$$L(\Phi, s) = N^{-s}\sum_{j \in \mathbb{Z}/N} \Phi(j)\,\zeta(s, j/N),$$
`ZMod.LFunction Φ s`. For $\operatorname{Re} s > 1$ it is the L-series of $n \mapsto \Phi(n)$, by `ZMod.LFunction_eq_LSeries`. It is differentiable away from $s = 1$, with residue $\frac1N\sum_j \Phi(j)$ there, by `ZMod.differentiableAt_LFunction` and `ZMod.LFunction_residue_one`. It is entire when $\sum_j \Phi(j) = 0$, by `ZMod.differentiable_LFunction_of_sum_zero`. The functional equation `ZMod.LFunction_one_sub` relates $L(\Phi, 1 - s)$ to the L-function of the discrete Fourier transform `ZMod.dft Φ`, and the completed versions are `ZMod.completedLFunction_one_sub_even` and `ZMod.completedLFunction_one_sub_odd` for even and odd $\Phi$.

#### Dirichlet L-functions

The module `Mathlib.NumberTheory.LSeries.DirichletContinuation` specializes this to a Dirichlet character $\chi$. The L-function `DirichletCharacter.LFunction` of Section 2 is `ZMod.LFunction χ`. The gamma factor `DirichletCharacter.gammaFactor χ s` is $\Gamma_{\mathbb{R}}(s)$ for even $\chi$ and $\Gamma_{\mathbb{R}}(s + 1)$ for odd $\chi$, and `DirichletCharacter.completedLFunction` is the completed L-function. The root number `DirichletCharacter.rootNumber χ` is the normalized Gauss sum $g(\chi)/(i^{\delta}\sqrt{N})$, with $\delta = 0$ or $1$ for even or odd $\chi$.

**Theorem.** Let $\chi$ be a primitive character modulo $N$. Then
$$\Lambda(\chi, 1 - s) = N^{s - 1/2}\,w(\chi)\,\Lambda(\bar\chi, s)$$
for all $s$, with $w(\chi)$ the root number.

This is `DirichletCharacter.IsPrimitive.completedLFunction_one_sub`. The L-function is entire for $\chi \neq 1$, by `DirichletCharacter.differentiable_LFunction`. A change of level multiplies it by the Euler factors of the new primes, by `DirichletCharacter.LFunction_changeLevel`. For the trivial character modulo $N$, `DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta` gives $\prod_{p \mid N}(1 - p^{-s})\zeta(s)$. The trivial zeros are `DirichletCharacter.Even.LFunction_neg_two_mul_nat` and `DirichletCharacter.Odd.LFunction_neg_two_mul_nat_sub_one`.

#### Common errors

1. `riemannZeta 1` is a value, not a pole. A statement such as $\zeta(s) \neq 0$ needs the hypothesis $s \neq 1$, or a separate check of the junk value.
2. The functional equations need hypotheses that remove the poles of $\Gamma(s)$: `riemannZeta_one_sub` asks $s \neq -n$ for all $n \in \mathbb{N}$ and $s \neq 1$. The completed form `completedRiemannZeta_one_sub` needs none.
3. The parameter of `HurwitzZeta.hurwitzZeta` is in `UnitAddCircle`, so $\zeta(s, a)$ depends only on $a$ modulo $1$. The series formula $\sum_{n \geq 0}(n + a)^{-s}$ holds only for the representative $a \in [0, 1]$, as in `HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re`.

### Exercises

1. (A) Use `riemannZeta_two_mul_nat` with $B_2 = 1/6$, $B_4 = -1/30$ and $B_6 = 1/42$ to compute $\zeta(2)$, $\zeta(4)$ and $\zeta(6)$.
2. (A) Use `riemannZeta_neg_nat_eq_bernoulli` to compute $\zeta(-1)$ and $\zeta(-3)$, and check the vanishing of $\zeta(-2)$ against `riemannZeta_neg_two_mul_nat_add_one`.
3. (B) Show that $\zeta(s, 0) + \zeta(s, 1/2) = 2^s\zeta(s)$ for $\operatorname{Re} s > 1$ from the series, and deduce it for all $s \neq 1$ by analytic continuation.
4. (B) Let $\chi_4$ be the nontrivial character modulo $4$. Write $L(\chi_4, s)$ as a combination of $\zeta(s, 1/4)$ and $\zeta(s, 3/4)$, and use it to compute $L(\chi_4, 0)$.
5. (B) Derive `riemannZeta_one_sub` from `completedRiemannZeta_one_sub` with the duplication and reflection formulas for $\Gamma$.
6. (C) Let $P$ be a `WeakFEPair` over ℂ with $f = g$ and $\varepsilon = 1$. Show that $\Lambda$ is symmetric about $s = k/2$ and real on the line $\operatorname{Re} s = k/2$ when $f$ takes real values.

### Reference

<?reference?>
