---
title: Divide and conquer recurrences
kind: theory
modules:
  - Mathlib.Computability.AkraBazzi.GrowsPolynomially
  - Mathlib.Computability.AkraBazzi.SumTransform
  - Mathlib.Computability.AkraBazzi.AkraBazzi
explains:
  E3: [AkraBazziRecurrence, AkraBazziRecurrence.GrowsPolynomially, AkraBazziRecurrence.growsPolynomially_rpow, AkraBazziRecurrence.growsPolynomially_log, AkraBazziRecurrence.p, AkraBazziRecurrence.sumCoeffsExp_p_eq_one, AkraBazziRecurrence.strictAnti_sumCoeffsExp, AkraBazziRecurrence.one_mem_range_sumCoeffsExp, AkraBazziRecurrence.sumTransform, AkraBazziRecurrence.asympBound, AkraBazziRecurrence.asympBound_def', AkraBazziRecurrence.eventually_atTop_sumTransform_le, AkraBazziRecurrence.eventually_atTop_sumTransform_ge, AkraBazziRecurrence.smoothingFn, AkraBazziRecurrence.rpow_p_mul_one_sub_smoothingFn_le, AkraBazziRecurrence.T_isBigO_smoothingFn_mul_asympBound, AkraBazziRecurrence.isBigO_asympBound, AkraBazziRecurrence.isTheta_asympBound]
  E2: [AkraBazziRecurrence.h_rec, AkraBazziRecurrence.dist_r_b, AkraBazziRecurrence.T_pos, AkraBazziRecurrence.growsPolynomially_const, AkraBazziRecurrence.growsPolynomially_id, AkraBazziRecurrence.growsPolynomially_pow, AkraBazziRecurrence.GrowsPolynomially.mul, AkraBazziRecurrence.GrowsPolynomially.add, AkraBazziRecurrence.GrowsPolynomially.const_mul, AkraBazziRecurrence.GrowsPolynomially.of_isTheta, AkraBazziRecurrence.GrowsPolynomially.eventually_atTop_le_nat, AkraBazziRecurrence.continuous_sumCoeffsExp, AkraBazziRecurrence.tendsto_zero_sumCoeffsExp, AkraBazziRecurrence.tendsto_atTop_sumCoeffsExp, AkraBazziRecurrence.injective_sumCoeffsExp, AkraBazziRecurrence.min_bi, AkraBazziRecurrence.eventually_bi_mul_le_r, AkraBazziRecurrence.exists_eventually_r_le_const_mul, AkraBazziRecurrence.isBigO_apply_r_sub_b, AkraBazziRecurrence.rpow_p_mul_one_add_smoothingFn_ge, AkraBazziRecurrence.smoothingFn_mul_asympBound_isBigO_T, AkraBazziRecurrence.isBigO_symm_asympBound]
  E1: auto
families: []
requires: [V03.C06, V15.C02, V15.C03, V15.C05, V15.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Divide and conquer recurrences

### Overview

A divide and conquer algorithm splits a problem of size $n$ into smaller problems of sizes about $b_1 n, \dots, b_k n$, solves them recursively, and combines the answers. Its running time satisfies a recurrence $$T(n) = \sum_{i=1}^{k} a_i\, T(r_i(n)) + g(n),$$ where $g(n)$ is the cost of the split and of the combination, and $r_i(n)$ is $b_i n$ up to a small error, for example $\lceil n/2 \rceil$. The Akra-Bazzi theorem gives the order of growth of $T$ in one formula: $$T(n) = \Theta\Big(n^{p}\Big(1 + \sum_{u < n} \frac{g(u)}{u^{p+1}}\Big)\Big),$$ where $p$ is the unique real number with $\sum_i a_i b_i^{p} = 1$. This section defines the hypotheses, proves the existence of $p$, proves the two estimates of the sum transform, and gives the induction that proves the theorem. It then derives the cases of the master theorem and treats merge sort, binary search and the Karatsuba recurrence.

Mathlib states the theorem with a sum, not with the integral of the original paper, and for $T \colon \mathbb{N} \to \mathbb{R}$.

### Definitions

**Definition (Polynomial growth).** A function $f \colon \mathbb{R} \to \mathbb{R}$ grows polynomially if for each $b \in (0, 1)$ there are $c_1, c_2 > 0$ such that, for all large $x$ and all $u \in [bx, x]$, $$c_1 f(x) \leq f(u) \leq c_2 f(x).$$ So the values of $f$ on $[bx, x]$ are comparable with $f(x)$, with constants that depend on $b$ only.

**Definition (Akra-Bazzi recurrence).** Let $\alpha$ be a finite nonempty type of indices. A function $T \colon \mathbb{N} \to \mathbb{R}$ is an Akra-Bazzi recurrence with data $g \colon \mathbb{R} \to \mathbb{R}$, $a, b \colon \alpha \to \mathbb{R}$ and $r \colon \alpha \to \mathbb{N} \to \mathbb{N}$ if there is $n_0 > 0$ such that:

1. $a_i > 0$ and $0 < b_i < 1$ for each $i$;
2. $g(x) \geq 0$ for $x \geq 0$, and $g$ grows polynomially;
3. $T(n) = \sum_i a_i T(r_i(n)) + g(n)$ for $n \geq n_0$, and $T(n) > 0$ for $n < n_0$;
4. $r_i(n) < n$ for $n \geq n_0$;
5. $r_i(n) - b_i n = o(n / \log^2 n)$ as $n \to \infty$, for each $i$.

The structure `AkraBazziRecurrence T g a b r` records these fields.

**Definition (Exponent).** The exponent is the real number $p$ with $\sum_i a_i b_i^{p} = 1$. Mathlib defines `p a b` as `Function.invFun` of the map $p \mapsto \sum_i a_i b_i^{p}$, applied to $1$.

**Definition (Sum transform).** For $p \in \mathbb{R}$, $g$ and $m \leq n$, $$\Sigma_p g(m, n) = n^{p} \sum_{u = m}^{n - 1} \frac{g(u)}{u^{p+1}}.$$ The asymptotic bound is $f(n) = n^{p} + \Sigma_p g(0, n) = n^{p}\big(1 + \sum_{u < n} g(u)/u^{p+1}\big)$ (`asympBound` and `asympBound_def'`).

In Lean the term $u = 0$ is $g(0)/0^{p+1}$, and the division by zero gives $0$ whenever $p + 1 \neq 0$.

**Definition (Smoothing function).** $\varepsilon(x) = 1/\log x$ (`smoothingFn`). The proof bounds $T$ by multiples of $(1 \mp \varepsilon(n)) f(n)$.

### Theorems and proofs

**Proposition (The exponent).** Let $\varphi(q) = \sum_i a_i b_i^{q}$. Then $\varphi$ is continuous and strictly decreasing, $\varphi(q) \to \infty$ as $q \to -\infty$, and $\varphi(q) \to 0$ as $q \to \infty$. So there is exactly one $p$ with $\varphi(p) = 1$.

*Proof.* For $0 < b < 1$, $q \mapsto b^{q} = e^{q \log b}$ is continuous and strictly decreasing, since $\log b < 0$. It tends to $\infty$ at $-\infty$ and to $0$ at $\infty$. A sum of such functions with positive coefficients has the same properties, since $\alpha$ is nonempty. By the limits, $\varphi(q_1) > 1$ and $\varphi(q_2) < 1$ for some $q_1 < q_2$. By the intermediate value theorem, $\varphi(p) = 1$ for some $p$. A strictly decreasing function is injective, so $p$ is unique, and `Function.invFun` selects it. $\square$

**Proposition (Examples of polynomial growth).** The constant functions, $x \mapsto x^{q}$ for each real $q$, and $\log$ grow polynomially. Products of functions that grow polynomially grow polynomially, and so do sums of eventually nonnegative ones.

*Proof.* Fix $b \in (0, 1)$. For $x > 0$ and $u \in [bx, x]$, $u^{q}$ lies between $(bx)^{q} = b^{q} x^{q}$ and $x^{q}$. So $c_1 = \min(1, b^{q})$ and $c_2 = \max(1, b^{q})$ work. For $\log$ and $x \geq b^{-2}$, $$\log x \geq \log u \geq \log x + \log b \geq \log x - \tfrac{1}{2} \log x = \tfrac{1}{2} \log x,$$ since $-\log b \leq \frac{1}{2}\log x$. So $c_1 = 1/2$ and $c_2 = 1$. For a product $fh$ of eventually nonnegative functions, multiply the bounds: $c_1 c_1'$ and $c_2 c_2'$. For a sum of eventually nonnegative functions, take $\min(c_1, c_1')$ and $\max(c_2, c_2')$. $\square$

**Lemma (Estimates of the sum transform).** For an Akra-Bazzi recurrence there are $c, C > 0$ such that, for all large $n$ and each $i$, $$c\, g(n) \leq \Sigma_p g(r_i(n), n) \leq C\, g(n).$$

*Proof.* By the hypothesis on $r_i$, there are constants $0 < \beta < \gamma < 1$ with $\beta n \leq r_i(n) \leq \gamma n$ for all large $n$ and each $i$. Mathlib takes $\beta = b_{\min}/2$, the half of the least $b_i$. Each $u$ in the sum lies in $[\beta n, n]$. By polynomial growth of $g$ with the constant $\beta$, $c_1 g(n) \leq g(u) \leq c_2 g(n)$. By the estimate for powers, $u^{p+1}$ lies between $d_1 n^{p+1}$ and $d_2 n^{p+1}$ with $d_1, d_2 > 0$ that depend on $\beta$ and $p$. The number of terms is $n - r_i(n)$, which lies between $(1 - \gamma) n$ and $n$. So $$\Sigma_p g(r_i(n), n) \leq n^{p} \cdot n \cdot \frac{c_2\, g(n)}{d_1 n^{p+1}} = \frac{c_2}{d_1} g(n),$$ and $\Sigma_p g(r_i(n), n) \geq n^{p} (1-\gamma) n \, c_1 g(n) / (d_2 n^{p+1}) = \frac{(1-\gamma) c_1}{d_2} g(n)$. $\square$

**Lemma (The smoothing gain).** For all large $n$ and each $i$, $$r_i(n)^{p}\big(1 - \varepsilon(r_i(n))\big) \leq b_i^{p} n^{p} \big(1 - \varepsilon(n)\big), \qquad r_i(n)^{p}\big(1 + \varepsilon(r_i(n))\big) \geq b_i^{p} n^{p} \big(1 + \varepsilon(n)\big).$$

*Proof.* Prove the first inequality; the second is the same with the signs changed. Let $q(x) = x^{p}(1 - \varepsilon(x))$, and fix $i$. First compare $q(b_i n)$ with the right side. Since $\log(b_i n) = \log n + \log b_i < \log n$, $$\varepsilon(b_i n) - \varepsilon(n) = \frac{-\log b_i}{\log n \, \log(b_i n)} \geq \frac{\kappa}{\log^2 n}, \qquad \kappa = -\log b_i > 0.$$ So $q(b_i n) \leq b_i^{p} n^{p}(1 - \varepsilon(n)) - b_i^{p} \kappa\, n^{p}/\log^2 n$. Next compare $q(r_i(n))$ with $q(b_i n)$. The derivative $q'(x) = p x^{p-1}(1 - \varepsilon(x)) + x^{p-1}/\log^2 x$ is $O(x^{p-1})$, and it grows polynomially. By the mean value theorem, $|q(r_i(n)) - q(b_i n)| \leq \sup |q'| \cdot |r_i(n) - b_i n|$, with the supremum over a point between $r_i(n)$ and $b_i n$. Both points lie in $[\beta n, n]$, so the supremum is $O(n^{p-1})$, and the hypothesis on $r_i$ gives $$q(r_i(n)) - q(b_i n) = O(n^{p-1}) \cdot o\Big(\frac{n}{\log^2 n}\Big) = o\Big(\frac{n^{p}}{\log^2 n}\Big).$$ For large $n$ this error is less than $b_i^{p} \kappa\, n^{p}/\log^2 n$, and the two estimates give the claim. $\square$

This lemma explains the hypothesis $o(n/\log^2 n)$: the gain from the smoothing factor has the order $n^{p}/\log^2 n$, and it must absorb the rounding error.

**Theorem (Akra-Bazzi).** Let $T$ be an Akra-Bazzi recurrence with exponent $p$ and asymptotic bound $f$. Then $T = \Theta(f)$ as $n \to \infty$.

*Proof.* First, $T(n) > 0$ for each $n$, by strong induction: for $n < n_0$ this is a hypothesis, and for $n \geq n_0$, $T(n)$ is a sum of positive multiples of earlier values plus $g(n) \geq 0$. Also $f(n) > 0$ for large $n$.

Upper bound. The aim is $T(n) \leq C (1 - \varepsilon(n)) f(n)$ for a constant $C$ and all large $n$. Since $1 - \varepsilon(n) \to 1$, this gives $T = O(f)$. Mathlib uses an induction principle for $O$ on $\mathbb{N}$: for nonnegative $T$ and eventually positive $h$, it suffices that for each large $m_0$ there is $C_0$ such that, for all large $n$ and all $C \geq C_0$, the bound $T(m) \leq C h(m)$ for $m_0 \leq m < n$ implies $T(n) \leq C h(n)$. The finitely many values below the threshold go into the constant.

For the step, let $n$ be large and assume the bound for all $m$ with $m_0 \leq m < n$. Each $r_i(n)$ is such an $m$ for large $n$. Write $S(m) = \sum_{u < m} g(u)/u^{p+1}$, so $f(m) = m^{p}(1 + S(m))$ and $n^{p}(S(n) - S(r_i(n))) = \Sigma_p g(r_i(n), n)$. By the smoothing gain, $$(1 - \varepsilon(r_i(n))) f(r_i(n)) \leq b_i^{p} n^{p}(1 - \varepsilon(n))(1 + S(r_i(n))) = b_i^{p} (1 - \varepsilon(n)) \big(f(n) - \Sigma_p g(r_i(n), n)\big).$$ By the lower estimate of the sum transform, the last factor is at most $f(n) - c\, g(n)$. With the recurrence, the hypothesis of induction and $\sum_i a_i b_i^{p} = 1$, $$T(n) \leq C (1 - \varepsilon(n)) \big(f(n) - c\, g(n)\big) + g(n) = C (1 - \varepsilon(n)) f(n) - \big(C c (1 - \varepsilon(n)) - 1\big) g(n).$$ For large $n$, $1 - \varepsilon(n) \geq 1/2$, so $C \geq 2/c$ makes the last bracket nonnegative, and $T(n) \leq C(1 - \varepsilon(n)) f(n)$.

Lower bound. The same induction with $(1 + \varepsilon(n)) f(n)$, the second inequality of the smoothing gain and the upper estimate of the sum transform gives $(1 + \varepsilon(n)) f(n) \leq C' T(n)$ for large $n$. The extra term is now $+g(n)$ on the side of $T$, and $C'$ large makes $C' g(n) \geq (1 + \varepsilon(n)) C g(n)$. So $f = O(T)$, and $T = \Theta(f)$. $\square$

**Corollary (Master theorem).** Also assume that $g(n) = \Theta(n^{t})$ for a real $t$. Then $T(n) = \Theta(n^{p})$ if $t < p$, $T(n) = \Theta(n^{p} \log n)$ if $t = p$, and $T(n) = \Theta(n^{t})$ if $t > p$.

*Proof.* By the theorem, $T = \Theta(f)$, and $f(n) = n^{p}(1 + S(n))$ with $S(n) = \Theta\big(\sum_{1 \leq u < n} u^{t - p - 1}\big)$ up to an additive constant from the finitely many small $u$. If $t < p$, the exponent $t - p - 1$ is less than $-1$, the series converges, and $1 + S(n) = \Theta(1)$. If $t = p$, the sum is the harmonic sum $H_{n-1} = \log n + O(1)$. If $t > p$, compare with the integral: $\sum_{1 \leq u < n} u^{t-p-1} = \Theta(n^{t-p})$, and $n^{p} \cdot n^{t-p} = n^{t}$. $\square$

The index of this edition has no declaration for the master theorem; the source file lists it as future work.

### Examples

**Example (Merge sort).** Merge sort satisfies $T(n) = T(\lceil n/2 \rceil) + T(\lfloor n/2 \rfloor) + n$ for $n \geq 2$, with $T(0) = T(1) = 1$. Take $\alpha$ with two elements, $a_1 = a_2 = 1$, $b_1 = b_2 = 1/2$, $r_1(n) = \lceil n/2 \rceil$, $r_2(n) = \lfloor n/2 \rfloor$, $g(x) = x$ and $n_0 = 2$. The hypotheses hold: $\lceil n/2 \rceil < n$ for $n \geq 2$, and $|r_i(n) - n/2| \leq 1/2$, which is $o(n/\log^2 n)$. The exponent solves $2 \cdot 2^{-p} = 1$, so $p = 1$. The bound is $$f(n) = n\Big(1 + \sum_{1 \leq u < n} \frac{u}{u^{2}}\Big) = n(1 + H_{n-1}),$$ where the term $u = 0$ is $0$. So $T(n) = \Theta(n \log n)$. This is the case $t = p = 1$ of the master theorem.

**Example (Binary search).** The recurrence $T(n) = T(\lfloor n/2 \rfloor) + 1$ for $n \geq 2$, with $T(0) = T(1) = 1$, has one index, $a = 1$, $b = 1/2$ and $g = 1$. Then $2^{-p} = 1$ gives $p = 0$, and $f(n) = 1 + \sum_{1 \leq u < n} 1/u = 1 + H_{n-1}$. So $T(n) = \Theta(\log n)$.

**Example (Karatsuba multiplication).** The Karatsuba algorithm multiplies two numbers of $n$ digits with three products of numbers of about $n/2$ digits and a linear amount of extra work: $T(n) = 3\,T(\lceil n/2 \rceil) + n$ for $n \geq 2$. Here $3 \cdot 2^{-p} = 1$, so $p = \log_2 3 \approx 1.585$. The sum $\sum_{u \geq 1} u / u^{p+1} = \sum_{u \geq 1} u^{-p}$ converges since $p > 1$. So $f(n) = \Theta(n^{\log_2 3})$ and $T(n) = \Theta(n^{\log_2 3})$, against $\Theta(n^2)$ for the school method.

**Example (Unequal parts).** Let $T(n) = T(\lfloor n/2 \rfloor) + T(\lfloor n/4 \rfloor) + n$. The exponent solves $2^{-p} + 4^{-p} = 1$. With $y = 2^{-p}$, $y^2 + y - 1 = 0$, so $y = (\sqrt 5 - 1)/2$ and $p = \log_2 \frac{1 + \sqrt 5}{2} \approx 0.694$. Since $p < 1 = t$, the master theorem gives $T(n) = \Theta(n)$. The master theorem in its textbook form, with one subproblem size, does not cover this recurrence.

**Counterexample (A function without polynomial growth).** The function $f(x) = 2^{x}$ does not grow polynomially. For $b = 1/2$ and $u = x/2$, $f(u)/f(x) = 2^{-x/2} \to 0$, so no $c_1 > 0$ works. The theorem does not apply to $T(n) = 2T(\lfloor n/2 \rfloor) + 2^{n}$.

### The library around it

::: mathlib
`AkraBazziRecurrence` · `Mathlib.Computability.AkraBazzi.SumTransform`

`AkraBazziRecurrence T g a b r` is a structure over `[Fintype α] [Nonempty α]` with the fields `n₀`, `n₀_gt_zero`, `a_pos`, `b_pos`, `b_lt_one`, `g_nonneg`, `g_grows_poly`, `h_rec`, `T_gt_zero'`, `r_lt_n` and `dist_r_b`. The last field is `(fun n => (r i n : ℝ) - b i * n) =o[atTop] fun n => n / (log n) ^ 2`. `T_pos` proves that `T` is positive.

<?decl AkraBazziRecurrence?>
:::

::: mathlib
`AkraBazziRecurrence.GrowsPolynomially` · `Mathlib.Computability.AkraBazzi.GrowsPolynomially`

The definition of polynomial growth, with `growsPolynomially_const`, `growsPolynomially_id`, `growsPolynomially_pow`, `growsPolynomially_rpow`, `growsPolynomially_zpow` and `growsPolynomially_log`. The closure lemmas are `GrowsPolynomially.mul`, `const_mul`, `add` (for eventually nonnegative functions), `add_isLittleO`, `inv`, `div`, `rpow`, `pow` and `of_isTheta`. `eventually_atTop_le_nat` and `eventually_atTop_ge_nat` give the bounds along `ℕ`.

<?decl AkraBazziRecurrence.GrowsPolynomially?>
:::

::: mathlib
`AkraBazziRecurrence.asympBound` · `Mathlib.Computability.AkraBazzi.SumTransform`

`p a b` is the exponent, with `sumCoeffsExp_p_eq_one`, and the lemmas `continuous_sumCoeffsExp`, `strictAnti_sumCoeffsExp`, `tendsto_zero_sumCoeffsExp`, `tendsto_atTop_sumCoeffsExp`, `one_mem_range_sumCoeffsExp` and `injective_sumCoeffsExp` on the map $q \mapsto \sum_i a_i b_i^{q}$. `sumTransform p g n₀ n` is `n ^ p * ∑ u ∈ Finset.Ico n₀ n, g u / u ^ (p + 1)`, and `asympBound g a b n` is `n ^ p a b + sumTransform (p a b) g 0 n`. `eventually_atTop_sumTransform_le` and `eventually_atTop_sumTransform_ge` are the two estimates, and `smoothingFn` is $1/\log$.

<?decl AkraBazziRecurrence.asympBound?>
:::

::: mathlib
`AkraBazziRecurrence.isTheta_asympBound` · `Mathlib.Computability.AkraBazzi.AkraBazzi`

The main theorem: `T =Θ[atTop] asympBound g a b`, from `isBigO_asympBound` and `isBigO_symm_asympBound`. The parts are `rpow_p_mul_one_sub_smoothingFn_le`, `rpow_p_mul_one_add_smoothingFn_ge`, `isBigO_apply_r_sub_b` (the mean value step), `T_isBigO_smoothingFn_mul_asympBound` and `smoothingFn_mul_asympBound_isBigO_T`.

<?decl AkraBazziRecurrence.isTheta_asympBound?>
:::

::: mathlib
`Asymptotics.isBigO_nat_atTop_induction_of_eventually_pos` · `Mathlib.Analysis.Asymptotics.Lemmas`

The induction principle for `f =O[atTop] g` on `ℕ` that the two halves of the proof use: if `f` is eventually nonnegative, `g` is eventually positive, and the bound propagates from `Finset.Ico n₀ n` to `n` for all large constants, then `f =O[atTop] g`.

<?decl Asymptotics.isBigO_nat_atTop_induction_of_eventually_pos?>
:::

Common errors of a learner: The first error is to give `r i n` as a real number such as `n / 2`; the field `r` has type `α → ℕ → ℕ`, so write `⌈n / 2⌉₊` or `n / 2` in `ℕ`, and prove `dist_r_b` for that function. The second error is to forget `T_gt_zero'`: the theorem needs `T n > 0` for `n < n₀`, and a recurrence with `T 0 = 0` must start at a larger `n₀` or change its first values. The third error is to expect `p a b` to compute; it is defined with `Function.invFun`, and its value comes from `sumCoeffsExp_p_eq_one` and `injective_sumCoeffsExp`. The fourth error is to read `asympBound` as a closed form; it is the sum, and the step to $n \log n$ or $n^{t}$ is a separate estimate.

### Exercises

1. (A) Find the exponent $p$ and the order of $T$ for $T(n) = 4T(\lfloor n/2 \rfloor) + n$. Hint: $4 \cdot 2^{-p} = 1$, so $p = 2 > t = 1$.
2. (A) Find the order of $T(n) = 7T(\lceil n/2 \rceil) + n^2$, the recurrence of the Strassen algorithm. Hint: $p = \log_2 7 > 2$.
3. (A) Show that $x \mapsto x^{2} + \log x$ grows polynomially, with the closure lemmas. Hint: both terms are eventually nonnegative.
4. (B) Show that $T(n) = 2T(\lfloor n/2 \rfloor) + n \log n$ gives $T(n) = \Theta(n \log^2 n)$. Hint: $p = 1$ and $\sum_{u < n} \log u / u = \Theta(\log^2 n)$.
5. (B) Show that the rounding $r(n) = \lfloor n/2 \rfloor + \lfloor \sqrt n \rfloor$ satisfies the hypothesis on $r$, and that $r(n) = \lfloor n/2 \rfloor + \lfloor n/\log n \rfloor$ does not. Hint: compare with $n / \log^2 n$.
6. (B) Prove that a function that grows polynomially and is positive for large $x$ satisfies $f(x) \leq x^{k}$ for some $k$ and all large $x$. Hint: iterate the bound for $b = 1/2$ on $[x/2, x]$, $[x/4, x/2]$, and so on.
7. (C) Solve $T(n) = T(\lfloor n/3 \rfloor) + T(\lfloor 2n/3 \rfloor) + n$. Hint: $3^{-p} + (2/3)^{p} = 1$ holds for $p = 1$.

### Notes and history

Akra and Bazzi published the theorem in 1998, with an integral in place of the sum and a real variable. The notes of Leighton give a version for sizes with rounding errors, and Eberl formalized the theorem in Isabelle. The Mathlib source lists these three references. The master theorem, with one subproblem size and $g(n) = \Theta(n^{t})$, appeared in textbooks on algorithms before the general theorem.

The three Mathlib files `Mathlib.Computability.AkraBazzi.GrowsPolynomially`, `Mathlib.Computability.AkraBazzi.SumTransform` and `Mathlib.Computability.AkraBazzi.AkraBazzi` are by Frédéric Dupuis, read from their headers.

### Reference

<?reference?>
