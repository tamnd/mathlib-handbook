---
title: Lp seminorms and the inequalities of Hölder and Minkowski
kind: theory
modules:
  - Mathlib.MeasureTheory.Function.LpSeminorm.Defs
  - Mathlib.MeasureTheory.Function.LpSeminorm.Basic
  - Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
  - Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
  - Mathlib.MeasureTheory.Function.EssSup
  - Mathlib.MeasureTheory.Integral.MeanInequalities
explains:
  E3: [MeasureTheory.eLpNorm, MeasureTheory.MemLp, essSup, ENNReal.lintegral_mul_le_Lp_mul_Lq, ENNReal.lintegral_Lp_add_le, MeasureTheory.eLpNorm_add_le]
  E2: [MeasureTheory.eLpNorm', MeasureTheory.eLpNormEssSup, MeasureTheory.eLpNorm_eq_lintegral_rpow_eNorm_toReal, MeasureTheory.eLpNorm_one_eq_lintegral_eNorm, MeasureTheory.eLpNorm_exponent_top, MeasureTheory.eLpNorm_of_not_aestronglyMeasurable, essSup_eq_sInf, ENNReal.ae_le_essSup, MeasureTheory.eNorm_ae_le_eLpNormEssSup, MeasureTheory.eLpNorm_eq_zero_iff, MeasureTheory.MemLp.add, MeasureTheory.eLpNorm_add_le', MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ, MeasureTheory.MemLp.mono_exponent, MeasureTheory.eLpNorm_smul_le_mul_eLpNorm]
  E1: auto
families: []
requires: [V15, V18.C04, V18.C05]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Lp seminorms and the inequalities of Hölder and Minkowski

### Overview

For $1 \le p < \infty$, the quantity $\|f\|_p = (\int |f|^p \, d\mu)^{1/p}$ measures the size of a function in a way that weighs large values more as $p$ grows. This section defines it for all $0 < p \le \infty$ and proves the two inequalities that make it a seminorm: Hölder's inequality $\int |fg| \le \|f\|_p \|g\|_q$ and Minkowski's inequality $\|f + g\|_p \le \|f\|_p + \|g\|_p$. It ends with the comparison of the exponents on a space of finite measure.

### Definitions

Let $(X, \mu)$ be a measure space and $f : X \to E$ measurable, with $E = \mathbb{R}$, $\mathbb{C}$ or a normed space.

**Definition (The $L^p$ seminorm).** For $0 < p < \infty$,
$$\|f\|_p = \Big( \int_X |f|^p \, d\mu \Big)^{1/p} \in [0, \infty].$$

**Definition (Essential supremum).** For $h : X \to [0, \infty]$, the essential supremum is $\operatorname{ess\,sup} h = \inf\{a \in [0, \infty] : \mu(\{h > a\}) = 0\}$. Then $\|f\|_\infty = \operatorname{ess\,sup} |f|$.

**Definition ($\mathcal{L}^p$).** The function $f$ belongs to $\mathcal{L}^p(\mu)$ if $\|f\|_p < \infty$.

**Definition (Conjugate exponents).** Exponents $p, q \in [1, \infty]$ are conjugate if $\frac{1}{p} + \frac{1}{q} = 1$, with $\frac{1}{\infty} = 0$.

The value $\|f\|_p$ does not change when $f$ changes on a null set. For $p < \infty$ this holds because the integral does not see null sets. For $p = \infty$ it is part of the next lemma.

### Theorems and proofs

**Lemma 1 (The essential supremum is attained).** For measurable $h \ge 0$, $h \le \operatorname{ess\,sup} h$ almost everywhere.

*Proof.* Let $M = \operatorname{ess\,sup} h$. If $M = \infty$ there is nothing to prove. Otherwise choose $a_n$ in the defining set with $a_n \downarrow M$. Then $\{h > M\} = \bigcup_n \{h > a_n\}$ is a countable union of null sets, so it is null. $\square$

**Theorem 2 (Hölder's inequality).** Let $p, q$ be conjugate. Then $\int |f g| \, d\mu \le \|f\|_p \, \|g\|_q$.

*Proof.* First let $p = 1$ and $q = \infty$. By Lemma 1, $|fg| \le |f| \, \|g\|_\infty$ almost everywhere, and integration gives the result. The case $p = \infty$ is the same.

Now let $1 < p < \infty$. If $\|f\|_p = 0$, then $|f|^p$ has integral zero, so $f = 0$ almost everywhere and the left side is $0$. The same holds if $\|g\|_q = 0$. If one of the norms is $\infty$ and the other is positive, the right side is $\infty$. So let $0 < \|f\|_p, \|g\|_q < \infty$, and put $F = |f| / \|f\|_p$ and $G = |g| / \|g\|_q$. Then $\int F^p = \int G^q = 1$. Young's inequality of Volume 15 gives $ab \le \frac{a^p}{p} + \frac{b^q}{q}$ for $a, b \ge 0$. With $a = F(x)$ and $b = G(x)$, integration gives
$$\int F G \, d\mu \le \frac{1}{p} \int F^p \, d\mu + \frac{1}{q} \int G^q \, d\mu = \frac{1}{p} + \frac{1}{q} = 1.$$
Multiply by $\|f\|_p \, \|g\|_q$. $\square$

**Theorem 3 (Minkowski's inequality).** Let $1 \le p \le \infty$. Then $\|f + g\|_p \le \|f\|_p + \|g\|_p$.

*Proof.* For $p = 1$, integrate $|f + g| \le |f| + |g|$. For $p = \infty$, Lemma 1 gives $|f + g| \le \|f\|_\infty + \|g\|_\infty$ almost everywhere, so $\|f + g\|_\infty \le \|f\|_\infty + \|g\|_\infty$.

Let $1 < p < \infty$, and let the right side be finite. The function $t \mapsto t^p$ is convex, so $\big(\frac{a + b}{2}\big)^p \le \frac{a^p + b^p}{2}$, and $|f + g|^p \le 2^{p - 1}(|f|^p + |g|^p)$. So $S = \int |f + g|^p \, d\mu$ is finite. If $S = 0$ there is nothing to prove. Let $q = \frac{p}{p - 1}$ be the conjugate exponent. Then
$$S \le \int |f| \, |f + g|^{p - 1} \, d\mu + \int |g| \, |f + g|^{p - 1} \, d\mu \le \big(\|f\|_p + \|g\|_p\big) \Big( \int |f + g|^{(p - 1) q} \, d\mu \Big)^{1/q},$$
by Hölder applied to each term. Since $(p - 1)q = p$, the last factor is $S^{1/q}$. Divide by $S^{1/q}$, which is finite and positive: $S^{1 - 1/q} = S^{1/p} = \|f + g\|_p \le \|f\|_p + \|g\|_p$. $\square$

So $\mathcal{L}^p(\mu)$ is a vector space for $1 \le p \le \infty$, and $\|\cdot\|_p$ is a seminorm on it. It is not a norm: $\|f\|_p = 0$ exactly when $f = 0$ almost everywhere. Section 2 removes this defect.

**Proposition 4 (Comparison of exponents).** Let $\mu(X) < \infty$ and $0 < p \le q \le \infty$. Then $\|f\|_p \le \|f\|_q \, \mu(X)^{1/p - 1/q}$. In particular $\mathcal{L}^q(\mu) \subseteq \mathcal{L}^p(\mu)$.

*Proof.* For $q = \infty$, integrate $|f|^p \le \|f\|_\infty^p$. For $q < \infty$, put $r = q/p \ge 1$ and let $r'$ be its conjugate exponent, with $1/r' = 1 - p/q$. Hölder for $|f|^p$ and $1$ gives
$$\int |f|^p \, d\mu \le \Big( \int |f|^q \, d\mu \Big)^{p/q} \mu(X)^{1 - p/q}.$$
Take the power $1/p$. $\square$

::: mathlib
`MeasureTheory.eLpNorm` · `Mathlib.MeasureTheory.Function.LpSeminorm.Defs`

Mathlib writes `eLpNorm f p μ : ℝ≥0∞` with `p : ℝ≥0∞`. The definition has three cases: `0` for `p = 0`, `eLpNormEssSup f μ` for `p = ∞`, and `eLpNorm' f p.toReal μ` otherwise, where `eLpNorm' f q μ = (∫⁻ a, ‖f a‖ₑ ^ q ∂μ) ^ (1/q)`. In this edition the value is `∞` when `f` is not a.e. strongly measurable (`eLpNorm_of_not_aestronglyMeasurable`). Then `MemLp f p μ` is `eLpNorm f p μ < ∞`. To compute, use `eLpNorm_eq_lintegral_rpow_eNorm_toReal`, `eLpNorm_one_eq_lintegral_eNorm` and `eLpNorm_exponent_top`. The value in `ℝ≥0∞` avoids a separate proof of finiteness before each inequality.

<?decl MeasureTheory.eLpNorm?>
<?decl MeasureTheory.MemLp?>
<?decl MeasureTheory.eLpNorm_eq_lintegral_rpow_eNorm_toReal?>
<?decl MeasureTheory.eLpNorm_eq_zero_iff?>
:::

::: mathlib
`essSup` · `Mathlib.MeasureTheory.Function.EssSup`

Mathlib defines `essSup f μ` as the limit superior of `f` along the filter `ae μ`, for values in any conditionally complete lattice. The lemma `essSup_eq_sInf` gives the formula of the definition above. Lemma 1 is `ENNReal.ae_le_essSup`, and for norms it is `eNorm_ae_le_eLpNormEssSup`.

<?decl essSup?>
<?decl essSup_eq_sInf?>
<?decl ENNReal.ae_le_essSup?>
:::

::: mathlib
`ENNReal.lintegral_mul_le_Lp_mul_Lq` · `Mathlib.MeasureTheory.Integral.MeanInequalities`

Hölder for functions with values in `ℝ≥0∞` is `ENNReal.lintegral_mul_le_Lp_mul_Lq`, with `p.HolderConjugate q` for real exponents. Its proof is the normalization above, with Young's inequality `ENNReal.young_inequality` and a separate treatment of the values $0$ and $\infty$. Minkowski in the same setting is `ENNReal.lintegral_Lp_add_le`. For `eLpNorm` the forms are `eLpNorm_smul_le_mul_eLpNorm`, with a class `HolderTriple p q r` for $\frac{1}{p} + \frac{1}{q} = \frac{1}{r}$, and `eLpNorm_add_le (hp1 : 1 ≤ p)`, which needs no measurability.

<?decl ENNReal.lintegral_mul_le_Lp_mul_Lq?>
<?decl ENNReal.lintegral_Lp_add_le?>
<?decl MeasureTheory.eLpNorm_add_le?>
<?decl MeasureTheory.eLpNorm_smul_le_mul_eLpNorm?>
:::

### Examples

**Example (Powers on the interval and on the half line).** Let $a > 0$ and $f(x) = x^{-a}$. On $(0, 1)$ with Lebesgue measure, $\int_0^1 x^{-ap} \, dx$ is $\frac{1}{1 - ap}$ if $ap < 1$ and $\infty$ otherwise (Chapter 8, Section 1). So $f \in \mathcal{L}^p(0, 1)$ exactly when $p < 1/a$. On $(1, \infty)$, the integral $\int_1^\infty x^{-ap} \, dx$ is finite exactly when $ap > 1$. So $f \in \mathcal{L}^p(1, \infty)$ exactly when $p > 1/a$. With $a = 1/2$: $x^{-1/2}$ on $(0, 1)$ is in $\mathcal{L}^1$ but not in $\mathcal{L}^2$, which agrees with Proposition 4. The function $x^{-1}$ on $(1, \infty)$ is in $\mathcal{L}^2$ but not in $\mathcal{L}^1$. So Proposition 4 fails when $\mu(X) = \infty$, and on $(0, \infty)$ neither of $\mathcal{L}^1$ and $\mathcal{L}^2$ contains the other.

**Counterexample (Minkowski fails for $p < 1$).** On $[0, 1]$ let $f = \mathbf{1}_{[0, 1/2]}$ and $g = \mathbf{1}_{(1/2, 1]}$. Then $\|f\|_p = \|g\|_p = 2^{-1/p}$ and $\|f + g\|_p = 1$. For $0 < p < 1$, $\|f\|_p + \|g\|_p = 2^{1 - 1/p} < 1$. So $\|\cdot\|_p$ is not a seminorm for $p < 1$. The proof of Theorem 3 breaks because $t \mapsto t^p$ is concave there, and Hölder needs $p \ge 1$.

**Example (Equality in Hölder).** On $[0, 1]$ let $f(x) = x$, $p = q = 2$, and $g = f$. Then $\int fg = \int_0^1 x^2 \, dx = \frac{1}{3}$ and $\|f\|_2 \|g\|_2 = \frac{1}{3}$. Equality holds, as it does in general when $|f|^p$ and $|g|^q$ are proportional, which is the case of equality in Young.

### The library around it

::: mathlib
`MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ` · `Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp`

Proposition 4 is `eLpNorm_le_eLpNorm_mul_rpow_measure_univ`, and the inclusion is `MemLp.mono_exponent`, with `[IsFiniteMeasure μ]`. For a probability measure, `eLpNorm_le_eLpNorm_of_exponent_le` drops the factor. For $p < 1$, Mathlib still has a triangle inequality with a constant: `eLpNorm_add_le'` multiplies by `LpAddConst p`, which is $2^{1/p - 1}$ for $0 < p < 1$ and $1$ otherwise.

<?decl MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ?>
<?decl MeasureTheory.MemLp.mono_exponent?>
<?decl MeasureTheory.eLpNorm_add_le'?>
:::

The closure of `MemLp` under addition is `MemLp.add`, a direct consequence of `eLpNorm_add_le`.

Common errors of a learner:

- Using `eLpNorm f 2 μ` and expecting a real number. It is in `ℝ≥0∞`; the norm in `ℝ` comes in Section 2.
- Forgetting the measurability in `MemLp`. In this edition, `eLpNorm f p μ` is `∞` for a function that is not a.e. strongly measurable, so `MemLp` contains the measurability.
- Applying Proposition 4 on $\mathbb{R}$ with Lebesgue measure. The first example shows that it fails there.
- Writing $\|f\|_\infty = \sup |f|$. The essential supremum ignores null sets: $\|\mathbf{1}_{\mathbb{Q}}\|_\infty = 0$.

### Exercises

1. (A) Compute $\|f\|_p$ for $f = \mathbf{1}_A$ and every $0 < p \le \infty$.
2. (A) Show that $\|cf\|_p = |c| \, \|f\|_p$ for $c \in \mathbb{R}$.
3. (A) Show that $\|fg\|_1 \le \|f\|_1 \, \|g\|_\infty$ and give an example of equality.
4. (B) Let $\mu(X) = 1$. Show that $\|f\|_p \to \|f\|_\infty$ as $p \to \infty$. Hint: for $a < \|f\|_\infty$, bound $\|f\|_p$ below by $a \, \mu(\{|f| > a\})^{1/p}$.
5. (B) Let $p < r < q$ and $\frac{1}{r} = \frac{\theta}{p} + \frac{1 - \theta}{q}$. Show that $\|f\|_r \le \|f\|_p^\theta \, \|f\|_q^{1 - \theta}$. Hint: Hölder for $|f|^{\theta r}$ and $|f|^{(1 - \theta) r}$ with the exponents $\frac{p}{\theta r}$ and $\frac{q}{(1 - \theta) r}$.
6. (B) Show that $\mathcal{L}^p \cap \mathcal{L}^\infty \subseteq \mathcal{L}^q$ for $p \le q$, on every measure space. Hint: $|f|^q \le \|f\|_\infty^{q - p} |f|^p$ almost everywhere.
7. (C) Let $f \in \mathcal{L}^1(\mathbb{R})$, $g \in \mathcal{L}^p(\mathbb{R})$ with $1 \le p < \infty$, and $h(x) = \int |f(y)| \, |g(x - y)| \, dy$. Show that $\|h\|_p \le \|f\|_1 \, \|g\|_p$. Hint: write $|f| |g(x - \cdot)| = |f|^{1/q} \cdot |f|^{1/p} |g(x - \cdot)|$, apply Hölder in $y$, then Tonelli (Chapter 6, Section 2) and the translation invariance of Lebesgue measure.

### Notes and history

The two inequalities carry the names of Otto Hölder and Hermann Minkowski. Minkowski used his inequality for sums in the geometry of numbers. In Mathlib, the files on the definition and basic properties of `eLpNorm` have Rémy Degenne and Sébastien Gouëzel as authors, the files on the triangle inequality, the essential supremum and the mean inequalities have Rémy Degenne, and the file on the comparison of exponents has Rémy Degenne and Eric Wieser.

### Reference

<?reference?>
