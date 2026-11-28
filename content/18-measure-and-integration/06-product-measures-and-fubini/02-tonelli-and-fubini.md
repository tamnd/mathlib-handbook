---
title: The theorems of Tonelli and Fubini
kind: theory
modules:
  - Mathlib.MeasureTheory.Integral.Prod
  - Mathlib.MeasureTheory.Integral.Pi
  - Mathlib.MeasureTheory.Integral.Marginal
explains:
  E3: [MeasureTheory.lintegral_prod, MeasureTheory.integral_prod, MeasureTheory.integrable_prod_iff, MeasureTheory.integral_integral_swap, MeasureTheory.integral_fintype_prod_eq_prod]
  E2: [MeasureTheory.lintegral_prod_symm, MeasureTheory.lintegral_lintegral_swap, MeasureTheory.lintegral_prod_mul, MeasureTheory.integrable_prod_iff', MeasureTheory.integral_prod_symm, MeasureTheory.integral_prod_mul, MeasureTheory.setIntegral_prod, MeasureTheory.Integrable.integral_prod_left, MeasureTheory.Integrable.prod_right_ae, MeasureTheory.Integrable.swap, MeasureTheory.integral_fintype_prod_eq_pow]
  E1: auto
families: []
requires: [V18.C02, V18.C03, V18.C04, V18.C05]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The theorems of Tonelli and Fubini

### Overview

Section 1 built $\mu \otimes \nu$ so that the measure of a set is the integral of the measures of its sections. This section extends the formula from sets to functions. Tonelli's theorem says that for $f \ge 0$ the double integral equals both iterated integrals, with no other hypothesis. Fubini's theorem gives the same for signed or vector valued $f$, under the hypothesis that $f$ is integrable for the product. Two counterexamples show what happens without integrability and without σ-finiteness. A worked example computes $\int_{\mathbb{R}} e^{-x^2} \, dx = \sqrt{\pi}$.

### Definitions

For $f : X \times Y \to E$ and $x \in X$, the section is $f_x(y) = f(x, y)$. The iterated integrals of $f$ are
$$\int_X \Big( \int_Y f(x, y) \, d\nu(y) \Big) d\mu(x) \quad\text{and}\quad \int_Y \Big( \int_X f(x, y) \, d\mu(x) \Big) d\nu(y).$$
The double integral is $\int_{X \times Y} f \, d(\mu \otimes \nu)$. In this section $\mu$ and $\nu$ are s-finite, so that Section 1 applies to both orders.

### Theorems and proofs

**Theorem 1 (Tonelli).** Let $f : X \times Y \to [0, \infty]$ be measurable. Then $x \mapsto \int f(x, y) \, d\nu(y)$ is measurable and
$$\int_{X \times Y} f \, d(\mu \otimes \nu) = \int_X \int_Y f(x, y) \, d\nu(y) \, d\mu(x) = \int_Y \int_X f(x, y) \, d\mu(x) \, d\nu(y).$$

*Proof.* For an indicator $f = \mathbf{1}_s$ with $s$ measurable, $\int \mathbf{1}_s(x, y) \, d\nu(y) = \nu(s_x)$. This is measurable by Theorem 1 of Section 1, and the first equality is the definition of $\mu \otimes \nu$. Both sides are additive and commute with multiplication by constants in $[0, \infty)$, so the equality holds for simple functions. For a general $f$, choose simple functions $0 \le \varphi_1 \le \varphi_2 \le \dots$ with $\sup_n \varphi_n = f$ (Chapter 4, Section 1). For each $x$, the sections $(\varphi_n)_x$ increase to $f_x$. By monotone convergence, $\int \varphi_n(x, y) \, d\nu(y)$ increases to $\int f(x, y) \, d\nu(y)$. A supremum of measurable functions is measurable. Monotone convergence once more on $X$, and once on $X \times Y$, gives
$$\int f \, d(\mu \otimes \nu) = \sup_n \int \varphi_n \, d(\mu \otimes \nu) = \sup_n \int_X \int_Y \varphi_n \, d\nu \, d\mu = \int_X \int_Y f \, d\nu \, d\mu.$$
The second equality follows in the same way from Corollary 4 of Section 1 in its s-finite form, which states the formula for indicators in the other order. $\square$

**Theorem 2 (Fubini).** Let $f : X \times Y \to \mathbb{R}$ be integrable for $\mu \otimes \nu$. Then:

1. for $\mu$-almost every $x$, the section $f_x$ is $\nu$-integrable;
2. the function $x \mapsto \int f(x, y) \, d\nu(y)$, defined almost everywhere, is $\mu$-integrable;
3. $\int f \, d(\mu \otimes \nu) = \int_X \int_Y f(x, y) \, d\nu(y) \, d\mu(x)$, and the same holds in the other order.

*Proof.* Apply Theorem 1 to $|f|$: $\int_X \int_Y |f(x, y)| \, d\nu \, d\mu = \int |f| \, d(\mu \otimes \nu) < \infty$. A function with finite integral is finite almost everywhere, so $\int |f_x| \, d\nu < \infty$ for $x$ outside a null set $N$. This is part 1.

Write $f = f^+ - f^-$ with $f^\pm \ge 0$, and let $F^\pm(x) = \int f^\pm(x, y) \, d\nu(y)$. By Theorem 1, $F^\pm$ is measurable and $\int F^\pm \, d\mu = \int f^\pm \, d(\mu \otimes \nu) \le \int |f| \, d(\mu \otimes \nu) < \infty$. So $F^+$ and $F^-$ are integrable. For $x \notin N$, both are finite and $\int f_x \, d\nu = F^+(x) - F^-(x)$. So the function of part 2 equals $F^+ - F^-$ almost everywhere, and it is integrable. Its integral is
$$\int F^+ \, d\mu - \int F^- \, d\mu = \int f^+ \, d(\mu \otimes \nu) - \int f^- \, d(\mu \otimes \nu) = \int f \, d(\mu \otimes \nu).$$
The other order is the same argument with the second equality of Theorem 1. $\square$

**Corollary 3 (Criterion of integrability).** A measurable $f$ on $X \times Y$ is integrable for $\mu \otimes \nu$ if and only if $f_x$ is $\nu$-integrable for almost every $x$ and $x \mapsto \int |f(x, y)| \, d\nu(y)$ is $\mu$-integrable.

*Proof.* By Theorem 1, $\int |f| \, d(\mu \otimes \nu) = \int_X \int_Y |f(x, y)| \, d\nu \, d\mu$. The left side is finite if and only if the right side is finite, and the right side is finite exactly when the two conditions hold. $\square$

In practice: bound one iterated integral of $|f|$, then exchange the order for $f$.

**Corollary 4 (Products of functions).** If $g \in L^1(\mu)$ and $h \in L^1(\nu)$, then $(x, y) \mapsto g(x) h(y)$ is integrable and $\int g(x) h(y) \, d(\mu \otimes \nu) = \int g \, d\mu \cdot \int h \, d\nu$.

*Proof.* Theorem 1 gives $\int |g(x)| |h(y)| \, d(\mu \otimes \nu) = \int |g| \, d\mu \int |h| \, d\nu < \infty$. Then Theorem 2 gives the formula, since the inner integral is $g(x) \int h \, d\nu$. $\square$

::: mathlib
`MeasureTheory.lintegral_prod` · `Mathlib.MeasureTheory.Measure.Prod`

Tonelli is `lintegral_prod`. It needs `[SFinite ν]` and only `AEMeasurable f (μ.prod ν)`. The other order is `lintegral_prod_symm`, and `lintegral_lintegral_swap` exchanges two iterated integrals. Both need `[SFinite μ]` too. Corollary 4 for nonnegative functions is `lintegral_prod_mul`. The proof in Mathlib does not use simple functions. It writes `μ.prod ν` as a `bind` and applies `lintegral_bind`.

<?decl MeasureTheory.lintegral_prod?>
<?decl MeasureTheory.lintegral_prod_symm?>
<?decl MeasureTheory.lintegral_lintegral_swap?>
:::

::: mathlib
`MeasureTheory.integral_prod` · `Mathlib.MeasureTheory.Integral.Prod`

Fubini is `integral_prod (f) (hf : Integrable f (μ.prod ν))`, for `f` with values in a Banach space `E`. The other order is `integral_prod_symm`, and `integral_integral_swap` is the exchange of iterated integrals. Parts 1 and 2 are `Integrable.prod_right_ae` and `Integrable.integral_prod_left`. Corollary 3 is `integrable_prod_iff`. For a vector valued $f$ the splitting $f^+ - f^-$ is not available, so Mathlib uses the induction principle `Integrable.induction` of Chapter 7, Section 2: indicators, sums, limits in $L^1$, and functions equal almost everywhere.

<?decl MeasureTheory.integral_prod?>
<?decl MeasureTheory.integrable_prod_iff?>
<?decl MeasureTheory.integral_integral_swap?>
<?decl MeasureTheory.Integrable.prod_right_ae?>
:::

### Examples

**Example (The Gaussian integral).** Let $I = \int_0^\infty e^{-x^2} \, dx$. By Corollary 4 in its nonnegative form, $I^2 = \int_0^\infty \int_0^\infty e^{-x^2 - y^2} \, dy \, dx$. Fix $x > 0$ and put $y = xs$. The scaling law of Chapter 3, Section 1 gives
$$\int_0^\infty e^{-x^2 - y^2} \, dy = \int_0^\infty x \, e^{-x^2(1 + s^2)} \, ds.$$
The integrand on the right is nonnegative and measurable in $(x, s)$, so Theorem 1 exchanges the order:
$$I^2 = \int_0^\infty \int_0^\infty x \, e^{-x^2(1 + s^2)} \, dx \, ds.$$
The inner integral is $\frac{1}{2(1 + s^2)}$, because $-\frac{e^{-x^2(1 + s^2)}}{2(1 + s^2)}$ is a primitive that tends to $0$ at $\infty$. The outer integral is then $\frac{1}{2} \int_0^\infty \frac{ds}{1 + s^2} = \frac{1}{2} \cdot \frac{\pi}{2}$. Chapter 8, Section 1 justifies both improper integrals with the fundamental theorem of calculus. So $I^2 = \pi/4$, $I = \sqrt{\pi}/2$, and by symmetry $\int_{\mathbb{R}} e^{-x^2} \, dx = \sqrt{\pi}$.

**Counterexample (Integrability is necessary).** Let $\mu = \nu$ be counting measure on $\mathbb{N}$, and let $a(m, m) = 1$, $a(m, m + 1) = -1$, and $a(m, n) = 0$ otherwise. Each row has the sum $1 - 1 = 0$, so $\sum_m \sum_n a(m, n) = 0$. Column $0$ has the sum $a(0, 0) = 1$. Column $n \ge 1$ has the sum $a(n, n) + a(n - 1, n) = 0$. So $\sum_n \sum_m a(m, n) = 1$. The two iterated sums differ, and Theorem 2 does not apply because $\sum_{m, n} |a(m, n)| = \infty$. The classical continuous form is $f(x, y) = \frac{x^2 - y^2}{(x^2 + y^2)^2}$ on $(0, 1)^2$, with iterated integrals $\pi/4$ and $-\pi/4$.

**Counterexample (σ-finiteness is necessary).** Let $\lambda$ be Lebesgue measure on $[0, 1]$, $c$ counting measure on $[0, 1]$, and $\Delta$ the diagonal. Then
$$\int \Big( \int \mathbf{1}_\Delta(x, y) \, dc(y) \Big) d\lambda(x) = \int 1 \, d\lambda = 1, \qquad \int \Big( \int \mathbf{1}_\Delta(x, y) \, d\lambda(x) \Big) dc(y) = \int 0 \, dc = 0.$$
The measure $c$ is not s-finite: a finite measure has only countably many points of positive mass, so a countable sum of them has too, while $c$ gives mass $1$ to uncountably many points. In Mathlib, `c.prod λ` is defined and gives $\Delta$ the measure $0$. The other product `λ.prod c` is the junk value $0$, so `lintegral_prod` cannot apply to it.

### The library around it

::: mathlib
`MeasureTheory.integral_fintype_prod_eq_prod` · `Mathlib.MeasureTheory.Integral.Pi`

For finitely many σ-finite measures, `integral_fintype_prod_eq_prod` states $\int \prod_i f_i(x_i) \, d\big(\bigotimes_i \mu_i\big) = \prod_i \int f_i \, d\mu_i$ for functions with values in `ℝ` or `ℂ`. The form `integral_fintype_prod_eq_pow` has one function and one measure. With the Gaussian example, it gives $\int_{\mathbb{R}^n} e^{-|x|^2} \, dx = \pi^{n/2}$. For two factors, `integral_prod_mul` is Corollary 4.

<?decl MeasureTheory.integral_fintype_prod_eq_prod?>
<?decl MeasureTheory.integral_fintype_prod_eq_pow?>
<?decl MeasureTheory.integral_prod_mul?>
:::

::: mathlib
`integral_gaussian` · `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral`

Mathlib states $\int e^{-b x^2} \, dx = \sqrt{\pi / b}$ as `integral_gaussian`. Its proof also squares the integral with `integral_prod_mul`, but then uses polar coordinates, the change of variables of Chapter 8, Section 2, in place of the substitution $y = xs$.

<?decl integral_gaussian?>
:::

The lemma `setIntegral_prod` is Fubini on a rectangle $s \times t$, and `Integrable.swap` moves integrability through the swap map.

The module `Mathlib.MeasureTheory.Integral.Marginal` integrates out some of the variables of a function on a finite product. For $f : \prod_i X_i \to [0, \infty]$ and a finite set $s$ of indices, the marginal `MeasureTheory.lmarginal μ s f`, written `∫⋯∫⁻_s, f ∂μ`, is again a function on $\prod_i X_i$: at a point $x$ it integrates $f$ over the coordinates in $s$ and keeps the coordinates of $x$ outside $s$. So $\int \cdots \int_\emptyset f = f$ (`MeasureTheory.lmarginal_empty`), and for all indices it is the integral of Tonelli for the product measure, `MeasureTheory.lintegral_eq_lmarginal_univ`. The rule `MeasureTheory.lmarginal_union` integrates over $s \cup t$ in two steps when $s$ and $t$ are disjoint, and `MeasureTheory.lmarginal_insert` adds one variable: $(\int \cdots \int_{s \cup \{i\}} f)(x) = \int (\int \cdots \int_s f)(x[i \mapsto y]) \, d\mu_i(y)$ for $i \notin s$. Both rules are the theorem of Tonelli for the product of the coordinates in $s$ and $t$. The lemmas `MeasureTheory.lmarginal_mono`, `MeasureTheory.lmarginal_le_of_subset` and `MeasureTheory.lintegral_le_of_lmarginal_le` support proofs by induction on the number of variables, such as the proof of the Gagliardo-Nirenberg-Sobolev inequality in Mathlib.

Common errors of a learner:

- Exchanging the order of a signed integral without a bound on $\int \int |f|$. The first counterexample shows that the two orders can differ.
- Using `integral_prod` with only `Integrable (fun y => f (x, y))` for each $x$. The hypothesis is integrability on the product.
- Forgetting that the inner integral in Fubini is only defined almost everywhere. Mathlib defines it everywhere, with the value $0$ where $f_x$ is not integrable.

### Exercises

1. (A) Compute $\int_{[0, 1]^2} x y^2 \, d\lambda_2$ with Corollary 4.
2. (A) Let $a_{m, n} \ge 0$. Show that $\sum_m \sum_n a_{m, n} = \sum_n \sum_m a_{m, n}$ with Theorem 1 for counting measure.
3. (A) Show that $\int_{\mathbb{R}^2} e^{-x^2 - y^2} \, d\lambda_2 = \pi$.
4. (B) Let $f \ge 0$ be measurable on $X$. Show that $\int f \, d\mu = \int_0^\infty \mu(\{f > t\}) \, dt$. Hint: write $f(x) = \int_0^\infty \mathbf{1}_{\{t < f(x)\}} \, dt$ and apply Theorem 1.
5. (B) Let $f, g \in L^1(\mathbb{R})$. Show that $h(x) = \int f(x - y) g(y) \, dy$ is defined for almost every $x$ and that $\int |h| \le \int |f| \int |g|$. Hint: Corollary 3 for $(x, y) \mapsto f(x - y) g(y)$ and the translation invariance of $\lambda$.
6. (B) Compute the two iterated integrals of $\frac{x^2 - y^2}{(x^2 + y^2)^2}$ on $(0, 1)^2$. Hint: $\frac{\partial}{\partial y} \frac{y}{x^2 + y^2} = \frac{x^2 - y^2}{(x^2 + y^2)^2}$.
7. (C) Show that $\int_0^\infty \frac{\sin x}{x} e^{-tx} \, dx = \frac{\pi}{2} - \arctan t$ for $t > 0$. Hint: write $\frac{1}{x} = \int_0^\infty e^{-xu} \, du$, check Corollary 3 for $(x, u) \mapsto \sin x \, e^{-(t + u)x}$ on $(0, \infty)^2$, and exchange the order.

### Notes and history

Fubini proved the theorem for Lebesgue integrable functions in 1907, and Tonelli the form for nonnegative functions in 1909. The Mathlib file on products has Floris van Doorn as author, and the file on finite products of integrals has Xavier Roblot.

### Reference

<?reference?>
