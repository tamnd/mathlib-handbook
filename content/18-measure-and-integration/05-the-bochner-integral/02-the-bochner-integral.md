---
title: The Bochner integral
kind: theory
modules:
  - Mathlib.MeasureTheory.Integral.Bochner.Basic
  - Mathlib.MeasureTheory.Integral.Bochner.L1
  - Mathlib.MeasureTheory.Integral.Bochner.Set
explains:
  E3: [MeasureTheory.integral, MeasureTheory.SimpleFunc.integral, MeasureTheory.L1.integral, MeasureTheory.integral_eq_lintegral_of_nonneg_ae, MeasureTheory.norm_integral_le_integral_norm]
  E2: [MeasureTheory.L1.integralCLM, MeasureTheory.SimpleFunc.integral_eq_sum, MeasureTheory.integral_undef, MeasureTheory.integral_add, MeasureTheory.integral_sub, MeasureTheory.integral_smul, MeasureTheory.integral_congr_ae, MeasureTheory.integral_mono, MeasureTheory.integral_const, MeasureTheory.integral_eq_integral_pos_part_sub_integral_neg_part, MeasureTheory.setIntegral_union, MeasureTheory.integral_indicator]
  E1: auto
families: []
requires: [V13, V15, V18.C02, V18.C03, V18.C04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The Bochner integral

### Overview

This section defines the integral $\int f \, d\mu \in E$ of an integrable function $f : X \to E$, where $E$ is a Banach space. The construction has three steps. A simple integrable function has the integral $\sum_v \mu(\{f = v\}) \, v$. Simple functions are dense among the integrable functions for the distance $\int \|f - g\| \, d\mu$. The integral is uniformly continuous for this distance, and completeness of $E$ extends it. It uses the integrable functions of Section 1 of this chapter.

### Definitions

Throughout, $E$ is a Banach space as in Section 1.

**Definition (Integral of a simple function).** Let $\varphi : X \to E$ be simple and integrable. Then $\mu(\{\varphi = v\}) < \infty$ for every $v \ne 0$, since $\|v\| \mu(\{\varphi = v\}) \le \int \|\varphi\| \, d\mu$. Put
$$\int \varphi \, d\mu = \sum_{v \ne 0} \mu(\{\varphi = v\}) \, v,$$
a finite sum in $E$.

The proof of the rules for simple functions in Chapter 4, Section 1 works here word for word: on the common refinement $\{\varphi = v\} \cap \{\psi = w\}$, the integral is additive and commutes with scalars. The triangle inequality gives $\|\int \varphi \, d\mu\| \le \sum_v \mu(\{\varphi = v\}) \|v\| = \int \|\varphi\| \, d\mu$.

::: mathlib
`MeasureTheory.SimpleFunc.integral` · `Mathlib.MeasureTheory.Integral.Bochner.L1`

`SimpleFunc.integral μ f` is `∑ x ∈ f.range, μ.real (f ⁻¹' {x}) • x`, where `μ.real s` is `(μ s).toReal`. The value $0$ absorbs the term with infinite measure, because `(∞).toReal = 0`. For integrable simple `f`, `SimpleFunc.integral_eq_sum` equates the general integral with this sum.

<?decl MeasureTheory.SimpleFunc.integral?>
<?decl MeasureTheory.SimpleFunc.integral_eq_sum?>
:::

**Lemma (Density of simple functions).** For integrable $f$ there are simple integrable $\psi_n$ with $\int \|f - \psi_n\| \, d\mu \to 0$.

*Proof.* The integral of $\|f - \psi_n\|$ does not change if $f$ changes on a null set, so let $f$ be strongly measurable, with simple $\varphi_n \to f$ pointwise. Put $\psi_n = \varphi_n$ where $\|\varphi_n\| \le 2 \|f\|$ and $\psi_n = 0$ elsewhere. The set where $\|\varphi_n\| \le 2\|f\|$ is measurable, so $\psi_n$ is simple, and $\|\psi_n\| \le 2 \|f\|$, so $\psi_n$ is integrable. If $f(x) \ne 0$, then $\|\varphi_n(x)\| \to \|f(x)\| < 2\|f(x)\|$, so $\psi_n(x) = \varphi_n(x)$ for large $n$. If $f(x) = 0$, then $\psi_n(x)$ is $\varphi_n(x)$ or $0$, and both tend to $0$. So $\psi_n \to f$ pointwise. The functions $\|f - \psi_n\|$ tend to $0$ and are dominated by $3\|f\|$, which has finite integral. The dominated convergence theorem of Chapter 4, Section 2 gives $\int \|f - \psi_n\| \, d\mu \to 0$. $\square$

**Definition (Bochner integral).** Let $f$ be integrable, and let $\psi_n$ be simple integrable with $\int \|f - \psi_n\| \, d\mu \to 0$. Then
$$\int f \, d\mu = \lim_n \int \psi_n \, d\mu.$$
If $f$ is not integrable, put $\int f \, d\mu = 0$.

*The limit exists and does not depend on $\psi_n$.* By linearity and the bound for simple functions,
$$\Big\| \int \psi_n \, d\mu - \int \psi_m \, d\mu \Big\| \le \int \|\psi_n - \psi_m\| \, d\mu \le \int \|\psi_n - f\| \, d\mu + \int \|f - \psi_m\| \, d\mu.$$
The right side tends to $0$, so the sequence is Cauchy, and it converges because $E$ is complete. For a second sequence $\psi_n'$, the sequence $\psi_1, \psi_1', \psi_2, \psi_2', \dots$ also approximates $f$. Its integrals converge, so the two limits agree. For a simple $f$, the constant sequence shows that the new integral extends the old one. $\square$

::: mathlib
`MeasureTheory.integral` · `Mathlib.MeasureTheory.Integral.Bochner.Basic`

`integral μ f`, written `∫ x, f x ∂μ`, is `if CompleteSpace G then (if hf : Integrable f μ then L1.integral (hf.toL1 f) else 0) else 0`. So it is $0$ when `f` is not integrable, by `integral_undef`, and also when `G` is not complete. Lemmas such as `integral_smul` need no integrability.

<?decl MeasureTheory.integral?>
<?decl MeasureTheory.integral_undef?>
:::

::: mathlib
`MeasureTheory.L1.integral` · `Mathlib.MeasureTheory.Integral.Bochner.L1`

Mathlib runs the construction on the space `α →₁[μ] E` of classes of integrable functions (Chapter 7). The integral on the dense subspace of simple classes is continuous and linear, and `ContinuousLinearMap.extend` extends it. The result is `L1.integralCLM`, a continuous linear map `(α →₁[μ] E) →L[ℝ] E`, and `L1.integral` is its function.

<?decl MeasureTheory.L1.integral?>
<?decl MeasureTheory.L1.integralCLM?>
:::

### Theorems and proofs

**Theorem (Linearity and the norm bound).** For integrable $f, g$ and $c \in \mathbb{R}$, $\int (f + g) \, d\mu = \int f \, d\mu + \int g \, d\mu$ and $\int cf \, d\mu = c \int f \, d\mu$. For all $f$, $\|\int f \, d\mu\| \le \int \|f\| \, d\mu$. If $f = g$ almost everywhere, then $\int f \, d\mu = \int g \, d\mu$.

*Proof.* Take simple $\psi_n \to f$ and $\chi_n \to g$ in the sense of the lemma. Then $\int \|(f + g) - (\psi_n + \chi_n)\| \, d\mu \le \int \|f - \psi_n\| \, d\mu + \int \|g - \chi_n\| \, d\mu \to 0$, so $\psi_n + \chi_n$ approximates $f + g$. Pass to the limit in the additivity for simple functions. The same works for $cf$.

For the bound, let $f$ be integrable; otherwise the left side is $0$. The bound holds for $\psi_n$. The inequality $|\|f\| - \|\psi_n\|| \le \|f - \psi_n\|$ gives $\int \|\psi_n\| \, d\mu \to \int \|f\| \, d\mu$, and the norm is continuous, so the bound passes to the limit. If $f = g$ almost everywhere, the same $\psi_n$ approximate both. $\square$

::: mathlib
`MeasureTheory.norm_integral_le_integral_norm` · `Mathlib.MeasureTheory.Integral.Bochner.Basic`

`‖∫ a, f a ∂μ‖ ≤ ∫ a, ‖f a‖ ∂μ` for every `f`, with no hypothesis: for a non-integrable `f` the left side is $0$. Linearity is `integral_add` and `integral_sub`, which need both functions integrable, and `integral_smul`, which needs nothing. Congruence is `integral_congr_ae`.

<?decl MeasureTheory.norm_integral_le_integral_norm?>
<?decl MeasureTheory.integral_add?>
<?decl MeasureTheory.integral_sub?>
<?decl MeasureTheory.integral_smul?>
<?decl MeasureTheory.integral_congr_ae?>
:::

**Theorem (Real functions).** Let $f : X \to \mathbb{R}$ be integrable with $f \ge 0$ almost everywhere. Then $\int f \, d\mu$ is the real number $\int f \, d\mu$ of Chapter 4. For every integrable real $f$, $\int f \, d\mu = \int f^+ \, d\mu - \int f^- \, d\mu$, with $f^+ = \max(f, 0)$ and $f^- = \max(-f, 0)$.

*Proof.* Change $f$ on a null set so that $f \ge 0$ everywhere. Take $\psi_n$ from the lemma and replace it by $\psi_n^+$. Since $f \ge 0$, $|f - \psi_n^+| \le |f - \psi_n|$, so $\psi_n^+$ also approximates $f$. For a simple $\varphi \ge 0$ with finite values, the two integrals are the same sum $\sum_v v \, \mu(\{\varphi = v\})$. Let $I$ be the integral of Chapter 4. Additivity there gives $I(f) \le I(\psi_n^+) + I(|f - \psi_n^+|)$ and $I(\psi_n^+) \le I(f) + I(|f - \psi_n^+|)$. All terms are finite, so $|I(f) - I(\psi_n^+)| \le I(|f - \psi_n^+|) \to 0$. Hence $\int \psi_n^+ \, d\mu = I(\psi_n^+) \to I(f)$. The formula with $f^+$ and $f^-$ follows from $f = f^+ - f^-$ and linearity. $\square$

**Corollary (Monotonicity).** If $f, g : X \to \mathbb{R}$ are integrable and $f \le g$, then $\int f \, d\mu \le \int g \, d\mu$.

*Proof.* $\int g \, d\mu - \int f \, d\mu = \int (g - f) \, d\mu \ge 0$ by the theorem, since $g - f \ge 0$. $\square$

::: mathlib
`MeasureTheory.integral_eq_lintegral_of_nonneg_ae` · `Mathlib.MeasureTheory.Integral.Bochner.Basic`

`0 ≤ᵐ[μ] f → AEStronglyMeasurable f μ → ∫ a, f a ∂μ = (∫⁻ a, ENNReal.ofReal (f a) ∂μ).toReal`. Integrability is not a hypothesis: if `∫⁻` is $\infty$, both sides are $0$. The decomposition is `integral_eq_integral_pos_part_sub_integral_neg_part`. Monotonicity is `integral_mono`, with both functions integrable and `f ≤ g` at every point. The form `integral_mono_ae` takes `f ≤ᵐ[μ] g`.

<?decl MeasureTheory.integral_eq_lintegral_of_nonneg_ae?>
<?decl MeasureTheory.integral_eq_integral_pos_part_sub_integral_neg_part?>
<?decl MeasureTheory.integral_mono?>
:::

**Proposition (Integrals over sets).** Write $\int_A f \, d\mu$ for $\int f \, d(\mu|_A)$. For measurable $A$, $\int_A f \, d\mu = \int f \mathbf{1}_A \, d\mu$. For disjoint measurable $A, B$ and $f$ integrable on both, $\int_{A \cup B} f \, d\mu = \int_A f \, d\mu + \int_B f \, d\mu$.

*Proof.* For simple $f$ both claims are identities of finite sums, since $\mu|_A(\{f = v\}) = \mu(\{f \mathbf{1}_A = v\})$ for $v \ne 0$ and $\mu|_{A \cup B} = \mu|_A + \mu|_B$. The approximating sequences of the lemma pass both identities to the limit. $\square$

::: mathlib
`MeasureTheory.setIntegral_union` · `Mathlib.MeasureTheory.Integral.Bochner.Set`

`Disjoint s t → MeasurableSet t → IntegrableOn f s μ → IntegrableOn f t μ → ∫ x in s ∪ t, f x ∂μ = ∫ x in s, f x ∂μ + ∫ x in t, f x ∂μ`. Only `t` must be measurable. `integral_indicator` needs `MeasurableSet s`. Constants give `integral_const`: `∫ x, c ∂μ = μ.real univ • c`.

<?decl MeasureTheory.setIntegral_union?>
<?decl MeasureTheory.integral_indicator?>
<?decl MeasureTheory.integral_const?>
:::

### Examples

**Example (A complex step function).** Let $f = \mathbf{1}_{[0, 1]} + i \, \mathbf{1}_{[1, 3]}$ on $\mathbb{R}$, with values in $\mathbb{C}$. It is simple with the values $1$, $1 + i$ and $i$ on $[0, 1)$, $\{1\}$ and $(1, 3]$. The definition gives $\int f \, d\lambda = 1 \cdot 1 + 0 \cdot (1 + i) + 2 \cdot i = 1 + 2i$.

**Example (A real function).** Let $f(x) = (-1)^n 2^{-n}$ on $[n, n + 1)$ for $n \ge 0$, and $0$ for $x < 0$. Then $\int |f| \, d\lambda = \sum_n 2^{-n} = 2$, so $f$ is integrable. The positive part is $2^{-n}$ on the intervals with $n$ even, so $\int f^+ \, d\lambda = \frac{4}{3}$, and $\int f^- \, d\lambda = \frac{2}{3}$. So $\int f \, d\lambda = \frac{2}{3}$.

**Counterexample (Monotonicity needs integrability).** Let $f = \mathbf{1}_{[0, 1]}$ and $g = 1$ on $\mathbb{R}$. Then $f \le g$, but $g$ is not integrable, so $\int g \, d\lambda = 0 < 1 = \int f \, d\lambda$. So `integral_mono` asks for both integrability proofs.

**Counterexample (An improper integral).** Let $f(x) = (-1)^n / (n + 1)$ on $[n, n + 1)$ for $n \ge 0$. The limit $\lim_{N \to \infty} \int_{[0, N)} f \, d\lambda = \sum_n (-1)^n / (n + 1) = \log 2$ exists. But $\int |f| \, d\lambda$ is the harmonic series, so $f$ is not integrable and $\int f \, d\lambda = 0$. The Bochner integral sees only absolutely convergent integrals.

### The library around it

The file `Mathlib.MeasureTheory.Integral.Bochner.L1` holds the construction, through `weightedSMul μ s`, the map `x ↦ μ.real s • x`.

Common errors of a learner:

- Using `integral_add` or `integral_mono` without the integrability of both functions.
- Reading `∫ x, f x ∂μ = 0` as a statement about `f`: it may be the junk value.
- Confusing `∫` with `∫⁻`. For real `f ≥ 0` the link is `integral_eq_lintegral_of_nonneg_ae`, with a `toReal`.

### Exercises

1. (A) Compute $\int f \, d\lambda$ for $f = 2 \cdot \mathbf{1}_{[0, 2]} - 3 \cdot \mathbf{1}_{[1, 4]}$.
2. (A) Show that $\int_A c \, d\mu = \mu(A) c$ for $c \in E$ and $\mu(A) < \infty$.
3. (A) Let $T : E \to F$ be a continuous linear map. Show that $\int T f \, d\mu = T \int f \, d\mu$ for simple integrable $f$.
4. (B) Extend Exercise 3 to all integrable $f$. Hint: $\|T v\| \le \|T\| \|v\|$ and the approximating sequences.
5. (B) Let $f : X \to \mathbb{R}$ be integrable with $\int_A f \, d\mu \ge 0$ for every measurable $A$. Show that $f \ge 0$ almost everywhere. Hint: $A = \{f < 0\}$.
6. (B) Let $f : X \to \mathbb{C}$ be integrable. Show that $\int f \, d\mu = \int \operatorname{Re} f \, d\mu + i \int \operatorname{Im} f \, d\mu$. Hint: Exercise 4 with $T = \operatorname{Re}$ and $T = \operatorname{Im}$.
7. (C) Let $f$ be integrable and real, with $|\int f \, d\mu| = \int |f| \, d\mu$. Show that $f \ge 0$ almost everywhere or $f \le 0$ almost everywhere. Hint: compare $\int f^+$ and $\int f^-$.

### Notes and history

Bochner introduced the integral in 1933, by the limit of integrals of simple functions in the norm of $L^1$, as in this section. In Mathlib, the files `Bochner.Basic` and `Bochner.L1` have Zhouhang Zhou, Yury Kudryashov, Sébastien Gouëzel and Rémy Degenne as authors, and `Bochner.Set` has Zhouhang Zhou and Yury Kudryashov.

### Reference

<?reference?>
