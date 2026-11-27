---
title: Integrable functions
kind: theory
modules:
  - Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
  - Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
  - Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
  - Mathlib.MeasureTheory.Function.L1Space.Integrable
  - Mathlib.MeasureTheory.Integral.IntegrableOn
explains:
  E3: [MeasureTheory.StronglyMeasurable, MeasureTheory.AEStronglyMeasurable, MeasureTheory.HasFiniteIntegral, MeasureTheory.Integrable, stronglyMeasurable_iff_measurable_separable]
  E2: [MeasureTheory.StronglyMeasurable.measurable, Measurable.stronglyMeasurable, Continuous.stronglyMeasurable, MeasureTheory.hasFiniteIntegral_iff_norm, MeasureTheory.Integrable.mono, MeasureTheory.Integrable.add, MeasureTheory.Integrable.smul, MeasureTheory.integrable_const, MeasureTheory.IntegrableOn, MeasureTheory.IntegrableOn.union]
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

## Integrable functions

### Overview

The integral of Chapter 4 has values in $[0, \infty]$. Most integrals in analysis have real, complex or vector values. This section fixes the target: a Banach space $E$, that is a complete normed space. It defines the functions that the Bochner integral of Section 2 accepts. Such a function must be a limit of simple functions, the condition of strong measurability, and the integral of its norm must be finite. The section proves that these functions form a vector space and gives the standard tests for integrability.

### Definitions

The following is the little that the chapter needs about normed spaces. Volume 16 treats them in full.

**Definition (Normed space).** A *normed space* is a real vector space $E$ with a map $\|\cdot\| : E \to [0, \infty)$ such that $\|v\| = 0$ only for $v = 0$, $\|c v\| = |c| \, \|v\|$, and $\|v + w\| \le \|v\| + \|w\|$. The distance $d(v, w) = \|v - w\|$ makes $E$ a metric space. A *Banach space* is a normed space that is complete for this metric: every Cauchy sequence converges.

The examples of this volume are $\mathbb{R}$ with $|\cdot|$, $\mathbb{C}$ with the modulus, and $\mathbb{R}^n$ with any norm. Completeness is the property of $\mathbb{R}$ from Volume 15, and of metric spaces from Volume 13. It matters for one reason: in a complete space, a series $\sum v_k$ with $\sum \|v_k\| < \infty$ converges. The partial sums are Cauchy, because $\|\sum_{k=m}^n v_k\| \le \sum_{k=m}^n \|v_k\|$.

::: mathlib
`NormedAddCommGroup` · `Mathlib.Analysis.Normed.Group.Defs`

Mathlib splits the definition. `NormedAddCommGroup E` gives an additive group with a norm whose distance is `dist x y = ‖x - y‖`. `NormedSpace ℝ E` adds the scalar multiplication with `‖c • x‖ ≤ ‖c‖ * ‖x‖`. Completeness is the separate class `CompleteSpace E`. A Banach space is `[NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]`.

<?decl NormedAddCommGroup?>
<?decl NormedSpace?>
<?decl CompleteSpace?>
:::

**Definition (Strongly measurable).** Let $E$ be a topological space. A function $f : X \to E$ is *strongly measurable* if it is the pointwise limit of a sequence of simple functions $X \to E$. It is *almost everywhere strongly measurable* for $\mu$ if it agrees $\mu$-almost everywhere with a strongly measurable function.

**Definition (Integrable function).** Let $E$ be a normed space. A function $f : X \to E$ is *integrable* for $\mu$ if it is almost everywhere strongly measurable and $\int \|f\| \, d\mu < \infty$, with the integral of Chapter 4.

::: mathlib
`MeasureTheory.StronglyMeasurable` · `Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic`

`StronglyMeasurable f` is `∃ fs : ℕ → α →ₛ β, ∀ x, Tendsto (fun n ↦ fs n x) atTop (𝓝 (f x))`, with the simple functions of Chapter 4. The target needs only a topology, not a σ-algebra. `StronglyMeasurable.measurable` recovers measurability when `β` is pseudo-metrizable with its Borel σ-algebra.

<?decl MeasureTheory.StronglyMeasurable?>
<?decl MeasureTheory.StronglyMeasurable.measurable?>
:::

::: mathlib
`MeasureTheory.AEStronglyMeasurable` · `Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable`

`AEStronglyMeasurable f μ` is `∃ g, StronglyMeasurable g ∧ f =ᵐ[μ] g`. This is the measurability hypothesis of almost every lemma on the Bochner integral.

<?decl MeasureTheory.AEStronglyMeasurable?>
:::

::: mathlib
`MeasureTheory.HasFiniteIntegral` · `Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral`

`HasFiniteIntegral f μ` is `∫⁻ a, ‖f a‖ₑ ∂μ < ∞`, where `‖x‖ₑ` is the norm as an element of `ℝ≥0∞`. The lemma `hasFiniteIntegral_iff_norm` restates it with `ENNReal.ofReal ‖f a‖`.

<?decl MeasureTheory.HasFiniteIntegral?>
<?decl MeasureTheory.hasFiniteIntegral_iff_norm?>
:::

::: mathlib
`MeasureTheory.Integrable` · `Mathlib.MeasureTheory.Function.L1Space.Integrable`

`Integrable f μ` is `AEStronglyMeasurable f μ ∧ HasFiniteIntegral f μ`. The measure is an `autoParam`: `Integrable f` alone means `Integrable f volume`. The target can be any type with a continuous extended norm, the class `ContinuousENorm`.

<?decl MeasureTheory.Integrable?>
:::

### Theorems and proofs

**Theorem (Measurable and separable).** Let $E$ be a metric space with its Borel $\sigma$-algebra. A function $f : X \to E$ is strongly measurable if and only if it is measurable and its range is separable.

*Proof.* Let $f = \lim_n \varphi_n$ with simple $\varphi_n$. Each $\varphi_n$ is measurable. A pointwise limit of measurable functions into a metric space is measurable: for a closed set $F$, put $U_k = \{y : d(y, F) < 1/k\}$. Then
$$f^{-1}(F) = \bigcap_k \bigcup_m \bigcap_{n \ge m} \varphi_n^{-1}(U_k),$$
a measurable set. Closed sets generate the Borel sets, so $f$ is measurable. The range of $f$ lies in the closure of the countable set $\bigcup_n \varphi_n(X)$, so it is separable.

Conversely, let $f$ be measurable, and let $e_1, e_2, \dots$ be dense in the range of $f$. For $x \in X$ let $\varphi_n(x) = e_k$, where $k \le n$ is the least index with $d(f(x), e_k) = \min_{j \le n} d(f(x), e_j)$. The map $x \mapsto d(f(x), e_j)$ is measurable, so each fiber of $\varphi_n$ is measurable, and $\varphi_n$ is simple. For $\varepsilon > 0$ there is $j$ with $d(f(x), e_j) < \varepsilon$, and for $n \ge j$, $d(\varphi_n(x), f(x)) \le d(f(x), e_j) < \varepsilon$. So $\varphi_n(x) \to f(x)$. $\square$

In particular, on $\mathbb{R}$, $\mathbb{C}$ and $\mathbb{R}^n$ every measurable function is strongly measurable, and every continuous function on a metric space with its Borel sets is too.

::: mathlib
`stronglyMeasurable_iff_measurable_separable` · `Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic`

`StronglyMeasurable f ↔ Measurable f ∧ IsSeparable (range f)`, for a pseudo-metrizable target with `[BorelSpace β]`. The special cases are `Measurable.stronglyMeasurable`, for a second countable target, and `Continuous.stronglyMeasurable`, which needs `OpensMeasurableSpace α`, a pseudo-metrizable `β`, and second countability of `α` or `β`.

<?decl stronglyMeasurable_iff_measurable_separable?>
<?decl Measurable.stronglyMeasurable?>
<?decl Continuous.stronglyMeasurable?>
:::

**Proposition (Domination).** Let $g : X \to F$ be integrable and $f : X \to E$ almost everywhere strongly measurable with $\|f\| \le \|g\|$ almost everywhere. Then $f$ is integrable.

*Proof.* Monotonicity of the integral and its invariance under null sets (Chapter 4, Section 1) give $\int \|f\| \, d\mu \le \int \|g\| \, d\mu < \infty$. $\square$

**Theorem (The integrable functions form a vector space).** If $f, g : X \to E$ are integrable and $c \in \mathbb{R}$, then $f + g$ and $c f$ are integrable.

*Proof.* Let $f = f_0$ and $g = g_0$ almost everywhere, with $f_0 = \lim \varphi_n$ and $g_0 = \lim \psi_n$ for simple $\varphi_n$, $\psi_n$. The functions $\varphi_n + \psi_n$ are simple, since they are constant on the sets $\varphi_n^{-1}(\{v\}) \cap \psi_n^{-1}(\{w\})$. They converge to $f_0 + g_0$ by the continuity of addition, and $f + g = f_0 + g_0$ outside the union of two null sets. So $f + g$ is almost everywhere strongly measurable. The triangle inequality and the additivity of Chapter 4, Section 2 give
$$\int \|f + g\| \, d\mu \le \int (\|f\| + \|g\|) \, d\mu = \int \|f\| \, d\mu + \int \|g\| \, d\mu < \infty.$$
For $cf$ the simple functions $c \varphi_n$ converge to $c f_0$, and $\int \|c f\| \, d\mu = |c| \int \|f\| \, d\mu$. $\square$

::: mathlib
`MeasureTheory.Integrable.mono` · `Mathlib.MeasureTheory.Function.L1Space.Integrable`

`Integrable g μ → AEStronglyMeasurable f μ → (∀ᵐ a ∂μ, ‖f a‖ ≤ ‖g a‖) → Integrable f μ`. The functions `f` and `g` may have different targets. The vector space rules are `Integrable.add`, `Integrable.neg`, `Integrable.sub` and `Integrable.smul`.

<?decl MeasureTheory.Integrable.mono?>
<?decl MeasureTheory.Integrable.add?>
<?decl MeasureTheory.Integrable.smul?>
:::

**Proposition (Bounded functions on finite measures).** If $\mu(X) < \infty$ and $f$ is almost everywhere strongly measurable with $\|f\| \le C$ almost everywhere, then $f$ is integrable. In particular every constant is integrable.

*Proof.* The constant $C$ has $\int C \, d\mu = C \mu(X) < \infty$ by Chapter 4, Section 1. Apply domination with $g = C$. $\square$

::: mathlib
`MeasureTheory.integrable_const` · `Mathlib.MeasureTheory.Function.L1Space.Integrable`

`Integrable (fun _ ↦ c) μ` under `[IsFiniteMeasure μ]`. The instance argument is the hypothesis $\mu(X) < \infty$.

<?decl MeasureTheory.integrable_const?>
:::

**Definition (Integrable on a set).** A function is *integrable on* a measurable set $A$ if it is integrable for the restriction $\mu|_A$.

::: mathlib
`MeasureTheory.IntegrableOn` · `Mathlib.MeasureTheory.Integral.IntegrableOn`

`IntegrableOn f s μ` is `Integrable f (μ.restrict s)`. The set need not be measurable. `IntegrableOn.union` combines two sets, `IntegrableOn.mono_set` passes to a subset, and `integrableOn_const` needs `μ s ≠ ⊤`, proved by an automatic tactic when it can.

<?decl MeasureTheory.IntegrableOn?>
<?decl MeasureTheory.IntegrableOn.union?>
:::

### Examples

**Example (Powers on the unit interval).** Let $f(x) = x^s$ on $(0, 1]$ with $s \in \mathbb{R}$. Cut $(0, 1]$ into $I_k = (2^{-k-1}, 2^{-k}]$, of length $2^{-k-1}$. On $I_k$ the value $x^s$ lies between $2^{-ks}$ and $2^{-(k+1)s}$, and these differ by the factor $2^{|s|}$. So
$$2^{-|s|-1} \, 2^{-k(s+1)} \le \int_{I_k} x^s \, d\lambda \le 2^{|s|} \, 2^{-k(s+1)}.$$
The corollary on series of Chapter 4 gives $\int_{(0,1]} x^s \, d\lambda = \sum_k \int_{I_k} x^s \, d\lambda$. This is a geometric series with ratio $2^{-(s+1)}$, finite exactly when $s > -1$. So $x^s$ is integrable on $(0, 1]$ if and only if $s > -1$. For $s = -1$ every term is comparable to $1$, and $1/x$ is not integrable.

::: mathlib
`intervalIntegral.integrableOn_Ioo_rpow_iff` · `Mathlib.Analysis.SpecialFunctions.Integrability.Basic`

For `0 < t`, `IntegrableOn (fun x ↦ x ^ s) (Ioo 0 t) ↔ -1 < s`. The value of the integral needs the fundamental theorem of calculus of Chapter 8.

<?decl intervalIntegral.integrableOn_Ioo_rpow_iff?>
:::

**Counterexample (Constants on an infinite measure).** On $\mathbb{R}$ with Lebesgue measure the constant $1$ is not integrable: $\int 1 \, d\lambda = \lambda(\mathbb{R}) = \infty$. The finiteness of $\mu$ is needed in the proposition on bounded functions.

**Counterexample (Measurability is part of the definition).** Let $V \subseteq [0, 1]$ be the Vitali set of Chapter 3 and $f = \mathbf{1}_V$ on $[0, 1]$. Then $\|f\| \le 1$, so $\int \|f\| \, d\lambda \le 1$. But $f$ is not integrable: it is not almost everywhere equal to a measurable function, since a measurable $h$ with $h = \mathbf{1}_V$ outside a null set $N$ makes $V$ differ from the measurable set $\{h = 1\}$ by a subset of $N$, and $V$ would be Lebesgue measurable.

### The library around it

Strong measurability is the measurability notion of the Bochner integral. For the usual targets it is the same as measurability, but it needs no σ-algebra on the target and it gives the simple approximations that Section 2 uses.

::: mathlib
`MeasureTheory.LocallyIntegrable` · `Mathlib.MeasureTheory.Function.LocallyIntegrable`

`LocallyIntegrable f μ` says that every point has a neighbourhood on which `f` is integrable. `Continuous.locallyIntegrable` gives it for continuous functions and a locally finite measure.

<?decl MeasureTheory.LocallyIntegrable?>
:::

Common errors of a learner:

- Proving `HasFiniteIntegral` and forgetting `AEStronglyMeasurable`.
- Applying `integrable_const` without `IsFiniteMeasure μ`.
- Expecting `Integrable f` to refer to the measure in the context. Without a measure it means `volume`.
- Confusing integrability on $(0, 1]$ with integrability on a compact set: $1/x$ is continuous on $(0, 1]$ but not integrable there.

### Exercises

1. (A) Show that $e^{-|x|}$ is integrable on $\mathbb{R}$. Hint: $e^{-|x|} \le e^{-n}$ on $n \le |x| < n + 1$.
2. (A) Show that $\mathbf{1}_A$ is integrable if and only if $A$ is measurable up to a null set and $\mu(A) < \infty$.
3. (A) Show that $f$ is integrable if and only if $\|f\|$ is integrable, for $f$ almost everywhere strongly measurable.
4. (B) Find the $s$ for which $x^s$ is integrable on $[1, \infty)$. Hint: cut into $[2^k, 2^{k+1})$.
5. (B) Show that $f$ is integrable on $A \cup B$ if it is integrable on $A$ and on $B$. Hint: $\mu|_{A \cup B} \le \mu|_A + \mu|_B$.
6. (B) Let $f : X \to \mathbb{R}^2$ have components $f_1, f_2$. Show that $f$ is integrable if and only if $f_1$ and $f_2$ are. Hint: $|f_i| \le \|f\| \le |f_1| + |f_2|$ for the sum norm.
7. (C) Let $E$ be a normed space that is not complete. Find simple functions $\varphi_n$ on $[0, 1]$ with $\sum_n \int \|\varphi_n\| \, d\lambda < \infty$ such that $\sum_n \varphi_n(x)$ converges at no $x$. Hint: constant functions and a series that does not converge in $E$.

### Notes and history

Bochner defined the integral of functions with values in a Banach space in 1933. In Mathlib, the files on strong measurability have Rémy Degenne and Sébastien Gouëzel as authors, and the files on integrable functions have Zhouhang Zhou. The choice of strong measurability lets the integral work with targets that have no natural σ-algebra.

### Reference

<?reference?>
