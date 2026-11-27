---
title: Simple functions and the Lebesgue integral
kind: theory
modules:
  - Mathlib.MeasureTheory.Function.SimpleFunc
  - Mathlib.MeasureTheory.Integral.Lebesgue.Basic
explains:
  E3: [MeasureTheory.SimpleFunc, MeasureTheory.SimpleFunc.lintegral, MeasureTheory.lintegral, MeasureTheory.SimpleFunc.eapprox, MeasureTheory.SimpleFunc.iSup_eapprox_apply]
  E2: [MeasureTheory.SimpleFunc.add_lintegral, MeasureTheory.SimpleFunc.lintegral_mono, MeasureTheory.SimpleFunc.lintegral_eq_lintegral, MeasureTheory.SimpleFunc.monotone_eapprox, MeasureTheory.lintegral_mono, MeasureTheory.lintegral_indicator_const, MeasureTheory.lintegral_eq_zero_iff, MeasureTheory.lintegral_congr_ae, Measurable.ennreal_induction]
  E1: auto
families: []
requires: [V04, V13, V18.C01, V18.C02, V18.C03]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Simple functions and the Lebesgue integral

### Overview

The Riemann integral cuts the domain into intervals. The Lebesgue integral cuts the range: it weights each value of $f$ by the measure of the set where $f$ takes it. A function with finitely many values, each on a measurable set, has an obvious integral, the sum of value times measure. This section defines these simple functions, proves the rules for their integral, and defines the integral of any $f : X \to [0, \infty]$ as the supremum of the integrals of the simple functions below $f$. The main theorem says that every measurable $f \ge 0$ is an increasing limit of simple functions.

### Definitions

The integral of this chapter takes values in $[0, \infty]$, the type `ℝ≥0∞` of Mathlib. Its arithmetic has the conventions $a + \infty = \infty$ and $0 \cdot \infty = 0$. With the second one, the value $\infty$ on a null set contributes nothing. Every subset of $[0, \infty]$ has a supremum.

**Definition (Simple function).** Let $(X, \mathcal{A})$ be a measurable space and $Y$ a set. A *simple function* $f : X \to Y$ has finite range, and each fiber $f^{-1}(\{y\})$ is measurable.

::: mathlib
`MeasureTheory.SimpleFunc` · `Mathlib.MeasureTheory.Function.SimpleFunc`

`SimpleFunc α β`, written `α →ₛ β`, is a structure with the fields `toFun`, `measurableSet_fiber'` and `finite_range'`.

<?decl MeasureTheory.SimpleFunc?>
:::

**Definition (Integral of a simple function).** For a simple $f : X \to [0, \infty]$,
$$\int f \, d\mu = \sum_{y \in f(X)} y \, \mu(f^{-1}(\{y\})).$$

**Definition (Lebesgue integral).** For any $f : X \to [0, \infty]$,
$$\int f \, d\mu = \sup \Big\{ \int g \, d\mu : g \text{ simple}, \ g \le f \Big\}.$$
For a measurable set $A$, $\int_A f \, d\mu = \int f \, d(\mu|_A)$, with the restriction $\mu|_A$ of Chapter 2.

::: mathlib
`MeasureTheory.SimpleFunc.lintegral` · `Mathlib.MeasureTheory.Function.SimpleFunc`

`f.lintegral μ` is `∑ x ∈ f.range, x * μ (f ⁻¹' {x})`, the formula of the definition.

<?decl MeasureTheory.SimpleFunc.lintegral?>
:::

::: mathlib
`MeasureTheory.lintegral` · `Mathlib.MeasureTheory.Integral.Lebesgue.Basic`

`lintegral μ f` is `⨆ (g : α →ₛ ℝ≥0∞) (_ : ⇑g ≤ f), g.lintegral μ`, written `∫⁻ x, f x ∂μ`. The form `∫⁻ x in s, f x ∂μ` is the integral for `μ.restrict s`. The definition has no measurability hypothesis. So `∫⁻ f` always exists, and only the lemmas that need measurability, such as additivity, ask for it.

<?decl MeasureTheory.lintegral?>
:::

### Theorems and proofs

**Lemma (Partition formula).** Let $A_1, \dots, A_m$ be disjoint measurable sets with union $X$, and let $f$ be simple with the value $a_i$ on $A_i$. Then $\int f \, d\mu = \sum_{i=1}^m a_i \, \mu(A_i)$.

*Proof.* For $y$ in the range of $f$, the fiber $f^{-1}(\{y\})$ is the disjoint union of the $A_i$ with $a_i = y$, so $\mu(f^{-1}(\{y\})) = \sum_{a_i = y} \mu(A_i)$. Multiply by $y$ and sum over $y$. Each index $i$ appears once, in the term $y = a_i$. An empty $A_i$ adds $a_i \cdot 0 = 0$. $\square$

**Proposition (Rules for simple functions).** Let $f, g \ge 0$ be simple and $c \in [0, \infty]$. Then $\int (f + g) \, d\mu = \int f \, d\mu + \int g \, d\mu$ and $\int c f \, d\mu = c \int f \, d\mu$, and $f \le g$ implies $\int f \, d\mu \le \int g \, d\mu$.

*Proof.* The sets $C_{y,z} = f^{-1}(\{y\}) \cap g^{-1}(\{z\})$, for $y$ in the range of $f$ and $z$ in the range of $g$, form a finite measurable partition of $X$. On $C_{y,z}$ the function $f + g$ is $y + z$. The partition formula gives
$$\int (f + g) \, d\mu = \sum_{y,z} y \, \mu(C_{y,z}) + \sum_{y,z} z \, \mu(C_{y,z}),$$
and the partition formula for $f$ and for $g$ on the same partition identifies the two sums as $\int f \, d\mu$ and $\int g \, d\mu$. The function $cf$ is $cy$ on $C_{y,z}$, which gives the second rule. If $f \le g$, then $y \le z$ for every nonempty $C_{y,z}$, and the empty ones add $0$, so $\sum y \, \mu(C_{y,z}) \le \sum z \, \mu(C_{y,z})$. $\square$

::: mathlib
`MeasureTheory.SimpleFunc.add_lintegral` · `Mathlib.MeasureTheory.Function.SimpleFunc`

`(f + g).lintegral μ = f.lintegral μ + g.lintegral μ`. The monotone form `SimpleFunc.lintegral_mono` takes `f ≤ g` and `μ ≤ ν` at once.

<?decl MeasureTheory.SimpleFunc.add_lintegral?>
<?decl MeasureTheory.SimpleFunc.lintegral_mono?>
:::

**Proposition (Consistency and monotonicity).** For a simple $f \ge 0$ the two definitions of $\int f \, d\mu$ agree. If $f \le g$, then $\int f \, d\mu \le \int g \, d\mu$. For measurable $A$, $\int c \mathbf{1}_A \, d\mu = c \, \mu(A)$.

*Proof.* Let $f$ be simple. The supremum is at least the simple integral of $f$, since $f \le f$, and at most it, since every simple $g \le f$ has a smaller simple integral. If $f \le g$, every simple function below $f$ is below $g$. The last claim is the partition formula for $A$, $X \setminus A$ with the values $c$, $0$. $\square$

::: mathlib
`MeasureTheory.SimpleFunc.lintegral_eq_lintegral` · `Mathlib.MeasureTheory.Integral.Lebesgue.Basic`

`∫⁻ a, f a ∂μ = f.lintegral μ` for `f : α →ₛ ℝ≥0∞`. Monotonicity is `lintegral_mono`, for all functions, with no measurability. Indicators give `lintegral_indicator_const`: `∫⁻ a, s.indicator (fun _ ↦ c) a ∂μ = c * μ s` for `MeasurableSet s`.

<?decl MeasureTheory.SimpleFunc.lintegral_eq_lintegral?>
<?decl MeasureTheory.lintegral_mono?>
<?decl MeasureTheory.lintegral_indicator_const?>
:::

**Theorem (Approximation by simple functions).** Let $f : X \to [0, \infty]$ be measurable. There are simple functions $0 \le \varphi_1 \le \varphi_2 \le \dots$ with finite values and $\varphi_n(x) \to f(x)$ for every $x$. If $f$ is bounded, the convergence is uniform.

*Proof.* For $t \in [0, \infty)$ put $d_n(t) = 2^{-n} \lfloor 2^n t \rfloor$, and put $d_n(\infty) = \infty$. Define $\varphi_n(x) = \min(n, d_n(f(x)))$.

*Simple.* The values of $\varphi_n$ lie in $\{k 2^{-n} : 0 \le k \le n 2^n\}$. For $k < n 2^n$ the fiber of $k 2^{-n}$ is $\{k 2^{-n} \le f < (k+1) 2^{-n}\}$, and the fiber of $n$ is $\{f \ge n\}$. These are preimages of intervals under $f$, so they are measurable by Chapter 1.

*Increasing.* For real $s$, $2 \lfloor s \rfloor$ is an integer at most $2s$, so $2 \lfloor s \rfloor \le \lfloor 2s \rfloor$. With $s = 2^n t$ this gives $d_n(t) \le d_{n+1}(t)$. The minimum is monotone in both arguments, so $\varphi_n \le \varphi_{n+1}$. Also $\varphi_n \le f$.

*Convergence.* If $f(x) = \infty$, then $\varphi_n(x) = n \to \infty$. If $f(x) < \infty$ and $n > f(x)$, then $\varphi_n(x) = d_n(f(x))$, and $\lfloor s \rfloor > s - 1$ gives $f(x) - 2^{-n} < \varphi_n(x) \le f(x)$.

*Uniformity.* If $f \le M$, the last estimate holds for $n > M$ at all $x$ at once. $\square$

::: mathlib
`MeasureTheory.SimpleFunc.eapprox` · `Mathlib.MeasureTheory.Function.SimpleFunc`

Mathlib does not use dyadic numbers. `eapprox f n` is `approx ennrealRatEmbed f n`, where `ennrealRatEmbed` enumerates the nonnegative rationals and `approx i f n a` is the largest `i k` with `k < n` and `i k ≤ f a`, or $0$. For `Measurable f`, `iSup_eapprox_apply` gives `⨆ n, eapprox f n a = f a`, and `monotone_eapprox` gives monotonicity.

<?decl MeasureTheory.SimpleFunc.eapprox?>
<?decl MeasureTheory.SimpleFunc.iSup_eapprox_apply?>
<?decl MeasureTheory.SimpleFunc.monotone_eapprox?>
:::

::: mathlib
`Measurable.ennreal_induction` · `Mathlib.MeasureTheory.Function.SimpleFunc`

The theorem gives a method of proof, in the form of an induction principle. The cases are: indicators `s.indicator (const c)` of measurable sets; sums `f + g` of measurable functions with disjoint supports; and suprema `⨆ n, f n` of increasing sequences of measurable functions. The conclusion holds for every measurable `f : α → ℝ≥0∞`.

<?decl Measurable.ennreal_induction?>
:::

**Proposition (Null sets do not count).** If $f = g$ almost everywhere, then $\int f \, d\mu = \int g \, d\mu$. If $f$ is measurable, then $\int f \, d\mu = 0$ if and only if $f = 0$ almost everywhere.

*Proof.* Let $N$ be a null set with $f = g$ outside $N$, and let $\varphi \le f$ be simple. Then $\psi = \varphi \mathbf{1}_{X \setminus N}$ is simple and $\psi \le g$. On the partition by the sets $\{\varphi = y\} \cap N$ and $\{\varphi = y\} \setminus N$, the partition formula gives $\int \psi \, d\mu = \int \varphi \, d\mu$, since the pieces in $N$ are null. So $\int \varphi \, d\mu \le \int g \, d\mu$, hence $\int f \, d\mu \le \int g \, d\mu$, and symmetry gives equality.

If $f = 0$ almost everywhere, then $\int f \, d\mu = \int 0 \, d\mu = 0$. Conversely, let $\int f \, d\mu = 0$. The set $A_n = \{f \ge 1/n\}$ is measurable and $\frac{1}{n} \mathbf{1}_{A_n} \le f$, so $\frac{1}{n} \mu(A_n) \le 0$ and $\mu(A_n) = 0$. Then $\{f > 0\} = \bigcup_n A_n$ is null. $\square$

::: mathlib
`MeasureTheory.lintegral_eq_zero_iff` · `Mathlib.MeasureTheory.Integral.Lebesgue.Basic`

`Measurable f → (∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0)`. The primed form takes `AEMeasurable f μ`. The first claim is `lintegral_congr_ae`, from `f =ᵐ[μ] g`, with no measurability.

<?decl MeasureTheory.lintegral_eq_zero_iff?>
<?decl MeasureTheory.lintegral_congr_ae?>
:::

### Examples

**Example (A step function).** Let $\lambda$ be Lebesgue measure on $[0, 3]$ and $f(x) = \lfloor x \rfloor$. The partition $[0, 1)$, $[1, 2)$, $[2, 3)$, $\{3\}$ carries the values $0, 1, 2, 3$, so $\int f \, d\lambda = 0 + 1 + 2 + 3 \cdot 0 = 3$.

**Example (The indicator of the rationals).** The set $\mathbb{Q}$ is countable, so it is null by Chapter 3, and $\int \mathbf{1}_{\mathbb{Q} \cap [0, 1]} \, d\lambda = 0$. It has no Riemann integral. In the same way $\int \infty \cdot \mathbf{1}_{\mathbb{Q}} \, d\lambda = \infty \cdot 0 = 0$.

**Counterexample (Measurability in the zero test).** Let $V \subseteq [0, 1]$ be the Vitali set of Chapter 3 and $f = \mathbf{1}_V$. A measurable $B \subseteq V$ is null: its translates by the rationals of $[-1, 1]$ are disjoint subsets of $[-1, 2]$, so countable additivity gives $\sum_q \lambda(B) \le 3$. A simple $\varphi \le f$ has its fibers over $y > 0$ inside $V$, so $\int \varphi \, d\lambda = 0$, and $\int f \, d\lambda = 0$. But $f$ is not $0$ almost everywhere. A null set $N \supseteq V$ would have null translates by the rationals of $[-1, 1]$ that cover $[0, 1]$.

### The library around it

The file `Mathlib.MeasureTheory.Integral.Lebesgue.Basic` proves the rules that need no limit theorem: monotonicity, constants (`lintegral_const`), indicators, congruence and the test for $0$. Additivity and the limit theorems are in the files of Section 2.

Common errors of a learner:

- Reading $0 \cdot \infty$ as undefined. In `ℝ≥0∞` it is $0$.
- Assuming that `∫⁻` needs a measurable function. Only some lemmas do.
- Using the formula of the definition for a sum over overlapping sets. The partition formula needs disjoint sets.
- Replacing `∫⁻ x in s, f x ∂μ` by the integral of `s.indicator f` for a set `s` that is not measurable. The lemma `lintegral_indicator` needs `MeasurableSet s`.

### Exercises

1. (A) Compute $\int f \, d\lambda$ for $f = 2 \cdot \mathbf{1}_{[0, 1]} + 5 \cdot \mathbf{1}_{[1/2, 3]}$ on $\mathbb{R}$.
2. (A) Let $\mu$ be the counting measure on $\mathbb{N}$ and $f : \mathbb{N} \to [0, \infty]$ with finite range. Show that $\int f \, d\mu = \sum_n f(n)$.
3. (A) Show that $\int f \, d\mu < \infty$ for a simple $f$ implies $\mu(\{f = \infty\}) = 0$.
4. (B) Let $A_1, \dots, A_m$ be measurable sets, not necessarily disjoint. Show that $\int \sum_i a_i \mathbf{1}_{A_i} \, d\mu = \sum_i a_i \mu(A_i)$. Hint: the rules for simple functions.
5. (B) Show that $\int f \, d(\mu + \nu) = \int f \, d\mu + \int f \, d\nu$ for simple $f$. Hint: the formula of the definition.
6. (C) Show that $\int f \, d\mu = \sup \{\int g \, d\mu : g \text{ measurable}, g \le f\}$ for every $f \ge 0$, and that the supremum is attained. Hint: take simple $g_n \le f$ with integrals tending to the supremum and use $\max(g_1, \dots, g_n)$ with Section 2.

### Notes and history

Lebesgue defined his integral in his thesis of 1902. He divided the range into small intervals and weighted each one by the measure of its preimage. In Mathlib, the files on simple functions and on the basic integral have Mario Carneiro and Johannes Hölzl as authors.

### Reference

<?reference?>
