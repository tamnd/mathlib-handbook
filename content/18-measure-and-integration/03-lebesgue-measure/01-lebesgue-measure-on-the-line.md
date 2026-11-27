---
title: Lebesgue measure on the line
kind: theory
modules:
  - Mathlib.MeasureTheory.Measure.Stieltjes
  - Mathlib.MeasureTheory.Measure.Lebesgue.Basic
  - Mathlib.MeasureTheory.Measure.Regular
  - Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
explains:
  E3: [StieltjesFunction, StieltjesFunction.measure, StieltjesFunction.measure_Ioc, StieltjesFunction.length_subadditive_Icc_Ioo, StieltjesFunction.measurableSet_Ioi, Real.volume_eq_stieltjes_id, Real.volume_Icc, MeasureTheory.Measure.Regular, Set.exists_isOpen_lt_add]
  E2: [StieltjesFunction.length, StieltjesFunction.outer, StieltjesFunction.outer_Ioc, StieltjesFunction.borel_le_measurable, StieltjesFunction.measure_singleton, StieltjesFunction.measure_Icc, StieltjesFunction.measure_Ioo, Monotone.stieltjesFunction, StieltjesFunction.id, Real.volume_Ioo, Real.volume_Ioc, Real.volume_singleton, Real.volume_univ, Real.volume_preimage_mul_left, Real.nullSingletonClass_volume, Set.Countable.measure_zero, MeasureTheory.NullSingletonClass, MeasureTheory.Measure.OuterRegular, MeasureTheory.Measure.InnerRegular, MeasurableSet.exists_isCompact_lt_add, MeasureTheory.Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure]
  E1: auto
families: []
requires: [V13, V15, V18.C01, V18.C02]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Lebesgue measure on the line

### Overview

This section applies the tools of Chapter 2 to the most important example: a measure $\lambda$ on the Borel sets of $\mathbb{R}$ with $\lambda((a, b]) = b - a$, built for any increasing right continuous $F$ at once as the Lebesgue-Stieltjes measure $\mu_F$. The key step is compactness: a closed interval cannot be covered by open intervals of smaller total length. The section then computes the measure of intervals and countable sets, proves translation invariance and the scaling law, and proves that Lebesgue measure is outer regular.

### Definitions

**Definition (Stieltjes function).** A *Stieltjes function* is a function $F : \mathbb{R} \to \mathbb{R}$ that is increasing and right continuous: $F(y) \to F(x)$ as $y \to x^+$. Its *left limit* at $x$ is $F(x^-) = \sup_{y < x} F(y)$.

An increasing function has one-sided limits everywhere (Volume 15, Chapter 1). Right continuity is a normalization, and a counterexample below shows that it cannot be dropped.

::: mathlib
`StieltjesFunction` · `Mathlib.MeasureTheory.Measure.Stieltjes`

A structure with the function `toFun`, the proof `mono'` of monotonicity and the proof `right_continuous'` of `ContinuousWithinAt toFun (Ici x) x`. Mathlib defines `StieltjesFunction R` for any conditionally complete, densely ordered linear order `R`, so it also covers $[0, \infty)$ and $[0, T]$. The identity is `StieltjesFunction.id`, and `Monotone.stieltjesFunction` turns a monotone function into a Stieltjes function by taking right limits.

<?decl StieltjesFunction?>
:::

**Definition (Lebesgue-Stieltjes outer measure).** For $A \subseteq \mathbb{R}$ let
$$\lambda_F^*(A) = \inf \Big\{ \sum_{i=0}^{\infty} \big(F(b_i) - F(a_i)\big) : a_i \le b_i, \ A \subseteq \bigcup_{i} (a_i, b_i] \Big\}.$$

By Chapter 2, Section 2 this is an outer measure. Half-open intervals are used because $(a, b] = (a, c] \cup (c, b]$ is a disjoint union and the lengths add exactly.

::: mathlib
`StieltjesFunction.outer` · `Mathlib.MeasureTheory.Measure.Stieltjes`

Two steps. `StieltjesFunction.length f s` is the infimum of `ofReal (f b - f a)` over the intervals `Ioc a b` that contain `s`, and `f.outer` is `OuterMeasure.ofFunction f.length` (Chapter 2, Section 2). Covering $A$ by sets and each set by one interval gives back the formula of the text. The values are in `ℝ≥0∞`.

<?decl StieltjesFunction.outer?>
:::

**Definition (Lebesgue-Stieltjes measure, Lebesgue measure).** The *Lebesgue-Stieltjes measure* $\mu_F$ is the restriction of $\lambda_F^*$ to the Borel sets. *Lebesgue measure* $\lambda$ is $\mu_F$ for $F(x) = x$.

Theorem 2 shows that $\mu_F$ is a measure. The sets that are Carathéodory measurable for $\lambda^*$ are the *Lebesgue measurable* sets; they form the completion of the Borel σ-algebra (Chapter 2, Section 3).

::: mathlib
`StieltjesFunction.measure` · `Mathlib.MeasureTheory.Measure.Stieltjes`

`f.measure : Measure ℝ` has `f.outer` as its outer measure. Countable additivity comes from Carathéodory's theorem and `StieltjesFunction.borel_le_measurable`.

<?decl StieltjesFunction.measure?>
:::

::: mathlib
`Real.volume_eq_stieltjes_id` · `Mathlib.MeasureTheory.Measure.Lebesgue.Basic`

Lebesgue measure on $\mathbb{R}$ is `volume`, from the instance `Real.measureSpace`. That instance is not defined by Stieltjes functions: it is the volume of a finite dimensional inner product space, the Haar measure that gives the unit cube of an orthonormal basis the value $1$ (Section 2). This theorem identifies the two constructions, and `Real.volume_val` rewrites `volume s` as `StieltjesFunction.id.measure s`.

<?decl Real.volume_eq_stieltjes_id?>
:::

**Definition (Regular measure).** A Borel measure $\mu$ is *outer regular* if $\mu(A) = \inf\{\mu(U) : U \supseteq A \text{ open}\}$ for every Borel set $A$, and *inner regular* if $\mu(A) = \sup\{\mu(K) : K \subseteq A \text{ compact}\}$. It is *regular* if it is outer regular, finite on compact sets, and inner regular on open sets.

::: mathlib
`MeasureTheory.Measure.Regular` · `Mathlib.MeasureTheory.Measure.Regular`

A class with the fields `IsFiniteMeasureOnCompacts`, `OuterRegular` and inner regularity of open sets. The same file has `WeaklyRegular` (closed sets in place of compact sets) and `InnerRegular`. The instance `Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure` makes every locally finite measure on a σ-compact metrizable space regular, so `volume` is regular with no work from the user.

<?decl MeasureTheory.Measure.Regular?>
:::

### Theorems and proofs

**Lemma (Finite covers of a closed interval).** Let $c \le d$ and $[c, d] \subseteq \bigcup_{i=1}^{n} (c_i, d_i)$. Then $F(d) - F(c) \le \sum_{i=1}^{n} \big(F(d_i) - F(c_i)\big)$.

*Proof.* Induction on $n$. For $n = 0$ the empty union cannot contain $[c, d]$. Let $n \ge 1$. The point $d$ lies in some $(c_k, d_k)$. If $c_k < c$, monotonicity gives $F(d) - F(c) \le F(d_k) - F(c_k)$, and the other terms are $\ge 0$. If $c \le c_k$, no point of $[c, c_k]$ lies in $(c_k, d_k)$, so the other $n - 1$ intervals cover $[c, c_k]$ and the induction hypothesis gives $F(c_k) - F(c) \le \sum_{i \ne k} (F(d_i) - F(c_i))$. Add $F(d) - F(c_k) \le F(d_k) - F(c_k)$. $\square$

**Theorem 1 (The outer measure of an interval).** For $a \le b$, $\lambda_F^*((a, b]) = F(b) - F(a)$.

*Proof.* The interval covers itself, which gives $\le$. For $\ge$ let $a < b$, let $(a, b] \subseteq \bigcup_i (a_i, b_i]$ with sum $S < \infty$, and let $\varepsilon > 0$. By right continuity choose $a' \in (a, b)$ with $F(a') \le F(a) + \varepsilon$ and $b_i' > b_i$ with $F(b_i') \le F(b_i) + \varepsilon 2^{-i-1}$. Then $[a', b] \subseteq \bigcup_i (a_i, b_i')$. The interval $[a', b]$ is compact (Volume 13, Chapter 5), so finitely many of the open intervals cover it, and the lemma gives
$$F(b) - F(a') \le \sum_{i} \big(F(b_i') - F(a_i)\big) \le S + \varepsilon.$$
So $F(b) - F(a) \le S + 2\varepsilon$ for every cover and every $\varepsilon$. $\square$

Right continuity is used twice: at $a$ to pass to a closed interval, and at the $b_i$ to open the covering intervals.

::: mathlib
`StieltjesFunction.length_subadditive_Icc_Ioo` · `Mathlib.MeasureTheory.Measure.Stieltjes`

The lemma and the compactness step together: if `Icc a b ⊆ ⋃ i, Iotop (c i) (d i)`, then `ofReal (f b - f a) ≤ ∑' i, ofReal (f (d i) - f (c i))`. Here `Iotop c d` is `Ioo c d`, or `Ioc c d` when `d` is a top element. The proof takes a finite subcover with `IsCompact.elim_finite_subcover_image` and inducts over a `Finset`. Theorem 1 is `StieltjesFunction.outer_Ioc`.

<?decl StieltjesFunction.length_subadditive_Icc_Ioo?>
:::

**Theorem 2 (Borel sets are measurable).** Every Borel set is Carathéodory measurable for $\lambda_F^*$. So $\mu_F$ is a measure, and $\mu_F((a, b]) = F(b) - F(a)$ for $a \le b$.

*Proof.* The rays $E = (c, \infty)$ generate the Borel σ-algebra (Chapter 1, Section 1), and the Carathéodory measurable sets form a σ-algebra (Chapter 2, Section 2). So it suffices to show $\lambda_F^*(T) \ge \lambda_F^*(T \cap E) + \lambda_F^*(T \setminus E)$ for every $T$ with $\lambda_F^*(T) < \infty$. Let $\varepsilon > 0$ and $T \subseteq \bigcup_i (a_i, b_i]$ with $\sum_i (F(b_i) - F(a_i)) \le \lambda_F^*(T) + \varepsilon$. Each interval splits as
$$(a_i, b_i] \cap E = (\max(a_i, c), \max(b_i, c)], \qquad (a_i, b_i] \setminus E = (\min(a_i, c), \min(b_i, c)].$$
For every $x$, the numbers $\max(x, c)$ and $\min(x, c)$ are $x$ and $c$ in some order, so $F(\max(x, c)) + F(\min(x, c)) = F(x) + F(c)$. With $x = b_i$ and $x = a_i$ this shows that the lengths of the two pieces add up to $F(b_i) - F(a_i)$. The first pieces cover $T \cap E$ and the second pieces cover $T \setminus E$, so $\lambda_F^*(T \cap E) + \lambda_F^*(T \setminus E) \le \lambda_F^*(T) + \varepsilon$. Carathéodory's theorem then makes $\lambda_F^*$ countably additive on the Borel sets, and Theorem 1 gives the value on $(a, b]$. $\square$

::: mathlib
`StieltjesFunction.measurableSet_Ioi` · `Mathlib.MeasureTheory.Measure.Stieltjes`

`MeasurableSet[f.outer.caratheodory] (Ioi c)`; the bracket names the σ-algebra. Then `StieltjesFunction.borel_le_measurable` proves `borel R ≤ f.outer.caratheodory` with `borel_eq_generateFrom_Ioi` and `MeasurableSpace.generateFrom_le`, as in the proof.

<?decl StieltjesFunction.measurableSet_Ioi?>
:::

::: mathlib
`StieltjesFunction.measure_Ioc` · `Mathlib.MeasureTheory.Measure.Stieltjes`

`f.measure (Ioc a b) = ofReal (f b - f a)`, with no hypothesis $a \le b$: for $b < a$ both sides are $0$. A simp lemma.

<?decl StieltjesFunction.measure_Ioc?>
:::

**Corollary 3 (Other intervals).** For $a \le b$, $\mu_F(\{a\}) = F(a) - F(a^-)$, $\mu_F([a, b]) = F(b) - F(a^-)$ and $\mu_F((a, b)) = F(b^-) - F(a)$. For Lebesgue measure every interval with end points $a \le b$ has measure $b - a$, every countable set is null, and $\lambda(\mathbb{R}) = \infty$.

*Proof.* The sets $(a - 1/n, a]$ decrease to $\{a\}$ and have finite measure, so continuity from above (Chapter 2, Section 1) gives $\mu_F(\{a\}) = \lim_n (F(a) - F(a - 1/n)) = F(a) - F(a^-)$. Then $[a, b] = \{a\} \cup (a, b]$ is disjoint. The sets $(a, b - 1/n]$ increase to $(a, b)$, and continuity from below gives the third formula. For $F(x) = x$, $F(x^-) = x$, so points are null, and a countable set is a countable union of points. Finally $\lambda(\mathbb{R}) \ge \lambda((-n, n]) = 2n$. $\square$

::: mathlib
`Real.volume_Icc` · `Mathlib.MeasureTheory.Measure.Lebesgue.Basic`

`volume (Icc a b) = ofReal (b - a)`, a simp lemma, with the siblings `Real.volume_Ioo`, `Real.volume_Ioc`, `Real.volume_singleton` and `Real.volume_univ`, and `Real.volume_real_Icc` for the real value `volume.real (Icc a b) = max (b - a) 0`. For countable sets the lemma is `Set.Countable.measure_zero`. It needs the class `NullSingletonClass μ`, which `Real.nullSingletonClass_volume` provides. The Stieltjes forms use `Function.leftLim f a` for $F(a^-)$.

<?decl Real.volume_Icc?>
:::

**Theorem 4 (Translations and dilations).** For every Borel set $A$, $x \in \mathbb{R}$ and $c \ne 0$: $\lambda(A + x) = \lambda(A)$ and $\lambda(cA) = |c|\,\lambda(A)$.

*Proof.* Let $\nu(A) = \lambda(A + x)$. It is the image of $\lambda$ under the continuous map $y \mapsto y - x$, so it is a Borel measure (Chapter 2, Section 3), and $\nu((a, b]) = \lambda((a + x, b + x]) = b - a$. The half-open intervals form a π-system that generates the Borel sets, and $\nu((-n, n]) = 2n < \infty$ for the sets $(-n, n]$ that exhaust $\mathbb{R}$. The uniqueness theorem of Chapter 2, Section 3 gives $\nu = \lambda$. For $c > 0$ the same argument applies to $\nu(A) = c^{-1}\lambda(cA)$. For $c = -1$ use $\nu(A) = \lambda(-A)$, with $\nu((a, b]) = \lambda([-b, -a)) = b - a$ by Corollary 3. A general $c < 0$ is the composition of the two cases. $\square$

This is the standard way to prove an identity of measures: check it on a π-system and apply uniqueness.

::: mathlib
`Real.volume_preimage_mul_left` · `Mathlib.MeasureTheory.Measure.Lebesgue.Basic`

Mathlib uses preimages, which are measurable with no hypothesis: `volume ((a * ·) ⁻¹' s) = ofReal |a⁻¹| * volume s` for `a ≠ 0`. Translation invariance comes from the general `MeasureTheory.measure_preimage_add`, because `volume` is a Haar measure (Section 2).

<?decl Real.volume_preimage_mul_left?>
:::

**Theorem 5 (Outer regularity).** For every Borel set $A$ and $\varepsilon > 0$ there is an open $U \supseteq A$ with $\lambda(U) \le \lambda(A) + \varepsilon$.

*Proof.* If $\lambda(A) = \infty$ take $U = \mathbb{R}$. Otherwise choose $A \subseteq \bigcup_i (a_i, b_i]$ with $\sum_i (b_i - a_i) \le \lambda(A) + \varepsilon/2$, and let $U = \bigcup_i (a_i, b_i + \varepsilon 2^{-i-2})$. It is open, contains $A$, and $\lambda(U) \le \sum_i (b_i - a_i + \varepsilon 2^{-i-2}) \le \lambda(A) + \varepsilon$ by subadditivity. $\square$

Exercise 5 derives inner regularity from this theorem: $\lambda(A) = \sup \{\lambda(K) : K \subseteq A \text{ compact}\}$.

::: mathlib
`Set.exists_isOpen_lt_add` · `Mathlib.MeasureTheory.Measure.Regular`

For any outer regular measure and any set `A`: `μ A ≠ ⊤ → ε ≠ 0 → ∃ U ⊇ A, IsOpen U ∧ μ U < μ A + ε`. The compact form `MeasurableSet.exists_isCompact_lt_add` needs the class `InnerRegularCompactLTTop μ`. Mathlib does not prove the regularity of `volume` by hand: it gets it from the general instance for locally finite measures.

<?decl Set.exists_isOpen_lt_add?>
:::

### Examples

**Example (Rationals and irrationals).** The set $\mathbb{Q} \cap [0, 1]$ is countable, so it is null, and the irrational numbers of $[0, 1]$ have measure $1$. In Mathlib the rationals are null by `Set.Countable.measure_zero (Set.countable_range ((↑) : ℚ → ℝ)) volume`.

**Example (A step function gives point masses).** Let $F(x) = \lfloor x \rfloor$, which is increasing and right continuous. By Theorem 2, $\mu_F((a, b]) = \lfloor b \rfloor - \lfloor a \rfloor$, the number of integers in $(a, b]$. So $\mu_F$ agrees with $\sum_{n \in \mathbb{Z}} \delta_n$ on half-open intervals, and the uniqueness theorem gives equality. By Corollary 3, $\mu_F([0, 2.5]) = F(2.5) - F(0^-) = 2 - (-1) = 3$.

**Example (The Cantor set).** Remove from $[0, 1]$ the open middle third, then the open middle thirds of the two remaining intervals, and so on. After $n$ steps $2^n$ intervals of length $3^{-n}$ remain, of total measure $(2/3)^n$. The Cantor set $C$ is the intersection, so $\lambda(C) = 0$. But $C$ is uncountable: it is the set of numbers with a ternary expansion in the digits $0$ and $2$. Mathlib has the set as `cantorSet` in `Mathlib.Topology.Instances.CantorSet`; the index of this edition has no declaration for its Lebesgue measure.

**Counterexample (Right continuity is needed).** Let $F(x) = 0$ for $x \le 0$ and $F(x) = 1$ for $x > 0$, and $\ell((a, b]) = F(b) - F(a)$. Then $\ell((0, 1]) = 1$, but $(0, 1]$ is the disjoint union of the intervals $(1/(n+1), 1/n]$, each with $\ell = 0$. So no measure extends $\ell$. The proof of Theorem 1 fails at its first step: no $a' > 0$ has $F(a') \le F(0) + \varepsilon$. Mathlib's `Monotone.stieltjesFunction` replaces $F$ by its right limits, the indicator of $[0, \infty)$, whose measure is $\delta_0$.

### The library around it

`Mathlib.MeasureTheory.Measure.Stieltjes` has a lemma `StieltjesFunction.measure_I**` for each kind of interval, and `StieltjesFunction.isProbabilityMeasure` for a function with limits $0$ and $1$ at $\mp\infty$: this is how a distribution function gives a law in Volume 20. `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` has the values of `volume` on intervals, rays and balls (`Real.volume_ball`), and the dilation lemmas `Real.map_volume_mul_left` and `Real.volume_preimage_mul_right`.

Common errors of a learner:

- Writing `volume (Icc a b) = b - a`. The value is in `ℝ≥0∞`; the right side is `ENNReal.ofReal (b - a)`, or use `volume.real`.
- Using `Set.Countable.measure_zero` for a measure with atoms, such as a Dirac measure.
- Believing that a null set is small in the sense of topology. The Cantor set is null and uncountable, and Exercise 6 gives a nowhere dense set of positive measure.

### Exercises

1. (A) Compute $\lambda(\{x \in [0, 2] : x^2 \in \mathbb{Q}\})$.
2. (A) Let $F(x) = x + \lfloor x \rfloor$. Compute $\mu_F(\{0\})$, $\mu_F((0, 1))$ and $\mu_F([0, 1])$, and show that $\mu_F = \lambda + \sum_{n \in \mathbb{Z}} \delta_n$.
3. (A) Show that a Borel set of positive Lebesgue measure is uncountable.
4. (B) Let $F(x) = x^3$. Show that $\mu_F(A) = \lambda(F(A))$ for every Borel set $A$. Hint: both sides are measures that agree on half-open intervals.
5. (B) Show that $\lambda(A) = \sup\{\lambda(K) : K \subseteq A \text{ compact}\}$ for every Borel set $A$. Hint: for $A \subseteq [-n, n]$ apply Theorem 5 to $[-n, n] \setminus A$ and take $K = [-n, n] \setminus U$; for general $A$ use continuity from below.
6. (B) Let $q_0, q_1, \dots$ enumerate $\mathbb{Q}$ and $U = \bigcup_n (q_n - 2^{-n-3}, q_n + 2^{-n-3})$. Show that $[0, 1] \setminus U$ is closed, nowhere dense, and of measure at least $1/2$.
7. (C) (Steinhaus) Let $\lambda(A) > 0$. Show that $A - A$ contains an interval $(-\delta, \delta)$. Hint: choose a compact $K \subseteq A$ with $\lambda(K) > 0$ and an open $U \supseteq K$ with $\lambda(U) < 2\lambda(K)$; for small $|t|$, $K + t \subseteq U$, so $K$ and $K + t$ meet.

### Notes and history

Borel described the measure of the Borel sets in his *Leçons sur la théorie des fonctions* (1898). Lebesgue defined the outer measure by countable covers with intervals, the measurable sets and the integral in his thesis (1902). Stieltjes introduced the integral with respect to an increasing function in 1894, and Radon gave the measure form in 1913. Carathéodory's criterion dates from 1914. In Mathlib, `Mathlib.MeasureTheory.Measure.Stieltjes` has the authors Johannes Hölzl, Yury Kudryashov and Sébastien Gouëzel, `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` the authors Johannes Hölzl, Sébastien Gouëzel and Yury Kudryashov, and `Mathlib.MeasureTheory.Measure.Regular` the authors Sébastien Gouëzel, Floris van Doorn and Yury Kudryashov.

### Reference

<?reference?>
