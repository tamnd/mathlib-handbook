---
title: Null sets and almost everywhere
kind: theory
modules:
  - Mathlib.MeasureTheory.OuterMeasure.AE
  - Mathlib.MeasureTheory.Measure.NullMeasurable
  - Mathlib.MeasureTheory.Measure.AEMeasurable
  - Mathlib.MeasureTheory.Measure.Map
  - Mathlib.MeasureTheory.Measure.Restrict
explains:
  E3: [MeasureTheory.ae, MeasureTheory.NullMeasurableSet, MeasureTheory.Measure.completion, AEMeasurable, MeasureTheory.ext_of_generate_finite, MeasureTheory.Measure.ext_of_generateFrom_of_iUnion, MeasureTheory.Measure.map, MeasureTheory.Measure.restrict]
  E2: [MeasureTheory.ae_iff, MeasureTheory.ae_all_iff, MeasureTheory.measure_congr, MeasureTheory.NullMeasurableSet.of_null, MeasureTheory.NullMeasurableSet.exists_measurable_superset_ae_eq, MeasureTheory.Measure.IsComplete, AEMeasurable.mk, MeasureTheory.Measure.map_apply, MeasureTheory.Measure.map_map, MeasureTheory.Measure.restrict_apply, MeasureTheory.ae_restrict_iff']
  E1: auto
families: []
requires: [V03, V04, V13, V18.C01]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Null sets and almost everywhere

### Overview

A set of measure $0$ is invisible to the integral, so measure theory states most results up to null sets: two functions are equal *almost everywhere* if they differ only on a null set, and a sequence converges almost everywhere if it converges outside a null set. Mathlib writes them with the filter `ae μ` of Volume 13.

This section defines null sets and the filter `ae μ`, the null measurable sets and the completion of a measure, and the almost everywhere measurable functions. It proves the uniqueness theorem: two measures that agree on a π-system that generates the σ-algebra are equal, if they are finite or σ-finite on the π-system. It ends with the image and the restriction of a measure.

### Definitions

**Definition (null set, almost everywhere).** Let $\mu$ be a measure on $(X, \Sigma)$. A set $N \subseteq X$ is *null* if $\mu(N) = 0$. Here $\mu(N)$ is the outer measure of Section 2 when $N \notin \Sigma$. A property $P$ of points holds *almost everywhere* ($\mu$-a.e.) if $\{x : \neg P(x)\}$ is null. Two functions are equal a.e., $f =_{\text{a.e.}} g$, if $\{f \ne g\}$ is null.

The sets $A$ with $\mu(A^c) = 0$ form a filter on $X$: $X$ is in it, it is closed under supersets by monotonicity, and under finite intersections because $(A \cap B)^c = A^c \cup B^c$ is null by subadditivity. It is even closed under countable intersections, by countable subadditivity.

::: mathlib
`MeasureTheory.ae` · `Mathlib.MeasureTheory.OuterMeasure.AE`

`ae μ : Filter α`, for a measure or an outer measure, with an instance `CountableInterFilter`. The notations are `∀ᵐ x ∂μ, p x`, `∃ᵐ x ∂μ, p x`, `f =ᵐ[μ] g` and `f ≤ᵐ[μ] g`. By `ae_iff`, `(∀ᵐ a ∂μ, p a) ↔ μ {a | ¬p a} = 0`, with no measurability of the set. For `[Countable ι]`, `ae_all_iff` exchanges `∀ᵐ` and `∀ i`; it fails for uncountable `ι`, since for the Lebesgue measure each point is null.

<?decl MeasureTheory.ae?>
<?decl MeasureTheory.ae_iff?>
<?decl MeasureTheory.ae_all_iff?>
:::

**Definition (null measurable set, completion).** A set $A \subseteq X$ is *null measurable* if $A =_{\text{a.e.}} B$ for some $B \in \Sigma$, that is, if the symmetric difference $A \mathbin{\triangle} B$ is null. The measure $\mu$ is *complete* if each null set is in $\Sigma$. The *completion* $\bar\mu$ of $\mu$ is the restriction of $\mu$ (as an outer measure) to the null measurable sets.

::: mathlib
`MeasureTheory.NullMeasurableSet` · `Mathlib.MeasureTheory.Measure.NullMeasurable`

`NullMeasurableSet s μ` means that `s` is measurable for `NullMeasurableSpace α μ`, a copy of `α` whose measurable sets are a.e. equal to measurable sets. Lemmas such as `measure_iUnion₀` and `measure_sdiff` ask only for it.

<?decl MeasureTheory.NullMeasurableSet?>
:::

::: mathlib
`MeasureTheory.Measure.completion` · `Mathlib.MeasureTheory.Measure.NullMeasurable`

`μ.completion : Measure (NullMeasurableSpace α μ)` has the same outer measure as `μ`. It satisfies the class `Measure.IsComplete`, whose field says `μ s = 0 → MeasurableSet s`. Mathlib seldom uses the completion: `NullMeasurableSet` and `AEMeasurable` do the same work on the original σ-algebra.

<?decl MeasureTheory.Measure.completion?>
<?decl MeasureTheory.Measure.IsComplete?>
:::

**Definition (a.e. measurable function).** A map $f : X \to Y$ is *a.e. measurable* if $f =_{\text{a.e.}} g$ for a measurable $g$.

::: mathlib
`AEMeasurable` · `Mathlib.MeasureTheory.Measure.MeasureSpaceDef`

`AEMeasurable f μ` is `∃ g, Measurable g ∧ f =ᵐ[μ] g`, in the root namespace. `hf.mk f` chooses `g`, with `AEMeasurable.measurable_mk` and `AEMeasurable.ae_eq_mk`; proofs often replace `f` by it.

<?decl AEMeasurable?>
<?decl AEMeasurable.mk?>
:::

**Definition (image and restriction).** Let $f : X \to Y$ be measurable. The *image measure* (push forward) $f_* \mu$ on $Y$ is $f_*\mu(B) = \mu(f^{-1}(B))$. For $S \in \Sigma$ the *restriction* $\mu|_S$ is $\mu|_S(A) = \mu(A \cap S)$.

Both are measures: preimages and intersections with $S$ preserve disjoint unions.

::: mathlib
`MeasureTheory.Measure.map` · `Mathlib.MeasureTheory.Measure.Map`

`μ.map f` is defined for each `f`. For an a.e. measurable `f` it is the image by `hf.mk f`; otherwise it is a junk value, `0` when `μ = 0` and a Dirac mass otherwise. The value is `map_apply`, `μ.map f s = μ (f ⁻¹' s)` for measurable `f` and `s`, and `map_map` gives `(μ.map f).map g = μ.map (g ∘ f)`.

<?decl MeasureTheory.Measure.map?>
<?decl MeasureTheory.Measure.map_apply?>
<?decl MeasureTheory.Measure.map_map?>
:::

::: mathlib
`MeasureTheory.Measure.restrict` · `Mathlib.MeasureTheory.Measure.Restrict`

`μ.restrict s` is defined for every set `s`, and `∫ x in s, f x ∂μ` of Chapter 4 integrates for it. `restrict_apply` gives `μ.restrict s t = μ (t ∩ s)` for a measurable `t`; `restrict_apply'` asks instead that `s` be measurable.

<?decl MeasureTheory.Measure.restrict?>
<?decl MeasureTheory.Measure.restrict_apply?>
:::

### Theorems and proofs

**Proposition (null sets).** A subset of a null set is null, and a countable union of null sets is null. If $A =_{\text{a.e.}} B$, then $\mu(A) = \mu(B)$.

*Proof.* The first two claims are monotonicity and countable subadditivity. If $N = A \mathbin{\triangle} B$ is null, then $A \subseteq B \cup N$, so $\mu(A) \le \mu(B) + \mu(N) = \mu(B)$, and by symmetry $\mu(B) \le \mu(A)$. $\square$

::: mathlib
`MeasureTheory.measure_congr` · `Mathlib.MeasureTheory.OuterMeasure.AE`

From `H : s =ᵐ[μ] t` it gives `μ s = μ t`.

<?decl MeasureTheory.measure_congr?>
:::

**Proposition (completion).** The null measurable sets form a σ-algebra $\bar\Sigma \supseteq \Sigma$ that contains all null sets, and the outer measure of $\mu$ is countably additive on $\bar\Sigma$. So $\bar\mu$ is a complete measure that extends $\mu$.

*Proof.* Each $B \in \Sigma$ is null measurable, and each null set $N$ satisfies $N =_{\text{a.e.}} \emptyset$. If $A =_{\text{a.e.}} B$, then $A^c =_{\text{a.e.}} B^c$, since $A^c \mathbin{\triangle} B^c = A \mathbin{\triangle} B$. If $A_n =_{\text{a.e.}} B_n$ with $B_n \in \Sigma$, then $\big(\bigcup_n A_n\big) \mathbin{\triangle} \big(\bigcup_n B_n\big) \subseteq \bigcup_n (A_n \mathbin{\triangle} B_n)$, a countable union of null sets. So $\bar\Sigma$ is a σ-algebra. Let $(A_n)$ be pairwise disjoint in $\bar\Sigma$ with $A_n =_{\text{a.e.}} B_n$. Put $B_n' = B_n \setminus \bigcup_{k < n} B_k$; these are disjoint members of $\Sigma$, and $B_n' =_{\text{a.e.}} A_n$ because $B_n \cap B_k$ is a.e. equal to $A_n \cap A_k = \emptyset$. By the previous proposition, $\mu\big(\bigcup_n A_n\big) = \mu\big(\bigcup_n B_n'\big) = \sum_n \mu(B_n') = \sum_n \mu(A_n)$. A set of $\bar\mu$-measure $0$ is null, so it is in $\bar\Sigma$. $\square$

::: mathlib
`MeasureTheory.NullMeasurableSet.of_null` · `Mathlib.MeasureTheory.Measure.NullMeasurable`

From `μ s = 0` it gives `NullMeasurableSet s μ`. A null measurable `s` has a measurable `t ⊇ s` with `t =ᵐ[μ] s`, `exists_measurable_superset_ae_eq`.

<?decl MeasureTheory.NullMeasurableSet.of_null?>
<?decl MeasureTheory.NullMeasurableSet.exists_measurable_superset_ae_eq?>
:::

**Theorem (uniqueness of finite measures).** Let $\Sigma = \sigma(\mathcal{C})$ with $\mathcal{C}$ a π-system, and let $\mu, \nu$ be finite measures on $\Sigma$ with $\mu(A) = \nu(A)$ for $A \in \mathcal{C}$ and $\mu(X) = \nu(X)$. Then $\mu = \nu$.

*Proof.* Let $\mathcal{D} = \{A \in \Sigma : \mu(A) = \nu(A)\}$. It contains $\emptyset$ and, by hypothesis, $\mathcal{C}$. If $A \in \mathcal{D}$, then $\mu(A^c) = \mu(X) - \mu(A) = \nu(X) - \nu(A) = \nu(A^c)$, where the finiteness makes the subtraction correct. If $(A_n)$ are pairwise disjoint in $\mathcal{D}$, then $\mu\big(\bigcup_n A_n\big) = \sum_n \mu(A_n) = \sum_n \nu(A_n) = \nu\big(\bigcup_n A_n\big)$. So $\mathcal{D}$ is a Dynkin system that contains $\mathcal{C}$, and by the π-λ theorem it contains $\sigma(\mathcal{C}) = \Sigma$. $\square$

::: mathlib
`MeasureTheory.ext_of_generate_finite` · `Mathlib.MeasureTheory.Measure.Typeclasses.Finite`

The theorem, with `hA : m0 = generateFrom C`, `hC : IsPiSystem C`, `[IsFiniteMeasure μ]`, agreement on `C` and `μ univ = ν univ`.

<?decl MeasureTheory.ext_of_generate_finite?>
:::

**Theorem (uniqueness of σ-finite measures).** Let $\Sigma = \sigma(\mathcal{C})$ with $\mathcal{C}$ a π-system, and let $B_0, B_1, \dots \in \mathcal{C}$ with $\bigcup_n B_n = X$ and $\mu(B_n) < \infty$ for each $n$. If $\mu(A) = \nu(A)$ for each $A \in \mathcal{C}$, then $\mu = \nu$.

*Proof.* Fix $n$, and let $\mu_n(A) = \mu(A \cap B_n)$ and $\nu_n(A) = \nu(A \cap B_n)$. These are measures, with $\mu_n(X) = \mu(B_n) = \nu(B_n) = \nu_n(X) < \infty$. For $A \in \mathcal{C}$, the set $A \cap B_n$ is in $\mathcal{C}$ or empty, so $\mu_n(A) = \nu_n(A)$. By the finite theorem, $\mu_n = \nu_n$. Now put $D_n = B_n \setminus (B_0 \cup \dots \cup B_{n-1})$, pairwise disjoint sets with union $X$ and $D_n \subseteq B_n$. For $A \in \Sigma$,
$$\mu(A) = \sum_n \mu(A \cap D_n) = \sum_n \mu_n(A \cap D_n) = \sum_n \nu_n(A \cap D_n) = \nu(A). \quad \square$$

::: mathlib
`MeasureTheory.Measure.ext_of_generateFrom_of_iUnion` · `Mathlib.MeasureTheory.Measure.Restrict`

The theorem, with `B : ℕ → Set α` in `C`, `⋃ i, B i = univ` and `μ (B i) ≠ ∞`. Chapter 3 applies it with the intervals to the Lebesgue measure.

<?decl MeasureTheory.Measure.ext_of_generateFrom_of_iUnion?>
:::

**Proposition (a.e. on a restriction).** Let $S \in \Sigma$ and let $P$ be a property of points. Then $P$ holds $\mu|_S$-a.e. if and only if $\mu$-a.e. point $x$ satisfies $x \in S \Rightarrow P(x)$.

*Proof.* By the definition of the restriction, with $S$ measurable and any set $N = \{x : \neg P(x)\}$, $\mu|_S(N) = \mu(N \cap S)$, and $N \cap S$ is the set of the points where the implication fails. $\square$

::: mathlib
`MeasureTheory.ae_restrict_iff'` · `Mathlib.MeasureTheory.Measure.Restrict`

The proposition for `hs : MeasurableSet s`.

<?decl MeasureTheory.ae_restrict_iff'?>
:::

### Examples

**Example (Dirac and counting measures).** For the Dirac measure $\delta_a$ with $\{a\}$ measurable, a set is null if and only if it does not contain $a$, so a property holds $\delta_a$-a.e. if and only if it holds at $a$; Mathlib has this as `MeasureTheory.ae_dirac_iff`. For the counting measure only $\emptyset$ is null, so a.e. means everywhere. For the Lebesgue measure of Chapter 3 each countable set is null, so $\mathbf{1}_{\mathbb{Q}} =_{\text{a.e.}} 0$. The image of $\delta_a$ under a measurable $f$ is $\delta_{f(a)}$, since $\delta_a(f^{-1}(B)) = 1$ if and only if $f(a) \in B$.

**Counterexample (the finiteness hypothesis is necessary).** On $\mathbb{N}$ let $\mathcal{C}$ be the family of the tails $T_n = \{n, n + 1, \dots\}$, a π-system with $T_m \cap T_n = T_{\max(m, n)}$. It generates $\mathcal{P}(\mathbb{N})$, since $\{n\} = T_n \setminus T_{n+1}$. Let $\mu = \#$ and $\nu = 2 \#$. Then $\mu(T_n) = \nu(T_n) = \infty$ for each $n$, and $T_0 = \mathbb{N}$, but $\mu(\{0\}) = 1 \ne 2 = \nu(\{0\})$. Both measures are σ-finite, but not on sets of $\mathcal{C}$.

### The library around it

Most a.e. lemmas are filter lemmas of Volume 13 under another name: `ae_of_all` is `Filter.Eventually.of_forall`, and `Filter.EventuallyEq.trans` composes a.e. equalities. Mathlib has `measure_mono_ae` for `s ≤ᵐ[μ] t`, `ae_eq_empty` for `s =ᵐ[μ] ∅ ↔ μ s = 0`, and `AEMeasurable.comp_measurable` for compositions. The restriction satisfies `restrict_restrict`, `restrict_univ` and `restrict_apply_univ`.

Common errors of a learner:

- Using `map_apply` without `Measurable f`. For a map that is not a.e. measurable, `μ.map f` is a junk value, and in this edition the junk value is a Dirac mass, not `0`.
- Mixing up `restrict_apply` and `restrict_apply'`: the first needs the set that is measured to be measurable, the second the set of the restriction.

### Exercises

1. (A) Show that if $f =_{\text{a.e.}} g$ and $g =_{\text{a.e.}} h$, then $f =_{\text{a.e.}} h$.
2. (A) Let $f_n \to f$ a.e. and $f_n \to g$ a.e., with values in a Hausdorff space. Show that $f =_{\text{a.e.}} g$.
3. (A) Show that $(\mu|_S)|_T = \mu|_{S \cap T}$ for $S, T \in \Sigma$.
4. (B) Show that two probability measures on $\mathbb{R}$ with the Borel sets are equal if they agree on the rays $(-\infty, q]$ with $q \in \mathbb{Q}$. Hint: Chapter 1, Section 1 and Section 2.
5. (B) Let $f : X \to Y$ be measurable and $\nu = f_*\mu$. Show that $g =_{\nu\text{-a.e.}} h$ implies $g \circ f =_{\mu\text{-a.e.}} h \circ f$ for measurable $g, h$. Hint: the set $\{g \ne h\}$ is measurable when $Y$ is a second countable Hausdorff space; otherwise use a measurable null superset.
6. (B) Show that a pointwise a.e. limit of a.e. measurable functions into $\mathbb{R}$ is a.e. measurable. Hint: replace the functions by measurable ones outside one null set.
7. (C) Let $\mu$ be σ-finite. Show that a set $A$ is null measurable if and only if $\mu^*(A \cap E) + \mu^*(E \setminus A) = \mu(E)$ for each $E \in \Sigma$ of finite measure. Hint: Section 2, Exercise 4.

### Notes and history

The use of a filter for it is a choice of Mathlib, which lets the library prove a.e. statements with the tactics and lemmas for filters. The Mathlib file `OuterMeasure.AE` has the authors Mario Carneiro and Yury Kudryashov, and `Measure.AEMeasurable` has the author Sébastien Gouëzel.

### Reference

<?reference?>
