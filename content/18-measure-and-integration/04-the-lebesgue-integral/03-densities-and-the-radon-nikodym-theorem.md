---
title: Densities and the Radon-Nikodym theorem
kind: theory
modules:
  - Mathlib.MeasureTheory.Measure.WithDensity
  - Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
  - Mathlib.MeasureTheory.Measure.MutuallySingular
  - Mathlib.MeasureTheory.Measure.Decomposition.Hahn
  - Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
  - Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
explains:
  E3: [MeasureTheory.Measure.withDensity, MeasureTheory.Measure.AbsolutelyContinuous, MeasureTheory.Measure.MutuallySingular, MeasureTheory.Measure.HaveLebesgueDecomposition, MeasureTheory.Measure.rnDeriv, MeasureTheory.Measure.withDensity_rnDeriv_eq]
  E2: [MeasureTheory.withDensity_apply, MeasureTheory.lintegral_withDensity_eq_lintegral_mul, MeasureTheory.withDensity_absolutelyContinuous, MeasureTheory.hahn_decomposition, MeasureTheory.Measure.exists_positive_of_not_mutuallySingular, MeasureTheory.Measure.singularPart, MeasureTheory.Measure.haveLebesgueDecomposition_add, MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite, MeasureTheory.Measure.rnDeriv_withDensity, MeasureTheory.Measure.setLIntegral_rnDeriv]
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

## Densities and the Radon-Nikodym theorem

### Overview

A measurable $f \ge 0$ turns a measure $\mu$ into a new measure $f \mu$ with $(f \mu)(A) = \int_A f \, d\mu$. It vanishes on $\mu$-null sets. The theorem of Radon and Nikodym says that for $\sigma$-finite measures this property gives a density. This section defines densities, absolute continuity and mutual singularity, proves the Hahn decomposition for two finite measures, and uses it to prove the Lebesgue decomposition and the Radon-Nikodym theorem.

### Definitions

**Definition (Measure with density).** For measurable $f : X \to [0, \infty]$, the measure $f \mu$ is $(f \mu)(A) = \int_A f \, d\mu$ for measurable $A$.

This is a measure: $(f\mu)(\emptyset) = 0$, and for disjoint $A_k$ the function $f \mathbf{1}_{\bigcup A_k}$ is the series $\sum_k f \mathbf{1}_{A_k}$, so the corollary on series of Section 2 gives countable additivity.

**Definition (Absolute continuity).** A measure $\nu$ is *absolutely continuous* with respect to $\mu$, written $\nu \ll \mu$, if $\mu(A) = 0$ implies $\nu(A) = 0$.

**Definition (Mutual singularity).** Measures $\mu$ and $\nu$ are *mutually singular*, written $\mu \perp \nu$, if there is a measurable $S$ with $\mu(S) = 0$ and $\nu(X \setminus S) = 0$.

A density measure is absolutely continuous: if $\mu(A) = 0$, then $f \mathbf{1}_A = 0$ almost everywhere, so $(f \mu)(A) = 0$ by Section 1.

::: mathlib
`MeasureTheory.Measure.withDensity` · `Mathlib.MeasureTheory.Measure.WithDensity`

`μ.withDensity f` is defined for every `f : α → ℝ≥0∞`. On measurable sets it satisfies `withDensity_apply`: `μ.withDensity f s = ∫⁻ a in s, f a ∂μ`. The lemma `withDensity_absolutelyContinuous` gives `μ.withDensity f ≪ μ`.

<?decl MeasureTheory.Measure.withDensity?>
<?decl MeasureTheory.withDensity_apply?>
<?decl MeasureTheory.withDensity_absolutelyContinuous?>
:::

::: mathlib
`MeasureTheory.Measure.AbsolutelyContinuous` · `Mathlib.MeasureTheory.Measure.AbsolutelyContinuous`

`μ ≪ ν` is `∀ ⦃s⦄, ν s = 0 → μ s = 0`, over all sets. `AbsolutelyContinuous.mk` asks for measurable sets only.

<?decl MeasureTheory.Measure.AbsolutelyContinuous?>
:::

::: mathlib
`MeasureTheory.Measure.MutuallySingular` · `Mathlib.MeasureTheory.Measure.MutuallySingular`

`μ ⟂ₘ ν` is `∃ s, MeasurableSet s ∧ μ s = 0 ∧ ν sᶜ = 0`, the definition above.

<?decl MeasureTheory.Measure.MutuallySingular?>
:::

### Theorems and proofs

**Proposition (Integration against a density).** For measurable $f, g \ge 0$, $\int g \, d(f \mu) = \int f g \, d\mu$.

*Proof.* For $g = c \mathbf{1}_A$ with $A$ measurable, both sides are $c \int_A f \, d\mu$. Both sides are additive in $g$ by Section 2, so the formula holds for simple $g$. For general $g$, take simple $g_n$ increasing to $g$. Then $f g_n$ increases to $f g$, and monotone convergence on both sides gives the formula. $\square$

::: mathlib
`MeasureTheory.lintegral_withDensity_eq_lintegral_mul` · `Mathlib.MeasureTheory.Measure.WithDensity`

`∫⁻ a, g a ∂μ.withDensity f = ∫⁻ a, (f * g) a ∂μ` for measurable `f` and `g`.

<?decl MeasureTheory.lintegral_withDensity_eq_lintegral_mul?>
:::

**Theorem (Hahn decomposition).** Let $\mu, \nu$ be finite measures. There is a measurable $P$ with $\nu(T) \le \mu(T)$ for all measurable $T \subseteq P$ and $\mu(T) \le \nu(T)$ for all measurable $T \subseteq X \setminus P$.

*Proof.* Put $d(A) = \mu(A) - \nu(A)$, a real number. It is additive on disjoint sets and continuous along increasing and decreasing sequences, because $\mu$ and $\nu$ are finite (Chapter 2). Let $c = \sup_A d(A)$. Then $0 \le c \le \mu(X)$.

For measurable $A, B$, $d(A \cap B) + d(A \cup B) = d(A) + d(B)$ and $d(A \cup B) \le c$, so
$$d(A \cap B) \ge d(A) + d(B) - c.$$
Choose $A_k$ with $d(A_k) \ge c - 2^{-k}$. For $n \le m$ let $D_{n,m} = A_n \cap \dots \cap A_m$. Induction on $m$ with the inequality gives $d(D_{n,m}) \ge c - \sum_{k=n}^{m} 2^{-k} \ge c - 2^{1-n}$. The sets $D_{n,m}$ decrease in $m$ to $C_n = \bigcap_{k \ge n} A_k$, so $d(C_n) \ge c - 2^{1-n}$. The $C_n$ increase to $P = \bigcup_n C_n$, so $d(P) \ge c$, and $d(P) = c$.

Let $T \subseteq P$ be measurable. If $d(T) < 0$, then $d(P \setminus T) = c - d(T) > c$, which is impossible. So $\nu(T) \le \mu(T)$. Let $T \subseteq X \setminus P$ be measurable. If $d(T) > 0$, then $d(P \cup T) = c + d(T) > c$. So $\mu(T) \le \nu(T)$. $\square$

::: mathlib
`MeasureTheory.hahn_decomposition` · `Mathlib.MeasureTheory.Measure.Decomposition.Hahn`

For `[IsFiniteMeasure μ] [IsFiniteMeasure ν]` it gives `∃ s, MeasurableSet s ∧ (∀ t, MeasurableSet t → t ⊆ s → ν t ≤ μ t) ∧ (∀ t, MeasurableSet t → t ⊆ sᶜ → μ t ≤ ν t)`.

<?decl MeasureTheory.hahn_decomposition?>
:::

**Lemma (A positive piece).** Let $\mu, \nu$ be finite and not mutually singular. There are $\varepsilon > 0$ and a measurable $E$ with $\nu(E) > 0$ and $\varepsilon \nu(A \cap E) \le \mu(A \cap E)$ for all measurable $A$.

*Proof.* For each $n \ge 1$, take a Hahn set $P_n$ for $\mu$ and $\frac{1}{n} \nu$. Let $N = \bigcap_n (X \setminus P_n)$. Since $N \subseteq X \setminus P_n$, $\mu(N) \le \frac{1}{n} \nu(N)$ for every $n$, so $\mu(N) = 0$. If $\nu(P_n) = 0$ for all $n$, then $\nu(X \setminus N) = \nu(\bigcup_n P_n) = 0$, and $\mu \perp \nu$. So $\nu(P_n) > 0$ for some $n$. Put $E = P_n$ and $\varepsilon = 1/n$. $\square$

::: mathlib
`MeasureTheory.Measure.exists_positive_of_not_mutuallySingular` · `Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue`

The lemma, with `ε : ℝ≥0`.

<?decl MeasureTheory.Measure.exists_positive_of_not_mutuallySingular?>
:::

**Theorem (Lebesgue decomposition).** Let $\mu, \nu$ be finite. There are a measurable $\xi \ge 0$ and a measure $\mu_s \perp \nu$ with $\mu = \mu_s + \xi \nu$.

*Proof.* Let $\mathcal{F}$ be the set of measurable $f \ge 0$ with $\int_A f \, d\nu \le \mu(A)$ for all measurable $A$. It contains $0$. It is closed under maximum: for $f, g \in \mathcal{F}$ and $B = \{f \ge g\}$,
$$\int_A \max(f, g) \, d\nu = \int_{A \cap B} f \, d\nu + \int_{A \setminus B} g \, d\nu \le \mu(A \cap B) + \mu(A \setminus B) = \mu(A).$$
Let $M = \sup_{f \in \mathcal{F}} \int f \, d\nu \le \mu(X) < \infty$. Choose $f_n \in \mathcal{F}$ with $\int f_n \, d\nu \to M$, and put $g_n = \max(f_1, \dots, f_n) \in \mathcal{F}$. The $g_n$ increase to a measurable $\xi$. Monotone convergence gives $\int_A \xi \, d\nu = \sup_n \int_A g_n \, d\nu \le \mu(A)$, so $\xi \in \mathcal{F}$, and $\int \xi \, d\nu = M$.

Put $\mu_s(A) = \mu(A) - \int_A \xi \, d\nu$. It is nonnegative because $\xi \in \mathcal{F}$, and countably additive as a difference of two finite measures. Suppose that $\mu_s$ and $\nu$ are not mutually singular. The lemma gives $\varepsilon > 0$ and $E$ with $\nu(E) > 0$ and $\varepsilon \nu(A \cap E) \le \mu_s(A \cap E)$. For measurable $A$,
$$\int_A (\xi + \varepsilon \mathbf{1}_E) \, d\nu = \int_A \xi \, d\nu + \varepsilon \nu(A \cap E) \le \int_A \xi \, d\nu + \mu_s(A) = \mu(A).$$
So $\xi + \varepsilon \mathbf{1}_E \in \mathcal{F}$, with integral $M + \varepsilon \nu(E) > M$. This contradicts the choice of $M$. $\square$

**Theorem (Radon-Nikodym).** Let $\mu, \nu$ be $\sigma$-finite with $\mu \ll \nu$. There is a measurable $f \ge 0$ with $\mu = f \nu$. Any two such $f$ agree $\nu$-almost everywhere.

*Proof.* Let first $\mu, \nu$ be finite, and take the Lebesgue decomposition. Since $\mu_s \le \mu$ and $\mu \ll \nu$, also $\mu_s \ll \nu$. Take $S$ with $\mu_s(S) = 0$ and $\nu(X \setminus S) = 0$. Then $\mu_s(X \setminus S) = 0$, so $\mu_s = 0$ and $\mu = \xi \nu$.

In the $\sigma$-finite case, intersect the two sequences of sets of finite measure and make them disjoint. This gives disjoint measurable $X_k$ with union $X$ and $\mu(X_k), \nu(X_k) < \infty$. The finite case gives $f_k$ with $\mu|_{X_k} = f_k \, \nu|_{X_k}$. Put $f = \sum_k f_k \mathbf{1}_{X_k}$. For measurable $A$, the corollary on series gives $\int_A f \, d\nu = \sum_k \int_{A \cap X_k} f_k \, d\nu = \sum_k \mu(A \cap X_k) = \mu(A)$.

For uniqueness, let $f \nu = g \nu$, and let first $\nu$ be finite with $\int f \, d\nu < \infty$. Put $A = \{f > g\}$. Then $\int_A f \, d\nu = \int_A g \, d\nu < \infty$, and the subtraction lemma of Section 2 gives $\int_A (f - g) \, d\nu = 0$. Since $f - g > 0$ on $A$, Section 1 gives $\nu(A) = 0$. Symmetry gives $f = g$ almost everywhere. In general, $\int_{X_k} f \, d\nu = \mu(X_k) < \infty$, so $f$ and $g$ are finite almost everywhere by the Markov inequality. Apply the finite case on the sets $X_k \cap \{f \le n\} \cap \{g \le n\}$. $\square$

::: mathlib
`MeasureTheory.Measure.HaveLebesgueDecomposition` · `Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue`

`μ.HaveLebesgueDecomposition ν` is a class: there is a pair `p` with `Measurable p.2`, `p.1 ⟂ₘ ν` and `μ = p.1 + ν.withDensity p.2`. The instance `haveLebesgueDecomposition_of_sigmaFinite` needs `[SFinite μ] [SigmaFinite ν]`.

<?decl MeasureTheory.Measure.HaveLebesgueDecomposition?>
<?decl MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite?>
:::

::: mathlib
`MeasureTheory.Measure.rnDeriv` · `Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue`

`μ.rnDeriv ν` and `μ.singularPart ν` are the two parts chosen from the class, and `haveLebesgueDecomposition_add` gives `μ = μ.singularPart ν + ν.withDensity (μ.rnDeriv ν)`. Without the class, both are $0$, a junk value. Uniqueness is `rnDeriv_withDensity`: for `[SigmaFinite ν]` and measurable `f`, `(ν.withDensity f).rnDeriv ν =ᵐ[ν] f`.

<?decl MeasureTheory.Measure.rnDeriv?>
<?decl MeasureTheory.Measure.singularPart?>
<?decl MeasureTheory.Measure.haveLebesgueDecomposition_add?>
<?decl MeasureTheory.Measure.rnDeriv_withDensity?>
:::

::: mathlib
`MeasureTheory.Measure.withDensity_rnDeriv_eq` · `Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym`

The theorem of Radon and Nikodym: `μ ≪ ν → ν.withDensity (μ.rnDeriv ν) = μ`, under `[μ.HaveLebesgueDecomposition ν]`. The form on sets is `setLIntegral_rnDeriv`: `∫⁻ x in s, μ.rnDeriv ν x ∂ν = μ s`, with `[SFinite ν]` in addition.

<?decl MeasureTheory.Measure.withDensity_rnDeriv_eq?>
<?decl MeasureTheory.Measure.setLIntegral_rnDeriv?>
:::

### Examples

**Example (Discrete measures).** Let $X$ be countable with the counting measure $c$, and let $\mu$ be any measure on all subsets. Then $\mu \ll c$, since only $\emptyset$ is $c$-null. The density is $f(x) = \mu(\{x\})$: by countable additivity, $\mu(A) = \sum_{x \in A} f(x) = \int_A f \, dc$.

**Example (A decomposition).** On $\mathbb{R}$ let $\mu = \lambda|_{[0, 1]} + 3 \delta_2$, with $\lambda$ Lebesgue measure. Relative to $\lambda$, $\xi = \mathbf{1}_{[0, 1]}$ and $\mu_s = 3 \delta_2$. The set $S = \mathbb{R} \setminus \{2\}$ shows $\mu_s \perp \lambda$: $\mu_s(S) = 0$ and $\lambda(\{2\}) = 0$.

**Counterexample ($\sigma$-finiteness is needed).** Let $c$ be the counting measure on the Borel sets of $[0, 1]$. Then $\lambda \ll c$, since only $\emptyset$ is $c$-null. Suppose $\lambda = f c$. Then $0 = \lambda(\{x\}) = \int_{\{x\}} f \, dc = f(x)$ for every $x$, so $f = 0$ and $\lambda = 0$, which is false. The measure $c$ is not $\sigma$-finite. In Mathlib the instance does not apply, and `λ.rnDeriv c` is the junk value $0$.

### The library around it

The file `Decomposition.RadonNikodym` also proves the chain rule for derivatives. Signed and complex measures have their own decomposition in the folder `MeasureTheory/VectorMeasure`.

Common errors of a learner:

- Using `μ.rnDeriv ν` without the instance `HaveLebesgueDecomposition`. Without it the derivative is $0$.
- Expecting equality of densities at every point. A density is unique only almost everywhere.
- Confusing $\mu \ll \nu$ with $\nu \ll \mu$. The density of $\mu$ with respect to $\nu$ needs $\mu \ll \nu$.

### Exercises

1. (A) Show that $\ll$ is reflexive and transitive.
2. (A) Show that $\mu \ll \nu$ and $\mu \perp \nu$ imply $\mu = 0$.
3. (B) Show that $\frac{d(f\mu)}{d\mu} = f$ almost everywhere for $\sigma$-finite $\mu$. Hint: the uniqueness part of the theorem.
4. (B) Let $\nu$ be finite. Show that $\mu \ll \nu$ for a finite $\mu$ if and only if for every $\varepsilon > 0$ there is $\delta > 0$ with $\nu(A) < \delta \Rightarrow \mu(A) < \varepsilon$. Hint: for the direct part, use the density and Exercise 7 of Section 2.
5. (B) Show that the Lebesgue decomposition of finite measures is unique. Hint: compare $\mu_s - \mu_s'$ on the union of the two singular sets.
6. (C) Let $\mu \ll \nu \ll \rho$ be finite. Show that $\frac{d\mu}{d\rho} = \frac{d\mu}{d\nu} \frac{d\nu}{d\rho}$ almost everywhere. Hint: the proposition on integration against a density.

### Notes and history

Radon proved the theorem in 1913 for measures on $\mathbb{R}^n$, and Nikodym proved the general form in 1930. Another proof, due to von Neumann, uses the representation of a functional on a Hilbert space. In Mathlib, the file on the Lebesgue decomposition has Kexing Ying as author, the file on the Radon-Nikodym theorem has Kexing Ying and Rémy Degenne, and the file `WithDensity` has Mario Carneiro and Johannes Hölzl.

### Reference

<?reference?>
