---
title: Measure preserving maps
kind: theory
modules:
  - Mathlib.Dynamics.Ergodic.MeasurePreserving
  - Mathlib.Dynamics.Ergodic.RadonNikodym
  - Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
explains:
  E3: [MeasureTheory.MeasurePreserving, MeasureTheory.MeasurePreserving.measure_preimage, MeasureTheory.MeasurePreserving.comp, MeasureTheory.MeasurePreserving.iterate, MeasureTheory.MeasurePreserving.exists_mem_iterate_mem_of_measure_univ_lt_mul_measure, MeasureTheory.MeasurePreserving.exists_mem_iterate_mem, MeasureTheory.MeasurePreserving.singularPart, MeasureTheory.MeasurePreserving.withDensity_rnDeriv]
  E2: [MeasureTheory.MeasurePreserving.id, MeasureTheory.MeasurePreserving.symm, MeasureTheory.MeasurePreserving.of_semiconj, MeasureTheory.MeasurePreserving.restrict_preimage, MeasureTheory.MeasurePreserving.quasiMeasurePreserving, MeasureTheory.MeasurePreserving.preimage_null, MeasureTheory.MeasurePreserving.measure_symmDiff_preimage_iterate_le, MeasureTheory.MeasurePreserving.aeconst_preimage, MeasureTheory.MeasurePreserving.rnDeriv_comp_aeEq, MeasureTheory.QuasiMeasurePreserving.birkhoffSum_ae_eq_of_ae_eq, MeasureTheory.QuasiMeasurePreserving.birkhoffAverage_ae_eq_of_ae_eq]
  E1: auto
families: []
requires: [V18, V21.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Measure preserving maps

### Overview

Ergodic theory studies the iterates of a map $f : X \to X$ that keeps a measure $\mu$. The measure lets one count how often an orbit visits a set, and asks for statements that hold for almost every point. This section defines measure preserving maps, proves their closure properties, and proves the first recurrence result: a set of positive measure in a finite measure space meets one of its preimages. It ends with three classical examples: the rotation, the doubling map and the Gauss map of continued fractions.

### Definitions

Let $(X, \mathcal{A}, \mu)$ and $(Y, \mathcal{B}, \nu)$ be measure spaces.

**Definition (Measure preserving map).** A map $f : X \to Y$ is *measure preserving* from $\mu$ to $\nu$ if $f$ is measurable and the image measure $f_*\mu$, defined by $f_*\mu(B) = \mu(f^{-1}(B))$, equals $\nu$. So $\mu(f^{-1}(B)) = \nu(B)$ for every measurable $B$.

The definition uses preimages, not images. The image of a measurable set need not be measurable, and $\mu(f(A))$ can differ from $\mu(A)$: the doubling map below sends $[0, \tfrac12)$ onto $[0, 1)$.

**Definition (Quasi measure preserving map).** A measurable map $f$ is *quasi measure preserving* if $f_*\mu \ll \nu$, that is, $\nu(B) = 0$ implies $\mu(f^{-1}(B)) = 0$.

A measure preserving map is quasi measure preserving. When $Y = X$ and $\nu = \mu$, one says that $f$ preserves $\mu$, or that $\mu$ is $f$-invariant.

::: mathlib
`MeasureTheory.MeasurePreserving` · `Mathlib.Dynamics.Ergodic.MeasurePreserving`

`MeasurePreserving f μa μb` is a structure with the fields `measurable : Measurable f` and `map_eq : Measure.map f μa = μb`. The measures are `autoParam` arguments, so `MeasurePreserving f` alone means that `f` preserves `volume`. Quasi measure preservation is `MeasureTheory.Measure.QuasiMeasurePreserving`, with home in Volume 18, and `MeasurePreserving.quasiMeasurePreserving` is the implication.

<?decl MeasureTheory.MeasurePreserving?>
:::

### Theorems and proofs

**Proposition (Closure properties).** The identity preserves $\mu$. If $f$ is measure preserving from $\mu$ to $\nu$ and $g$ from $\nu$ to $\rho$, then $g \circ f$ is measure preserving from $\mu$ to $\rho$. If $f$ preserves $\mu$, then so does each iterate $f^n$. If $f$ is a measurable bijection with measurable inverse that is measure preserving from $\mu$ to $\nu$, then $f^{-1}$ is measure preserving from $\nu$ to $\mu$.

*Proof.* $(g \circ f)^{-1}(C) = f^{-1}(g^{-1}(C))$, so $\mu((g\circ f)^{-1}C) = \nu(g^{-1}C) = \rho(C)$. Iterates follow by induction. For the inverse, $\nu((f^{-1})^{-1}(A)) = \nu(f(A)) = \mu(f^{-1}(f(A))) = \mu(A)$. $\square$

For null measurable sets the equation $\mu(f^{-1}(B)) = \nu(B)$ still holds, since $B$ differs from a measurable set by a null set and $f^{-1}$ keeps null sets null.

**Theorem (Recurrence by pigeonhole).** Let $f$ preserve $\mu$, let $s$ be null measurable and $n \ge 1$ with $\mu(X) < n\,\mu(s)$. Then there are $x \in s$ and $0 < m < n$ with $f^m(x) \in s$.

*Proof.* Consider the $n$ sets $s, f^{-1}(s), \dots, f^{-(n-1)}(s)$. Each has measure $\mu(s)$. If they were pairwise almost disjoint, then the measure of their union would be $n\,\mu(s) > \mu(X)$, which is false. So there are $0 \le i < j < n$ with $\mu(f^{-i}(s) \cap f^{-j}(s)) > 0$. This set is $f^{-i}(s \cap f^{-(j-i)}(s))$, and $f^i$ preserves $\mu$, so $\mu(s \cap f^{-(j-i)}(s)) > 0$. A point $x$ of this set lies in $s$, and $f^{j-i}(x) \in s$ with $0 < j - i < n$. $\square$

**Corollary.** If $\mu$ is finite, $f$ preserves $\mu$ and $\mu(s) > 0$, then some $x \in s$ and some $m \ge 1$ satisfy $f^m(x) \in s$.

*Proof.* Since $\mu(X) < \infty$ and $\mu(s) > 0$, there is $n$ with $n\,\mu(s) > \mu(X)$. Apply the theorem. $\square$

This is the weak form of the recurrence theorem of Poincaré. Section 2 proves the strong form: almost every point of $s$ returns to $s$ infinitely often. Finiteness is needed: the translation $x \mapsto x + 1$ preserves Lebesgue measure on $\mathbb{R}$, and no point of $[0, 1)$ returns to $[0, 1)$.

**Proposition (Almost invariant sets).** If $f$ preserves $\mu$, then $\mu(s \,\triangle\, f^{-n}(s)) \le n\,\mu(s \,\triangle\, f^{-1}(s))$.

*Proof.* $s \,\triangle\, f^{-n}(s) \subseteq \bigcup_{k<n} \big(f^{-k}(s) \,\triangle\, f^{-(k+1)}(s)\big)$, a chain of symmetric differences. The $k$th set is $f^{-k}(s \,\triangle\, f^{-1}(s))$, of measure $\mu(s \,\triangle\, f^{-1}(s))$. $\square$

So a set with $f^{-1}(s) = s$ almost everywhere has $f^{-n}(s) = s$ almost everywhere for all $n$. Chapter 6 calls such sets invariant.

**Theorem (Lebesgue decomposition is invariant).** Let $\mu$ be finite and $\nu$ be $\sigma$-finite, and let $f$ preserve both. Write $\mu = \mu_s + \mu_a$ with $\mu_s \perp \nu$ and $\mu_a = \frac{d\mu}{d\nu}\,\nu \ll \nu$. Then $f$ preserves $\mu_s$ and $\mu_a$.

*Proof.* Volume 18, Chapter 4, proves that the decomposition is unique. Write the decomposition of $f_*\mu_s$ as $\sigma + \rho$ with $\sigma \perp \nu$ and $\rho \ll \nu$. Also $f_*\mu_a \ll \nu$: if $\nu(B) = 0$, then $\nu(f^{-1}B) = \nu(B) = 0$, so $\mu_a(f^{-1}B) = 0$. Then
$$\mu = f_*\mu = \sigma + (\rho + f_*\mu_a),$$
with $\sigma \perp \nu$ and $\rho + f_*\mu_a \ll \nu$. Uniqueness gives $\sigma = \mu_s$ and $\rho + f_*\mu_a = \mu_a$. Compare total masses: $\sigma(X) + \rho(X) = f_*\mu_s(X) = \mu_s(X) = \sigma(X)$, and all are finite, so $\rho(X) = 0$. Hence $f_*\mu_s = \mu_s$ and $f_*\mu_a = \mu_a$. $\square$

### Examples

**Example (Rotations and translations).** On the circle $\mathbb{T} = \mathbb{R}/\mathbb{Z}$ with Haar measure $\lambda$, the rotation $R_a(x) = x + a$ preserves $\lambda$, because $\lambda$ is invariant under translation. In the same way each translation of a group preserves a left invariant Haar measure.

**Example (The doubling map).** Let $D(x) = 2x \bmod 1$ on $[0, 1)$ with Lebesgue measure. For $0 \le a < b \le 1$,
$$D^{-1}[a, b) = \left[\tfrac{a}{2}, \tfrac{b}{2}\right) \cup \left[\tfrac{a+1}{2}, \tfrac{b+1}{2}\right),$$
of measure $b - a$. So $D_*\lambda$ and $\lambda$ agree on the half open intervals, a $\pi$-system that generates the Borel sets, and on $[0, 1)$. By the uniqueness theorem of Volume 18, Chapter 2, $D_*\lambda = \lambda$. The same argument shows that $x \mapsto nx$ preserves $\lambda$ on $\mathbb{T}$ for each integer $n \ne 0$.

**Example (The Gauss map).** Let $G(x) = 1/x - \lfloor 1/x \rfloor$ for $x \in (0, 1]$ and $G(0) = 0$. It shifts the continued fraction expansion: $G([0; a_1, a_2, \dots]) = [0; a_2, a_3, \dots]$. It does not preserve Lebesgue measure, but it preserves the Gauss measure $\gamma(A) = \frac{1}{\log 2}\int_A \frac{dx}{1 + x}$. For $0 < t \le 1$,
$$G^{-1}[0, t) = \bigcup_{k \ge 1} \left(\tfrac{1}{k+t}, \tfrac{1}{k}\right],$$
up to the point $0$. With $b_k = \log(1 + t/k)$,
$$\gamma\left(\tfrac{1}{k+t}, \tfrac1k\right] = \frac{1}{\log 2}\left(\log\frac{k+1}{k} - \log\frac{k+1+t}{k+t}\right) = \frac{b_k - b_{k+1}}{\log 2}.$$
The sum over $k$ telescopes to $(b_1 - \lim_k b_k)/\log 2 = \log(1+t)/\log 2 = \gamma[0, t)$. The $\pi$-system argument gives $G_*\gamma = \gamma$.

**Counterexample (Quasi but not measure preserving).** The map $x \mapsto 2x$ on $\mathbb{R}$ sends Lebesgue measure $\lambda$ to $\tfrac12\lambda$. It keeps null sets null in both directions, so it is quasi measure preserving, and it does not preserve $\lambda$.

### The library around it

::: mathlib
`MeasureTheory.MeasurePreserving.measure_preimage` · `Mathlib.Dynamics.Ergodic.MeasurePreserving`

`MeasurePreserving f μa μb → NullMeasurableSet s μb → μa (f ⁻¹' s) = μb s`. The closure lemmas are `MeasurePreserving.id`, `comp`, `iterate` and `symm` for a measurable equivalence. The lemma `of_semiconj` transfers invariance along a factor map, and `restrict_preimage` restricts to a preimage. A set is a.e. trivial if and only if its preimage is, by `aeconst_preimage`, a fact that Chapter 6 uses for ergodicity.

<?decl MeasureTheory.MeasurePreserving.measure_preimage?>
:::

::: mathlib
`MeasureTheory.MeasurePreserving.exists_mem_iterate_mem_of_measure_univ_lt_mul_measure` · `Mathlib.Dynamics.Ergodic.MeasurePreserving`

`μ Set.univ < ↑n * μ s → ∃ x ∈ s, ∃ m ∈ Set.Ioo 0 n, f^[m] x ∈ s`, for a null measurable `s`. The corollary `exists_mem_iterate_mem` needs `IsFiniteMeasure μ` and `μ s ≠ 0`, and gives `m ≠ 0`. The symmetric difference bound is `measure_symmDiff_preimage_iterate_le`, with `n •` on the right.

<?decl MeasureTheory.MeasurePreserving.exists_mem_iterate_mem_of_measure_univ_lt_mul_measure?>
:::

::: mathlib
`MeasureTheory.MeasurePreserving.singularPart` · `Mathlib.Dynamics.Ergodic.RadonNikodym`

With `IsFiniteMeasure μ`, `SigmaFinite ν` and `f` preserving both, `f` preserves `μ.singularPart ν`, and `withDensity_rnDeriv` says that it preserves `ν.withDensity (μ.rnDeriv ν)`. For two finite measures, `rnDeriv_comp_aeEq` gives `μ.rnDeriv ν ∘ f =ᵐ[ν] μ.rnDeriv ν`: the density is an invariant function. The text does not prove this last statement.

<?decl MeasureTheory.MeasurePreserving.singularPart?>
:::

The file `Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving` has the first fact about Birkhoff sums under quasi measure preservation: `QuasiMeasurePreserving.birkhoffSum_ae_eq_of_ae_eq` says that if $\varphi = \psi$ a.e., then the sums $\sum_{k<n} \varphi \circ f^k$ and $\sum_{k<n} \psi \circ f^k$ agree a.e., and `birkhoffAverage_ae_eq_of_ae_eq` is the same for averages. The proof is that each $\varphi \circ f^k = \psi \circ f^k$ a.e. Chapter 6 defines these sums.

The library has many measure preserving maps outside this chapter. `MeasureTheory.measurePreserving_add_left` gives translations for a left invariant measure, and `MeasureTheory.measurePreserving_vadd` gives an invariant action.

<?decl MeasureTheory.measurePreserving_add_left?>

On a compact divisible group with Haar measure, `MeasureTheory.Measure.measurePreserving_zsmul` says that $g \mapsto n g$ preserves the measure for $n \ne 0$; it covers $x \mapsto nx$ on the circle.

<?decl MeasureTheory.Measure.measurePreserving_zsmul?>

Common errors of a learner:

- `MeasurePreserving f` without measures means `volume` on both sides. Write `MeasurePreserving f μ μ` for a general measure.
- The corollary needs a finite measure. The pigeonhole theorem does not, but it needs $\mu(X) < n\,\mu(s)$.
- The equation $\mu(f(A)) = \mu(A)$ is not part of the definition, and it fails for the doubling map.

### Exercises

1. (A) Show that $x \mapsto 1 - x$ and $x \mapsto x^2$ on $[0, 1]$ are measurable, that the first preserves Lebesgue measure, and that the second does not.
2. (A) Let $f$ preserve $\mu$ and let $g \in L^1(\mu)$. Show that $\int g \circ f \, d\mu = \int g \, d\mu$. Hint: start with indicators of sets.
3. (A) Show that $x \mapsto 3x \bmod 1$ preserves Lebesgue measure on $[0, 1)$.
4. (B) Let $f$ preserve a probability measure $\mu$ and let $\mu(s) > \tfrac13$. Show that $s \cap f^{-1}(s)$ or $s \cap f^{-2}(s)$ has positive measure. Hint: follow the pigeonhole proof with $n = 3$.
5. (B) Show that the tent map $T(x) = 1 - |2x - 1|$ preserves Lebesgue measure on $[0, 1]$, and that $x \mapsto 4x(1-x)$ preserves the measure with density $\frac{1}{\pi\sqrt{x(1-x)}}$. Hint: the map $x \mapsto \sin^2(\pi x/2)$ conjugates them.
6. (B) Let $f$ preserve $\mu$ and let $U f$ be the map $g \mapsto g \circ f$ on $L^2(\mu)$. Show that $U$ is an isometry, and that it is unitary when $f$ is invertible with measurable inverse.
7. (B) Show that the Gauss map does not preserve Lebesgue measure: $\lambda(G^{-1}[0, \tfrac12)) = 2 - 2\log 2$. Hint: $\frac{1}{k(2k+1)} = 2\left(\frac{1}{2k} - \frac{1}{2k+1}\right)$ and $\sum_{j \ge 1} (-1)^{j+1}/j = \log 2$.

### Notes and history

The invariance of the Gauss measure goes back to Gauss, who stated it in a letter to Laplace in 1812. The recurrence theorem in the weak form above is due to Poincaré (1890), in his memoir on the three body problem.

### Reference

<?reference?>
