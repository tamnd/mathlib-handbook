---
title: Ergodic maps
kind: theory
modules:
  - Mathlib.Dynamics.Ergodic.Ergodic
  - Mathlib.Dynamics.Ergodic.Function
  - Mathlib.Dynamics.Ergodic.Extreme
  - Mathlib.Dynamics.Ergodic.AddCircle
  - Mathlib.Dynamics.Ergodic.AddCircleAdd
explains:
  E3: [PreErgodic, Ergodic, QuasiErgodic, PreErgodic.of_preimage_eq, Ergodic.ae_eq_const_of_ae_eq_comp₀, Ergodic.iff_mem_extremePoints, AddCircle.ergodic_nsmul, AddCircle.ergodic_add_left]
  E2: [PreErgodic.ae_empty_or_univ, PreErgodic.prob_eq_zero_or_one, PreErgodic.of_preimage_eq_of_measurable, Ergodic.of_preimage_eq, Ergodic.quasiErgodic, Ergodic.ae_empty_or_univ_of_preimage_ae_le, PreErgodic.ae_eq_const_of_ae_eq_comp, Ergodic.ae_eq_const_of_ae_eq_comp_ae, MeasureTheory.MeasurePreserving.ergodic_of_ergodic_semiconj, MeasureTheory.MeasurePreserving.ergodic_conjugate_iff, Ergodic.symm, PreErgodic.of_iterate, Ergodic.iff_mem_extremePoints_measure_univ_eq, AddCircle.ergodic_zsmul, AddCircle.ergodic_nsmul_add, AddCircle.ae_empty_or_univ_of_forall_vadd_ae_eq_self, AddCircle.ergodic_add_right]
  E1: auto
families: []
requires: [V18, V19, V21.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Ergodic maps

### Overview

An ergodic map cannot be split into two invariant pieces of positive measure. Ergodicity is the hypothesis under which time averages equal space averages in Section 3. This section defines ergodicity, gives three equivalent forms of it (invariant sets, invariant functions, extreme invariant measures), and proves that the irrational rotations and the maps $x \mapsto nx$ of the circle are ergodic.

### Definitions

Let $f$ be a measurable map of a measure space $(X, \mu)$. A set $s$ is *invariant* if $f^{-1}(s) = s$ almost everywhere, that is, $\mu(f^{-1}(s) \,\triangle\, s) = 0$. It is *trivial* if it is null or conull.

**Definition (Ergodic map).** The map $f$ is *pre-ergodic* if every null measurable invariant set is trivial. It is *ergodic* if it preserves $\mu$ and is pre-ergodic, and *quasi ergodic* if it is quasi measure preserving and pre-ergodic.

::: mathlib
`Ergodic` · `Mathlib.Dynamics.Ergodic.Ergodic`

`PreErgodic f μ` has one field, `aeconst_set : ∀ ⦃s⦄, NullMeasurableSet s μ → f ⁻¹' s =ᵐ[μ] s → EventuallyEmptyOrUniv s (ae μ)`. The structure `Ergodic f μ` extends `MeasurePreserving f μ μ` and `PreErgodic f μ`, and `QuasiErgodic f μ` extends `QuasiMeasurePreserving f μ μ` and `PreErgodic f μ`. `PreErgodic.ae_empty_or_univ` and `prob_eq_zero_or_one` unpack it.

<?decl Ergodic?>
:::

### Theorems and proofs

**Proposition (Strictly invariant sets suffice).** Let $f$ be quasi measure preserving, and assume that every null measurable set with $f^{-1}(s) = s$ exactly is trivial. Then $f$ is pre-ergodic.

*Proof.* Let $s$ be null measurable with $f^{-1}(s) = s$ a.e. Preimages under a quasi measure preserving map keep a.e. equalities, so by induction $f^{-n}(s) = s$ a.e. for all $n$. Put
$$s' = \bigcap_{N \ge 0} \bigcup_{n \ge N} f^{-n}(s).$$
So $s' = s$ a.e., and $s'$ is null measurable. And $f^{-1}(s') = \bigcap_N \bigcup_{n \ge N} f^{-(n+1)}(s) = s'$, because the sets $\bigcup_{n \ge N+1} f^{-n}(s)$ decrease in $N$ and have the same intersection. So $s'$ is trivial, and so is $s$. $\square$

For a finite measure, an inclusion is enough: if $f$ preserves $\mu$ and $f^{-1}(s) \subseteq s$ a.e., then $\mu(s \setminus f^{-1}(s)) = \mu(s) - \mu(f^{-1}(s)) = 0$, so $s$ is invariant.

**Theorem (Invariant functions are constant).** Let $f$ be ergodic, and $g : X \to \mathbb{R}$ null measurable with $g \circ f = g$ a.e. Then $g$ is a.e. constant.

*Proof.* If $\mu = 0$ there is nothing to prove. For $q \in \mathbb{Q}$ let $s_q = \{g < q\}$. Then $f^{-1}(s_q) = \{g \circ f < q\} = s_q$ a.e., so $s_q$ is null or conull. The sets $s_q$ increase to $X$ and decrease to $\emptyset$, so $s_q$ is null for small $q$ and conull for large $q$. Let $c = \sup\{q \in \mathbb{Q} : \mu(s_q) = 0\}$, a real number. For rational $q < c$, $g \ge q$ a.e.; for rational $q > c$, $g < q$ a.e. Over countably many $q$, this gives $g = c$ a.e. $\square$

The proof works for any target with a countable separating family of measurable sets. Conversely, indicators of invariant sets are invariant functions.

**Proposition (Factors).** Let $g : X \to Y$ be measure preserving from $\mu$ to $\nu$, let $f'$ be a measurable map of $Y$ with $g \circ f = f' \circ g$, and let $f$ be ergodic. Then $f'$ is ergodic.

*Proof.* $f'$ preserves $\nu$ by the semiconjugacy lemma of Chapter 5. Let $t$ be invariant for $f'$. Then $f^{-1}(g^{-1}(t)) = g^{-1}(f'^{-1}(t)) = g^{-1}(t)$ a.e., since $g$ is quasi measure preserving. So $g^{-1}(t)$ is trivial for $\mu$, and $\nu(t) = \mu(g^{-1}(t))$, $\nu(Y \setminus t) = \mu(X \setminus g^{-1}(t))$. $\square$

**Theorem (Ergodic measures are extreme).** Let $f$ be measurable, and let $K$ be the convex set of $f$-invariant probability measures. A measure $\mu \in K$ is ergodic if and only if it is an extreme point of $K$.

*Proof.* Assume $\mu$ is not ergodic, with an invariant $E$ and $0 < \mu(E) < 1$. Put $\mu_E(A) = \mu(A \cap E)/\mu(E)$. Since $f^{-1}(E) = E$ a.e., $\mu_E(f^{-1}A) = \mu(f^{-1}A \cap f^{-1}E)/\mu(E) = \mu_E(A)$, so $\mu_E \in K$, and likewise $\mu_{E^c} \in K$. Now $\mu = \mu(E)\mu_E + \mu(E^c)\mu_{E^c}$, and $\mu_E \ne \mu_{E^c}$ since $\mu_E(E) = 1$ and $\mu_{E^c}(E) = 0$. So $\mu$ is not extreme.

Assume $\mu$ is ergodic and $\mu = t\nu_1 + (1 - t)\nu_2$ with $\nu_i \in K$ and $0 < t < 1$. Then $\nu_1 \le \mu/t$, so $\nu_1 \ll \mu$, with a density $h = d\nu_1/d\mu$ by the Radon-Nikodym theorem (Volume 18, Chapter 4). Let $E = \{h < 1\}$ and $F = f^{-1}(E)$. Since $\mu(E) = \mu(F)$ and $\mu$ is finite, $\mu(E \setminus F) = \mu(F \setminus E)$. Since $\nu_1(E) = \nu_1(F)$,
$$\int_{E \setminus F} h \, d\mu = \int_{F \setminus E} h \, d\mu.$$
The left side is $\le \mu(E \setminus F)$, with strict inequality if $\mu(E \setminus F) > 0$, because $h < 1$ there. The right side is $\ge \mu(F \setminus E) = \mu(E \setminus F)$, because $h \ge 1$ there. So $\mu(E \setminus F) = 0 = \mu(F \setminus E)$, and $E$ is invariant. If $\mu(E) = 1$, then $\nu_1(X) = \int_E h\,d\mu < 1$, which is false. So $\mu(E) = 0$, $h \ge 1$ a.e., and $\int h \, d\mu = 1$ forces $h = 1$ a.e. Then $\nu_1 = \mu$, and $\nu_2 = \mu$ too. $\square$

**Theorem (Irrational rotations).** The rotation $R_a(x) = x + a$ of $\mathbb{T} = \mathbb{R}/\mathbb{Z}$ is ergodic for Haar measure if and only if $a$ is irrational.

*Proof.* Let $a = p/q$ with $q \ge 1$. The set $\bigcup_{j < q} [j/q, j/q + 1/(2q))$ is invariant under $R_a$ and has measure $\tfrac12$. So $R_a$ is not ergodic. Let $a$ be irrational and $s$ invariant, and let $g = 1_s \in L^2(\mathbb{T})$. Its Fourier coefficients (Volume 19, Chapter 6) satisfy $\widehat{g \circ R_a}(k) = e^{2\pi i k a}\hat g(k)$. Since $g \circ R_a = g$ a.e., $(e^{2\pi i k a} - 1)\hat g(k) = 0$. For $k \ne 0$, $ka \notin \mathbb{Z}$, so $\hat g(k) = 0$. So $g = \hat g(0)$ a.e., and $s$ is trivial. $\square$

**Theorem (The maps $x \mapsto nx$).** For an integer $n$ with $|n| \ge 2$, the map $E_n(x) = nx$ of $\mathbb{T}$ is ergodic for Haar measure.

*Proof.* $E_n$ preserves Haar measure by Chapter 5. Let $g = 1_s$ for an invariant $s$. The function $g \circ E_n$ has coefficient $\hat g(k/n)$ at $k$ when $n \mid k$, and $0$ otherwise. From $g \circ E_n = g$ follows $\hat g(nk) = \hat g(k)$ for all $k$. By induction $\hat g(k) = \hat g(n^j k)$ for all $j$. Bessel's inequality gives $\sum_m |\hat g(m)|^2 < \infty$, so $\hat g(n^j k) \to 0$ as $j \to \infty$ when $k \ne 0$. So $\hat g(k) = 0$ for $k \ne 0$, and $s$ is trivial. $\square$

Mathlib avoids Fourier series. If $s = E_n^{-1}(s)$, then $s$ is invariant under the translation by $1/n^k$, since $n^k(x + 1/n^k) = n^k x$. A set invariant under translations by points of order tending to infinity is trivial, by a density argument.

### Examples

**Example (Doubling map).** The doubling map $D(x) = 2x \bmod 1$ is ergodic for Lebesgue measure. In binary, $D$ is the shift of digits, and ergodicity is a zero-one law for events about the digits that do not change when the first digit is removed.

**Example (Extreme points).** For a periodic orbit $x, f(x), \dots, f^{p-1}(x)$ of exact period $p$, the measure $\frac1p\sum_{j<p}\delta_{f^j(x)}$ is invariant and ergodic. For the map $x \mapsto x^2$ on $[0, 1]$, the invariant probability measures are $t\delta_0 + (1-t)\delta_1$, and the ergodic ones are $\delta_0$ and $\delta_1$.

### The library around it

::: mathlib
`PreErgodic.of_preimage_eq` · `Mathlib.Dynamics.Ergodic.Ergodic`

`QuasiMeasurePreserving f μ μ → (∀ ⦃s⦄, NullMeasurableSet s μ → f ⁻¹' s = s → EventuallyEmptyOrUniv s (ae μ)) → PreErgodic f μ`. The variant `PreErgodic.of_preimage_eq_of_measurable` needs `Measurable f` and tests measurable sets only, and `Ergodic.of_preimage_eq` adds `MeasurePreserving`. The inclusion form is `Ergodic.ae_empty_or_univ_of_preimage_ae_le`. If an iterate is pre-ergodic, so is `f`, by `PreErgodic.of_iterate`.

<?decl PreErgodic.of_preimage_eq?>
:::

::: mathlib
`Ergodic.ae_eq_const_of_ae_eq_comp₀` · `Mathlib.Dynamics.Ergodic.Function`

With `[MeasurableSpace.CountablySeparated X]`, `Ergodic f μ → NullMeasurable g μ → g ∘ f =ᵐ[μ] g → ∃ c, g =ᵐ[μ] const α c`. The variant `PreErgodic.ae_eq_const_of_ae_eq_comp` asks for `Measurable g` and `g ∘ f = g`, and `Ergodic.ae_eq_const_of_ae_eq_comp_ae` takes `AEStronglyMeasurable g μ` in a metrizable space.

<?decl Ergodic.ae_eq_const_of_ae_eq_comp₀?>
:::

::: mathlib
`Ergodic.iff_mem_extremePoints` · `Mathlib.Dynamics.Ergodic.Extreme`

For `[IsProbabilityMeasure μ]`, `Ergodic f μ ↔ μ ∈ Set.extremePoints ENNReal {ν | MeasurePreserving f ν ν ∧ IsProbabilityMeasure ν}`. The version for finite measures of a fixed mass is `iff_mem_extremePoints_measure_univ_eq`. Factors are `MeasurePreserving.ergodic_of_ergodic_semiconj`, which needs `Measurable f'`, and `ergodic_conjugate_iff`; inverses are `Ergodic.symm`.

<?decl Ergodic.iff_mem_extremePoints?>
:::

::: mathlib
`AddCircle.ergodic_nsmul` · `Mathlib.Dynamics.Ergodic.AddCircle`

`1 < n → Ergodic (fun y ↦ n • y) volume` on `AddCircle T`. The other forms are `ergodic_zsmul` with `1 < |n|`, and `ergodic_nsmul_add` and `ergodic_zsmul_add` for $y \mapsto ny + x$. The density step is `AddCircle.ae_empty_or_univ_of_forall_vadd_ae_eq_self`, for translations `u i` with `Tendsto (addOrderOf ∘ u) l atTop`.

<?decl AddCircle.ergodic_nsmul?>
:::

::: mathlib
`AddCircle.ergodic_add_left` · `Mathlib.Dynamics.Ergodic.AddCircleAdd`

`Ergodic (fun x ↦ a + x) volume ↔ addOrderOf a = 0` on `AddCircle p`. For `AddCircle 1` the condition says that `a` is the class of an irrational number. The right translation is `ergodic_add_right`.

<?decl AddCircle.ergodic_add_left?>
:::

Common errors of a learner:

- `PreErgodic` does not include measure preservation. The identity is pre-ergodic for a Dirac measure, and so is every map for the zero measure.
- `addOrderOf a = 0` means infinite order.

### Exercises

1. (A) Show that a rational rotation $R_{p/q}$ has a nonconstant invariant $g \in L^2$.
2. (A) Show that $(x, y) \mapsto (x + a, y)$ on $\mathbb{T}^2$ is never ergodic.
3. (B) Let $a \in \mathbb{R}$. Show that $(x, y) \mapsto (x + a, x + y)$ preserves Haar measure on $\mathbb{T}^2$, and that it is ergodic when $a$ is irrational. Hint: for an invariant $g \in L^2$, show $|\hat g(k, l)| = |\hat g(k - l, l)|$; use Bessel for $l \ne 0$ and the irrationality of $a$ for $l = 0$.
4. (B) Let $f$ preserve a finite $\mu$ and $g \in L^1(\mu)$ real with $g \circ f \ge g$ a.e. Show that $g \circ f = g$ a.e. Hint: $\int (g \circ f - g)\,d\mu = 0$.
5. (C) Show that the Gauss map is ergodic for the Gauss measure, given that its cylinder sets $\{x : a_1(x) = k_1, \dots, a_m(x) = k_m\}$ satisfy $\gamma(C \cap G^{-m}A) \ge c\,\gamma(C)\gamma(A)$ for a constant $c > 0$ and all measurable $A$.
6. (C) Let $\mu$ and $\nu$ be ergodic invariant probability measures for $f$. Show that $\mu = \nu$ or $\mu \perp \nu$. Hint: decompose $\mu$ with respect to $\nu$ as in Chapter 5, use that $\mu$ is extreme, and use that $d\mu/d\nu$ is an invariant function.

### Notes and history

The term ergodic comes from Boltzmann's ergodic hypothesis in statistical mechanics. The index of this edition has no declaration for the ergodic decomposition.

### Reference

<?reference?>
