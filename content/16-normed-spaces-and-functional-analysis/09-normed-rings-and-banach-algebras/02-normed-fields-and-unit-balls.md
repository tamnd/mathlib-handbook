---
title: Normed fields and unit balls
kind: api
modules:
  - Mathlib.Analysis.Normed.Field.Lemmas
  - Mathlib.Analysis.Normed.Field.Instances
  - Mathlib.Analysis.Normed.Field.ProperSpace
  - Mathlib.Analysis.Normed.Field.UnitBall
  - Mathlib.Analysis.Normed.Field.Approximation
  - Mathlib.Analysis.Normed.Field.Dense
explains:
  E2: [NormedField.continuousAt_inv, Filter.tendsto_inv₀_cobounded, DilationEquiv.mulLeft, NormedField.discreteTopology_or_nontriviallyNormedField, NormedField.completeSpace_iff_isComplete_closedBall, NormedField.instCompletableTopField, ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace, Submonoid.unitClosedBall, Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt, IsAlgClosed.of_denseRange]
  E1: auto
families: []
requires: [V06, V13, V16.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Normed fields and unit balls

### Overview

A normed field is a field with a multiplicative norm: $\|x y\| = \|x\| \|y\|$. The real numbers, the complex numbers and the $p$-adic numbers are normed fields, and so is each field with the trivial norm, which is $1$ at each $x \ne 0$. In a normed division ring the inverse is continuous at each $x \ne 0$, multiplication by $a \ne 0$ multiplies distances by $\|a\|$, and the inverse exchanges the neighborhoods of $0$ with the neighborhood of infinity. A normed field is either discrete or nontrivially normed, which means that it has an element $c$ with $\|c\| > 1$.

The unit balls of a normed field are closed under multiplication. The closed unit ball is a monoid, and in a field such as $\mathbb{Q}_p$ it is the ring of integers. The unit sphere is a group, the circle group for $\mathbb{C}$. The last two modules of the section are about polynomials. When the coefficients of two monic polynomials are close, their roots are close. From this, the completion of an algebraically closed field with a nonarchimedean norm is again algebraically closed. This result shows, for example, that $\mathbb{C}_p$, the completion of an algebraic closure of $\mathbb{Q}_p$, is algebraically closed.

### The library around it

The module `Mathlib.Analysis.Normed.Field.Lemmas` continues the theory of the basic classes `NormedDivisionRing`, `NormedField`, `NontriviallyNormedField` and `DenselyNormedField`. The instance `NormedDivisionRing.to_isTopologicalDivisionRing` states that a normed division ring is a topological division ring. The lemma `NormedField.continuousAt_inv` states that the inverse is continuous at $x$ if and only if $x \ne 0$, in a nontrivially normed field. The lemma `NormedField.continuousAt_zpow` gives the same for $x^n$ with $n \in \mathbb{Z}$: it is continuous at $x$ if and only if $x \ne 0$ or $n \ge 0$. The lemmas `TendstoLocallyUniformly.inv₀` and `TendstoLocallyUniformly.div₀` state that locally uniform limits pass to inverses and quotients when the limit has no zero.

The neighborhood of infinity is the filter `Bornology.cobounded α`. The lemma `Filter.tendsto_inv₀_cobounded` states that $x^{-1} \to 0$ as $\|x\| \to \infty$, and `Filter.tendsto_inv₀_nhdsNE_zero` states the converse, from the punctured neighborhoods of $0$ to infinity. The lemmas `Filter.inv_cobounded₀` and `Filter.inv_nhdsNE_zero` give the same facts as equalities of filters. The map $x \mapsto a x$ for $a \ne 0$ is `DilationEquiv.mulLeft`, a bijection that multiplies distances by $\|a\|$, and `DilationEquiv.mulRight` is the same on the right. The lemma `Filter.map_mul_left_cobounded` states that this map fixes the filter at infinity.

A field with a norm that takes only the values $0$ and $1$ is discrete. The lemma `NormedField.discreteTopology_or_nontriviallyNormedField` states that each normed field is discrete or has an instance of `NontriviallyNormedField` with the same norm. The lemma `NormedField.discreteTopology_of_bddAbove_range_norm` states that a normed field with a bounded norm is discrete. With this, `NormedField.completeSpace_iff_isComplete_closedBall` states that a normed field is complete if and only if its closed unit ball is complete. The instance `NormedField.instCompletableTopField` states that the completion of a normed field is a field. The instances `Rat.instNormedField` and `Rat.instDenselyNormedField` give the absolute value on $\mathbb{Q}$.

The module `Mathlib.Analysis.Normed.Field.ProperSpace` holds `ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace`. It states that a nontrivially normed field in which each point has a compact neighborhood is proper: each closed ball is compact. The proof takes a compact ball at $0$ and scales it by the powers of an element $c$ with $\|c\| > 1$. Chapter 3 proves the same for normed spaces, with more imports. The field $\mathbb{Q}_p$ is proper by this result.

The module `Mathlib.Analysis.Normed.Field.UnitBall` gives the algebraic structure of the unit balls. The open unit ball has `Metric.unitBall.instSemigroupWithZero`, and the closed unit ball has `Metric.unitClosedBall.instMonoidWithZero` when $\|1\| = 1$. The unit sphere has `Metric.unitSphere.instMonoid` in a ring with `NormMulClass` and `NormOneClass`, and `Metric.unitSphere.instGroup` in a normed division ring. In the second case it is a topological group, by `Metric.sphere.instIsTopologicalGroup`. The same sets are also substructures of the ring: `Subsemigroup.unitBall`, `Submonoid.unitClosedBall` and `Submonoid.unitSphere`. The lemma `Submonoid.mem_unitClosedBall` states that $x$ is in the closed unit ball if and only if $\|x\| \le 1$. The map `unitSphereToUnits` sends the unit sphere to the group of units, and `unitSphereToUnits_injective` states that it is injective.

The three sets inherit the rules of cancellation of a field. The instances `Metric.unitBall.instIsCancelMulZero` and `Metric.unitClosedBall.instIsCancelMulZero` state that $a b = a c$ with $a \ne 0$ gives $b = c$ in each ball, and `Metric.unitClosedBall.coe_eq_one` states that an element of the closed ball is $1$ if and only if its value in the field is $1$. These instances make it possible to state facts about the ring of integers of a nonarchimedean field as facts about a monoid, before Chapter 10 builds the ring structure from the ultrametric inequality. For $\mathbb{C}$, the group `Metric.sphere 0 1` with the instance `Metric.sphere.instCommGroup` is the circle group, and Volume 19 uses it for Fourier series and for the characters of $\mathbb{Z}$.

The module `Mathlib.Analysis.Normed.Field.Approximation` gives the continuity of roots. The theorem `Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt` takes two monic polynomials $f$ and $g$ of the same degree $d$ with $\|g_i - f_i\| < \varepsilon$ for each coefficient, and $g$ splits. Then each root $a$ of $f$ has a root $b$ of $g$ with $\|a - b\| < ((d + 1) \varepsilon)^{1/d} \max(\|a\|, 1)$. The theorem `Polynomial.exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt` is the form for a field extension. The theorem `Polynomial.exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt` states that, for a subfield with dense image, each monic polynomial over the large field is close to a monic polynomial over the subfield of the same degree.

The module `Mathlib.Analysis.Normed.Field.Dense` combines the two results. The theorem `IsAlgClosed.of_denseRange` takes an algebraically closed field $K$ and a complete nontrivially normed field $L$ of characteristic $0$ with an ultrametric norm, and an algebra map $K \to L$ with dense range. Then $L$ is algebraically closed. The proof approximates a monic irreducible polynomial over $L$ by one over $K$, which splits, and uses the continuity of roots and the ultrametric inequality to find a root in $L$.

#### Common errors

1. Expecting a `NormedField` to have an element of norm larger than $1$. A field with the trivial norm is a normed field. The lemma `NormedField.exists_one_lt_norm` needs `NontriviallyNormedField`.
2. Using `NormedField.continuousAt_inv` at $0$. The lemma gives an equivalence, so it proves that the inverse is not continuous at $0$. Mathlib sets $0^{-1} = 0$, and this value does not make the inverse continuous.
3. Applying `IsAlgClosed.of_denseRange` to $\mathbb{C}$ with the dense subfield of algebraic numbers. The theorem needs `IsUltrametricDist`, and the absolute value on $\mathbb{C}$ is not ultrametric. For $\mathbb{C}$, use `Complex.isAlgClosed`.

### Exercises

1. (A) Use `Filter.tendsto_inv₀_cobounded` to show that $1 / (1 + x^2) \to 0$ as $|x| \to \infty$ in $\mathbb{R}$.
2. (A) Show with `Submonoid.mem_unitClosedBall` that the product of two complex numbers of modulus at most $1$ has modulus at most $1$.
3. (B) Show that each finite normed field has the trivial norm, with `IsOfFinOrder.norm_eq_one`, and deduce that it is discrete.
4. (B) Show with `DilationEquiv.mulLeft` that the image of the ball $B(0, r)$ under $x \mapsto a x$ is $B(0, \|a\| r)$ for $a \ne 0$.
5. (B) Apply `Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt` to $f = x^2 - 2$ and $g = x^2 - 2 - \varepsilon$ in $\mathbb{C}$, and compare the bound with the true distance of the roots.
6. (C) Prove `ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace` for $\mathbb{R}$ from the compactness of $[-1, 1]$ and the scaling argument of the text.

### Reference

<?reference?>
