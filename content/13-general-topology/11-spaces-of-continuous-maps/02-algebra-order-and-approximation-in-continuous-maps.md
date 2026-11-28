---
title: Algebra, order and approximation in the continuous maps
kind: api
modules:
  - Mathlib.Topology.ContinuousMap.Algebra
  - Mathlib.Topology.ContinuousMap.Lattice
  - Mathlib.Topology.ContinuousMap.Ordered
  - Mathlib.Topology.ContinuousMap.Star
  - Mathlib.Topology.ContinuousMap.StarOrdered
  - Mathlib.Topology.ContinuousMap.ContinuousSqrt
  - Mathlib.Topology.ContinuousMap.Units
  - Mathlib.Topology.ContinuousMap.Polynomial
  - Mathlib.Topology.ContinuousMap.Weierstrass
  - Mathlib.Topology.ContinuousMap.StoneWeierstrass
  - Mathlib.Topology.ContinuousMap.Ideals
  - Mathlib.Topology.ContinuousMap.Periodic
  - Mathlib.Topology.ContinuousMap.LocallyConvex
explains:
  E2: [ContinuousMap.isUnit_iff_forall_ne_zero, polynomialFunctions_closure_eq_top, ContinuousMap.abs_mem_subalgebra_closure, ContinuousMap.sublattice_closure_eq_top, ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints, ContinuousMap.idealOf_compl_singleton_isMaximal, ContinuousMap.ideal_isMaximal_iff]
  E1: auto
families: []
requires: [V04, V05, V06, V13.C01, V13.C04, V13.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Algebra, order and approximation in the continuous maps

### Overview

The sum and the product of two continuous real functions are continuous. So the continuous functions on a space form a ring, and the ring operations are pointwise. This section describes how the library gives `C(X, Y)` each structure of $Y$: a group, a ring, an algebra, a module, a lattice, an order, a star operation. It then proves the two approximation theorems of the subject. The theorem of Weierstrass says that the polynomials are dense in `C([a, b], ℝ)`. The theorem of Stone and Weierstrass says that each subalgebra of `C(X, ℝ)` that separates the points of a compact space $X$ is dense.

The last part studies the ideals of `C(X, 𝕜)` for a compact Hausdorff space $X$. The closed ideals correspond to the open sets of $X$, the maximal ideals correspond to the points, and $X$ is recovered from the ring as its space of characters.

The section uses the bundled maps and the compact-open topology of Section 1, the supremum norm for a compact domain, and the rings, modules and algebras of Volumes 5 to 7.

### The library around it

#### Pointwise algebraic structure

The module `Mathlib.Topology.ContinuousMap.Algebra` gives `C(X, Y)` the algebraic structure of $Y$, with pointwise operations. Each instance asks for the continuity of the operation of $Y$. For example, the product $f g$ is defined when the multiplication of $Y$ is continuous, `ContinuousMul Y`, and `ContinuousMap.mul_apply` says $(f g)(x) = f(x) g(x)$. The instances follow the hierarchy of Volume 5: `ContinuousMap.instMonoidOfContinuousMul`, `ContinuousMap.instGroupOfIsTopologicalGroup`, `ContinuousMap.instCommRingOfIsTopologicalRing`, `ContinuousMap.module` and `ContinuousMap.algebra`. The constant maps give the algebra map `ContinuousMap.C`, a ring hom from $R$ to `C(X, A)`.

The names follow three patterns. The rule `ContinuousMap.coe_mul` says that the coercion of a product is the product of the coercions, and there is a `coe_` rule for each operation. The rule `ContinuousMap.mul_apply` gives the value at a point. The rule `ContinuousMap.mul_comp` says that composition on the right is a ring hom: $(f_1 f_2) \circ g = (f_1 \circ g)(f_2 \circ g)$. The same three forms exist for `add`, `sub`, `neg`, `smul`, `pow` and `zsmul`.

The operations are continuous for the compact-open topology when $X$ is locally compact. Then `C(X, Y)` is a topological group or ring: `ContinuousMap.instIsTopologicalGroup` and `ContinuousMap.instIsTopologicalRingOfLocallyCompactSpace`. Bundled homs convert the coercion and the evaluation into algebra homs: `ContinuousMap.coeFnAlgHom` sends $f$ to the bare function, `ContinuousMap.evalAlgHom x` sends $f$ to $f(x)$, and `ContinuousMap.compRightAlgHom` is composition on the right. An algebra hom $\varphi$ of the target gives a hom of continuous maps by composition on the left: `AlgHom.compLeftContinuous`. The bare functions also have their subobjects: `continuousSubring X R` is the subring of the continuous functions in $X \to R$.

The module `Mathlib.Topology.ContinuousMap.LocallyConvex` shows that `C(X, E)` is a locally convex space when $E$ is (`ContinuousMap.instLocallyConvexSpace`). The module `Mathlib.Topology.ContinuousMap.Periodic` sums the translates of a map: the sum $\sum_{n \in \mathbb{Z}} f(x + n p)$ is a periodic function of period $p$ (`ContinuousMap.periodic_tsum_comp_add_zsmul`).

#### Units

A continuous map $f$ to a ring is a unit of `C(X, R)` when it has a continuous inverse. Its values are then units. The converse needs a continuous inversion, so it needs a complete normed ring:

**Proposition.** Let $R$ be a complete normed division ring and $f \in C(X, R)$. Then $f$ is a unit of `C(X, R)` if and only if $f(x) \ne 0$ for each $x \in X$.

*Proof.* If $f g = 1$, then $f(x) g(x) = 1$, so $f(x) \ne 0$. Conversely, the inversion $y \mapsto y^{-1}$ is continuous on the units of a complete normed ring. So $x \mapsto f(x)^{-1}$ is continuous, and it is the inverse of $f$. $\square$

This is `ContinuousMap.isUnit_iff_forall_ne_zero`, in `Mathlib.Topology.ContinuousMap.Units`. The form for a complete normed ring is `ContinuousMap.isUnit_iff_forall_isUnit`. The bijection `ContinuousMap.unitsLift` identifies the continuous maps to the units $M^\times$ with the units of `C(X, M)`. As a consequence, the spectrum of $f$ in `C(X, 𝕜)` is its range (`ContinuousMap.spectrum_eq_range`).

#### Order and lattice structure

The module `Mathlib.Topology.ContinuousMap.Ordered` gives the pointwise order: $f \le g$ if and only if $f(x) \le g(x)$ for each $x$ (`ContinuousMap.le_def`). The maximum and the minimum of two continuous maps to a topological lattice are continuous, so `C(X, Y)` is a lattice (`ContinuousMap.instLatticeOfTopologicalLattice`), with the rules `ContinuousMap.sup_apply` and `ContinuousMap.coe_sup`. The module `Mathlib.Topology.ContinuousMap.Lattice` adds the absolute value, with `ContinuousMap.abs_apply`: $|f|(x) = |f(x)|$. The extension `ContinuousMap.IccExtend` extends a map on $[a, b]$ to the whole line by constants.

#### Star structure and the star order

The module `Mathlib.Topology.ContinuousMap.Star` gives the pointwise star when the star of the target is continuous. The rule `ContinuousMap.star_apply` says $f^*(x) = f(x)^*$, and the instance `ContinuousMap.instStarRingOfContinuousStar` makes `C(X, β)` a star ring. Composition with a continuous star algebra hom is a star algebra hom (`ContinuousMap.compStarAlgHom`). For $\mathbb{C}$, the star is the complex conjugation.

A star-ordered ring is a ring whose nonnegative elements are the sums of the elements $s^* s$. In `C(X, ℝ)` a nonnegative function is a square: $f = (\sqrt{f})^2$, and $\sqrt{f}$ is continuous. The class `ContinuousSqrt R`, in `Mathlib.Topology.ContinuousMap.StarOrdered`, isolates this fact: it gives a continuous function $s$ on the pairs $x_1 \le x_2$ with $x_2 = x_1 + s(x)^2$ (`ContinuousSqrt.sqrt_mul_sqrt`). Under this class, `C(X, R)` is a star-ordered ring (`ContinuousMap.instStarOrderedRingOfContinuousSqrt`). The module `Mathlib.Topology.ContinuousMap.ContinuousSqrt` gives the instances for $\mathbb{R}$, $\mathbb{R}_{\ge 0}$ and $\mathbb{C}$: `instContinuousSqrtReal`, `instContinuousSqrtNNReal` and `instContinuousSqrtComplex`.

#### Polynomials and the theorem of Weierstrass

The module `Mathlib.Topology.ContinuousMap.Polynomial` sees a polynomial as a continuous function. The map `Polynomial.toContinuousMapOn p X` restricts the polynomial function of $p$ to a set $X \subseteq R$. It is an algebra hom (`Polynomial.toContinuousMapOnAlgHom`). Its range is the subalgebra `polynomialFunctions X` of `C(X, R)`.

**Theorem (Weierstrass).** For real numbers $a$ and $b$, the polynomial functions are dense in `C([a, b], ℝ)`.

This is `polynomialFunctions_closure_eq_top`, in `Mathlib.Topology.ContinuousMap.Weierstrass`. The library first proves the case $[0, 1]$ (`polynomialFunctions_closure_eq_top'`) with the Bernstein polynomials. The general case follows by an affine change of variable. The map $t \mapsto a + t (b - a)$ is a homeomorphism $[0, 1] \cong [a, b]$, and the composition with it sends polynomials to polynomials. The $\varepsilon$ form is `exists_polynomial_near_continuousMap`: for each $f$ and each $\varepsilon > 0$ there is a polynomial $p$ with $\lVert p - f \rVert < \varepsilon$ on $[a, b]$.

#### The Stone-Weierstrass theorem

A subalgebra $A$ of `C(X, ℝ)` separates points if for $x \ne y$ some $f \in A$ has $f(x) \ne f(y)$. The predicate is `Subalgebra.SeparatesPoints`.

**Theorem (Stone-Weierstrass).** Let $X$ be compact, and let $A$ be a subalgebra of `C(X, ℝ)` that separates points. Then $A$ is dense in `C(X, ℝ)`.

This is `ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints`, in `Mathlib.Topology.ContinuousMap.StoneWeierstrass`. The proof has three steps, and each step is a lemma of the module.

*Step 1.* If $f \in A$, then $|f|$ is in the closure $\bar A$. The values of $f$ lie in $[-\lVert f \rVert, \lVert f \rVert]$. By the theorem of Weierstrass, polynomials $p_n$ tend to the absolute value uniformly on this interval. Then $p_n \circ f \in A$, and $p_n \circ f$ tends to $|f|$. This is `ContinuousMap.abs_mem_subalgebra_closure`.

*Step 2.* The closure $\bar A$ is a lattice. Indeed $\max(f, g) = \tfrac{1}{2}(f + g + |f - g|)$, and the same holds for the minimum (`ContinuousMap.sup_mem_subalgebra_closure`, `ContinuousMap.inf_mem_closed_subalgebra`).

*Step 3.* A set $L$ of functions separates points strongly if for $x \ne y$ and real numbers $a$ and $b$ some $f \in L$ has $f(x) = a$ and $f(y) = b$. An algebra that separates points and contains the constants separates points strongly (`Subalgebra.SeparatesPoints.strongly`). A lattice of functions on a compact space that separates points strongly is dense (`ContinuousMap.sublattice_closure_eq_top`). For the proof of this step, fix $f$ and $\varepsilon > 0$. For each pair $x, y$ choose $h_{xy} \in L$ equal to $f$ at $x$ and at $y$. For fixed $x$, the sets $\{h_{xy} > f - \varepsilon\}$ cover $X$. A finite subcover and a maximum give $h_x \in L$ with $h_x > f - \varepsilon$ everywhere and $h_x(x) = f(x)$. The sets $\{h_x < f + \varepsilon\}$ cover $X$ again, and a minimum of finitely many $h_x$ is within $\varepsilon$ of $f$. $\square$

The $\varepsilon$ form is `ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints`. For $\mathbb{R}$ or $\mathbb{C}$ (the class `RCLike`) the theorem needs a star subalgebra: a subalgebra of `C(X, ℂ)` that separates points and is closed under conjugation is dense (`ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints`). The condition on conjugation is needed: the holomorphic polynomials on the closed disc separate points, but their uniform limits are holomorphic in the open disc.

For a compact set $s \subseteq \mathbb{C}$, the polynomials in $z$ and $\bar z$ are dense in `C(s, ℂ)` (`polynomialFunctions.starClosure_topologicalClosure`). The induction rule `ContinuousMap.induction_on_of_compact` turns this into a proof method: a closed property of the maps of `C(s, 𝕜)` that holds for the constants, for $z$ and $\bar z$, and is closed under sums and products, holds for each map.

#### Ideals and characters

The module `Mathlib.Topology.ContinuousMap.Ideals` relates the ideals of `C(X, 𝕜)` to the sets of $X$. For a set $s$, the ideal `ContinuousMap.idealOfSet 𝕜 s` is the set of the functions that vanish off $s$ (`ContinuousMap.mem_idealOfSet`). For an ideal $I$, the set `ContinuousMap.setOfIdeal I` is the set of the points where some $f \in I$ does not vanish (`ContinuousMap.mem_setOfIdeal`). Let $X$ be compact Hausdorff. Then the set of an ideal is open, and:

| Lean name | Statement |
|---|---|
| `ContinuousMap.setOfIdeal_ofSet_eq_interior` | the set of the ideal of $s$ is the interior of $s$ |
| `ContinuousMap.idealOfSet_ofIdeal_eq_closure` | the ideal of the set of $I$ is the closure of $I$ |
| `ContinuousMap.idealOpensGI` | the two maps form a Galois insertion between open sets and ideals |
| `ContinuousMap.idealOf_compl_singleton_isMaximal` | the functions that vanish at $x$ form a maximal ideal |
| `ContinuousMap.ideal_isMaximal_iff` | each closed maximal ideal has this form |

The maximality of the ideal $I_x$ of the functions that vanish at $x$ is short. The evaluation at $x$ is a surjective ring hom onto the field $𝕜$, and its kernel is $I_x$. A kernel of a surjection onto a field is maximal.

For the converse, let $I$ be a closed proper ideal. Suppose that each point $x$ has some $f_x \in I$ with $f_x(x) \ne 0$. Then $|f_x|^2 = \overline{f_x} f_x \in I$ is positive near $x$. By compactness, a finite sum $g$ of such functions is positive on $X$. Thus $g$ is a unit by the proposition on units, and $g \in I$, a contradiction. So all the functions of $I$ vanish at some point $x$, and $I \subseteq I_x$. If $I$ is maximal, then $I = I_x$.

The characters of `C(X, 𝕜)` are the nonzero algebra homs to $𝕜$. Each evaluation is one. The map `WeakDual.CharacterSpace.homeoEval` is a homeomorphism from $X$ to the character space. So a compact Hausdorff space is determined by its ring of continuous functions. This is the commutative case of the theorem of Gelfand.

#### Common errors

1. Expecting `C(X, Y)` to be a topological ring for each space $X$. The algebraic instances need only the continuity of the operations of $Y$. The continuity of the operations on `C(X, Y)` itself needs a locally compact $X$, or the norm of a compact $X$.
2. Applying the real Stone-Weierstrass theorem to complex functions. Over $\mathbb{C}$ the subalgebra must be a star subalgebra, and the statement is `ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints`.
3. Using `ContinuousMap.ideal_isMaximal_iff` for an ideal that is not closed. The rule has the hypothesis `IsClosed I`. The proof above shows that each maximal ideal of `C(X, 𝕜)` is closed, but the rule asks for the hypothesis.

### Exercises

1. (A) Prove `ContinuousMap.mul_comp` from `ContinuousMap.ext` and `ContinuousMap.mul_apply`.
2. (A) Show that the function $x \mapsto x$ is a unit of `C((0, 1], ℝ)` and is not a unit of `C([0, 1], ℝ)`.
3. (B) Deduce the theorem of Weierstrass on $[a, b]$ from the case $[0, 1]$ with an affine homeomorphism.
4. (B) Let $X$ be compact and $A$ a subalgebra of `C(X, ℝ)` that separates points. Show that $A$ together with the constants separates points strongly.
5. (B) Show that the trigonometric polynomials are dense in the continuous functions on the circle. Use the star form of the Stone-Weierstrass theorem.
6. (C) Prove that each maximal ideal of `C(X, ℝ)` is closed, for a compact Hausdorff space $X$.

### Reference

<?reference?>
