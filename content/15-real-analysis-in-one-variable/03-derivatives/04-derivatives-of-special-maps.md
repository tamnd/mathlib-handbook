---
title: Derivatives of special maps
kind: api
modules:
  - Mathlib.Analysis.Calculus.Deriv.AffineMap
  - Mathlib.Analysis.Calculus.Deriv.Linear
  - Mathlib.Analysis.Calculus.Deriv.Polynomial
  - Mathlib.Analysis.Calculus.Deriv.ZPow
  - Mathlib.Analysis.Calculus.Deriv.Shift
  - Mathlib.Analysis.Calculus.Deriv.CompMul
  - Mathlib.Analysis.Calculus.Deriv.Prod
  - Mathlib.Analysis.Calculus.Deriv.Pi
  - Mathlib.Analysis.Calculus.Deriv.Star
  - Mathlib.Analysis.Calculus.Deriv.Support
explains:
  E2: [deriv_zpow, iter_deriv_zpow, iter_deriv_inv, deriv_comp_neg, deriv_comp_mul_left, Polynomial.deriv, AffineMap.hasDerivAt_lineMap, hasDerivAt_pi, support_deriv_subset]
  E1: auto
families: []
requires: [V02, V13, V15.C01, V15.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Derivatives of special maps

### Overview

Section 1 proved the general rules of differentiation: sums, products, quotients, the chain rule and the power rule for natural exponents. A proof in Mathlib often needs the derivative of one concrete kind of map, and it is faster to apply a ready lemma than to compose the general rules. This section treats ten small modules that give these lemmas. They cover affine and linear maps, polynomials, integer powers, translations and dilations of the variable, maps into products and into function types, the star operation and the complex conjugate, and the support of a derivative.

All the modules use the same setting as Section 1. The variable lives in a nontrivially normed field $\mathbb{K}$, which is $\mathbb{R}$ or $\mathbb{C}$ in practice, and the values live in a normed space $F$ over $\mathbb{K}$. Each module gives the result in the four forms of Section 1: the strict derivative `HasStrictDerivAt`, the derivative `HasDerivAt`, the derivative within a set `HasDerivWithinAt`, and the derivative along a filter `HasDerivAtFilter`. It also gives the equations for the functions `deriv` and `derivWithin`. A reader who knows one form knows the names of the other forms.

### The library around it

#### Affine and linear maps

The module `Mathlib.Analysis.Calculus.Deriv.Linear` treats a continuous linear map $e : \mathbb{K} \to F$. Such a map is $e(x) = x\,e(1)$, so its derivative at every point is the vector $e(1)$. The lemmas `ContinuousLinearMap.hasDerivAt`, `ContinuousLinearMap.hasStrictDerivAt` and `ContinuousLinearMap.deriv` state this. The same lemmas exist for a plain linear map `e : 𝕜 →ₗ[𝕜] F` in the namespace `LinearMap`, for example `LinearMap.hasDerivAt`, because a linear map on the one-dimensional space $\mathbb{K}$ is automatically continuous. The equation for `derivWithin` needs the hypothesis `UniqueDiffWithinAt 𝕜 s x`, as always.

The module `Mathlib.Analysis.Calculus.Deriv.AffineMap` treats an affine map `f : 𝕜 →ᵃ[𝕜] E`. Such a map is a constant plus a linear map, and its linear part is `f.linear`. So the derivative is `f.linear 1` at each point (`AffineMap.hasDerivAt`, `AffineMap.deriv`). The most used special case is the line through two points. The map `AffineMap.lineMap a b` sends $t$ to $a + t(b - a)$, so that $0 \mapsto a$ and $1 \mapsto b$.

**Proposition.** The map $t \mapsto a + t(b - a)$ has the derivative $b - a$ at every $t$.

*Proof.* The map is the constant $a$ plus the linear map $t \mapsto t(b - a)$. The derivative of a constant is $0$, and the linear map has the derivative $1 \cdot (b - a)$. $\square$

This is `AffineMap.hasDerivAt_lineMap`, with the variants `AffineMap.hasStrictDerivAt_lineMap` and `AffineMap.hasDerivWithinAt_lineMap`. The lemma transfers the mean value theorem of Section 2 from an interval to a segment $[a, b]$ in a normed space: compose $f$ with the line map and apply the one-variable theorem to $f \circ \mathrm{lineMap}\ a\ b$ on $[0, 1]$.

#### Polynomials

The module `Mathlib.Analysis.Calculus.Deriv.Polynomial` connects the two meanings of the derivative of a polynomial. For $p \in \mathbb{K}[X]$ the formal derivative `Polynomial.derivative p` is defined by the algebra: $\left(\sum a_k X^k\right)' = \sum k a_k X^{k-1}$. The analytic derivative is the derivative of the function $x \mapsto p(x)$, which Mathlib writes as `fun x => Polynomial.eval x p`.

**Proposition.** For every polynomial $p$ over $\mathbb{K}$ and every $x$, the function $x \mapsto p(x)$ is differentiable at $x$ and its derivative is $p'(x)$.

*Proof.* Induction on $p$. The constants have the derivative $0$, and $X$ has the derivative $1$. The formal derivative and the analytic derivative are both additive and both satisfy the product rule (`Polynomial.derivative_mul` and the product rule of Section 1). Every polynomial is built from constants and $X$ by sums and products. $\square$

The lemmas are `Polynomial.hasDerivAt`, `Polynomial.hasStrictDerivAt` and `Polynomial.deriv`, together with `Polynomial.differentiable` and `Polynomial.differentiableOn`. A second family has the suffix `_aeval`, for example `Polynomial.deriv_aeval` and `Polynomial.hasDerivAt_aeval`. These lemmas take a polynomial $q$ over a commutative semiring $R$ with an algebra structure `Algebra R 𝕜`, and evaluate it with `Polynomial.aeval`. This is the form for a polynomial with integer or rational coefficients that a proof evaluates at real numbers. The module also gives the Fréchet derivative, `Polynomial.fderiv` and `Polynomial.hasFDerivAt`, for use with the multivariable calculus of Volume 17.

#### Integer powers

The module `Mathlib.Analysis.Calculus.Deriv.ZPow` treats $x \mapsto x^m$ for $m \in \mathbb{Z}$. The power `x ^ m` with `m : ℤ` is `zpow`, and for $m < 0$ it is $(x^{-m})^{-1}$. Since $0^{-1} = 0$ in Mathlib, the value $0^m$ is $0$ for every $m \neq 0$. The function $x^m$ is differentiable at $x$ exactly when $x \neq 0$ or $m \ge 0$ (`differentiableAt_zpow`). The lemmas `hasDerivAt_zpow` and `hasStrictDerivAt_zpow` carry this hypothesis in the form `x ≠ 0 ∨ 0 ≤ m`.

**Proposition.** For every $m \in \mathbb{Z}$ and every $x \in \mathbb{K}$, `deriv (fun x => x ^ m) x = m * x ^ (m - 1)`, with no hypothesis.

*Proof.* If $x \neq 0$ or $m \ge 0$, this is `hasDerivAt_zpow`. Otherwise $x = 0$ and $m < 0$. The function is not differentiable at $0$, so the left side is the junk value $0$. On the right side $m - 1 < 0$, so $0^{m-1} = 0$ and the product is $0$. $\square$

This is `deriv_zpow`, and `deriv_zpow'` states it as an equation of functions. The absence of a hypothesis lets a proof iterate the rule. The lemma `iter_deriv_zpow` gives the $k$-th derivative:
$$\frac{d^k}{dx^k} x^m = \Big(\prod_{i=0}^{k-1} (m - i)\Big)\, x^{m-k}.$$
The proof is an induction on $k$: the derivative of $c\,x^{m-k}$ is $c\,(m-k)\,x^{m-k-1}$ by `deriv_zpow` and the rule for a constant factor, at every point. For $m = -1$ the product is $\prod_{i<k}(-1-i) = (-1)^k k!$, and this gives `iter_deriv_inv`:
$$\frac{d^k}{dx^k} \frac{1}{x} = (-1)^k\, k!\, x^{-1-k}.$$
The lemmas `iter_deriv_inv_linear` and `iter_deriv_inv_linear_sub` give the same formula for $1/(cx + d)$ and $1/(cx - d)$, with an extra factor $c^k$. The lemma `iter_deriv_pow` is the version for natural exponents. The iterate `deriv^[k]` is the same as `iteratedDeriv k` by `iteratedDeriv_eq_iterate`, which connects these formulas with Chapter 4. For a function `f : E → 𝕜` the lemmas `DifferentiableAt.zpow` and `Differentiable.zpow` give the differentiability of $f^m$ under the same alternative.

#### Translations, reflections and dilations

The module `Mathlib.Analysis.Calculus.Deriv.Shift` treats $f(x + a)$, $f(a + x)$, $f(x - a)$, $f(a - x)$ and $f(-x)$. The names follow one pattern: `deriv_comp_add_const`, `deriv_comp_const_add`, `deriv_comp_sub_const`, `deriv_comp_const_sub`, `deriv_comp_neg`, and the same with `derivWithin_` and `HasDerivAt.` in front.

**Proposition.** For every $f : \mathbb{K} \to F$ and every $x$, the derivative of $x \mapsto f(-x)$ at $x$ is $-f'(-x)$, with no hypothesis of differentiability.

*Proof.* If $f$ is differentiable at $-x$, the chain rule gives $f'(-x) \cdot (-1)$. If $f$ is not differentiable at $-x$, then $x \mapsto f(-x)$ is not differentiable at $x$, because $f$ is the composition of this function with $x \mapsto -x$. Then both sides are the junk value $0$. $\square$

This is `deriv_comp_neg`. The same argument works for each map of the module, because each inner map is a bijection whose inverse is differentiable. So the `deriv` lemmas of the module have no hypothesis, but the `HasDerivAt` lemmas, such as `HasDerivAt.comp_const_sub`, need the derivative of $f$ at the image point. The `derivWithin` lemmas move the set as well: `derivWithin_comp_neg` uses the set `-s`, and `derivWithin_comp_add_const` uses the translate `a +ᵥ s`, the pointwise translation of the set.

The module `Mathlib.Analysis.Calculus.Deriv.CompMul` treats the dilation $f(cx)$. The lemma `deriv_comp_mul_left` states $\frac{d}{dx} f(cx) = c\, f'(cx)$ for every $c$, again with no hypothesis. For $c \neq 0$ the proof is the argument above. For $c = 0$ the function is constant, and both sides are $0$. The lemma `hasDerivWithinAt_comp_mul_left_smul_iff` is the version with a set, and `derivWithin_comp_mul_left` uses the set `c • s`.

#### Maps into products and function types

The module `Mathlib.Analysis.Calculus.Deriv.Prod` treats curves with values in a product. A map $x \mapsto (f_1(x), f_2(x))$ into $F \times G$ has the derivative $(f_1', f_2')$ when $f_1$ and $f_2$ have the derivatives $f_1'$ and $f_2'$ (`HasDerivAt.prodMk`). For a map $\varphi : \mathbb{K} \to \prod_i E_i$ into a finite product, the derivative is taken componentwise.

**Proposition.** For a finite index type $\iota$, the map $\varphi$ has the derivative $\varphi'$ at $x$ if and only if each component $x \mapsto \varphi(x)_i$ has the derivative $\varphi'_i$ at $x$.

*Proof.* The norm on $\prod_i E_i$ is the maximum of the norms of the components. So the difference quotient of $\varphi$ tends to $\varphi'$ exactly when each component of it tends to $\varphi'_i$. $\square$

This is `hasDerivAt_pi`, with `hasStrictDerivAt_pi`, `hasDerivWithinAt_pi` and the equation `deriv_pi`. The lemmas with `finCons` treat a tuple `Fin.cons (φ x) (φs x)` of length $n + 1$, which is the form in an induction on the length: `hasDerivAt_finCons` splits the derivative into the head and the tail.

The module `Mathlib.Analysis.Calculus.Deriv.Pi` treats two curves in $\mathbb{K}^\iota$. The curve `Function.update x i` replaces the coordinate $i$ of the point $x$ by the variable $y$. The curve `Pi.single i` puts the variable at the coordinate $i$ and $0$ elsewhere. Both are affine in $y$, and both have the derivative `Pi.single i 1`, the $i$-th basis vector (`hasDerivAt_update`, `hasDerivAt_single`, `deriv_update`, `deriv_single`). These lemmas compute partial derivatives in coordinates.

#### The star operation and the conjugate

The module `Mathlib.Analysis.Calculus.Deriv.Star` treats the star operation of a normed space with a star structure. On a field with the trivial star, such as $\mathbb{R}$ with the class `TrivialStar`, the star is real linear and $\frac{d}{dx}\,\overline{f(x)} = \overline{f'(x)}$ (`HasDerivAt.star`, `deriv.star`). This rules out $\mathbb{K} = \mathbb{C}$, since complex conjugation is not complex linear: $z \mapsto \bar z$ has no complex derivative. For $\mathbb{C}$ the correct statement conjugates twice. If $f$ has the derivative $f'$ at $x$, then $\overline{f(\bar z)}$ has the derivative $\overline{f'}$ at $\bar x$ (`HasDerivAt.conj_conj`). The equivalence `hasDerivAt_conj_conj_iff` and the equation `deriv_conj_conj` state this with `starRingEnd 𝕜`, the conjugation as a ring map. The lemmas `HasDerivAt.star_conj` and `deriv_star_conj` treat $\mathrm{star} \circ f \circ \mathrm{conj}$ for $f$ with values in a normed space.

#### The support of the derivative

The module `Mathlib.Analysis.Calculus.Deriv.Support` relates the derivative with the topological support `tsupport f`, the closure of the set where $f \neq 0$.

**Proposition.** The set where $f' \neq 0$ is contained in the topological support of $f$.

*Proof.* Let $x \notin$ `tsupport f`. The complement of the support is open, so $f = 0$ on a neighbourhood of $x$. The derivative of a function that is $0$ near $x$ is $0$ at $x$. $\square$

This is `support_deriv_subset`, and the closed version is `tsupport_deriv_subset`. The pointwise lemmas `HasDerivAt.of_notMem_tsupport` and `deriv_of_notMem_tsupport` give the derivative $0$ outside the support. The corollary `HasCompactSupport.deriv` says that the derivative of a function with compact support has compact support. This is the step that lets an integration by parts on $\mathbb{R}$ drop the boundary terms for bump functions.

#### Common errors

1. Adding the hypothesis `x ≠ 0` to `deriv_zpow` or the hypothesis of differentiability to `deriv_comp_neg`. These lemmas have no hypothesis because of the junk values. The hypotheses are only in the `HasDerivAt` forms, such as `hasDerivAt_zpow`.
2. Applying `Polynomial.deriv` to a polynomial with integer coefficients evaluated at a real number. The function is then `fun x => aeval x q`, and the lemma is `Polynomial.deriv_aeval`.
3. Using `HasDerivAt.star` for a complex function. It needs `TrivialStar 𝕜`, so it fails for $\mathbb{K} = \mathbb{C}$. Use `HasDerivAt.conj_conj`, which changes the point to $\bar x$.

### Exercises

1. (A) Compute the third derivative of $x^{-2}$ with `iter_deriv_zpow`, and check that the product $\prod_{i<3}(-2-i)$ is $-24$.
2. (A) Show that $\frac{d}{dx} f(3 - x) = -f'(3 - x)$ for every $f : \mathbb{R} \to \mathbb{R}$ and every $x$, also when $f$ is not differentiable at $3 - x$.
3. (A) Show that the curve $t \mapsto (\cos t, \sin t)$ in $\mathbb{R} \times \mathbb{R}$ has the derivative $(-\sin t, \cos t)$, and find the $t$ at which this derivative has the norm $1$ for the maximum norm.
4. (B) Prove `iter_deriv_inv` from `iter_deriv_zpow`: show $\prod_{i=0}^{k-1}(-1-i) = (-1)^k k!$ by induction on $k$.
5. (B) Let $f : \mathbb{C} \to \mathbb{C}$ be differentiable at every point. Show that $g(z) = \overline{f(\bar z)}$ is differentiable at every point, and compute $g'$ for $f(z) = i z^2$.
6. (C) Let $f : \mathbb{R} \to \mathbb{R}$ be differentiable with compact support. Show that $f'$ has compact support and that $\int_{\mathbb{R}} f' = 0$. Hint: the support of $f$ lies in some $[-R, R]$, and the fundamental theorem of calculus applies on $[-R-1, R+1]$.

### Reference

<?reference?>
