---
title: Inner products
kind: theory
modules:
  - Mathlib.Analysis.InnerProductSpace.Defs
  - Mathlib.Analysis.InnerProductSpace.Basic
  - Mathlib.Analysis.InnerProductSpace.OfNorm
  - Mathlib.Analysis.InnerProductSpace.PiL2
  - Mathlib.Analysis.InnerProductSpace.LinearMap
  - Mathlib.Analysis.InnerProductSpace.Continuous
  - Mathlib.Analysis.InnerProductSpace.ConformalLinearMap
explains:
  E3: [InnerProductSpace, norm_inner_le_norm, parallelogram_law_with_norm, InnerProductSpace.ofNorm]
  E2: [Inner, inner_conj_symm, inner_smul_left, inner_smul_right, inner_add_left, inner_self_eq_zero, real_inner_self_eq_norm_sq, inner_self_eq_norm_sq_to_K, real_inner_le_norm, abs_real_inner_le_norm, norm_inner_eq_norm_iff, inner_eq_sum_norm_sq_div_four, real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two, norm_add_sq_real, InnerProductSpace.ofCore, EuclideanSpace, PiLp.inner_apply, innerSL, innerSL_apply_norm]
  E1: auto
families: []
requires: [V07, V13, V16.C01, V16.C02]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Inner products

### Overview

An inner product on a vector space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$ is a positive definite Hermitian form. It defines a norm, and this section proves the three identities that make the norm useful: the inequality of Cauchy-Schwarz, the parallelogram law and the polarization identity, which recovers the inner product from the norm. A norm comes from an inner product exactly when it satisfies the parallelogram law, and the section proves this in the real case. Mathlib does not build the norm from the inner product. Its class `InnerProductSpace 𝕜 E` takes a normed space and asks that the norm and the inner product agree, so the two structures on `E` never conflict.

### Definitions

**Definition (inner product).** An *inner product* on a vector space $E$ over $\mathbb{K}$ is a map $\langle \cdot, \cdot \rangle : E \times E \to \mathbb{K}$ such that for all $x, y, z \in E$ and $c \in \mathbb{K}$:

- $\langle x + y, z \rangle = \langle x, z \rangle + \langle y, z \rangle$ and $\langle cx, y \rangle = \bar{c}\langle x, y \rangle$;
- $\langle y, x \rangle = \overline{\langle x, y \rangle}$;
- $\langle x, x \rangle \ge 0$, with $\langle x, x \rangle = 0$ only for $x = 0$.

From the first two conditions, $\langle x, cy \rangle = c\langle x, y \rangle$. So the form is conjugate linear in the first argument and linear in the second. Over $\mathbb{R}$ the bar is the identity and the form is bilinear and symmetric. The *norm* of the inner product is $\|x\| = \sqrt{\langle x, x \rangle}$. An *inner product space* is a vector space with an inner product and this norm.

::: mathlib
`InnerProductSpace` · `Mathlib.Analysis.InnerProductSpace.Defs`

`InnerProductSpace 𝕜 E` extends `NormedSpace 𝕜 E` and `Inner 𝕜 E` for a field with `RCLike 𝕜` and `[SeminormedAddCommGroup E]`. Its fields are `norm_sq_eq_re_inner : ‖x‖ ^ 2 = re (inner x x)`, `conj_inner_symm`, `add_left` and `smul_left : inner (r • x) y = conj r * inner x y`. The convention is the one of the text: conjugate linear in the first argument. The inner product is `inner 𝕜 x y`, with the field explicit, and the scoped notation `⟪x, y⟫_𝕜` of the namespace `InnerProductSpace`. Positive definiteness comes from the norm: with `NormedAddCommGroup E`, `inner_self_eq_zero` gives `inner 𝕜 x x = 0 ↔ x = 0`.

<?decl InnerProductSpace?>
:::

To build an inner product space from an inner product alone, Mathlib has the class `InnerProductSpace.Core`, with the axioms of the text. The norm comes first, from `InnerProductSpace.Core.toNormedAddCommGroup`, and then `InnerProductSpace.ofCore` gives the instance from the underlying `PreInnerProductSpace.Core`. This is the route for a new example.

**Definition (Euclidean space).** For a finite type $\iota$, the *Euclidean space* $\mathbb{K}^\iota$ has $\langle x, y \rangle = \sum_i \overline{x_i}\, y_i$ and $\|x\| = (\sum_i |x_i|^2)^{1/2}$.

::: mathlib
`EuclideanSpace` · `Mathlib.Analysis.InnerProductSpace.PiL2`

`EuclideanSpace 𝕜 ι` is `PiLp 2 (fun _ : ι ↦ 𝕜)`, the space of functions `ι → 𝕜` with the $\ell^2$ norm. It is a type synonym: the plain type `ι → 𝕜` carries the sup norm of Chapter 1, and `EuclideanSpace 𝕜 ι` carries the Euclidean norm. The maps `WithLp.toLp` and `ofLp` go between the two. The inner product is computed by `PiLp.inner_apply` as a sum over `ι`.

<?decl EuclideanSpace?>
:::

### Theorems and proofs

**Theorem (Cauchy-Schwarz).** In an inner product space, $|\langle x, y \rangle| \le \|x\|\,\|y\|$ for all $x, y$. Equality holds if and only if $x$ and $y$ are linearly dependent.

*Proof.* If $y = 0$ both sides are $0$ and the pair is dependent. Let $y \ne 0$ and $t = \langle y, x \rangle / \|y\|^2$. By the axioms,
$$0 \le \|x - ty\|^2 = \|x\|^2 - t\langle x, y \rangle - \bar{t}\langle y, x \rangle + |t|^2\|y\|^2.$$
Since $\langle y, x \rangle\langle x, y \rangle = |\langle x, y \rangle|^2$, each of the last three terms equals $|\langle x, y \rangle|^2 / \|y\|^2$, with the signs shown. So $0 \le \|x\|^2 - |\langle x, y \rangle|^2/\|y\|^2$, which is the inequality. Equality holds if and only if $\|x - ty\| = 0$, that is $x = ty$. Conversely, if $x = sy$ then $|\langle x, y \rangle| = |s|\,\|y\|^2 = \|x\|\,\|y\|$. $\square$

**Corollary (the norm).** The map $x \mapsto \sqrt{\langle x, x \rangle}$ is a norm.

*Proof.* Definiteness is the last axiom and $\|cx\| = |c|\,\|x\|$ follows from $\langle cx, cx \rangle = \bar{c}c\langle x, x \rangle$. For the triangle inequality,
$$\|x + y\|^2 = \|x\|^2 + 2\operatorname{Re}\langle x, y \rangle + \|y\|^2 \le \|x\|^2 + 2\|x\|\,\|y\| + \|y\|^2 = (\|x\| + \|y\|)^2$$
by Cauchy-Schwarz. $\square$

::: mathlib
`norm_inner_le_norm` · `Mathlib.Analysis.InnerProductSpace.Basic`

`norm_inner_le_norm x y : ‖⟪x, y⟫_𝕜‖ ≤ ‖x‖ * ‖y‖`. The real forms are `real_inner_le_norm` and `abs_real_inner_le_norm`. The proof goes through `InnerProductSpace.Core.norm_inner_le_norm`, the same inequality for a core, which is needed before the norm exists. The equality case is `norm_inner_eq_norm_iff`: for `x ≠ 0` and `y ≠ 0`, `‖⟪x, y⟫_𝕜‖ = ‖x‖ * ‖y‖ ↔ ∃ r, r ≠ 0 ∧ y = r • x`.

<?decl norm_inner_le_norm?>
:::

**Corollary (continuity).** The inner product is continuous on $E \times E$, and for each $x$ the map $y \mapsto \langle x, y \rangle$ is a bounded linear functional of norm $\|x\|$.

*Proof.* $|\langle x, y \rangle - \langle x', y' \rangle| \le |\langle x - x', y \rangle| + |\langle x', y - y' \rangle| \le \|x - x'\|\,\|y\| + \|x'\|\,\|y - y'\|$. The functional has norm at most $\|x\|$ by Cauchy-Schwarz, and its value at $x$ is $\|x\|^2$. $\square$

In Mathlib the map $x \mapsto \langle x, \cdot \rangle$ is `innerSL 𝕜 : E →L⋆[𝕜] E →L[𝕜] 𝕜`, a conjugate linear map into the dual, and `innerSL_apply_norm` is the equality of norms.

**Theorem (parallelogram law and polarization).** In an inner product space,
$$\|x + y\|^2 + \|x - y\|^2 = 2\|x\|^2 + 2\|y\|^2.$$
Over $\mathbb{R}$, $\langle x, y \rangle = \tfrac14(\|x + y\|^2 - \|x - y\|^2)$. Over $\mathbb{C}$,
$$\langle x, y \rangle = \tfrac14\left(\|x + y\|^2 - \|x - y\|^2 + i\|x - iy\|^2 - i\|x + iy\|^2\right).$$

*Proof.* Expand $\|x \pm y\|^2 = \|x\|^2 \pm 2\operatorname{Re}\langle x, y \rangle + \|y\|^2$ and add, or subtract for the real polarization. Over $\mathbb{C}$ the same expansion with $iy$ in place of $y$ gives $\|x - iy\|^2 - \|x + iy\|^2 = -4\operatorname{Re}(i\langle x, y \rangle) = 4\operatorname{Im}\langle x, y \rangle$. So the right side is $\operatorname{Re}\langle x, y \rangle + i\operatorname{Im}\langle x, y \rangle$. $\square$

::: mathlib
`parallelogram_law_with_norm` · `Mathlib.Analysis.InnerProductSpace.Basic`

`parallelogram_law_with_norm 𝕜 x y : ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2)`. The complex polarization is `inner_eq_sum_norm_sq_div_four`, with `RCLike.I` for $i$, so it holds over each `RCLike` field; over `ℝ` the terms with `I` vanish. A real form with one square fewer is `real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two`, from `norm_add_sq_real`.

<?decl parallelogram_law_with_norm?>
:::

**Theorem (Jordan-von Neumann, real case).** Let $E$ be a real normed space whose norm satisfies the parallelogram law. Then $\langle x, y \rangle = \tfrac14(\|x + y\|^2 - \|x - y\|^2)$ is an inner product with $\langle x, x \rangle = \|x\|^2$.

*Proof.* Write $\varphi(x, y)$ for the formula. It is symmetric, $\varphi(x, x) = \|x\|^2$, and $\varphi(-x, y) = -\varphi(x, y)$, $\varphi(0, y) = 0$. The parallelogram law for the pairs $(x + y, x')$ and $(x - y, x')$ gives
$$\|x + x' + y\|^2 + \|x - x' + y\|^2 = 2\|x + y\|^2 + 2\|x'\|^2,$$
$$\|x + x' - y\|^2 + \|x - x' - y\|^2 = 2\|x - y\|^2 + 2\|x'\|^2.$$
Subtract and divide by $4$: $\varphi(x + x', y) + \varphi(x - x', y) = 2\varphi(x, y)$. With $x' = x$ this gives $\varphi(2x, y) = 2\varphi(x, y)$. For $u, v \in E$ take $x = (u + v)/2$ and $x' = (u - v)/2$:
$$\varphi(u, y) + \varphi(v, y) = 2\varphi\left(\tfrac{u + v}{2}, y\right) = \varphi(u + v, y).$$
So $\varphi$ is additive in the first argument. By induction $\varphi(nx, y) = n\varphi(x, y)$ for $n \in \mathbb{N}$, then for $n \in \mathbb{Z}$ by oddness, then $\varphi(qx, y) = q\varphi(x, y)$ for $q \in \mathbb{Q}$ by $q = m/n$. The map $c \mapsto \varphi(cx, y)$ is continuous, since the norm is, so $\varphi(cx, y) = c\varphi(x, y)$ for $c \in \mathbb{R}$ by density of $\mathbb{Q}$. Positivity is $\varphi(x, x) = \|x\|^2$. $\square$

The complex case follows: if a complex norm satisfies the law, the real inner product $\varphi$ of the restriction to $\mathbb{R}$ gives $\langle x, y \rangle = \varphi(x, y) + i\varphi(x, iy)$ after a check of the complex homogeneity, as in Exercise 6.

::: mathlib
`InnerProductSpace.ofNorm` · `Mathlib.Analysis.InnerProductSpace.OfNorm`

`InnerProductSpace.ofNorm 𝕜 h : InnerProductSpace 𝕜 E` for a normed space over an `RCLike` field with `h : ∀ x y, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)`. It is a definition, not an instance, because it would make a second inner product on spaces that have one. The inner product it defines is the polarization formula with the terms $\|ix \pm y\|$. The source proves additivity from the parallelogram law by computation, and homogeneity in the steps of the text: $\mathbb{N}$, $\mathbb{Z}$, $\mathbb{Q}$, then $\mathbb{R}$ by continuity, then $\mathbb{C}$.

<?decl InnerProductSpace.ofNorm?>
:::

### Examples

**Example (the space $\ell^2_n$).** On $\mathbb{C}^2$ let $x = (1, i)$ and $y = (i, 1)$. Then $\langle x, y \rangle = \bar{1}\cdot i + \bar{i}\cdot 1 = i - i = 0$, and $\langle y, x \rangle = 0$. For $z = (1, 0)$, $\langle x, z \rangle = 1$ and $\langle z, x \rangle = 1$. With $c = i$, $\langle ix, z \rangle = \bar{i} = -i$ and $\langle x, iz \rangle = i$, which shows the two linearity conventions at work. In Mathlib this is `EuclideanSpace ℂ (Fin 2)`.

**Example (the integral inner product).** On $C[0, 1]$ with real values, $\langle f, g \rangle = \int_0^1 f g$ is an inner product: the integral of a nonnegative continuous function is $0$ only if the function is $0$. Cauchy-Schwarz gives $(\int_0^1 f)^2 \le \int_0^1 f^2$, with $g = 1$. The space is not complete for this norm, which Section 3 uses.

**Counterexample (the sup norm).** On $\mathbb{R}^2$ with $\|(a, b)\|_\infty = \max(|a|, |b|)$ let $x = (1, 0)$ and $y = (0, 1)$. Then $\|x + y\|^2 + \|x - y\|^2 = 1 + 1 = 2$ and $2\|x\|^2 + 2\|y\|^2 = 4$. The parallelogram law fails, so no inner product gives this norm. The same pair shows that $\|\cdot\|_1$ on $\mathbb{R}^2$ does not come from an inner product, and so does $\ell^p$ for $p \ne 2$.

### The library around it

The file `Mathlib.Analysis.InnerProductSpace.Basic` holds the algebra of inner products: `inner_add_left`, `inner_smul_left`, `inner_smul_right`, `inner_conj_symm`, `real_inner_self_eq_norm_sq` and `inner_self_eq_norm_sq_to_K`, which reads `⟪x, x⟫_𝕜 = (‖x‖ : 𝕜) ^ 2`. These are the rewriting lemmas of daily use.

The file `Mathlib.Analysis.InnerProductSpace.Continuous` proves that the inner product is continuous. The map $(x, y) \mapsto \langle x, y \rangle$ is a bounded real bilinear map, `isBoundedBilinearMap_inner`, because $|\langle x, y \rangle| \le \lVert x \rVert \lVert y \rVert$. So it is continuous, `continuous_inner`, and the composed forms `Continuous.inner`, `ContinuousAt.inner`, `ContinuousOn.inner`, `ContinuousWithinAt.inner` and `Filter.Tendsto.inner` say that $t \mapsto \langle f(t), g(t) \rangle$ is continuous, or has the limit $\langle x, y \rangle$, when $f$ and $g$ are continuous or have the limits $x$ and $y$.

The file `Mathlib.Analysis.InnerProductSpace.ConformalLinearMap` has one theorem, `isConformalMap_iff`: a bounded real linear map $f$ between real inner product spaces is conformal if and only if there is a $c > 0$ with $\langle f u, f v \rangle = c \langle u, v \rangle$ for all $u$ and $v$. The proof uses polarization: a conformal map multiplies all norms by one factor $r > 0$, so it multiplies all inner products by $c = r^2$.

Common errors:

- Mathlib is conjugate linear in the first argument, the convention of physics. Many books of mathematics use the second. A formula copied from such a book needs its arguments swapped.
- `inner` takes the field as an explicit argument: `inner 𝕜 x y`. Over `ℝ`, open the namespace `RealInnerProductSpace` to write `⟪x, y⟫`.
- `ι → ℝ` has the sup norm, not the Euclidean norm. Use `EuclideanSpace ℝ ι` for the inner product.
- Do not declare `InnerProductSpace.ofNorm` as a global instance.

### Exercises

1. (A) Show that $\langle x, y \rangle = 2x_1y_1 + x_1y_2 + x_2y_1 + x_2y_2$ is an inner product on $\mathbb{R}^2$, and compute the norm of $(1, -1)$.
2. (A) Prove $\|x - y\|^2 = \|x\|^2 - 2\langle x, y \rangle + \|y\|^2$ in a real inner product space, and derive the law of cosines.
3. (A) Show that $\ell^1$ with its norm is not an inner product space.
4. (B) Show that $\|x + y\| = \|x\| + \|y\|$ holds in an inner product space if and only if one vector is a nonnegative multiple of the other.
5. (B) Show that in a real inner product space $\langle x, y \rangle = 0$ if and only if $\|x + ty\| \ge \|x\|$ for all $t \in \mathbb{R}$.
6. (B) Let $E$ be a complex normed space with the parallelogram law, and $\varphi$ the real inner product of the theorem. Show that $\langle x, y \rangle = \varphi(x, y) + i\varphi(x, iy)$ satisfies $\langle x, iy \rangle = i\langle x, y \rangle$.
7. (C) Show that a normed space is an inner product space if each subspace of dimension $2$ is one.

### Notes and history

Augustin-Louis Cauchy proved the inequality for finite sums in 1821. Viktor Bunyakovsky and Hermann Amandus Schwarz proved the form for integrals. Pascual Jordan and John von Neumann characterized the norms that come from inner products by the parallelogram law in 1935. The files `Mathlib.Analysis.InnerProductSpace.Defs` and `Mathlib.Analysis.InnerProductSpace.Basic` have the authors Zhouhang Zhou, Sébastien Gouëzel and Frédéric Dupuis. The file `Mathlib.Analysis.InnerProductSpace.OfNorm` has the author Heather Macbeth, and the file `Mathlib.Analysis.InnerProductSpace.PiL2` has the authors Joseph Myers, Sébastien Gouëzel and Heather Macbeth.

### Reference

<?reference?>
