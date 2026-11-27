---
title: The complex numbers as a normed field
kind: theory
modules:
  - Mathlib.Analysis.Complex.Basic
  - Mathlib.Analysis.Complex.Norm
  - Mathlib.Analysis.Complex.ReImTopology
  - Mathlib.Analysis.Complex.Order
  - Mathlib.Analysis.Complex.Isometry
explains:
  E3: [Complex.instNormedField, Complex.instCompleteSpace, Complex.ringHom_eq_id_or_conj_of_continuous, Complex.le_def, linear_isometry_complex]
  E2: [Complex.norm_def, Complex.norm_mul, Complex.norm_conj, Complex.abs_re_le_norm, Complex.abs_im_le_norm, Complex.norm_le_abs_re_add_abs_im, Complex.dist_eq_re_im, Complex.norm_le_sqrt_two_mul_max, Complex.equivRealProdCLM, Complex.lipschitz_equivRealProd, Complex.antilipschitz_equivRealProd, Complex.instProperSpace, Complex.conjLIE, Complex.isometry_conj, Complex.continuous_re, Complex.continuous_im, Complex.isOpenMap_re, Complex.closure_reProdIm, Complex.interior_reProdIm, Complex.frontier_reProdIm, Complex.closure_setOfPred_re_lt, Complex.partialOrder, Complex.lt_def, Complex.nonneg_iff, Complex.not_le_iff, Complex.sq_nonneg_iff, Complex.re_eq_norm, Complex.real_le_real, rotation, rotation_apply, LinearIsometry.re_apply_eq_re]
  E1: auto
families: []
requires: [V16.C01, V13]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The complex numbers as a normed field

### Overview

The field $\mathbb{C}$ is also the real plane $\mathbb{R}^2$ and a metric space. This section shows that these structures fit together. The norm $|z|$ is multiplicative, so $\mathbb{C}$ is a normed field in the sense of Volume 16, Chapter 1. The identification with $\mathbb{R}^2$ is a homeomorphism, so $\mathbb{C}$ is complete and its closed bounded sets are compact. The section also treats conjugation, products of sets of real and imaginary parts, and the partial order of Mathlib. It ends with two rigidity results: a continuous ring homomorphism of $\mathbb{C}$ is the identity or conjugation, and a real linear isometry of $\mathbb{C}$ is a rotation, possibly after conjugation.

### Definitions

A complex number is a pair $z = (x, y)$ of real numbers, written $z = x + iy$, with $x = \operatorname{Re} z$ and $y = \operatorname{Im} z$. The *conjugate* of $z$ is $\bar z = x - iy$, and conjugation is a ring automorphism that fixes $\mathbb{R}$.

**Definition (Norm).** The *norm* of $z = x + iy$ is $|z| = \sqrt{x^2 + y^2}$. Equivalently $|z|^2 = z \bar z$, and $z \bar z = x^2 + y^2$ is called the *norm squared* $N(z)$. The distance is $d(z, w) = |z - w|$.

**Definition (Partial order).** For $z, w \in \mathbb{C}$, write $z \le w$ when $\operatorname{Re} z \le \operatorname{Re} w$ and $\operatorname{Im} z = \operatorname{Im} w$.

Two numbers are comparable only when they lie on the same horizontal line, and $0 \le z$ means that $z$ is a nonnegative real number.

**Definition (Rotation).** For $a \in \mathbb{C}$ with $|a| = 1$, the *rotation* by $a$ is the map $z \mapsto a z$.

::: mathlib
`Complex.instNormedField` · `Mathlib.Analysis.Complex.Basic`

The instance makes `ℂ` a `NormedField`. The norm itself comes from `Complex.instNormedAddCommGroup` in `Mathlib.Analysis.Complex.Norm`, with `Complex.norm_def : ‖z‖ = √(normSq z)`. The function `Complex.normSq` is a `MonoidWithZeroHom`, so it is multiplicative by construction.

<?decl Complex.instNormedField?>
:::

### Theorems and proofs

**Theorem (Multiplicative norm).** For $z, w \in \mathbb{C}$, $|zw| = |z||w|$ and $|\bar z| = |z|$. Hence $\mathbb{C}$ is a normed field.

*Proof.* Conjugation is a ring homomorphism, so $\overline{zw} = \bar z \bar w$. Then $N(zw) = zw\,\overline{zw} = (z \bar z)(w \bar w) = N(z)N(w)$, because $\mathbb{C}$ is commutative. Both sides are nonnegative reals, so taking square roots gives $|zw| = |z||w|$. For the conjugate, $N(\bar z) = \bar z z = N(z)$. The triangle inequality is that of the Euclidean norm on $\mathbb{R}^2$ (Volume 16, Chapter 6). $\square$

**Theorem (Comparison with the coordinates).** For $z = x + iy$,
$$\max(|x|, |y|) \le |z| \le |x| + |y| \le \sqrt 2 \max(|x|, |y|).$$
Hence the map $z \mapsto (x, y)$ is a linear homeomorphism $\mathbb{C} \to \mathbb{R} \times \mathbb{R}$, for the max norm on $\mathbb{R} \times \mathbb{R}$. It is $1$-Lipschitz, and its inverse is $\sqrt 2$-Lipschitz.

*Proof.* Since $y^2 \ge 0$, $x^2 \le x^2 + y^2$, so $|x| \le |z|$; the same holds for $y$. Next $(|x| + |y|)^2 = x^2 + y^2 + 2|x||y| \ge x^2 + y^2$, so $|z| \le |x| + |y|$. Finally, with $m = \max(|x|,|y|)$, $x^2 + y^2 \le 2m^2$, so $|z| \le \sqrt 2\, m$. The first inequality says that the map to $\mathbb{R} \times \mathbb{R}$ is $1$-Lipschitz, and the last says that its inverse is $\sqrt 2$-Lipschitz. A Lipschitz bijection with a Lipschitz inverse is a homeomorphism. $\square$

**Theorem (Completeness and compactness).** $\mathbb{C}$ is complete. A closed bounded subset of $\mathbb{C}$ is compact.

*Proof.* Let $(z_n)$ be a Cauchy sequence, $z_n = x_n + i y_n$. Since $|x_n - x_m| \le |z_n - z_m|$, the real parts form a Cauchy sequence, with a limit $x$ (Volume 15, Chapter 1); the imaginary parts have a limit $y$. Then $|z_n - (x + iy)| \le |x_n - x| + |y_n - y| \to 0$.

Let $K \subseteq \mathbb{C}$ be closed and bounded, with $|z| \le R$ on $K$. Its image in $\mathbb{R} \times \mathbb{R}$ is closed and lies in the square $[-R, R]^2$, which is compact (Volume 13). A closed subset of a compact set is compact, and the inverse map is continuous, so $K$ is compact. $\square$

**Theorem (Continuous ring homomorphisms).** Let $f : \mathbb{C} \to \mathbb{C}$ be a continuous ring homomorphism. Then $f$ is the identity or conjugation.

*Proof.* A ring homomorphism maps $1$ to $1$, so $f(n) = n$ for every integer $n$. For a rational $p/q$, $q f(p/q) = f(p) = p$, so $f(p/q) = p/q$. The rationals are dense in $\mathbb{R}$, and $f$ is continuous, so $f(x) = x$ for every real $x$. Next $f(i)^2 = f(i^2) = f(-1) = -1$, so $f(i) = i$ or $f(i) = -i$. In the first case $f(x + iy) = f(x) + f(i) f(y) = x + iy$, and $f$ is the identity. In the second case $f(x + iy) = x - iy$, and $f$ is conjugation. $\square$

Without continuity the result is false: with the axiom of choice, $\mathbb{C}$ has other field automorphisms.

::: mathlib
`Complex.ringHom_eq_id_or_conj_of_continuous` · `Mathlib.Analysis.Complex.Basic`

The statement is `{f : ℂ →+* ℂ} → Continuous f → f = RingHom.id ℂ ∨ f = starRingEnd ℂ`. Mathlib writes conjugation as `starRingEnd ℂ`, and the notation `conj` is available after `open ComplexConjugate`. The isometry property is `Complex.isometry_conj`, and the bundled real linear isometry is `Complex.conjLIE : ℂ ≃ₗᵢ[ℝ] ℂ`.

<?decl Complex.ringHom_eq_id_or_conj_of_continuous?>
:::

**Theorem (Real linear isometries).** Let $f : \mathbb{C} \to \mathbb{C}$ be a real linear map with $|f(z)| = |z|$ for all $z$. Then there is $a$ with $|a| = 1$ such that $f(z) = az$ for all $z$, or $f(z) = a \bar z$ for all $z$.

*Proof.* Put $a = f(1)$. Then $|a| = |1| = 1$, so $a \ne 0$ and $a^{-1} = \bar a$. The map $g(z) = \bar a f(z)$ is real linear, and $|g(z)| = |f(z)| = |z|$ by the multiplicative norm. Also $g(1) = 1$. Put $w = g(i)$. Then $|w| = 1$ and $|w - 1| = |g(i - 1)| = |i - 1| = \sqrt 2$. Expand the second equation with $w = u + iv$:
$$2 = (u - 1)^2 + v^2 = u^2 + v^2 - 2u + 1 = 2 - 2u.$$
So $u = 0$, and then $v^2 = 1$, so $w = i$ or $w = -i$. Real linearity gives $g(x + iy) = x + y\,w$. If $w = i$ then $g$ is the identity and $f(z) = az$. If $w = -i$ then $g$ is conjugation and $f(z) = a \bar z$. $\square$

::: mathlib
`linear_isometry_complex` · `Mathlib.Analysis.Complex.Isometry`

For `f : ℂ ≃ₗᵢ[ℝ] ℂ` it gives `∃ a, f = rotation a ∨ f = conjLIE.trans (rotation a)`. Here `a : Circle`, the unit circle of Section 2, and `rotation : Circle →* ℂ ≃ₗᵢ[ℝ] ℂ` is a group homomorphism with `rotation_apply : rotation a z = ↑a * z`. The step $\operatorname{Re} g(z) = \operatorname{Re} z$ for an isometry with $g(1) = 1$ is `LinearIsometry.re_apply_eq_re`.

<?decl linear_isometry_complex?>
:::

**Theorem (The order).** The relation $\le$ is a partial order on $\mathbb{C}$. It is not total, and $0 \le z^2$ holds only when $z$ is real.

*Proof.* The order axioms follow from those of $\le$ and $=$ on $\mathbb{R}$, coordinate by coordinate. The numbers $0$ and $i$ are not comparable. Next $\operatorname{Im}(z^2) = 2xy$ and $\operatorname{Re}(z^2) = x^2 - y^2$. If $0 \le z^2$ then $xy = 0$ and $x^2 \ge y^2$, which forces $y = 0$. Conversely a real $z$ has $z^2 \ge 0$. $\square$

::: mathlib
`Complex.le_def` · `Mathlib.Analysis.Complex.Order`

The statement is `z ≤ w ↔ z.re ≤ w.re ∧ z.im = w.im`. The instance `Complex.partialOrder` is scoped: it is active only after `open ComplexOrder`. The helper lemmas are `Complex.nonneg_iff`, `Complex.lt_def`, `Complex.not_le_iff`, `Complex.real_le_real` and `Complex.sq_nonneg_iff : 0 ≤ z ^ 2 ↔ z.im = 0`.

<?decl Complex.le_def?>
:::

### Examples

**Example.** $|3 + 4i| = 5$ and $|1 - i| = \sqrt 2$. The product is $(3 + 4i)(1 - i) = 7 + i$, and $|7 + i| = \sqrt{50} = 5\sqrt 2$, as the multiplicative norm predicts.

**Example.** Let $R = [0, 1] \times [0, 2]$ in the plane, that is the set of $z$ with $\operatorname{Re} z \in [0,1]$ and $\operatorname{Im} z \in [0,2]$. Its interior is $(0,1) \times (0,2)$, and its frontier is
$$\big([0,1] \times \{0, 2\}\big) \cup \big(\{0, 1\} \times [0, 2]\big),$$
the four sides of the rectangle. Chapter 2 integrates over this boundary.

### The library around it

::: mathlib
`Complex.instCompleteSpace` · `Mathlib.Analysis.Complex.Basic`

Completeness is an instance, so `CompleteSpace ℂ` is found by type class search. So is `Complex.instProperSpace`: closed balls are compact. The comparison with coordinates is `Complex.equivRealProdCLM : ℂ ≃L[ℝ] ℝ × ℝ`, with `Complex.lipschitz_equivRealProd` (constant `1`) and `Complex.antilipschitz_equivRealProd` (constant `NNReal.sqrt 2`). The inequalities are `Complex.abs_re_le_norm`, `Complex.abs_im_le_norm`, `Complex.norm_le_abs_re_add_abs_im` and `Complex.norm_le_sqrt_two_mul_max`.

<?decl Complex.instCompleteSpace?>
:::

Mathlib writes the set $\{z : \operatorname{Re} z \in s,\ \operatorname{Im} z \in t\}$ as `s ×ℂ t` (the definition `Set.reProdIm`). The lemmas `Complex.closure_reProdIm`, `Complex.interior_reProdIm` and `Complex.frontier_reProdIm` compute closure, interior and frontier, and `Complex.closure_setOfPred_re_lt` gives $\overline{\{\operatorname{Re} z < a\}} = \{\operatorname{Re} z \le a\}$. The map `Complex.re` is continuous (`Complex.continuous_re`) and open (`Complex.isOpenMap_re`).

Common errors of a learner:

- Writing `Complex.abs z`. Use `‖z‖`. The lemma names follow: `Complex.norm_mul`, `Complex.norm_conj`, `Complex.dist_eq_re_im`.
- Working with the square root. Square first: `Complex.sq_norm` turns `‖z‖ ^ 2` into `normSq z`, a polynomial in `z.re` and `z.im`.
- Expecting `z ≤ w` to typecheck without `open ComplexOrder`. The order is scoped on purpose.

### Exercises

1. (A) Compute $|(1 + i)^{10}|$ and $(1 + i)^{10}$. Hint: $(1 + i)^2 = 2i$.
2. (A) Show that $|z + w|^2 + |z - w|^2 = 2|z|^2 + 2|w|^2$. Hint: expand with $|u|^2 = u \bar u$.
3. (B) Show that $|z - w| = |1 - \bar w z|$ when $|w| = 1$. Hint: multiply $z - w$ by $\bar w$.
4. (B) Show that the partial order of $\mathbb{C}$ is closed: the set $\{(z, w) : z \le w\}$ is closed in $\mathbb{C} \times \mathbb{C}$. Hint: write it with continuous functions.
5. (C) Let $f : \mathbb{C} \to \mathbb{C}$ be a map with $|f(z) - f(w)| = |z - w|$ for all $z, w$, not assumed linear. Show that $f(z) = az + b$ or $f(z) = a\bar z + b$ with $|a| = 1$. Hint: $g = f - f(0)$ preserves norms and distances, so it preserves $\operatorname{Re}(z \bar w)$. Deduce that $g$ is real linear, then use the classification.
6. (C) Show that no total order on $\mathbb{C}$ makes $\mathbb{C}$ an ordered field. Hint: in an ordered field, $i^2 \ge 0$.

### Notes and history

The picture of complex numbers as points of the plane goes back to Wessel, Argand and Gauss. Hamilton defined them as pairs of real numbers in 1837. Mathlib uses this definition, with fields `re` and `im`.

### Reference

<?reference?>
