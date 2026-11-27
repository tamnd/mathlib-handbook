---
title: Normed fields and normed spaces
kind: theory
modules:
  - Mathlib.Analysis.Normed.Field.Basic
  - Mathlib.Analysis.Normed.Module.Basic
  - Mathlib.Analysis.Normed.MulAction
  - Mathlib.Analysis.Normed.Module.RCLike.Real
  - Mathlib.Analysis.Normed.Lp.WithLp
  - Mathlib.Analysis.Normed.Lp.PiLp
explains:
  E3: [NormedField, NontriviallyNormedField, NormedSpace, norm_smul, PiLp]
  E2: [norm_smul_le, NormedField.exists_one_lt_norm, NormedSpace.exists_lt_norm, NormedSpace.unbounded_univ, norm_smul_of_nonneg, closure_ball, WithLp, PiLp.norm_eq_sum, PiLp.norm_eq_of_L1, PiLp.norm_eq_of_L2, PiLp.norm_eq_ciSup]
  E1: auto
families: []
requires: [V02, V07, V13, V15]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Normed fields and normed spaces

### Overview

A normed space is a vector space over a field of scalars with a norm, such that scaling a vector by $c$ multiplies its norm by $|c|$. To state this the field itself needs a norm, so the section starts with normed fields. The scalar fields of this volume are $\mathbb{R}$ and $\mathbb{C}$, which Mathlib groups in the class `RCLike`, but most definitions work over any field with a multiplicative norm. The section proves the basic geometry of a normed space: balls are convex, the closure of an open ball is the closed ball, and the space is unbounded. It then compares the norms $\|\cdot\|_1$, $\|\cdot\|_2$ and $\|\cdot\|_\infty$ on $\mathbb{R}^n$ and explains the type `PiLp p` that Mathlib uses to put the $p$-norm on a product.

### Definitions

**Definition (Normed field).** A *normed field* is a field $K$ with a norm $|\cdot|$ on its additive group that is multiplicative: $|ab| = |a||b|$. It is *nontrivially normed* if some $a \in K$ has $|a| > 1$.

The real and the complex numbers with the absolute value are nontrivially normed fields. Each field has the *trivial norm*, $|a| = 1$ for $a \neq 0$ and $|0| = 0$, and this norm is excluded by the second condition. The field $\mathbb{Q}_p$ of $p$-adic numbers with $|p|_p = 1/p$ is nontrivially normed, since $|1/p|_p = p > 1$. In a nontrivially normed field the powers $a^n$ of an element with $|a| > 1$ have $|a^n| = |a|^n \to \infty$ and $|a^{-n}| \to 0$. So there are scalars of arbitrarily large and arbitrarily small nonzero norm, and many proofs rescale a vector with them.

::: mathlib
`NormedField` · `Mathlib.Analysis.Normed.Field.Basic`

The class extends `Norm α`, `Field α` and `MetricSpace α`, with the fields `dist_eq` and `norm_mul`, as a normed group does in Section 1. The lemma `norm_mul` of `Mathlib.Analysis.Normed.Ring.Basic` states the multiplicativity, and `norm_inv` gives $|a^{-1}| = |a|^{-1}$.

<?decl NormedField?>
:::

::: mathlib
`NontriviallyNormedField` · `Mathlib.Analysis.Normed.Field.Basic`

It adds the field `non_trivial : ∃ x, 1 < ‖x‖`. The lemma `NormedField.exists_one_lt_norm` extracts such an element. The open mapping theorem, the operator norm and the equivalence of norms in finite dimension all ask for a `NontriviallyNormedField`, because their proofs rescale.

<?decl NontriviallyNormedField?>
:::

**Definition (The class RCLike).** Many results hold for $K = \mathbb{R}$ and $K = \mathbb{C}$ with the same proof, using the real part, the imaginary part and the conjugation. Mathlib collects these in the class `RCLike K`: a nontrivially normed field that is a normed algebra over $\mathbb{R}$, with a conjugation $\bar z$, the maps $\operatorname{Re}$ and $\operatorname{Im}$ to $\mathbb{R}$ and an element $I$ with $z = \operatorname{Re} z + \operatorname{Im} z \cdot I$. For $K = \mathbb{R}$ the conjugation is the identity and $I = 0$. For $K = \mathbb{C}$ they are the usual ones. The inner product spaces of Chapter 6 are defined over an `RCLike` field.

::: mathlib
`RCLike` · `Mathlib.Analysis.RCLike.Basic`

The instances are `Real.instRCLike` and `Complex.instRCLike`. The lemma `RCLike.re_add_im` states `↑(re z) + ↑(im z) * I = z`, and `RCLike.norm_sq_eq_def` states `‖z‖ ^ 2 = re z * re z + im z * im z`. The conjugation appears as `starRingEnd K`, written `conj` in the text.

<?decl RCLike?>
:::

**Definition (Normed space).** Let $K$ be a normed field. A *normed space* over $K$ is a vector space $E$ over $K$ with a seminorm $\|\cdot\|$ on its additive group such that
$$\|c x\| \le |c| \, \|x\| \quad \text{for all } c \in K, \ x \in E.$$

The axiom is an inequality, and the equality follows. Let $c \neq 0$. Then $x = c^{-1}(cx)$, so $\|x\| \le |c|^{-1} \|cx\|$, that is $|c|\,\|x\| \le \|cx\|$. For $c = 0$ both sides are $0$. So $\|cx\| = |c|\,\|x\|$ for all $c$ and $x$. The inequality is easier to check in an instance, and it is the form that makes sense for a module over a normed ring, where scalars need not be invertible.

::: mathlib
`NormedSpace` · `Mathlib.Analysis.Normed.Module.Basic`

`NormedSpace 𝕜 E` takes `[NormedField 𝕜] [SeminormedAddCommGroup E]` as parameters and extends `Module 𝕜 E` with one field, `norm_smul_le : ∀ a b, ‖a • b‖ ≤ ‖a‖ * ‖b‖`. The norm and the metric of `E` are not part of `NormedSpace`: they come from the group. So the same type can carry one norm and several scalar fields, for example a complex space is also a real normed space. A normed field is a normed space over itself by `NormedField.toNormedSpace`, and products and finite functions have the instances `Prod.normedSpace` and `Pi.normedSpace`.

<?decl NormedSpace?>
:::

### Theorems and proofs

**Theorem (Homogeneity).** In a normed space, $\|cx\| = |c|\,\|x\|$. So $\|x\|$ is determined by its values on one vector of each line.

*Proof.* This is the computation after the definition. $\square$

::: mathlib
`norm_smul` · `Mathlib.Analysis.Normed.MulAction`

`‖r • x‖ = ‖r‖ * ‖x‖`, under a class `NormSMulClass α β` that a normed space over a normed field satisfies. The axiom itself is `norm_smul_le`, under the weaker class `IsBoundedSMul`. For a real space and $t \ge 0$, `norm_smul_of_nonneg` gives `‖t • x‖ = t * ‖x‖` with no absolute value.

<?decl norm_smul?>
:::

**Theorem (Geometry of balls).** Let $E$ be a real or complex normed space and $r > 0$.

1. The scalar multiplication $K \times E \to E$ is continuous.
2. The ball $B(a, r)$ is convex: if $x, y \in B(a, r)$ and $0 \le t \le 1$, then $(1 - t)x + ty \in B(a, r)$.
3. The closure of $B(a, r)$ is the closed ball $\bar B(a, r) = \{x : \|x - a\| \le r\}$.
4. If $E \neq 0$ and $E$ is a normed space (not only seminormed), then $E$ is unbounded.

*Proof.* (1) Write $c'x' - cx = (c' - c)x' + c(x' - x)$. Then
$$\|c'x' - cx\| \le |c' - c|\,\|x'\| + |c|\,\|x' - x\| \le |c' - c|(\|x\| + \|x' - x\|) + |c|\,\|x' - x\|,$$
by the triangle inequality, homogeneity and $\|x'\| \le \|x\| + \|x' - x\|$. The right side tends to $0$ when $c' \to c$ and $x' \to x$.

(2) $\|(1 - t)x + ty - a\| = \|(1 - t)(x - a) + t(y - a)\| \le (1 - t)\|x - a\| + t\|y - a\| < (1 - t)r + tr = r$, by the triangle inequality and homogeneity with $1 - t, t \ge 0$.

(3) The closed ball is closed, since the norm is continuous (Section 1), and it contains $B(a, r)$. So the closure is inside it. Conversely let $\|x - a\| = r$. For $0 < t < 1$ put $x_t = a + t(x - a)$. Then $\|x_t - a\| = tr < r$, so $x_t \in B(a, r)$, and $\|x_t - x\| = (1 - t)r \to 0$ as $t \to 1$. So $x$ is in the closure.

(4) Choose $x \neq 0$, so $\|x\| > 0$. For $n \in \mathbb{N}$ the vector $nx$ has norm $n\|x\|$, which is not bounded. $\square$

Part 3 fails in a general metric space. With the discrete metric, $B(a, 1) = \{a\}$ is closed and the closed ball $\bar B(a, 1)$ is the whole space. The proof uses the segment from $a$ to $x$, which a vector space has and a metric space has not.

::: mathlib
`closure_ball` · `Mathlib.Analysis.Normed.Module.RCLike.Real`

`r ≠ 0 → closure (ball x r) = closedBall x r` in a real normed space. The hypothesis is `r ≠ 0`, not `0 < r`: for `r < 0` both sides are empty. The companion is `interior_closedBall`. Convexity of balls is `convex_ball` in `Mathlib.Analysis.Normed.Module.Convex`.

<?decl closure_ball?>
:::

::: mathlib
`NormedSpace.unbounded_univ` · `Mathlib.Analysis.Normed.Module.Basic`

`¬Bornology.IsBounded Set.univ` for a nontrivial normed space over a nontrivially normed field. The form with a bound is `NormedSpace.exists_lt_norm`: for each `c` there is `x` with `c < ‖x‖`. The field must be nontrivially normed. Over a field with the trivial norm, the scalar multiples of a vector of norm $1$ all have norm $\le 1$.

<?decl NormedSpace.unbounded_univ?>
:::

**Definition (The $p$-norms on $K^n$).** For $x \in K^n$ and $1 \le p < \infty$ put
$$\|x\|_p = \Bigl(\sum_{i=1}^n |x_i|^p\Bigr)^{1/p}, \qquad \|x\|_\infty = \max_i |x_i|.$$

These are norms. For $p = 1$ and $p = \infty$ the triangle inequality follows from that of $|\cdot|$ term by term. For $p = 2$ it follows from the inequality of Cauchy-Schwarz, which Chapter 6 proves for any inner product. For general $p$ it is the inequality of Minkowski, whose proof uses the inequality of Hölder (Volume 15, which has the mean inequalities in `Mathlib.Analysis.MeanInequalities`). For $0 < p < 1$ the formula is not a norm: in $\mathbb{R}^2$ with $p = 1/2$, $\|(1, 0)\|_p = \|(0, 1)\|_p = 1$ and $\|(1, 1)\|_p = (1 + 1)^2 = 4 > 2$.

**Theorem (Comparison of the norms on $K^n$).** For $x \in K^n$,
$$\|x\|_\infty \le \|x\|_2 \le \|x\|_1 \le \sqrt{n}\,\|x\|_2 \le n\,\|x\|_\infty.$$

*Proof.* Let $m = \max_i |x_i|$, attained at $i = j$. First, $m^2 = |x_j|^2 \le \sum_i |x_i|^2$, so $\|x\|_\infty \le \|x\|_2$. Second,
$$\Bigl(\sum_i |x_i|\Bigr)^2 = \sum_i |x_i|^2 + \sum_{i \neq k} |x_i||x_k| \ge \sum_i |x_i|^2,$$
so $\|x\|_2 \le \|x\|_1$. Third, the inequality of Cauchy-Schwarz in $\mathbb{R}^n$ for the vectors $(|x_1|, \dots, |x_n|)$ and $(1, \dots, 1)$ gives $\sum_i |x_i| \cdot 1 \le \bigl(\sum_i |x_i|^2\bigr)^{1/2} n^{1/2}$. Fourth, $\sum_i |x_i|^2 \le n m^2$, so $\sqrt n \|x\|_2 \le \sqrt n \sqrt n\, m = n m$. $\square$

So the three norms define the same open sets, the same convergent sequences and the same Cauchy sequences. Chapter 3 proves that this holds for any two norms on a finite dimensional space. The constants are sharp: $x = (1, 0, \dots, 0)$ gives equality in the first two inequalities, and $x = (1, 1, \dots, 1)$ in the last two.

**Definition (The type `PiLp`).** Section 1 explains that Mathlib puts the maximum norm on the type `ι → K` and cannot put a second norm on the same type. For the $p$-norm, Mathlib uses a copy of the type: `WithLp p V` is a structure with one field `ofLp : V`, and `toLp p : V → WithLp p V` is its constructor. The type `PiLp p β` is `WithLp p ((i : ι) → β i)`, with the norm $\bigl(\sum_i \|f_i\|^p\bigr)^{1/p}$ for $0 < p < \infty$ and the supremum for $p = \infty$. Since it is a new structure, the instances of `ι → K` do not apply to it, and Lean does not confuse the two norms.

::: mathlib
`PiLp` · `Mathlib.Analysis.Normed.Lp.PiLp`

`PiLp p β` is an abbreviation for `WithLp p (∀ i, β i)`, with `p : ℝ≥0∞`. The instance `PiLp.normedAddCommGroup` needs `[Fact (1 ≤ p)]`, since for `p < 1` the formula is not a norm. The formulas are `PiLp.norm_eq_sum` (for `0 < p.toReal`), `PiLp.norm_eq_of_L1`, `PiLp.norm_eq_of_L2` with a square root, and `PiLp.norm_eq_ciSup` for `p = ⊤`. The Euclidean space `EuclideanSpace 𝕜 n` of Chapter 6 is `PiLp 2 (fun _ : n ↦ 𝕜)`.

<?decl PiLp?>
:::

::: mathlib
`WithLp` · `Mathlib.Analysis.Normed.Lp.WithLp`

`WithLp p V` is a structure with the constructor `WithLp.toLp p` and the projection `WithLp.ofLp`. A vector `x : V` becomes `WithLp.toLp p x`, and an element `f : PiLp p β` has coordinates `f.ofLp i`. The bundled equivalence `WithLp.equiv` gives the same maps as an `Equiv`. The structure is the same for products: `WithLp p (E × F)` has the norm $(\|x\|^p + \|y\|^p)^{1/p}$, in `Mathlib.Analysis.Normed.Lp.ProdLp`.

<?decl WithLp?>
:::

### Examples

**Example (Three norms of one vector).** Let $x = (3, -4, 12) \in \mathbb{R}^3$. Then $\|x\|_\infty = 12$, $\|x\|_2 = \sqrt{9 + 16 + 144} = 13$ and $\|x\|_1 = 19$. The chain of the theorem reads $12 \le 13 \le 19 \le 13\sqrt3 \approx 22.5 \le 36$.

**Example (The unit balls in the plane).** In $\mathbb{R}^2$ the closed unit ball of $\|\cdot\|_1$ is the square with vertices $(\pm1, 0)$ and $(0, \pm1)$, that of $\|\cdot\|_2$ is the round disc, and that of $\|\cdot\|_\infty$ is the square $[-1, 1]^2$. Each is convex and symmetric under $x \mapsto -x$, as part 2 of the theorem on balls predicts. The comparison theorem says that each ball contains a scaled copy of each other: $B_1 \subseteq B_2 \subseteq B_\infty \subseteq 2B_1$.

**Example (The complex numbers as a real space).** The field $\mathbb{C}$ is a normed space over $\mathbb{C}$ and over $\mathbb{R}$, with the same norm $|z|$. As a real space it is $\mathbb{R}^2$ with $\|\cdot\|_2$, since $|a + bi| = \sqrt{a^2 + b^2}$. In Mathlib both instances exist on the type `ℂ`, so a lemma about real normed spaces applies to `ℂ` directly.

**Counterexample (A field with the trivial norm).** Give $\mathbb{Q}$ the trivial norm and $E = \mathbb{Q}$ the norm $\|x\| = 1$ for $x \neq 0$. This is a normed space over the trivially normed field, since $\|cx\| = |c|\,\|x\|$ holds in all cases. The space is bounded: every vector has norm at most $1$. So part 4 of the theorem on balls needs a field with an element of norm $> 1$. The closure of the ball $B(0, 1) = \{0\}$ is $\{0\}$, not the closed ball $\mathbb{Q}$, so part 3 needs the real scalars of the segment.

### The library around it

The normed fields are in `Mathlib.Analysis.Normed.Field`, with the basic lemmas in `Basic` and `Lemmas`, and the normed rings, in which only $\|ab\| \le \|a\|\,\|b\|$ holds, in `Mathlib.Analysis.Normed.Ring`. A matrix ring and the ring of bounded operators of Chapter 2 are normed rings and not normed fields. The class `DenselyNormedField` asks that the norms are dense in $[0, \infty)$, which holds for $\mathbb{R}$ and $\mathbb{C}$ and not for $\mathbb{Q}_p$. The real geometry of balls and spheres is in `Mathlib.Analysis.Normed.Module.RCLike.Real` and `Mathlib.Analysis.Normed.Module.Ball`, with `smul_ball` for the image $c \cdot B(x, r) = B(cx, |c|r)$. The `WithLp` types come with the maps `WithLp.toLp` and `WithLp.ofLp` and simp lemmas that move between them: `PiLp.toLp_apply` and the like.

Common errors of a learner:

- Expecting the Euclidean norm on `Fin n → ℝ`. Its norm is $\|\cdot\|_\infty$; the Euclidean norm lives on `EuclideanSpace ℝ (Fin n)`.
- Forgetting the coercions `toLp` and `ofLp` when moving between `ι → K` and `PiLp p (fun _ ↦ K)`.
- Using a lemma for a `NontriviallyNormedField` over a field with the trivial norm.
- Taking $p < 1$ and expecting a norm.

### Exercises

1. (A) Compute $\|x\|_1$, $\|x\|_2$ and $\|x\|_\infty$ for $x = (1, -2, 2, 0) \in \mathbb{R}^4$ and check the chain of inequalities.
2. (A) Show that in a normed space $\|x\| = 1$ implies $\|cx\| = |c|$, and that each $x \neq 0$ is a multiple of a unit vector.
3. (A) Show that the closed ball $\bar B(a, r)$ of a real normed space is convex.
4. (B) Find the smallest $C$ with $\|x\|_1 \le C\|x\|_\infty$ on $\mathbb{R}^n$, and a vector that attains it.
5. (B) Show that $(c, x) \mapsto cx$ is continuous for any normed space over any normed field, with the estimate of the proof.
6. (B) Show that $\|x\|_p \to \|x\|_\infty$ as $p \to \infty$ for a fixed $x \in \mathbb{R}^n$. Hint: $m \le \|x\|_p \le n^{1/p} m$.
7. (C) Let $E$ be a real normed space. Show that the closed unit ball $\bar B$ is convex, symmetric, and that each line through $0$ meets it in a bounded segment. Conversely, let $C \subseteq \mathbb{R}^n$ be closed, convex, symmetric, bounded, with $0$ in its interior. Show that $\|x\| = \inf\{t > 0 : x \in tC\}$ is a norm with closed unit ball $C$.

### Notes and history

The $p$-norms on finite sequences go back to the inequalities of Hölder (1889) and Minkowski (1896). The axioms of a normed space over $\mathbb{R}$ or $\mathbb{C}$ were given in the early 1920s by Banach and, independently, by Wiener. The files `Mathlib.Analysis.Normed.Field.Basic` and `Mathlib.Analysis.Normed.Module.Basic` have the authors Patrick Massot and Johannes Hölzl, and `Mathlib.Analysis.Normed.Lp.PiLp` the authors Sébastien Gouëzel and Jireh Loreaux.

### Reference

<?reference?>
