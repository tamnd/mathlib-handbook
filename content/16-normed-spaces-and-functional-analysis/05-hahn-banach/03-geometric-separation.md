---
title: Geometric separation
kind: theory
modules:
  - Mathlib.Analysis.Convex.Gauge
  - Mathlib.Analysis.LocallyConvex.Separation
explains:
  E3: [separate_convex_open_set, geometric_hahn_banach_open, geometric_hahn_banach_compact_closed]
  E2: [gauge, gauge_add_le, gauge_lt_one_of_mem_of_isOpen, geometric_hahn_banach_open_open, geometric_hahn_banach_point_closed, geometric_hahn_banach_closed_point, RCLike.geometric_hahn_banach_closed_point, iInter_halfSpaces_eq]
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

## Geometric separation

### Overview

The theorem of Hahn-Banach has a geometric form. A convex open set and a convex set that do not meet lie on the two sides of a closed hyperplane, and a compact convex set and a closed convex set that do not meet are strictly separated. The bridge from the analytic form of Section 1 is the gauge of a convex open set, a sublinear functional whose sublevel set below $1$ is the set. This section proves the forms for real normed spaces and gives the corollary that a closed convex set is the intersection of the closed half-spaces that contain it. Mathlib states the geometric forms for real topological vector spaces, with a locally convex hypothesis where the proof needs it, and gives complex versions through the real part.

### Definitions

In this section $E$ is a real normed space and $E^*$ its dual. The results hold for complex spaces with $\operatorname{Re} f$ in place of $f$.

**Definition (convex set).** A subset $C$ of a real vector space is *convex* if $tx + (1 - t)y \in C$ for all $x, y \in C$ and $t \in [0, 1]$. In Mathlib this is `Convex ℝ C`.

**Definition (gauge).** Let $C$ be a subset of a real vector space $E$. The *gauge*, or Minkowski functional, of $C$ is
$$p_C(x) = \inf\{t > 0 : x \in tC\},$$
with the convention that the infimum of the empty set is $0$, the convention of Mathlib.

::: mathlib
`gauge` · `Mathlib.Analysis.Convex.Gauge`

`gauge s x` is the infimum of `{r | 0 < r ∧ x ∈ r • s}` as a real number. Since `sInf ∅ = 0` in `ℝ`, the gauge is `0` at a vector that no multiple of `s` absorbs. The lemmas of the file assume `Absorbent ℝ s`, which removes this case. An open set that contains `0` is absorbent, by `absorbent_nhds_zero`.

<?decl gauge?>
:::

**Definition (half-space).** A *closed half-space* of $E$ is a set $\{x : f(x) \le c\}$ with $f \in E^*$, $f \ne 0$ and $c \in \mathbb{R}$. Two sets $A$ and $B$ are *separated* by $f$ if there is $u$ with $f(a) \le u \le f(b)$ for $a \in A$ and $b \in B$, and *strictly separated* if there are $u < v$ with $f(a) < u$ and $v < f(b)$.

### Theorems and proofs

**Lemma (gauge of a convex open set).** Let $E$ be a real normed space and $C \subseteq E$ convex and open with $0 \in C$. Then $p_C$ is sublinear, $C = \{x : p_C(x) < 1\}$, and there is $r > 0$ with $p_C(x) \le \|x\| / r$ for each $x$.

*Proof.* Pick $r > 0$ with $B(0, r) \subseteq C$. For $x \ne 0$ and $t > \|x\|/r$, $\|x/t\| < r$, so $x \in tC$ and $p_C(x) \le \|x\|/r$. This bound also holds at $x = 0$. For $s > 0$, $sx \in tC$ if and only if $x \in (t/s)C$, so $p_C(sx) = s\,p_C(x)$. For subadditivity let $x, y \in E$ and $\varepsilon > 0$. Pick $a < p_C(x) + \varepsilon$ and $b < p_C(y) + \varepsilon$ with $a, b > 0$ and $x \in aC$, $y \in bC$. Then
$$\frac{x + y}{a + b} = \frac{a}{a + b}\cdot\frac{x}{a} + \frac{b}{a + b}\cdot\frac{y}{b} \in C$$
by convexity, so $p_C(x + y) \le a + b < p_C(x) + p_C(y) + 2\varepsilon$. If $x \in C$, then $(1 + \delta)x \in C$ for a small $\delta > 0$ because $C$ is open, so $p_C(x) \le 1/(1 + \delta) < 1$. If $p_C(x) < 1$, then $x \in tC$ for some $t < 1$, and $x = t(x/t) + (1 - t)0 \in C$ by convexity. $\square$

::: mathlib
`gauge_add_le` · `Mathlib.Analysis.Convex.Gauge`

`gauge_add_le hs ha x y : gauge s (x + y) ≤ gauge s x + gauge s y` with `hs : Convex ℝ s` and `ha : Absorbent ℝ s`. Homogeneity is `gauge_smul_of_nonneg`. The bound `gauge_lt_one_of_mem_of_isOpen` gives `gauge s x < 1` for `x` in an open `s`, in any real topological vector space. The equality `{x | gauge s x < 1} = s` is `setOfPred_gauge_lt_one_eq_self_of_isOpen`, the current name of the deprecated `gauge_lt_one_eq_self_of_isOpen`.

<?decl gauge_add_le?>
:::

**Theorem (separation of a point from a convex open set).** Let $E$ be a real normed space, $C$ a convex open set with $0 \in C$, and $x_0 \notin C$. There is $f \in E^*$ with $f(x_0) = 1$ and $f(x) < 1$ for each $x \in C$.

*Proof.* Note $x_0 \ne 0$. Define $f_0(tx_0) = t$ on $\mathbb{R}x_0$. For $t > 0$, $p_C(tx_0) = t\,p_C(x_0) \ge t$, because $x_0 \notin C$ gives $p_C(x_0) \ge 1$ by the lemma. For $t \le 0$, $f_0(tx_0) = t \le 0 \le p_C(tx_0)$. So $f_0 \le p_C$ on $\mathbb{R}x_0$. The sublinear form of Section 1 extends $f_0$ to a linear $f$ on $E$ with $f \le p_C$. Then $f(x_0) = 1$, and for $x \in C$, $f(x) \le p_C(x) < 1$. The function $f$ is bounded: $f(x) \le p_C(x) \le \|x\|/r$ and $-f(x) = f(-x) \le \|x\|/r$, so $|f(x)| \le \|x\|/r$. $\square$

::: mathlib
`separate_convex_open_set` · `Mathlib.Analysis.LocallyConvex.Separation`

`separate_convex_open_set hs₀ hs₁ hs₂ hx₀ : ∃ f : StrongDual ℝ E, f x₀ = 1 ∧ ∀ x ∈ s, f x < 1` in any real topological vector space. The proof is the proof of the text with `exists_extension_of_le_sublinear` and `gauge s`. Without a norm, the continuity of `f` comes from `LinearMap.continuous_of_ne_zero_on_open` of `Mathlib.Topology.Algebra.Module.FiniteDimension`: a linear functional that has no zero on a nonempty open set is continuous.

<?decl separate_convex_open_set?>
:::

**Theorem (separation of a convex open set from a convex set).** Let $E$ be a real normed space, and let $A, B \subseteq E$ be convex and disjoint, with $A$ open. There are $f \in E^*$ and $u \in \mathbb{R}$ with $f(a) < u \le f(b)$ for all $a \in A$ and $b \in B$.

*Proof.* If $A$ or $B$ is empty, take $f = 0$ and a suitable $u$. Otherwise pick $a_0 \in A$, $b_0 \in B$, and let $x_0 = b_0 - a_0$ and $C = x_0 + (A - B)$. The set $A - B = \bigcup_{b \in B}(A - b)$ is open, and it is convex because $A$ and $B$ are convex, so $C$ is convex and open. It contains $x_0 + a_0 - b_0 = 0$. It does not contain $x_0$, because $x_0 \in C$ would give $0 \in A - B$, against $A \cap B = \emptyset$. The previous theorem gives $f \in E^*$ with $f(x_0) = 1$ and $f < 1$ on $C$. For $a \in A$, $b \in B$: $f(x_0) + f(a) - f(b) < 1$, so $f(a) < f(b)$. Let $u = \sup_{a \in A} f(a)$, which is finite and at most $f(b)$ for each $b$. The image $f(A)$ is an open subset of $\mathbb{R}$ because $f \ne 0$ is an open map, so the supremum is not attained and $f(a) < u$ for each $a \in A$. $\square$

::: mathlib
`geometric_hahn_banach_open` · `Mathlib.Analysis.LocallyConvex.Separation`

`geometric_hahn_banach_open hs₁ hs₂ ht disj : ∃ (f : StrongDual ℝ E) (u : ℝ), (∀ a ∈ s, f a < u) ∧ ∀ b ∈ t, u ≤ f b` with `hs₁ : Convex ℝ s`, `hs₂ : IsOpen s`, `ht : Convex ℝ t`. The proof is the proof of the text, with the set `x₀ +ᵥ (s - t)`. The variant `geometric_hahn_banach_open_open` with both sets open gives a strict inequality on both sides.

<?decl geometric_hahn_banach_open?>
:::

**Theorem (strict separation).** Let $E$ be a real normed space, and let $K, B \subseteq E$ be convex and disjoint, with $K$ compact and $B$ closed. There are $f \in E^*$ and $u < v$ with $f(k) < u$ for $k \in K$ and $v < f(b)$ for $b \in B$.

*Proof.* Assume $K$ and $B$ are nonempty; otherwise the statement is easy. The function $k \mapsto d(k, B)$ is continuous and positive on $K$, since $B$ is closed and $K \cap B = \emptyset$. By compactness it has a minimum $2r > 0$. Let $A = K + B(0, r)$. It is open, as a union of open balls, and convex, as a sum of convex sets. It does not meet $B$: if $k + z \in B$ with $\|z\| < r$, then $d(k, B) < r$. The previous theorem gives $f \in E^*$ and $w$ with $f < w$ on $A$ and $w \le f$ on $B$, and $f \ne 0$ since $A$ is nonempty. Let $u_0 = \max_K f$, which exists since $K$ is compact. Pick $z$ with $\|z\| < r$ and $f(z) > 0$; it exists because $f \ne 0$. For $k \in K$ with $f(k) = u_0$, the point $k + z$ is in $A$, so $u_0 < u_0 + f(z) < w$. Take $u$ and $v$ with $u_0 < u < v < w$. $\square$

::: mathlib
`geometric_hahn_banach_compact_closed` · `Mathlib.Analysis.LocallyConvex.Separation`

`geometric_hahn_banach_compact_closed hs₁ hs₂ ht₁ ht₂ disj : ∃ (f : StrongDual ℝ E) (u v : ℝ), (∀ a ∈ s, f a < u) ∧ u < v ∧ ∀ b ∈ t, v < f b`, with `s` convex and compact and `t` convex and closed, in a real locally convex space. In place of a ball Mathlib uses `Disjoint.exists_open_convexes`, which gives disjoint convex open sets `U ⊇ s` and `V ⊇ t`, then applies `geometric_hahn_banach_open_open` to `U` and `V` and takes the maximum of `f` on `s`. The special cases `geometric_hahn_banach_point_closed` and `geometric_hahn_banach_closed_point` take a point for one of the sets.

<?decl geometric_hahn_banach_compact_closed?>
:::

**Corollary (closed convex sets).** In a real normed space each closed convex set $C$ is the intersection of the closed half-spaces $\{x : f(x) \le c\}$ that contain it.

*Proof.* Each such half-space contains $C$, so the intersection contains $C$. If $x \notin C$, strict separation of the compact set $\{x\}$ from $C$ gives $f$ and $u < v$ with $f(x) < u$ and $v < f(c)$ for $c \in C$. Then $-f \le -v$ on $C$, and $-f(x) > -u > -v$. The half-space $\{-f \le -v\}$ contains $C$ and not $x$. $\square$

### Examples

**Example (separation in the plane).** Let $A = \{(a, b) : a^2 + b^2 < 1\}$ and $B = \{(a, b) : a \ge 1\}$. They are convex and disjoint, and $A$ is open. The functional $f(a, b) = a$ and $u = 1$ separate them: $f < 1$ on $A$ and $f \ge 1$ on $B$. No strict separation is possible, since $\sup_A f = 1 = \inf_B f$. This shows that the inequality $u \le f(b)$ in the open form can be an equality.

**Counterexample (two closed convex sets).** In $\mathbb{R}^2$ let $B_1 = \{(a, b) : b \le 0\}$ and $B_2 = \{(a, b) : a > 0, b \ge 1/a\}$. Both are closed and convex, and they are disjoint. For a functional $f(a, b) = \alpha a + \beta b$ with $f \le u$ on $B_1$, the half-plane $B_1$ forces $\alpha = 0$ and $\beta \ge 0$, so $f(a, b) = \beta b$. Then $\inf_{B_2} f = 0 = \sup_{B_1} f$. The two sets are separated by the line $b = 0$ but not strictly, so the compactness hypothesis in strict separation cannot be dropped.

**Counterexample (no separation without local convexity).** For $0 < p < 1$ the space $L^p[0, 1]$ of measurable functions with $\int_0^1 |f|^p < \infty$ is a complete metric vector space for $d(f, g) = \int_0^1 |f - g|^p$. Its only continuous linear functional is $0$. So the point $1$ and the closed convex set $\{0\}$ cannot be separated by a continuous functional. The space has no convex open set other than $\emptyset$ and the whole space, which is the reason. This is why Mathlib asks for `LocallyConvexSpace ℝ E` in strict separation.

### The library around it

The geometric forms are in `Mathlib.Analysis.LocallyConvex.Separation`, for a real topological vector space. The forms with an open set need only `IsTopologicalAddGroup E` and `ContinuousSMul ℝ E`, and the forms with a compact set or a closed set add `LocallyConvexSpace ℝ E`. A normed space has all three instances. The `RCLike` versions such as `RCLike.geometric_hahn_banach_closed_point` compare the real parts `re (f a)` for a complex functional `f`.

::: mathlib
`iInter_halfSpaces_eq` · `Mathlib.Analysis.LocallyConvex.Separation`

`iInter_halfSpaces_eq hs₁ hs₂ : ⋂ l : StrongDual ℝ E, {x | ∃ y ∈ s, l x ≤ l y} = s` for a closed convex `s` in a real locally convex space. Each set `{x | ∃ y ∈ s, l x ≤ l y}` contains the half-space `{x | l x ≤ sup l(s)}`, and it is the same set when the supremum is attained. The statement avoids a supremum that may be infinite.

<?decl iInter_halfSpaces_eq?>
:::

Common errors with these statements:

- `geometric_hahn_banach_open` gives `u ≤ f b`, not a strict inequality. The strict forms need either both sets open or one compact and one closed.
- The geometric forms are stated for `StrongDual ℝ E`. For a complex space, use the `RCLike.` versions or restrict the scalars to `ℝ` first.

### Exercises

1. (A) Compute the gauge of the open unit ball of a normed space, and of the open square $(-1, 1)^2$ in $\mathbb{R}^2$.
2. (A) In $\mathbb{R}^2$ with the Euclidean norm, find $f$ and $u$ with $f(a) < u \le f(x)$ for each $a$ in the open unit disc and $x = (2, 1)$.
3. (B) Let $C$ be a convex open bounded set with $0 \in C$ and $C = -C$ in a real normed space. Show that $p_C$ is a norm equivalent to the given norm.
4. (B) Show that the gauge of a convex set $C$ with $0 \in C$ need not be continuous if $C$ is not a neighbourhood of $0$. Hint: take $C = [0,1] \times \{0\}$ in $\mathbb{R}^2$.
5. (C) Let $K$ be a compact convex subset of a real normed space. Show that $K$ is the intersection of the closed half-spaces $\{f \le \max_K f\}$, $f \in E^*$.
6. (C) Let $C$ be a closed convex set in a real normed space and $(x_n)$ a sequence in $C$ with $f(x_n) \to f(x)$ for each $f \in E^*$. Show that $x \in C$.

### Notes and history

Stanisław Mazur published the geometric form of the theorem of Hahn-Banach, the separation of a point from a convex open set in a normed space, in 1933. The gauge is also called the Minkowski functional, after Hermann Minkowski, who used it in his work on convex bodies. The file `Mathlib.Analysis.LocallyConvex.Separation` has the authors Bhavik Mehta and Yaël Dillies, and the file `Mathlib.Analysis.Convex.Gauge` has the authors Yaël Dillies and Bhavik Mehta.

### Reference

<?reference?>
