---
title: Betweenness and sides
kind: theory
modules:
  - Mathlib.Analysis.Convex.Between
  - Mathlib.Analysis.Convex.BetweenList
  - Mathlib.Analysis.Convex.Side
explains:
  E3: [affineSegment, Wbtw, Sbtw, Wbtw.trans_left, wbtw_rotate_iff, Collinear.wbtw_or_wbtw_or_wbtw, List.Wbtw, AffineSubspace.WSameSide, AffineSubspace.SSameSide, AffineSubspace.WOppSide, AffineSubspace.SOppSide, AffineSubspace.wOppSide_iff_exists_wbtw]
  E2: [wbtw_comm, wbtw_self_left, wbtw_self_right, Wbtw.trans_right, Wbtw.collinear, Sbtw.not_rotate, List.Sbtw, List.wbtw_triple, List.exists_map_eq_of_sorted_iff_wbtw, AffineSubspace.SSameSide.trans, AffineSubspace.SOppSide.trans, AffineSubspace.SOppSide.exists_sbtw, AffineSubspace.sSameSide_self_iff]
  E1: auto
families: []
requires: [V07, V16.C05, V22.C01]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Betweenness and sides

### Overview

Over an ordered ring, a point $y$ is between $x$ and $z$ if $y$ is on the segment from $x$ to $z$. Mathlib calls this relation `Wbtw`, and the strict form `Sbtw`. They need no metric. This section proves the basic rules of betweenness and treats lists of points in order and the two sides of an affine subspace.

Throughout, $R$ is an ordered ring and $P$ an affine space over an $R$-module $V$, with the line map $\mathrm{lineMap}(x, z)(t) = t(z -_v x) +_v x$.

### Definitions

**Definition (segment, betweenness).** The *affine segment* from $x$ to $z$ is the set $\{\mathrm{lineMap}(x, z)(t) : 0 \le t \le 1\}$. The point $y$ is *weakly between* $x$ and $z$ if $y$ is in this segment. It is *strictly between* $x$ and $z$ if also $y \ne x$ and $y \ne z$.

::: mathlib
`Wbtw` · `Mathlib.Analysis.Convex.Between`

`Wbtw R x y z` is `y ∈ affineSegment R x z`, where `affineSegment R x y = lineMap x y '' Set.Icc (0 : R) 1`. `Sbtw R x y z` is `Wbtw R x y z ∧ y ≠ x ∧ y ≠ z`. The middle argument is the point between.

<?decl Wbtw?>
:::

**Definition (points in order on a line).** A list $[p_1, \dots, p_m]$ of points is *weakly in order* if $p_j$ is weakly between $p_i$ and $p_l$ for all $i < j < l$. It is *strictly in order* if also the points are pairwise distinct.

::: mathlib
`List.Wbtw` · `Mathlib.Analysis.Convex.BetweenList`

`List.Wbtw R l` is `l.Triplewise (Wbtw R)`, and `List.Sbtw R l` is `l.Wbtw R ∧ l.Pairwise (· ≠ ·)`. For three points, `List.wbtw_triple` reduces to `Wbtw`. By `List.exists_map_eq_of_sorted_iff_wbtw`, a list is weakly in order if and only if it is the image of a sorted list of scalars under a line map.

<?decl List.Wbtw?>
:::

**Definition (sides of a subspace).** Let $R$ be an ordered commutative ring and $s$ an affine subspace of $P$. The points $x$ and $y$ are *weakly on the same side* of $s$ if there are $p_1, p_2 \in s$ such that $x -_v p_1$ and $y -_v p_2$ are in the same ray. They are *weakly on opposite sides* if this holds with $p_2 -_v y$ in place of $y -_v p_2$. The strict forms add the conditions $x \notin s$ and $y \notin s$.

Two vectors $u$ and $v$ are in the same ray if one of them is $0$ or $u = r v$ for some $r > 0$ (Volume 16).

::: mathlib
`AffineSubspace.SSameSide` · `Mathlib.Analysis.Convex.Side`

`s.WSameSide x y` is `∃ p₁ ∈ s, ∃ p₂ ∈ s, SameRay R (x -ᵥ p₁) (y -ᵥ p₂)`, and `s.WOppSide x y` is the same with `p₂ -ᵥ y`. `s.SSameSide x y` is `s.WSameSide x y ∧ x ∉ s ∧ y ∉ s`, and `AffineSubspace.SOppSide` is defined in the same way.

<?decl AffineSubspace.SSameSide?>
:::

### Theorems and proofs

**Lemma (first rules).** For all $x, y, z$: $y$ is weakly between $x$ and $z$ if and only if it is weakly between $z$ and $x$. The ends $x$ and $z$ are weakly between $x$ and $z$. An affine map $f$ keeps betweenness: if $y$ is between $x$ and $z$, then $f(y)$ is between $f(x)$ and $f(z)$.

*Proof.* The map $t \mapsto 1 - t$ sends $[0, 1]$ onto itself, and $\mathrm{lineMap}(x, z)(t) = \mathrm{lineMap}(z, x)(1 - t)$. So the two segments are equal. The ends are the values at $t = 0$ and $t = 1$. Last, an affine map commutes with line maps, $f(\mathrm{lineMap}(x, z)(t)) = \mathrm{lineMap}(f(x), f(z))(t)$, by Section 2 of Chapter 1. $\square$

::: mathlib
`wbtw_comm` · `Mathlib.Analysis.Convex.Between`

`wbtw_comm : Wbtw R x y z ↔ Wbtw R z y x`, with the direction `Wbtw.symm`. The ends are `wbtw_self_left` and `wbtw_self_right`.

<?decl wbtw_comm?>
:::

**Theorem (transitivity).** If $y$ is weakly between $w$ and $z$, and $x$ is weakly between $w$ and $y$, then $x$ is weakly between $w$ and $z$.

*Proof.* Write $y = t_1(z -_v w) +_v w$ and $x = t_2(y -_v w) +_v w$ with $t_1, t_2 \in [0, 1]$. Then $y -_v w = t_1(z -_v w)$, so $x = t_2 t_1 (z -_v w) +_v w$. The product $t_2 t_1$ is in $[0, 1]$, since $0 \le t_2 t_1 \le t_1 \le 1$. $\square$

::: mathlib
`Wbtw.trans_left` · `Mathlib.Analysis.Convex.Between`

`Wbtw.trans_left (h₁ : Wbtw R w y z) (h₂ : Wbtw R w x y) : Wbtw R w x z`. The mirror form is `Wbtw.trans_right`.

<?decl Wbtw.trans_left?>
:::

**Theorem (no rotation).** Let $R$ be an ordered field. Then $y$ is between $x$ and $z$ and also $x$ is between $z$ and $y$ if and only if $x = y$.

*Proof.* If $x = y$, both hold by the first rules. Conversely, let $u = z -_v x$, $y -_v x = t u$ and $x -_v z = s(y -_v z)$ with $s, t \in [0, 1]$. Then $y -_v z = (t - 1)u$, so $(1 - s(1 - t))u = 0$. If $u = 0$, then $z = x$, and the segment from $x$ to $x$ is $\{x\}$, so $y = x$. Otherwise $s(1 - t) = 1$ with both factors in $[0, 1]$, so $t = 0$ and $y = x$. $\square$

::: mathlib
`wbtw_rotate_iff` · `Mathlib.Analysis.Convex.Between`

`wbtw_rotate_iff (x : P) : Wbtw R x y z ∧ Wbtw R z x y ↔ x = y`. The strict form is `Sbtw.not_rotate : Sbtw R x y z → ¬Wbtw R z x y`.

<?decl wbtw_rotate_iff?>
:::

**Theorem (three collinear points).** Let $R$ be a linearly ordered field. If $\{x, y, z\}$ is collinear, then one of the three points is weakly between the other two.

*Proof.* By Section 3, write $x = a v +_v o$, $y = b v +_v o$ and $z = c v +_v o$ for a vector $v$. One of $a, b, c$ is between the other two, say $a \le b \le c$. If $a < c$, then $y = \mathrm{lineMap}(x, z)(t)$ with $t = (b - a)/(c - a) \in [0, 1]$. If $a = c$, then $x = y = z$. The other cases are the same. $\square$

::: mathlib
`Collinear.wbtw_or_wbtw_or_wbtw` · `Mathlib.Analysis.Convex.Between`

`Collinear.wbtw_or_wbtw_or_wbtw (h : Collinear R {x, y, z}) : Wbtw R x y z ∨ Wbtw R y z x ∨ Wbtw R z x y`. The converse direction for one relation is `Wbtw.collinear`, and `Wbtw.mem_affineSpan` puts $y$ on the line through $x$ and $z$.

<?decl Collinear.wbtw_or_wbtw_or_wbtw?>
:::

**Theorem (opposite sides through a segment).** Let $R$ be a linearly ordered field. Then $x$ and $y$ are weakly on opposite sides of $s$ if and only if there is $p \in s$ weakly between $x$ and $y$.

*Proof.* If $p \in s$ and $p -_v x = t(y -_v x)$ with $t \in [0, 1]$, take $p_1 = p_2 = p$: the vectors $x -_v p = t(x -_v y)$ and $p -_v y = (1 - t)(x -_v y)$ are in the same ray. Conversely, let $p_1, p_2 \in s$ with $x -_v p_1$ and $p_2 -_v y$ in the same ray. If one of them is $0$, take $p = x$ or $p = y$. Otherwise $x -_v p_1 = r_1 v$ and $p_2 -_v y = r_2 v$ with $r_1, r_2 > 0$. With a base point $o$ and $\bar q = q -_v o$, $r_2 \bar x + r_1 \bar y = r_2 \bar p_1 + r_1 \bar p_2$. So the point $p$ with $\bar p = (r_2 \bar x + r_1 \bar y)/(r_1 + r_2)$ is $\mathrm{lineMap}(p_1, p_2)(\lambda) \in s$ and also $\mathrm{lineMap}(x, y)(\lambda)$, with $\lambda = r_1/(r_1 + r_2)$. $\square$

::: mathlib
`AffineSubspace.wOppSide_iff_exists_wbtw` · `Mathlib.Analysis.Convex.Side`

`s.WOppSide x y ↔ ∃ p ∈ s, Wbtw R x p y`. The strict form `AffineSubspace.SOppSide.exists_sbtw` gives a point of `s` strictly between `x` and `y`.

<?decl AffineSubspace.wOppSide_iff_exists_wbtw?>
:::

### Examples

**Example (a point between two points, and opposite sides of a line).** In $\mathbb{R}^2$, the point $(1, 1)$ is strictly between $(0, 0)$ and $(3, 3)$, with $t = \tfrac13$. Let $s$ be the $x$-axis, $x = (1, 2)$ and $y = (3, -1)$. The segment from $x$ to $y$ is $(1 + 2t, 2 - 3t)$, which meets $s$ at $t = \tfrac23$, in the point $(\tfrac73, 0)$. So $x$ and $y$ are strictly on opposite sides of $s$.

**Counterexample (an empty subspace has no sides).** If $s = \bot$, no $p_1 \in s$ exists, so no two points are weakly on the same side of $s$, not even $x$ and $x$. This is why `AffineSubspace.sSameSide_self_iff` reads `s.SSameSide x x ↔ (s : Set P).Nonempty ∧ x ∉ s`.

### The library around it

Over a linearly ordered field, `AffineSubspace.SSameSide.trans` gives transitivity of strictly the same side, and `AffineSubspace.SOppSide.trans` says that two strict opposite sides give the same side. Over $\mathbb{R}$, the set of points strictly on the same side as $x$ is connected, `AffineSubspace.isConnected_setOfPred_sSameSide`. `Affine.Simplex.mem_closedInterior_iff_wbtw` identifies the closed interior of a $1$-simplex with the segment.

### Exercises

1. (A) Show that $(2, 1)$ is strictly between $(0, -1)$ and $(3, 2)$ in $\mathbb{R}^2$, and find $t$.
2. (A) Show that $y$ is weakly between $x$ and $x$ if and only if $y = x$.
3. (A) Show that $x$ and $y$ are weakly on the same side of $s$ when $x \in s$. Hint: take $p_1 = x$.
4. (B) In $\mathbb{R}^2$, let $s$ be the line $\alpha a + \beta b + \gamma = 0$ with $(\alpha, \beta) \ne 0$, and $f(a, b) = \alpha a + \beta b + \gamma$. Show that two points not in $s$ are strictly on the same side of $s$ if and only if $f$ has the same sign at both points.
5. (B) Show that if $y$ is strictly between $x$ and $z$, then $x \ne z$.
6. (C) Let $R$ be a linearly ordered field. Show that if $x$ and $y$ are strictly on opposite sides of $s$, and $y$ and $z$ are strictly on opposite sides of $s$, then $x$ and $z$ are strictly on the same side. Hint: follow `AffineSubspace.SOppSide.trans`.

### Notes and history

Betweenness as a primitive notion of geometry goes back to the axioms of Pasch and Hilbert. In Mathlib it is defined from line maps, and the axioms become theorems.

### Reference

<?reference?>
