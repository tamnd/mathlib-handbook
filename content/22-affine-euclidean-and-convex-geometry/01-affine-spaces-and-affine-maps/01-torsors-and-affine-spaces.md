---
title: Torsors and affine spaces
kind: theory
modules:
  - Mathlib.LinearAlgebra.AffineSpace.Defs
  - Mathlib.LinearAlgebra.AffineSpace.Midpoint
  - Mathlib.LinearAlgebra.AffineSpace.MidpointZero
  - Mathlib.Algebra.Order.AddTorsor
explains:
  E3: [Affine.termAffineSpace, midpoint, midpoint_eq_iff, AddMonoidHom.ofMapMidpoint, IsOrderedVAdd, IsOrderedCancelVAdd]
  E2: [midpoint_vsub_left, midpoint_vsub_midpoint, midpoint_eq_midpoint_iff_vsub_eq_vsub, AffineMap.map_midpoint, lineMap_one_half, homothety_one_half, IsOrderedSMul]
  E1: auto
families: []
requires: [V05.C06, V07]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Torsors and affine spaces

### Overview

An affine space is a set of points on which a vector space acts by translation, freely and transitively. Mathlib uses the additive torsor `AddTorsor V P` of Volume 5 for affine spaces. This section derives the rules of computation, treats the midpoint, and ends with order classes for actions.

### Definitions

**Definition (torsor).** Let $V$ be an additive group. An *additive torsor* over $V$ is a nonempty set $P$ with an action $V \times P \to P$, written $(v, p) \mapsto v +_v p$, and a map $P \times P \to V$, written $(p, q) \mapsto p -_v q$, such that $(p -_v q) +_v q = p$ and $(v +_v p) -_v p = v$ for all $p, q \in P$ and $v \in V$.

::: mathlib
`AddTorsor` · `Mathlib.Algebra.Torsor.Defs`

`AddTorsor G P` extends `AddAction G P` and `VSub G P`, and it has the fields `Nonempty P`, `vsub_vadd'` and `vadd_vsub'`. The group `G` is an `outParam`. The notation is `+ᵥ` for the action and `-ᵥ` for the difference.

<?decl AddTorsor?>
:::

**Definition (affine space).** Let $k$ be a ring and $V$ a module over $k$. An *affine space* over $V$ is an additive torsor $P$ over the additive group of $V$.

::: mathlib
`Affine.termAffineSpace` · `Mathlib.LinearAlgebra.AffineSpace.Defs`

After `open Affine`, the scoped notation `AffineSpace V P` stands for `AddTorsor V P`.

<?decl Affine.termAffineSpace?>
:::

**Definition (midpoint).** Let $k$ be a ring in which $2$ is invertible, and $P$ an affine space over a $k$-module $V$. The *midpoint* of $x, y \in P$ is $\operatorname{mid}(x, y) = \tfrac12 (y -_v x) +_v x$.

::: mathlib
`midpoint` · `Mathlib.LinearAlgebra.AffineSpace.Midpoint`

`midpoint R x y` is defined as `lineMap x y (⅟2 : R)`, the point at parameter one half on the line from `x` to `y`. The hypothesis is `[Ring R] [Invertible (2 : R)]`.

<?decl midpoint?>
:::

### Theorems and proofs

**Lemma (rules of computation).** In an additive torsor $P$ over $V$, for $p, q, r \in P$ and $v, w \in V$:

1. $p -_v p = 0$;
2. $(p -_v q) + (q -_v r) = p -_v r$ (Chasles);
3. $-(p -_v q) = q -_v p$;
4. $(v +_v p) -_v q = v + (p -_v q)$;
5. $v +_v p = w +_v p$ implies $v = w$, and $p -_v q = p -_v r$ implies $q = r$.

*Proof.* (1) By the second axiom, $p -_v p = (0 +_v p) -_v p = 0$. (4) Put $u = (v +_v p) -_v q$. Then $u +_v q = v +_v p = v +_v ((p -_v q) +_v q) = (v + (p -_v q)) +_v q$. The map $u \mapsto u +_v q$ is injective, since $p -_v q$ recovers $u$ from $u +_v q$, so $u = v + (p -_v q)$. (2) Apply (4) with $v = p -_v q$ and the point $q$ in place of $p$: $((p -_v q) +_v q) -_v r = (p -_v q) + (q -_v r)$, and the left side is $p -_v r$. (3) By (2) and (1), $(p -_v q) + (q -_v p) = p -_v p = 0$. (5) The first part follows by subtraction of $p$. For the second, $q = (q -_v p) +_v p = -(p -_v q) +_v p$ by (3), and the same holds for $r$. $\square$

**Theorem (characterization of the midpoint).** Let $2$ be invertible in $k$, and $x, y, z \in P$. Then $\operatorname{mid}(x, y) = z$ if and only if $y = 2(z -_v x) +_v x$, that is, if and only if the point reflection of $x$ in $z$ is $y$.

*Proof.* Put $m = \operatorname{mid}(x, y)$, so $m -_v x = \tfrac12(y -_v x)$. If $m = z$, then $2(z -_v x) = y -_v x$, so $2(z -_v x) +_v x = y$. Conversely, if $y = 2(z -_v x) +_v x$, then $y -_v x = 2(z -_v x)$ by rule (4), and $m -_v x = z -_v x$, so $m = z$ by rule (5). The reflection of $x$ in $z$ is $(z -_v x) +_v z = 2(z -_v x) +_v x$ by rule (4). $\square$

::: mathlib
`midpoint_eq_iff` · `Mathlib.LinearAlgebra.AffineSpace.Midpoint`

`midpoint_eq_iff : midpoint R x y = z ↔ pointReflection R z x = y`. Here `Equiv.pointReflection` comes from Volume 5. By `midpoint_unique`, the midpoint does not depend on the ring.

<?decl midpoint_eq_iff?>
:::

**Theorem (midpoints and vectors).** For $x, y, x', y' \in P$:

1. $\operatorname{mid}(x, y) -_v x = \tfrac12(y -_v x)$ and $\operatorname{mid}(x, y) -_v y = \tfrac12 (x -_v y)$;
2. $\operatorname{mid}(x, y) -_v \operatorname{mid}(x', y') = \tfrac12\big((x -_v x') + (y -_v y')\big)$;
3. $\operatorname{mid}(x, y) = \operatorname{mid}(x', y')$ if and only if $x -_v x' = y' -_v y$.

*Proof.* (1) The first claim is the definition and rule (4). For the second, $\operatorname{mid}(x, y) -_v y = \tfrac12(y -_v x) + (x -_v y) = \tfrac12(x -_v y)$ by rules (4), (2) and (3). (2) Write $m = \operatorname{mid}(x, y)$ and $m' = \operatorname{mid}(x', y')$. By Chasles, $m -_v m' = (m -_v x) + (x -_v x') + (x' -_v m')$. The same holds with $y$ and $y'$. Add the two equalities and use (1): the terms $(m -_v x) + (m -_v y)$ and $(x' -_v m') + (y' -_v m')$ are $0$. So $2(m -_v m') = (x -_v x') + (y -_v y')$. (3) By (2) and rule (5), $m = m'$ if and only if $(x -_v x') + (y -_v y') = 0$, that is, $x -_v x' = -(y -_v y') = y' -_v y$. $\square$

Part (3) is the parallelogram rule: the diagonals of the quadrilateral $x, y', y, x'$ bisect each other if and only if $x -_v x' = y' -_v y$, that is, if and only if two opposite sides are equal and parallel. In Mathlib the parts are `midpoint_vsub_left`, `midpoint_vsub_midpoint` and `midpoint_eq_midpoint_iff_vsub_eq_vsub`.

**Theorem (maps that preserve midpoints).** Let $E$ and $F$ be additive groups in which $2$ is invertible, for example modules over $\mathbb{Q}$. Let $f : E \to F$ satisfy $f(0) = 0$ and $f(\operatorname{mid}(x, y)) = \operatorname{mid}(f x, f y)$ for all $x, y$. Then $f$ is additive.

*Proof.* In a group, $\operatorname{mid}(x, y) = \tfrac12(x + y)$. With $y = 0$, $f(\tfrac12 x) = \tfrac12 f(x)$. For general $x, y$, $\tfrac12 f(x + y) = f(\tfrac12(x + y)) = f(\operatorname{mid}(x, y)) = \tfrac12(f x + f y)$. Multiply by $2$. $\square$

::: mathlib
`AddMonoidHom.ofMapMidpoint` · `Mathlib.LinearAlgebra.AffineSpace.Midpoint`

`AddMonoidHom.ofMapMidpoint R R' f h0 hm` builds an additive monoid hom from `f : E → F` with `f 0 = 0` and `∀ x y, f (midpoint R x y) = midpoint R' (f x) (f y)`. Mathlib uses it for the Mazur-Ulam theorem of Chapter 3.

<?decl AddMonoidHom.ofMapMidpoint?>
:::

Affine maps preserve midpoints, by `AffineMap.map_midpoint`.

### Examples

**Example (a group is a torsor over itself).** Each additive group $V$ is a torsor over itself, by addition and subtraction. In Lean this is the instance `AddGroup.instAddTorsor`. So in $\mathbb{R}^2$ the midpoint of $(1, 4)$ and $(5, 0)$ is $\tfrac12((5, 0) - (1, 4)) + (1, 4) = (3, 2)$.

**Example (an affine hyperplane).** Let $P = \{(x, y, z) \in \mathbb{R}^3 : x + y + z = 1\}$ and $V = \{v : v_1 + v_2 + v_3 = 0\}$. Then $V$ acts on $P$ by addition, and $p - q \in V$ for $p, q \in P$. So $P$ is an affine space over $V$. It is not a vector space, since $0 \notin P$. The midpoint of $(1, 0, 0)$ and $(0, 1, 0)$ is $(\tfrac12, \tfrac12, 0) \in P$.

**Counterexample (the hypothesis on 2 is needed).** Let $k = \mathbb{F}_2$ and $P = V = \mathbb{F}_2$. If a midpoint $m$ of $0$ and $1$ existed with $2(m -_v 0) = 1 -_v 0$, then $2m = 1$. But $2m = 0$ in $\mathbb{F}_2$. So no point of $\mathbb{F}_2$ has the defining property, and the definition of `midpoint` needs `Invertible (2 : R)`.

### The library around it

In `Mathlib.LinearAlgebra.AffineSpace.MidpointZero`, `lineMap_one_half` restates the definition in a division ring, and `homothety_one_half` says that the homothety of ratio one half with center $a$ maps $b$ to $\operatorname{mid}(a, b)$.

The file `Mathlib.Algebra.Order.AddTorsor` has order classes for actions. `IsOrderedVAdd G P` says that $a \le b$ implies $a +_v x \le b +_v x$, and $x \le y$ implies $a +_v x \le a +_v y$. `IsOrderedCancelVAdd G P` adds the converse rules. The multiplicative form is `IsOrderedSMul`. For an ordered torsor, the docstring says to combine `[AddTorsor G P]` with `[IsOrderedCancelVAdd G P]`.

::: mathlib
`IsOrderedCancelVAdd` · `Mathlib.Algebra.Order.AddTorsor`

`IsOrderedCancelVAdd G P` extends `IsOrderedVAdd G P`. Its fields are `le_of_vadd_le_vadd_left : ∀ (a : G) (b c : P), a +ᵥ b ≤ a +ᵥ c → b ≤ c` and `le_of_vadd_le_vadd_right : ∀ (a b : G) (c : P), a +ᵥ c ≤ b +ᵥ c → a ≤ b`.

<?decl IsOrderedCancelVAdd?>
:::

### Exercises

1. (A) Prove $v +_v (w +_v p) = (v + w) +_v p$ from the axioms of an action, and show that $p -_v q = 0$ implies $p = q$.
2. (A) Compute the midpoint of $(2, -1, 3)$ and $(0, 5, 1)$ in $\mathbb{R}^3$ and check the result with part (1) of the theorem on midpoints and vectors.
3. (A) Show that $\operatorname{mid}(x, x) = x$ and that $\operatorname{mid}(x, y) = x$ implies $x = y$.
4. (B) Prove the medial law $\operatorname{mid}(\operatorname{mid}(a, b), \operatorname{mid}(c, d)) = \operatorname{mid}(\operatorname{mid}(a, c), \operatorname{mid}(b, d))$. Hint: subtract $a$ from both sides.
5. (B) Let $a, b, c, d \in P$. Show that the midpoints of $ab$, $bc$, $cd$ and $da$ form a parallelogram (Varignon). Hint: use part (3) of the theorem on midpoints and vectors.
6. (C) Let $f : \mathbb{R} \to \mathbb{R}$ preserve midpoints and be bounded on $[0, 1]$. Show that $f$ is affine. Hint: $g = f - f(0)$ is additive, and an additive function bounded on an interval is linear.

### Notes and history

The file `Mathlib.LinearAlgebra.AffineSpace.Defs` has the author Joseph Myers. The file on midpoints has the author Yury Kudryashov, and the file on ordered actions has the author Scott Carnahan.

### Reference

<?reference?>
