---
title: Affine subspaces and spans
kind: theory
modules:
  - Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
  - Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
  - Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Range
  - Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Shift
  - Mathlib.LinearAlgebra.AffineSpace.Pointwise
  - Mathlib.LinearAlgebra.AffineSpace.Restrict
explains:
  E3: [AffineSubspace, vectorSpan, affineSpan, AffineSubspace.direction, AffineSubspace.mk', AffineSubspace.inter_nonempty_of_nonempty_of_sup_direction_eq_top, AffineSubspace.direction_sup, AffineSubspace.Parallel]
  E2: [spanPoints, direction_affineSpan, AffineSubspace.coe_direction_eq_vsub_set, AffineSubspace.mem_mk', AffineSubspace.ext_of_direction_eq, AffineSubspace.inter_eq_singleton_of_nonempty_of_isCompl, AffineSubspace.instCompleteLattice, affineSpan_le, vectorSpan_pair, AffineSubspace.direction_affineSpan_insert, AffineSubspace.parallel_iff_direction_eq_and_eq_bot_iff_eq_bot, AffineSubspace.map, AffineSubspace.map_direction, AffineSubspace.map_span, AffineSubspace.comap, AffineMap.restrict]
  E1: auto
families: []
requires: [V07, V22.C01]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Affine subspaces and spans

### Overview

An affine subspace is a set of points closed under the operation $c(p_1 -_v p_2) +_v p_3$. A nonempty affine subspace is a translate of a linear subspace, its direction, and it is determined by its direction and one of its points. The affine span of a set is the smallest affine subspace that contains it. This section also treats joins, meeting subspaces and parallel subspaces. Mathlib allows the empty subspace, so several statements need nonemptiness.

Throughout, $k$ is a ring and $P$ is an affine space over a $k$-module $V$.

### Definitions

**Definition (affine subspace).** An *affine subspace* of $P$ is a subset $s$ such that $c(p_1 -_v p_2) +_v p_3 \in s$ for all $c \in k$ and $p_1, p_2, p_3 \in s$.

::: mathlib
`AffineSubspace` · `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs`

`structure AffineSubspace (k P)` has a `carrier : Set P` and the closure condition `smul_vsub_vadd_mem'`. The empty set satisfies the condition, and it is the bottom element `⊥` of the complete lattice `AffineSubspace.instCompleteLattice`.

<?decl AffineSubspace?>
:::

**Definition (vector span, direction, affine span).** For a set $S \subseteq P$, the *vector span* is the submodule $\operatorname{vs}(S) = \operatorname{span}\{p -_v q : p, q \in S\}$ of $V$. The *direction* of an affine subspace $s$ is $\operatorname{vs}(s)$. The *affine span* $\operatorname{aff}(S)$ is the intersection of all affine subspaces that contain $S$.

::: mathlib
`affineSpan` · `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs`

`vectorSpan k s` is `Submodule.span k (s -ᵥ s)`, and `AffineSubspace.direction s` is `vectorSpan k (s : Set P)`. The carrier of `affineSpan k s` is `spanPoints k s`, the set of points `v +ᵥ p` with `p ∈ s` and `v ∈ vectorSpan k s`. The universal property is `affineSpan_le`. The notation is `line[k, p₁, p₂]` for two points.

<?decl affineSpan?>
:::

**Definition (subspace through a point).** For $p \in P$ and a submodule $D \subseteq V$, the set $\{q \in P : q -_v p \in D\}$ is an affine subspace. Its direction is $D$, and it contains $p$.

In Lean this is `AffineSubspace.mk' p D`, with `AffineSubspace.mem_mk'`.

**Definition (parallel).** Two affine subspaces $s_1, s_2$ are *parallel* if $s_2 = v + s_1$ for some $v \in V$, where $v + s_1 = \{v +_v p : p \in s_1\}$.

::: mathlib
`AffineSubspace.Parallel` · `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic`

`s₁.Parallel s₂` is `∃ v : V, s₂ = s₁.map (constVAdd k P v)`, with the scoped notation `s₁ ∥ s₂` after `open Affine`. It is an equivalence relation.

<?decl AffineSubspace.Parallel?>
:::

### Theorems and proofs

**Theorem (the direction).** Let $s$ be a nonempty affine subspace. Then $\{p -_v q : p, q \in s\}$ is a submodule of $V$, so it is the direction $D$ of $s$. For each $p \in s$, $s = \{q : q -_v p \in D\}$.

*Proof.* Call the set $D'$. It contains $0 = p -_v p$. For $c \in k$, $c(p_1 -_v p_2) = (c(p_1 -_v p_2) +_v p_2) -_v p_2 \in D'$, since the point $c(p_1 -_v p_2) +_v p_2$ is in $s$. For a sum, rule (4) of Chapter 1 gives $(p_1 -_v p_2) + (p_3 -_v p_4) = ((p_1 -_v p_2) +_v p_3) -_v p_4$, and $(p_1 -_v p_2) +_v p_3 = 1 \cdot (p_1 -_v p_2) +_v p_3 \in s$. So $D'$ is a submodule. It contains the generators of $D$ and lies in $D$, so $D' = D$. Fix $p \in s$. If $q \in s$, then $q -_v p \in D$. If $q -_v p = p_1 -_v p_2$ with $p_1, p_2 \in s$, then $q = (p_1 -_v p_2) +_v p \in s$. $\square$

::: mathlib
`AffineSubspace.coe_direction_eq_vsub_set` · `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs`

`AffineSubspace.coe_direction_eq_vsub_set : (s : Set P).Nonempty → (s.direction : Set V) = (s : Set P) -ᵥ s`.

<?decl AffineSubspace.coe_direction_eq_vsub_set?>
:::

**Theorem (the affine span).** For a nonempty $S \subseteq P$, $\operatorname{aff}(S) = \{v +_v p : p \in S,\ v \in \operatorname{vs}(S)\}$, and the direction of $\operatorname{aff}(S)$ is $\operatorname{vs}(S)$.

*Proof.* Call the right side $T$. Let $q_i = v_i +_v p_i$ with $p_i \in S$ and $v_i \in \operatorname{vs}(S)$. Then $q_1 -_v q_2 = v_1 - v_2 + (p_1 -_v p_2) \in \operatorname{vs}(S)$, by rule (4) and Chasles. So $c(q_1 -_v q_2) +_v q_3 = (c(q_1 -_v q_2) + v_3) +_v p_3 \in T$, and $T$ is an affine subspace. It contains $S$, with $v = 0$. Let $s$ be an affine subspace that contains $S$. The direction of $s$ contains each $p -_v q$ with $p, q \in S$, so it contains $\operatorname{vs}(S)$, and $v +_v p \in s$ for $v \in \operatorname{vs}(S)$ and $p \in S$. So $T \subseteq s$, and $T = \operatorname{aff}(S)$. The direction of $T$ is $\operatorname{vs}(S)$ by the same computation. $\square$

::: mathlib
`direction_affineSpan` · `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs`

`direction_affineSpan : (affineSpan k s).direction = vectorSpan k s`, with no hypothesis of nonemptiness. For two points, `vectorSpan_pair` gives `vectorSpan k {p₁, p₂} = k ∙ (p₁ -ᵥ p₂)`.

<?decl direction_affineSpan?>
:::

**Theorem (two subspaces meet).** Let $s_1, s_2$ be nonempty affine subspaces with directions $D_1, D_2$ such that $D_1 + D_2 = V$. Then $s_1 \cap s_2 \neq \emptyset$. If $V = D_1 \oplus D_2$, the intersection is one point.

*Proof.* Pick $p_1 \in s_1$ and $p_2 \in s_2$, and write $p_2 -_v p_1 = v_1 + v_2$ with $v_i \in D_i$. Put $q = v_1 +_v p_1 \in s_1$. Then $p_2 = (v_1 + v_2) +_v p_1 = v_2 +_v q$, so $q = (-v_2) +_v p_2 \in s_2$. If the sum is direct and $q, q'$ are two common points, then $q -_v q' \in D_1 \cap D_2 = 0$. $\square$

::: mathlib
`AffineSubspace.inter_nonempty_of_nonempty_of_sup_direction_eq_top` · `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs`

The hypotheses are `(s₁ : Set P).Nonempty`, `(s₂ : Set P).Nonempty` and `s₁.direction ⊔ s₂.direction = ⊤`. The form with complements is `AffineSubspace.inter_eq_singleton_of_nonempty_of_isCompl`.

<?decl AffineSubspace.inter_nonempty_of_nonempty_of_sup_direction_eq_top?>
:::

**Theorem (direction of a join).** Let $p_1 \in s_1$ and $p_2 \in s_2$. The direction of $s_1 \vee s_2 = \operatorname{aff}(s_1 \cup s_2)$ is $D_1 + D_2 + k(p_2 -_v p_1)$.

*Proof.* Put $E = D_1 + D_2 + k(p_2 -_v p_1)$. Each of $D_1$, $D_2$ and $p_2 -_v p_1$ is a difference of points of $s_1 \vee s_2$, so $E$ lies in the direction. Conversely, the subspace $t = \{q : q -_v p_1 \in E\}$ contains $s_1$. It also contains $s_2$: for $q \in s_2$, $q -_v p_1 = (q -_v p_2) + (p_2 -_v p_1) \in E$. So $s_1 \vee s_2 \subseteq t$, and its direction lies in $E$. $\square$

::: mathlib
`AffineSubspace.direction_sup` · `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic`

`AffineSubspace.direction_sup (hp₁ : p₁ ∈ s₁) (hp₂ : p₂ ∈ s₂) : (s₁ ⊔ s₂).direction = s₁.direction ⊔ s₂.direction ⊔ k ∙ (p₂ -ᵥ p₁)`. The case of one point is `AffineSubspace.direction_affineSpan_insert`.

<?decl AffineSubspace.direction_sup?>
:::

**Theorem (parallel subspaces).** Two affine subspaces are parallel if and only if they have the same direction and either both are empty or both are nonempty.

*Proof.* A translate $v + s_1$ has the same differences as $s_1$, since $(v +_v p) -_v (v +_v q) = p -_v q$ by rule (4) of Chapter 1 and Chasles. It is empty exactly when $s_1$ is. Conversely, if both are empty, take $v = 0$. If $s_1, s_2$ are nonempty with direction $D$, pick $p_i \in s_i$ and put $v = p_2 -_v p_1$. Then $v + s_1$ contains $p_2$ and has direction $D$, so $v + s_1 = s_2$ by the theorem on the direction. $\square$

The Lean form is `AffineSubspace.parallel_iff_direction_eq_and_eq_bot_iff_eq_bot`.

### Examples

**Example (a plane in space).** Let $S = \{(1, 0, 0), (0, 1, 0), (0, 0, 1)\} \subseteq \mathbb{R}^3$. The differences from $a = (1, 0, 0)$ are $(-1, 1, 0)$ and $(-1, 0, 1)$, so $\operatorname{vs}(S)$ is the plane $D = \{v : v_1 + v_2 + v_3 = 0\}$. By the theorem on affine spans, $\operatorname{aff}(S) = a + D = \{x : x_1 + x_2 + x_3 = 1\}$.

**Counterexample (skew lines).** In $\mathbb{R}^3$, let $\ell_1 = \{(t, 0, 0)\}$ and $\ell_2 = \{(0, t, 1)\}$. Their directions are $D_1 = \mathbb{R} e_1$ and $D_2 = \mathbb{R} e_2$, so $D_1 + D_2 \neq \mathbb{R}^3$. The lines do not meet, since the third coordinate is $0$ on $\ell_1$ and $1$ on $\ell_2$. So the hypothesis $D_1 + D_2 = V$ in the theorem on meeting subspaces is needed.

**Counterexample (the empty subspace).** The empty subspace $\bot$ and a point $\{p\}$ have the same direction $0$. They are not parallel and not equal. So two subspaces with the same direction need a common point to be equal, and the theorem on parallel subspaces needs the condition on emptiness. In Lean, equality from a common point is `AffineSubspace.ext_of_direction_eq`.

### The library around it

Affine maps move subspaces. For $f : P_1 \to P_2$ affine, `AffineSubspace.map f s` is the image and `AffineSubspace.comap f s` the preimage. The direction of the image is the image of the direction under the linear part, by `AffineSubspace.map_direction`, and `AffineSubspace.map_span` says that the image of an affine span is the affine span of the image. Maps restrict to subspaces by `AffineMap.restrict`.

### Exercises

1. (A) Find $\operatorname{aff}\{(1, 2), (3, 6)\}$ in $\mathbb{R}^2$.
2. (A) Show that the intersection of affine subspaces is an affine subspace.
3. (A) Show that a nonempty subset $s$ of a module $V$ is an affine subspace if and only if $s - p$ is a submodule for one, and then each, $p \in s$.
4. (B) Show that two lines in an affine plane over a field are either parallel or meet in exactly one point.
5. (B) Show that the image of an affine subspace under an affine map is an affine subspace, with direction the image of the direction.
6. (C) Let $k$ be a field in which $2 \neq 0$, and $s \subseteq P$ nonempty. Show that $s$ is an affine subspace if and only if it contains the line through any two of its points. Hint: put $q = c(p_1 -_v p_2) +_v p_2$ and let $m$ be the midpoint of $q$ and $p_3$. The point $c(p_1 -_v p_2) +_v p_3$ is on the line through $p_2$ and $m$.

### Notes and history

The files `AffineSubspace.Defs` and `AffineSubspace.Basic` have the author Joseph Myers. The file on ranges has the author Olivia Röhrig, the file on shifts Weiyi Wang, the file on pointwise operations Hanting Zhang, and the file on restrictions Paul Reichert.

### Reference

<?reference?>
