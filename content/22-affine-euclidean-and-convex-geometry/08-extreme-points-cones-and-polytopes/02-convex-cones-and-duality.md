---
title: Convex cones and duality
kind: theory
modules:
  - Mathlib.Geometry.Convex.Cone.Basic
  - Mathlib.Geometry.Convex.Cone.Pointed
  - Mathlib.Geometry.Convex.Cone.Dual
  - Mathlib.Geometry.Convex.Cone.DualFinite
  - Mathlib.Geometry.Convex.Cone.Simplicial
  - Mathlib.Geometry.Convex.Cone.TensorProduct
  - Mathlib.Geometry.Convex.Cone.Face.Basic
  - Mathlib.Geometry.Convex.Cone.Face.Lattice
explains:
  E3: [ConvexCone, PointedCone, PointedCone.hull, PointedCone.dual, PointedCone.mem_dual, PointedCone.DualFG, PointedCone.DualFG.dual_dual_flip, PointedCone.IsFaceOf, PointedCone.Face, PointedCone.IsSimplicial]
  E2: [ConvexCone.Pointed, ConvexCone.Salient, ConvexCone.Flat, PointedCone.lineal, PointedCone.dual_anti, PointedCone.dual_union, PointedCone.dual_hull, PointedCone.subset_dual_dual, PointedCone.dual_dual_flip_dual, PointedCone.DualFG.dual_of_fg, PointedCone.DualFG.inf, PointedCone.DualFG.iff_exists_fg_dual, PointedCone.IsFaceOf.isExtreme, PointedCone.IsFaceOf.trans, PointedCone.IsFaceOf.lineal, PointedCone.Face.instCompleteLattice]
  E1: auto
families: []
requires: [V07, V16.C05, V22.C06, V22.C07]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Convex cones and duality

### Overview

A cone is a convex set that is closed under multiplication by positive scalars. A system of inequalities $Ax \ge 0$ describes a cone, and a polytope becomes a cone after one adds a coordinate. This section develops the algebraic theory of cones in Geometry/Convex/Cone: pointed cones, the dual cone along a bilinear pairing, duals of finite sets, and faces. The topological theory, with the separation form of Farkas' lemma, is in Volume 16.

### Definitions

Let $R$ be an ordered field, for example $\mathbb{R}$, and $M$ an $R$-module.

**Definition (convex cone).** A *convex cone* is a set $C \subseteq M$ with $ax + by \in C$ for all $x, y \in C$ and $a, b > 0$. It is *pointed* if $0 \in C$, *salient* if $x \in C$ and $-x \in C$ imply $x = 0$, and *flat* if some $x \ne 0$ has $x, -x \in C$.

**Definition (pointed cone).** A *pointed cone* is a submodule of $M$ over the semiring $R_{\ge 0}$ of nonnegative scalars. As a set, it is a convex cone that contains $0$. The *conic hull* $\mathrm{cone}(S)$ of $S \subseteq M$ is the $R_{\ge 0}$-span of $S$. The *lineality space* of $C$ is the largest linear subspace in $C$.

**Definition (dual cone).** Let $p : M \times N \to R$ be bilinear. The *dual* of $S \subseteq M$ along $p$ is
$$S^{*} = \{ y \in N : p(x, y) \ge 0 \text{ for all } x \in S \}.$$

**Definition (finitely generated cones).** A pointed cone is *finitely generated*, or a V-cone, if it is $\mathrm{cone}(S)$ for a finite $S$. It is *dually finitely generated*, or an H-cone, if it is $S^{*}$ for a finite $S$.

**Definition (face of a cone).** A pointed cone $F \le C$ is a *face* of $C$ if for all $x, y \in C$ and $a > 0$ with $ax + y \in F$, the point $x$ lies in $F$.

**Definition (simplicial cone).** A pointed cone is *simplicial* if it is $\mathrm{cone}(S)$ for a finite linearly independent set $S$.

### Theorems and proofs

**Lemma (conic hull).** $\mathrm{cone}(S)$ is the set of combinations $\sum_i a_i s_i$ with $s_i \in S$ and $a_i \ge 0$. It is the smallest pointed cone that contains $S$.

*Proof.* These combinations form a pointed cone that contains $S$, and every pointed cone that contains $S$ contains them, by induction on the length. $\square$

**Theorem (rules for the dual).** For $S, T \subseteq M$:

1. if $T \subseteq S$, then $S^{*} \subseteq T^{*}$;
2. $(S \cup T)^{*} = S^{*} \cap T^{*}$ and $\mathrm{cone}(S)^{*} = S^{*}$;
3. $S \subseteq S^{**}$, where the second dual uses the flipped pairing $p^{\mathrm{t}}(y, x) = p(x, y)$;
4. $S^{***} = S^{*}$.

*Proof.* (1) A condition on all $x \in S$ implies the condition on all $x \in T$. (2) The first claim is the definition. For the second, $p(\cdot, y) \ge 0$ on $S$ implies $p(\cdot, y) \ge 0$ on nonnegative combinations, by the lemma. (3) If $x \in S$ and $y \in S^{*}$, then $p^{\mathrm{t}}(y, x) = p(x, y) \ge 0$, so $x \in S^{**}$. (4) Apply (3) to $S^{*}$ to get $S^{*} \subseteq S^{***}$. Apply (1) to the inclusion (3) to get $S^{***} \subseteq S^{*}$. $\square$

**Theorem (H-cones).** Let $C, D \subseteq N$ be pointed cones.

1. $C$ is an H-cone if and only if $C = D_0^{*}$ for a finitely generated cone $D_0$.
2. If $C$ and $D$ are H-cones, then so is $C \cap D$.
3. If $C$ is an H-cone, then $C^{**} = C$.

*Proof.* (1) If $C = S^{*}$ with $S$ finite, take $D_0 = \mathrm{cone}(S)$ and use rule (2). The converse is the same rule read backwards. (2) If $C = S^{*}$ and $D = T^{*}$, then $C \cap D = (S \cup T)^{*}$. (3) With $C = S^{*}$, rule (4) gives $C^{**} = S^{***} = S^{*} = C$. $\square$

**Theorem (faces).** Let $C$ be a pointed cone over an ordered field.

1. Each face $F$ of $C$ is an extreme subset of $C$ in the sense of Section 1.
2. If $F_2$ is a face of $F_1$ and $F_1$ is a face of $C$, then $F_2$ is a face of $C$.
3. The lineality space of $C$ is a face of $C$.
4. The faces of $C$, ordered by inclusion, form a complete lattice, with intersection as the meet.

*Proof.* (1) Let $x, y \in C$ and $z = (1 - t)x + ty \in F$ with $0 < t < 1$. Put $a = 1 - t > 0$ and $y' = ty \in C$. Then $ax + y' \in F$, so $x \in F$. In the same way $y \in F$. (2) Let $x, y \in C$ and $a > 0$ with $ax + y \in F_2 \subseteq F_1$. Since $F_1$ is a face of $C$, $x \in F_1$. Also $y \in F_1$, by the face property with $a = 1$ applied to $y + ax$. Since $F_2$ is a face of $F_1$, $x \in F_2$. (3) Let $L$ be the lineality space and $ax + y \in L$ with $x, y \in C$. Then $-(ax) = y - (ax + y)$, and $y \in C$, $-(ax + y) \in L \subseteq C$, so $-ax \in C$. Hence $\pm x \in C$, and $x$ lies in the subspace $C \cap (-C)$, which is $L$. (4) Faces are closed under all intersections, and $C$ is the largest face, so they form a complete lattice. $\square$

For a simplicial cone $\mathrm{cone}\{s_1, \dots, s_k\}$, each $\mathrm{cone}\{s_j : j \in J\}$ is a face: in $ax + y$ the coefficient $a x_i + y_i$ of $s_i$ is $0$ for $i \notin J$, and both terms are nonnegative.

### Examples

**Example (the orthant).** Let $C = \mathbb{R}^2_{\ge 0} = \mathrm{cone}\{e_1, e_2\}$ with the dot product. Then $y \in C^{*}$ if and only if $y_1 = \langle e_1, y \rangle \ge 0$ and $y_2 \ge 0$, so $C^{*} = C$. By the remark on simplicial cones its faces include $\{0\}$, the two half-axes and $C$. These are all the faces, since a face that contains $u e_1 + v e_2$ with $u, v > 0$ contains $e_1$ and $e_2$.

**Example (a cone with a lineality space).** Let $C = \{(u, v) \in \mathbb{R}^2 : v \ge 0\}$. It is flat, because $(1, 0)$ and $(-1, 0)$ lie in $C$, and its lineality space is the $u$-axis. Its dual is $\{y : y_1 \cdot 1 \ge 0,\ -y_1 \ge 0,\ y_2 \ge 0\} = \{0\} \times \mathbb{R}_{\ge 0}$, a single ray. Its only faces are the $u$-axis and $C$ itself. So $\{0\}$ need not be a face of a cone: it is a face exactly when the cone is salient.

### The library around it

::: mathlib
`ConvexCone` · `Mathlib.Geometry.Convex.Cone.Basic`

`ConvexCone R M` is a bundled set closed under `a • x + b • y` for positive `a, b`. The predicates are `ConvexCone.Pointed`, `ConvexCone.Salient` and `ConvexCone.Flat`.

<?decl ConvexCone?>
:::

::: mathlib
`PointedCone` · `Mathlib.Geometry.Convex.Cone.Pointed`

`PointedCone R E` abbreviates a `Submodule` over the nonnegative elements of `R`, so the `Submodule` API applies. `PointedCone.hull` is the span over nonnegative scalars and `PointedCone.lineal` the lineality space.

<?decl PointedCone?>
:::

::: mathlib
`PointedCone.dual` · `Mathlib.Geometry.Convex.Cone.Dual`

`PointedCone.dual p s` for a bilinear `p : M →ₗ[R] N →ₗ[R] R`, with `PointedCone.mem_dual` as the definition. The rules of the theorem are `PointedCone.dual_anti`, `PointedCone.dual_union`, `PointedCone.dual_hull`, `PointedCone.subset_dual_dual` and `PointedCone.dual_dual_flip_dual`.

<?decl PointedCone.dual?>
:::

::: mathlib
`PointedCone.DualFG` · `Mathlib.Geometry.Convex.Cone.DualFinite`

`DualFG p C` means `∃ s : Finset M, dual p s = C`. `PointedCone.DualFG.iff_exists_fg_dual`, `PointedCone.DualFG.dual_of_fg` and `PointedCone.DualFG.inf` are the first two parts of the theorem on H-cones.

<?decl PointedCone.DualFG?>
:::

::: mathlib
`PointedCone.DualFG.dual_dual_flip` · `Mathlib.Geometry.Convex.Cone.DualFinite`

The double dual of an H-cone is the cone. For closed cones the analogue is `ProperCone.dual_dual_flip` of Volume 16, proved with the geometric form of Farkas' lemma.

<?decl PointedCone.DualFG.dual_dual_flip?>
:::

The docstring of the module says that in finite dimension FG and DualFG are equivalent by the theorem of Minkowski and Weyl. The index has no declaration for this theorem, for the closedness of a finitely generated cone, or for an algebraic Farkas lemma. To get this Farkas lemma, prove closedness (Exercise 6) and apply the separation of Volume 16.

::: mathlib
`PointedCone.IsFaceOf` · `Mathlib.Geometry.Convex.Cone.Face.Basic`

`PointedCone.IsFaceOf.isExtreme`, `PointedCone.IsFaceOf.trans` and `PointedCone.IsFaceOf.lineal` are parts (1) to (3) of the theorem on faces. The definition avoids `IsExtreme`, because over rings such as the integers extreme sets are too rare.

<?decl PointedCone.IsFaceOf?>
:::

::: mathlib
`PointedCone.Face` · `Mathlib.Geometry.Convex.Cone.Face.Lattice`

`Face C` bundles a face with its proof, and `PointedCone.Face.instCompleteLattice` is part (4).

<?decl PointedCone.Face?>
:::

::: mathlib
`PointedCone.IsSimplicial` · `Mathlib.Geometry.Convex.Cone.Simplicial`

`IsSimplicial C` is `∃ s, s.Finite ∧ LinearIndepOn R id s ∧ hull R s = C`. The remark on its faces is not in the index.

<?decl PointedCone.IsSimplicial?>
:::

The module on tensor products defines the minimal and maximal tensor products of two cones.

### Exercises

1. (A) Compute the dual of $\mathrm{cone}\{(1, 0), (1, 1)\}$ in $\mathbb{R}^2$ for the dot product.
2. (A) Show that a pointed cone is salient if and only if its lineality space is $\{0\}$.
3. (B) Show that every face of $\mathbb{R}^3_{\ge 0}$ is $\mathrm{cone}\{e_j : j \in J\}$ for some $J$.
4. (B) Show that the circular cone $L = \{(u, v, w) : \sqrt{u^2 + v^2} \le w\}$ is its own dual. Hint: Cauchy-Schwarz.
5. (B) In $\mathbb{R}^d$ with the dot product, show that the intersection of an H-cone with a linear subspace $V$ is an H-cone. Hint: $V$ is the dual of $\{\pm f_1, \dots, \pm f_k\}$ for a basis $f_1, \dots, f_k$ of $V^{\perp}$.
6. (C) Show that a finitely generated cone in $\mathbb{R}^d$ is closed. Hint: by a conic form of Caratheodory, it is a finite union of simplicial cones.

### Notes and history

Farkas published his lemma on linear inequalities in 1902. Minkowski studied cones and polyhedra in his geometry of numbers, and Weyl proved the equivalence of the two descriptions of polyhedral cones in 1935. The file on convex cones names Yury Kudryashov and Frédéric Dupuis as authors. The file on pointed cones names Apurva Nakade, the dual cone Yaël Dillies, the duals of finite sets Martin Winter, the faces Olivia Röhrig, and the simplicial cones and tensor products Bjørn Solheim.

### Reference

<?reference?>
