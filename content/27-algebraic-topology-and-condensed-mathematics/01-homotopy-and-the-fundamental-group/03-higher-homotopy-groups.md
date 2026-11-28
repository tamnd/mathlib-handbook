---
title: Higher homotopy groups
kind: theory
modules:
  - Mathlib.Topology.Category.TopCat.Sphere
  - Mathlib.Topology.Homotopy.HomotopyGroup
explains:
  E3: [Cube.boundary, GenLoop, GenLoop.Homotopic, HomotopyGroup, HomotopyGroup.Pi, GenLoop.transAt, HomotopyGroup.group, HomotopyGroup.commGroup, TopCat.sphere]
  E2: [LoopSpace, GenLoop.const, GenLoop.toLoop, GenLoop.fromLoop, GenLoop.loopHomeo, GenLoop.symmAt, GenLoop.transAt_distrib, homotopyGroupEquivFundamentalGroup, HomotopyGroup.auxGroup, HomotopyGroup.isUnital_auxGroup, HomotopyGroup.auxGroup_indep, HomotopyGroup.mul_spec, HomotopyGroup.inv_spec, HomotopyGroup.one_def, HomotopyGroup.pi0EquivZerothHomotopy, genLoopHomeoOfIsEmpty, HomotopyGroup.pi1EquivFundamentalGroup, HomotopyGroup.pi1MulEquivFundamentalGroup, HomotopyGroup.homotopyGroupOfUniqueMulEquivFundamentalGroup, TopCat.disk, TopCat.diskBoundary, TopCat.ball, TopCat.diskBoundaryInclusion, TopCat.ballInclusion]
  E1: auto
families: []
requires: [V05.C01, V13.C01, V13.C05, V24.C01, V24.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Higher homotopy groups

### Overview

The fundamental group classifies loops, which are maps from a circle. The higher homotopy groups classify maps from spheres of higher dimension. A map from the sphere $S^n$ that sends a base point to $x$ is the same as a map from the cube $I^n$ that sends the whole boundary of the cube to $x$, because $I^n$ with its boundary collapsed to a point is homeomorphic to $S^n$. Mathlib takes the cube as the definition. This choice makes the group law simple: two cubes are glued along one coordinate, as two paths are glued in the fundamental group.

This section defines the generalized loops, the cubes with the boundary sent to the base point, and the homotopy group $\pi_n(X, x)$ as the set of their classes up to homotopy relative to the boundary. It identifies $\pi_0$ with the set of path components and $\pi_1$ with the fundamental group. It builds the group structure for $n \ge 1$ and proves that it is commutative for $n \ge 2$ by the Eckmann-Hilton argument. It computes the homotopy groups of a point, and it ends with the spheres and disks of `TopCat`.

### Definitions

Mathlib indexes the coordinates of the cube by an arbitrary type $N$. For $N = \operatorname{Fin} n$ this gives the usual cube $I^n$. The general index makes it easy to split off one coordinate.

**Definition (Cube and boundary).** For a type $N$, the cube $I^N$ is the space of functions $N \to I$ with the product topology. Its *boundary* $\partial I^N$ is the set of $y \in I^N$ with $y_i = 0$ or $y_i = 1$ for some $i \in N$.

For $N$ empty the cube is a single point and the boundary is empty, since no coordinate exists. For $N$ with one element the cube is $I$ and the boundary is $\{0, 1\}$.

**Definition (Generalized loop).** Let $x \in X$. A *generalized loop* of index $N$ at $x$ is a continuous map $f : I^N \to X$ with $f(y) = x$ for all $y \in \partial I^N$. The set of them is $\Omega^N(X, x)$, with the compact-open topology. The *constant* generalized loop has value $x$ everywhere.

**Definition (Homotopy group).** Two generalized loops $f$ and $g$ are *homotopic* when a homotopy from $f$ to $g$ relative to $\partial I^N$ exists. This is an equivalence relation, by the first section of this chapter. The quotient is the *homotopy group* $\pi_N(X, x)$. For $N = \operatorname{Fin} n$ write $\pi_n(X, x)$.

**Definition (Concatenation and reversal along a coordinate).** Let $i \in N$ and $f, g \in \Omega^N(X, x)$. The *concatenation along $i$* is the map $f +_i g$ with
$$(f +_i g)(y) = \begin{cases} f(y[i \mapsto 2y_i]) & y_i \le 1/2, \\ g(y[i \mapsto 2y_i - 1]) & y_i \ge 1/2, \end{cases}$$
where $y[i \mapsto s]$ is $y$ with the $i$-th coordinate replaced by $s$. The *reversal along $i$* is $(-_i f)(y) = f(y[i \mapsto 1 - y_i])$.

At $y_i = 1/2$ both formulas give $x$, because $y[i \mapsto 1]$ and $y[i \mapsto 0]$ lie on the boundary. So $f +_i g$ is continuous by the pasting lemma. It sends the boundary to $x$: a point with $y_j \in \{0, 1\}$ for some $j \neq i$ goes to a boundary point under both substitutions, and a point with $y_i \in \{0, 1\}$ goes to a boundary point of $f$ or of $g$.

**Definition (Spheres and disks).** For $n \in \mathbb{N}$, the *disk* $\mathbb{D}^n$ is the closed unit ball of $\mathbb{R}^n$, its *boundary* $\partial \mathbb{D}^n$ is the unit sphere of $\mathbb{R}^n$, the *ball* $\mathbb{B}^n$ is the open unit ball, and the *sphere* $\mathbb{S}^n$ is $\partial \mathbb{D}^{n+1}$, the unit sphere of $\mathbb{R}^{n+1}$. All carry the subspace topology.

### Theorems and proofs

**Proposition (The cases $N$ empty and $N$ a point).** If $N$ is empty, then $\Omega^N(X, x) \cong X$ and $\pi_N(X, x)$ is the set of path components of $X$. If $N$ has one element, then $\Omega^N(X, x)$ is the space of loops at $x$ and $\pi_N(X, x) \cong \pi_1(X, x)$.

*Proof.* For $N$ empty, $I^N$ is a point and $\partial I^N$ is empty. A map from a point is its value, so $\Omega^N(X, x) \cong X$. A homotopy relative to the empty set between two maps from a point is a path between their values. So two points have the same class exactly when a path joins them. For $N$ with one element, $I^N \cong I$, the boundary is $\{0, 1\}$, and a generalized loop is a path from $x$ to $x$. A homotopy relative to $\{0, 1\}$ is a path homotopy. The concatenation along the unique coordinate is the composite of paths. $\square$

The case $N$ empty gives only a set: the class of $x$ is a distinguished element, but no group law exists in general.

**Lemma (Splitting off one coordinate).** Let $i \in N$ and $N' = N \setminus \{i\}$. The map $f \mapsto (t \mapsto f(t, -))$ is a homeomorphism
$$\Omega^N(X, x) \cong \Omega\big(\Omega^{N'}(X, x), c\big),$$
where $c$ is the constant generalized loop and $\Omega$ is the space of loops. It sends homotopies relative to $\partial I^N$ to path homotopies and back, and it sends $f +_i g$ to the composite of the two loops.

*Proof.* Write $I^N \cong I \times I^{N'}$, with the coordinate $i$ first. For $f \in \Omega^N(X, x)$ and $t \in I$, the map $f(t, -)$ sends $\partial I^{N'}$ to $x$, since $(t, z)$ lies in $\partial I^N$ when $z \in \partial I^{N'}$. For $t \in \{0, 1\}$ the whole slice lies in $\partial I^N$, so $f(0, -) = f(1, -) = c$. The map $t \mapsto f(t, -)$ into the space of maps is continuous, because $I^{N'}$ is compact Hausdorff, so currying is a homeomorphism for the compact-open topology. Its inverse uncurries. A point of $\partial I^N$ has either $t \in \{0, 1\}$ or its other coordinates in $\partial I^{N'}$, so the inverse lands in $\Omega^N(X, x)$. The same currying applied to $I \times I^N$ turns a homotopy relative to $\partial I^N$ into a homotopy of loops that fixes the end points and stays in $\Omega^{N'}$. The formula for $f +_i g$ is the formula for the composite of the loops $t \mapsto f(t, -)$ and $t \mapsto g(t, -)$. $\square$

**Theorem (Group structure).** Let $N$ be nonempty and $i \in N$. The operation $[f] \cdot_i [g] = [f +_i g]$ is well defined on $\pi_N(X, x)$ and makes it a group, with unit the class of the constant generalized loop and inverse $[-_i f]$.

*Proof.* By the lemma, $\pi_N(X, x)$ is in bijection with $\pi_1(\Omega^{N'}(X, x), c)$, and the bijection carries $+_i$ to the composite of loops and $-_i$ to the reverse. The fundamental group is a group by the previous section, with unit the class of the constant loop, which corresponds to the constant generalized loop. Transport the group structure along the bijection. $\square$

**Lemma (Interchange law).** For $i \neq j$ in $N$ and $a, b, c, d \in \Omega^N(X, x)$,
$$(a +_j b) +_i (c +_j d) = (a +_i c) +_j (b +_i d).$$

*Proof.* Both sides are the map that divides the square of the coordinates $i$ and $j$ into four quadrants. For $y_i \le 1/2$ and $y_j \le 1/2$, the left side gives $(a +_j b)(y[i \mapsto 2y_i]) = a(y[i \mapsto 2y_i][j \mapsto 2y_j])$, and the right side gives $(a +_i c)(y[j \mapsto 2y_j]) = a(y[j \mapsto 2y_j][i \mapsto 2y_i])$. The two substitutions act on different coordinates, so they commute, and both sides agree. The other three quadrants give $b$, $c$ and $d$ in the same way: $y_i \le 1/2 \le y_j$ gives $b$, $y_j \le 1/2 \le y_i$ gives $c$, and $y_i, y_j \ge 1/2$ gives $d$. The equation is an equality of maps, not only of classes. $\square$

**Lemma (Eckmann-Hilton).** Let $M$ be a set with two binary operations $\circ$ and $\ast$, with units $e$ and $e'$, such that $(a \ast b) \circ (c \ast d) = (a \circ c) \ast (b \circ d)$ for all $a, b, c, d$. Then $e = e'$, the two operations are equal, and they are commutative and associative.

*Proof.* First $e' = e' \ast e' = (e \circ e') \ast (e' \circ e) = (e \ast e') \circ (e' \ast e) = e \circ e = e$, where the third step is the interchange law read from right to left. Write $e$ for the common unit. Then $a \circ b = (a \ast e) \circ (e \ast b) = (a \circ e) \ast (e \circ b) = a \ast b$. So the operations are equal. Next $a \circ b = (e \ast a) \circ (b \ast e) = (e \circ b) \ast (a \circ e) = b \ast a = b \circ a$. For associativity, $(a \circ b) \circ c = (a \ast b) \circ (e \ast c) = (a \circ e) \ast (b \circ c) = a \circ (b \circ c)$. $\square$

**Theorem (Commutativity).** Let $N$ have two distinct elements $i \neq j$. The group structures $\cdot_i$ and $\cdot_j$ on $\pi_N(X, x)$ are equal, and the group is abelian. In particular $\pi_n(X, x)$ is abelian for $n \ge 2$.

*Proof.* Both operations have the class of the constant loop as unit. Pass the interchange law to classes: $([a] \cdot_j [b]) \cdot_i ([c] \cdot_j [d]) = ([a] \cdot_i [c]) \cdot_j ([b] \cdot_i [d])$. The Eckmann-Hilton lemma, with $\circ = \cdot_i$ and $\ast = \cdot_j$, shows that the two operations agree and are commutative. $\square$

The same argument shows that the group structure does not depend on the choice of the coordinate $i$, for any $N$ with at least two elements. For $N$ with one element only one choice exists.

**Proposition (Homotopy groups of a point).** Let $X$ be a one-point space $\{x\}$. Then $\pi_N(X, x)$ has exactly one element for every $N$.

*Proof.* There is exactly one map $I^N \to \{x\}$, the constant map, and it sends the boundary to $x$. So $\Omega^N(X, x)$ has one element, and so has its quotient. $\square$

For $N$ nonempty this says that $\pi_N(X, x)$ is the trivial group. For $N$ empty it says that a point has one path component.

**Remark (The sphere model).** The quotient $I^n / \partial I^n$ is homeomorphic to $\mathbb{S}^n$, and so $\pi_n(X, x)$ is in bijection with the based homotopy classes of maps $(\mathbb{S}^n, \ast) \to (X, x)$. The index of this edition has no declaration for this homeomorphism, and none for the computation $\pi_n(\mathbb{S}^n) \cong \mathbb{Z}$; the source file lists it as a task.

### Examples

**Example (The interchange law in the square).** Take $N = \operatorname{Fin} 2$, with $i = 0$ and $j = 1$, and the point $y = (0.3, 0.8)$. Then $y_0 \le 1/2 \le y_1$. The left side $(a +_1 b) +_0 (c +_1 d)$ first uses the coordinate $0$: since $0.3 \le 1/2$ it evaluates $a +_1 b$ at $(0.6, 0.8)$; then $0.8 \ge 1/2$ gives $b(0.6, 0.6)$. The right side $(a +_0 c) +_1 (b +_0 d)$ first uses the coordinate $1$: since $0.8 \ge 1/2$ it evaluates $b +_0 d$ at $(0.3, 0.6)$; then $0.3 \le 1/2$ gives $b(0.6, 0.6)$. The two values agree, as the lemma says.

**Example (Homotopy groups of a convex set).** Let $C$ be a convex subset of $\mathbb{R}^m$ and $x \in C$. For a generalized loop $f$, the straight-line homotopy $H(s, y) = (1 - s) f(y) + s x$ stays in $C$, and on the boundary $H(s, y) = (1 - s)x + sx = x$. So $H$ is a homotopy relative to $\partial I^N$ from $f$ to the constant loop. Every class is trivial, so $\pi_N(C, x)$ has one element for each $N$. For $f(y) = x + (y_0 - y_0^2, 0, \dots, 0)$ in $C = \mathbb{R}^m$ with $N = \operatorname{Fin} 1$, the value at $s = 1/2$ and $y_0 = 1/2$ is $x + (1/8, 0, \dots, 0)$.

**Counterexample (No group law on $\pi_0$).** Let $X = \{0, 1\}$ with the discrete topology and base point $0$. Then $\pi_0(X, 0)$ has two elements, the two path components. The formula of concatenation needs a coordinate, so for $N$ empty there is none, and Mathlib gives no group instance; it asks for `Nonempty N`. So $\pi_0$ is only a pointed set, with the class of the base point as its distinguished element.

**Example (The fundamental group as the case $n = 1$).** For $X = \mathbb{S}^1$, the class of the loop that goes once around generates $\pi_1(\mathbb{S}^1)$, and Chapter 2 shows that $\pi_1(\mathbb{S}^1) \cong \mathbb{Z}$. Through the proposition on the case $N$ a point, this is also $\pi_{\operatorname{Fin} 1}(\mathbb{S}^1)$.

### The library around it

::: mathlib
`Cube.boundary` · `Mathlib.Topology.Homotopy.HomotopyGroup`

The cube is written `I^N`, the scoped notation for `N → I`. `Cube.boundary N` is `{y | ∃ i, y i = 0 ∨ y i = 1}`. The homeomorphisms `Cube.splitAt i` and `Cube.insertAt i` split off and insert the coordinate `i`.

<?decl Cube.boundary?>
:::

::: mathlib
`GenLoop` · `Mathlib.Topology.Homotopy.HomotopyGroup`

`GenLoop N X x`, with notation `Ω^ N X x`, is the set of `C(I^N, X)` that send `Cube.boundary N` to `x`. `GenLoop.const` is the constant one, and `LoopSpace X x`, with notation `Ω`, is `Path x x`. The relation `GenLoop.Homotopic` is homotopy relative to the boundary. `GenLoop.toLoop i`, `GenLoop.fromLoop i` and the homeomorphism `GenLoop.loopHomeo i` are the lemma on splitting off a coordinate.

<?decl GenLoop?>
:::

::: mathlib
`GenLoop.transAt` · `Mathlib.Topology.Homotopy.HomotopyGroup`

`transAt i f g` is the concatenation $f +_i g$ by the formula above, and `GenLoop.symmAt i f` is the reversal. `GenLoop.transAt_distrib` is the interchange law; it is an equality of generalized loops.

<?decl GenLoop.transAt?>
:::

::: mathlib
`HomotopyGroup` · `Mathlib.Topology.Homotopy.HomotopyGroup`

`HomotopyGroup N X x` is the quotient of `Ω^ N X x` by `GenLoop.Homotopic`. `HomotopyGroup.Pi n X x`, with notation `π_ n X x`, is the case `N = Fin n`. `homotopyGroupEquivFundamentalGroup i` is the bijection with the fundamental group of `Ω^ {j // j ≠ i} X x`. `HomotopyGroup.pi0EquivZerothHomotopy` and `genLoopHomeoOfIsEmpty` are the case $N$ empty, and `HomotopyGroup.pi1EquivFundamentalGroup`, `HomotopyGroup.pi1MulEquivFundamentalGroup` and `HomotopyGroup.homotopyGroupOfUniqueMulEquivFundamentalGroup` are the case $N$ a point.

<?decl HomotopyGroup?>
:::

::: mathlib
`HomotopyGroup.group` · `Mathlib.Topology.Homotopy.HomotopyGroup`

The instance needs `[DecidableEq N] [Nonempty N]` and uses the coordinate `Classical.arbitrary N`. For each `i`, `HomotopyGroup.auxGroup i` is the group of the coordinate `i`, and `HomotopyGroup.isUnital_auxGroup` shows that the class of `const` is its unit. `HomotopyGroup.auxGroup_indep` says that the group does not depend on `i`, by `EckmannHilton.mul`. The lemma `HomotopyGroup.mul_spec` states `⟦p⟧ * ⟦q⟧ = ⟦transAt i q p⟧`: the right factor comes first, as in `FundamentalGroup`. `HomotopyGroup.inv_spec` and `HomotopyGroup.one_def` describe the inverse and the unit.

<?decl HomotopyGroup.group?>
:::

::: mathlib
`HomotopyGroup.commGroup` · `Mathlib.Topology.Homotopy.HomotopyGroup`

The instance needs `[Nontrivial N]`, so it applies to `π_ (n + 2) X x`. It is built with `EckmannHilton.commGroup` from two distinct coordinates and the interchange law.

<?decl HomotopyGroup.commGroup?>
:::

::: mathlib
`TopCat.sphere` · `Mathlib.Topology.Category.TopCat.Sphere`

`TopCat.disk n` is the closed unit ball of `EuclideanSpace ℝ (Fin n)` as an object of `TopCat`, lifted by `ULift` to an arbitrary universe. `TopCat.diskBoundary n` is its boundary sphere, `TopCat.ball n` the open ball, and `TopCat.sphere n` is `diskBoundary (n + 1)`. The notations are `𝔻`, `∂𝔻`, `𝔹` and `𝕊`. The maps `TopCat.diskBoundaryInclusion` and `TopCat.ballInclusion` are monomorphisms, and the disk and its boundary are compact. These objects are the cells of Chapter 6.

<?decl TopCat.sphere?>
:::

The index of this edition has no declaration for the map induced on $\pi_n$ by a continuous map, and none for the homotopy groups of a sphere. The homotopy groups of a point follow from the fact that `Ω^ N X x` is a subsingleton when `X` is.

```lean
open scoped Topology in
example (n : ℕ) (X : Type*) [TopologicalSpace X] (x : X) :
    CommGroup (HomotopyGroup.Pi (n + 2) X x) :=
  inferInstance
```

Common errors of a learner: `π_ 0 X x` is only a type, with no group instance. The product `⟦p⟧ * ⟦q⟧` runs `q` along the chosen coordinate first. The spheres of `TopCat` live in an arbitrary universe through `ULift`, so a point of `𝕊 n` is not directly a point of `EuclideanSpace ℝ (Fin (n + 1))`. The boundary of the cube with $N$ empty is empty, not the whole cube.

### Exercises

1. (A) For $N = \operatorname{Fin} 2$, list the points of $\partial I^N$ with $y_0 = 1/2$. *Hint:* The second coordinate must be $0$ or $1$.
2. (A) Show that $-_i(-_i f) = f$ as maps, and that $(-_i f)(y) = x$ on the boundary. *Hint:* The map $s \mapsto 1 - s$ fixes the set $\{0, 1\}$.
3. (B) Show that $\pi_N(X \times Y, (x, y))$ is in bijection with $\pi_N(X, x) \times \pi_N(Y, y)$. *Hint:* A map into a product is a pair of maps, and so is a homotopy.
4. (B) Show that a continuous map $\varphi : X \to Y$ with $\varphi(x) = y$ induces a map $\pi_N(X, x) \to \pi_N(Y, y)$, and that it is a homomorphism for $N$ nonempty. *Hint:* Compose with $\varphi$ and check that $\varphi \circ (f +_i g) = (\varphi \circ f) +_i (\varphi \circ g)$.
5. (B) Let $M$ be a set with two unital operations that satisfy the interchange law. Show that the operations are associative, without the assumption that one of them is a group law. *Hint:* Follow the last step of the proof of the Eckmann-Hilton lemma.
6. (C) Let $G$ be a topological group with unit $1$. Show that $\pi_1(G, 1)$ is abelian, by the Eckmann-Hilton argument applied to the composite of loops and the pointwise product. *Hint:* Check that the pointwise product of loops is a unital operation on classes and that it satisfies the interchange law with the composite.
7. (C) Show that $\pi_N(X, x)$ depends only on the path component of $x$ up to a bijection, for $N$ with one element. *Hint:* Use the change of base point of the previous section.

### Notes and history

Hurewicz introduced the higher homotopy groups in 1935. The Eckmann-Hilton argument carries the names of Beno Eckmann and Peter Hilton. The cube definition, with the boundary sent to the base point, is the one of many textbooks, and it gives the commutativity in dimension at least 2 directly from the interchange law.

The Mathlib Author of `Topology.Homotopy.HomotopyGroup` is Roberto Alvarez. The Mathlib Authors of `Topology.Category.TopCat.Sphere` are Jiazhen Xia and Elliot Dean Young.

### Reference

<?reference?>
