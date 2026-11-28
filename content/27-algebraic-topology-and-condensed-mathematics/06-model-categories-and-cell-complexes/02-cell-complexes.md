---
title: Cell complexes
kind: theory
modules:
  - Mathlib.AlgebraicTopology.RelativeCellComplex.AttachCells
  - Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
  - Mathlib.Topology.CWComplex.Abstract.Basic
  - Mathlib.Topology.CWComplex.Classical.Basic
  - Mathlib.Topology.CWComplex.Classical.Finite
  - Mathlib.Topology.CWComplex.Classical.Graph
  - Mathlib.Topology.CWComplex.Classical.Subcomplex
explains:
  E3: [HomotopicalAlgebra.AttachCells, HomotopicalAlgebra.RelativeCellComplex, TopCat.RelativeCWComplex, TopCat.CWComplex, Topology.RelCWComplex, Topology.CWComplex, Topology.RelCWComplex.closedCell, Topology.RelCWComplex.skeletonLT, Topology.RelCWComplex.Finite, Topology.RelCWComplex.Subcomplex, Topology.CWComplex.OneSkeletonGraph]
  E2: [HomotopicalAlgebra.AttachCells.cell, HomotopicalAlgebra.AttachCells.hom_ext, HomotopicalAlgebra.AttachCells.pushouts_coproducts, HomotopicalAlgebra.nonempty_attachCells_iff, HomotopicalAlgebra.RelativeCellComplex.Cells, HomotopicalAlgebra.RelativeCellComplex.Cells.ι, HomotopicalAlgebra.RelativeCellComplex.hom_ext, HomotopicalAlgebra.RelativeCellComplex.transfiniteCompositionOfShape, TopCat.RelativeCWComplex.basicCell, Topology.RelCWComplex.openCell, Topology.RelCWComplex.cellFrontier, Topology.RelCWComplex.skeleton, Topology.RelCWComplex.closed, Topology.RelCWComplex.isClosed, Topology.RelCWComplex.isCompact_closedCell, Topology.RelCWComplex.closure_openCell_eq_closedCell, Topology.RelCWComplex.closedCell_zero_eq_singleton, Topology.RelCWComplex.cellFrontier_zero_eq_empty, Topology.RelCWComplex.cellFrontier_one_eq, Topology.CWComplex.exists_cellFrontier_one_eq, Topology.RelCWComplex.FiniteDimensional, Topology.RelCWComplex.FiniteType, Topology.RelCWComplex.finite_iff_finite_cells, Topology.RelCWComplex.mkFinite, Topology.RelCWComplex.Subcomplex.instRelCWComplex, Topology.RelCWComplex.Subcomplex.finite_subcomplex_of_finite, Topology.CWComplex.OneSkeletonGraph.exists_isLoopAt_iff_subsingleton, Topology.CWComplex.ofDiscreteTopology]
  E1: auto
families: []
requires: [V13.C01, V13.C05, V24.C04, V25.C03, V27.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Cell complexes

### Overview

A cell complex is a space built from a base by attaching disks along their boundaries, one stage after the other. Mathlib has two definitions. The abstract definition works in any category: a map is a relative cell complex if it is a transfinite composition of pushouts of coproducts of given basic cells. In `TopCat` the basic cells $\partial D^n \to D^n$ give relative CW complexes. The classical definition of Whitehead describes a CW complex as a subset of a space with characteristic maps and the weak topology.

This section gives both definitions. It proves that maps out of a cell complex are determined by their values on the base and on the cells, and that a relative cell complex has the left lifting property against each map against which the basic cells have it. For the classical definition, it proves basic facts on cells, closedness and finiteness. Mathlib in this edition has no proof that the two definitions agree.

### Definitions

**Definition (Attaching cells).** Let $\mathcal{C}$ be a category, let $g_a : A_a \to B_a$ for $a \in \alpha$ be a family of maps, and let $f : X_1 \to X_2$. A structure of *attachment of cells* of type $g$ on $f$ is an index set $\iota$, a map $\pi : \iota \to \alpha$ and a pushout square

$$\begin{array}{ccc} \coprod_{i \in \iota} A_{\pi(i)} & \xrightarrow{g_1} & X_1 \\ {\scriptstyle m}\downarrow & & \downarrow{\scriptstyle f} \\ \coprod_{i \in \iota} B_{\pi(i)} & \xrightarrow{g_2} & X_2 \end{array}$$

where $m$ is the coproduct of the maps $g_{\pi(i)}$. The *cell* $i$ is the map $B_{\pi(i)} \to X_2$, the composite of the coproduct inclusion and $g_2$.

In Mathlib this is `AttachCells g f`, with the pushout in the field `isPushout`. `nonempty_attachCells_iff` says that such a structure exists if and only if $f$ is a pushout of a coproduct of maps $g_a$.

**Definition (Relative cell complex).** Let $J$ be a well-ordered set with a least element $\bot$, and for each $j \in J$ let $g^{(j)}$ be a family of basic cells. A *relative cell complex* structure on $f : X \to Y$ is a functor $F : J \to \mathcal{C}$ with these properties:

1. $F(\bot) \cong X$.
2. $F$ is continuous: for a limit element $j$, $F(j)$ is the colimit of the $F(k)$ for $k < j$.
3. $Y$ is the colimit of $F$, and $f$ is the induced map from $F(\bot)$.
4. For each $j$ that is not maximal, $F(j) \to F(j + 1)$ has an attachment of cells of type $g^{(j)}$.

The first three properties make $f$ a *transfinite composition* of the maps $F(j) \to F(j+1)$. A *cell* of the complex is a pair of a step $j$ and a cell of the attachment at that step. Its inclusion into $Y$ is the composite $B \to F(j+1) \to Y$.

In Mathlib this is `RelativeCellComplex basicCell f`, which extends `TransfiniteCompositionOfShape J f` with the field `attachCells`. The cells form the type `RelativeCellComplex.Cells`, and the inclusion of a cell is `Cells.ι`.

**Definition (Abstract CW complex).** Let $D^n$ be the closed unit disk in $\mathbb{R}^n$ with the Euclidean norm, and let $\partial D^n$ be its boundary sphere. A *relative CW complex* is a map $f : X \to Y$ in `TopCat` with a relative cell complex structure indexed by $J = \mathbb{N}$, where at step $n$ the only basic cell is $\partial D^n \to D^n$. A space $Y$ is a *CW complex* if the map from the empty space to $Y$ is a relative CW complex.

The stage $F(n)$ is the $(n-1)$-skeleton. Each nonzero element of $\mathbb{N}$ is a successor, so the continuity condition is empty. In Mathlib these are `TopCat.RelativeCWComplex f` and `TopCat.CWComplex X`, with the basic cells `RelativeCWComplex.basicCell n`.

**Definition (Classical relative CW complex).** Let $X$ be a topological space and $D \subseteq C \subseteq X$. Give $\mathbb{R}^n$ the sup norm, so that the unit ball $B^n$ and the closed unit ball $\bar{B}^n$ are cubes, and the sphere $S^{n-1}$ is the boundary of the cube. A *CW structure on $C$ relative to $D$* is a family of index types $\mathrm{cell}(n)$ for $n \in \mathbb{N}$, and for each $i \in \mathrm{cell}(n)$ a *characteristic map* $\Phi_i : \mathbb{R}^n \to X$ with these properties:

1. $\Phi_i$ is continuous on $\bar{B}^n$, and it restricts to a homeomorphism from $B^n$ onto its image.
2. The *open cells* $\Phi_i(B^n)$ are pairwise disjoint and disjoint from $D$.
3. For each $i \in \mathrm{cell}(n)$, $\Phi_i(S^{n-1})$ lies in the union of $D$ and finitely many *closed cells* $\Phi_j(\bar{B}^m)$ with $m < n$.
4. A set $A \subseteq C$ is closed if $A \cap D$ is closed and $A \cap \Phi_i(\bar{B}^n)$ is closed for each cell.
5. $D$ is closed, and $C$ is the union of $D$ and all closed cells.

A *CW complex* is the case $D = \varnothing$.

Mathlib states this as the class `RelCWComplex C D`, where `map n i` is a `PartialEquiv (Fin n → ℝ) X` with source `ball 0 1`. The class `CWComplex C` is a separate class with an instance to `RelCWComplex C ∅`. The sets `openCell n i`, `closedCell n i` and `cellFrontier n i` are $\Phi_i(B^n)$, $\Phi_i(\bar{B}^n)$ and $\Phi_i(S^{n-1})$.

**Definition (Skeleton).** For $n \in \mathbb{N} \cup \{\infty\}$, `skeletonLT C n` is the union of $D$ and the closed cells of dimension less than $n$. The $n$-skeleton is `skeleton C n = skeletonLT C (n + 1)`. Both are subcomplexes.

**Definition (Subcomplex).** A *subcomplex* of $C$ is a closed set $E$ with a set $I_n \subseteq \mathrm{cell}(n)$ for each $n$ such that $E$ is the union of $D$ and the open cells with index in $I$. This is `RelCWComplex.Subcomplex C`. For a Hausdorff $X$, the instance `Subcomplex.instRelCWComplex` makes $E$ a CW complex relative to $D$ with the cells $I$.

**Definition (Finiteness).** A classical complex is *finite dimensional* if $\mathrm{cell}(n)$ is empty for all large $n$, of *finite type* if each $\mathrm{cell}(n)$ is finite, and *finite* if both hold. These are the classes `FiniteDimensional`, `FiniteType` and `Finite` in the namespace `RelCWComplex`.

**Definition (Graph of the $1$-skeleton).** For a CW complex $C$, `CWComplex.OneSkeletonGraph C` is the graph, in the sense of `Graph` in Mathlib, with vertex set $\mathrm{cell}(0)$ and edge set $\mathrm{cell}(1)$. An edge $e$ links $x$ and $y$ if the frontier of $e$ is the union of the closed $0$-cells $x$ and $y$.

### Theorems and proofs

**Proposition (Maps out of an attachment).** Let $f : X_1 \to X_2$ have an attachment of cells, and let $\varphi, \varphi' : X_2 \to Z$. If $\varphi \circ f = \varphi' \circ f$ and $\varphi \circ c_i = \varphi' \circ c_i$ for each cell $c_i : B_{\pi(i)} \to X_2$, then $\varphi = \varphi'$.

*Proof.* The maps $\varphi \circ g_2$ and $\varphi' \circ g_2$ agree on each summand $B_{\pi(i)}$ of the coproduct, because $g_2$ restricted to that summand is $c_i$. By the universal property of the coproduct, $\varphi \circ g_2 = \varphi' \circ g_2$. The square is a pushout and $\varphi$ and $\varphi'$ agree on both legs $f$ and $g_2$, so $\varphi = \varphi'$ by the uniqueness part of the universal property. $\square$ This is `AttachCells.hom_ext`.

**Proposition (Maps out of a relative cell complex).** Let $f : X \to Y$ be a relative cell complex and $\varphi, \varphi' : Y \to Z$. If $\varphi \circ f = \varphi' \circ f$ and $\varphi$ and $\varphi'$ agree on the inclusion of each cell, then $\varphi = \varphi'$.

*Proof.* Let $\iota_j : F(j) \to Y$ be the colimit maps. Show $\varphi \circ \iota_j = \varphi' \circ \iota_j$ by well-founded induction on $j$. For $j = \bot$ this is the hypothesis on $f$, because $F(\bot) \cong X$ and $\iota_\bot$ corresponds to $f$. For a successor $j + 1$ with $j$ not maximal, apply the previous proposition to $F(j) \to F(j+1)$ and the maps $\varphi \circ \iota_{j+1}$ and $\varphi' \circ \iota_{j+1}$. They agree on $F(j)$ by induction, and on each cell at step $j$ by hypothesis. For a limit element $j$, $F(j)$ is the colimit of the $F(k)$ with $k < j$, and the two maps agree on each $F(k)$ by induction. Since $Y$ is the colimit of $F$, $\varphi = \varphi'$. $\square$ This is `RelativeCellComplex.hom_ext`.

**Theorem (Lifting for cell complexes).** Let $p : E \to B$ be a map, and assume that each basic cell $g_a$ has the left lifting property against $p$. Then each relative cell complex of type $g$ has the left lifting property against $p$.

*Proof.* Let $W$ be the class of maps with the left lifting property against $p$. It has three properties.

1. $W$ is stable under coproducts. Given a square from $\coprod A_i \to \coprod B_i$ to $p$, choose a lift on each summand and combine the lifts by the universal property.
2. $W$ is stable under cobase change. Let $f$ be a pushout of $m \in W$ along $g_1$, and take a square from $f$ to $p$ with top $u : X_1 \to E$ and bottom $v : X_2 \to B$. The composite square from $m$ to $p$ has a lift $d$. The maps $u$ and $d$ agree on $\coprod A_{\pi(i)}$, so they induce $e : X_2 \to E$ with $e \circ f = u$. The maps $p \circ e$ and $v$ agree on $X_1$ and on $\coprod B_{\pi(i)}$, so $p \circ e = v$ by the uniqueness part of the pushout property.
3. $W$ is stable under transfinite composition. Take a square with top $u : F(\bot) \to E$ and bottom $v : Y \to B$. Build compatible lifts $d_j : F(j) \to E$ with $p \circ d_j = v \circ \iota_j$ by transfinite recursion. Let $d_\bot = u$. At a successor, lift in the square from $F(j) \to F(j+1)$ to $p$ with top $d_j$. At a limit element, take the map induced by the $d_k$ on the colimit $F(j)$. The colimit of the $d_j$ is a lift $Y \to E$.

By 1 and 2, each step $F(j) \to F(j+1)$ is in $W$. By 3, $f$ is in $W$. $\square$

In Mathlib, `RelativeCellComplex.transfiniteCompositionOfShape` makes a relative cell complex a transfinite composition of pushouts of coproducts, and the lifting statement follows from the next lemma.

::: mathlib
`CategoryTheory.MorphismProperty.transfiniteCompositions_pushouts_coproducts_le_llp_rlp` · `Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting`

Transfinite compositions of pushouts of coproducts of maps in $W$ have the left lifting property against each map in $W^{\mathrm{rlp}}$.

<?decl CategoryTheory.MorphismProperty.transfiniteCompositions_pushouts_coproducts_le_llp_rlp?>
:::

For the classical definition, let $C$ be a CW complex relative to $D$ in $X$.

**Proposition (Closed cells).** Each closed cell is compact. If $X$ is Hausdorff, then each closed cell is closed, and the closure of the open cell is the closed cell.

*Proof.* The closed cube $\bar{B}^n$ is compact, and $\Phi_i$ is continuous on it, so its image is compact. In a Hausdorff space a compact set is closed. A map continuous on $\bar{B}^n = \overline{B^n}$ sends it into the closure of $\Phi_i(B^n)$. Thus $\Phi_i(\bar{B}^n) \subseteq \overline{\Phi_i(B^n)}$. The other inclusion holds because $\Phi_i(\bar{B}^n)$ is closed and contains $\Phi_i(B^n)$. $\square$ These are `isCompact_closedCell` and `closure_openCell_eq_closedCell`.

**Proposition (Cells of dimension $0$ and $1$).** A closed $0$-cell is a point, and its frontier is empty. The frontier of a $1$-cell $e$ is $\{\Phi_e(-1), \Phi_e(1)\}$. If $D = \varnothing$, it is the union of two closed $0$-cells.

*Proof.* The space $\mathbb{R}^0$ is a point of norm $0$. So $B^0 = \bar{B}^0$ is that point, and $S^{-1}$, the set of points of norm $1$, is empty. The closed $0$-cell is one point and the frontier is empty. In $\mathbb{R}^1$ the sup norm is the absolute value, so $S^0 = \{-1, 1\}$ and the frontier of $e$ is $\{\Phi_e(-1), \Phi_e(1)\}$. If $D = \varnothing$, property 3 puts this set in a finite union of closed $0$-cells, which are points. So $\Phi_e(-1)$ is a $0$-cell $x$ and $\Phi_e(1)$ is a $0$-cell $y$, and the frontier is $\{x\} \cup \{y\}$. $\square$

The lemmas are `closedCell_zero_eq_singleton`, `cellFrontier_zero_eq_empty`, `cellFrontier_one_eq` and `CWComplex.exists_cellFrontier_one_eq`. The last one gives the edges of `OneSkeletonGraph`. If $x = y$ the edge is a loop; `exists_isLoopAt_iff_subsingleton` says this happens exactly when the frontier has at most one point.

**Proposition.** If $X$ is Hausdorff, then $C$ is closed in $X$.

*Proof.* Apply property 4 to $A = C$. The set $C \cap D = D$ is closed by property 5. For each cell, $C \cap \Phi_i(\bar{B}^n) = \Phi_i(\bar{B}^n)$ is closed by the previous proposition. So $C$ is closed. $\square$

**Theorem (Finiteness).** A complex is finite if and only if it has finitely many cells in total.

*Proof.* Let the complex be finite. Then $\mathrm{cell}(m)$ is empty for $m \ge N$, and each $\mathrm{cell}(m)$ with $m < N$ is finite. The set of all cells is the disjoint union of the $\mathrm{cell}(m)$ for $m < N$, which is finite. Conversely, let the set of all cells be finite. Each $\mathrm{cell}(n)$ injects into it, so it is finite. If there are no cells, all $\mathrm{cell}(n)$ are empty. If not, let $N$ be the largest dimension of a cell. Then $\mathrm{cell}(m)$ is empty for $m > N$. $\square$ This is `finite_iff_finite_cells`.

**Proposition (Finite complexes have the weak topology).** Let $X$ be Hausdorff, and let $D$ and finitely many sets $\Phi_i(\bar{B}^n)$ satisfy properties 1, 2, 3 and 5. Then property 4 holds.

*Proof.* Let $A \subseteq C$ meet $D$ and each closed cell in a closed set. Since $C$ is the union of $D$ and the closed cells, $A$ is the union of $A \cap D$ and the sets $A \cap \Phi_i(\bar{B}^n)$. A finite union of closed sets is closed. $\square$

This is why `RelCWComplex.mkFinite` builds a finite complex without the condition `closed'`.

### Examples

**Example (Discrete spaces).** A discrete space $X$ is a CW complex with one $0$-cell for each point and no other cells. Property 4 holds because each subset of $X$ is closed. This is the instance `CWComplex.ofDiscreteTopology`.

**Example (The interval).** The interval $[-1, 1] \subseteq \mathbb{R}$ is a CW complex with two $0$-cells, $\{-1\}$ and $\{1\}$, and one $1$-cell with $\Phi(t) = t$. The open cell is $(-1, 1)$, and its frontier is the union of the two $0$-cells. Its graph is one edge between two vertices.

**Example (The circle).** The unit circle $S^1 \subseteq \mathbb{R}^2$ has a structure with one $0$-cell $\{(1, 0)\}$ and one $1$-cell $\Phi(t) = (-\cos \pi t, -\sin \pi t)$. The map is injective on $(-1, 1)$, and $\Phi(\pm 1) = (1, 0)$. So the frontier of the $1$-cell has one point, and the graph is one vertex with a loop.

**Example (The abstract sphere).** In `TopCat`, attach one $n$-cell to a point. The pushout of $\partial D^n \to D^n$ along $\partial D^n \to *$ is the quotient $D^n / \partial D^n$, which is homeomorphic to the sphere $S^n$. This gives an abstract CW structure on $S^n$ with one $0$-cell and one $n$-cell.

In Lean, the closedness of a classical complex in a Hausdorff space reads as follows.

```lean
open Topology in
example {X : Type*} [TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C] :
    IsClosed C :=
  RelCWComplex.isClosed
```

### The library around it

The small object argument in Mathlib produces factorizations through the same structure `RelativeCellComplex`, and the lifting theorem above is the reason why they give weak factorization systems. In a cofibrantly generated model category, the cofibrations are the retracts of relative cell complexes of the generating cofibrations. Mathlib in this edition has no model structure on `TopCat`, so this fact is not stated there for spaces.

The classical files contain many lemmas on skeletons, for example that the union of all `skeletonLT C n` is $C$. A subcomplex of a finite complex is finite by the instance `Subcomplex.finite_subcomplex_of_finite`.

::: mathlib
`Topology.RelCWComplex.cellFrontier_subset_finite_openCell` · `Mathlib.Topology.CWComplex.Classical.Basic`

The frontier of a cell lies in the union of $D$ and finitely many open cells of lower dimension.

<?decl Topology.RelCWComplex.cellFrontier_subset_finite_openCell?>
:::

Common errors of a learner: The first error is to use a Euclidean ball for the classical cells. The classical definition uses the sup norm on `Fin n → ℝ`, so the cells are cubes, while the abstract definition uses Euclidean disks. The second error is to expect a map between the two definitions; the source file of the abstract definition lists this equivalence as future work. The third error is to forget that `RelCWComplex C D` is a structure on a subset `C` of `X`. A space $Y$ is a CW complex by `CWComplex (univ : Set Y)`. The fourth error is to forget `[T2Space X]`, which many lemmas need.

### Exercises

1. (A) Let $f : X_1 \to X_2$ have an attachment of cells with $\iota$ empty. Show that $f$ is an isomorphism. *Hint:* the empty coproduct is initial, and a pushout along a map between initial objects is an isomorphism.
2. (A) Give a CW structure on the closed square $[-1, 1]^2$ with four $0$-cells, four $1$-cells and one $2$-cell. *Hint:* the characteristic map of the $2$-cell can be the identity, because the cells are cubes.
3. (B) Show that the class of maps with the left lifting property against a fixed $p$ is stable under composition, and deduce the case $J = \{0, 1, 2\}$ of the lifting theorem without the use of transfinite recursion.
4. (B) Let $C$ be a CW complex with finitely many cells in a Hausdorff space. Show that $C$ is compact. *Hint:* $C$ is a finite union of closed cells.
5. (C) Let $C$ be a CW complex in a Hausdorff space. Show that each subset of the $0$-skeleton is closed in $X$. *Hint:* show by induction on $n$ that a closed $n$-cell contains only finitely many $0$-cells, and then use property 4.
6. (C) Let $C$ be a CW complex whose graph of the $1$-skeleton has $v$ vertices and $e$ edges, and with no cells of dimension at least $2$. Assume $v$ and $e$ finite. Using the cellular chain complex $\mathbb{Z}^e \to \mathbb{Z}^v$ that sends an edge to the difference of its end points, show that $\mathrm{rank}\, H_1 - \mathrm{rank}\, H_0 = e - v$. *Hint:* the alternating sum of ranks of a finite complex of free groups equals that of its homology.

### Notes and history

Whitehead introduced CW complexes in 1949. The letters C and W stand for closure finiteness, which is property 3, and the weak topology, which is property 4. The source file of the classical definition cites the book *Algebraic Topology* of Hatcher, the file on subcomplexes cites the book *Topology* of Jänich, and the file of the abstract definition cites *Cellular Structures in Topology* of Fritsch and Piccinini.

The Mathlib Authors: the files in `AlgebraicTopology.RelativeCellComplex` are by Joël Riou. The abstract definition is by Jiazhen Xia, Elliot Dean Young and Joël Riou. The classical files `Basic`, `Finite` and `Subcomplex` are by Floris van Doorn and Hannah Scholz, and the file `Graph` is by Jun Kwon.

### Reference

<?reference?>
