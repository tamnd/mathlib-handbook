---
title: Simplicial complexes, polygons and polytopes
kind: theory
modules:
  - Mathlib.Analysis.Convex.SimplicialComplex.Basic
  - Mathlib.Analysis.Convex.SimplicialComplex.AffineIndependentUnion
  - Mathlib.Geometry.Polygon.Basic
  - Mathlib.Geometry.Convex.ConvexSpace.ToSSet
explains:
  E3: [Geometry.SimplicialComplex, Geometry.SimplicialComplex.space, Geometry.SimplicialComplex.disjoint_or_exists_inter_eq_convexHull, Geometry.SimplicialComplex.face_subset_face_iff, Geometry.SimplicialComplex.ofAffineIndependent, Polygon, Polygon.HasNondegenerateVertices, Convexity.ConvexSpace.toSSet, Convexity.ConvexSpace.toSSet.extraDegeneracy]
  E2: [Geometry.SimplicialComplex.vertices, Geometry.SimplicialComplex.facets, Geometry.SimplicialComplex.vertex_mem_convexHull_iff, Geometry.SimplicialComplex.convexHull_inter_convexHull, Geometry.SimplicialComplex.ofSimpleGraph, Polygon.boundary, Polygon.edgeSet, Polygon.HasNondegenerateVertices.hasNondegenerateEdges, Polygon.HasNondegenerateVertices.three_le, Convexity.ConvexSpace.toSSet_obj, Convexity.ConvexSpace.toSSet.cone, Convexity.ConvexSpace.toSSet.δ_zero, Convexity.ConvexSpace.toSSet.d_comp_cone_eq_sub]
  E1: auto
families: []
requires: [V07, V13, V16.C05, V22.C02, V22.C06, V22.C07]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Simplicial complexes, polygons and polytopes

### Overview

A polytope is the convex hull of finitely many points. Many questions about polytopes become combinatorial once the polytope is cut into simplices that meet along common faces. Such a decomposition is a simplicial complex. This section defines simplicial complexes by their vertex sets and proves that two faces meet in a face. It then studies polygons, the simplicial set of affine simplices in a convex space, and the vertices of a polytope.

### Definitions

Let $E$ be a vector space over an ordered field $K$.

**Definition (simplicial complex).** A *simplicial complex* in $E$ is a set $\mathcal{K}$ of nonempty finite subsets of $E$, the *faces*, such that:

1. each nonempty subset of a face is a face;
2. each face is affinely independent;
3. for faces $s, t$, $\mathrm{conv}(s) \cap \mathrm{conv}(t) \subseteq \mathrm{conv}(s \cap t)$.

The *vertices* are the points $x$ with $\{x\} \in \mathcal{K}$. The *facets* are the maximal faces. The *space* $|\mathcal{K}|$ is the union of the hulls $\mathrm{conv}(s)$ over all faces.

**Definition (abstract simplicial complex).** An *abstract simplicial complex* on a set $I$ is a set of nonempty finite subsets of $I$ that is closed under nonempty subsets.

**Definition (polygon).** A *polygon* with $n$ vertices in an affine space $P$ is a map $v : \mathbb{Z}/n \to P$. Its $i$-th *edge* is the segment $[v_i, v_{i+1}]$, and its *boundary* is the union of the edges. It has *nondegenerate edges* if $v_i \ne v_{i+1}$ for each $i$, and *nondegenerate vertices* if each triple $v_i, v_{i+1}, v_{i+2}$ is affinely independent.

**Definition (affine simplices of a convex space).** For a convex space $Y$ (Chapter 6), an *affine $n$-simplex* in $Y$ is an affine map $\Delta_n \to Y$ from the standard simplex on $n + 1$ vertices. Composition with the face and degeneracy maps makes these sets a simplicial set.

**Definition (polytope).** A *polytope* is the convex hull of a finite subset of $E$. Its *vertices* are its extreme points.

### Theorems and proofs

**Lemma (vertices in a hull).** Let $s$ be a finite affinely independent set, $u \subseteq s$ and $x \in s$. If $x \in \mathrm{conv}(u)$, then $x \in u$.

*Proof.* The point $x$ has the barycentric coordinates $\delta_x$ with respect to $s$. A combination of the points of $u$ gives coordinates supported in $u$. Barycentric coordinates with respect to an affinely independent set are unique (Chapter 2), so $\delta_x$ is supported in $u$, that is, $x \in u$. $\square$

**Theorem (faces meet in faces).** Let $s, t$ be faces of a simplicial complex $\mathcal{K}$.

1. $\mathrm{conv}(s) \cap \mathrm{conv}(t) = \mathrm{conv}(s \cap t)$.
2. Either the two hulls are disjoint, or their intersection is $\mathrm{conv}(u)$ for a face $u$.
3. $\mathrm{conv}(s) \subseteq \mathrm{conv}(t)$ if and only if $s \subseteq t$.

*Proof.* (1) The inclusion $\subseteq$ is condition (3), and $\supseteq$ is the monotonicity of the hull. (2) If $s \cap t \ne \emptyset$, it is a face by condition (1). (3) If $s \subseteq t$, the hull is monotone. Conversely, let $x \in s$. Then $x \in \mathrm{conv}(t) \cap \mathrm{conv}(s) = \mathrm{conv}(s \cap t)$ by (1). The set $s$ is affinely independent and $s \cap t \subseteq s$, so the lemma gives $x \in s \cap t$, and $x \in t$. $\square$

**Theorem (one independent set).** Let $\mathcal{A}$ be a set of nonempty finite subsets of $E$ that is closed under nonempty subsets. If the union $V$ of all members of $\mathcal{A}$ is affinely independent, then $\mathcal{A}$ is a simplicial complex.

*Proof.* Each face is a subset of $V$, so it is affinely independent. For condition (3), let $x \in \mathrm{conv}(s) \cap \mathrm{conv}(t)$. The two expressions give barycentric coordinates of $x$ with respect to $V$, supported in $s$ and in $t$. They are equal by uniqueness, so they are supported in $s \cap t$, and $x \in \mathrm{conv}(s \cap t)$. $\square$

For an abstract complex on a set $I$, place the vertex $i$ at the basis vector $e_i$ of $K^{(I)}$, the space of finitely supported functions. These vectors are affinely independent, so the theorem applies. A simple graph gives an abstract complex whose faces are the vertices and the edges.

**Theorem (polygons).** If a polygon has nondegenerate vertices, then it has nondegenerate edges, and $n \ge 3$.

*Proof.* If $v_i = v_{i+1}$, the triple $v_i, v_{i+1}, v_{i+2}$ has a repeated point and is affinely dependent. For $n \le 2$ each triple has a repeated point. $\square$

**Theorem (cones and contractibility).** Let $Y$ be a convex space and $y \in Y$. For an affine $n$-simplex $\sigma$, let $c_y(\sigma)$ be the affine $(n+1)$-simplex that sends the vertex $0$ to $y$ and the vertex $k + 1$ to $\sigma(k)$, as in Chapter 6. Then the face $d_0$ of $c_y(\sigma)$ is $\sigma$. On the chain complex of the simplicial set, the operator $c_y$ satisfies $\partial c_y + c_y \partial = \mathrm{id}$ in positive degrees. So the chain complex is acyclic in positive degrees.

*Proof.* An affine map out of $\Delta_{n+1}$ is fixed by its values on the vertices (Chapter 6). The face $d_0$ omits the vertex $0$, so it sends $k$ to $\sigma(k)$, which is $\sigma$. For $n \ge 1$ the faces $d_{k+1}$ of $c_y(\sigma)$ are $c_y(d_k \sigma)$. In the alternating sum $\partial c_y(\sigma) = \sigma - \sum_k (-1)^k c_y(d_k \sigma) = \sigma - c_y(\partial \sigma)$, which is the formula. $\square$

In Mathlib the operator $c_y$ is part of an extra degeneracy of the augmented simplicial set, which gives the stronger statement that the simplicial set is contractible.

**Theorem (vertices of a polytope).** Let $V \subseteq \mathbb{R}^d$ be finite and $P = \mathrm{conv}(V)$. Then $\mathrm{ext}(P) \subseteq V$ and $P = \mathrm{conv}(\mathrm{ext}(P))$.

*Proof.* The first claim is the lemma on extreme points of a hull in Section 1. The hull of a finite set is compact, and $P$ is convex, so the theorem of Minkowski in Section 1 gives $P = \mathrm{conv}(\mathrm{ext}(P))$. $\square$

### Examples

**Example (a square cut by a diagonal).** In $\mathbb{R}^2$ let $a = (0,0)$, $b = (1,0)$, $c = (1,1)$, $e = (0,1)$. The faces are $\{a, b, c\}$, $\{a, c, e\}$ and all their nonempty subsets. The two triangles meet in $\mathrm{conv}\{a, c\}$, the diagonal, which is the hull of $\{a, b, c\} \cap \{a, c, e\}$. So condition (3) holds, and the space is the square.

**Counterexample (a bad gluing).** Take the triangles $\{a, b, c\}$ and $\{a, b', c\}$ with $b' = (2, 0)$, so the second triangle contains the first. Their hulls meet in $\mathrm{conv}\{a, b, c\}$, but $\{a, b, c\} \cap \{a, b', c\} = \{a, c\}$. Condition (3) fails, so the two triangles and their subsets do not form a simplicial complex.

**Example (a square as a polygon).** The polygon $(a, b, c, e)$ has nondegenerate vertices. The polygon $(a, b, c, b)$ has nondegenerate edges, but the triple $b, c, b$ is dependent.

### The library around it

::: mathlib
`Geometry.SimplicialComplex` · `Mathlib.Analysis.Convex.SimplicialComplex.Basic`

The structure has the fields `indep` and `inter_subset_convexHull`. `Geometry.SimplicialComplex.vertices`, `Geometry.SimplicialComplex.facets` and `Geometry.SimplicialComplex.space` are the definitions above, and `Geometry.SimplicialComplex.vertex_mem_convexHull_iff` is the lemma on vertices in a hull.

<?decl Geometry.SimplicialComplex?>
:::

::: mathlib
`Geometry.SimplicialComplex.disjoint_or_exists_inter_eq_convexHull` · `Mathlib.Analysis.Convex.SimplicialComplex.Basic`

Part (2) of the theorem on faces. Part (1) is `Geometry.SimplicialComplex.convexHull_inter_convexHull`, and part (3) is `Geometry.SimplicialComplex.face_subset_face_iff`.

<?decl Geometry.SimplicialComplex.disjoint_or_exists_inter_eq_convexHull?>
:::

::: mathlib
`Geometry.SimplicialComplex.ofAffineIndependent` · `Mathlib.Analysis.Convex.SimplicialComplex.AffineIndependentUnion`

The theorem on one independent set, as a construction. `Geometry.SimplicialComplex.ofSimpleGraph` does it for a simple graph.

<?decl Geometry.SimplicialComplex.ofAffineIndependent?>
:::

::: mathlib
`Polygon` · `Mathlib.Geometry.Polygon.Basic`

`Polygon P n` has the single field `vertices : Fin n → P`. `Polygon.edgeSet` is the edge as an `affineSegment`, and `Polygon.boundary` their union.

<?decl Polygon?>
:::

::: mathlib
`Polygon.HasNondegenerateVertices` · `Mathlib.Geometry.Polygon.Basic`

Each triple `![poly i, poly (i + 1), poly (i + 2)]` is affinely independent. `Polygon.HasNondegenerateVertices.hasNondegenerateEdges` and `Polygon.HasNondegenerateVertices.three_le` are the theorem on polygons.

<?decl Polygon.HasNondegenerateVertices?>
:::

::: mathlib
`Convexity.ConvexSpace.toSSet` · `Mathlib.Geometry.Convex.ConvexSpace.ToSSet`

`toSSet R Y` is the simplicial set with `Convexity.ConvexSpace.toSSet_obj` giving the affine maps from `StdSimplex R (Fin (n + 1))` to `Y` as $n$-simplices. `Convexity.ConvexSpace.toSSet.cone`, `Convexity.ConvexSpace.toSSet.δ_zero` and `Convexity.ConvexSpace.toSSet.d_comp_cone_eq_sub` are the cone operator and its formulas.

<?decl Convexity.ConvexSpace.toSSet?>
:::

::: mathlib
`Convexity.ConvexSpace.toSSet.extraDegeneracy` · `Mathlib.Geometry.Convex.ConvexSpace.ToSSet`

For `y : Y`, an extra degeneracy of the augmented simplicial set, built from the cone at `y`. It gives contractibility.

<?decl Convexity.ConvexSpace.toSSet.extraDegeneracy?>
:::

The index has no declaration for polytopes as such, for their faces, or for the Euler relation $f_0 - f_1 + f_2 = 2$. A polytope can be written as `convexHull ℝ ↑s` for a `Finset` `s`. Polygons have no interior, area or winding number in this edition.

### Exercises

1. (A) List all faces, facets and vertices of the complex of the square cut by a diagonal.
2. (A) Show that the polygon $(a, b, c)$ of a triangle with distinct vertices on no line has nondegenerate vertices.
3. (B) Show that the complex of the simple graph with vertices $1, 2, 3$ and edges $\{1, 2\}$, $\{2, 3\}$ has as its space $[e_1, e_2] \cup [e_2, e_3]$ in $K^{(3)}$.
4. (B) Show that each simplicial complex with finitely many vertices whose space is $\mathrm{conv}(V)$ for a finite $V$ has all points of $\mathrm{ext}(\mathrm{conv}(V))$ among its vertices.
5. (B) Show that a polytope in $\mathbb{R}^2$ with $k \ge 3$ vertices, not on a line, is the space of a simplicial complex with $k - 2$ facets. Hint: cut along the diagonals from one vertex.
6. (C) Show that $\partial c_y(\sigma) = \sigma - y$ for a $0$-simplex $\sigma$. Deduce that with integer coefficients the homology of the chain complex in degree $0$ is $\mathbb{Z}$, for $Y$ nonempty.

### Notes and history

The combinatorial study of simplicial complexes goes back to Poincaré's work on analysis situs at the end of the nineteenth century. Eilenberg and Zilber introduced simplicial sets around 1950. The Mathlib file on simplicial complexes names Yaël Dillies and Bhavik Mehta as authors, and the file on affinely independent unions names Bolton Bailey. The file on polygons names A. M. Berns, and the file on simplicial sets of convex spaces names Joël Riou.

### Reference

<?reference?>
