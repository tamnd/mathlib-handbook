---
title: Embeddings and the Whitney theorem
kind: theory
modules:
  - Mathlib.Geometry.Manifold.SmoothEmbedding
  - Mathlib.Geometry.Manifold.WhitneyEmbedding
explains:
  E3: [Manifold.IsSmoothEmbedding, exists_embedding_euclidean_of_compact]
  E2: [Manifold.isSmoothEmbedding_iff, Manifold.IsSmoothEmbedding.isImmersion, Manifold.IsSmoothEmbedding.isEmbedding, Manifold.IsSmoothEmbedding.contMDiff, Manifold.IsSmoothEmbedding.id, Manifold.IsSmoothEmbedding.prodMap, Manifold.IsSmoothEmbedding.of_opens, ModelWithCorners.isSmoothEmbedding, SmoothBumpCovering.exists_immersion_euclidean]
  E1: auto
families: []
requires: [V23.C03, V23.C04, V23.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Embeddings and the Whitney theorem

### Overview

An immersion controls a map near each point, but not globally: it can cross itself, or come back close to itself. A smooth embedding is an immersion that is also a homeomorphism onto its image. Its image is then a submanifold, cut out in suitable charts by a linear subspace. This section defines smooth embeddings, shows by examples that neither condition implies the other, proves the slice form of the image, and proves that every compact manifold has an injective immersion into some $\mathbb{R}^N$ that is a closed embedding. That last theorem is the form of the theorem of Whitney that Mathlib has. Its proof uses the smooth bump coverings of Chapter 6.

The notation of Section 1 stays: $M$ and $N$ are $C^n$ manifolds modelled on $(E, H, I)$ and $(E'', G, J)$.

### Definitions

**Definition (Topological embedding).** A continuous map $f : M \to N$ is a *topological embedding* if it is injective and $M$ carries the topology induced by $f$: a set $U \subseteq M$ is open if and only if $U = f^{-1}(V)$ for an open set $V \subseteq N$. Equivalently, $f$ is a homeomorphism from $M$ onto $f(M)$ with the subspace topology. It is a *closed embedding* if in addition $f(M)$ is closed.

**Definition (Smooth embedding).** A map $f : M \to N$ is a *$C^n$ embedding* if it is a $C^n$ immersion in the sense of Section 1, with one complement $F$ for all points, and a topological embedding.

**Definition (Smooth bump covering).** Recall from Chapter 6 that, for a real manifold $M$ modelled on a finite-dimensional space, a *smooth bump covering* is a family $(f_i)_{i \in \iota}$ of smooth bump functions with centres $c_i$, such that $\operatorname{tsupp} f_i$ lies in the source of the chart at $c_i$, the supports are locally finite, and each $x$ has an index $i$ with $f_i = 1$ near $x$.

::: mathlib
`Manifold.IsSmoothEmbedding` · `Mathlib.Geometry.Manifold.SmoothEmbedding`

`IsSmoothEmbedding I J n f` is a structure with two fields, `isImmersion : IsImmersion I J n f` and `isEmbedding : IsEmbedding f`, with the lemma `isSmoothEmbedding_iff`. Smoothness is a consequence, `IsSmoothEmbedding.contMDiff`. The docstring warns that a smooth map that is a topological embedding, or even a homeomorphism, need not be a smooth embedding. There is no pointwise version.

<?decl Manifold.IsSmoothEmbedding?>
<?decl Manifold.isSmoothEmbedding_iff?>
<?decl Manifold.IsSmoothEmbedding.contMDiff?>
:::

### Theorems and proofs

**Theorem (Compact source).** Let $M$ be compact, $N$ Hausdorff, and $f : M \to N$ an injective $C^n$ immersion with one complement. Then $f$ is a smooth embedding, and $f(M)$ is closed.

*Proof.* The map $f$ is continuous, as a $C^n$ map. Let $C \subseteq M$ be closed. Then $C$ is compact, so $f(C)$ is compact, and a compact subset of a Hausdorff space is closed. So $f$ is a closed map. A continuous, injective and closed map is a homeomorphism onto its image: the inverse $f(M) \to M$ pulls back each closed set $C$ to $f(C) = f(C) \cap f(M)$, which is closed in $f(M)$. Taking $C = M$ shows that $f(M)$ is closed. $\square$

**Theorem (Slice charts).** Let $M$ have no boundary, so that charts have open images in $E$, and let $f : M \to N$ be a smooth embedding with complement $F$. For each $x \in M$ there is a chart $\psi$ of $N$ at $f(x)$, in the maximal atlas, and an isomorphism $A : E \times F \to E''$, with
$$\tilde\psi(f(M) \cap \operatorname{dom}\psi) = \tilde\psi(\operatorname{dom}\psi) \cap A(E \times \{0\}).$$

*Proof.* Take the presentation $(\varphi, \psi)$ and the isomorphism $A$ of the immersion at $x$, and write $U = \operatorname{dom}\varphi$ and $\Omega = \tilde\varphi(U)$, an open set of $E$. The image $f(U)$ is open in $f(M)$ because $f$ is an embedding, so $f(U) = f(M) \cap V_0$ for an open set $V_0$ of $N$. Restrict $\psi$ to the open set
$$V = V_0 \cap \operatorname{dom}\psi \cap \tilde\psi^{-1}(A(\Omega \times F)).$$
It contains $f(x)$, since $\tilde\psi(f(x)) = A(\tilde\varphi(x), 0)$. Let $y \in f(M) \cap V$. Then $y \in f(U)$, say $y = f(p)$, and $\tilde\psi(y) = A(\tilde\varphi(p), 0) \in A(E \times \{0\})$. Conversely, let $z \in \tilde\psi(V)$ with $z = A(u, 0)$. As $z \in A(\Omega \times F)$, $u \in \Omega$, so $u = \tilde\varphi(p)$ for some $p \in U$, and $\tilde\psi(f(p)) = A(u, 0) = z$. The point $f(p)$ lies in $f(U) \subseteq V_0$, in $\operatorname{dom}\psi$, and in $\tilde\psi^{-1}(A(\Omega \times F))$, so $f(p) \in f(M) \cap V$ and $z \in \tilde\psi(f(M) \cap V)$. $\square$

The slice form says that $f(M)$ is an embedded submanifold of $N$. The index of this edition has no declaration for embedded submanifolds, so the theorem has no Mathlib form.

**Theorem (Whitney, compact case).** Let $M$ be a compact Hausdorff smooth manifold modelled on a finite-dimensional real space $E$. Then there is $N \in \mathbb{N}$ and a $C^\infty$ map $e : M \to \mathbb{R}^N$ that is a closed embedding and has an injective differential at every point.

*Proof.* *Step 1: a finite bump covering.* By Chapter 6 there is a smooth bump covering $(f_i)_{i \in \iota}$ of $M$. Each support is nonempty, and the family of supports is locally finite. In a compact space a locally finite family of nonempty sets is finite: each point has a neighbourhood that meets finitely many sets, finitely many of these neighbourhoods cover $M$, and every set meets one of them. So $\iota$ is finite.

*Step 2: the map.* Write $\tilde\varphi_i$ for the extended chart at $c_i$. Define $e_0 : M \to (E \times \mathbb{R})^\iota$ by
$$e_0(x)_i = \big(f_i(x)\,\tilde\varphi_i(x),\; f_i(x)\big),$$
where the first entry means $0$ outside the chart source. It is $C^\infty$. The map $f_i$ is $C^\infty$, and the product $f_i \tilde\varphi_i$ is $C^\infty$ on the chart source. Outside the closed set $\operatorname{tsupp} f_i$, which lies in the chart source, the product is $0$ on an open set. These two open sets cover $M$.

*Step 3: injectivity.* Let $e_0(x) = e_0(y)$. Choose $i$ with $f_i = 1$ near $x$. The second entries give $f_i(y) = f_i(x) = 1$. So $y \in \operatorname{supp} f_i$, which lies in the chart source. The first entries give $\tilde\varphi_i(x) = 1 \cdot \tilde\varphi_i(x) = 1 \cdot \tilde\varphi_i(y) = \tilde\varphi_i(y)$. The chart is injective on its source, so $x = y$.

*Step 4: the differential.* Fix $x$ and $i$ with $f_i = 1$ on a neighbourhood $W$ of $x$. Let $P : (E \times \mathbb{R})^\iota \to E$ take the first entry of the $i$-th factor. It is continuous linear, and $P \circ e_0 = \tilde\varphi_i$ on $W$. The chain rule gives $P \circ de_{0,x} = d(\tilde\varphi_i)_x$. The differential of a chart at a point of its source is injective (Chapter 4). If $de_{0,x}(v) = 0$, then $d(\tilde\varphi_i)_x(v) = 0$, so $v = 0$.

*Step 5: Euclidean space.* The space $(E \times \mathbb{R})^\iota$ has finite dimension $N = |\iota|(\dim E + 1)$. Choose a continuous linear isomorphism $L$ onto $\mathbb{R}^N$ and put $e = L \circ e_0$. It is $C^\infty$ and injective, and $de_x = L \circ de_{0,x}$ is injective. By the first theorem of this section, or directly by compactness, $e$ is a closed embedding. $\square$

The proof needs no partition of unity, only the property $f_i = 1$ near each point. The factor $f_i(x)$ in the second entry is what makes the map injective. Without it, two points in different charts could have the same first entries.

### Examples

**Example (The figure eight).** Let $\beta : (-\pi, \pi) \to \mathbb{R}^2$, $\beta(t) = (\sin 2t, \sin t)$. Its derivative $(2\cos 2t, \cos t)$ never vanishes: $\cos t = 0$ forces $\cos 2t = 2\cos^2 t - 1 = -1$. It is injective. If $\sin s = \sin t$ with $s \ne t$, then $s = \pi - t$ or $s = -\pi - t$, so $\sin 2s = -\sin 2t$, and $\sin 2s = \sin 2t$ forces $\sin 2t = 0$, that is $t = \pm\pi/2$ and then $s = t$. So $\beta$ is an injective immersion. It is not an embedding: $\beta(t) \to (0, 0) = \beta(0)$ as $t \to \pi$, while $t$ stays away from $0$. So $\beta^{-1}$ is not continuous at $(0, 0)$.

**Counterexample (A smooth homeomorphism).** The map $t \mapsto t^3$ on $\mathbb{R}$ is $C^\infty$ and a homeomorphism, hence a topological embedding. Its derivative vanishes at $0$, so it is not a $C^1$ immersion and not a smooth embedding. This is the warning of the Mathlib docstring.

**Example (The irrational line on the torus).** Let $\alpha$ be irrational and $\gamma(t) = (e^{2\pi i t}, e^{2\pi i \alpha t})$ from $\mathbb{R}$ to the torus $S^1 \times S^1$. It is an immersion, since $\gamma'(t) \ne 0$. It is injective: $\gamma(s) = \gamma(t)$ gives $s - t \in \mathbb{Z}$ and $\alpha(s - t) \in \mathbb{Z}$, so $s = t$. Its image is dense, so it is not an embedding: an embedded line is locally closed (Exercise 5), a dense locally closed set is open, and a curve has empty interior in the torus.

**Example (The circle in $\mathbb{R}^4$).** Cover $S^1$ by two angle charts and take a bump covering with two functions $f_1, f_2$, with $f_1 = 1$ near the upper half and $f_2 = 1$ near the lower half. Then $E \times \mathbb{R} = \mathbb{R}^2$ and the proof gives an embedding $x \mapsto (f_1 \theta_1, f_1, f_2 \theta_2, f_2)$ of $S^1$ in $\mathbb{R}^4$. The standard inclusion in $\mathbb{R}^2$ shows that the dimension $N$ of the proof is far from optimal.

### The library around it

The theorem of Whitney is in `Mathlib.Geometry.Manifold.WhitneyEmbedding`. It has two public results. `SmoothBumpCovering.exists_immersion_euclidean` takes a bump covering with finite index type and returns $n$ and $e : M \to$ `EuclideanSpace ℝ (Fin n)` with `CMDiff ∞ e`, `Injective e` and an injective `mfderiv` at every point. `exists_embedding_euclidean_of_compact` adds `[T2Space M] [CompactSpace M]` and returns `IsClosedEmbedding e` in place of injectivity. The finite covering comes from `SmoothBumpCovering.exists_isSubordinate` and `SmoothBumpCovering.fintype`, and the closed embedding from `Continuous.isClosedEmbedding`. The map $e_0$ of the proof is an internal definition of the file and not in the index.

::: mathlib
`exists_embedding_euclidean_of_compact` · `Mathlib.Geometry.Manifold.WhitneyEmbedding`

The standing hypotheses are `[FiniteDimensional ℝ E]` and `[IsManifold I ∞ M]`. The result states the conclusion with `Injective (mfderiv% e x)`, not with `IsSmoothEmbedding`. To pass to `IsSmoothEmbedding` one needs the step from an injective differential to an immersion in normal form, which the index of this edition does not contain (Section 1).

<?decl exists_embedding_euclidean_of_compact?>
<?decl SmoothBumpCovering.exists_immersion_euclidean?>
<?decl SmoothBumpCovering.exists_isSubordinate?>
<?decl Continuous.isClosedEmbedding?>
:::

::: mathlib
`Manifold.IsSmoothEmbedding.prodMap` · `Mathlib.Geometry.Manifold.SmoothEmbedding`

The file proves that the identity is a smooth embedding (`IsSmoothEmbedding.id`), that products of smooth embeddings are smooth embeddings (`prodMap`), that the inclusion of an open subset is one (`of_opens`), that a model with corners is one (`ModelWithCorners.isSmoothEmbedding`), and that the inclusions into a disjoint union are (`sumInl`, `sumInr`). Composition, and the facts that a diffeomorphism is a smooth embedding, are TODO items.

<?decl Manifold.IsSmoothEmbedding.prodMap?>
<?decl Manifold.IsSmoothEmbedding.of_opens?>
<?decl ModelWithCorners.isSmoothEmbedding?>
<?decl Manifold.IsSmoothEmbedding.id?>
:::

Common errors of a learner:

- Expecting `exists_embedding_euclidean_of_compact` to give an `IsSmoothEmbedding`. It gives a closed embedding with injective differential.
- Using `SmoothBumpCovering.exists_immersion_euclidean` with an infinite index type. The dimension is $|\iota|(\dim E + 1)$, so the index type must be finite.
- Assuming that a smooth homeomorphism onto its image is a smooth embedding. The map $t \mapsto t^3$ is a counterexample.

### Exercises

1. (A) Show that the inclusion of an open subset $U \subseteq M$ is a smooth embedding with complement $0$.
2. (A) Show that $t \mapsto (t^2, t^3)$ is a topological embedding of $\mathbb{R}$ in $\mathbb{R}^2$ and not a smooth embedding.
3. (B) Show that $t \mapsto (\cos t, \sin t)$ induces a smooth embedding of $\mathbb{R}/2\pi\mathbb{Z}$ in $\mathbb{R}^2$. Hint: use the theorem on compact sources.
4. (B) Show that an injective immersion that is a proper map is a closed embedding. Hint: a proper map to a locally compact Hausdorff space is closed.
5. (B) Prove that the image of a smooth embedding of a manifold without boundary is locally closed. Hint: use slice charts.
6. (C) Let $M$ be compact of dimension $m$ and $e : M \to \mathbb{R}^N$ an injective immersion with $N > 2m + 1$. Show that for almost every unit vector $v$, the composite of $e$ with the orthogonal projection onto $v^\perp$ is still an injective immersion. Hint: the map $(x, y, t) \mapsto t(e(x) - e(y))$ on $M \times M \times \mathbb{R}$ and the map $(x, w) \mapsto de_x(w)$ on the tangent bundle have images of measure zero, by the easy case of Sard's theorem for maps from a lower dimension.

### Notes and history

Whitney proved in 1936 that every smooth $m$-manifold embeds in $\mathbb{R}^{2m+1}$, and in 1944 that it embeds in $\mathbb{R}^{2m}$. Exercise 6 is the step that lowers the dimension in the weak form. The Mathlib file lists the weak theorem for $\sigma$-compact manifolds as a TODO and notes that it needs a version of the theorem of Sard. The index of this edition has no declaration for the theorem of Sard or for regular values. It has the measure statement `MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero` for maps of a space to itself.

### Reference

<?reference?>
