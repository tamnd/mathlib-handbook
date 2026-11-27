---
title: Smooth maps, charts, products and normed spaces
kind: theory
modules:
  - Mathlib.Geometry.Manifold.ContMDiff.Atlas
  - Mathlib.Geometry.Manifold.ContMDiff.Constructions
  - Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
  - Mathlib.Geometry.Manifold.ContMDiffMap
explains:
  E3: [contMDiff_iff_contDiff, IsManifold.mem_maximalAtlas_iff_contMDiffOn, contMDiff_prod_iff, ContMDiffMap]
  E2: [ModelWithCorners.contMDiff, ModelWithCorners.contMDiffOn_symm, contMDiffOn_of_mem_maximalAtlas, contMDiffOn_symm_of_mem_maximalAtlas, contMDiffOn_chart, contMDiffOn_chart_symm, contMDiffOn_extChartAt, OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn, isLocalStructomorphOn_contDiffGroupoid_iff, contMDiffWithinAt_iff_contDiffWithinAt, contMDiffOn_iff_contDiffOn, ContDiff.contMDiff, ContMDiff.contDiff, ContDiff.comp_contMDiff, ContinuousLinearMap.contMDiff, ContMDiff.clm_comp, ContMDiff.clm_apply, contMDiff_fst, contMDiff_snd, ContMDiff.prodMk, ContMDiff.prodMap, contMDiff_prod_module_iff, contMDiff_pi_iff, contMDiff_pi_module_iff, ContMDiff.sumElim, ContMDiffMap.comp, ContMDiffMap.id, ContMDiffMap.const, ContMDiffMap.prodMk, ContMDiffMap.coe_injective]
  E1: auto
families: []
requires: [V23.C01, V23.C02, V17.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Smooth maps, charts, products and normed spaces

### Overview

Section 1 defined $C^n$ maps and proved that they compose. This section supplies the basic $C^n$ maps from which others are built. Between normed spaces with the trivial models, the new notion is the old one of Volume 17. The model $I$ and the charts of the maximal atlas are $C^n$, and conversely a partial homeomorphism that is $C^n$ in both directions belongs to the maximal atlas. On products, the projections are $C^n$ and a map into a product is $C^n$ exactly when its two components are. The section ends with the bundled type of $C^n$ maps.

### Definitions

The constructions need no new notion of smoothness. Only one new type appears.

**Definition (Bundled $C^n$ maps).** For models $I, I'$ and charted spaces $M, M'$, the type $C^n(I, M; I', M')$ is the type of pairs of a map $f : M \to M'$ and a proof that $f$ is $C^n$.

The identity, constant maps, composites, projections and pairs are elements of these types, by the theorems below and of Section 1.

::: mathlib
`ContMDiffMap` · `Mathlib.Geometry.Manifold.ContMDiffMap`

`ContMDiffMap I I' M M' n` is the subtype `{f : M → M' // CMDiff n f}`, with notation `C^n⟮I, M; I', M'⟯` in the scope `Manifold`, and `C^n⟮I, M; 𝕜⟯` for maps into `𝕜` with the trivial model. It has a `FunLike` instance, so its elements apply to points, and `ContMDiffMap.coe_injective` says that an element is determined by its map. The constructions are `ContMDiffMap.id`, `ContMDiffMap.const`, `ContMDiffMap.comp`, `ContMDiffMap.fst`, `ContMDiffMap.snd` and `ContMDiffMap.prodMk`.

<?decl ContMDiffMap?>
<?decl ContMDiffMap.comp?>
:::

### Theorems and proofs

**Theorem (Normed spaces).** Let $f : E \to E'$, with the trivial models on both sides. Then $f$ is $C^n$ within $s$ at $x$ in the sense of manifolds if and only if it is $C^n$ within $s$ at $x$ in the sense of Volume 17. The same holds for $C^n$ on a set, at a point, and everywhere.

*Proof.* For the trivial model of $E$, every extended chart is the identity (Chapter 2, Section 2), and the range of the model is $E$. By the formula of Section 1, $f$ is $C^n$ within $s$ at $x$ for the manifolds if and only if $f$ is continuous within $s$ at $x$ and $\mathrm{id} \circ f \circ \mathrm{id}$ is $C^n$ within $s \cap E = s$ at $x$. A map that is $C^n$ within $s$ at $x$ is continuous within $s$ at $x$, so the first condition follows from the second. The other three forms follow from this one, since each is a condition on all points. $\square$

**Theorem (The model is $C^n$).** Let $H$ be a charted space over itself. The map $I : H \to E$ is $C^n$, and $I^{-1} : E \to H$ is $C^n$ on $\mathrm{range}\, I$, for every $n$.

*Proof.* The preferred chart of $H$ at $y$ is the identity, so its extended chart is $I$, with inverse $I^{-1}$. The extended charts of $E$ are identities. In charts, $I$ at $y$ becomes $\mathrm{id} \circ I \circ I^{-1}$, which equals the identity on $\mathrm{range}\, I$. The identity is $C^n$ within $\mathrm{range}\, I$, and $I$ is continuous, so $I$ is $C^n$ at $y$. For $z \in \mathrm{range}\, I$, the map $I^{-1}$ becomes $I \circ I^{-1} \circ \mathrm{id}$ within $\mathrm{range}\, I$ at $z$. It again equals the identity on $\mathrm{range}\, I$, and $I^{-1}$ is continuous. $\square$

**Theorem (Charts are $C^n$).** Let $M$ be a $C^n$ manifold and $e$ a partial homeomorphism of $M$ to $H$. Then $e$ is in the maximal atlas if and only if $e$ is $C^n$ on its source and $e^{-1}$ is $C^n$ on its target.

*Proof.* Assume that $e$ is in the maximal atlas, and let $x \in e.\mathrm{source}$. The identity chart of $H$ is in the maximal atlas of $H$. By the corollary of Section 1, $e$ is $C^n$ at $x$ if $e$ is continuous at $x$ and $I \circ e \circ e_I^{-1}$ is $C^n$ within $\mathrm{range}\, I$ at $e_I(x)$. Continuity holds on the open source. The map equals $I \circ e \circ e^{-1} \circ I^{-1}$, which is the identity on $e_I.\mathrm{target}$. That set is a neighbourhood of $e_I(x)$ within $\mathrm{range}\, I$, by Chapter 2, Section 2. So the map is $C^n$ within $\mathrm{range}\, I$ there. Since the source is open, $e$ is $C^n$ on its source. The same argument with the charts reversed applies to $e^{-1}$ on the target.

Conversely, assume the two conditions, and let $c$ be a chart of the atlas. The definition of the maximal atlas asks that $e^{-1} \gg c$ and $c^{-1} \gg e$ lie in $G_n(I)$. For the first, the map $I \circ c \circ e^{-1} \circ I^{-1}$ must be $C^n$ on $T = (I^{-1})^{-1}((e^{-1} \gg c).\mathrm{source}) \cap \mathrm{range}\, I$, as a map of $E$. Write it as the composite of four maps: $I^{-1}$, which is $C^n$ on $\mathrm{range}\, I$ as a map $E \to H$; $e^{-1}$, which is $C^n$ on $e.\mathrm{target}$; $c$, which is $C^n$ on $c.\mathrm{source}$ by the first part; and $I$, which is $C^n$. On $T$ each map sends the set into the next domain. By the composition theorem of Section 1, the composite is $C^n$ on $T$ as a map between manifolds with the trivial models. By the theorem on normed spaces, it is $C^n$ on $T$ in the usual sense. The second condition has the same proof with $e$ and $c$ exchanged. $\square$

**Theorem (Products).** Let $M$, $N$ and $P$ be charted spaces with models $I$, $J$ and $K$, and give $M \times N$ the model $I \times J$. Then the projections $M \times N \to M$ and $M \times N \to N$ are $C^n$. A map $f : P \to M \times N$ is $C^n$ if and only if its components $f_1$ and $f_2$ are $C^n$.

*Proof.* The preferred chart of $M \times N$ at $(x, y)$ is $\varphi_x \times \psi_y$, so its extended chart is $\hat\varphi_x \times \hat\psi_y$ (Chapter 2, Section 2), and $\mathrm{range}(I \times J) = \mathrm{range}\, I \times \mathrm{range}\, J$. In charts, the first projection becomes $\hat\varphi_x \circ \mathrm{pr}_1 \circ (\hat\varphi_x \times \hat\psi_y)^{-1}$. On the target of the product chart this equals the linear projection $\mathrm{pr}_1 : E \times F \to E$, which is $C^\infty$. The projection is continuous, so it is $C^n$. The same holds for the second projection.

If $f$ is $C^n$, then $f_1 = \mathrm{pr}_1 \circ f$ and $f_2 = \mathrm{pr}_2 \circ f$ are $C^n$ by composition. Conversely, assume $f_1$ and $f_2$ are $C^n$, and let $z \in P$. Then $f$ is continuous. Let $\hat\chi = \hat\chi_z$. In charts, $f$ becomes the map $w \mapsto (\hat\varphi_{f_1(z)}(f_1(\hat\chi^{-1}(w))),\ \hat\psi_{f_2(z)}(f_2(\hat\chi^{-1}(w))))$, whose components are $f_1$ and $f_2$ in charts. Both are $C^n$ within $\mathrm{range}\, K$ at $\hat\chi(z)$. A map into $E \times F$ whose two components are $C^n$ within a set at a point is $C^n$ there (Volume 17, Chapter 4). So $f$ is $C^n$ at $z$. $\square$

**Corollary (Products of maps).** If $f : M \to M'$ and $g : N \to N'$ are $C^n$, then $f \times g : M \times N \to M' \times N'$ is $C^n$.

*Proof.* Its components are $f \circ \mathrm{pr}_1$ and $g \circ \mathrm{pr}_2$. They are $C^n$ by composition, and the theorem applies. $\square$

::: mathlib
`IsManifold.mem_maximalAtlas_iff_contMDiffOn` · `Mathlib.Geometry.Manifold.ContMDiff.Atlas`

The theorem on charts is `IsManifold.mem_maximalAtlas_iff_contMDiffOn` under `[IsManifold I n M]`. The forward parts `contMDiffOn_of_mem_maximalAtlas` and `contMDiffOn_symm_of_mem_maximalAtlas` need no instance, and the preferred charts give `contMDiffOn_chart`, `contMDiffOn_chart_symm` and `contMDiffOn_extChartAt`. The model gives `ModelWithCorners.contMDiff` and `ModelWithCorners.contMDiffOn_symm`. The normed space theorem is `contMDiff_iff_contDiff`, with the aliases `ContMDiff.contDiff` and `ContDiff.contMDiff`, and `contMDiffWithinAt_iff_contDiffWithinAt`. The product theorem is `contMDiff_prod_iff`, with `contMDiff_fst`, `contMDiff_snd`, `ContMDiff.prodMk` and `ContMDiff.prodMap`.

<?decl IsManifold.mem_maximalAtlas_iff_contMDiffOn?>
<?decl contMDiff_iff_contDiff?>
<?decl contMDiff_prod_iff?>
<?decl ContMDiff.prodMap?>
:::

### Examples

**Example (Linear maps and their compositions).** A continuous linear map $L : E \to F$ is $C^n$ for the trivial models (`ContinuousLinearMap.contMDiff`), by the theorem on normed spaces. If $f : M \to F$ is $C^n$ and $g : F \to F'$ is $C^n$ in the usual sense, then $g \circ f$ is $C^n$ (`ContDiff.comp_contMDiff`). So sums, scalar multiples and norms away from $0$ of $C^n$ functions into normed spaces are $C^n$. If $g : M \to (F_1 \to_L F_2)$ and $f : M \to F_1$ are $C^n$, then $x \mapsto g(x)(f(x))$ is $C^n$ (`ContMDiff.clm_apply`), since evaluation is a continuous bilinear map. The same holds for the composite $x \mapsto g(x) \circ f(x)$ (`ContMDiff.clm_comp`).

**Example (The sphere in its space).** The inclusion of the unit sphere $S \subseteq E$ is $C^\omega$. In the chart of the stereographic projection from $-v$, it becomes the inverse of the projection, an explicit rational map, which is analytic.

**Example (Functions on a product).** The map $\mathbb{R} \times S \to E$, $(t, x) \mapsto t x$, is $C^\infty$: it is the composite of the pair of the two $C^\infty$ maps $\mathrm{pr}_1$ and $\mathrm{incl} \circ \mathrm{pr}_2$ into $\mathbb{R} \times E$, with the bilinear map $(t, v) \mapsto t v$. One must check that the product model on $\mathbb{R} \times E$ and the trivial model of the normed space $\mathbb{R} \times E$ give the same notion. They do, because both have identity extended charts.

**Example (Families).** For a family of models $I_i$ indexed by a finite type, a map into $\prod_i M_i$ is $C^n$ if and only if each component is (`contMDiff_pi_iff`). For maps into a product of normed spaces with the trivial model, `contMDiff_pi_module_iff` gives the same statement.

### The library around it

The module `Mathlib.Geometry.Manifold.ContMDiff.Constructions` also treats disjoint unions: `ContMDiff.sumElim` glues two $C^n$ maps on $M$ and $M'$ into a map on $M \sqcup M'$. The module `Mathlib.Geometry.Manifold.ContMDiff.Atlas` relates $C^n$ maps to the local structomorphisms of Chapter 1: by `isLocalStructomorphOn_contDiffGroupoid_iff`, a partial homeomorphism between manifolds with the same model is a local structomorphism for $G_n(I)$ exactly when it is $C^n$ in both directions. The module `Mathlib.Geometry.Manifold.ContMDiff.NormedSpace` has many lemmas on maps into spaces of continuous linear maps. They are used for the smoothness of the derivative in Chapter 4 and for vector bundles in Chapter 5.

Under pointwise operations, the bundled maps $C^n(I, M; \mathbb{K})$ form a ring (Exercise 7).

Common errors of a learner:

- Using the product model `I.prod J` on `E × F` where the trivial model `𝓘(𝕜, E × F)` is expected. The two are different terms, and lemmas stated for one do not rewrite the other. `contMDiff_prod_iff` uses the product model, and `contMDiff_prod_module_iff` the trivial one.
- Expecting `IsManifold.mem_maximalAtlas_iff_contMDiffOn` without the instance `IsManifold I n M`.
- Using the deprecated `contMDiffOn_model_symm`. The current name is `ModelWithCorners.contMDiffOn_symm`.

### Exercises

1. (A) Show that the diagonal $M \to M \times M$ and the swap $M \times N \to N \times M$ are $C^n$.
2. (A) Show that the sum of two $C^n$ maps $M \to F$ is $C^n$.
3. (A) Show that the inclusion of an open subset $U \subseteq E$, with the charts of Chapter 2, is $C^n$, using the theorem on normed spaces.
4. (B) Show that a $C^n$ map $f : M \to \mathbb{R}$ with no zero has a $C^n$ inverse $1/f$.
5. (B) Prove that $(\varphi_x)^{-1}$ is $C^n$ on the target of $\varphi_x$ directly from the definition, without the maximal atlas.
6. (B) Let $M$ be the line $\mathbb{R}$ with the single chart $t \mapsto t^3$. Show that the identity map from $M$ to $\mathbb{R}$ with the trivial atlas is $C^0$ and not $C^1$, while its inverse is $C^\omega$.
7. (C) Show that the bundled maps $C^n(I, M; \mathbb{K})$ form a commutative ring, and that the evaluation at a point is a ring homomorphism.

### Notes and history

The smoothness of the atlas and of products is part of every text on manifolds. Exercise 6 is the standard example of two smooth structures on $\mathbb{R}$ that differ as atlases and are diffeomorphic, as Section 3 shows.

### Reference

<?reference?>
