---
title: Isometries, dilations and similarities
kind: api
modules:
  - Mathlib.Topology.MetricSpace.Isometry
  - Mathlib.Topology.MetricSpace.Dilation
  - Mathlib.Topology.MetricSpace.DilationEquiv
  - Mathlib.Topology.MetricSpace.Similarity
  - Mathlib.Topology.MetricSpace.Congruence
explains:
  E2: [Isometry.injective, Isometry.isEmbedding, Isometry.isClosedEmbedding, IsometryEquiv.completeSpace_iff, Dilation.edist_eq, Dilation.ratio_unique, Congruent.similar, similar_iff_exists_dist_eq]
  E1: auto
families: []
requires: [V04, V13.C01, V13.C03, V13.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Isometries, dilations and similarities

### Overview

A map between metric spaces is an isometry when it keeps all distances: $d(f(x), f(y)) = d(x, y)$ for all $x$ and $y$. A map is a dilation with ratio $r > 0$ when it multiplies all distances by $r$. These are the morphisms of metric geometry. An isometry of the plane is a rigid motion, and a dilation of the plane is a similarity transformation of school geometry.

The five modules of this section hold the library for these maps. The predicate `Isometry` and the bundled bijections `IsometryEquiv` come first. The bundled dilations `Dilation` and their bijective form `DilationEquiv` follow. The last two modules compare two families of points, not two spaces: the predicates `Congruent` and `Similar` say that two indexed families have the same distances, or proportional distances. The section uses the metric spaces of Chapter 3, the embeddings of Chapter 1 and the uniform embeddings of Chapter 7.

### The library around it

#### Isometries

The predicate `Isometry f` is defined for a map $f : \alpha \to \beta$ between pseudo extended metric spaces. It says that `edist (f x) (f y) = edist x y` for all $x$ and $y$. The extended distance is the primary notion, and the real distance follows. In a pseudometric space, `isometry_iff_dist_eq` gives the form with `Dist.dist`, and `Isometry.of_dist_eq` builds an isometry from it. The forms with the nonnegative distance are `isometry_iff_nnDist_eq` and `Isometry.nnDist_eq`. The nonnegative distance is `NNDist.nnDist`, with a capital letter in the middle of the name.

The basic closure properties are as expected: `isometry_id`, `Isometry.comp`, `Isometry.prodMap` and `Isometry.piMap` for a finite product with the sup distance. The inclusion of a subtype is an isometry by `isometry_subtypeVal`, and `isometry_subsingleton` says that each map on a subsingleton is an isometry. If $g$ is a right inverse of an isometry $f$, then $g$ is an isometry (`Isometry.right_inv`).

An isometry keeps balls and diameters. The lemmas `Isometry.preimage_ball`, `Isometry.preimage_closedBall` and `Isometry.preimage_sphere` state $f^{-1}(B(f(x), r)) = B(x, r)$. The lemmas `Isometry.mapsTo_ball` and `Isometry.mapsTo_sphere` give the forward inclusions, and `Isometry.diam_image` and `Isometry.ediam_image` state $\operatorname{diam} f(s) = \operatorname{diam} s$.

An isometry is Lipschitz and antilipschitz with constant $1$: `Isometry.lipschitzWith` and `Isometry.antilipschitzWith`. The topological consequences come from this.

1. `Isometry.injective`: an isometry from an extended metric space is injective. If $f(x) = f(y)$, then $\operatorname{edist}(x, y) = \operatorname{edist}(f(x), f(y)) = 0$, so $x = y$.
2. `Isometry.isUniformEmbedding`, and its weaker forms `Isometry.isUniformInducing`, `Isometry.isEmbedding` and `Isometry.continuous`. The uniformity of $\alpha$ is the pullback of the uniformity of $\beta$, because the entourages $\{(x, y) : \operatorname{edist}(x, y) < \varepsilon\}$ correspond under $f \times f$. So $f$ is a uniform embedding, and in particular a topological embedding.
3. `Isometry.isClosedEmbedding`: if $\alpha$ is complete and $\beta$ is an extended metric space, then the range of $f$ is closed. Proof: the range is the image of a complete space under a uniform embedding, so it is complete, and a complete subset of a Hausdorff uniform space is closed.

The converse direction also has a name. If the topology or uniformity of $\alpha$ is induced from $\beta$ by $f$, then $f$ is an isometry for the induced metric: `EMetricSpace.isometry_induced`, `PseudoMetricSpace.isometry_induced` and `Topology.IsEmbedding.to_isometry`. The lemmas `Isometry.comp_continuous_iff` and `Isometry.tendsto_nhds_iff` let a proof drop an isometry in front of a continuity or a limit statement.

#### Isometric bijections

The structure `IsometryEquiv α β`, with the notation `α ≃ᵢ β`, is an equivalence whose forward map is an isometry. It follows the pattern of `Equiv` and `Homeomorph`. It has `IsometryEquiv.refl`, `IsometryEquiv.symm` and `IsometryEquiv.trans`, the simp lemmas `IsometryEquiv.apply_symm_apply` and `IsometryEquiv.symm_apply_apply`, and the forgetful maps `IsometryEquiv.toEquiv` and `IsometryEquiv.toHomeomorph`. The self isometries of a space form a group, `IsometryEquiv.instGroup`, with multiplication equal to composition: `IsometryEquiv.coe_mul` states $e_1 * e_2 = e_1 \circ e_2$. An isometric bijection maps balls onto balls (`IsometryEquiv.image_ball`), keeps the diameter of each set (`IsometryEquiv.diam_image`), and transfers completeness: `IsometryEquiv.completeSpace_iff`. The last result holds because both $e$ and $e^{-1}$ are uniformly continuous, and a uniform equivalence transfers Cauchy filters in both directions.

An isometry from an extended metric space onto its range gives an isometric bijection, `Isometry.isometryEquivOnRange`. Several standard identifications of product spaces are isometric bijections.

| Lean name | Statement |
|---|---|
| `IsometryEquiv.funUnique` | $(\iota \to \alpha) \cong \alpha$ when $\iota$ has one element |
| `IsometryEquiv.piFinTwo` | a function on `Fin 2` is a pair |
| `IsometryEquiv.sumArrowIsometryEquivProdArrow` | $(\alpha \oplus \beta \to \gamma) \cong (\alpha \to \gamma) \times (\beta \to \gamma)$ |
| `Fin.appendIsometry` | $(\mathrm{Fin}\ m \to \alpha) \times (\mathrm{Fin}\ n \to \alpha) \cong (\mathrm{Fin}\ (m + n) \to \alpha)$ |
| `IsometryEquiv.piCongrLeft` | reindex a finite product along an equivalence |

The class `IsometryClass F α β` says that each element of a type $F$ of bundled maps is an isometry. It has the same lemmas as the predicate, for example `IsometryClass.dist_eq` and `IsometryClass.diam_image`, and `IsometryClass.toIsometryEquiv` turns an element of a class of bijective isometries into an `IsometryEquiv`.

#### Dilations

A dilation $f : \alpha \to \beta$ with ratio $r$ satisfies $\operatorname{edist}(f(x), f(y)) = r \cdot \operatorname{edist}(x, y)$ for all $x$ and $y$, with $r \neq 0$ and $r \neq \infty$. The structure `Dilation α β`, with the notation `α →ᵈ β`, holds the map and the existence of such an $r$. The class `DilationClass` is the `FunLike` version. The value $r = 0$ is excluded so that a dilation of extended metric spaces is injective (`Dilation.injective`). The value $r = \infty$ is excluded so that the ratio is a nonnegative real number.

The ratio is the function `Dilation.ratio f`, a term of $\mathbb{R}_{\ge 0}$. It is a choice. When all distances in $\alpha$ are $0$ or $\infty$, no ratio is determined, and the library sets `Dilation.ratio f = 1` (`Dilation.ratio_of_trivial`). In all other cases the ratio is unique. The lemma `Dilation.ratio_unique` says: if $\operatorname{edist}(x, y) \notin \{0, \infty\}$ and $\operatorname{edist}(f(x), f(y)) = r \cdot \operatorname{edist}(x, y)$, then $r$ is the ratio. The proof divides by $\operatorname{edist}(x, y)$. The main identity `Dilation.edist_eq` then holds for all pairs: $\operatorname{edist}(f(x), f(y)) = \operatorname{ratio}(f) \cdot \operatorname{edist}(x, y)$. For a pair with distance $0$ or $\infty$ both sides agree because $\operatorname{ratio}(f)$ is a positive finite number. The real forms are `Dilation.dist_eq` and `Dilation.nnDist_eq`, and the positivity is `Dilation.ratio_pos`.

A proof builds a dilation with `Dilation.mkOfDistEq`, from a map and a real ratio. An isometry is a dilation with ratio $1$: `Isometry.toDilation` and `Isometry.toDilation_ratio`. Dilations compose with `Dilation.comp`. When the source is a metric space with at least two points, the ratios multiply: `Dilation.ratio_comp`. The form `Dilation.ratio_comp'` asks only for two points at finite nonzero distance. Without such points the ratio of $f$ and of $g \circ f$ is $1$ by convention, while the ratio of $g$ can be any number. The self dilations form a monoid, `Dilation.instMonoid`, and `Dilation.ratioHom` is the ratio as a monoid homomorphism to $\mathbb{R}_{\ge 0}$.

Since $f$ is Lipschitz with constant $r$ and antilipschitz with constant $r^{-1}$, a dilation has the topological properties of an isometry: `Dilation.lipschitzWith`, `Dilation.antilipschitzWith`, `Dilation.isUniformEmbedding`, `Dilation.isEmbedding`, and `Dilation.isClosedEmbedding` when the source is complete. It maps balls to balls with the radius multiplied by the ratio (`Dilation.mapsTo_ball`), and it maps bounded sets to bounded sets in both directions: `Dilation.comap_cobounded`.

#### Bijective dilations

The structure `DilationEquiv X Y`, with notation `X ≃ᵈ Y`, is an equivalence whose forward map is a dilation. The inverse of a dilation with ratio $r$ is a dilation with ratio $r^{-1}$, so the type has `DilationEquiv.symm` with `DilationEquiv.ratio_symm`, and `DilationEquiv.trans` with `DilationEquiv.ratio_trans`. The bijective self dilations of a space form a group, `DilationEquiv.instGroup`, and `DilationEquiv.ratioHom` is the ratio as a group homomorphism. Each `IsometryEquiv` gives a `DilationEquiv` with ratio $1$ through `IsometryEquiv.toDilationEquiv`, and each dilation equivalence is a homeomorphism through `DilationEquiv.toHomeomorph`.

#### Congruent and similar families

The modules `Mathlib.Topology.MetricSpace.Congruence` and `Mathlib.Topology.MetricSpace.Similarity` compare two families of points $v_1 : \iota \to P_1$ and $v_2 : \iota \to P_2$ with the same index type. A typical case is two triangles, with $\iota = \mathrm{Fin}\ 3$.

1. `Congruent v₁ v₂` says $\operatorname{edist}(v_1(i), v_1(j)) = \operatorname{edist}(v_2(i), v_2(j))$ for all $i$ and $j$. The scoped notation is `v₁ ≅ v₂`.
2. `Similar v₁ v₂` says that there is $r \neq 0$ in $\mathbb{R}_{\ge 0}$ with $\operatorname{edist}(v_1(i), v_1(j)) = r \cdot \operatorname{edist}(v_2(i), v_2(j))$ for all $i$ and $j$.

Both relations are reflexive, symmetric and transitive: `Congruent.refl`, `Congruent.symm`, `Congruent.trans` and the same names for `Similar`. A congruence is a similarity with $r = 1$ (`Congruent.similar`). In a pseudometric space the forms with the real distance are `congruent_iff_dist_eq` and `similar_iff_exists_dist_eq`. Since the distance is symmetric and $d(x, x) = 0$, it is enough to compare distinct indices: `congruent_iff_pairwise_dist_eq` and `similar_iff_exists_pairwise_dist_eq`.

The relations behave well under maps. Composition with an isometry keeps congruence (`Congruent.comp_left_iff`), and composition with a dilation keeps similarity (`Similar.comp_left_iff`). A reindexing along a map keeps both (`Congruent.index_map`, `Similar.index_map`), and a reindexing along an equivalence reflects them (`Congruent.index_equiv`). For triangles the module has a side ratio test: `similar_of_side_side` gives the similarity of $(a, b, c)$ and $(a', b', c')$ from the two proportions $d(a, b) \cdot d(b', c') = d(b, c) \cdot d(a', b')$ and $d(a, b) \cdot d(c', a') = d(c, a) \cdot d(a', b')$.

#### Common errors

1. The lemmas about the nonnegative distance have nnDist in the name, with a capital letter D, as in `Isometry.nnDist_eq` and `congruent_iff_nnDist_eq`. The forms with a small letter are old aliases, and a proof does not use them. In the same way, the Lipschitz facts are `Isometry.lipschitzWith` and `Dilation.lipschitzWith`.
2. `Isometry.injective` and `Dilation.injective` need an `EMetricSpace` on the source. In a pseudometric space two distinct points can have distance $0$, and an isometry can identify them.
3. `Dilation.ratio f` is a choice when all distances of the source are $0$ or $\infty$. A proof that needs the ratio of a composition uses `Dilation.ratio_comp`, which asks for a nontrivial metric space as source, or `Dilation.ratio_comp'`, which asks for two points at finite nonzero distance.

### Exercises

1. (A) Prove that the map $x \mapsto -x$ on $\mathbb{R}$ is an isometry with `Isometry.of_dist_eq`, and find its form as an `IsometryEquiv`.
2. (A) Show that the self isometries of $\mathbb{R}$ that fix $0$ are $x \mapsto x$ and $x \mapsto -x$.
3. (B) Let $f : \mathbb{R} \to \mathbb{R}$, $f(x) = 2x + 1$. Build $f$ as a dilation with `Dilation.mkOfDistEq` and prove that its ratio is $2$ with `Dilation.ratio_unique`.
4. (B) Prove that a dilation of a nonempty compact metric space into itself with ratio $r$ satisfies $r \le 1$. Hint: compare diameters.
5. (B) Show that two families with values in the same space are congruent if they differ by an isometry of the space, and use `Congruent.comp_left_iff`.
6. (C) Prove that an isometry of a compact metric space into itself is surjective.

### Reference

<?reference?>
