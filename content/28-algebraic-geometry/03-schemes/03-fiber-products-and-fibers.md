---
title: Fiber products and fibers
kind: theory
modules:
  - Mathlib.AlgebraicGeometry.AffineTransitionLimit
  - Mathlib.AlgebraicGeometry.ColimitsOver
  - Mathlib.AlgebraicGeometry.EffectiveEpi
  - Mathlib.AlgebraicGeometry.Fiber
  - Mathlib.AlgebraicGeometry.Limits
  - Mathlib.AlgebraicGeometry.Over
  - Mathlib.AlgebraicGeometry.PullbackCarrier
  - Mathlib.AlgebraicGeometry.Pullbacks
  - Mathlib.AlgebraicGeometry.SpreadingOut
explains:
  E3: [AlgebraicGeometry.pullbackSpecIso, AlgebraicGeometry.Scheme.Pullback.hasPullback_of_cover, AlgebraicGeometry.Scheme.Pullback.carrierEquiv, AlgebraicGeometry.Scheme.Hom.fiber, AlgebraicGeometry.Scheme.Hom.fiberHomeo, AlgebraicGeometry.specZIsTerminal, AlgebraicGeometry.Scheme.Over, AlgebraicGeometry.Scheme.nonempty_of_isLimit, AlgebraicGeometry.spread_out_of_isGermInjective]
  E2: [AlgebraicGeometry.Scheme.Pullback.gluing, AlgebraicGeometry.Scheme.Pullback.gluedLift, AlgebraicGeometry.Scheme.Pullback.gluedIsLimit, AlgebraicGeometry.Scheme.Pullback.affine_affine_hasPullback, AlgebraicGeometry.Scheme.Pullback.openCoverOfLeft, AlgebraicGeometry.Scheme.Pullback.openCoverOfBase, AlgebraicGeometry.Scheme.Pullback.Triplet, AlgebraicGeometry.Scheme.Pullback.Triplet.tensor, AlgebraicGeometry.Scheme.Pullback.range_fst, AlgebraicGeometry.Scheme.isEmpty_pullback_iff, AlgebraicGeometry.Scheme.Hom.fiberι, AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField, AlgebraicGeometry.Scheme.Hom.range_fiberι, AlgebraicGeometry.Spec.fiberToSpecResidueFieldIso, AlgebraicGeometry.emptyIsInitial, AlgebraicGeometry.isInitial_iff_isEmpty, AlgebraicGeometry.coprodSpec, AlgebraicGeometry.sigmaOpenCover, AlgebraicGeometry.Scheme.Hom.IsOver, AlgebraicGeometry.Scheme.CanonicallyOver, AlgebraicGeometry.Scheme.compactSpace_of_isLimit, AlgebraicGeometry.exists_appTop_π_eq_of_isLimit, AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation, AlgebraicGeometry.Scheme.IsGermInjectiveAt, AlgebraicGeometry.Scheme.IsGermInjective, AlgebraicGeometry.spread_out_unique_of_isGermInjective, AlgebraicGeometry.isRegularEpi_of_flat_of_surjective_of_isAffine, AlgebraicGeometry.Scheme.Cover.hasColimit_of_locallyDirected]
  E1: auto
families: []
requires: [V08.C02, V09.C02, V13.C01, V24.C03, V24.C04, V24.C05, V28.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Fiber products and fibers

### Overview

The fiber product $X \times_S Y$ is the most used construction on schemes after gluing. It gives the product of two varieties, the base change of a scheme to a larger field, the fiber of a morphism over a point and the intersection of two subschemes. For affine schemes it is the spectrum of a tensor product. In general it is glued from affine pieces.

The underlying set of $X \times_S Y$ is not the fiber product of the sets. Its points over a pair $(x, y)$ are the points of the spectrum of $\kappa(x) \otimes_{\kappa(s)} \kappa(y)$. This section proves the existence of fiber products, describes their points, and studies the fiber $X_y$ of a morphism over a point $y$. It ends with the terminal and initial schemes, limits with affine transition maps and spreading out.

### Definitions

**Definition (Fiber product).** Let $f : X \to S$ and $g : Y \to S$ be morphisms of schemes. A *fiber product* is a scheme $P$ with morphisms $p : P \to X$ and $q : P \to Y$ such that $f \circ p = g \circ q$, and such that for each scheme $T$ with $a : T \to X$, $b : T \to Y$ and $f \circ a = g \circ b$ there is a unique $h : T \to P$ with $p \circ h = a$ and $q \circ h = b$. It is written $X \times_S Y$.

A fiber product is unique up to a unique isomorphism, as each limit is.

**Definition (Scheme over a base).** For a scheme $S$, an *$S$-scheme* is a scheme $X$ with a morphism $X \to S$, the *structure morphism*. A morphism of $S$-schemes is a morphism that commutes with the structure morphisms. For a ring $R$, an $R$-scheme is a $\operatorname{Spec} R$-scheme.

The fiber product $X \times_S Y$ is the product in the category of $S$-schemes, and $S$ is the terminal object of that category.

**Definition (Fiber).** Let $f : X \to Y$ be a morphism and $y \in Y$. The *fiber* of $f$ over $y$ is the $\kappa(y)$-scheme $X_y = X \times_Y \operatorname{Spec}\kappa(y)$, formed with the morphism $\operatorname{Spec}\kappa(y) \to Y$ of the previous section.

### Theorems and proofs

**Lemma (The affine case).** Let $R \to A$ and $R \to B$ be ring maps. Then $\operatorname{Spec}(A \otimes_R B)$, with the morphisms of the ring maps $A \to A \otimes_R B$ and $B \to A \otimes_R B$, is a fiber product of $\operatorname{Spec} A$ and $\operatorname{Spec} B$ over $\operatorname{Spec} R$.

*Proof.* Let $T$ be a scheme. By the adjunction of the first section, morphisms $T \to \operatorname{Spec} C$ correspond to ring maps $C \to \Gamma(T, \mathcal{O}_T)$, naturally in $C$. A ring map $A \otimes_R B \to \Gamma(T, \mathcal{O}_T)$ is the same as a pair of ring maps $A \to \Gamma(T, \mathcal{O}_T)$ and $B \to \Gamma(T, \mathcal{O}_T)$ that agree on $R$, by the universal property of the tensor product of commutative $R$-algebras. Such a pair is a pair of morphisms $T \to \operatorname{Spec} A$ and $T \to \operatorname{Spec} B$ that agree after composition with the morphisms to $\operatorname{Spec} R$. These bijections are natural in $T$, so the claim follows by the Yoneda lemma. $\square$

**Lemma (Restriction to an open set).** Let $P = X \times_S Y$ with projections $p$ and $q$, and let $U \subseteq X$ be open. Then the open subscheme $p^{-1}(U)$, with the restrictions of $p$ and $q$, is a fiber product $U \times_S Y$.

*Proof.* Let $a : T \to U$ and $b : T \to Y$ agree over $S$. View $a$ as a morphism to $X$. It gives a unique $h : T \to P$ with $p \circ h = a$ and $q \circ h = b$. Then $h(T) \subseteq p^{-1}(U)$, so $h$ factors uniquely through the open immersion $p^{-1}(U) \to P$, by the universal property of the previous section. A second factorization would give a second $h$ into $P$, so it is unique. $\square$

**Lemma (Gluing fiber products).** Let $(X_i \to X)_i$ be an open cover. If each $X_i \times_S Y$ exists, then $X \times_S Y$ exists.

*Proof.* Identify $X_i$ with an open subset of $X$ and put $P_i = X_i \times_S Y$, with projection $p_i : P_i \to X_i$. Let $P_{ij} = p_i^{-1}(X_i \cap X_j)$. By the previous lemma $P_{ij}$ and $P_{ji}$ are both fiber products $(X_i \cap X_j) \times_S Y$, so there is a unique isomorphism $\varphi_{ij} : P_{ij} \to P_{ji}$ that commutes with the projections. The uniqueness gives $\varphi_{ii} = \mathrm{id}$ and the cocycle condition: on the triple overlap, $\varphi_{jk} \circ \varphi_{ij}$ and $\varphi_{ik}$ both commute with the projections to $(X_i \cap X_j \cap X_k) \times_S Y$. Glue the $P_i$ to a scheme $P$. The projections $p_i$ and $q_i : P_i \to Y$ agree on the overlaps, so they glue to $p : P \to X$ and $q : P \to Y$. For the universal property, let $a : T \to X$ and $b : T \to Y$ agree over $S$. Put $T_i = a^{-1}(X_i)$. The restrictions give unique $h_i : T_i \to P_i \subseteq P$. On $T_i \cap T_j$ both $h_i$ and $h_j$ land in $P_{ij} \cong P_{ji}$ and solve the same problem for $(X_i \cap X_j) \times_S Y$, so they agree. By the gluing of morphisms they give $h : T \to P$. It is unique, because its restriction to each $T_i$ is unique. $\square$

**Theorem (Existence of fiber products).** For all morphisms $f : X \to S$ and $g : Y \to S$ of schemes the fiber product $X \times_S Y$ exists.

*Proof.* First let $S$ and $Y$ be affine. Cover $X$ by affine open sets. The lemma on the affine case gives the fiber products of the pieces, and the gluing lemma gives $X \times_S Y$. The fiber product is symmetric in $X$ and $Y$, so the same argument with an affine cover of $Y$ treats an affine $S$ and arbitrary $X$ and $Y$. Now let $S$ be arbitrary, and cover $S$ by affine open sets $S_i$. Put $X_i = f^{-1}(S_i)$ and $Y_i = g^{-1}(S_i)$. Then $X_i \times_{S_i} Y_i$ exists. It is also $X_i \times_S Y$: if $a : T \to X_i$ and $b : T \to Y$ agree over $S$, then $g(b(T)) = f(a(T)) \subseteq S_i$, so $b$ lands in $Y_i$. A morphism to the open subscheme $S_i$ is determined by its composite to $S$, so the conditions over $S$ and over $S_i$ are the same. The sets $X_i$ cover $X$, and the gluing lemma gives $X \times_S Y$. $\square$

**Theorem (Points of a fiber product).** Let $P = X \times_S Y$. The points of $P$ correspond to the pairs of a triple $(x, y, s)$ with $f(x) = s = g(y)$ and a prime ideal of $\kappa(x) \otimes_{\kappa(s)} \kappa(y)$.

*Proof.* Let $z \in P$, and put $x = p(z)$, $y = q(z)$ and $s = f(x) = g(y)$. The maps of residue fields $\kappa(x) \to \kappa(z)$ and $\kappa(y) \to \kappa(z)$ agree on $\kappa(s)$, so they define $\tau_z : \kappa(x) \otimes_{\kappa(s)} \kappa(y) \to \kappa(z)$. Its kernel $\mathfrak{q}_z$ is prime, because $\kappa(z)$ is a field. This gives the map in one direction.

Conversely, let $\mathfrak{q}$ be a prime of $C = \kappa(x) \otimes_{\kappa(s)} \kappa(y)$ and $K = \kappa(\mathfrak{q})$. The maps $\kappa(x) \to K$ and $\kappa(y) \to K$ give, by the theorem on points with values in a field, morphisms $\operatorname{Spec} K \to X$ and $\operatorname{Spec} K \to Y$ that agree over $S$. So they give $\operatorname{Spec} K \to P$, and its image is a point $z$. The map $C \to K$ factors as $\tau_z$ followed by the field map $\kappa(z) \to K$, which is injective. So $\mathfrak{q}_z = \mathfrak{q}$.

It remains to show that $z$ is determined by its data. Start from $z$, put $\mathfrak{q} = \mathfrak{q}_z$, and let $z'$ be the point built from $\mathfrak{q}$. The map $\tau_z$ induces an injection $C/\mathfrak{q} \to \kappa(z)$, which extends to $\kappa(\mathfrak{q}) \to \kappa(z)$. So $\operatorname{Spec}\kappa(z) \to P$ and $\operatorname{Spec}\kappa(z) \to \operatorname{Spec}\kappa(\mathfrak{q}) \to P$ have the same composites to $X$ and to $Y$. By the universal property they are equal, and their images $z$ and $z'$ are equal. $\square$

**Corollary (Image of a projection).** The image of $p : X \times_S Y \to X$ is $f^{-1}(g(Y))$. The fiber product is empty if and only if $f(X) \cap g(Y) = \emptyset$.

*Proof.* For $x$ with $f(x) = g(y)$, the ring $\kappa(x) \otimes_{\kappa(s)} \kappa(y)$ is a tensor product of two nonzero vector spaces over a field, so it is nonzero and has a prime ideal. The theorem gives a point over $(x, y)$. $\square$

**Proposition (The fiber as a subspace).** The projection $X_y \to X$ is a homeomorphism onto $f^{-1}(y)$.

*Proof.* The unique point of $\operatorname{Spec}\kappa(y)$ maps to $y$, so the triples of the theorem are the $(x, y)$ with $f(x) = y$. For such $x$ the ring $\kappa(x) \otimes_{\kappa(y)} \kappa(y) = \kappa(x)$ has one prime. So the projection is a bijection onto $f^{-1}(y)$. For the topology, a map that is a homeomorphism onto its image over each set of an open cover of $X$ and of $Y$ is a homeomorphism onto its image, so it suffices to treat $Y = \operatorname{Spec} R$, $X = \operatorname{Spec} A$, $y = \mathfrak{p}$. Then $X_y = \operatorname{Spec}(A \otimes_R \kappa(\mathfrak{p}))$ and $A \otimes_R \kappa(\mathfrak{p}) = A_{\mathfrak{p}}/\mathfrak{p}A_{\mathfrak{p}}$, with $A_{\mathfrak{p}}$ the localization at the image of $R \setminus \mathfrak{p}$. The maps $\operatorname{Spec}(S^{-1}A) \to \operatorname{Spec} A$ and $\operatorname{Spec}(A/I) \to \operatorname{Spec} A$ are homeomorphisms onto their images, by Volume 9. The composite of two such maps is again one. $\square$

**Proposition (Terminal and initial objects).** The scheme $\operatorname{Spec}\mathbb{Z}$ is terminal, and the empty scheme is initial. A scheme is initial if and only if it is empty.

*Proof.* For a scheme $X$, morphisms $X \to \operatorname{Spec}\mathbb{Z}$ correspond to ring maps $\mathbb{Z} \to \Gamma(X, \mathcal{O}_X)$, and there is exactly one. The empty scheme has a unique morphism to each $X$: the empty map with the zero maps of sheaves. If $X$ is initial, the two morphisms $X \to X \sqcup X$ agree, so $X$ has no point. $\square$

So the product $X \times Y$ in the category of schemes is $X \times_{\operatorname{Spec}\mathbb{Z}} Y$.

**Remark (Limits with affine transition maps).** Let $(X_i)$ be a cofiltered diagram of schemes in which each transition map is affine. Mathlib follows EGA IV, Section 8, and the Stacks project. If each $X_i$ is nonempty and quasi-compact, then the limit is nonempty and quasi-compact. If in addition each $X_i$ is quasi-separated, each global section of the limit comes from some $X_i$, and a morphism from the limit to a scheme $X$ that is locally of finite presentation over a base $S$ factors through some $X_j$.

**Remark (Spreading out).** Let $X$ and $Y$ be $S$-schemes, $x \in X$ and $y \in Y$ over the same point of $S$, and $\varphi : \mathcal{O}_{Y,y} \to \mathcal{O}_{X,x}$ a local map over $\mathcal{O}_{S,s}$. When $Y$ is locally of finite type over $S$ and the germ map $\mathcal{O}_X(U) \to \mathcal{O}_{X,x}$ is injective for some affine $U \ni x$, the morphism $\operatorname{Spec}\varphi$ extends to an $S$-morphism from an open neighbourhood of $x$ to $Y$. The germ condition holds for integral schemes and for locally Noetherian schemes.

### Examples

**Example (The fibers of Spec ℤ[i] over 2, 3 and 5).** Let $f : \operatorname{Spec}\mathbb{Z}[i] \to \operatorname{Spec}\mathbb{Z}$ come from the inclusion, with $\mathbb{Z}[i] = \mathbb{Z}[x]/(x^2 + 1)$. The fiber over $(p)$ is $\operatorname{Spec}(\mathbb{Z}[i] \otimes_{\mathbb{Z}} \mathbb{F}_p) = \operatorname{Spec}\mathbb{F}_p[x]/(x^2 + 1)$.

For $p = 2$: $x^2 + 1 = (x + 1)^2$ in $\mathbb{F}_2[x]$. The ring $\mathbb{F}_2[x]/(x + 1)^2$ has one prime, $(x + 1)$, and the nonzero nilpotent $x + 1$. The fiber is one point and is not reduced. The point is the prime $(1 + i)$, and $2 = -i(1 + i)^2$: the prime $2$ *ramifies*.

For $p = 3$: the squares in $\mathbb{F}_3$ are $0$ and $1$, so $-1$ is not a square and $x^2 + 1$ is irreducible. The fiber is $\operatorname{Spec}\mathbb{F}_9$, one point with residue field $\mathbb{F}_9$. The prime $3$ stays prime in $\mathbb{Z}[i]$: it is *inert*.

For $p = 5$: $x^2 + 1 = (x - 2)(x + 2)$ in $\mathbb{F}_5[x]$, since $4 + 1 = 5$. The factors are coprime, so by the Chinese remainder theorem the ring is $\mathbb{F}_5 \times \mathbb{F}_5$. The fiber has two points, $(2 - i)$ and $(2 + i)$, and $5 = (2 - i)(2 + i)$: the prime $5$ *splits*.

The fiber over the generic point $(0)$ is $\operatorname{Spec}(\mathbb{Z}[i] \otimes \mathbb{Q}) = \operatorname{Spec}\mathbb{Q}(i)$, one point.

**Counterexample (Points of a product are not pairs).** Take $X = Y = \operatorname{Spec}\mathbb{C}$ over $S = \operatorname{Spec}\mathbb{R}$. The product of the underlying sets has one element. But $\mathbb{C} \otimes_{\mathbb{R}} \mathbb{C} \cong \mathbb{C}[x]/(x^2 + 1) \cong \mathbb{C} \times \mathbb{C}$, by $x \mapsto (i, -i)$. So $X \times_S Y$ has two points. In the same way $\mathbb{A}^1_k \times_k \mathbb{A}^1_k = \operatorname{Spec} k[x, y] = \mathbb{A}^2_k$ has the generic points of curves, such as the prime $(x - y)$, which are not pairs of points.


### The library around it

::: mathlib
`AlgebraicGeometry.pullbackSpecIso` · `Mathlib.AlgebraicGeometry.Pullbacks`

`pullbackSpecIso R S T` is the isomorphism from the pullback of `Spec.map` of `algebraMap R S` and `algebraMap R T` to `Spec (S ⊗[R] T)`. The instance of existence for affine schemes is `Scheme.Pullback.affine_affine_hasPullback`.

<?decl AlgebraicGeometry.pullbackSpecIso?>
:::

::: mathlib
`AlgebraicGeometry.Scheme.Pullback.hasPullback_of_cover` · `Mathlib.AlgebraicGeometry.Pullbacks`

The gluing lemma: an open cover `𝒰` of `X` with `HasPullback (𝒰.f i ≫ f) g` for all `i` gives `HasPullback f g`. The glue data is `Scheme.Pullback.gluing`, the lift is `Scheme.Pullback.gluedLift` and the limit is `Scheme.Pullback.gluedIsLimit`. The covers of a pullback are `Scheme.Pullback.openCoverOfLeft` and `Scheme.Pullback.openCoverOfBase`.

<?decl AlgebraicGeometry.Scheme.Pullback.hasPullback_of_cover?>
:::

::: mathlib
`AlgebraicGeometry.Scheme.Pullback.carrierEquiv` · `Mathlib.AlgebraicGeometry.PullbackCarrier`

An equivalence from the points of `pullback f g` to `Σ T : Triplet f g, Spec T.tensor`. A `Scheme.Pullback.Triplet f g` holds `x`, `y`, `s` with the two equalities, and `Triplet.tensor` is $\kappa(x) \otimes_{\kappa(s)} \kappa(y)$. The corollary is `Scheme.Pullback.range_fst` and `Scheme.isEmpty_pullback_iff`.

<?decl AlgebraicGeometry.Scheme.Pullback.carrierEquiv?>
:::

::: mathlib
`AlgebraicGeometry.Scheme.Hom.fiber` · `Mathlib.AlgebraicGeometry.Fiber`

`f.fiber y` is `pullback f (Y.fromSpecResidueField y)`, with `f.fiberι` to `X` and `f.fiberToSpecResidueField y` to `Spec κ(y)`. The range of `f.fiberι y` is `f ⁻¹' {y}` by `Scheme.Hom.range_fiberι`. For `Spec S ⟶ Spec R`, `Spec.fiberToSpecResidueFieldIso` identifies the fiber with `Spec` of `κ(p) ⊗[R] S`.

<?decl AlgebraicGeometry.Scheme.Hom.fiber?>
:::

::: mathlib
`AlgebraicGeometry.Scheme.Hom.fiberHomeo` · `Mathlib.AlgebraicGeometry.Fiber`

The homeomorphism `f.fiber y ≃ₜ f ⁻¹' {y}` of the proposition.

<?decl AlgebraicGeometry.Scheme.Hom.fiberHomeo?>
:::

::: mathlib
`AlgebraicGeometry.specZIsTerminal` · `Mathlib.AlgebraicGeometry.Limits`

`IsTerminal (Spec (.of ℤ))`. The initial object is `emptyIsInitial`, and `isInitial_iff_isEmpty` is the last claim. The file also gives the coproducts, with `sigmaOpenCover` and `coprodSpec : Spec R ⨿ Spec S ⟶ Spec (R × S)`, which is an isomorphism.

<?decl AlgebraicGeometry.specZIsTerminal?>
:::

::: mathlib
`AlgebraicGeometry.Scheme.Over` · `Mathlib.AlgebraicGeometry.Over`

`X.Over S` is `OverClass X S`, a class that holds the structure morphism, written `X ↘ S`. A morphism over `S` satisfies `f.IsOver S`. `Scheme.CanonicallyOver` marks a structure morphism that comes from the data, for example `Spec A ↘ Spec R` for an `R`-algebra `A`. Colimits of schemes over `S` along a locally directed cover are `Scheme.Cover.hasColimit_of_locallyDirected`.

<?decl AlgebraicGeometry.Scheme.Over?>
:::

::: mathlib
`AlgebraicGeometry.Scheme.nonempty_of_isLimit` · `Mathlib.AlgebraicGeometry.AffineTransitionLimit`

For a cofiltered `D : I ⥤ Scheme` with `IsAffineHom (D.map f)`, nonempty and compact `D.obj i`, the cone point of a limit is nonempty. `Scheme.compactSpace_of_isLimit` gives quasi-compactness, `exists_appTop_π_eq_of_isLimit` the global sections and `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` the factorization of the remark.

<?decl AlgebraicGeometry.Scheme.nonempty_of_isLimit?>
:::

::: mathlib
`AlgebraicGeometry.spread_out_of_isGermInjective` · `Mathlib.AlgebraicGeometry.SpreadingOut`

The existence of the spread out morphism, under `LocallyOfFiniteType sY` and `X.IsGermInjectiveAt x`. The class `Scheme.IsGermInjective` asks it at all points, and it has instances for `IsIntegral` and for `IsLocallyNoetherian`. Uniqueness is `spread_out_unique_of_isGermInjective`. In a related file, `isRegularEpi_of_flat_of_surjective_of_isAffine` says that a flat surjective morphism of affine schemes is a regular epimorphism.

<?decl AlgebraicGeometry.spread_out_of_isGermInjective?>
:::

Common errors of a learner: `pullback f g` needs an instance `HasPullback f g`, which holds for all morphisms of schemes, but `pullbackSpecIso` is stated with `algebraMap`, so a general ring map must first become an algebra. The points of a pullback are not pairs, so a proof on points goes through `carrierEquiv` or `range_fst`. The fiber `f.fiber y` is a scheme over `Spec κ(y)`, not an open subscheme of `X`. `X ↘ S` is notation for the structure morphism of a class, so two different structure morphisms on one scheme give two different instances.

### Exercises

1. (A) Show that $\mathbb{A}^m_k \times_k \mathbb{A}^n_k \cong \mathbb{A}^{m+n}_k$. *Hint:* Use the lemma on the affine case and $k[x_1, \dots, x_m] \otimes_k k[y_1, \dots, y_n]$.
2. (A) Compute the fiber of $\operatorname{Spec}\mathbb{Z}[i] \to \operatorname{Spec}\mathbb{Z}$ over $(7)$ and over $(13)$. *Hint:* Find whether $-1$ is a square modulo $7$ and modulo $13$.
3. (B) Let $f : X \to S$ be a morphism and $U \subseteq S$ open. Show that $X \times_S U \cong f^{-1}(U)$. *Hint:* Apply the lemma on the restriction to an open set to $S \times_S X = X$.
4. (B) Compute $\operatorname{Spec}\mathbb{Q}(\sqrt{2}) \times_{\mathbb{Q}} \operatorname{Spec}\mathbb{Q}(\sqrt{2})$ and $\operatorname{Spec}\mathbb{Q}(\sqrt[3]{2}) \times_{\mathbb{Q}} \operatorname{Spec}\mathbb{Q}(\sqrt[3]{2})$. *Hint:* Factor $x^2 - 2$ over $\mathbb{Q}(\sqrt{2})$ and $x^3 - 2$ over $\mathbb{Q}(\sqrt[3]{2})$.
5. (B) Let $f : \operatorname{Spec} k[x, y]/(y^2 - x) \to \operatorname{Spec} k[x]$ with $\operatorname{char} k \neq 2$. Describe the fiber over $(x - a)$ for $a \in k$, and show that the fiber over $(x)$ is not reduced. *Hint:* The fiber is $\operatorname{Spec} k[y]/(y^2 - a)$.
6. (C) Let $X$ and $Y$ be $k$-schemes. Show that the $k$-points of $X \times_k Y$ are the pairs of $k$-points of $X$ and $Y$, and give a nonempty fiber product $X \times_k Y$ where $X$ has no $k$-point. *Hint:* Use the universal property with $T = \operatorname{Spec} k$, and the example $\operatorname{Spec}\mathbb{C}$ over $\mathbb{R}$.
7. (C) Show that the diagonal $X \to X \times_S X$ of a morphism $X \to S$ is a homeomorphism onto its image, and that this image is closed when $X$ and $S$ are affine. *Hint:* The projection is a left inverse. In the affine case the diagonal comes from the surjection $A \otimes_R A \to A$.

### Notes and history

The fiber product of schemes is in Grothendieck, EGA I, 1960. The proof by gluing affine pieces is also in Hartshorne, *Algebraic Geometry*, 1977, Theorem II.3.3. The splitting of primes in $\mathbb{Z}[i]$ is the classical theorem on sums of two squares in geometric form: an odd prime $p$ splits if and only if $p \equiv 1 \pmod 4$. The limits with affine transition maps follow EGA IV, Section 8, and the Stacks project.

The Mathlib Author of `AlgebraicGeometry.Fiber`, `AlgebraicGeometry.Limits`, `AlgebraicGeometry.Over`, `AlgebraicGeometry.Pullbacks` and `AlgebraicGeometry.SpreadingOut` is Andrew Yang. The Mathlib Authors of `AlgebraicGeometry.AffineTransitionLimit` are Andrew Yang and Christian Merten. The Mathlib Authors of `AlgebraicGeometry.PullbackCarrier` are Qi Ge, Christian Merten and Andrew Yang. The Mathlib Author of `AlgebraicGeometry.ColimitsOver` is Christian Merten. The Mathlib Author of `AlgebraicGeometry.EffectiveEpi` is Yong-Gyu Choi.

### Reference

<?reference?>
