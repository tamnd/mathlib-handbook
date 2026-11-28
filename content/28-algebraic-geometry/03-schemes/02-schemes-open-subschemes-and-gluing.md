---
title: Schemes, open subschemes and gluing
kind: theory
modules:
  - Mathlib.AlgebraicGeometry.Cover.Directed
  - Mathlib.AlgebraicGeometry.Cover.MorphismProperty
  - Mathlib.AlgebraicGeometry.Cover.Open
  - Mathlib.AlgebraicGeometry.Cover.Over
  - Mathlib.AlgebraicGeometry.Cover.QuasiCompact
  - Mathlib.AlgebraicGeometry.Cover.Sigma
  - Mathlib.AlgebraicGeometry.Gluing
  - Mathlib.AlgebraicGeometry.GluingOneHypercover
  - Mathlib.AlgebraicGeometry.OpenImmersion
  - Mathlib.AlgebraicGeometry.PointsPi
  - Mathlib.AlgebraicGeometry.RelativeGluing
  - Mathlib.AlgebraicGeometry.ResidueField
  - Mathlib.AlgebraicGeometry.Restrict
  - Mathlib.AlgebraicGeometry.Scheme
  - Mathlib.AlgebraicGeometry.Stalk
explains:
  E3: [AlgebraicGeometry.Scheme, AlgebraicGeometry.IsOpenImmersion, AlgebraicGeometry.Scheme.Opens.toScheme, AlgebraicGeometry.Scheme.OpenCover, AlgebraicGeometry.Scheme.GlueData, AlgebraicGeometry.Scheme.residueField, AlgebraicGeometry.Scheme.SpecToEquivOfField]
  E2: [AlgebraicGeometry.Scheme.Hom, AlgebraicGeometry.Spec, AlgebraicGeometry.Spec.map, AlgebraicGeometry.Scheme.Spec, AlgebraicGeometry.Scheme.Γ, AlgebraicGeometry.Scheme.ΓSpecIso, AlgebraicGeometry.Scheme.Hom.stalkMap, AlgebraicGeometry.Scheme.Opens.ι, AlgebraicGeometry.Scheme.Opens.range_ι, AlgebraicGeometry.basicOpenIsoSpecAway, AlgebraicGeometry.IsOpenImmersion.isOpen_range, AlgebraicGeometry.Scheme.Hom.opensRange, AlgebraicGeometry.IsOpenImmersion.lift, AlgebraicGeometry.Scheme.Cover, AlgebraicGeometry.Scheme.affineCover, AlgebraicGeometry.Scheme.OpenCover.affineRefinement, AlgebraicGeometry.Scheme.OpenCover.finiteSubcover, AlgebraicGeometry.Scheme.directedAffineCover, AlgebraicGeometry.Scheme.Cover.sigma, AlgebraicGeometry.Scheme.Cover.Over, AlgebraicGeometry.QuasiCompactCover, AlgebraicGeometry.Scheme.GlueData.glued, AlgebraicGeometry.Scheme.GlueData.ι, AlgebraicGeometry.Scheme.GlueData.ι_eq_iff, AlgebraicGeometry.Scheme.GlueData.oneHypercover, AlgebraicGeometry.Scheme.Cover.RelativeGluingData, AlgebraicGeometry.Scheme.Cover.glueMorphisms, AlgebraicGeometry.Scheme.residue, AlgebraicGeometry.Scheme.fromSpecResidueField, AlgebraicGeometry.Scheme.Hom.residueFieldMap, AlgebraicGeometry.Scheme.fromSpecStalk, AlgebraicGeometry.Scheme.range_fromSpecStalk, AlgebraicGeometry.SpecToEquivOfLocalRing, AlgebraicGeometry.pointsPi]
  E1: auto
families: []
requires: [V09.C02, V10.C02, V13.C01, V13.C05, V24.C04, V28.C01, V28.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Schemes, open subschemes and gluing

### Overview

An affine scheme is the spectrum of one ring. Most spaces of geometry are not of this form. The projective line has no nonconstant global functions, so it is not the spectrum of its ring of functions. A scheme is a locally ringed space that is affine near each point. This is the same step as from open subsets of $\mathbb{R}^n$ to manifolds: the local model is fixed, and the global object is glued from copies of it.

This section defines schemes and their morphisms, open subschemes and open immersions, and open covers. It constructs schemes by gluing, with two examples: the affine line with a doubled origin and the projective line. It ends with residue fields and with the points of a scheme with values in a field, which describe the morphisms from $\operatorname{Spec} K$ to a scheme.

### Definitions

**Definition (Scheme).** A *scheme* is a locally ringed space $(X, \mathcal{O}_X)$ in which each point has an open neighbourhood $U$ such that $(U, \mathcal{O}_X|_U)$ is an affine scheme. A *morphism of schemes* is a morphism of locally ringed spaces. The schemes form a full subcategory of the category of locally ringed spaces.

A morphism $f : X \to Y$ is a continuous map with a map of sheaves $f^\# : \mathcal{O}_Y \to f_*\mathcal{O}_X$ whose stalk maps $\mathcal{O}_{Y, f(x)} \to \mathcal{O}_{X,x}$ are local. The ring of global sections is $\Gamma(X, \mathcal{O}_X) = \mathcal{O}_X(X)$, and $\Gamma$ is a functor from the opposite of schemes to rings. Each affine scheme is a scheme, with $U = X$.

**Definition (Open subscheme).** For an open $U \subseteq X$ the *open subscheme* on $U$ is the locally ringed space $(U, \mathcal{O}_X|_U)$, with $\mathcal{O}_X|_U(V) = \mathcal{O}_X(V)$ for open $V \subseteq U$.

**Definition (Open immersion).** A morphism $f : X \to Y$ is an *open immersion* when $f$ is a homeomorphism onto an open set $f(X)$ and $f^\#$ restricts to an isomorphism of sheaves $\mathcal{O}_Y|_{f(X)} \to f_*\mathcal{O}_X$. Equivalently, $f$ is an isomorphism onto the open subscheme $f(X)$ followed by the inclusion.

**Definition (Open cover).** An *open cover* of $X$ is a family of open immersions $f_i : U_i \to X$ whose images cover $X$. It is *affine* when each $U_i$ is affine. A second cover $(V_j \to X)_j$ *refines* it when each $V_j \to X$ factors through some $f_i$.

**Definition (Residue field).** The *residue field* of $X$ at $x$ is $\kappa(x) = \mathcal{O}_{X,x}/\mathfrak{m}_x$. The *value* of a section $s \in \mathcal{O}_X(U)$ at $x \in U$ is the class of its germ in $\kappa(x)$.

A morphism $f$ gives a map $\kappa(f(x)) \to \kappa(x)$, because the stalk map is local and so induces a map of the quotients by the maximal ideals.

### Theorems and proofs

**Lemma (Basic open sets are affine).** Let $R$ be a ring and $f \in R$. The morphism $\operatorname{Spec} R_f \to \operatorname{Spec} R$ of the ring map $R \to R_f$ is an open immersion with image $D(f)$. So $D(f) \cong \operatorname{Spec} R_f$.

*Proof.* The primes of $R_f$ correspond to the primes $\mathfrak{p}$ of $R$ with $f \notin \mathfrak{p}$, by $\mathfrak{q} \mapsto \mathfrak{q} \cap R$ and $\mathfrak{p} \mapsto \mathfrak{p}R_f$. So the map on points is a bijection onto $D(f)$. It is continuous. It is open: the image of the basic open set $D(a/f^n)$ is $D(af) \cap D(f) = D(af)$, because $a/f^n \notin \mathfrak{p}R_f$ if and only if $a \notin \mathfrak{p}$. So it is a homeomorphism onto $D(f)$. At a prime $\mathfrak{q} = \mathfrak{p}R_f$ the stalk map is $R_{\mathfrak{p}} \to (R_f)_{\mathfrak{q}}$, and it is an isomorphism, because inverting $f$ and then the elements outside $\mathfrak{p}$ gives the same ring as inverting the elements outside $\mathfrak{p}$ at once. A morphism of sheaves that is an isomorphism on all stalks is an isomorphism, by Chapter 1. $\square$

**Proposition (Open subschemes are schemes).** For each open $U \subseteq X$ the open subscheme $(U, \mathcal{O}_X|_U)$ is a scheme. The affine open sets of $X$ form a basis of its topology.

*Proof.* The stalks of $\mathcal{O}_X|_U$ are the stalks of $\mathcal{O}_X$, so $U$ is a locally ringed space. Let $x \in U$. Choose an open $V \ni x$ and an isomorphism $V \cong \operatorname{Spec} R$. The set $U \cap V$ is open in $\operatorname{Spec} R$ and contains $x$, so it contains a basic open set $D(f) \ni x$. By the lemma $D(f)$ is affine, and its structure sheaf is the restriction of $\mathcal{O}_X$. So $x$ has an affine neighbourhood inside $U$. This also shows that the affine open sets are a basis. $\square$

**Proposition (Universal property of an open immersion).** Let $f : X \to Y$ be an open immersion and $g : Z \to Y$ a morphism with $g(Z) \subseteq f(X)$. There is a unique morphism $h : Z \to X$ with $f \circ h = g$.

*Proof.* Write $f$ as an isomorphism $X \cong U$ followed by the inclusion of the open subscheme $U = f(X)$. It suffices to treat the inclusion $j : U \to Y$. On spaces, $h$ must be $g$ with the codomain $U$, and this map is continuous. On sheaves, for $V \subseteq U$ open, $\mathcal{O}_U(V) = \mathcal{O}_Y(V)$, so $h^\#$ must be $g^\#$ on the open sets inside $U$. This $h$ is a morphism of locally ringed spaces, because its stalk maps are those of $g$. It is unique, because both its map on points and its sheaf map are forced. $\square$

**Proposition (Gluing morphisms).** Let $(f_i : U_i \to X)_i$ be an open cover and $g_i : U_i \to Y$ morphisms such that $g_i$ and $g_j$ agree on $U_i \times_X U_j$, the preimage of $f_i(U_i) \cap f_j(U_j)$. There is a unique morphism $g : X \to Y$ with $g \circ f_i = g_i$ for all $i$.

*Proof.* Identify $U_i$ with the open set $f_i(U_i)$. The continuous maps $g_i$ agree on the overlaps, so they glue to a continuous map $g$. For an open $W \subseteq Y$ the maps $g_i^\# : \mathcal{O}_Y(W) \to \mathcal{O}_X(U_i \cap g^{-1}W)$ give sections that agree on $U_i \cap U_j \cap g^{-1}W$. By the sheaf condition they glue to a unique section of $\mathcal{O}_X(g^{-1}W)$. This defines $g^\#$. Its stalk maps are those of the $g_i$, so they are local. Uniqueness follows from the uniqueness of gluing of maps and of sections. $\square$

Each scheme has an affine open cover, by the definition. Each open cover has an affine refinement: cover each $U_i$ by affine open sets. When $X$ is quasi-compact, each open cover has a finite subcover.

**Definition (Gluing data).** *Gluing data* consist of schemes $U_i$ for $i \in I$, open subschemes $U_{ij} \subseteq U_i$ with $U_{ii} = U_i$, and isomorphisms $\varphi_{ij} : U_{ij} \to U_{ji}$ with $\varphi_{ii} = \mathrm{id}$. They must satisfy the *cocycle condition*: $\varphi_{ij}(U_{ij} \cap U_{ik}) = U_{ji} \cap U_{jk}$, and $\varphi_{jk} \circ \varphi_{ij} = \varphi_{ik}$ on $U_{ij} \cap U_{ik}$.

**Theorem (Gluing of schemes).** For gluing data there is a scheme $X$ with open immersions $\iota_i : U_i \to X$ such that the images cover $X$, $\iota_i(U_{ij}) = \iota_i(U_i) \cap \iota_j(U_j)$, and $\iota_j \circ \varphi_{ij} = \iota_i$ on $U_{ij}$. Two points $x \in U_i$ and $y \in U_j$ have the same image if and only if $x \in U_{ij}$ and $\varphi_{ij}(x) = y$.

*Proof.* On the disjoint union $\coprod_i U_i$, put $x \sim y$ for $x \in U_i$, $y \in U_j$ when $x \in U_{ij}$ and $\varphi_{ij}(x) = y$. The conditions $\varphi_{ii} = \mathrm{id}$, $\varphi_{ji} = \varphi_{ij}^{-1}$ (the cocycle condition with $k = i$) and the cocycle condition give reflexivity, symmetry and transitivity. Let $X$ be the quotient space and $\iota_i$ the induced maps. Each $\iota_i$ is injective, because $\varphi_{ii} = \mathrm{id}$. For $V \subseteq U_i$ open, the preimage of $\iota_i(V)$ in $U_j$ is $\varphi_{ij}(V \cap U_{ij})$, which is open. So $\iota_i(V)$ is open, and $\iota_i$ is a homeomorphism onto an open set. For $W \subseteq X$ open, let $\mathcal{O}_X(W)$ be the set of families $(s_i)$ with $s_i \in \mathcal{O}_{U_i}(\iota_i^{-1}W)$ and $\varphi_{ij}^\#(s_j) = s_i$ on $U_{ij} \cap \iota_i^{-1}W$. This is a sheaf of rings, because each $\mathcal{O}_{U_i}$ is one. On $W \subseteq \iota_i(U_i)$ the family is determined by $s_i$: the other members are $s_j = (\varphi_{ij}^{-1})^\#(s_i)$, and they are compatible by the cocycle condition. So $\mathcal{O}_X|_{\iota_i(U_i)} \cong \mathcal{O}_{U_i}$. Thus $X$ is locally isomorphic to the schemes $U_i$ and is a scheme, and each $\iota_i$ is an open immersion. The other claims are the definition of $\sim$. $\square$

**Theorem (Points with values in a field).** Let $X$ be a scheme and $K$ a field. Morphisms $\operatorname{Spec} K \to X$ correspond to pairs of a point $x \in X$ and a field map $\kappa(x) \to K$.

*Proof.* For $x \in X$ choose an affine open $U \ni x$ with $U \cong \operatorname{Spec} A$, so $x$ is a prime $\mathfrak{p}$ and $\kappa(x) = \kappa(\mathfrak{p})$. The ring map $A \to \kappa(\mathfrak{p})$ gives $\operatorname{Spec}\kappa(x) \to U \to X$. A second choice $U'$ gives the same morphism: both factor through an affine neighbourhood of $x$ inside $U \cap U'$, and the stalk maps agree. A pair $(x, \kappa(x) \to K)$ gives the composite $\operatorname{Spec} K \to \operatorname{Spec}\kappa(x) \to X$.

Conversely let $g : \operatorname{Spec} K \to X$, and let $x$ be the image of the one point. The stalk map $\mathcal{O}_{X,x} \to K$ is local, and the maximal ideal of $K$ is $0$, so its kernel is $\mathfrak{m}_x$ and it induces $\kappa(x) \to K$. The two constructions are inverse. Take $U$ as above. By the universal property of open immersions $g$ factors through $U$, and by the adjunction it is given by a ring map $\psi : A \to K$. Its kernel is the prime $\mathfrak{p}$, since $g$ sends the point to $x$. Elements outside $\mathfrak{p}$ map to nonzero elements of $K$, which are units. So $\psi$ factors through $A_{\mathfrak{p}}$, then through $\kappa(\mathfrak{p})$, and $g$ is the composite of the first construction. $\square$

### Examples

**Example (The affine line with a doubled origin).** Let $k$ be a field and $U_1 = U_2 = \mathbb{A}^1_k = \operatorname{Spec} k[x]$. Glue along $U_{12} = U_{21} = D(x)$ with $\varphi_{12} = \mathrm{id}$. The cocycle condition holds trivially. The scheme $X$ has two origins $0_1$ and $0_2$ and one copy of each other point. A global section is a pair $(f, g) \in k[x] \times k[x]$ with $f = g$ in $k[x, x^{-1}]$. Since $k[x] \to k[x, x^{-1}]$ is injective, $f = g$, and $\Gamma(X, \mathcal{O}_X) = k[x]$. The unit $X \to \operatorname{Spec} k[x]$ sends both origins to $(x)$: the germ of $x$ lies in the maximal ideal at each origin. So the unit is not injective, and $X$ is not affine. The two open immersions $\mathbb{A}^1_k \to X$ agree on $D(x)$ and differ at the origin; this makes $X$ the standard non-separated scheme of Chapter 5. The index of this edition has no declaration for the affine line with a doubled origin.

**Example (The projective line).** Let $U_1 = \operatorname{Spec} k[x]$ and $U_2 = \operatorname{Spec} k[y]$. Glue $U_{12} = D(x) = \operatorname{Spec} k[x, x^{-1}]$ to $U_{21} = D(y) = \operatorname{Spec} k[y, y^{-1}]$ by the isomorphism $\varphi_{12}$ of the ring map $k[y, y^{-1}] \to k[x, x^{-1}]$, $y \mapsto x^{-1}$. The result is the projective line $\mathbb{P}^1_k$. A global section is a pair $(f(x), g(y))$ with $f(x) = g(x^{-1})$ in $k[x, x^{-1}]$. The left side has only powers $x^n$ with $n \geq 0$, the right side only with $n \leq 0$. So both are constant, and $\Gamma(\mathbb{P}^1_k, \mathcal{O}) = k$. If $\mathbb{P}^1_k$ were affine, it would be $\operatorname{Spec} k$, one point. But it has the distinct points $(x)$ and $(x - 1)$ of $U_1$. So $\mathbb{P}^1_k$ is not affine. Chapter 4 constructs it again as $\operatorname{Proj} k[x, y]$.

**Counterexample (A homeomorphism that is not an open immersion).** Let $R = k[\varepsilon]/(\varepsilon^2)$. The morphism $\operatorname{Spec} k \to \operatorname{Spec} R$ of the quotient map $R \to k$ is a homeomorphism of one-point spaces, and its image is open. Its map on global sections is $R \to k$, which is not injective. So it is not an open immersion. The condition on sheaves in the definition is not automatic.

**Example (Points of Spec ℤ).** Ring maps $\mathbb{Z} \to K$ are unique. For $K = \mathbb{F}_p$ the morphism $\operatorname{Spec}\mathbb{F}_p \to \operatorname{Spec}\mathbb{Z}$ hits $(p)$, with $\kappa((p)) = \mathbb{F}_p \to \mathbb{F}_p$ the identity. For $K = \mathbb{C}$ it hits $(0)$, with $\mathbb{Q} \to \mathbb{C}$. The point $x$ of the theorem is the kernel of $\mathbb{Z} \to K$, which is $(\operatorname{char} K)$.

### The library around it

::: mathlib
`AlgebraicGeometry.Scheme` · `Mathlib.AlgebraicGeometry.Scheme`

The structure extends `LocallyRingedSpace` with the field `local_affine`: each point has an open neighbourhood `U` with `X.restrict U.isOpenEmbedding` (the open subspace) isomorphic to `Spec.toLocallyRingedSpace.obj (op R)`. A morphism is `Scheme.Hom`, a structure around a morphism of locally ringed spaces. `Spec R` takes `R : CommRingCat`, `Spec.map` is contravariant, `Scheme.Spec` and `Scheme.Γ` are the functors, and `Scheme.ΓSpecIso R : Γ(Spec R, ⊤) ≅ R`. The stalk map of a morphism is `Scheme.Hom.stalkMap`.

<?decl AlgebraicGeometry.Scheme?>
:::

::: mathlib
`AlgebraicGeometry.Scheme.Opens.toScheme` · `Mathlib.AlgebraicGeometry.Restrict`

For `U : X.Opens` there is a coercion to schemes, and `U.ι : ↑U ⟶ X` is the inclusion, with range `U` by `Scheme.Opens.range_ι`. The lemma of basic open sets is `basicOpenIsoSpecAway f : basicOpen f ≅ Spec (Localization.Away f)`.

<?decl AlgebraicGeometry.Scheme.Opens.toScheme?>
:::

::: mathlib
`AlgebraicGeometry.IsOpenImmersion` · `Mathlib.AlgebraicGeometry.OpenImmersion`

A `MorphismProperty Scheme`, defined through the open immersions of locally ringed spaces. The image is open by `IsOpenImmersion.isOpen_range`, and `Scheme.Hom.opensRange f` is the image as an open set. The universal property is `IsOpenImmersion.lift f g h` with `h : Set.range g ⊆ Set.range f`.

<?decl AlgebraicGeometry.IsOpenImmersion?>
:::

::: mathlib
`AlgebraicGeometry.Scheme.OpenCover` · `Mathlib.AlgebraicGeometry.Cover.Open`

`X.OpenCover` is `Scheme.Cover (precoverage IsOpenImmersion) X`. A cover `𝒰` has the index type `𝒰.I₀`, the schemes `𝒰.X i` and the maps `𝒰.f i`. `Scheme.Cover` allows any morphism property. The standard cover is `X.affineCover`, and `OpenCover.affineRefinement` and `OpenCover.finiteSubcover` are the two remarks after the gluing of morphisms. The gluing of morphisms is `Scheme.Cover.glueMorphisms`. The related files give `Scheme.directedAffineCover`, the cover by one coproduct `Scheme.Cover.sigma`, the covers of schemes over a base `Scheme.Cover.Over` and the class `QuasiCompactCover`.

<?decl AlgebraicGeometry.Scheme.OpenCover?>
:::

::: mathlib
`AlgebraicGeometry.Scheme.GlueData` · `Mathlib.AlgebraicGeometry.Gluing`

The structure extends `CategoryTheory.GlueData Scheme` with the field `f_open` that the maps `V i j ⟶ U i` are open immersions. The glued scheme `D.glued` is a multicoequalizer, with the open immersions `D.ι i`, and `Scheme.GlueData.ι_eq_iff` is the last claim of the theorem. `Scheme.GlueData.oneHypercover` sees the cover as a 1-hypercover in the Zariski topology. `Scheme.Cover.RelativeGluingData` glues schemes over the pieces of a locally directed cover.

<?decl AlgebraicGeometry.Scheme.GlueData?>
:::

::: mathlib
`AlgebraicGeometry.Scheme.residueField` · `Mathlib.AlgebraicGeometry.ResidueField`

`X.residueField x : CommRingCat`, with `X.residue x` from the stalk. The morphism `X.fromSpecResidueField x : Spec (X.residueField x) ⟶ X` is the first construction of the theorem, and `Scheme.Hom.residueFieldMap` is the map of residue fields. For the stalk, `X.fromSpecStalk x` has the range of the generizations of `x`, by `Scheme.range_fromSpecStalk`.

<?decl AlgebraicGeometry.Scheme.residueField?>
:::

::: mathlib
`AlgebraicGeometry.Scheme.SpecToEquivOfField` · `Mathlib.AlgebraicGeometry.ResidueField`

The equivalence `(Spec (.of K) ⟶ X) ≃ Σ x, X.residueField x ⟶ .of K` of the theorem. `SpecToEquivOfLocalRing` is the version for a local ring `R`, with local maps from the stalk. `pointsPi R X` sends a morphism from `Spec` of a product to its components; `pointsPi_injective` needs a quasi-separated `X` and `pointsPi_surjective` a quasi-compact `X` and local rings.

<?decl AlgebraicGeometry.Scheme.SpecToEquivOfField?>
:::

Common errors of a learner: an open set `U : X.Opens` is not a scheme until the coercion applies, and its points are a subtype, so `U.ι x` is the point of `X`. `Γ(X, U)` and `Γ(U, ⊤)` are isomorphic, not equal. In a cover the index type is `𝒰.I₀`, not a set of opens. The glued scheme of `D` is `D.glued`, and its points come from the quotient, so a statement on points goes through `ι_eq_iff` or `ι_jointly_surjective`.

### Exercises

1. (A) Show that the composite of two open immersions is an open immersion. *Hint:* Use the form "isomorphism onto an open subscheme followed by the inclusion".
2. (A) Show that the empty space with the zero sheaf is a scheme, and that it is $\operatorname{Spec}$ of the zero ring. *Hint:* The zero ring has no prime ideal.
3. (B) Show that the disjoint union of two schemes is a scheme, and that $X \sqcup Y \cong \operatorname{Spec}(A \times B)$ when $X = \operatorname{Spec} A$ and $Y = \operatorname{Spec} B$. *Hint:* Use the adjunction and the idempotents of $A \times B$.
4. (B) In the affine line with a doubled origin, show that the intersection of the two open sets $\iota_1(U_1)$ and $\iota_2(U_2)$ is affine, and compute its ring of sections. *Hint:* It is $\iota_1(D(x))$.
5. (B) Let $\mathbb{P}^1_k$ be glued as above. Show that the sections on $\iota_1(D(x - 1))$ form the ring $k[x, (x - 1)^{-1}]$, and describe the sections on the complement of the two points $(x)$ of $U_1$ and $(y)$ of $U_2$. *Hint:* The complement is $\iota_1(D(x))$.
6. (C) Glue $\mathbb{A}^2_k$ with itself along $\mathbb{A}^2_k \setminus \{(0, 0)\}$ by the identity. Show that the global sections are $k[x, y]$ and that the intersection of the two affine open sets is not affine. *Hint:* Use the last exercise of the previous section.
7. (C) Let $X$ be a scheme and $x \in X$. Show that the image of $\operatorname{Spec}\mathcal{O}_{X,x} \to X$ is the set of points $y$ with $x \in \overline{\{y\}}$. *Hint:* Reduce to $X = \operatorname{Spec} A$, $x = \mathfrak{p}$, and use the primes of $A_{\mathfrak{p}}$.

### Notes and history

Schemes are the work of Grothendieck in EGA, from 1960 to 1967. Serre, in *Faisceaux algébriques cohérents*, 1955, had already defined varieties as spaces with a sheaf of rings that are glued from affine pieces. The two examples of gluing are in Hartshorne, *Algebraic Geometry*, 1977, Chapter II. Buzzard, Commelin and Massot gave a definition of schemes in Lean in 2020.

The Mathlib Author of `AlgebraicGeometry.Scheme` is Kim Morrison. The Mathlib Author of `AlgebraicGeometry.Cover.Open`, `AlgebraicGeometry.Gluing`, `AlgebraicGeometry.OpenImmersion`, `AlgebraicGeometry.PointsPi`, `AlgebraicGeometry.ResidueField` and `AlgebraicGeometry.Restrict` is Andrew Yang. The Mathlib Authors of `AlgebraicGeometry.Cover.MorphismProperty` are Christian Merten and Andrew Yang. The Mathlib Author of `AlgebraicGeometry.Cover.Directed`, `AlgebraicGeometry.Cover.Over`, `AlgebraicGeometry.Cover.QuasiCompact`, `AlgebraicGeometry.Cover.Sigma` and `AlgebraicGeometry.RelativeGluing` is Christian Merten. The Mathlib Authors of `AlgebraicGeometry.GluingOneHypercover` are Calle Sönne, Joël Riou and Ravi Vakil. The Mathlib Authors of `AlgebraicGeometry.Stalk` are Andrew Yang and Fangming Li.

### Reference

<?reference?>
