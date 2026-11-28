---
title: Open immersions, gluing and colimits
kind: theory
modules:
  - Mathlib.Geometry.RingedSpace.LocallyRingedSpace.HasColimits
  - Mathlib.Geometry.RingedSpace.OpenImmersion
  - Mathlib.Geometry.RingedSpace.PresheafedSpace.Gluing
  - Mathlib.Geometry.RingedSpace.PresheafedSpace.HasColimits
explains:
  E3: [AlgebraicGeometry.PresheafedSpace.IsOpenImmersion, AlgebraicGeometry.SheafedSpace.IsOpenImmersion, AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion, AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoRestrict, AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftIsLimit, AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift, AlgebraicGeometry.SheafedSpace.IsOpenImmersion.of_stalk_iso, AlgebraicGeometry.PresheafedSpace.GlueData, AlgebraicGeometry.PresheafedSpace.GlueData.ιIsOpenImmersion, AlgebraicGeometry.LocallyRingedSpace.GlueData, AlgebraicGeometry.PresheafedSpace.colimit, AlgebraicGeometry.LocallyRingedSpace.coequalizer, AlgebraicGeometry.LocallyRingedSpace.coproduct]
  E2: [AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.base_open, AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.c_iso, AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoRestrict_hom_ofRestrict, AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.mono, AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.comp, AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofIso, AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofIsIso, AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofRestrict, AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.to_iso, AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.stalk_iso, AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackConeOfLeft, AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.hasPullback_of_left, AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackSndOfLeft, AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset, AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift_uniq, AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoOfRangeEq, AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toSheafedSpace, AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toLocallyRingedSpace, AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sigma_ι_isOpenImmersion, AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.of_stalk_iso, AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullbackConeOfLeftIsLimit, AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift, AlgebraicGeometry.PresheafedSpace.GlueData.ι_isOpenEmbedding, AlgebraicGeometry.PresheafedSpace.GlueData.ι_jointly_surjective, AlgebraicGeometry.PresheafedSpace.GlueData.vPullbackConeIsLimit, AlgebraicGeometry.SheafedSpace.GlueData, AlgebraicGeometry.SheafedSpace.GlueData.ιIsOpenImmersion, AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_isOpenImmersion, AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_jointly_surjective, AlgebraicGeometry.PresheafedSpace.pushforwardDiagramToColimit, AlgebraicGeometry.PresheafedSpace.colimitCocone, AlgebraicGeometry.PresheafedSpace.colimitCoconeIsColimit, AlgebraicGeometry.PresheafedSpace.instHasColimits, AlgebraicGeometry.PresheafedSpace.forget_preservesColimits, AlgebraicGeometry.LocallyRingedSpace.coproductCofanIsColimit, AlgebraicGeometry.LocallyRingedSpace.coequalizerCoforkIsColimit, AlgebraicGeometry.LocallyRingedSpace.HasCoequalizer.imageBasicOpen, AlgebraicGeometry.LocallyRingedSpace.HasCoequalizer.coequalizer_π_stalk_isLocalHom, AlgebraicGeometry.LocallyRingedSpace.instHasColimits, AlgebraicGeometry.LocallyRingedSpace.preservesColimits_forgetToSheafedSpace]
  E1: auto
families: []
requires: [V13.C01, V24.C04, V28.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Open immersions, gluing and colimits

### Overview

A scheme is built from affine pieces, so the theory needs two tools: a way to say that one space is an open piece of another, and a way to glue pieces along open overlaps. The first tool is the open immersion: an open embedding of spaces under which the structure sheaf of the source is the restriction of the sheaf of the target. The second is gluing data, a family of spaces with identified open subsets that satisfy a cocycle condition. The glued space is a colimit, so this section also constructs colimits of presheafed spaces and of locally ringed spaces.

This section proves that open immersions are restrictions to open subsets, that they compose, and that among open embeddings of sheafed spaces they are the maps with isomorphic stalks. It constructs pullbacks along open immersions, glued spaces, colimits of presheafed spaces, and coequalizers of locally ringed spaces.

### Definitions

**Definition (Open immersion).** A morphism $(f, f^\#) : X \to Y$ of presheafed spaces is an *open immersion* when $f$ is an open embedding and, for each open $U \subseteq X$, the component
$$f^\#_{f(U)} : \mathcal{O}_Y(f(U)) \to \mathcal{O}_X(f^{-1}f(U)) = \mathcal{O}_X(U)$$
is an isomorphism. A morphism of sheafed spaces or of locally ringed spaces is an open immersion when its underlying morphism of presheafed spaces is one.

**Definition (Gluing data).** Gluing data in a category consist of an index set $J$, objects $U_i$, morphisms $f_{ij} : V_{ij} \to U_i$, morphisms $t_{ij} : V_{ij} \to V_{ji}$ and $t'_{ijk} : V_{ij} \times_{U_i} V_{ik} \to V_{jk} \times_{U_j} V_{ji}$, such that:

- each $f_{ij}$ is a monomorphism and $f_{ii}$ is an isomorphism;
- $t_{ii} = \mathrm{id}$;
- $t'_{ijk}$ followed by the second projection equals the first projection followed by $t_{ij}$;
- the cocycle condition $t'_{ijk} \circ t'_{kij} \circ t'_{jki} = \mathrm{id}$ holds, as maps composed in the order $t'_{ijk}$, then $t'_{jki}$, then $t'_{kij}$.

For presheafed spaces, sheafed spaces and locally ringed spaces, the $f_{ij}$ are also open immersions.

Here $V_{ij}$ is the part of $U_i$ glued to $U_j$, and the cocycle condition makes the identifications $t_{ij}$ agree on triple overlaps.

**Definition (Glued space).** The *glued space* is the coequalizer of the two maps $\coprod_{i,j} V_{ij} \rightrightarrows \coprod_i U_i$ that are $f_{ij}$ and $f_{ji} \circ t_{ij}$ on $V_{ij}$. The maps $\iota_i : U_i \to X$ are the components of the coequalizer.

**Definition (Colimit of presheafed spaces).** Let $D : I \to \mathrm{PSh}$ be a diagram of presheafed spaces over a category $C$ with limits, with spaces $X_j$ and maps $\iota_j : X_j \to X$ to the colimit $X$ of the spaces. The *colimit* is the space $X$ with the presheaf
$$\mathcal{O}_X(W) = \lim_{j \in I^{\mathrm{op}}} \mathcal{O}_{X_j}(\iota_j^{-1} W),$$
the limit of the pushforwards $(\iota_j)_* \mathcal{O}_{X_j}$.

### Theorems and proofs

**Theorem (An open immersion is a restriction).** Let $f : X \to Y$ be an open immersion. Then $f$ factors as an isomorphism $X \cong Y|_{f(X)}$ followed by the inclusion $Y|_{f(X)} \to Y$.

*Proof.* As a map of spaces, $f$ is a homeomorphism from $X$ onto the open set $f(X)$, since it is an open embedding. The presheaf of $Y|_{f(X)}$, transported to $X$ along this homeomorphism, is $U \mapsto \mathcal{O}_Y(f(U))$. The components $f^\#_{f(U)} : \mathcal{O}_Y(f(U)) \to \mathcal{O}_X(U)$ are isomorphisms and natural in $U$, so they form an isomorphism of presheaves. A homeomorphism with an isomorphism of presheaves is an isomorphism of presheafed spaces. Composed with the inclusion, its sheaf components are $\mathcal{O}_Y(V) \to \mathcal{O}_Y(V \cap f(X)) \to \mathcal{O}_X(f^{-1}V)$, which is $f^\#_V$ by naturality. $\square$

**Proposition (Closure properties).** Isomorphisms are open immersions, a composite of open immersions is an open immersion, and an open immersion with surjective underlying map is an isomorphism. Open immersions are monomorphisms.

*Proof.* For an isomorphism, the map is a homeomorphism and all components are isomorphisms. For a composite $g \circ f$, the map $g \circ f$ is an open embedding, and its component at $g(f(U))$ is $f^\#_{f(U)} \circ g^\#_{g(f(U))}$, a composite of isomorphisms. If $f$ is surjective, then every open $V \subseteq Y$ is $f(f^{-1}V)$, so every component is an isomorphism, and $f$ is a homeomorphism. For the last claim, $f$ is an isomorphism onto $Y|_{f(X)}$, and the inclusion of a restriction is a monomorphism: two morphisms into $Y|_{f(X)}$ with equal composites to $Y$ have equal maps of spaces, and their sheaf components agree because each component into $\mathcal{O}_Y(V)$ with $V \subseteq f(X)$ is the same. $\square$

**Theorem (Stalks characterize open immersions).** The stalk maps of an open immersion are isomorphisms. Conversely, a morphism of sheafed spaces $f : X \to Y$ whose map is an open embedding and whose stalk maps are isomorphisms is an open immersion.

*Proof.* The first claim follows from the factorization and from the fact that the inclusion of a restriction is an isomorphism on stalks, proved in the previous section. For the converse, set $U' = f(X)$, open in $Y$. Consider the morphism of sheaves on $U'$ from $\mathcal{O}_Y|_{U'}$ to the transport of $\mathcal{O}_X$ along the homeomorphism $X \cong U'$, with components $f^\#_{f(U)}$. Its stalk at $f(x)$ is $f_x$, because the neighbourhoods $f(U)$ of $f(x)$ are cofinal. All these stalk maps are isomorphisms, and both sides are sheaves. By the stalk criterion of Chapter 1, the morphism is an isomorphism, so each $f^\#_{f(U)}$ is an isomorphism. $\square$

**Theorem (Factorization through an open immersion).** Let $f : X \to Z$ be an open immersion and $g : Y \to Z$ a morphism with $g(Y) \subseteq f(X)$. Then there is exactly one $h : Y \to X$ with $f \circ h = g$.

*Proof.* By the factorization, assume $X = Z|_{U}$ with $U = f(X)$ and $f$ the inclusion. On spaces, $h$ must be $g$ with codomain $U$. For an open $W \subseteq U$, the component of $h$ must be a map $\mathcal{O}_Z(W) \to \mathcal{O}_Y(g^{-1}W)$, and $f \circ h = g$ at the open $W$ of $Z$ forces it to be $g^\#_W$. These components are natural, so $h$ exists, and it is unique. If $f$ and $g$ are morphisms of locally ringed spaces, then $h_y = (f_{h(y)})^{-1} \circ g_y$ is a composite of local homomorphisms, so $h$ is one too. $\square$

**Theorem (Pullback along an open immersion).** Let $f : X \to Z$ be an open immersion and $g : Y \to Z$ any morphism. Then $Y|_{g^{-1}(f(X))}$, with its inclusion into $Y$ and the factorization of $g$ restricted, is a pullback of $f$ and $g$. Its map to $Y$ is an open immersion.

*Proof.* Let $W = g^{-1}(f(X))$, open in $Y$, and $j : Y|_W \to Y$ the inclusion. The composite $g \circ j$ has image in $f(X)$, so it factors as $f \circ p$ with a unique $p$. Let $a : T \to X$ and $b : T \to Y$ satisfy $f \circ a = g \circ b$. Then $b(T) \subseteq g^{-1}(f(X)) = W$, so $b$ factors uniquely as $j \circ b'$ through the open immersion $j$. Then $f \circ p \circ b' = g \circ b = f \circ a$, and $f$ is a monomorphism, so $p \circ b' = a$. Uniqueness of $b'$ follows from $j$ being a monomorphism. $\square$

**Theorem (Colimits of presheafed spaces).** If $C$ has limits, the space $X$ with the presheaf of the definition is a colimit of $D$. Its space is the colimit of the spaces of $D$.

*Proof.* The maps $\iota_j$ with the limit projections $\mathcal{O}_X \to (\iota_j)_*\mathcal{O}_{X_j}$ form a cocone. Let $(g_j, g_j^\#) : X_j \to Z$ be another cocone. The continuous maps $g_j$ give a unique continuous $g : X \to Z$ with $g \circ \iota_j = g_j$. For an open $W \subseteq Z$, the maps $g_j^\# : \mathcal{O}_Z(W) \to \mathcal{O}_{X_j}(g_j^{-1}W) = \mathcal{O}_{X_j}(\iota_j^{-1}g^{-1}W)$ are compatible with the transition maps of $D$, because the $g_j$ form a cocone. So they define a unique map $\mathcal{O}_Z(W) \to \lim_j \mathcal{O}_{X_j}(\iota_j^{-1}g^{-1}W) = \mathcal{O}_X(g^{-1}W)$, natural in $W$. This gives the unique morphism $X \to Z$ of the cocone. $\square$

The same construction gives colimits of sheafed spaces, since a limit of sheaves is a sheaf. For a coproduct, $X$ is the disjoint union and $\mathcal{O}_X(W) = \prod_j \mathcal{O}_{X_j}(W \cap X_j)$, so the stalk at a point of $X_j$ is the stalk of $X_j$. A coproduct of locally ringed spaces is therefore locally ringed.

**Theorem (Coequalizers of locally ringed spaces).** Let $f, g : X \rightrightarrows Y$ be morphisms of locally ringed spaces, and $\pi : Y \to Z$ their coequalizer as ringed spaces. Then $Z$ is locally ringed, $\pi$ is a morphism of locally ringed spaces, and $\pi$ is a coequalizer of locally ringed spaces.

*Proof.* By the colimit theorem, $Z$ is the quotient space of $Y$ by the equivalence relation generated by $f(x) \sim g(x)$, and $\mathcal{O}_Z(U) = \{s \in \mathcal{O}_Y(\pi^{-1}U) : f^\#(s) = g^\#(s)\}$. The map $\pi$ is surjective.

Step 1. Let $s \in \mathcal{O}_Z(U)$ and $V = Y_{\pi^\# s}$. Since $f$ is local, $f^{-1}(V) = X_{f^\#\pi^\# s}$ by an exercise of the previous section, and likewise for $g$. As $f^\#\pi^\# s = g^\#\pi^\# s$, the sets $f^{-1}(V)$ and $g^{-1}(V)$ are equal. So $V$ is saturated for the relation, $\pi^{-1}(\pi(V)) = V$, and $\pi(V)$ is open.

Step 2. On $V$ the section $\pi^\# s$ has an inverse $t$. Its images $f^\# t$ and $g^\# t$ are inverses of the equal sections $f^\#\pi^\# s = g^\#\pi^\# s$, so they are equal. So $t$ is a section of $\mathcal{O}_Z$ over $\pi(V)$, and $s$ is a unit on $\pi(V)$.

Step 3. Let $z = \pi(y)$. The ring $\mathcal{O}_{Z,z}$ maps to the nonzero ring $\mathcal{O}_{Y,y}$, so it is nonzero. For a germ $s_z$, one of $\pi^\# s$ and $1 - \pi^\# s$ is a unit at $y$, since $\mathcal{O}_{Y,y}$ is local. By Steps 1 and 2, $s_z$ or $1 - s_z$ is a unit. A nonzero ring in which $a$ or $1 - a$ is a unit for each $a$ is local.

Step 4. If $\pi_y(s_z)$ is a unit, then $y \in Y_{\pi^\# s}$, and $s_z$ is a unit by Step 2. So $\pi_y$ is local. A morphism $h : Y \to T$ of locally ringed spaces with $h \circ f = h \circ g$ factors as $h' \circ \pi$ in ringed spaces, and on stalks $h_y = \pi_y \circ h'_z$. If $h'_z(a)$ is a unit, then $h_y(a) = \pi_y(h'_z(a))$ is a unit, so $a$ is a unit because $h_y$ is local. So $h'_z$ is local, and $h'$ is a morphism of locally ringed spaces. $\square$

With coproducts and coequalizers, locally ringed spaces have all small colimits, and the forgetful functor to sheafed spaces preserves them.

**Theorem (The glued space).** For gluing data of presheafed spaces, each $\iota_i : U_i \to X$ is an open immersion, the maps $\iota_i$ are jointly surjective, and $V_{ij}$ is the pullback of $\iota_i$ and $\iota_j$.

*Proof.* The forgetful functor to spaces preserves colimits, so $X$ is the topological gluing: the disjoint union of the $U_i$ modulo $f_{ij}(v) \sim f_{ji}(t_{ij}(v))$. The cocycle condition makes this relation an equivalence relation, so a point $\iota_i(u)$ has preimage in $U_j$ equal to $f_{ji}(t_{ij}(f_{ij}^{-1}(u)))$. The $\iota_i$ are jointly surjective, and each $\iota_i$ is an open embedding, since the preimage in $U_j$ of $\iota_i(O)$ is $f_{ji}t_{ij}f_{ij}^{-1}(O)$, open as $f_{ji}$ is an open embedding. For the sheaf, the colimit formula says that a section over $\iota_i(O)$ is a compatible family of sections over the preimages of $\iota_i(O)$ in all $U_j$ and $V_{jk}$. Each of these preimages lies in the image of $V_{ij}$ or $V_{ik}$ under an isomorphism $t$ composed with an open immersion $f$, so the whole family is determined by its component on $O \subseteq U_i$, and every section on $O$ extends to a compatible family by transport along the $t$. So the component $\mathcal{O}_X(\iota_i(O)) \to \mathcal{O}_{U_i}(O)$ is an isomorphism. The pullback of the open immersion $\iota_i$ along $\iota_j$ is the restriction of $U_j$ to $\iota_j^{-1}(\iota_i(U_i)) = f_{ji}(V_{ji})$, which is isomorphic to $V_{ji}$, and to $V_{ij}$ through $t_{ij}$. $\square$

### Examples

**Example (Open subsets of a manifold).** For an open $U \subseteq \mathbb{R}^n$ with continuous functions, the inclusion $U \to \mathbb{R}^n$ is an open immersion: for open $V \subseteq U$ the component $\mathcal{O}_{\mathbb{R}^n}(V) \to \mathcal{O}_U(V)$ is the identity of $C(V, \mathbb{R})$.

**Counterexample (A homeomorphism that is not an open immersion).** Let $X$ be a point with the ring $k[\varepsilon]/(\varepsilon^2)$ and $Y$ a point with the ring $k$. The inclusion $k \to k[\varepsilon]/(\varepsilon^2)$ defines a morphism $X \to Y$ of locally ringed spaces, since $k$ has maximal ideal $0$. Its map is a homeomorphism, but the component at the point is not an isomorphism, so it is not an open immersion.

**Example (The line with two origins).** Take $U_1 = U_2 = \mathbb{R}$ with continuous functions, $V_{12} = V_{21} = \mathbb{R} \setminus \{0\}$ and $t_{12} = t_{21} = \mathrm{id}$. The glued space has two origins $0_1$ and $0_2$, and every neighbourhood of $0_1$ meets every neighbourhood of $0_2$, so it is not Hausdorff. A global section is a pair of continuous functions $s_1, s_2$ on $\mathbb{R}$ with $s_1 = s_2$ on $\mathbb{R} \setminus \{0\}$. By continuity $s_1(0) = \lim_{x \to 0} s_1(x) = s_2(0)$, so the global sections are $C(\mathbb{R}, \mathbb{R})$, and they do not separate the two origins.

**Example (The circle from two lines).** Take $U_1 = U_2 = \mathbb{R}$, $V_{12} = V_{21} = \mathbb{R} \setminus \{0\}$ and $t_{12} = t_{21} : x \mapsto 1/x$, with $s \mapsto s \circ t$ on functions. A point $x \neq 0$ of $U_1$ is glued to $1/x$ in $U_2$, so the glued space is the real projective line, a circle. A global section is a pair with $s_2(1/x) = s_1(x)$ for $x \neq 0$. For example $s_1(x) = x^2/(1 + x^2)$ and $s_2(y) = 1/(1 + y^2)$: then $s_2(1/x) = 1/(1 + 1/x^2) = x^2/(x^2 + 1) = s_1(x)$. With polynomial functions on the two lines and $k[x, x^{-1}]$ on the overlap, the same gluing gives the projective line of Chapter 3, whose global sections are only the constants: $p(x) = q(1/x)$ in $k[x, x^{-1}]$ forces $p$ and $q$ to be the same constant.

**Example (A coequalizer).** Let $Y = \mathbb{R}$ with continuous functions and $X$ a point with the ring $\mathbb{R}$. Let $f, g : X \to Y$ map the point to $0$ and $1$, with evaluation at $0$ and at $1$ on sections. The coequalizer $Z$ is $\mathbb{R}$ with $0$ and $1$ identified, and $\mathcal{O}_Z(U)$ is the ring of continuous $s$ on $\pi^{-1}U$ with $s(0) = s(1)$ when $\pi^{-1}U$ contains $0$ and $1$. At the identified point the stalk is local with residue field $\mathbb{R}$, and its maximal ideal is the set of germs with $s(0) = s(1) = 0$.

### The library around it

::: mathlib
`AlgebraicGeometry.PresheafedSpace.IsOpenImmersion` · `Mathlib.Geometry.RingedSpace.OpenImmersion`

A class with `base_open : IsOpenEmbedding f.base` and `c_iso`, the isomorphism of `f.c.app` at the images of open sets. `SheafedSpace.IsOpenImmersion f` and `LocallyRingedSpace.IsOpenImmersion f` apply it to the underlying presheafed morphism. The scheme version is `AlgebraicGeometry.IsOpenImmersion`.

<?decl AlgebraicGeometry.PresheafedSpace.IsOpenImmersion?>
:::

::: mathlib
`AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoRestrict` · `Mathlib.Geometry.RingedSpace.OpenImmersion`

`isoRestrict : X ≅ Y.restrict H.base_open`, with `isoRestrict_hom_ofRestrict` for the factorization. Closure properties are `comp`, `ofIso`, `ofRestrict`, `to_iso` (with `[Epi f.base]`) and `stalk_iso`.

<?decl AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoRestrict?>
:::

::: mathlib
`AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift` · `Mathlib.Geometry.RingedSpace.OpenImmersion`

`lift f g H` takes `H : Set.range g.base ⊆ Set.range f.base` and satisfies `lift_fac` and `lift_uniq`. It is built from the pullback `pullbackConeOfLeft`, whose limit property is `pullbackConeOfLeftIsLimit`.

<?decl AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift?>
:::

::: mathlib
`AlgebraicGeometry.SheafedSpace.IsOpenImmersion.of_stalk_iso` · `Mathlib.Geometry.RingedSpace.OpenImmersion`

An open embedding of sheafed spaces with isomorphisms on all stalks is an open immersion. The locally ringed version is `LocallyRingedSpace.IsOpenImmersion.of_stalk_iso`.

<?decl AlgebraicGeometry.SheafedSpace.IsOpenImmersion.of_stalk_iso?>
:::

::: mathlib
`AlgebraicGeometry.PresheafedSpace.GlueData` · `Mathlib.Geometry.RingedSpace.PresheafedSpace.Gluing`

It extends `CategoryTheory.GlueData` with `f_open`. The glued space is `CategoryTheory.GlueData.glued`, a multicoequalizer, with maps `CategoryTheory.GlueData.ι`. The results are `ιIsOpenImmersion`, `ι_jointly_surjective` and `vPullbackConeIsLimit`. The topological gluing is `TopCat.GlueData`, and the gluing of schemes is `AlgebraicGeometry.Scheme.GlueData`.

<?decl AlgebraicGeometry.PresheafedSpace.GlueData?>
:::

::: mathlib
`AlgebraicGeometry.PresheafedSpace.colimit` · `Mathlib.Geometry.RingedSpace.PresheafedSpace.HasColimits`

The carrier is the colimit of the spaces and the presheaf is `limit (pushforwardDiagramToColimit F).leftOp`. `colimitCoconeIsColimit` is the universal property, and `instHasColimits` needs `[HasLimits C]`.

<?decl AlgebraicGeometry.PresheafedSpace.colimit?>
:::

::: mathlib
`AlgebraicGeometry.LocallyRingedSpace.coequalizer` · `Mathlib.Geometry.RingedSpace.LocallyRingedSpace.HasColimits`

The coequalizer of sheafed spaces with the proof that its stalks are local. `HasCoequalizer.imageBasicOpen` is the open set $\pi(V)$ of Step 1, and `coequalizer_π_stalk_isLocalHom` is Step 4. With `coproduct`, this gives `instHasColimits` and `preservesColimits_forgetToSheafedSpace`.

<?decl AlgebraicGeometry.LocallyRingedSpace.coequalizer?>
:::

Common errors of a learner: `c_iso` asks for isomorphisms only at the images of open sets of the source, not at every open set of the target. The class `IsOpenImmersion` for sheafed spaces is about `f.hom`, so lemmas of the presheafed version need `f.hom`. The glued space is a colimit and is not Hausdorff in general, as the line with two origins shows.

### Exercises

1. (A) Show that for an open immersion $f : X \to Y$ and an open $V \subseteq Y$, the component $\mathcal{O}_Y(V) \to \mathcal{O}_X(f^{-1}V)$ is restriction to $V \cap f(X)$ followed by an isomorphism. *Hint:* Use naturality of $f^\#$ for $V \cap f(X) \subseteq V$.
2. (A) Show that the inclusions of the summands of a coproduct of sheafed spaces are open immersions. *Hint:* Each summand is open in the disjoint union.
3. (B) Show that two open immersions $f : X \to Z$ and $g : Y \to Z$ with the same image give an isomorphism $X \cong Y$ over $Z$. *Hint:* Factor each through the other.
4. (B) In the line with two origins, compute the sections over the open set $(\mathbb{R} \setminus \{0\}) \cup \{0_1\}$ and over the whole space. *Hint:* The first is a copy of $\mathbb{R}$.
5. (B) Show that the pullback of two open immersions $f : X \to Z$ and $g : Y \to Z$ is the restriction of $Z$ to $f(X) \cap g(Y)$. *Hint:* Apply the pullback theorem and compute $g^{-1}(f(X))$.
6. (C) Glue $J = \{1, 2, 3\}$ copies of $\mathbb{R}$ pairwise along $\mathbb{R} \setminus \{0\}$ by the identity. Check the cocycle condition and describe the glued space and its global sections. *Hint:* The triple overlaps are $\mathbb{R} \setminus \{0\}$.
7. (C) Let $f, g : X \to Y$ be equal morphisms of locally ringed spaces. Show that the coequalizer is $Y$ with the identity. *Hint:* Use the description of $\mathcal{O}_Z$ in the proof.

### Notes and history

Gluing along open subsets with a cocycle condition is how Weil, in Foundations of Algebraic Geometry (1946), built abstract varieties from affine pieces. Grothendieck glued schemes from affine schemes in EGA, from 1960 to 1967, and Hartshorne (1977) gives the gluing of schemes as an exercise. The proof that coequalizers of locally ringed spaces are local follows a paper of Demazure and Gabriel cited in the Mathlib source as MR0302656.

The Mathlib Author of `Geometry.RingedSpace.OpenImmersion`, `Geometry.RingedSpace.PresheafedSpace.Gluing` and `Geometry.RingedSpace.LocallyRingedSpace.HasColimits` is Andrew Yang. The Mathlib Author of `Geometry.RingedSpace.PresheafedSpace.HasColimits` is Kim Morrison.

### Reference

<?reference?>
