---
title: Stalks, sheafification and skyscraper sheaves
kind: theory
modules:
  - Mathlib.Topology.Sheaves.EtaleSpace
  - Mathlib.Topology.Sheaves.Flasque
  - Mathlib.Topology.Sheaves.LocallySurjective
  - Mathlib.Topology.Sheaves.Points
  - Mathlib.Topology.Sheaves.Sheafify
  - Mathlib.Topology.Sheaves.Skyscraper
  - Mathlib.Topology.Sheaves.Stalks
explains:
  E3: [TopCat.Presheaf.stalkFunctor, TopCat.Presheaf.stalk, TopCat.Presheaf.germ, TopCat.Presheaf.stalkPushforward, TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso, TopCat.Presheaf.sheafify, TopCat.Presheaf.EtaleSpace, skyscraperPresheaf, skyscraperSheaf, skyscraperPresheafStalkAdjunction, TopCat.Sheaf.IsFlasque, TopCat.Presheaf.IsLocallySurjective, TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks, Opens.pointGrothendieckTopology]
  E2: [TopCat.Presheaf.germ_ext, TopCat.Presheaf.germ_eq, TopCat.Presheaf.exists_germ_eq, TopCat.Presheaf.section_ext, TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective, TopCat.Presheaf.app_surjective_of_stalkFunctor_map_bijective, TopCat.Presheaf.app_isIso_of_stalkFunctor_map_iso, TopCat.Presheaf.isIso_of_stalkFunctor_map_iso, TopCat.Presheaf.mono_iff_stalk_mono, TopCat.Presheaf.stalkSpecializes, TopCat.Presheaf.stalkPullbackIso, TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing, TopCat.Presheaf.Sheafify.isGerm, TopCat.Presheaf.Sheafify.isLocallyGerm, TopCat.Presheaf.toSheafify, TopCat.Presheaf.sheafifyStalkIso, TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso, TopCat.Presheaf.EtaleSpace.isCoveringMap_base, TopCat.Presheaf.EtaleSpace.eventually_nhds, TopCat.Presheaf.EtaleSpace.homeomorph, skyscraperPresheaf_isSheaf, skyscraperPresheafStalkOfSpecializes, skyscraperPresheafStalkOfNotSpecializes, stalkSkyscraperSheafAdjunction, skyscraperSheafFunctor, TopCat.Presheaf.IsFlasque, TopCat.Sheaf.IsFlasque.epi_of_shortExact, TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂, isFlasque_skyscraperSheaf_of_hasZeroObject, TopCat.Presheaf.isLocallySurjective_iff, TopCat.Sheaf.isLocallySurjective_iff_epi, Opens.pointsGrothendieckTopology, Opens.isConservativeFamilyOfPoints_pointsGrothendieckTopology, Opens.pointGrothendieckTopologyHomEquiv]
  E1: auto
families: []
requires: [V13.C01, V13.C04, V24.C04, V24.C05, V25.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Stalks, sheafification and skyscraper sheaves

### Overview

A sheaf is local, so its value near one point should carry information of its own. The stalk at $x$ is that value: it is the colimit of the sections over all open neighbourhoods of $x$, and its elements are germs. For a sheaf of continuous functions the germ at $x$ is the class of a function up to equality near $x$. Stalks detect isomorphisms of sheaves, they turn a presheaf into a sheaf by sheafification, and for a scheme they are the local rings at the points.

This section defines stalks, germs and the maps of stalks for a continuous map and for a specialization. It proves that a morphism of sheaves is an isomorphism when it is one on all stalks, constructs the sheafification of a presheaf of sets by germs, and treats the étale space. It defines skyscraper sheaves, computes their stalks and proves their adjunction with the stalk functor. It ends with flasque sheaves, locally surjective morphisms and the points of the site of opens.

### Definitions

Fix a space $X$ and a category $C$ with colimits. For $x \in X$ the open neighbourhoods of $x$ form a category $N_x$, and $N_x^{\mathrm{op}}$ is filtered: two neighbourhoods contain their intersection.

**Definition (Stalk and germ).** The *stalk* of a presheaf $F$ at $x$ is $F_x = \operatorname{colim}_{U \in N_x^{\mathrm{op}}} F(U)$. The colimit map $F(U) \to F_x$ for $x \in U$ is the *germ* map, written $s \mapsto s_x$. A morphism $\phi : F \to G$ induces $\phi_x : F_x \to G_x$, and the stalk is a functor $\mathrm{PSh}(X, C) \to C$.

For sets, filteredness gives the familiar description: $F_x$ is the set of pairs $(U, s)$ with $x \in U$ and $s \in F(U)$, modulo $(U, s) \sim (V, t)$ when $s|_W = t|_W$ for some open $W \ni x$ in $U \cap V$.

**Definition (Stalk maps for a continuous map and a specialization).** Let $f : X \to Y$ be continuous. Since $x \in f^{-1}V$ whenever $f(x) \in V$, the maps $F(f^{-1}V) \to F_x$ define $(f_*F)_{f(x)} \to F_x$. If $x \rightsquigarrow y$, that is $y \in \overline{\{x\}}$, then every open neighbourhood of $y$ contains $x$, and the germ maps at $x$ define $F_y \to F_x$.

**Definition (Sheafification by germs).** Let $F$ be a presheaf of sets. For open $U$, let $F^{\#}(U)$ be the set of $f \in \prod_{x \in U} F_x$ such that each $x \in U$ has an open $V \ni x$, $V \subseteq U$, and $s \in F(V)$ with $f(y) = s_y$ for all $y \in V$. The map $F \to F^{\#}$ sends $s$ to $(x \mapsto s_x)$.

**Definition (Étale space).** The *étale space* of $F$ is the set of pairs $(x, g)$ with $g \in F_x$, with the topology generated by the sets $\{(y, s_y) : y \in U\}$ for $s \in F(U)$. The base map sends $(x, g)$ to $x$.

**Definition (Skyscraper presheaf).** Let $p_0 \in X$, $A \in C$, and let $C$ have a terminal object $\ast$. The *skyscraper presheaf* is $\mathrm{Sky}_{p_0}(A)(U) = A$ if $p_0 \in U$ and $\ast$ otherwise. A restriction is the identity of $A$ when both sets contain $p_0$, and the unique map to $\ast$ otherwise.

This is a functor of $A$, written $\mathrm{Sky}_{p_0} : C \to \mathrm{PSh}(X, C)$.

**Definition (Flasque sheaf).** A sheaf $F$ is *flasque* when every restriction $F(U) \to F(V)$ is an epimorphism.

**Definition (Locally surjective morphism).** A morphism $\phi : F \to G$ of presheaves of sets is *locally surjective* when for each $t \in G(U)$ and $x \in U$ there are an open $V \ni x$ in $U$ and $s \in F(V)$ with $\phi(s) = t|_V$.

**Definition (Point of the site of opens).** For $x \in X$, the functor $U \mapsto \{x\} \cap U$, with value a point or empty, is a *point* of the site of opens. The stalk of a sheaf at this point is $F_x$.

### Theorems and proofs

In the next results, $C$ is the category of sets, or a concrete category whose forgetful functor preserves filtered colimits and limits and reflects isomorphisms, such as rings or abelian groups. These hypotheses reduce each claim to sets.

**Lemma (Germs).** Every $g \in F_x$ is $s_x$ for some $s \in F(U)$, $x \in U$. If $s_x = t_x$ for $s \in F(U)$ and $t \in F(V)$, then $s|_W = t|_W$ for an open $W \ni x$ in $U \cap V$.

*Proof.* The forgetful functor preserves the filtered colimit, so it suffices to treat sets. A filtered colimit of sets is the disjoint union of the $F(U)$ modulo the relation that identifies $s$ and $t$ when they have equal images at some later stage. A later stage of $U$ and $V$ in $N_x^{\mathrm{op}}$ is an open $W \ni x$ contained in both. $\square$

**Proposition (Sections are determined by germs).** Let $F$ be a sheaf and $s, t \in F(U)$ with $s_x = t_x$ for all $x \in U$. Then $s = t$.

*Proof.* By the lemma, each $x \in U$ has an open $W_x \ni x$ with $s|_{W_x} = t|_{W_x}$. The $W_x$ cover $U$, and $s$ and $t$ are two gluings of one family, so $s = t$ by uniqueness. $\square$

**Theorem (Isomorphisms are detected on stalks).** Let $\phi : F \to G$ be a morphism of sheaves. If $\phi_x$ is injective for all $x \in U$, then $\phi_U$ is injective. If $\phi_x$ is bijective for all $x$, then $\phi$ is an isomorphism.

*Proof.* Injectivity. Let $\phi(s) = \phi(t)$ in $G(U)$. Then $\phi_x(s_x) = \phi(s)_x = \phi(t)_x = \phi_x(t_x)$, so $s_x = t_x$ for all $x \in U$, and $s = t$ by the proposition.

Surjectivity. Let $t \in G(U)$. For $x \in U$, surjectivity of $\phi_x$ and the lemma give an open $V_x \ni x$ and $s^x \in F(V_x)$ with $\phi(s^x)_x = t_x$. By the lemma again, after shrinking $V_x$, $\phi(s^x) = t|_{V_x}$. On $V_x \cap V_y$ the sections $s^x$ and $s^y$ have the same image $t|_{V_x \cap V_y}$, so they are equal by injectivity on $V_x \cap V_y$. They glue to $s \in F(U)$. Then $\phi(s)$ and $t$ agree on each $V_x$, so $\phi(s) = t$. So each $\phi_U$ is bijective. The forgetful functor reflects isomorphisms, so each $\phi_U$ is an isomorphism, and $\phi$ is an isomorphism of functors. $\square$

**Theorem (Locally surjective means surjective on stalks).** A morphism $\phi : F \to G$ of presheaves is locally surjective if and only if each $\phi_x$ is surjective.

*Proof.* Let $\phi$ be locally surjective and $g \in G_x$. By the lemma $g = t_x$ with $t \in G(U)$. Choose $V \ni x$ and $s \in F(V)$ with $\phi(s) = t|_V$. Then $\phi_x(s_x) = t_x = g$. Conversely, let each $\phi_x$ be surjective, $t \in G(U)$ and $x \in U$. Choose $s \in F(V)$ with $\phi_x(s_x) = t_x$, so $\phi(s)_x = t_x$. By the lemma $\phi(s)|_W = t|_W$ on an open $W \ni x$, and $s|_W$ is the required local preimage. $\square$

**Proposition (Stalk of a pushforward along an embedding).** If $f : X \to Y$ is inducing, then $(f_*F)_{f(x)} \to F_x$ is an isomorphism.

*Proof.* Since $f$ is inducing, each open $U \ni x$ is $f^{-1}V$ for an open $V \subseteq Y$, and then $f(x) \in V$. So the opens $f^{-1}V$ with $f(x) \in V$ are cofinal in $N_x^{\mathrm{op}}$. The stalk map is the comparison map of colimits along this cofinal functor, so it is an isomorphism. $\square$

**Theorem (Sheafification).** For a presheaf of sets $F$, $F^{\#}$ is a sheaf, and the map $F \to F^{\#}$ induces bijections $F_x \to F^{\#}_x$ for all $x$.

*Proof.* The condition that defines $F^{\#}$ is stable under restriction and is local, so it is a local predicate on functions $\prod_x F_x$, and $F^{\#}$ is a sheaf by the theorem on sheaves of functions of the previous section. Define $e : F^{\#}_x \to F_x$ by $e(f_x) = f(x)$; this respects germs, since equal germs agree at $x$. Then $e$ composed with the map $F_x \to F^{\#}_x$ sends $s_x$ to $s_x$, so it is the identity. It remains to show that $e$ is injective. Let $f \in F^{\#}(U)$ and $f' \in F^{\#}(U')$ with $f(x) = f'(x)$. Near $x$, $f = (y \mapsto s_y)$ for $s \in F(V)$ and $f' = (y \mapsto s'_y)$ for $s' \in F(V')$. Then $s_x = s'_x$, so $s|_W = s'|_W$ on an open $W \ni x$. So $f|_W = f'|_W$, and $f_x = f'_x$. $\square$

**Theorem (The skyscraper sheaf).** The skyscraper presheaf $\mathrm{Sky}_{p_0}(A)$ is a sheaf. Its stalk at $y$ is $A$ if $y \in \overline{\{p_0\}}$ and $\ast$ otherwise.

*Proof.* Let $i : \{\mathrm{pt}\} \to X$ send the point to $p_0$, and let $P$ be the sheaf on the point with $P(\mathrm{pt}) = A$ and $P(\emptyset) = \ast$. Then $i^{-1}U$ is the point if $p_0 \in U$ and empty otherwise, so $i_*P = \mathrm{Sky}_{p_0}(A)$, and the pushforward of a sheaf is a sheaf.

For the stalk, first let $y \in \overline{\{p_0\}}$. Every open $U \ni y$ meets $\{p_0\}$, so the diagram $U \mapsto A$ on $N_y^{\mathrm{op}}$ is constant with identity maps. This category is connected, so the colimit is $A$. Next let $y \notin \overline{\{p_0\}}$. Some open $U_0 \ni y$ misses $p_0$. The neighbourhoods inside $U_0$ are cofinal, and on them the diagram is constant with value $\ast$, so the stalk is $\ast$. $\square$

**Theorem (Stalk and skyscraper are adjoint).** For a presheaf $F$ and $A \in C$, $\mathrm{Hom}_C(F_{p_0}, A) \cong \mathrm{Hom}(F, \mathrm{Sky}_{p_0}(A))$, naturally in $F$ and $A$.

*Proof.* A morphism $F \to \mathrm{Sky}_{p_0}(A)$ has a unique component $F(U) \to \ast$ when $p_0 \notin U$. Its other components are maps $c_U : F(U) \to A$ for $p_0 \in U$, and naturality for $V \subseteq U$, both containing $p_0$, says $c_V \circ \rho_{UV} = c_U$. The naturality squares that involve $\ast$ commute automatically. So a morphism is a cocone with vertex $A$ on the diagram of $F$ over $N_{p_0}^{\mathrm{op}}$, and such cocones correspond to maps from the colimit $F_{p_0}$ to $A$. Both constructions are natural. $\square$

**Theorem (Flasque kernels give surjective sections).** Let $0 \to F \to G \xrightarrow{g} H \to 0$ be a short exact sequence of sheaves of abelian groups with $F$ flasque. Then $g_U : G(U) \to H(U)$ is surjective for each $U$.

*Proof.* Fix $s \in H(U)$. Consider pairs $(V, t)$ with $V \subseteq U$ open, $t \in G(V)$ and $g(t) = s|_V$, ordered by $(V, t) \le (V', t')$ when $V \subseteq V'$ and $t'|_V = t$. In a chain, the sections are compatible, so they glue on the union of the open sets, and the gluing maps to $s$ on each member, hence on the union. So every chain has an upper bound, and Zorn's lemma gives a maximal $(V, t)$. Suppose $x \in U \setminus V$. An epimorphism of sheaves is surjective on stalks, so the theorem on locally surjective morphisms gives an open $W \ni x$ in $U$ and $t' \in G(W)$ with $g(t') = s|_W$. On $V \cap W$, $g(t - t') = 0$, so $t - t'$ is the image of a section $r \in F(V \cap W)$, since $F(V \cap W)$ is the kernel of $g$ on sections. As $F$ is flasque, $r = \tilde r|_{V \cap W}$ for some $\tilde r \in F(W)$. Then $t'$ plus the image of $\tilde r$ agrees with $t$ on $V \cap W$ and maps to $s|_W$. So $t$ and this section glue to a pair over $V \cup W$, which contradicts maximality. So $V = U$. $\square$

### Examples

**Example (Germs of continuous functions).** Let $F$ be the sheaf of continuous real functions on $\mathbb{R}$. The functions $|x|$ and $x$ have the same germ at $1$, since they agree on $(0, 2)$, but different germs at $0$: they differ at $-\varepsilon$ for every $\varepsilon > 0$. The function $\sin(1/x)$ on $(0, \infty)$ has a germ at each positive point but none at $0$, since it is not a section over any neighbourhood of $0$.

**Example (Skyscrapers on Spec $\mathbb{Z}$).** In $\operatorname{Spec} \mathbb{Z}$ the closure of the generic point $(0)$ is the whole space, and the closure of $(p)$ is $\{(p)\}$. A skyscraper at $(p)$ has stalk $A$ at $(p)$ and stalk $\ast$ at $(q)$ for $q \neq p$ and at $(0)$. For the generic point the open $D(p) = \operatorname{Spec} \mathbb{Z} \setminus \{(p)\}$ contains $(0)$ and not $(p)$, which confirms the computation. A skyscraper at $(0)$ has $F(U) = A$ for each nonempty $U$, because every nonempty open set contains $(0)$, and its stalk at every point is $A$.

**Example (The generic point of the affine line).** In $\operatorname{Spec} k[x]$ every nonempty open set is the complement of finitely many closed points and contains the generic point $\eta = (0)$. The skyscraper at $\eta$ with value $k(x)$ is the constant sheaf $U \mapsto k(x)$ on nonempty $U$. It is flasque, since all restrictions between nonempty open sets are identities and $A \to \ast$ is surjective.

**Counterexample (Locally surjective but not surjective).** On $X = \mathbb{C} \setminus \{0\}$ let $\exp : \mathcal{O} \to \mathcal{O}^{\times}$ send a holomorphic $f$ to $e^f$. Each nowhere zero function has a logarithm on a disk, so $\exp$ is locally surjective and surjective on stalks. The global section $z$ is not $e^f$: then $f'(z) = 1/z$, and $\oint_{|z| = 1} dz/z = 2\pi i \neq 0$ contradicts the existence of a primitive. The kernel $2\pi i \underline{\mathbb{Z}}$ is not flasque, consistent with the theorem above.

**Counterexample (A sheaf that is not flasque).** Continuous functions on $\mathbb{R}$ are not flasque: $1/x$ on $(0, \infty)$ is not the restriction of a continuous function on $\mathbb{R}$.

### The library around it

::: mathlib
`TopCat.Presheaf.germ` · `Mathlib.Topology.Sheaves.Stalks`

`F.germ U x hx : F.obj (op U) ⟶ F.stalk x` is the colimit map, and `stalkFunctor C x` is the stalk as a functor. The element lemmas `exists_germ_eq` and `germ_eq` need a concrete category whose forgetful functor preserves filtered colimits.

<?decl TopCat.Presheaf.germ?>
:::

::: mathlib
`TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso` · `Mathlib.Topology.Sheaves.Stalks`

For sheaves in a concrete category whose forgetful functor reflects isomorphisms and preserves limits and filtered colimits, a morphism is an isomorphism if and only if all stalk maps are. The pieces are `app_injective_of_stalkFunctor_map_injective`, `app_surjective_of_stalkFunctor_map_bijective` and `section_ext`.

<?decl TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso?>
:::

::: mathlib
`TopCat.Presheaf.sheafify` · `Mathlib.Topology.Sheaves.Sheafify`

For a presheaf of types, `F.sheafify` is `subsheafToTypes` of the local predicate `Sheafify.isLocallyGerm`, and `sheafifyStalkIso` is the bijection of stalks. The universal property is in the site library: `CategoryTheory.sheafify` and `CategoryTheory.sheafificationAdjunction`.

<?decl TopCat.Presheaf.sheafify?>
:::

::: mathlib
`TopCat.Presheaf.EtaleSpace.isCoveringMap_base` · `Mathlib.Topology.Sheaves.EtaleSpace`

If each point has a neighbourhood `U` such that every germ map out of `F(U)` is bijective, then the base map of the étale space is an `IsCoveringMap`. The trivialization is `EtaleSpace.homeomorph`, with the stalk in the discrete topology as fiber.

<?decl TopCat.Presheaf.EtaleSpace.isCoveringMap_base?>
:::

::: mathlib
`skyscraperPresheafStalkAdjunction` · `Mathlib.Topology.Sheaves.Skyscraper`

This is `stalkFunctor C p₀ ⊣ skyscraperPresheafFunctor p₀` for `C` with colimits. The stalks are `skyscraperPresheafStalkOfSpecializes` and `skyscraperPresheafStalkOfNotSpecializes`, stated with `p₀ ⤳ y`. The sheaf version is `stalkSkyscraperSheafAdjunction`.

<?decl skyscraperPresheafStalkAdjunction?>
:::

::: mathlib
`TopCat.Sheaf.IsFlasque.epi_of_shortExact` · `Mathlib.Topology.Sheaves.Flasque`

For a short exact sequence of sheaves of abelian groups with flasque first term, the map on sections over each open is an epimorphism. The proof uses Zorn's lemma as above. `of_shortExact_of_isFlasque₁₂` deduces that the third term is flasque when the first two are.

<?decl TopCat.Sheaf.IsFlasque.epi_of_shortExact?>
:::

::: mathlib
`TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks` · `Mathlib.Topology.Sheaves.LocallySurjective`

`IsLocallySurjective` is the site notion `CategoryTheory.Presheaf.IsLocallySurjective` for the opens of `X`. For sheaves, `TopCat.Sheaf.isLocallySurjective_iff_epi` identifies it with being an epimorphism.

<?decl TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks?>
:::

::: mathlib
`Opens.pointGrothendieckTopology` · `Mathlib.Topology.Sheaves.Points`

The point of the site of opens attached to `x`, a `CategoryTheory.GrothendieckTopology.Point`. The family of all these points is conservative, so the site has enough points, and `pointGrothendieckTopologyHomEquiv` identifies morphisms of points with specializations.

<?decl Opens.pointGrothendieckTopology?>
:::

Common errors of a learner: `x ⤳ y` means $y \in \overline{\{x\}}$, and the map `stalkSpecializes` goes from the stalk at `y` to the stalk at `x`. The skyscraper stalk is `A` exactly at the points of the closure of `p₀`, not only at `p₀`. The criterion on stalks needs a sheaf as source; for presheaves it fails. The construction `F.sheafify` is for presheaves of types; other targets use the general sheafification of sites.

### Exercises

1. (A) Compute the stalk at $x$ of the sheaf of locally constant functions to a set $S$ on any space. *Hint:* A germ of a locally constant function is its value.
2. (A) Let $X$ be the Sierpinski space with open sets $\emptyset$, $\{1\}$, $\{0, 1\}$. Compute the stalks of a sheaf $F$ at $0$ and at $1$. *Hint:* The smallest neighbourhood of $0$ is $X$.
3. (B) Show that the sheafification of the constant presheaf $U \mapsto S$ is the sheaf of locally constant functions to $S$. *Hint:* Compare germs.
4. (B) Let $\phi : F \to G$ be a morphism of sheaves of sets that is injective on stalks. Show that $\phi$ is a monomorphism. *Hint:* Use the injectivity part of the stalk theorem on each open.
5. (B) Show that a skyscraper sheaf of abelian groups is flasque. *Hint:* Every restriction is an identity or a map to $0$.
6. (C) Show that the stalk functor at $x$ preserves finite limits of presheaves of sets. *Hint:* Filtered colimits of sets commute with finite limits.
7. (C) Let $\mathcal{O}$ be the sheaf of continuous real functions on $\mathbb{R}$. Show that $\mathcal{O}_0$ is a local ring with maximal ideal the germs vanishing at $0$ and residue field $\mathbb{R}$. *Hint:* A function with $f(0) \neq 0$ is nowhere zero near $0$.

### Notes and history

Stalks, germs and the étale space go back to the first theory of sheaves of Leray in 1946 and to the Cartan seminar, where a sheaf was defined as an étale space. Serre in FAC (1955) works with sheaves as étale spaces as well. Hartshorne (1977) uses flasque sheaves to compute sheaf cohomology.

The Mathlib Authors of `Topology.Sheaves.Stalks` are Kim Morrison and Justus Springer, and the Mathlib Author of `Topology.Sheaves.Sheafify` is Kim Morrison. The Mathlib Authors of `Topology.Sheaves.Skyscraper` are Jujian Zhang and Junyan Xu. The Mathlib Author of `Topology.Sheaves.EtaleSpace` is Yury Kudryashov, and that of `Topology.Sheaves.Flasque` is Brian Nugent. The Mathlib Authors of `Topology.Sheaves.LocallySurjective` are Sam van Gool and Jake Levinson. The Mathlib Author of `Topology.Sheaves.Points` is Joël Riou.

### Reference

<?reference?>
