---
title: Adjunctions and limits
kind: theory
modules:
  - Mathlib.CategoryTheory.Adjunction.Limits
  - Mathlib.CategoryTheory.Adjunction.Unique
  - Mathlib.CategoryTheory.Adjunction.FullyFaithful
  - Mathlib.CategoryTheory.Adjunction.Reflective
explains:
  E3: [CategoryTheory.Adjunction.rightAdjoint_preservesLimits, CategoryTheory.Adjunction.leftAdjointUniq, CategoryTheory.Adjunction.fullyFaithfulLOfIsIsoUnit, CategoryTheory.Reflective]
  E2: [CategoryTheory.Adjunction.leftAdjoint_preservesColimits, CategoryTheory.Adjunction.conesIso, CategoryTheory.Functor.instPreservesLimitsOfSizeOfIsRightAdjoint, CategoryTheory.Adjunction.rightAdjointUniq, CategoryTheory.Adjunction.comp, CategoryTheory.Adjunction.fullyFaithfulROfIsIsoCounit, CategoryTheory.Adjunction.unit_isIso_of_L_fully_faithful, CategoryTheory.Adjunction.counit_isIso_of_R_fully_faithful, CategoryTheory.Adjunction.mem_essImage_of_unit_isIso, CategoryTheory.reflector, CategoryTheory.reflectorAdjunction, CategoryTheory.Functor.essImage.unit_isIso]
  E1: auto
families: []
requires: [V24.C01, V24.C02, V24.C03, V24.C04, V05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Adjunctions and limits

### Overview

This section proves the main structural facts about adjunctions. A right adjoint preserves all limits, and a left adjoint preserves all colimits. An adjoint is unique up to a unique natural isomorphism, and adjunctions compose. A left adjoint is fully faithful exactly when its unit is an isomorphism, which leads to reflective subcategories such as abelian groups inside groups. The first theorem is also the main test for the existence of an adjoint: a functor that fails to preserve some limit has no left adjoint. Section 3 proves a converse, the adjoint functor theorem.

Throughout, $F : C \to D$ and $G : D \to C$ with an adjunction $F \dashv G$, bijections $\varphi$, unit $\eta$ and counit $\varepsilon$, as in Section 1. Write $g^\flat = \varphi^{-1}(g)$ for the transpose of $g : X \to G Y$. Naturality of $\varphi^{-1}$ in $Y$ reads $(G(k) \circ g)^\flat = k \circ g^\flat$.

### Definitions

**Definition (Reflective subcategory).** A full subcategory $D$ of $C$ is *reflective* if the inclusion $i : D \to C$ has a left adjoint $L$, the *reflector*. More generally, a fully faithful functor with a left adjoint is called reflective.

For $X$ in $C$, the unit $\eta_X : X \to i L X$ is then the best approximation of $X$ by an object of $D$: every map from $X$ to an object of $D$ factors uniquely through $\eta_X$.

::: mathlib
`CategoryTheory.Reflective` · `Mathlib.CategoryTheory.Adjunction.Reflective`

`Reflective R` is a class on a functor `R : D ⥤ C`. It extends `R.Full` and `R.Faithful` and holds a left adjoint `L` and an adjunction `adj : L ⊣ R`. Mathlib does not ask that `D` be a subcategory: any fully faithful right adjoint is allowed. The chosen left adjoint is `reflector R`, with `reflectorAdjunction R : reflector R ⊣ R`. The lemma `Functor.essImage.unit_isIso` says that the unit is an isomorphism at each object in the essential image of `R`.

<?decl CategoryTheory.Reflective?>
:::

### Theorems and proofs

**Theorem (Right adjoints preserve limits).** If $F \dashv G$, then $G$ preserves all limits that exist in $D$. Dually, $F$ preserves all colimits that exist in $C$.

*Proof.* Let $K : J \to D$ and let $(L, \pi)$ be a limit cone over $K$. Let $(X, \sigma)$ be a cone over $G \circ K$, so $\sigma_j : X \to G K(j)$ and $G K(u) \circ \sigma_j = \sigma_k$ for $u : j \to k$.

*Transpose the cone.* The maps $\sigma_j^\flat : F X \to K(j)$ form a cone over $K$: $K(u) \circ \sigma_j^\flat = (G K(u) \circ \sigma_j)^\flat = \sigma_k^\flat$. So there is a unique $v : F X \to L$ with $\pi_j \circ v = \sigma_j^\flat$ for all $j$.

*Existence.* Put $w = \varphi(v) : X \to G L$. By naturality of $\varphi$ in $Y$, $G(\pi_j) \circ w = \varphi(\pi_j \circ v) = \varphi(\sigma_j^\flat) = \sigma_j$.

*Uniqueness.* Let $w' : X \to G L$ with $G(\pi_j) \circ w' = \sigma_j$ for all $j$. Then $\pi_j \circ w'^\flat = (G(\pi_j) \circ w')^\flat = \sigma_j^\flat$. By the uniqueness of $v$, $w'^\flat = v$, so $w' = \varphi(v) = w$.

So $(G L, (G \pi_j)_j)$ is a limit cone over $G \circ K$. The statement on colimits is the same proof in the opposite categories, since $G^{\mathrm{op}} \dashv F^{\mathrm{op}}$. $\square$

The proof shows more: transposition is a bijection between cones over $G \circ K$ with apex $X$ and cones over $K$ with apex $F X$, natural in $X$.

**Theorem (Uniqueness of adjoints).** If $F \dashv G$ and $F' \dashv G$, then there is a natural isomorphism $\theta : F' \Rightarrow F$. Dually, two right adjoints of one functor are isomorphic.

*Proof.* Let $\varphi$ and $\varphi'$ be the two adjunctions, and put $\psi = \varphi'^{-1} \circ \varphi : \mathrm{Hom}(F X, Y) \to \mathrm{Hom}(F' X, Y)$. It is a bijection, natural in $X$ and $Y$. Put $\theta_X = \psi(1_{F X}) : F' X \to F X$. Naturality in $Y$ gives $\psi(f) = \psi(f \circ 1_{F X}) = f \circ \theta_X$ for each $f : F X \to Y$. In the same way, $\theta'_X = \psi^{-1}(1_{F' X})$ satisfies $\psi^{-1}(g) = g \circ \theta'_X$. Then $\theta'_X \circ \theta_X = \psi(\theta'_X) = \psi(\psi^{-1}(1_{F' X})) = 1_{F' X}$ and $\theta_X \circ \theta'_X = \psi^{-1}(\theta_X) = 1_{F X}$. So each $\theta_X$ is an isomorphism. For naturality, let $h : X' \to X$. Naturality of $\psi$ in $X$ gives $\psi(f \circ F(h)) = \psi(f) \circ F'(h)$. With $f = 1_{F X}$, the left side is $F(h) \circ \theta_{X'}$ and the right side is $\theta_X \circ F'(h)$. $\square$

This is the Yoneda argument of Chapter 3: $F X$ represents the functor $\mathrm{Hom}(X, G(-))$, and representing objects are unique.

**Proposition (Composition).** If $F \dashv G$ with $F : C \to D$ and $H \dashv I$ with $H : D \to E$, then $H \circ F \dashv G \circ I$.

*Proof.* The composite of the natural bijections $\mathrm{Hom}_E(H F X, Z) \cong \mathrm{Hom}_D(F X, I Z) \cong \mathrm{Hom}_C(X, G I Z)$ is a bijection, natural in $X$ and $Z$, since each factor is natural. $\square$

**Theorem (Fully faithful adjoints).** $F$ is fully faithful if and only if the unit $\eta$ is an isomorphism. Dually, $G$ is fully faithful if and only if $\varepsilon$ is an isomorphism.

*Proof.* Fix $X$ and $X'$. Consider the composite
$$\mathrm{Hom}_C(X, X') \xrightarrow{\;F\;} \mathrm{Hom}_D(F X, F X') \xrightarrow{\;\varphi\;} \mathrm{Hom}_C(X, G F X').$$
It sends $h$ to $\varphi(F(h)) = G F(h) \circ \eta_X = \eta_{X'} \circ h$, by the formula of Section 1 and naturality of $\eta$. Since $\varphi$ is a bijection, $F$ is bijective on $\mathrm{Hom}(X, X')$ if and only if $h \mapsto \eta_{X'} \circ h$ is bijective. Fix $X'$. The map $h \mapsto \eta_{X'} \circ h$ is bijective for all $X$ if and only if $\eta_{X'}$ is an isomorphism, by the Yoneda lemma: the natural transformation $\mathrm{Hom}(-, X') \Rightarrow \mathrm{Hom}(-, G F X')$ is an isomorphism exactly when the map that induces it is. So $F$ is fully faithful if and only if every $\eta_{X'}$ is an isomorphism. $\square$

**Corollary (Reflective subcategories).** Let $D \subseteq C$ be reflective with reflector $L$. Then the counit $L i \Rightarrow 1_D$ is an isomorphism, and an object $X$ of $C$ is isomorphic to an object of $D$ if and only if $\eta_X$ is an isomorphism. If a diagram in $D$ has a limit in $C$, this limit is isomorphic to an object of $D$.

*Proof.* The inclusion $i$ is fully faithful, so the dual part of the theorem gives the first claim. If $\eta_X$ is an isomorphism, $X \cong i L X$. Conversely, let $\alpha : X \to i Y$ be an isomorphism. By naturality of $\eta$, $\eta_{iY} \circ \alpha = i L(\alpha) \circ \eta_X$. Here $\eta_{iY}$ is an isomorphism, since the second triangle gives $i(\varepsilon_Y) \circ \eta_{iY} = 1$ and $\varepsilon_Y$ is an isomorphism. So $\eta_X = (i L \alpha)^{-1} \circ \eta_{iY} \circ \alpha$ is an isomorphism. For the last claim, let $K : J \to D$ and let $(M, \mu)$ be a limit of $i \circ K$ in $C$. Maps from $i L M$ to an object of $D$ are determined by their composite with $\eta_M$, since they correspond to maps out of $L M$. Each $\mu_j$ has its target in $D$, so $\mu_j = \nu_j \circ \eta_M$ for a unique $\nu_j : i L M \to i K(j)$. For $u : j \to k$, both $i K(u) \circ \nu_j$ and $\nu_k$ give $\mu_k$ after composition with $\eta_M$, so they are equal, and $\nu$ is a cone. Let $s : i L M \to M$ be the map with $\mu_j \circ s = \nu_j$. Then $\mu_j \circ s \circ \eta_M = \mu_j$ for all $j$, so $s \circ \eta_M = 1_M$. Next, $(\eta_M \circ s) \circ \eta_M = \eta_M = 1 \circ \eta_M$, so $\eta_M \circ s = 1$. Hence $\eta_M$ is an isomorphism. $\square$

::: mathlib
`CategoryTheory.Adjunction.rightAdjoint_preservesLimits` · `Mathlib.CategoryTheory.Adjunction.Limits`

`adj.rightAdjoint_preservesLimits : PreservesLimitsOfSize G` for `adj : F ⊣ G`, for shapes in fixed universes, and `adj.leftAdjoint_preservesColimits` is the dual. There is also an instance for any `G` with `[G.IsRightAdjoint]`. The transposition of cones in the proof is `Adjunction.conesIso`, an isomorphism of functors of cones.

<?decl CategoryTheory.Adjunction.rightAdjoint_preservesLimits?>
:::

::: mathlib
`CategoryTheory.Adjunction.leftAdjointUniq` · `Mathlib.CategoryTheory.Adjunction.Unique`

`leftAdjointUniq adj1 adj2 : F ≅ F'` for `adj1 : F ⊣ G` and `adj2 : F' ⊣ G`, and `rightAdjointUniq` is the dual. Composition is `Adjunction.comp adj₁ adj₂ : F ⋙ H ⊣ I ⋙ G`, in `Mathlib.CategoryTheory.Adjunction.Basic`; note the order `F ⋙ H`, which is the textbook $H \circ F$.

<?decl CategoryTheory.Adjunction.leftAdjointUniq?>
:::

::: mathlib
`CategoryTheory.Adjunction.fullyFaithfulLOfIsIsoUnit` · `Mathlib.CategoryTheory.Adjunction.FullyFaithful`

One direction of the theorem is `h.fullyFaithfulLOfIsIsoUnit : L.FullyFaithful` from `[IsIso h.unit]`, and the other is the instance `unit_isIso_of_L_fully_faithful`. The dual forms are `fullyFaithfulROfIsIsoCounit` and `counit_isIso_of_R_fully_faithful`. The lemma `mem_essImage_of_unit_isIso` is one half of the corollary.

<?decl CategoryTheory.Adjunction.fullyFaithfulLOfIsIsoUnit?>
:::

### Examples

**Example (Abelianization).** Let $\mathbf{Ab} \subseteq \mathbf{Grp}$ be the full subcategory of abelian groups. For a group $G$, let $G^{\mathrm{ab}} = G/[G, G]$, the quotient by the commutator subgroup (Volume 5, Chapter 5). Each homomorphism $f : G \to A$ to an abelian group kills all commutators, since $f(x y x^{-1} y^{-1}) = 1$ in $A$. So $f$ factors uniquely through the quotient map $G \to G^{\mathrm{ab}}$. Hence $\mathrm{Hom}_{\mathbf{Ab}}(G^{\mathrm{ab}}, A) \cong \mathrm{Hom}_{\mathbf{Grp}}(G, A)$, and $\mathbf{Ab}$ is reflective. The unit is the quotient map, and it is an isomorphism exactly when $[G, G]$ is trivial, that is, when $G$ is abelian, as the corollary says. For example, $S_3^{\mathrm{ab}} \cong \mathbb{Z}/2$, the sign. By the corollary, a product or equalizer of abelian groups computed in groups is abelian.

**Counterexample (The forgetful functor of groups has no right adjoint).** Suppose $U : \mathbf{Grp} \to \mathbf{Set}$ had a right adjoint. Then $U$ would preserve colimits, in particular initial objects. The trivial group is initial, but $U$ sends it to a one-point set, which is not initial in $\mathbf{Set}$.

**Counterexample (The free group functor has no left adjoint).** Suppose the free group functor $F : \mathbf{Set} \to \mathbf{Grp}$ had a left adjoint. Then $F$ would preserve limits, in particular terminal objects. But $F(\{*\}) \cong \mathbb{Z}$, which is not the trivial group. So $F$ is a left adjoint and not a right adjoint.

**Example (Products and the diagonal).** The diagonal $\Delta : C \to C \times C$ has a right adjoint exactly when $C$ has binary products, and the adjoint is $(Y, Z) \mapsto Y \times Z$. So the product functor preserves all limits: $\lim_j (Y_j \times Z_j) \cong \lim_j Y_j \times \lim_j Z_j$ whenever the limits exist.

::: mathlib
`GrpCat.abelianizeAdj` · `Mathlib.Algebra.Category.Grp.Adjunctions`

`GrpCat.abelianizeAdj : GrpCat.abelianize ⊣ forget₂ CommGrpCat GrpCat` is the adjunction of the first example. Mathlib uses the separate category `CommGrpCat` and the forgetful functor `forget₂`, which is fully faithful, instead of a subcategory. The group is `Group.Abelianization G`, with the map `Group.Abelianization.of` and the universal property `Group.Abelianization.lift`.

<?decl GrpCat.abelianizeAdj?>
<?decl Group.Abelianization.lift?>
:::

### The library around it

Many instances of preservation in the library come from adjunctions. The forgetful functor from groups to sets preserves limits because it is a right adjoint (Section 1) and also because it creates them (Chapter 4). The functor `lim : (J ⥤ C) ⥤ C` is a right adjoint of the constant functor, so it preserves limits.

Common errors of a learner:

- Expecting a left adjoint to preserve limits. The free group functor preserves coproducts, $F(S \sqcup T) \cong F(S) * F(T)$, but not products.
- Forgetting the universe condition. `rightAdjoint_preservesLimits` holds for shapes in the universes of the categories, not for arbitrary shapes.
- Proving uniqueness of adjoints by hand. Use `leftAdjointUniq` or `rightAdjointUniq`.

### Exercises

1. (A) Show that the free group functor sends the disjoint union $S \sqcup T$ to the free product $F(S) * F(T)$.
2. (A) Use the theorem on right adjoints to show that the forgetful functor from rings to sets has no right adjoint.
3. (A) In commutative rings, show that the polynomial ring functor $S \mapsto \mathbb{Z}[x_s : s \in S]$ sends $S \sqcup T$ to $\mathbb{Z}[x_s : s \in S] \otimes_{\mathbb{Z}} \mathbb{Z}[x_t : t \in T]$.
4. (B) Let $i : D \to C$ be reflective. Show that $D$ has every colimit of a diagram $K$ for which $i \circ K$ has a colimit in $C$, and that it is $L$ of that colimit.
5. (B) Show that the torsion free abelian groups form a reflective subcategory of abelian groups, with reflector $A \mapsto A / A_{\mathrm{tors}}$.
6. (B) Show that the inclusion of $\mathbf{Ab}$ into $\mathbf{Grp}$ has no right adjoint. Hint: does it preserve coproducts?
7. (C) Let $F \dashv G$. Show that $F$ is an equivalence if and only if both $\eta$ and $\varepsilon$ are isomorphisms, and that then $G$ is an inverse of $F$.

### Notes and history

Adjoint functors go back to Kan (1958). The preservation of limits by right adjoints is the most used property of adjoints, and Freyd's adjoint functor theorem in Section 3 gives a converse. Reflective subcategories appear throughout algebra and topology: abelianization, sheafification and the Stone-Čech compactification are reflectors.

### Reference

<?reference?>
