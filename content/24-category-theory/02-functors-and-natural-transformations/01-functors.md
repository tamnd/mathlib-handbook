---
title: Functors
kind: theory
modules:
  - Mathlib.CategoryTheory.Functor.Basic
  - Mathlib.CategoryTheory.Functor.FullyFaithful
  - Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
  - Mathlib.CategoryTheory.ConcreteCategory.Basic
  - Mathlib.CategoryTheory.ConcreteCategory.Forget
  - Mathlib.CategoryTheory.Category.Cat
explains:
  E3: [CategoryTheory.Functor, CategoryTheory.Functor.Faithful, CategoryTheory.Functor.Full, CategoryTheory.Functor.FullyFaithful, CategoryTheory.Functor.ReflectsIsomorphisms, CategoryTheory.ConcreteCategory]
  E2: [CategoryTheory.Functor.obj, CategoryTheory.Functor.map, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.comp, CategoryTheory.Functor.id, CategoryTheory.Functor.mapIso, CategoryTheory.Functor.map_isIso, CategoryTheory.Functor.FullyFaithful.preimage, CategoryTheory.Functor.FullyFaithful.ofFullyFaithful, CategoryTheory.Functor.FullyFaithful.isIso_of_isIso_map, CategoryTheory.Functor.map_injective, CategoryTheory.Functor.Full.map_surjective, CategoryTheory.isIso_of_reflects_iso, CategoryTheory.Functor.FullyFaithful.reflectsIsomorphisms, CategoryTheory.forget, CategoryTheory.forget₂, CategoryTheory.Cat, CategoryTheory.Cat.of, CategoryTheory.Functor.monotone, Monotone.functor, OrderHom.equivFunctor, CategoryTheory.SingleObj.mapHom, CategoryTheory.Functor.op]
  E1: auto
families: []
requires: [V24.C01, V04.C02, V05.C02, V05.C05, V06.C01, V07.C06, V13.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Functors

### Overview

A functor is a morphism of categories. It sends each object to an object and each morphism to a morphism, and it keeps identities and composites. Many constructions of algebra are functors: the underlying set of a group, the group of units of a ring, the abelianization of a group, the dual of a vector space. The functor property says that the construction acts on maps too, in a way compatible with composition.

This section defines functors and their composition, and the properties faithful, full and fully faithful. It proves that functors keep isomorphisms and that fully faithful functors reflect them. It shows that a functor between preorders is a monotone map and a functor between one-object categories is a homomorphism of monoids.

In Mathlib, `F : C ⥤ D` is a functor, `F.obj X` is the image of an object and `F.map f` the image of a morphism. Composition is in diagram order: `F ⋙ G` is "first `F`, then `G`", the textbook $G \circ F$, as `f ≫ g` is the textbook $g \circ f$.

### Definitions

**Definition (Functor).** Let $C$ and $D$ be categories. A *functor* $F : C \to D$ consists of a map $X \mapsto F(X)$ on objects and, for each pair $X, Y$, a map $\mathrm{Hom}_C(X, Y) \to \mathrm{Hom}_D(F(X), F(Y))$, written $f \mapsto F(f)$, such that

1. $F(1_X) = 1_{F(X)}$ for each object $X$;
2. $F(g \circ f) = F(g) \circ F(f)$ for all composable $f, g$.

A functor $C^{\mathrm{op}} \to D$ is a *contravariant functor* from $C$ to $D$. It reverses the direction of morphisms: it sends $f : X \to Y$ to a morphism $F(Y) \to F(X)$, and $F(g \circ f) = F(f) \circ F(g)$.

::: mathlib
`CategoryTheory.Functor` · `Mathlib.CategoryTheory.Functor.Basic`

`Functor C D`, with the notation `C ⥤ D`, is a structure with the fields `obj`, `map`, `map_id : F.map (𝟙 X) = 𝟙 (F.obj X)` and `map_comp : F.map (f ≫ g) = F.map f ≫ F.map g`. The two laws have the default proof `by cat_disch`. `Functor.id C`, written `𝟭 C`, is the identity functor, and `Functor.comp F G`, written `F ⋙ G`, is the composite. A contravariant functor is a term of `Cᵒᵖ ⥤ D`, and `Functor.op` turns `F : C ⥤ D` into `Cᵒᵖ ⥤ Dᵒᵖ`.

<?decl CategoryTheory.Functor?>
:::

The composite of functors $F : C \to D$ and $G : D \to E$ is $(G \circ F)(X) = G(F(X))$ and $(G \circ F)(f) = G(F(f))$. It is a functor, since $G(F(g \circ f)) = G(F(g) \circ F(f)) = G(F(g)) \circ G(F(f))$, and the same holds for identities. Composition of functors is associative, and the identity functors are units for it. In Mathlib these are the equalities `Functor.comp_id`, `Functor.id_comp` and `Functor.assoc`.

**Definition (Faithful, full, fully faithful).** A functor $F : C \to D$ is *faithful* when each map $\mathrm{Hom}_C(X, Y) \to \mathrm{Hom}_D(F(X), F(Y))$ is injective, *full* when each is surjective, and *fully faithful* when each is bijective.

::: mathlib
`CategoryTheory.Functor.Faithful` · `Mathlib.CategoryTheory.Functor.FullyFaithful`

`F.Faithful` is a class with the field `map_injective`, used through `Functor.map_injective`. `F.Full` is a class with `map_surjective`, used through `Full.map_surjective`. Both are propositions.

<?decl CategoryTheory.Functor.Faithful?>
<?decl CategoryTheory.Functor.Full?>
:::

::: mathlib
`CategoryTheory.Functor.FullyFaithful` · `Mathlib.CategoryTheory.Functor.FullyFaithful`

`F.FullyFaithful` is a structure, not a proposition. It holds the inverse map `preimage : (F.obj X ⟶ F.obj Y) → (X ⟶ Y)` with the two laws `map_preimage` and `preimage_map`. So the inverse is data and is computable. From the two classes `Full` and `Faithful`, the definition `FullyFaithful.ofFullyFaithful` builds one by choice.

<?decl CategoryTheory.Functor.FullyFaithful?>
:::

**Definition (Reflecting isomorphisms).** A functor $F$ *reflects isomorphisms* when $f$ is an isomorphism whenever $F(f)$ is one.

### Theorems and proofs

**Proposition (Functors keep isomorphisms).** Let $F : C \to D$ be a functor and $f : X \to Y$ an isomorphism with inverse $g$. Then $F(f)$ is an isomorphism with inverse $F(g)$. So $X \cong Y$ implies $F(X) \cong F(Y)$.

*Proof.* $F(g) \circ F(f) = F(g \circ f) = F(1_X) = 1_{F(X)}$, and in the same way $F(f) \circ F(g) = 1_{F(Y)}$. $\square$

In Mathlib, `Functor.mapIso` sends `X ≅ Y` to `F.obj X ≅ F.obj Y`, and the instance `Functor.map_isIso` gives `IsIso (F.map f)` from `IsIso f`. The converse fails in general, and the next result gives a case where it holds.

**Proposition (Fully faithful functors reflect isomorphisms).** Let $F : C \to D$ be fully faithful and $f : X \to Y$ in $C$. If $F(f)$ is an isomorphism, then $f$ is an isomorphism. If $F(X) \cong F(Y)$, then $X \cong Y$.

*Proof.* Let $h : F(Y) \to F(X)$ be the inverse of $F(f)$. Since $F$ is full, $h = F(g)$ for some $g : Y \to X$. Then $F(g \circ f) = h \circ F(f) = 1_{F(X)} = F(1_X)$. Since $F$ is faithful, $g \circ f = 1_X$. In the same way $f \circ g = 1_Y$. For the second claim, let $u : F(X) \to F(Y)$ be an isomorphism. Then $u = F(f)$ for some $f$, by fullness, and $f$ is an isomorphism by the first claim. $\square$

In Mathlib this is `FullyFaithful.isIso_of_isIso_map`, and the instance `FullyFaithful.reflectsIsomorphisms` gives the class. A functor reflects isomorphisms without being full in many cases.

::: mathlib
`CategoryTheory.Functor.ReflectsIsomorphisms` · `Mathlib.CategoryTheory.Functor.ReflectsIso.Basic`

`F.ReflectsIsomorphisms` is a class with the field `reflects : ∀ f, IsIso (F.map f) → IsIso f`, used through `isIso_of_reflects_iso`. The class does not assume that `F` is faithful.

<?decl CategoryTheory.Functor.ReflectsIsomorphisms?>
:::

**Theorem (Functors between preorders).** Let $P$ and $Q$ be preorders, seen as thin categories. A functor $P \to Q$ is the same as a monotone map $P \to Q$.

*Proof.* Let $F$ be a functor. If $a \le b$, there is a morphism $a \to b$, so there is a morphism $F(a) \to F(b)$, and $F(a) \le F(b)$. So the object map of $F$ is monotone. Conversely, let $\varphi$ be monotone. Define $F(a) = \varphi(a)$, and send the unique morphism $a \to b$ to the unique morphism $\varphi(a) \to \varphi(b)$, which exists since $\varphi(a) \le \varphi(b)$. The functor laws are equalities in a thin category, so they hold. Two functors with the same object map are equal, since $Q$ is thin. So the two constructions are inverse to each other. $\square$

So the morphisms of $\mathbf{Preord}$ of Chapter 1 are the functors between the preorders. Volume 4, Chapter 2 studies monotone maps.

::: mathlib
`OrderHom.equivFunctor` · `Mathlib.CategoryTheory.Category.Preorder`

The equivalence of types `(X →o Y) ≃ (X ⥤ Y)`. Its two directions are `Monotone.functor`, which builds a functor from a monotone map, and `Functor.monotone`, which says that the object map of a functor is monotone.

<?decl OrderHom.equivFunctor?>
:::

**Theorem (Functors between monoids).** Let $M$ and $N$ be monoids, and $BM$, $BN$ their one-object categories. A functor $BM \to BN$ is the same as a homomorphism of monoids $M \to N$.

*Proof.* A functor sends the one object to the one object, and it is a map $\varphi : M \to N$ on morphisms. The functor laws say $\varphi(1) = 1$ and $\varphi(gh) = \varphi(g)\varphi(h)$. These are the laws of a homomorphism of monoids. $\square$

::: mathlib
`CategoryTheory.SingleObj.mapHom` · `Mathlib.CategoryTheory.SingleObj`

The equivalence `(M →* N) ≃ SingleObj M ⥤ SingleObj N`. With it, `MonCat.toCat` is a fully faithful functor from monoids to categories.

<?decl CategoryTheory.SingleObj.mapHom?>
:::

### Examples

**Example (Forgetful functors).** The functor $U : \mathbf{Grp} \to \mathbf{Set}$ sends a group to its underlying set and a homomorphism to its function. It is faithful, since a homomorphism is determined by its function. It is not full: a function between groups is rarely a homomorphism. It reflects isomorphisms, since the inverse function of a bijective homomorphism is a homomorphism (Volume 5, Chapter 2). The forgetful functors of rings and modules behave in the same way.

::: mathlib
`CategoryTheory.ConcreteCategory` · `Mathlib.CategoryTheory.ConcreteCategory.Basic`

`ConcreteCategory C FC` says that each morphism of `C` is a bundled function of a type `FC X Y`, with the maps `hom` and `ofHom`. The functor `forget C : C ⥤ Type w` sends an object to its underlying type and is faithful. A functor between two concrete categories that commutes with the forgetful functors is `forget₂ C D`, such as the functor from rings to abelian groups. The instance `GrpCat.forget_reflects_isos` gives the fact on groups above.

<?decl CategoryTheory.ConcreteCategory?>
:::

**Example (Units and abelianization).** The group of units $R \mapsto R^\times$ is a functor from rings to groups. A ring homomorphism $f : R \to S$ sends units to units, and its restriction $f^\times$ satisfies $(g \circ f)^\times = g^\times \circ f^\times$. The abelianization $G \mapsto G/[G, G]$ is a functor from groups to abelian groups. A homomorphism $f : G \to H$ sends commutators to commutators, so it induces $G/[G, G] \to H/[H, H]$, and the uniqueness of induced maps gives the functor laws (Volume 5, Chapter 5).

**Example (The dual space).** Let $k$ be a field. The dual $V \mapsto V^* = \mathrm{Hom}_k(V, k)$ is a contravariant functor on $k$-vector spaces. A linear map $f : V \to W$ gives the transpose $f^* : W^* \to V^*$, $\lambda \mapsto \lambda \circ f$. Then $(g \circ f)^* = f^* \circ g^*$ and $1^* = 1$ (Volume 7, Chapter 6). So $V \mapsto V^*$ is a functor from the opposite of the category of vector spaces.

**Example (The power set).** The power set $X \mapsto \mathcal{P}(X)$ is a covariant functor on sets, with $f \mapsto (A \mapsto f(A))$, and a contravariant one, with $f \mapsto (B \mapsto f^{-1}(B))$. Both laws hold, since images and preimages compose.

**Counterexample (A faithful functor that does not reflect isomorphisms).** The forgetful functor $\mathbf{Top} \to \mathbf{Set}$ is faithful. Let $X$ be the set $\{0, 1\}$ with the discrete topology and $Y$ the same set with the indiscrete topology. The identity map $X \to Y$ is continuous, and its image in $\mathbf{Set}$ is a bijection. It is not a homeomorphism (Volume 13, Chapter 1). So the functor does not reflect isomorphisms.

**Counterexample (The center is not a functor).** No functor from groups to groups sends each group $G$ to its center $Z(G)$, whatever it does on morphisms. Let $i : \mathbb{Z}/2 \to S_3$ send the generator to a transposition, and let $p : S_3 \to \mathbb{Z}/2$ be the sign, so $p \circ i = 1$. If $Z$ were a functor, then $Z(p) \circ Z(i) = Z(1) = 1$ on $Z(\mathbb{Z}/2) = \mathbb{Z}/2$. But this composite factors through $Z(S_3)$, which is trivial. So it is trivial, a contradiction.

### The library around it

The file `Mathlib.CategoryTheory.Functor.Basic` has `Functor`, `Functor.comp` and `Functor.id`. The simp lemmas `Functor.map_id` and `Functor.map_comp` rewrite the images of composites. The file `Mathlib.CategoryTheory.Category.Cat` defines `Cat`, the category of categories with functors as morphisms. An object `Cat.of C` bundles a type with a category instance. A morphism of `Cat` is a structure that wraps a functor.

Common errors of a learner:

- `F ⋙ G` is "first `F`, then `G`", the textbook $G \circ F$.
- `F.FullyFaithful` is data, not a `Prop`. To state that `F` is fully faithful, use `F.Full` and `F.Faithful`, or give a term of `F.FullyFaithful`.
- Two functors with equal object maps and equal morphism maps are equal, but the equality of object maps makes the morphism maps live in different types. Compare functors by natural isomorphisms (Section 2), not by equality.

### Exercises

1. (A) Show that a composite of faithful functors is faithful, and a composite of full functors is full.
2. (A) Show that the forgetful functor from abelian groups to groups is fully faithful.
3. (A) Show that a functor $F : C \to D$ gives a functor $C^{\mathrm{op}} \to D^{\mathrm{op}}$ with the same maps.
4. (B) Show that the forgetful functor from rings to sets reflects isomorphisms, and that the forgetful functor from partial orders to sets does not.
5. (B) Show that $G \mapsto G \times G$ and $G \mapsto$ the set of elements of order dividing $2$ are functors on groups, the second with values in sets.
6. (B) Let $F : C \to D$ be fully faithful. Show that each morphism $F(X) \to F(X)$ comes from a unique endomorphism of $X$, and that $\mathrm{End}(X) \to \mathrm{End}(F(X))$ is an isomorphism of monoids.
7. (C) Let $G$ be a group. Show that a functor $BG \to \mathbf{Set}$ is a set with an action of $G$, and that a functor $BG \to \mathbf{Vect}_k$ is a linear representation of $G$ (Volume 5, Chapter 6).

### Notes and history

Functors were defined with categories in Eilenberg and Mac Lane, "General theory of natural equivalences" (1945). Their first examples were the functors of algebraic topology, such as homology. The name "functor" was taken from the philosopher Carnap. Mac Lane, *Categories for the Working Mathematician* (1971), Chapter 1, and Riehl, *Category Theory in Context* (2016), Chapter 1, treat this material.

### Reference

<?reference?>
