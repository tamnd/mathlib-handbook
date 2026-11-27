---
title: The Yoneda lemma
kind: theory
modules:
  - Mathlib.CategoryTheory.Yoneda
explains:
  E3: [CategoryTheory.yoneda, CategoryTheory.coyoneda, CategoryTheory.yonedaEquiv, CategoryTheory.yonedaLemma, CategoryTheory.Yoneda.fullyFaithful]
  E2: [CategoryTheory.yonedaPairing, CategoryTheory.yonedaEvaluation, CategoryTheory.yonedaEquiv_naturality, CategoryTheory.yonedaEquiv_comp, CategoryTheory.yonedaEquiv_apply, CategoryTheory.yonedaEquiv_symm_app_apply, CategoryTheory.curriedYonedaLemma, CategoryTheory.Yoneda.yoneda_full, CategoryTheory.Yoneda.yoneda_faithful, CategoryTheory.Yoneda.isIso, CategoryTheory.Yoneda.ext, CategoryTheory.coyonedaEquiv, CategoryTheory.coyonedaLemma, CategoryTheory.Coyoneda.fullyFaithful]
  E1: auto
families: []
requires: [V24.C01, V24.C02, V04.C01, V05.C01, V05.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The Yoneda lemma

### Overview

An object of a category has no elements, but it has morphisms into it. For each object $X$, the sets $\mathrm{Hom}(W, X)$, for all $W$, form a functor $\mathrm{Hom}(-, X)$ from $C^{\mathrm{op}}$ to sets. The Yoneda lemma computes the natural transformations from this functor to any functor $F : C^{\mathrm{op}} \to \mathbf{Set}$: they correspond to the elements of $F(X)$. The bijection sends a transformation $\alpha$ to $\alpha_X(1_X)$.

The proof is short, and each step is forced. Its consequences are many. The functor $X \mapsto \mathrm{Hom}(-, X)$ is fully faithful, so each category embeds in a category of functors to sets. Two objects with naturally isomorphic functors of morphisms are isomorphic. For a group seen as a one-object category, the embedding is Cayley's theorem.

Mathlib composes in diagram order: `f ≫ g` is the textbook $g \circ f$. In the functor of morphisms, a morphism $f : W' \to W$ acts on $u : W \to X$ by $u \mapsto u \circ f$, which Mathlib writes `f ≫ u`.

### Definitions

**Definition (Functors of morphisms).** Let $C$ be a locally small category and $X$ an object. The *contravariant functor of morphisms* $h_X = \mathrm{Hom}(-, X) : C^{\mathrm{op}} \to \mathbf{Set}$ sends $W$ to $\mathrm{Hom}(W, X)$ and $f : W' \to W$ to the map $u \mapsto u \circ f$. The *covariant functor of morphisms* $h^X = \mathrm{Hom}(X, -) : C \to \mathbf{Set}$ sends $Z$ to $\mathrm{Hom}(X, Z)$ and $g : Z \to Z'$ to $v \mapsto g \circ v$.

Both are functors by the associative law and the unit laws. A functor $C^{\mathrm{op}} \to \mathbf{Set}$ is a *presheaf* on $C$, and the functor category $[C^{\mathrm{op}}, \mathbf{Set}]$ is the *category of presheaves*.

**Definition (Yoneda embedding).** The *Yoneda embedding* $y : C \to [C^{\mathrm{op}}, \mathbf{Set}]$ sends $X$ to $h_X$ and $g : X \to Y$ to the natural transformation $h_g : h_X \Rightarrow h_Y$ with components $u \mapsto g \circ u$.

The map $h_g$ is natural, since $g \circ (u \circ f) = (g \circ u) \circ f$. The functor laws for $y$ are the unit and associative laws again.

::: mathlib
`CategoryTheory.yoneda` · `Mathlib.CategoryTheory.Yoneda`

`yoneda : C ⥤ (Cᵒᵖ ⥤ Type v₁)` for a category `C` with `Category.{v₁} C`. The value `(yoneda.obj X).obj (op W)` is `W ⟶ X`. The values live in `Type v₁`, the universe of the morphisms, so `C` must be locally small in this sense. The functor `uliftYoneda` moves the values to a higher universe.

<?decl CategoryTheory.yoneda?>
:::

::: mathlib
`CategoryTheory.coyoneda` · `Mathlib.CategoryTheory.Yoneda`

`coyoneda : Cᵒᵖ ⥤ (C ⥤ Type v₁)`, with `(coyoneda.obj (op X)).obj Z` equal to `X ⟶ Z`. It is the family of covariant functors of morphisms $h^X$. The object `X` enters through `op X`, since $X \mapsto h^X$ is contravariant.

<?decl CategoryTheory.coyoneda?>
:::

### Theorems and proofs

**Theorem (Yoneda lemma).** Let $F : C^{\mathrm{op}} \to \mathbf{Set}$ be a functor and $X$ an object of $C$. The map
$$\Phi : \mathrm{Nat}(h_X, F) \to F(X), \qquad \alpha \mapsto \alpha_X(1_X)$$
is a bijection. Its inverse sends $x \in F(X)$ to the transformation $\Psi(x)$ with components $\Psi(x)_W(u) = F(u)(x)$ for $u : W \to X$.

*Proof.* First, $\Psi(x)$ is natural. Let $f : W' \to W$ and $u \in h_X(W)$. Then
$$\Psi(x)_{W'}(u \circ f) = F(u \circ f)(x) = F(f)(F(u)(x)) = F(f)(\Psi(x)_W(u)),$$
since $F$ is contravariant. This is the naturality square at $f$.

Next, $\Phi(\Psi(x)) = \Psi(x)_X(1_X) = F(1_X)(x) = x$.

Last, let $\alpha$ be a natural transformation and $x = \alpha_X(1_X)$. For $u : W \to X$, the naturality of $\alpha$ at the morphism $u$ says $\alpha_W \circ h_X(u) = F(u) \circ \alpha_X$. Apply both sides to $1_X$. Since $h_X(u)(1_X) = 1_X \circ u = u$, this gives
$$\alpha_W(u) = F(u)(\alpha_X(1_X)) = \Psi(x)_W(u).$$
So $\Psi(\Phi(\alpha)) = \alpha$. $\square$

The last step is the heart of the lemma: a natural transformation out of $h_X$ is determined by its value on the single element $1_X$, since each $u : W \to X$ is the image of $1_X$ under $h_X(u)$.

::: mathlib
`CategoryTheory.yonedaEquiv` · `Mathlib.CategoryTheory.Yoneda`

`yonedaEquiv : (yoneda.obj X ⟶ F) ≃ F.obj (op X)` for `F : Cᵒᵖ ⥤ Type v₁`. The forward map is `η.app (op X) (𝟙 X)`, the map $\Phi$, and the inverse has the components `fun f ↦ F.map f.op ξ`, the map $\Psi$. The lemmas `yonedaEquiv_apply` and `yonedaEquiv_symm_app_apply` unfold the two directions. `yonedaEquiv_comp` says `yonedaEquiv (α ≫ β) = β.app _ (yonedaEquiv α)`.

<?decl CategoryTheory.yonedaEquiv?>
:::

**Proposition (Naturality of the Yoneda bijection).** The bijection $\Phi$ is natural in $X$ and in $F$. For $g : X' \to X$, a transformation $\alpha : h_X \Rightarrow F$ and a transformation $\beta : F \Rightarrow G$,
$$\Phi(\alpha \circ h_g) = F(g)(\Phi(\alpha)), \qquad \Phi(\beta \circ \alpha) = \beta_X(\Phi(\alpha)).$$

*Proof.* For the first, $\Phi(\alpha \circ h_g) = \alpha_{X'}(g \circ 1_{X'}) = \alpha_{X'}(g)$. By the last step of the proof above, $\alpha_{X'}(g) = F(g)(\alpha_X(1_X)) = F(g)(\Phi(\alpha))$. For the second, $\Phi(\beta \circ \alpha) = \beta_X(\alpha_X(1_X))$ by the definition of the vertical composite. $\square$

So $\Phi$ is a natural isomorphism between two functors $C^{\mathrm{op}} \times [C^{\mathrm{op}}, \mathbf{Set}] \to \mathbf{Set}$: the pairing $(X, F) \mapsto \mathrm{Nat}(h_X, F)$ and the evaluation $(X, F) \mapsto F(X)$.

::: mathlib
`CategoryTheory.yonedaLemma` · `Mathlib.CategoryTheory.Yoneda`

`yonedaLemma C : yonedaPairing C ≅ yonedaEvaluation C`, a natural isomorphism of functors on `Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)`. The evaluation functor `yonedaEvaluation` takes values in `Type (max u₁ v₁)`, with a `ULift`, so that the two sides live in the same universe. For most uses, `yonedaEquiv` and the lemma `yonedaEquiv_naturality` are simpler. `curriedYonedaLemma` is a curried form.

<?decl CategoryTheory.yonedaLemma?>
:::

**Corollary (The Yoneda embedding is fully faithful).** For all objects $X$ and $Y$, the map $\mathrm{Hom}(X, Y) \to \mathrm{Nat}(h_X, h_Y)$, $g \mapsto h_g$, is a bijection.

*Proof.* Apply the lemma to $F = h_Y$. The map $\Phi : \mathrm{Nat}(h_X, h_Y) \to h_Y(X) = \mathrm{Hom}(X, Y)$ is a bijection. It is a left inverse of $g \mapsto h_g$, since $\Phi(h_g) = g \circ 1_X = g$. A left inverse of a map that is a bijection is its inverse, so $g \mapsto h_g$ is the inverse bijection $\Phi^{-1}$. $\square$

**Corollary (Detection of isomorphisms).** A morphism $g : X \to Y$ is an isomorphism if and only if $h_g$ is a natural isomorphism, that is, if and only if each map $\mathrm{Hom}(W, X) \to \mathrm{Hom}(W, Y)$, $u \mapsto g \circ u$, is a bijection. Two objects $X$ and $Y$ are isomorphic if and only if $h_X \cong h_Y$.

*Proof.* A fully faithful functor reflects isomorphisms (Chapter 2, Section 1), and each functor keeps them. A natural transformation is an isomorphism exactly when each component is a bijection (Chapter 2, Section 2). For the last claim, an isomorphism $h_X \cong h_Y$ is $h_g$ for some $g$ by fullness, and $g$ is an isomorphism by the first claim. $\square$

::: mathlib
`CategoryTheory.Yoneda.fullyFaithful` · `Mathlib.CategoryTheory.Yoneda`

`Yoneda.fullyFaithful : yoneda.FullyFaithful`, with `preimage f := f.app _ (𝟙 _)`, the map $\Phi$. The instances `Yoneda.yoneda_full` and `Yoneda.yoneda_faithful` give the classes. `Yoneda.isIso` says that `f` is an isomorphism when `yoneda.map f` is one. `Yoneda.ext` builds `X ≅ Y` from maps `(Z ⟶ X) → (Z ⟶ Y)` and back that are inverse and natural.

<?decl CategoryTheory.Yoneda.fullyFaithful?>
:::

The dual statements hold for covariant functors. For $F : C \to \mathbf{Set}$, the map $\mathrm{Nat}(h^X, F) \to F(X)$, $\alpha \mapsto \alpha_X(1_X)$, is a bijection, and $X \mapsto h^X$ is a fully faithful functor $C^{\mathrm{op}} \to [C, \mathbf{Set}]$. The proof is the same proof in $C^{\mathrm{op}}$. In Mathlib these are `coyonedaEquiv`, `coyonedaLemma` and `Coyoneda.fullyFaithful`.

### Examples

**Example (Cayley's theorem).** Let $G$ be a group and $BG$ its one-object category, with $g \circ h = gh$. The functor $h_\star$ is the set $G$, and a morphism $f$ acts on $u \in G$ by $u \mapsto u \circ f = uf$. So $h_\star$ is $G$ with the right action of $G$ on itself. The Yoneda embedding sends $g$ to $h_g : u \mapsto gu$, the left multiplication. By the corollary, $g \mapsto h_g$ is a bijection from $G$ onto the maps $G \to G$ that commute with right multiplications. It is a homomorphism, since $h_{gg'} = h_g \circ h_{g'}$, and it is injective. So $G$ is isomorphic to a subgroup of the symmetric group of the set $G$ (Volume 5, Chapter 2). This is Cayley's theorem. The Yoneda lemma adds the converse: each $\varphi : G \to G$ with $\varphi(uf) = \varphi(u) f$ is a left multiplication, by $\varphi(1)$.

**Example (Down-sets of a preorder).** Let $P$ be a preorder, seen as a thin category. The functor $h_a$ sends $b$ to a one-point set if $b \le a$ and to the empty set otherwise. So $h_a$ is the down-set ${\downarrow} a = \{b : b \le a\}$. A natural transformation $h_a \Rightarrow h_c$ exists exactly when ${\downarrow} a \subseteq {\downarrow} c$, and it is unique. The Yoneda embedding thus says $a \le c$ if and only if ${\downarrow} a \subseteq {\downarrow} c$ (Volume 4, Chapter 1). In this case the lemma is the simple fact that $a \in {\downarrow} a$.

**Example (Natural operations on groups).** Let $U : \mathbf{Grp} \to \mathbf{Set}$ be the forgetful functor. A homomorphism $\mathbb{Z} \to G$ is determined by the image of $1$, and each element is such an image (Volume 5, Chapter 2). So $U \cong h^{\mathbb{Z}}$. The covariant Yoneda lemma gives $\mathrm{Nat}(U, U) \cong \mathrm{Nat}(h^{\mathbb{Z}}, U) \cong U(\mathbb{Z}) = \mathbb{Z}$. So the only maps $G \to G$, defined for all groups and commuting with all homomorphisms, are the powers $x \mapsto x^n$ for $n \in \mathbb{Z}$. In the same way, $U \times U \cong h^{F_2}$ for the free group $F_2$ on two letters, and the natural operations $G \times G \to G$ are the words in two letters.

**Counterexample (A presheaf that is not representable).** Let $C$ be the category with one object $\star$ and one morphism. A presheaf on $C$ is a set, and $h_\star$ is a one-point set. So the presheaves given by the empty set or by a two-point set are not isomorphic to any $h_X$. The Yoneda embedding is fully faithful but not essentially surjective. Section 2 studies the presheaves in its essential image.

### The library around it

The file `Mathlib.CategoryTheory.Yoneda` has the functors, the lemma in three forms (`yonedaEquiv`, `yonedaLemma` and `curriedYonedaLemma`), and the representable functors of Section 2. The variants `uliftYoneda` and `uliftCoyoneda` lift the universe of the values. The tactic `simp` knows `yonedaEquiv_apply` and the naturality lemmas, so many computations with presheaves reduce to the element $1_X$.

Common errors of a learner:

- A presheaf is a functor `Cᵒᵖ ⥤ Type v₁`. Its value at `X : C` is `F.obj (op X)`, and its map at `f : X ⟶ Y` is `F.map f.op : F.obj (op Y) ⟶ F.obj (op X)`.
- In `yoneda.obj X`, the action of `f` on `u` is `f ≫ u`, the textbook $u \circ f$. The functor `yoneda.map g` acts by `u ≫ g`, the textbook $g \circ u$.
- The universes must match: `yonedaEquiv` needs `F : Cᵒᵖ ⥤ Type v₁` with the same `v₁` as the morphisms of `C`.

### Exercises

1. (A) Write out the dual Yoneda lemma for $F : C \to \mathbf{Set}$ and prove it, without the passage to $C^{\mathrm{op}}$.
2. (A) Show that two morphisms $g, g' : X \to Y$ are equal if and only if $g \circ u = g' \circ u$ for each object $W$ and each $u : W \to X$. Explain why this is a weak form of faithfulness of the Yoneda embedding.
3. (A) Let $P$ be a partial order. Use the Yoneda embedding to show that $a = c$ if and only if ${\downarrow} a = {\downarrow} c$.
4. (B) Use the Yoneda lemma to show that a product $X \times Y$ in a category, if it exists, is unique up to isomorphism. Hint: $\mathrm{Hom}(W, X \times Y) \cong \mathrm{Hom}(W, X) \times \mathrm{Hom}(W, Y)$ naturally in $W$.
5. (B) Let $U : \mathbf{Ring} \to \mathbf{Set}$ be the forgetful functor. Using $U \cong h^{\mathbb{Z}[t]}$ (Section 2), show that the natural maps $R \to R$ for all rings are the evaluations of integer polynomials.
6. (B) Let $G$ be a group. Show that the natural transformations $h_\star \Rightarrow h_\star$ of the presheaf $h_\star$ on $BG$ form a group isomorphic to $G$, and identify the group of $G$-equivariant bijections of a right $G$-set $X$ with one orbit and trivial stabilizers.
7. (C) Let $C$ be small. Show that $\mathrm{Nat}(h_X \times h_Y, F)$ is in bijection with the set of elements of $F(X \times Y)$ when the product $X \times Y$ exists in $C$, and give an example where $h_X \times h_Y$ is not representable.

### Notes and history

The lemma is named after Nobuo Yoneda, who worked with it in the 1950s. Mac Lane, *Categories for the Working Mathematician* (1971), Chapter 3, places it with universal properties. Grothendieck used the embedding of a category into presheaves throughout algebraic geometry, where a scheme is studied by its functor of points. Riehl, *Category Theory in Context* (2016), Chapter 2, gives a full treatment with many examples.

### Reference

<?reference?>
