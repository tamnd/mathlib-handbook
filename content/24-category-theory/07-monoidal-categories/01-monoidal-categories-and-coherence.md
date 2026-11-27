---
title: Monoidal categories and coherence
kind: theory
modules:
  - Mathlib.CategoryTheory.Monoidal.Category
  - Mathlib.CategoryTheory.Monoidal.Free.Basic
  - Mathlib.CategoryTheory.Monoidal.Free.Coherence
  - Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
  - Mathlib.CategoryTheory.Monoidal.Types.Basic
explains:
  E3: [CategoryTheory.MonoidalCategory, CategoryTheory.MonoidalCategory.pentagon, CategoryTheory.MonoidalCategory.whisker_exchange, CategoryTheory.FreeMonoidalCategory, CategoryTheory.FreeMonoidalCategory.subsingleton_hom, CategoryTheory.MonoidalCategory.unitors_equal, CategoryTheory.typesCartesianMonoidalCategory]
  E2: [CategoryTheory.MonoidalCategoryStruct, CategoryTheory.MonoidalCategory.triangle, CategoryTheory.MonoidalCategory.tensorHom_def, CategoryTheory.MonoidalCategory.associator_naturality, CategoryTheory.MonoidalCategory.ofTensorHom, CategoryTheory.MonoidalCategory.leftUnitor_tensor_hom, CategoryTheory.MonoidalCategory.tensorLeft, CategoryTheory.MonoidalCategory.prodMonoidal, CategoryTheory.FreeMonoidalCategory.project, CategoryTheory.FreeMonoidalCategory.fullNormalizeIso, CategoryTheory.FreeMonoidalCategory.NormalMonoidalObject, CategoryTheory.types_tensorObj_def, CategoryTheory.types_tensorUnit_def]
  E1: auto
families: []
requires: [V08, V24.C02, V24.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Monoidal categories and coherence

### Overview

Many categories carry a product of objects that is associative and unital up to isomorphism: sets with the cartesian product, modules over a commutative ring with the tensor product, endofunctors with composition. A *monoidal category* axiomatizes this. The associativity is an isomorphism $\alpha$, not an equality, so the axioms must say how the isomorphisms fit together. Two axioms suffice, the pentagon and the triangle. Mac Lane's coherence theorem then says that every diagram built from $\alpha$ and the unitors commutes.

This section gives the definition in the textbook form and in Mathlib's whiskered form, the first consequences of the axioms, the examples, and the idea of the proof of coherence. In Mathlib, `f ≫ g` is "first $f$, then $g$", the textbook $g \circ f$.

### Definitions

**Definition (Monoidal category).** A *monoidal category* is a category $C$ with a functor $\otimes : C \times C \to C$, an object $I$, and natural isomorphisms
$$\alpha_{X,Y,Z} : (X \otimes Y) \otimes Z \to X \otimes (Y \otimes Z), \qquad \lambda_X : I \otimes X \to X, \qquad \rho_X : X \otimes I \to X,$$
the *associator* and the *left* and *right unitors*, such that for all objects the *pentagon* and the *triangle* hold:
$$(\mathrm{id}_W \otimes \alpha_{X,Y,Z}) \circ \alpha_{W, X \otimes Y, Z} \circ (\alpha_{W,X,Y} \otimes \mathrm{id}_Z) = \alpha_{W,X,Y \otimes Z} \circ \alpha_{W \otimes X, Y, Z},$$
$$(\mathrm{id}_X \otimes \lambda_Y) \circ \alpha_{X,I,Y} = \rho_X \otimes \mathrm{id}_Y.$$
The category is *strict* if $\alpha$, $\lambda$ and $\rho$ are identities.

**Definition (Whiskering).** For an object $X$ and a morphism $g : Y \to Y'$, the *left whiskering* is $X \triangleleft g = \mathrm{id}_X \otimes g$. For $f : X \to X'$, the *right whiskering* is $f \triangleright Y = f \otimes \mathrm{id}_Y$.

Functoriality of $\otimes$ in each variable says $X \triangleleft (g' \circ g) = (X \triangleleft g') \circ (X \triangleleft g)$ and $X \triangleleft \mathrm{id} = \mathrm{id}$, and the same for $\triangleright$. The proposition below shows that whiskerings, with one exchange law, carry the same information as the bifunctor.

::: mathlib
`CategoryTheory.MonoidalCategory` · `Mathlib.CategoryTheory.Monoidal.Category`

The data are in `MonoidalCategoryStruct C`: `tensorObj X Y`, written `X ⊗ Y`, `whiskerLeft X g`, written `X ◁ g`, `whiskerRight f Y`, written `f ▷ Y`, `tensorHom f g`, the unit `𝟙_ C`, and the isomorphisms `α_ X Y Z`, `λ_ X` and `ρ_ X`. The class `MonoidalCategory C` adds the laws. The field `tensorHom_def` says `tensorHom f g = f ▷ X₂ ≫ Y₁ ◁ g`. The field `MonoidalCategory.pentagon` is stated with whiskerings: `(α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom = (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom`. Naturality of the associator is the field `associator_naturality`. To build an instance from a bifunctor in the textbook style, use `MonoidalCategory.ofTensorHom`.

<?decl CategoryTheory.MonoidalCategory?>
:::

Mathlib takes the whiskerings as primitive because most morphisms in practice are whiskered: each factor of a composite acts on one tensor factor and is the identity on the others. A composite of whiskerings has a normal form, and the `monoidal` tactic works with it. The term `tensorHom f g` hides an exchange, and rewriting with it is harder.

### Theorems and proofs

**Proposition (Whiskering and the tensor of morphisms).** In a monoidal category, for $f : X_1 \to Y_1$ and $g : X_2 \to Y_2$,
$$f \otimes g = (Y_1 \triangleleft g) \circ (f \triangleright X_2) = (f \triangleright Y_2) \circ (X_1 \triangleleft g).$$
Conversely, let left and right whiskerings be given that are functorial in the morphism and satisfy the exchange law $(f \triangleright Y_2) \circ (X_1 \triangleleft g) = (Y_1 \triangleleft g) \circ (f \triangleright X_2)$. Then $f \otimes g = (Y_1 \triangleleft g) \circ (f \triangleright X_2)$ defines a functor $C \times C \to C$.

*Proof.* In $C \times C$, $(f, g) = (\mathrm{id}, g) \circ (f, \mathrm{id}) = (f, \mathrm{id}) \circ (\mathrm{id}, g)$. Apply the functor $\otimes$. For the converse, $\mathrm{id} \otimes \mathrm{id} = \mathrm{id}$ is clear. For $f' : Y_1 \to Z_1$ and $g' : Y_2 \to Z_2$, the exchange law moves $f' \triangleright Y_2$ past $Y_1 \triangleleft g$:
$$(f' \otimes g') \circ (f \otimes g) = (Z_1 \triangleleft g') \circ (f' \triangleright Y_2) \circ (Y_1 \triangleleft g) \circ (f \triangleright X_2) = (Z_1 \triangleleft g') \circ (Z_1 \triangleleft g) \circ (f' \triangleright X_2) \circ (f \triangleright X_2),$$
which is $(Z_1 \triangleleft g'g) \circ (f'f \triangleright X_2) = (f'f) \otimes (g'g)$. $\square$

::: mathlib
`CategoryTheory.MonoidalCategory.whisker_exchange` · `Mathlib.CategoryTheory.Monoidal.Category`

The exchange law reads `W ◁ g ≫ f ▷ Z = f ▷ Y ≫ X ◁ g` for `f : W ⟶ X` and `g : Y ⟶ Z`. The functor `tensorLeft X` is $X \otimes -$, and `prodMonoidal` puts the monoidal structure on a product of two monoidal categories.

<?decl CategoryTheory.MonoidalCategory.whisker_exchange?>
:::

**Lemma (Unit functors are faithful).** The functors $I \otimes -$ and $- \otimes I$ are faithful, and $\lambda_{I \otimes X} = \mathrm{id}_I \otimes \lambda_X$.

*Proof.* Naturality of $\lambda$ gives $\lambda_{Y} \circ (I \triangleleft h) = h \circ \lambda_X$ for $h : X \to Y$, so $I \triangleleft h = \lambda_Y^{-1} \circ h \circ \lambda_X$, which determines $h$. The same argument with $\rho$ works for $- \otimes I$. Naturality of $\lambda$ at $h = \lambda_X : I \otimes X \to X$ gives $\lambda_X \circ (I \triangleleft \lambda_X) = \lambda_X \circ \lambda_{I \otimes X}$. Cancel the isomorphism $\lambda_X$. $\square$

**Proposition (Left unitor of a tensor product).** For all $X, Y$, $\lambda_{X \otimes Y} \circ \alpha_{I,X,Y} = \lambda_X \triangleright Y$.

*Proof.* By the lemma it suffices to prove the equation after $I \triangleleft -$. The pentagon at $(I, I, X, Y)$ gives
$$(I \triangleleft \alpha_{I,X,Y}) \circ \alpha_{I, I \otimes X, Y} \circ (\alpha_{I,I,X} \triangleright Y) = \alpha_{I,I,X \otimes Y} \circ \alpha_{I \otimes I, X, Y}.$$
Compose on the left with $I \triangleleft \lambda_{X \otimes Y}$. The triangle at $(I, X \otimes Y)$ turns the right side into $(\rho_I \triangleright (X \otimes Y)) \circ \alpha_{I \otimes I, X, Y}$. Naturality of $\alpha$ in the first variable turns this into $\alpha_{I,X,Y} \circ ((\rho_I \triangleright X) \triangleright Y)$. The triangle at $(I, X)$ gives $\rho_I \triangleright X = (I \triangleleft \lambda_X) \circ \alpha_{I,I,X}$, so the right side is $\alpha_{I,X,Y} \circ ((I \triangleleft \lambda_X) \triangleright Y) \circ (\alpha_{I,I,X} \triangleright Y)$. Naturality of $\alpha$ in the middle variable turns it into $(I \triangleleft (\lambda_X \triangleright Y)) \circ \alpha_{I, I \otimes X, Y} \circ (\alpha_{I,I,X} \triangleright Y)$. The left side is $(I \triangleleft (\lambda_{X \otimes Y} \circ \alpha_{I,X,Y})) \circ \alpha_{I, I \otimes X, Y} \circ (\alpha_{I,I,X} \triangleright Y)$. Cancel the isomorphism $\alpha_{I, I \otimes X, Y} \circ (\alpha_{I,I,X} \triangleright Y)$ on the right. $\square$

**Corollary (The two unitors of the unit agree).** $\lambda_I = \rho_I$.

*Proof.* Take $X = Y = I$ in the proposition and use the lemma: $\lambda_I \triangleright I = \lambda_{I \otimes I} \circ \alpha_{I,I,I} = (I \triangleleft \lambda_I) \circ \alpha_{I,I,I}$. By the triangle at $(I, I)$, this is $\rho_I \triangleright I$. Since $- \otimes I$ is faithful, $\lambda_I = \rho_I$. $\square$

::: mathlib
`CategoryTheory.MonoidalCategory.unitors_equal` · `Mathlib.CategoryTheory.Monoidal.CoherenceLemmas`

The corollary is `unitors_equal : (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom`. The proposition is `MonoidalCategory.leftUnitor_tensor_hom`, which reads `(λ_ (X ⊗ Y)).hom = (α_ (𝟙_ C) X Y).inv ≫ (λ_ X).hom ▷ Y`.

<?decl CategoryTheory.MonoidalCategory.unitors_equal?>
:::

**Theorem (Mac Lane's coherence theorem).** Let $S$ be a set and $F(S)$ the free monoidal category on $S$: its objects are the bracketed words in the letters of $S$ and the symbol $I$, and its morphisms are the formal composites and tensor products of identities, of $\alpha$, $\lambda$, $\rho$ and their inverses, modulo the axioms of a monoidal category. Then between two objects of $F(S)$ there is at most one morphism.

*Idea of the proof.* Every object $A$ of $F(S)$ has a *normal form* $N(A)$, the list of its letters in order, with the brackets and the symbols $I$ removed. Morphisms of $F(S)$ do not change this list. So $N$ is a functor from $F(S)$ to the discrete category on the lists, and there is an inclusion $\iota$ back that brackets a list to the left. The work of the proof is to build a natural isomorphism $\nu : \mathrm{id} \Rightarrow \iota \circ N$, by induction on the words, and the pentagon and the triangle are exactly what makes $\nu$ natural. Then for $f : A \to B$, naturality gives $\nu_B \circ f = \iota(Nf) \circ \nu_A = \nu_A$, since $Nf$ is an identity of a discrete category. So $f = \nu_B^{-1} \circ \nu_A$ depends only on $A$ and $B$. $\square$

For a monoidal category $C$ and a map $S \to C$ on objects, there is a strict monoidal functor $F(S) \to C$. Every diagram in $C$ that is the image of a diagram in $F(S)$ therefore commutes. The condition matters: a map in $C$ can have the right source and target without being the image of a formal map.

::: mathlib
`CategoryTheory.FreeMonoidalCategory.subsingleton_hom` · `Mathlib.CategoryTheory.Monoidal.Free.Coherence`

`FreeMonoidalCategory C` is an inductive type of formal words, and its morphisms are formal morphisms modulo the relation `HomEquiv`. The statement `subsingleton_hom : Quiver.IsThin (FreeMonoidalCategory C)` is the theorem. The proof follows the normalization argument above: `NormalMonoidalObject C` is the type of normal forms, and `fullNormalizeIso` is the isomorphism $\nu$. The functor `FreeMonoidalCategory.project` sends formal words to a monoidal category. The file states that it follows Beylin and Dybjer. In practice, the `coherence` tactic proves an equation between two composites of structural isomorphisms, and the `monoidal` tactic also handles whiskered morphisms between them.

<?decl CategoryTheory.FreeMonoidalCategory.subsingleton_hom?>
:::

### Examples

**Example (Cartesian products of sets).** On types, $X \otimes Y = X \times Y$ and $I$ is a one-point set $\{\ast\}$. The associator is $((x, y), z) \mapsto (x, (y, z))$, and $\lambda(\ast, x) = x$, $\rho(x, \ast) = x$. For the pentagon, both sides send $(((w, x), y), z)$ to $(w, (x, (y, z)))$. For the triangle, both sides send $((x, \ast), y)$ to $(x, y)$. The category is not strict: $(X \times Y) \times Z$ and $X \times (Y \times Z)$ are different sets. Any category with finite products is monoidal in the same way.

::: mathlib
`CategoryTheory.typesCartesianMonoidalCategory` · `Mathlib.CategoryTheory.Monoidal.Types.Basic`

This instance makes `Type u` a cartesian monoidal category, and so a monoidal category. The lemmas `types_tensorObj_def : X ⊗ Y = (X × Y)` and `types_tensorUnit_def` unfold the data.

<?decl CategoryTheory.typesCartesianMonoidalCategory?>
:::

**Example (Modules).** Let $R$ be a commutative ring. On $R$-modules, $M \otimes N = M \otimes_R N$ and $I = R$ (Volume 8, Chapter 2). The associator is the linear map with $(m \otimes n) \otimes p \mapsto m \otimes (n \otimes p)$, and $\lambda(r \otimes m) = rm$. The pentagon and the triangle hold on the pure tensors, which generate. The cartesian product $M \times N$ also gives a monoidal structure, with unit $0$; the two structures differ, since $R \otimes_R R \cong R$ while $R \times R$ has rank $2$.

::: mathlib
`ModuleCat.monoidalCategory` · `Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic`

For a commutative ring `R`, this instance on `ModuleCat R` has the tensor product of modules as `M ⊗ N` and `R` as the unit. Volume 26 uses it.
:::

**Example (Endofunctors).** The functors $C \to C$ with the natural transformations form a strict monoidal category, with composition as tensor product and the identity functor as unit. The whiskerings are the whiskerings of natural transformations of Chapter 2, and the exchange law is the interchange law. Mathlib's instance `endofunctorMonoidalCategory` defines `F ⊗ G` as `F ⋙ G`, so $(F \otimes G)(X) = G(F(X))$.

### The library around it

Besides the coherence statements, Mathlib has `MonoidalCategory.associatorNatIso`, which packages $\alpha$ as an isomorphism of functors $C \times C \times C \to C$. Proofs in the library rarely use `FreeMonoidalCategory` directly; they call the tactics.

### Exercises

1. (A) Show that a monoid $M$, seen as a discrete category with $m \otimes n = mn$, is a strict monoidal category. Conversely, show that a strict monoidal structure on a discrete category is a monoid.
2. (A) Show that $\rho_{X \otimes I} = \rho_X \triangleright I$. Hint: imitate the lemma on faithful unit functors.
3. (A) Show that pointed sets with the smash product $X \wedge Y = (X \times Y)/(X \times \{y_0\} \cup \{x_0\} \times Y)$ form a monoidal category with unit a two-point set.
4. (B) Prove that $(X \triangleleft \rho_Y) \circ \alpha_{X,Y,I} = \rho_{X \otimes Y}$, with the method of the proposition on the left unitor.
5. (B) Let $C$ be monoidal. Show that $\mathrm{End}(I)$ is a commutative monoid. Hint: for $f, g : I \to I$, write $g \circ f$ with $f \triangleright I$ and $I \triangleleft g$, use the exchange law and the corollary.
6. (C) In sets with $\times$, let $X$ have two elements. The map $(x, y) \mapsto (y, x)$ is an endomorphism of $X \otimes X$ that is not the identity. Explain why this does not contradict the coherence theorem, and describe the diagrams in $\mathbf{Set}$ to which the theorem applies.

### Notes and history

Monoidal categories appeared in 1963, in the work of Bénabou and of Mac Lane. Mac Lane's paper "Natural associativity and commutativity" (1963) proved the coherence theorem. Kelly (1964) showed that some of Mac Lane's axioms follow from the pentagon and the triangle, with arguments like the proof of $\lambda_I = \rho_I$ above. Mac Lane's *Categories for the Working Mathematician* (1971) gives the coherence theorem with a proof by normal forms.

### Reference

<?reference?>
