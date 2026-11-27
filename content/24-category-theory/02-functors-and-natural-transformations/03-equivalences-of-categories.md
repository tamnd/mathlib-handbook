---
title: Equivalences of categories
kind: theory
modules:
  - Mathlib.CategoryTheory.Equivalence
  - Mathlib.CategoryTheory.EssentialImage
  - Mathlib.CategoryTheory.Skeletal
explains:
  E3: [CategoryTheory.Equivalence, CategoryTheory.Functor.IsEquivalence, CategoryTheory.Functor.EssSurj, CategoryTheory.Skeleton, CategoryTheory.ThinSkeleton]
  E2: [CategoryTheory.Equivalence.mk, CategoryTheory.Equivalence.functor, CategoryTheory.Equivalence.inverse, CategoryTheory.Equivalence.unitIso, CategoryTheory.Equivalence.counitIso, CategoryTheory.Equivalence.functor_unitIso_comp, CategoryTheory.Equivalence.unit_inverse_comp, CategoryTheory.Equivalence.adjointifyη, CategoryTheory.Equivalence.symm, CategoryTheory.Equivalence.trans, CategoryTheory.Equivalence.fullyFaithfulFunctor, CategoryTheory.Functor.IsEquivalence.mk', CategoryTheory.Functor.asEquivalence, CategoryTheory.Functor.inv, CategoryTheory.Functor.essImage, CategoryTheory.Functor.objPreimage, CategoryTheory.Functor.objObjPreimageIso, CategoryTheory.Skeletal, CategoryTheory.skeletonEquivalence, CategoryTheory.skeleton_skeletal, CategoryTheory.ThinSkeleton.equivalence, CategoryTheory.Functor.isEquivalence_iff_isIso_of_skeletal]
  E1: auto
families: []
requires: [V24.C01, V04.C01, V07.C02, V07.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Equivalences of categories

### Overview

When are two categories the same? An isomorphism of categories is a functor with an inverse functor. This notion is too strict. The category of finite-dimensional vector spaces over a field $k$ and the category of natural numbers with matrices as morphisms describe the same linear algebra. But the first has a proper class of objects in each dimension, and the second has one, so no functor between them has an inverse.

An equivalence weakens "inverse" to "inverse up to natural isomorphism". The main theorem of the section says that a functor is an equivalence exactly when it is fully faithful and essentially surjective. The proof uses the axiom of choice. As a consequence, each category is equivalent to a skeleton, in which isomorphic objects are equal. For a preorder, the skeleton is the partial order of Volume 4, Chapter 1 obtained by identifying $a$ and $b$ when $a \le b \le a$.

Mathlib writes `C ≌ D` for the type of equivalences. Composition is in diagram order, as in all of Mathlib: `F ⋙ G` is the textbook $G \circ F$, as `f ≫ g` is $g \circ f$.

### Definitions

**Definition (Isomorphism of categories).** A functor $F : C \to D$ is an *isomorphism of categories* when there is a functor $G : D \to C$ with $G \circ F = 1_C$ and $F \circ G = 1_D$.

**Definition (Equivalence).** An *equivalence* between $C$ and $D$ consists of functors $F : C \to D$ and $G : D \to C$ and natural isomorphisms
$$\eta : 1_C \cong G \circ F, \qquad \varepsilon : F \circ G \cong 1_D.$$
Here $\eta$ is the *unit* and $\varepsilon$ the *counit*. The equivalence is *adjoint* when it satisfies the triangle law $\varepsilon_{F(X)} \circ F(\eta_X) = 1_{F(X)}$ for each $X$. A functor $F$ *is an equivalence* when it is part of an equivalence.

::: mathlib
`CategoryTheory.Equivalence` · `Mathlib.CategoryTheory.Equivalence`

`C ≌ D` is a structure with the fields `functor`, `inverse`, `unitIso : 𝟭 C ≅ functor ⋙ inverse`, `counitIso : inverse ⋙ functor ≅ 𝟭 D` and `functor_unitIso_comp`, the triangle law. So an equivalence of Mathlib is always adjoint. The other triangle law is the lemma `unit_inverse_comp`. The constructor `Equivalence.mk F G η ε` takes any unit and counit, with no law, and corrects the unit with `adjointifyη`. The operations `Equivalence.symm` and `Equivalence.trans` invert and compose.

<?decl CategoryTheory.Equivalence?>
:::

**Remark.** Each equivalence becomes adjoint after a change of the counit (Exercise 7) or of the unit, and then the second triangle law $G(\varepsilon_Y) \circ \eta_{G(Y)} = 1_{G(Y)}$ holds too. Chapter 5 explains this with adjunctions.

**Definition (Essentially surjective).** A functor $F : C \to D$ is *essentially surjective* when each object of $D$ is isomorphic to $F(X)$ for some $X$. The *essential image* of $F$ is the class of objects of $D$ isomorphic to some $F(X)$.

::: mathlib
`CategoryTheory.Functor.EssSurj` · `Mathlib.CategoryTheory.EssentialImage`

`F.EssSurj` is a class with the field `mem_essImage`: each object is in `F.essImage`, an `ObjectProperty D`. From the class, `F.objPreimage Y` chooses an object of `C` and `F.objObjPreimageIso Y : F.obj (F.objPreimage Y) ≅ Y` an isomorphism. These two definitions are noncomputable.

<?decl CategoryTheory.Functor.EssSurj?>
:::

**Definition (Skeleton).** A category is *skeletal* when isomorphic objects are equal. A *skeleton* of $C$ is a full subcategory that contains exactly one object of each isomorphism class.

### Theorems and proofs

**Lemma (Equivalences are fully faithful and essentially surjective).** Let $(F, G, \eta, \varepsilon)$ be an equivalence. Then $F$ and $G$ are fully faithful and essentially surjective.

*Proof.* Each $Y$ satisfies $Y \cong F(G(Y))$ by $\varepsilon_Y^{-1}$, so $F$ is essentially surjective. For $f : X \to X'$, naturality of $\eta$ gives $G(F(f)) \circ \eta_X = \eta_{X'} \circ f$, so
$$f = \eta_{X'}^{-1} \circ G(F(f)) \circ \eta_X.$$
So $F(f)$ determines $f$, and $F$ is faithful. The data $(G, F, \varepsilon^{-1}, \eta^{-1})$ form an equivalence too, so $G$ is faithful by the same argument. Now let $g : F(X) \to F(X')$ and set $f = \eta_{X'}^{-1} \circ G(g) \circ \eta_X$. The naturality of $\eta$ at $f$ gives $G(F(f)) = \eta_{X'} \circ f \circ \eta_X^{-1}$, and by the definition of $f$ this is $G(g)$. Since $G$ is faithful, $F(f) = g$. So $F$ is full. The claims for $G$ follow by symmetry. $\square$

**Theorem (Characterization of equivalences).** Assume the axiom of choice. A functor $F : C \to D$ is an equivalence if and only if it is fully faithful and essentially surjective.

*Proof.* The lemma gives one direction. Conversely, let $F$ be fully faithful and essentially surjective. For each object $Y$ of $D$, choose an object $G(Y)$ of $C$ and an isomorphism $\varepsilon_Y : F(G(Y)) \to Y$.

For $g : Y \to Y'$, let $G(g) : G(Y) \to G(Y')$ be the unique morphism with
$$F(G(g)) = \varepsilon_{Y'}^{-1} \circ g \circ \varepsilon_Y.$$
It exists and is unique since $F$ is fully faithful. The functor laws hold: $F(G(1_Y)) = 1 = F(1_{G(Y)})$, and $F(G(g') \circ G(g)) = \varepsilon_{Y''}^{-1} \circ g' \circ \varepsilon_{Y'} \circ \varepsilon_{Y'}^{-1} \circ g \circ \varepsilon_Y = F(G(g' \circ g))$. Faithfulness gives $G(1_Y) = 1$ and $G(g' \circ g) = G(g') \circ G(g)$. The defining equation reads $\varepsilon_{Y'} \circ F(G(g)) = g \circ \varepsilon_Y$, so $\varepsilon : F \circ G \Rightarrow 1_D$ is a natural isomorphism.

For each object $X$ of $C$, let $\eta_X : X \to G(F(X))$ be the unique morphism with $F(\eta_X) = \varepsilon_{F(X)}^{-1}$. Then $F(\eta_X)$ is an isomorphism, and a fully faithful functor reflects isomorphisms (Section 1), so $\eta_X$ is an isomorphism. For naturality, let $f : X \to X'$. Then
$$F(G(F(f)) \circ \eta_X) = \varepsilon_{F(X')}^{-1} \circ F(f) \circ \varepsilon_{F(X)} \circ \varepsilon_{F(X)}^{-1} = \varepsilon_{F(X')}^{-1} \circ F(f) = F(\eta_{X'} \circ f).$$
Faithfulness gives $G(F(f)) \circ \eta_X = \eta_{X'} \circ f$. So $(F, G, \eta, \varepsilon)$ is an equivalence. $\square$

The proof chooses $G(Y)$ and $\varepsilon_Y$ for all $Y$ at once. Without choice the converse can fail, so Mathlib keeps the chosen data visible.

::: mathlib
`CategoryTheory.Functor.IsEquivalence` · `Mathlib.CategoryTheory.Equivalence`

`F.IsEquivalence` is a class, a proposition, with the fields `faithful`, `full` and `essSurj`. So in Mathlib the characterization above is the definition. The constructor `Functor.IsEquivalence.mk'` builds an instance from an inverse, a unit and a counit. In the other direction, `F.asEquivalence : C ≌ D` and the inverse `F.inv` are built by choice, with `objPreimage` and `objObjPreimageIso`, as in the proof. `Equivalence.fullyFaithfulFunctor` gives the data of the lemma.

<?decl CategoryTheory.Functor.IsEquivalence?>
:::

**Theorem (Skeletons).** Assume the axiom of choice. Each category $C$ has a skeleton $S$, and the inclusion $S \to C$ is an equivalence. Two equivalent skeletal categories are isomorphic.

*Proof.* Choose one object in each isomorphism class, and let $S$ be the full subcategory on these objects. It is skeletal. The inclusion is fully faithful, since $S$ is full, and essentially surjective, since each object is isomorphic to the chosen one. The characterization makes it an equivalence.

Let $F : S \to S'$ be an equivalence of skeletal categories. If $F(X) = F(X')$, then $X \cong X'$, since $F$ is fully faithful and reflects isomorphisms, so $X = X'$. Each $Y$ is isomorphic to some $F(X)$, so $Y = F(X)$. So $F$ is bijective on objects. It is bijective on morphisms. Its inverse on objects and morphisms is a functor, since $F$ keeps identities and composites. $\square$

So two categories are equivalent if and only if their skeletons are isomorphic.

::: mathlib
`CategoryTheory.Skeleton` · `Mathlib.CategoryTheory.Skeletal`

`Skeleton C` is the quotient of the objects by the relation of isomorphism, with the morphisms of chosen representatives. `skeletonEquivalence C : Skeleton C ≌ C`, and `skeleton_skeletal` says it is skeletal. `Skeletal C` is the proposition that isomorphic objects are equal. `Functor.isEquivalence_iff_isIso_of_skeletal` is the second part of the theorem.

<?decl CategoryTheory.Skeleton?>
:::

### Examples

**Example (Matrices and vector spaces).** Let $k$ be a field. Let $\mathbf{Mat}_k$ have the natural numbers as objects and the $n \times m$ matrices as morphisms $m \to n$, with matrix product as composition. Define $F : \mathbf{Mat}_k \to \mathbf{FinVect}_k$ by $F(n) = k^n$ and $F(A) = (x \mapsto Ax)$. It is a functor, since $(AB)x = A(Bx)$. It is fully faithful, since each linear map $k^m \to k^n$ has exactly one matrix (Volume 7, Chapter 3). It is essentially surjective, since a space of dimension $n$ has a basis, and a basis is an isomorphism $k^n \cong V$ (Volume 7, Chapter 2). So $F$ is an equivalence. Its inverse chooses a basis of each space. $\mathbf{Mat}_k$ is a skeleton of $\mathbf{FinVect}_k$.

::: mathlib
`CategoryTheory.Mat` · `Mathlib.CategoryTheory.Preadditive.Mat`

`Mat R` has finite types as objects and matrices `Matrix X Y R` as morphisms `X ⟶ Y`, with `f ≫ g = f * g`. The diagram order matches the product of matrices that act on row vectors. The index of this edition has no declaration for the equivalence of `Mat R` with finite-dimensional modules.

<?decl CategoryTheory.Mat?>
:::

**Example (A preorder and its partial order).** Let $P$ be a preorder. Define $a \sim b$ when $a \le b$ and $b \le a$, and order $P/\!\sim$ by $[a] \le [b]$ when $a \le b$. The functor $P/\!\sim \to P$ that sends a class to a chosen element is fully faithful, since both categories are thin and the orders agree. It is essentially surjective, since $a \cong$ the chosen element of $[a]$. So it is an equivalence, and $P/\!\sim$ is a skeleton of $P$. It is an isomorphism only when $P$ is already a partial order.

::: mathlib
`CategoryTheory.ThinSkeleton` · `Mathlib.CategoryTheory.Skeletal`

For a thin category `C`, `ThinSkeleton C` is the quotient of the objects by isomorphism, with the partial order `ThinSkeleton.thinSkeletonPartialOrder`. `ThinSkeleton.equivalence C : ThinSkeleton C ≌ C` is the example above. For partial orders, `Equivalence.toOrderIso` turns an equivalence into an order isomorphism.

<?decl CategoryTheory.ThinSkeleton?>
:::

**Counterexample (Bijective on objects is not enough).** Let $C$ have two objects $0, 1$ and only identities, and $D$ the same objects with one isomorphism $0 \to 1$ and its inverse. The identity on objects is a functor $C \to D$. It is faithful and bijective on objects, but not full. It is not an equivalence, since $0 \cong 1$ in $D$ and not in $C$. Yet $D$ is equivalent to the category with one object and one morphism, which has fewer objects.

### The library around it

The file `Mathlib.CategoryTheory.Equivalence` has `Equivalence` and `Functor.IsEquivalence`. The two forms play two roles. Use `C ≌ D` when the inverse functor matters, and `F.IsEquivalence` for a property of a given functor. The file `Mathlib.CategoryTheory.EssentialImage` has the essential image, and `Mathlib.CategoryTheory.Skeletal` has skeletons. For an isomorphism of categories, `Cat.equivOfIso` gives an equivalence.

Common errors of a learner:

- The unit of `C ≌ D` is `unitIso : 𝟭 C ≅ functor ⋙ inverse`, and the counit goes the other way, `inverse ⋙ functor ≅ 𝟭 D`.
- `Equivalence.mk` changes the unit. The unit of `Equivalence.mk F G η ε` is not `η` in general.
- `F.inv` is noncomputable. Prefer an explicit inverse when there is one.

### Exercises

1. (A) Show that the composite of two equivalences is an equivalence, and that the relation "equivalent" is an equivalence relation.
2. (A) Show that an equivalence keeps and reflects monomorphisms and epimorphisms.
3. (A) Show that a category is equivalent to the one-point category if and only if it is nonempty and each $\mathrm{Hom}(X, Y)$ has exactly one element.
4. (B) Show that the category of finite sets with all maps is equivalent to the category with objects $\{1, \ldots, n\}$ for $n \ge 0$, and that the two are not isomorphic.
5. (B) Let $G$ be a group. Show that a groupoid in which any two objects are isomorphic and the automorphism group of one object is $G$ is equivalent to $BG$.
6. (B) Show that the opposite of the category of finite-dimensional vector spaces is equivalent to the category itself. Hint: the dual functor and the double dual of Section 2.
7. (C) Let $(F, G, \eta, \varepsilon)$ be an equivalence. Define $\varepsilon'_Y = \varepsilon_Y \circ F(\eta_{G(Y)}^{-1}) \circ \varepsilon_{F(G(Y))}^{-1}$. Show that $(F, G, \eta, \varepsilon')$ satisfies the triangle law $\varepsilon'_{F(X)} \circ F(\eta_X) = 1_{F(X)}$.

### Notes and history

Equivalences of categories appear in Grothendieck's Tohoku paper (1957) and became central with Grothendieck's school in algebraic geometry. The theorem on fully faithful and essentially surjective functors is in Mac Lane, *Categories for the Working Mathematician* (1971), Chapter 4, and in Riehl, *Category Theory in Context* (2016), Chapter 1. Skeletons are in both books.

### Reference

<?reference?>
