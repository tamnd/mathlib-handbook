---
title: Representable functors
kind: theory
modules:
  - Mathlib.CategoryTheory.Elements
  - Mathlib.CategoryTheory.Limits.Elements
explains:
  E3: [CategoryTheory.Functor.RepresentableBy, CategoryTheory.Functor.IsRepresentable, CategoryTheory.Functor.CorepresentableBy, CategoryTheory.Functor.RepresentableBy.uniqueUpToIso, CategoryTheory.Functor.Elements]
  E2: [CategoryTheory.Functor.RepresentableBy.homEquiv, CategoryTheory.Functor.RepresentableBy.homEquiv_comp, CategoryTheory.Functor.RepresentableBy.toIso, CategoryTheory.Functor.RepresentableBy.ofIso, CategoryTheory.Functor.representableByEquiv, CategoryTheory.Functor.reprX, CategoryTheory.Functor.reprx, CategoryTheory.Functor.reprW, CategoryTheory.Functor.IsCorepresentable, CategoryTheory.Functor.coreprX, CategoryTheory.Functor.CorepresentableBy.uniqueUpToIso, CategoryTheory.instIsCorepresentableIdType, CategoryTheory.Functor.Elements.π, CategoryTheory.Functor.elementsMk, CategoryTheory.Functor.Elements.initialOfCorepresentableBy, CategoryTheory.Functor.Elements.isInitialOfCorepresentableBy, CategoryTheory.Functor.Elements.hasInitial_iff_isCorepresentable, CategoryTheory.Functor.Elements.hasInitial_iff_isRepresentable]
  E1: auto
families: []
requires: [V24.C01, V24.C02, V05.C02, V06.C05, V08.C02, V13.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Representable functors

### Overview

Many functors to sets are functors of morphisms in disguise. The underlying set of a group $G$ is the set of homomorphisms $\mathbb{Z} \to G$. The power set of a set $X$ is the set of maps $X \to \{0, 1\}$. The open sets of a space are the continuous maps to the Sierpinski space. A functor isomorphic to $\mathrm{Hom}(-, X)$ or $\mathrm{Hom}(X, -)$ is *representable*, and $X$ is its representing object.

By the Yoneda lemma, a representation is the same as one element of $F(X)$ with a universal property. This section proves this, shows that the representing object is unique up to a unique isomorphism, and recasts a representation as an initial object of the category of elements. Many constructions of the later chapters, such as limits and adjoints, are representing objects of suitable functors.

Mathlib composes in diagram order: `f ≫ g` is the textbook $g \circ f$. So the naturality of a representation reads `homEquiv (f ≫ g) = F.map f.op (homEquiv g)`.

### Definitions

**Definition (Representable functor).** A functor $F : C^{\mathrm{op}} \to \mathbf{Set}$ is *representable* when there is an object $X$ and a natural isomorphism $\theta : h_X \cong F$. The pair $(X, \theta)$ is a *representation* of $F$. Dually, $F : C \to \mathbf{Set}$ is *corepresentable* when $F \cong h^X$ for some $X$.

**Definition (Universal element).** Let $F : C^{\mathrm{op}} \to \mathbf{Set}$. An element $x \in F(X)$ is *universal* when for each object $W$ and each $w \in F(W)$ there is a unique $u : W \to X$ with $F(u)(x) = w$. For a covariant $F : C \to \mathbf{Set}$, an element $x \in F(X)$ is universal when for each $z \in F(Z)$ there is a unique $v : X \to Z$ with $F(v)(x) = z$.

::: mathlib
`CategoryTheory.Functor.RepresentableBy` · `Mathlib.CategoryTheory.Yoneda`

For `F : Cᵒᵖ ⥤ Type v` and `Y : C`, the structure `F.RepresentableBy Y` holds a bijection `homEquiv : (X ⟶ Y) ≃ F.obj (op X)` for each `X` and the naturality law `homEquiv_comp`. It is data, a representation with a chosen object. `RepresentableBy.toIso` gives `yoneda.obj Y ≅ F`, and `representableByEquiv` is the bijection between the two forms. `RepresentableBy.ofIso` moves a representation along `F ≅ F'`.

<?decl CategoryTheory.Functor.RepresentableBy?>
:::

::: mathlib
`CategoryTheory.Functor.IsRepresentable` · `Mathlib.CategoryTheory.Yoneda`

`F.IsRepresentable` is a class, a proposition: some `F.RepresentableBy Y` exists. From it, `F.reprX` chooses the representing object, `F.reprx : F.obj (op F.reprX)` the universal element, and `F.reprW` the natural isomorphism. All three are noncomputable.

<?decl CategoryTheory.Functor.IsRepresentable?>
:::

::: mathlib
`CategoryTheory.Functor.CorepresentableBy` · `Mathlib.CategoryTheory.Yoneda`

The covariant form, for `F : C ⥤ Type v`: a bijection `homEquiv : (X ⟶ Y) ≃ F.obj Y`, natural in `Y`. `F.IsCorepresentable` and `F.coreprX` are the class and the chosen object. The instance `instIsCorepresentableIdType` says the identity functor of `Type` is corepresentable, by a one-point type.

<?decl CategoryTheory.Functor.CorepresentableBy?>
:::

**Definition (Category of elements).** Let $F : C \to \mathbf{Set}$. The *category of elements* $\int F$ has the pairs $(X, x)$ with $x \in F(X)$ as objects. A morphism $(X, x) \to (X', x')$ is a morphism $f : X \to X'$ with $F(f)(x) = x'$. Composition is that of $C$. The projection $(X, x) \mapsto X$ is a functor $\int F \to C$.

The composite of $f : (X, x) \to (X', x')$ and $f' : (X', x') \to (X'', x'')$ is a morphism of $\int F$, since $F(f' \circ f)(x) = F(f')(F(f)(x)) = x''$.

::: mathlib
`CategoryTheory.Functor.Elements` · `Mathlib.CategoryTheory.Elements`

For `F : C ⥤ Type w`, `F.Elements` is a structure with an object `obj` and a value `val : F.obj obj`. A morphism is a structure with `hom : x.obj ⟶ y.obj` and the law `map_val : F.map hom x.val = y.val`. `F.elementsMk X x` builds an element, and `Elements.π F : F.Elements ⥤ C` is the projection. The older namespace `CategoryTheory.CategoryOfElements` is deprecated in this edition.

<?decl CategoryTheory.Functor.Elements?>
:::

### Theorems and proofs

**Theorem (Representations and universal elements).** Let $F : C^{\mathrm{op}} \to \mathbf{Set}$ and $X$ an object. The Yoneda bijection $\theta \mapsto \theta_X(1_X)$ restricts to a bijection between the natural isomorphisms $h_X \cong F$ and the universal elements of $F(X)$.

*Proof.* Let $x \in F(X)$ and let $\theta = \Psi(x)$ be the transformation of the Yoneda lemma, with $\theta_W(u) = F(u)(x)$. It is the unique transformation with $\theta_X(1_X) = x$. By the theorem on componentwise isomorphisms (Chapter 2, Section 2), $\theta$ is a natural isomorphism exactly when each $\theta_W : \mathrm{Hom}(W, X) \to F(W)$ is a bijection. That says: for each $w \in F(W)$ there is a unique $u$ with $F(u)(x) = w$. This is the definition of a universal element. $\square$

**Theorem (Uniqueness of representations).** Let $x \in F(X)$ and $x' \in F(X')$ be universal elements of $F : C^{\mathrm{op}} \to \mathbf{Set}$. There is a unique morphism $\varphi : X' \to X$ with $F(\varphi)(x) = x'$, and it is an isomorphism.

*Proof.* By universality of $x$, there is a unique $\varphi : X' \to X$ with $F(\varphi)(x) = x'$. By universality of $x'$, there is a unique $\psi : X \to X'$ with $F(\psi)(x') = x$. Then $F(\varphi \circ \psi)(x) = F(\psi)(F(\varphi)(x)) = F(\psi)(x') = x$. Since also $F(1_X)(x) = x$, the uniqueness part of universality of $x$ gives $\varphi \circ \psi = 1_X$. In the same way $\psi \circ \varphi = 1_{X'}$. $\square$

So a representing object is unique up to a unique isomorphism that respects the universal elements. Without the elements the isomorphism is not unique: an object $X$ represents $h_X$ through each automorphism of $X$.

::: mathlib
`CategoryTheory.Functor.RepresentableBy.uniqueUpToIso` · `Mathlib.CategoryTheory.Yoneda`

For `e : F.RepresentableBy Y` and `e' : F.RepresentableBy Y'`, the isomorphism `Y ≅ Y'` of the theorem. Its proof in Mathlib goes through the Yoneda embedding: `yoneda.obj Y ≅ F ≅ yoneda.obj Y'`, and full faithfulness gives `Y ≅ Y'`. `CorepresentableBy.uniqueUpToIso` is the covariant form.

<?decl CategoryTheory.Functor.RepresentableBy.uniqueUpToIso?>
:::

**Theorem (Representations as initial objects).** Let $F : C \to \mathbf{Set}$. An element $x \in F(X)$ is universal if and only if $(X, x)$ is an initial object of $\int F$, that is, each object of $\int F$ receives exactly one morphism from $(X, x)$. So $F$ is corepresentable if and only if $\int F$ has an initial object.

*Proof.* A morphism $(X, x) \to (Z, z)$ in $\int F$ is a morphism $v : X \to Z$ with $F(v)(x) = z$. So "exactly one morphism to each $(Z, z)$" is the definition of a universal element of the covariant $F$. The second claim follows from the covariant form of the theorem on universal elements. $\square$

The uniqueness theorem is then the uniqueness of initial objects up to unique isomorphism, a fact of Chapter 4.

::: mathlib
`CategoryTheory.Functor.Elements.hasInitial_iff_isCorepresentable` · `Mathlib.CategoryTheory.Limits.Elements`

For `F : C ⥤ Type w`, the statement `HasInitial F.Elements ↔ F.IsCorepresentable`. The file `Mathlib.CategoryTheory.Elements` has the explicit forms: `Elements.initialOfCorepresentableBy` is the element of a representation, and `Elements.isInitialOfCorepresentableBy` proves it initial. For a presheaf `F : Cᵒᵖ ⥤ Type w`, `Elements.hasInitial_iff_isRepresentable` uses the elements of `F` as a functor on `Cᵒᵖ`, so its morphisms go the other way.

<?decl CategoryTheory.Functor.Elements.hasInitial_iff_isCorepresentable?>
:::

### Examples

**Example (The underlying set of a group).** The forgetful functor $U : \mathbf{Grp} \to \mathbf{Set}$ is corepresented by $\mathbb{Z}$ with the universal element $1 \in \mathbb{Z}$. For each group $G$ and $g \in G$, there is a unique homomorphism $v : \mathbb{Z} \to G$ with $v(1) = g$, namely $v(n) = g^n$ (Volume 5, Chapter 2). In the same way the forgetful functor of abelian groups is corepresented by $\mathbb{Z}$, and that of monoids by $\mathbb{N}$.

::: mathlib
`GrpCat.forget_isCorepresentable` · `Mathlib.Algebra.Category.Grp.ForgetCorepresentable`

The instance `(forget GrpCat).IsCorepresentable`. The same file has `CommGrpCat.forget_isCorepresentable`, and the file `Mathlib.Algebra.Category.MonCat.ForgetCorepresentable` has `MonCat.forget_isCorepresentable`.

<?decl GrpCat.forget_isCorepresentable?>
:::

**Example (The underlying set of a ring).** The forgetful functor from commutative rings to sets is corepresented by the polynomial ring $\mathbb{Z}[t]$ with the universal element $t$. For each ring $R$ and $r \in R$, evaluation at $r$ is the unique ring homomorphism $\mathbb{Z}[t] \to R$ with $t \mapsto r$ (Volume 6, Chapter 5). The index of this edition has no declaration for this corepresentability as an instance of `IsCorepresentable`. In Mathlib the universal property is `Polynomial.eval₂RingHom` with the uniqueness lemma `Polynomial.ringHom_ext`.

**Example (The power set).** The contravariant power set functor $\mathcal{P} : \mathbf{Set}^{\mathrm{op}} \to \mathbf{Set}$, with $f \mapsto f^{-1}$, is represented by $2 = \{0, 1\}$ with the universal element $\{1\} \in \mathcal{P}(2)$. For each set $W$ and $A \subseteq W$, the characteristic function $\chi_A : W \to 2$ is the unique map with $\chi_A^{-1}(\{1\}) = A$.

**Example (Open sets).** Let $\mathbb{S}$ be the Sierpinski space: the set $\{0, 1\}$ with the open sets $\emptyset$, $\{1\}$ and $\{0, 1\}$. The functor $\mathbf{Top}^{\mathrm{op}} \to \mathbf{Set}$ that sends a space to its set of open subsets, and a continuous map to its preimage map, is represented by $\mathbb{S}$ with the universal element $\{1\}$. A map $\chi : W \to \mathbb{S}$ is continuous exactly when $\chi^{-1}(\{1\})$ is open, and then $\chi$ is the characteristic function of this open set (Volume 13, Chapter 1).

**Counterexample (The covariant power set).** The covariant power set functor $\mathcal{P} : \mathbf{Set} \to \mathbf{Set}$, with $f \mapsto (A \mapsto f(A))$, is not corepresentable. Suppose $\mathcal{P} \cong h^A$. Then $\mathrm{Hom}(A, \emptyset)$ is in bijection with $\mathcal{P}(\emptyset)$, which has one element. So $A = \emptyset$. Then $\mathrm{Hom}(A, \{\ast\})$ has one element, but $\mathcal{P}(\{\ast\})$ has two, a contradiction.

### The library around it

The representable functors are in `Mathlib.CategoryTheory.Yoneda`, and the categories of elements in `Mathlib.CategoryTheory.Elements`. The data `RepresentableBy` is the form used by the constructions: an adjunction gives `Adjunction.corepresentableBy` (Chapter 5), and limits and colimits relate to representations through `Limits.IsLimit` and `Limits.IsColimit` (Chapter 4). The equivalence `Elements.costructuredArrowYonedaEquivalence` compares the elements of a presheaf with a category of arrows into it.

Common errors of a learner:

- `RepresentableBy` is for presheaves `Cᵒᵖ ⥤ Type v`, and `CorepresentableBy` for functors `C ⥤ Type v`. The forgetful functor of groups is corepresentable, not representable.
- `F.reprX` is a chosen object and is not computable. To compute, keep a term of `F.RepresentableBy Y`.
- `F.Elements` is defined for covariant functors. The elements of a presheaf are the elements of a functor on `Cᵒᵖ`, and the direction of the morphisms flips.

### Exercises

1. (A) Show that the identity functor of $\mathbf{Set}$ is corepresented by a one-point set, and name the universal element.
2. (A) Show that $X \mapsto X \times X$ is corepresented by a two-point set, and $X \mapsto X^n$ by an $n$-point set.
3. (A) Show that the functor $G \mapsto \{g \in G : g^n = 1\}$ on groups is corepresented by $\mathbb{Z}/n$.
4. (B) Show that the functor $\mathbf{Set}^{\mathrm{op}} \to \mathbf{Set}$ that sends $X$ to the set of equivalence relations on $X$ is not representable. Hint: look at a one-point set and a two-point set.
5. (B) Let $k$ be a field and $V, W$ vector spaces. Show that the functor $U \mapsto \{\text{bilinear maps } V \times W \to U\}$ is corepresented by $V \otimes_k W$, and deduce the uniqueness of the tensor product (Volume 8, Chapter 2).
6. (B) Let $F$ be represented by $(X, x)$ and let $\varphi$ be an automorphism of $X$. Show that $F(\varphi)(x)$ is universal too, and that each universal element of $F(X)$ has this form.
7. (C) Let $G$ be a group and $F : BG \to \mathbf{Set}$ a $G$-set. Describe $\int F$, and show that $F$ is corepresentable if and only if the action is free and transitive.

### Notes and history

Universal elements and representable functors go back to the work of Grothendieck in algebraic geometry in the late 1950s, where a moduli problem is solved by a representing object. Mac Lane, *Categories for the Working Mathematician* (1971), Chapter 3, and Riehl, *Category Theory in Context* (2016), Chapter 2, treat representability, universal elements and the category of elements.

### Reference

<?reference?>
