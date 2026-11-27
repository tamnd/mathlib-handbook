---
title: Categories and examples
kind: theory
modules:
  - Mathlib.Combinatorics.Quiver.Basic
  - Mathlib.CategoryTheory.Category.Basic
  - Mathlib.CategoryTheory.Category.Preorder
  - Mathlib.CategoryTheory.SingleObj
  - Mathlib.CategoryTheory.Discrete.Basic
  - Mathlib.CategoryTheory.Opposites
  - Mathlib.CategoryTheory.Products.Basic
  - Mathlib.CategoryTheory.Types.Basic
  - Mathlib.Order.Category.Preord
  - Mathlib.Order.Category.PartOrd
explains:
  E3: [CategoryTheory.Category, CategoryTheory.CategoryStruct, Preorder.smallCategory, CategoryTheory.SingleObj, CategoryTheory.Category.opposite]
  E2: [Quiver, Quiver.IsThin, CategoryTheory.Category.assoc, CategoryTheory.Category.id_comp, CategoryTheory.Category.comp_id, CategoryTheory.LargeCategory, CategoryTheory.SmallCategory, CategoryTheory.homOfLE, CategoryTheory.leOfHom, CategoryTheory.SingleObj.comp_as_mul, CategoryTheory.Discrete, CategoryTheory.discreteCategory, CategoryTheory.op_comp, CategoryTheory.prod', CategoryTheory.types, CategoryTheory.types_comp, TypeCat.Hom, Preord, PartOrd]
  E1: auto
families: []
requires: [V04.C01, V05.C01, V05.C02, V06.C01, V07.C01, V13.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Categories and examples

### Overview

Groups come with homomorphisms, rings with ring homomorphisms, modules with linear maps, and topological spaces with continuous maps. In each case the maps compose, the composition is associative, and each object has an identity map. A category keeps only these facts. It forgets what the objects are made of and records how the maps compose.

This section states the axioms and gives the first examples. Some are small: a preorder is a category with at most one morphism between two objects, and a monoid is a category with one object. The section also builds opposite and product categories.

Mathlib writes composition in diagram order. The composite `f ≫ g` means "first `f`, then `g`". It is the textbook $g \circ f$.

### Definitions

**Definition (Category).** A *category* $C$ consists of:

1. a class $\mathrm{Ob}(C)$ of *objects*;
2. for each pair of objects $X, Y$, a set $\mathrm{Hom}(X, Y)$ of *morphisms* from $X$ to $Y$;
3. for each object $X$, an *identity* $1_X \in \mathrm{Hom}(X, X)$;
4. for each triple $X, Y, Z$, a *composition* $\mathrm{Hom}(X, Y) \times \mathrm{Hom}(Y, Z) \to \mathrm{Hom}(X, Z)$, written $(f, g) \mapsto g \circ f$.

These data satisfy two axioms. The *unit laws* say $1_Y \circ f = f$ and $f \circ 1_X = f$ for each $f : X \to Y$. The *associative law* says $h \circ (g \circ f) = (h \circ g) \circ f$ for all composable $f, g, h$.

A morphism $f \in \mathrm{Hom}(X, Y)$ is written $f : X \to Y$. Its *source* is $X$ and its *target* is $Y$. Two morphisms compose only when the target of the first is the source of the second.

::: mathlib
`CategoryTheory.CategoryStruct` · `Mathlib.CategoryTheory.Category.Basic`

A `Quiver V` gives a type `X ⟶ Y` of arrows for each pair of vertices, with no composition. The class `CategoryStruct obj` extends `Quiver obj` with the fields `id` and `comp`, written `𝟙 X` and `f ≫ g`. It has no axioms.

<?decl CategoryTheory.CategoryStruct?>
:::

::: mathlib
`CategoryTheory.Category` · `Mathlib.CategoryTheory.Category.Basic`

`Category.{v, u} C` extends `CategoryStruct` with the axioms `id_comp : 𝟙 X ≫ f = f`, `comp_id : f ≫ 𝟙 Y = f` and `assoc : (f ≫ g) ≫ h = f ≫ (g ≫ h)`. The objects live in `Type u` and each `X ⟶ Y` in `Type v`. Each axiom has the default proof `by cat_disch`.

<?decl CategoryTheory.Category?>
:::

**Definition (Small and large categories).** A category is *small* when its objects and its morphisms form sets, and *locally small* when each $\mathrm{Hom}(X, Y)$ is a set. The category of all sets is locally small but not small.

Mathlib uses universe levels in place of "set" and "class". A `SmallCategory C` is a `Category.{u} C` with `C : Type u`. A `LargeCategory C` is a `Category.{u} C` with `C : Type (u+1)`, so the objects live one universe higher than the morphisms.

**Definition (Thin category).** A category is *thin* when each $\mathrm{Hom}(X, Y)$ has at most one element. In a thin category each diagram of morphisms commutes, since two parallel morphisms are equal. Mathlib states this as `Quiver.IsThin C`, which asks that each type `X ⟶ Y` be a subsingleton.

### Theorems and proofs

**Proposition (General associativity).** Let $f_1, \ldots, f_n$ be morphisms with the target of $f_i$ equal to the source of $f_{i+1}$. All ways to put brackets in the composite $f_n \circ \cdots \circ f_1$ give the same morphism.

*Proof.* Use induction on $n$; for $n \le 2$ there is one bracketing. Let $R_n = f_n \circ (f_{n-1} \circ (\cdots \circ f_1))$. A bracketing is $B \circ A$, with $A$ a bracketing of $f_k, \ldots, f_1$ and $B$ one of $f_n, \ldots, f_{k+1}$, for some $1 \le k < n$. By induction, $A$ and $B$ are equal to their right normal forms. If $B$ is the single morphism $f_n$, then $B \circ A = f_n \circ R_{n-1} = R_n$. Otherwise $B = f_n \circ B'$, with $B'$ the right normal form of $f_{n-1}, \ldots, f_{k+1}$. The associative law gives $B \circ A = (f_n \circ B') \circ A = f_n \circ (B' \circ A)$. The bracketing $B' \circ A$ has $n - 1$ factors, so it equals $R_{n-1}$ by induction. So $B \circ A = f_n \circ R_{n-1} = R_n$. $\square$

The simp lemma `Category.assoc` moves brackets to the right, as in this proof.

**Proposition (Preorders are thin categories).** Let $(P, \le)$ be a preorder. Define a category with object set $P$, with $\mathrm{Hom}(a, b)$ a one-point set if $a \le b$ and the empty set otherwise. This is a thin category. Conversely, a thin category $C$ gives a preorder on its objects, with $a \le b$ when $\mathrm{Hom}(a, b)$ is not empty.

*Proof.* Reflexivity of $\le$ gives the identities, and transitivity gives the composition. The axioms are equalities between morphisms in sets with at most one element, so they hold. Conversely, the identity $1_a$ shows $a \le a$, and the composite of $a \to b$ and $b \to c$ shows $a \le c$. $\square$

The two constructions are inverse to each other up to the names of the morphisms. So a thin category is the same as a preorder (Volume 4, Chapter 1).

::: mathlib
`Preorder.smallCategory` · `Mathlib.CategoryTheory.Category.Preorder`

Each preorder is a small category with `U ⟶ V` equal to `ULift (PLift (U ≤ V))`, which moves the proposition into a type. The functions `homOfLE` and `leOfHom` go between `x ≤ y` and `x ⟶ y`. The instance has priority 100, so a more specific instance wins.

<?decl Preorder.smallCategory?>
:::

**Proposition (Monoids are one-object categories).** Let $M$ be a monoid. Define a category $BM$ with one object $\star$, with $\mathrm{Hom}(\star, \star) = M$, with $1_\star = 1$ and with $g \circ f = gf$. This is a category. Conversely, if $C$ is a category with one object $\star$, then $\mathrm{Hom}(\star, \star)$ is a monoid under composition.

*Proof.* The unit laws of $BM$ are $1 f = f = f 1$, and the associative law is $(hg)f = h(gf)$. Conversely, the axioms of the category are the axioms of a monoid with product $g \circ f$ and unit $1_\star$. $\square$

A group gives a one-object category in which each morphism has an inverse (Volume 5, Chapter 1).

::: mathlib
`CategoryTheory.SingleObj` · `Mathlib.CategoryTheory.SingleObj`

`SingleObj M` has one object, `SingleObj.star M`, and `star M ⟶ star M` is `M`. The lemma `SingleObj.comp_as_mul` says `f ≫ g = g * f`: the factors flip, to match the textbook $g \circ f = gf$.

<?decl CategoryTheory.SingleObj?>
:::

**Definition (Opposite category).** The *opposite* $C^{\mathrm{op}}$ of a category $C$ has the same objects. Its morphisms are $\mathrm{Hom}_{C^{\mathrm{op}}}(X, Y) = \mathrm{Hom}_C(Y, X)$, and its composition is $g \circ_{\mathrm{op}} f = f \circ g$.

The unit laws and the associative law of $C^{\mathrm{op}}$ are those of $C$ read backwards, so $C^{\mathrm{op}}$ is a category, and $(C^{\mathrm{op}})^{\mathrm{op}} = C$. Each statement about all categories thus has a *dual* statement, with all arrows reversed, and the dual statement holds too.

::: mathlib
`CategoryTheory.Category.opposite` · `Mathlib.CategoryTheory.Opposites`

The objects of `Cᵒᵖ` form the type `Opposite C` of Volume 1, with `op` and `unop`. A morphism `X ⟶ Y` in `Cᵒᵖ` is a morphism `unop Y ⟶ unop X` in `C`, and `f.op` is the image of `f`. The lemma `op_comp` says `(f ≫ g).op = g.op ≫ f.op`. Since `Cᵒᵖ` is a new type, an object of `C` is never taken for an object of `Cᵒᵖ`.

<?decl CategoryTheory.Category.opposite?>
:::

**Definition (Product category).** The *product* $C \times D$ of two categories has the pairs $(X, Y)$ as objects. A morphism $(X, Y) \to (X', Y')$ is a pair $(f, g)$ with $f : X \to X'$ in $C$ and $g : Y \to Y'$ in $D$. Identities and composition are taken in each factor.

The axioms hold in each component. In Mathlib the instance is `CategoryTheory.prod'`.

### Examples

**Example (Types and sets).** The category $\mathbf{Set}$ has sets as objects and functions as morphisms, with the usual composition. In Mathlib the instance `types` gives `Category.{u} (Type u)`. A morphism `X ⟶ Y` is a term of the structure `TypeCat.Hom X Y`, which wraps a function. The function is `ConcreteCategory.hom f`, and `TypeCat.ofHom g` turns a function into a morphism. The lemma `types_comp` says that the function of `f ≫ g` is that of `g` composed with that of `f`.

**Example (Concrete categories of algebra and topology).** The category $\mathbf{Grp}$ of groups has group homomorphisms as morphisms. The categories $\mathbf{Ring}$ of rings, $\mathbf{Mod}_R$ of modules over a ring $R$ and $\mathbf{Top}$ of topological spaces have ring homomorphisms, linear maps and continuous maps. Composites of such maps are maps of the same kind (Volume 5, Chapter 2; Volume 6, Chapter 1; Volume 7, Chapter 1; Volume 13, Chapter 1), and the axioms hold for the underlying functions.

::: mathlib
`GrpCat` · `Mathlib.Algebra.Category.Grp.Basic`

An object of `GrpCat` bundles a type `carrier` with a group instance, and `GrpCat.of G` builds one. A morphism wraps a homomorphism `G →* H`. `RingCat`, `ModuleCat R` and `TopCat` follow the same pattern.

<?decl GrpCat?>
:::

**Example (Preorders and partial orders as a category).** The preorders with monotone maps form a category $\mathbf{Preord}$, and the partial orders a category $\mathbf{PartOrd}$. A preorder is thus both one object of $\mathbf{Preord}$ and a category. Chapter 2 shows that the morphisms at the first level are the functors at the second.

::: mathlib
`Preord` · `Mathlib.Order.Category.Preord`

An object of `Preord` is built with `Preord.of α`, and a morphism wraps an order homomorphism `α →o β`. `PartOrd` is the same for partial orders.

<?decl Preord?>
:::

**Example (Discrete categories).** Let $S$ be a set. The *discrete category* on $S$ has the elements of $S$ as objects, and its only morphisms are the identities. It is the thin category of the equality relation on $S$. In Mathlib, `Discrete α` wraps a term `as : α`, and in the instance `discreteCategory α` the type `X ⟶ Y` is a lift of `X.as = Y.as`.

**Counterexample (A failure of associativity).** Take one object $\star$ and the morphisms $\mathbb{Z}$, with $g \circ f = g - f$ and $1_\star = 0$. Then $f \circ 0 = f$, but $0 \circ f = -f$, and $(h - g) - f \ne h - (g - f)$ in general. So the data fail both the unit laws and the associative law.

### The library around it

The file `Mathlib.CategoryTheory.Category.Basic` has the classes, the notation and the cancellation lemmas. The notation `𝟙` and `≫` is scoped, so a file needs `open CategoryTheory`. A category on a type is a class, found by instance search. The type synonyms `Discrete`, `SingleObj` and `Opposite` give a type one fixed category structure, so two structures on one type never compete. The definition `uliftCategory` moves a category to a higher universe.

Common errors of a learner:

- `f ≫ g` is "first `f`, then `g`". The textbook $g \circ f$ is `f ≫ g`, and in `SingleObj M` it is `g * f`.
- `Category.{v, u} C` has the level of morphisms first. A wrong order gives universe errors.
- A morphism in `Type u` is a term of `TypeCat.Hom X Y`, not a function. Use `ConcreteCategory.hom f` or the coercion, and `TypeCat.ofHom` back.
- In a preorder, `x ⟶ y` is not the proposition `x ≤ y`. Use `homOfLE` and `leOfHom`.

### Exercises

1. (A) Show that the composite $f_4 \circ f_3 \circ f_2 \circ f_1$ has five bracketings, and check by hand with the associative law that the five composites are equal.
2. (A) Let $C$ be a category with one object $\star$ in which each morphism has an inverse. Show that $\mathrm{Hom}(\star, \star)$ is a group. Hint: the inverse of a morphism is unique, by the argument for inverses in a monoid.
3. (A) Show that a thin category $C$ in which $a \to b$ and $b \to a$ imply $a = b$ gives a partial order on its objects.
4. (B) Show that $(C \times D)^{\mathrm{op}}$ and $C^{\mathrm{op}} \times D^{\mathrm{op}}$ have the same objects, the same morphisms and the same composition.
5. (B) Let $M$ be a monoid. Define the *opposite monoid* $M^{\mathrm{op}}$ with the product $a \cdot_{\mathrm{op}} b = ba$. Show that $(BM)^{\mathrm{op}}$ is the category $B(M^{\mathrm{op}})$.
6. (B) Let $C$ be the category with natural numbers as objects and $n \times m$ real matrices as morphisms $m \to n$. Check the unit laws and the associative law. Which objects $n$ have a morphism $0 \to n$, and how many?
7. (C) Let $S$ be a set of morphisms in a category $C$. Show that there is a smallest subcategory of $C$ that contains $S$, and describe its morphisms as composites of elements of $S$ and identities. Hint: use general associativity.

### Notes and history

Eilenberg and Mac Lane defined categories, functors and natural transformations in "General theory of natural equivalences" (1945). Their aim was to make precise the word "natural" in algebraic topology. Categories were at first a language for functors. Grothendieck's Tohoku paper (1957) made categories a working tool in homological algebra. The standard texts are Mac Lane, *Categories for the Working Mathematician* (1971), and Riehl, *Category Theory in Context* (2016).

### Reference

<?reference?>
