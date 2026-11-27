---
title: Isomorphisms, monomorphisms and epimorphisms
kind: theory
modules:
  - Mathlib.CategoryTheory.Iso
  - Mathlib.CategoryTheory.EpiMono
  - Mathlib.CategoryTheory.Groupoid
  - Mathlib.CategoryTheory.Balanced
explains:
  E3: [CategoryTheory.Iso, CategoryTheory.IsIso, CategoryTheory.Mono, CategoryTheory.Epi, CategoryTheory.SplitMono, CategoryTheory.Balanced]
  E2: [CategoryTheory.Iso.symm, CategoryTheory.Iso.trans, CategoryTheory.Iso.ext, CategoryTheory.asIso, CategoryTheory.inv, CategoryTheory.IsIso.mono_of_iso, CategoryTheory.IsIso.epi_of_iso, CategoryTheory.cancel_mono, CategoryTheory.cancel_epi, CategoryTheory.mono_comp, CategoryTheory.mono_of_mono, CategoryTheory.SplitEpi, CategoryTheory.IsSplitMono, CategoryTheory.IsSplitEpi, CategoryTheory.retraction, CategoryTheory.section_, CategoryTheory.isIso_of_epi_of_isSplitMono, CategoryTheory.op_mono_iff, CategoryTheory.op_epi_iff, CategoryTheory.Groupoid, CategoryTheory.IsGroupoid, CategoryTheory.isIso_of_mono_of_epi, CategoryTheory.mono_iff_injective, CategoryTheory.epi_iff_surjective, CategoryTheory.isIso_iff_bijective, CategoryTheory.isSplitEpi_iff_surjective, PartialOrder.isIso_iff_eq]
  E1: auto
families: []
requires: [V04.C01, V05.C02, V06.C01, V13.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Isomorphisms, monomorphisms and epimorphisms

### Overview

The objects of a category have no elements, so the words "bijective", "injective" and "surjective" have no direct meaning. An isomorphism is a morphism with a two-sided inverse. A monomorphism can be cancelled on the left of a composite, and an epimorphism on the right.

For sets and for groups these notions give back the bijections, injections and surjections. For rings and spaces they do not: the inclusion $\mathbb{Z} \to \mathbb{Q}$ is an epimorphism of rings, and a continuous bijection can fail to be an isomorphism.

Mathlib writes composition in diagram order: `f ≫ g` is the textbook $g \circ f$. So a monomorphism `f` cancels as in `g ≫ f = h ≫ f → g = h`.

### Definitions

**Definition (Isomorphism).** A morphism $f : X \to Y$ is an *isomorphism* when there is $g : Y \to X$ with $g \circ f = 1_X$ and $f \circ g = 1_Y$. Then $g$ is an *inverse* of $f$, and $X \cong Y$.

::: mathlib
`CategoryTheory.Iso` · `Mathlib.CategoryTheory.Iso`

A term of `X ≅ Y` is a structure with the data `hom : X ⟶ Y` and `inv : Y ⟶ X` and the proofs `hom_inv_id : hom ≫ inv = 𝟙 X` and `inv_hom_id : inv ≫ hom = 𝟙 Y`. So an isomorphism carries its inverse. `Iso.symm` swaps the two maps and `Iso.trans` composes. `Iso.ext` says two isomorphisms are equal when their `hom` fields are equal.

<?decl CategoryTheory.Iso?>
:::

::: mathlib
`CategoryTheory.IsIso` · `Mathlib.CategoryTheory.Iso`

`IsIso f` is a class and a proposition: an inverse exists. The inverse `inv f` is chosen from the proof, and `asIso f` gives a term of `X ≅ Y`.

<?decl CategoryTheory.IsIso?>
:::

**Definition (Groupoid).** A *groupoid* is a category in which each morphism is an isomorphism. A group is a groupoid with one object. In Mathlib, `Groupoid` is a class that extends `Category` with a field `inv` for each morphism, and `IsGroupoid` is the property version.

**Definition (Monomorphism and epimorphism).** A morphism $f : X \to Y$ is a *monomorphism* (or is *mono*) when $f \circ g = f \circ h$ implies $g = h$ for all $g, h : W \to X$. It is an *epimorphism* (or is *epi*) when $g \circ f = h \circ f$ implies $g = h$ for all $g, h : Y \to Z$.

::: mathlib
`CategoryTheory.Mono` · `Mathlib.CategoryTheory.Category.Basic`

`Mono f` is a class with one field `right_cancellation : g ≫ f = h ≫ f → g = h`, and `cancel_mono f` is the equivalence `g ≫ f = h ≫ f ↔ g = h`. The lemma `mono_comp` composes two monomorphisms.

<?decl CategoryTheory.Mono?>
:::

::: mathlib
`CategoryTheory.Epi` · `Mathlib.CategoryTheory.Category.Basic`

`Epi f` has the field `left_cancellation : f ≫ g = f ≫ h → g = h`, and `cancel_epi f` is the equivalence. The lemmas `op_mono_iff` and `op_epi_iff` give the duality.

<?decl CategoryTheory.Epi?>
:::

**Definition (Split monomorphism and split epimorphism).** A morphism $f : X \to Y$ is a *split monomorphism* when there is $r : Y \to X$ with $r \circ f = 1_X$. Then $r$ is a *retraction* of $f$. Dually, $f$ is a *split epimorphism* when there is $s : Y \to X$ with $f \circ s = 1_Y$, a *section* of $f$.

::: mathlib
`CategoryTheory.SplitMono` · `Mathlib.CategoryTheory.EpiMono`

`SplitMono f` is a structure with `retraction : Y ⟶ X` and `id : f ≫ retraction = 𝟙 X`. The class `IsSplitMono f` says one exists, and `retraction f` picks one. `SplitEpi`, `IsSplitEpi` and `section_` are the duals.

<?decl CategoryTheory.SplitMono?>
:::

**Definition (Balanced category).** A category is *balanced* when each morphism that is both mono and epi is an isomorphism.

::: mathlib
`CategoryTheory.Balanced` · `Mathlib.CategoryTheory.Balanced`

`Balanced C` is a class with one field, `isIso_of_mono_of_epi`.

<?decl CategoryTheory.Balanced?>
:::

### Theorems and proofs

**Proposition (Inverses).** Let $f : X \to Y$.

1. If $g$ and $g'$ are inverses of $f$, then $g = g'$.
2. If $f$ has a left inverse $g$ and a right inverse $g'$, then $g = g'$ and $f$ is an isomorphism.
3. Identities are isomorphisms, the inverse of an isomorphism is an isomorphism, and a composite of isomorphisms is an isomorphism.

*Proof.* For 2, $g \circ f = 1_X$ and $f \circ g' = 1_Y$ give $g = g \circ (f \circ g') = (g \circ f) \circ g' = g'$. Part 1 follows. For 3, $1_X$ is its own inverse, $f$ is an inverse of $f^{-1}$, and $f^{-1} \circ g^{-1}$ is an inverse of $g \circ f$, since $(f^{-1} \circ g^{-1}) \circ (g \circ f) = f^{-1} \circ 1 \circ f = 1_X$ and the other composite is the same with the roles reversed. $\square$

**Proposition (Rules for monomorphisms).** Let $f : X \to Y$ and $g : Y \to Z$.

1. Each split monomorphism is a monomorphism. In particular, each isomorphism is mono.
2. If $f$ and $g$ are mono, then $g \circ f$ is mono.
3. If $g \circ f$ is mono, then $f$ is mono.
4. If $f$ is a split monomorphism and an epimorphism, then $f$ is an isomorphism.

The dual rules hold for epimorphisms.

*Proof.* 1. Let $r \circ f = 1_X$. If $f \circ u = f \circ v$, then $u = r \circ f \circ u = r \circ f \circ v = v$.

2. If $g \circ f \circ u = g \circ f \circ v$, cancel $g$ and then $f$.

3. If $f \circ u = f \circ v$, then $g \circ f \circ u = g \circ f \circ v$, so $u = v$.

4. Let $r \circ f = 1_X$. Then $(f \circ r) \circ f = f \circ 1_X = 1_Y \circ f$. Since $f$ is epi, $f \circ r = 1_Y$. So $r$ is an inverse of $f$.

The dual rules are the rules for monomorphisms in the opposite category, since $f$ is epi in $C$ exactly when it is mono in $C^{\mathrm{op}}$. $\square$

Part 4 is `isIso_of_epi_of_isSplitMono` in Mathlib, and part 3 is `mono_of_mono`.

**Theorem (Sets).** In the category of sets, a function $f : X \to Y$ is mono if and only if it is injective, epi if and only if it is surjective, and an isomorphism if and only if it is bijective. Each surjection is a split epimorphism, and the category of sets is balanced.

*Proof.* Let $f$ be injective. If $f \circ u = f \circ v$, then $f(u(w)) = f(v(w))$ for each $w$, so $u = v$. Conversely, let $f$ be mono and $f(x) = f(x')$. Take $W = \{\ast\}$ with $u(\ast) = x$ and $v(\ast) = x'$. Then $f \circ u = f \circ v$, so $u = v$ and $x = x'$.

Let $f$ be surjective. If $u \circ f = v \circ f$ and $y = f(x)$, then $u(y) = v(y)$. Conversely, let $f$ be epi. Define $u, v : Y \to \{0, 1\}$ by $u(y) = 1$ for all $y$, and $v(y) = 1$ if $y \in f(X)$ and $v(y) = 0$ otherwise. Then $u \circ f = v \circ f$, so $u = v$ and $f(X) = Y$.

A bijection has an inverse function, and an isomorphism is mono and epi, so bijective. For a surjection $f$, the axiom of choice gives $s$ with $f(s(y)) = y$. $\square$

::: mathlib
`CategoryTheory.mono_iff_injective` · `Mathlib.CategoryTheory.Types.Basic`

For `f : X ⟶ Y` in `Type u`, the statement is `Mono f ↔ Function.Injective f`, with `f` coerced to a function. The file also has `epi_iff_surjective`, `isIso_iff_bijective` and `isSplitEpi_iff_surjective`.

<?decl CategoryTheory.mono_iff_injective?>
:::

### Examples

**Example (Groups).** A homomorphism of groups $f : G \to H$ is mono if and only if it is injective. If $f$ is injective, the proof for sets applies. Conversely, let $f$ be mono and $K = \ker f$. Let $i : K \to G$ be the inclusion and $e : K \to G$ the trivial homomorphism. Then $f \circ i = f \circ e$, since both are trivial. So $i = e$ and $K = \{1\}$, which makes $f$ injective (Volume 5, Chapter 2). Dually, an epimorphism of groups is surjective, with a harder proof. Mathlib proves it with two homomorphisms into the permutations of the set of left cosets of the image, with one point added.

::: mathlib
`GrpCat.epi_iff_surjective` · `Mathlib.Algebra.Category.Grp.EpiMono`

For `f : A ⟶ B` in `GrpCat`, the statement is `Epi f ↔ Function.Surjective f`. `GrpCat.mono_iff_injective` is the statement for monomorphisms.

<?decl GrpCat.epi_iff_surjective?>
:::

**Example (The integers in the rationals).** The inclusion $j : \mathbb{Z} \to \mathbb{Q}$ is an epimorphism of rings, and it is not surjective. Let $g, h : \mathbb{Q} \to R$ be ring homomorphisms with $g \circ j = h \circ j$. For $n \ne 0$, both $g(1/n)$ and $h(1/n)$ are inverses of $g(n) = h(n)$ in the monoid $(R, \cdot)$. Inverses in a monoid are unique, so $g(1/n) = h(1/n)$. Then $g(m/n) = g(m)\, g(1/n) = h(m)\, h(1/n) = h(m/n)$. So $g = h$. The map $j$ is injective, hence mono by the argument for sets. It is mono and epi but not an isomorphism, so the category of rings is not balanced.

::: mathlib
`IsLocalization.epi` · `Mathlib.Algebra.Category.Ring.Instances`

For each localization `S` of a commutative ring `R` at a submonoid `M`, the map `CommRingCat.ofHom (algebraMap R S)` is an epimorphism in `CommRingCat`. The map $\mathbb{Z} \to \mathbb{Q}$ is the localization at the nonzero integers. The statement is in `CommRingCat`, not `RingCat`.

<?decl IsLocalization.epi?>
:::

**Example (Topological spaces).** In the category of topological spaces, mono means injective and epi means surjective. The proof for sets applies, since maps from a point and maps to $\{0, 1\}$ with the indiscrete topology are continuous. Take $\{0, 1\}$ with the discrete topology on the source and the indiscrete one on the target. The identity function is continuous, mono and epi. Its inverse is not continuous (Volume 13, Chapter 1), so the category is not balanced. In Mathlib the two facts are `TopCat.mono_iff_injective` and `TopCat.epi_iff_surjective`.

**Example (Preorders).** In the category of a preorder, each morphism is mono and epi, since two parallel morphisms are equal. A morphism $a \to b$ is an isomorphism exactly when $b \le a$ too. In a partial order the only isomorphisms are the identities, which is `PartialOrder.isIso_iff_eq`. So a preorder with $a < b$ is not balanced.

**Counterexample (A monomorphism that does not split).** Let $f : \mathbb{Z} \to \mathbb{Z}$ be $f(n) = 2n$ in the category of abelian groups. It is injective, so it is mono. Suppose $r$ is a retraction. Then $1 = r(f(1)) = r(2) = 2 r(1)$, and $1$ is not even. So $f$ is not split. Dually, the quotient map $\mathbb{Z} \to \mathbb{Z}/2$ is epi and not split, since $\mathbb{Z}$ has no element of order $2$.

### The library around it

The file `Mathlib.CategoryTheory.Iso` has the API of `Iso` and `IsIso`, with `IsIso.mono_of_iso` and `IsIso.epi_of_iso`. The concrete facts are in the volumes of each structure, such as `ModuleCat.epi_iff_surjective` for modules. The index of this edition has no declaration for the fact that a continuous map with dense image is an epimorphism of Hausdorff spaces.

Common errors of a learner:

- `Mono f` cancels on the left in the textbook order $f \circ g$, which is on the right in `g ≫ f`. The field names `right_cancellation` and `left_cancellation` refer to the diagram order.
- `X ≅ Y` is data, and two terms with the same `hom` are equal by `Iso.ext`. `IsIso f` is a proposition, and `inv f` is chosen from it.
- A morphism that is mono and epi need not be an isomorphism, as rings, spaces and preorders show.

### Exercises

1. (A) Show that if $g \circ f$ is an isomorphism and $g$ is mono, then $f$ is an isomorphism. Hint: find a left inverse of $f$ first.
2. (A) Show that in a groupoid each morphism is mono and epi, and that the groupoid is balanced.
3. (A) Show that a morphism that is both a split epimorphism and a monomorphism is an isomorphism.
4. (B) Show that in the category of modules over a ring, a monomorphism is an injective linear map. Hint: use the kernel, as for groups (Volume 7, Chapter 1).
5. (B) Show that the inclusion $\mathbb{Z} \to \mathbb{Z}_{(p)}$ into the rationals with denominator prime to $p$ is an epimorphism of rings.
6. (B) In the category of Hausdorff spaces, show that the inclusion $\mathbb{Q} \to \mathbb{R}$ is an epimorphism. Hint: two continuous maps to a Hausdorff space that agree on a dense set are equal.
7. (C) Show that $f : X \to Y$ is an isomorphism if and only if, for each object $W$, the map $\mathrm{Hom}(W, X) \to \mathrm{Hom}(W, Y)$, $u \mapsto f \circ u$, is a bijection. Hint: for the converse, take $W = Y$ and find $g$ with $f \circ g = 1_Y$, then take $W = X$.

### Notes and history

Isomorphisms were part of the first paper of Eilenberg and Mac Lane (1945), where natural isomorphisms are the main subject. Monomorphisms and epimorphisms became standard tools with Grothendieck's Tohoku paper (1957). Mac Lane, *Categories for the Working Mathematician* (1971), Chapter 1, and Riehl, *Category Theory in Context* (2016), Chapter 1, treat the notions of this section.

### Reference

<?reference?>
