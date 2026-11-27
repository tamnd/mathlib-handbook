---
title: Presentable and accessible categories
kind: theory
modules:
  - Mathlib.CategoryTheory.Presentable.IsCardinalFiltered
  - Mathlib.CategoryTheory.Presentable.Basic
  - Mathlib.CategoryTheory.Presentable.Finite
  - Mathlib.CategoryTheory.Presentable.CardinalFilteredPresentation
  - Mathlib.CategoryTheory.Presentable.LocallyPresentable
  - Mathlib.CategoryTheory.Presentable.StrongGenerator
  - Mathlib.CategoryTheory.Presentable.Type
  - Mathlib.CategoryTheory.Presentable.Presheaf
explains:
  E3: [CategoryTheory.IsCardinalFiltered, CategoryTheory.isCardinalFiltered_iff, CategoryTheory.IsCardinalPresentable, CategoryTheory.IsFinitelyPresentable, CategoryTheory.IsCardinalLocallyPresentable, CategoryTheory.IsLocallyPresentable, CategoryTheory.IsCardinalLocallyPresentable.iff_exists_isStrongGenerator, CategoryTheory.Types.isCardinalPresentable_iff]
  E2: [CategoryTheory.isCardinalFiltered_aleph0_iff, CategoryTheory.isFiltered_of_isCardinalFiltered, CategoryTheory.IsCardinalFiltered.of_le, CategoryTheory.isCardinalFiltered_preorder, CategoryTheory.isCardinalFiltered_of_hasTerminal, CategoryTheory.isCardinalFiltered_under, CategoryTheory.IsCardinalFiltered.max, CategoryTheory.IsCardinalFiltered.coeq, CategoryTheory.Functor.IsCardinalAccessible, CategoryTheory.Functor.IsAccessible, CategoryTheory.IsPresentable, CategoryTheory.isCardinalPresentable_of_le, CategoryTheory.isCardinalPresentable_monotone, CategoryTheory.IsCardinalPresentable.exists_hom_of_isColimit, CategoryTheory.IsCardinalPresentable.exists_eq_of_isColimit, CategoryTheory.HasCardinalFilteredColimits, CategoryTheory.Functor.IsFinitelyAccessible, CategoryTheory.isFinitelyPresentable_iff_preservesFilteredColimits, CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator, CategoryTheory.HasCardinalFilteredGenerator, CategoryTheory.HasCardinalFilteredGenerator.exists_small_generator, CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator.isStrongGenerator, CategoryTheory.IsCardinalAccessibleCategory, CategoryTheory.IsLocallyFinitelyPresentable, CategoryTheory.IsFinitelyAccessibleCategory, CategoryTheory.IsAccessibleCategory, CategoryTheory.instIsAccessibleCategoryOfIsLocallyPresentable, CategoryTheory.instIsPresentableOfIsAccessibleCategory, CategoryTheory.Types.isStrongGenerator_punit, CategoryTheory.Types.instIsCardinalLocallyPresentableType, CategoryTheory.Types.instIsLocallyPresentableType, CategoryTheory.Presheaf.isStrongGenerator, CategoryTheory.Presheaf.instIsCardinalLocallyPresentableFunctorOppositeOfHasPullbacks]
  E1: auto
families: []
requires: [V04, V24.C03, V24.C04, V24.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Presentable and accessible categories

### Overview

Many categories in algebra are large, but each object in them is built from small pieces in a controlled way. A set is the union of its finite subsets. A module is the filtered colimit of its finitely presented modules. A presheaf on a small category is a colimit of representable presheaves. A locally presentable category is a cocomplete category with a small set of objects that are "small" in a precise sense, such that each object is a highly filtered colimit of these objects.

The notion of size uses a regular cardinal $\kappa$. An object $X$ is $\kappa$-presentable if the functor $\mathrm{Hom}(X, -)$ preserves colimits over $\kappa$-filtered categories. For $\kappa = \aleph_0$ this is the notion of a finitely presentable object, or a compact object. This section defines $\kappa$-filtered categories, $\kappa$-presentable objects, and locally presentable and accessible categories. It proves that a set is $\kappa$-presentable if and only if it has fewer than $\kappa$ elements, and that the categories of sets and of presheaves of sets are locally presentable.

In the text $g \circ f$ is the textbook composite, and Mathlib writes `f ≫ g`. Filtered categories and filtered colimits of sets are in Volume 24, Chapter 4.

### Definitions

**Definition (Regular cardinal).** An infinite cardinal $\kappa$ is regular if a union of fewer than $\kappa$ sets, each with fewer than $\kappa$ elements, has fewer than $\kappa$ elements. The cardinal $\aleph_0$ is regular, because a finite union of finite sets is finite. Each infinite successor cardinal is regular. For a type $X$, the statement `HasCardinalLT X κ` says that $X$ has fewer than $\kappa$ elements.

In the rest of the section, $\kappa$ is a regular cardinal. Mathlib gives this hypothesis as the instance argument `[Fact κ.IsRegular]`.

**Definition ($\kappa$-filtered category).** A category $J$ is $\kappa$-filtered if each functor $F : A \to J$ has a cocone, where $A$ is a small category with fewer than $\kappa$ morphisms.

For a small $A$ with fewer than $\kappa$ morphisms, $A$ also has fewer than $\kappa$ objects, because the identity morphisms are distinct. The empty category has no morphisms, so a $\kappa$-filtered category is not empty.

**Definition (Accessible functor).** A functor $G : C \to D$ is $\kappa$-accessible if it preserves the colimits of the functors $J \to C$ for each small $\kappa$-filtered category $J$. It is accessible if it is $\kappa$-accessible for some regular cardinal $\kappa$.

**Definition ($\kappa$-presentable object).** An object $X$ of $C$ is $\kappa$-presentable if the functor $\mathrm{Hom}(X, -) : C \to \mathbf{Set}$ is $\kappa$-accessible. It is finitely presentable if it is $\aleph_0$-presentable. It is presentable if it is $\kappa$-presentable for some regular cardinal $\kappa$.

**Definition ($\kappa$-filtered generator).** Let $P$ be a property of the objects of $C$. Then $P$ is a $\kappa$-filtered generator if each object with $P$ is $\kappa$-presentable, and each object of $C$ is the colimit of a functor $J \to C$ with values in $P$, where $J$ is a small $\kappa$-filtered category.

**Definition (Locally presentable category).** A locally small category $C$ is locally $\kappa$-presentable if it has all small colimits and it has an essentially small $\kappa$-filtered generator. It is $\kappa$-accessible if it has colimits over each small $\kappa$-filtered category and it has an essentially small $\kappa$-filtered generator. It is locally presentable, or accessible, if this is true for some regular cardinal $\kappa$. For $\kappa = \aleph_0$ the names are locally finitely presentable and finitely accessible.

::: mathlib
`CategoryTheory.IsCardinalFiltered` · `Mathlib.CategoryTheory.Presentable.IsCardinalFiltered`

The class `IsCardinalFiltered J κ` has one field, `nonempty_cocone`. It gives a cocone for each functor `F : A ⥤ J` with `A` a small category in the universe `w` of the cardinal and `HasCardinalLT (Arrow A) κ`. The functions `IsCardinalFiltered.max` and `IsCardinalFiltered.coeq` give an upper bound of a small family of objects and a morphism that makes a small family of parallel morphisms equal.

<?decl CategoryTheory.IsCardinalFiltered?>
:::

### Theorems and proofs

The first theorem replaces the definition by two conditions on families of objects and of morphisms, as for filtered categories.

**Theorem (The two conditions).** A category $J$ is $\kappa$-filtered if and only if these two conditions are true.

1. For each family $(j_i)_{i \in I}$ of objects with $|I| < \kappa$, there is an object $k$ with a morphism $j_i \to k$ for each $i$.
2. For each family $(f_i : j \to k)_{i \in I}$ of parallel morphisms with $|I| < \kappa$, there are morphisms $a : k \to l$ and $b : j \to l$ with $a \circ f_i = b$ for each $i$.

*Proof.* Suppose that $J$ is $\kappa$-filtered. For condition 1, let $A$ be the discrete category on $I$. Its morphisms are the identities, so it has $|I| < \kappa$ morphisms. A cocone on the functor $i \mapsto j_i$ is an object $k$ with morphisms $j_i \to k$. For condition 2, let $A$ be the category with two objects $0$ and $1$, the identities, and one morphism $0 \to 1$ for each $i \in I$. It has $|I| + 2$ morphisms, and $|I| + 2 < \kappa$ because $\kappa$ is infinite. The family $(f_i)$ gives a functor $A \to J$. A cocone on this functor is an object $l$ with $b : j \to l$ and $a : k \to l$, and the naturality condition is $a \circ f_i = b$.

Suppose that conditions 1 and 2 are true, and let $F : A \to J$ be a functor, where $A$ has fewer than $\kappa$ morphisms. Then $A$ has fewer than $\kappa$ objects. By condition 1, there is an object $k$ with morphisms $g_x : F(x) \to k$ for each object $x$ of $A$. For each morphism $u : x \to y$ of $A$, the morphisms $g_x$ and $g_y \circ F(u)$ go from $F(x)$ to $k$, and they need not be equal. By condition 2 for this pair, there is a morphism $e_u : k \to l_u$ with $e_u \circ g_x = e_u \circ g_y \circ F(u)$. By condition 1 for the family $(l_u)$, which has fewer than $\kappa$ members, there is an object $m$ with morphisms $h_u : l_u \to m$. The morphisms $h_u \circ e_u : k \to m$ are a family of fewer than $\kappa$ parallel morphisms. By condition 2, there are $a : m \to n$ and $b : k \to n$ with $a \circ h_u \circ e_u = b$ for each $u$. Put $c_x = b \circ g_x : F(x) \to n$. For $u : x \to y$,

$$c_y \circ F(u) = a \circ h_u \circ e_u \circ g_y \circ F(u) = a \circ h_u \circ e_u \circ g_x = c_x.$$

So the morphisms $c_x$ are a cocone on $F$ with vertex $n$. $\square$

**Corollary (Finite case).** A category is $\aleph_0$-filtered if and only if it is filtered.

*Proof.* A filtered category is not empty, each pair of objects has an upper bound and each pair of parallel morphisms is made equal by a morphism. An induction on the number of members gives conditions 1 and 2 for nonempty finite families. For the empty family of objects, any object is an upper bound, and an object exists because $J$ is not empty. For an empty family of morphisms $j \to k$, take an upper bound $l$ of $j$ and $k$, with $b : j \to l$ and $a : k \to l$. There is no equation to satisfy. Conversely, conditions 1 and 2 for families with at most two members are the axioms of a filtered category. $\square$

**Proposition (Change of cardinal).** If $\kappa \le \kappa'$, then each $\kappa'$-filtered category is $\kappa$-filtered, and each $\kappa$-presentable object is $\kappa'$-presentable.

*Proof.* A category with fewer than $\kappa$ morphisms has fewer than $\kappa'$ morphisms. This gives the first statement. So a $\kappa'$-filtered category $J$ is $\kappa$-filtered, and $\mathrm{Hom}(X, -)$ preserves the colimits over $J$ when $X$ is $\kappa$-presentable. $\square$

The next theorem gives the practical meaning of presentability. The colimit of sets is the filtered colimit of Volume 24, Chapter 4: an element of $\mathrm{colim}_j S_j$ is the class of an element of some $S_j$, and two elements $s \in S_i$ and $s' \in S_{i'}$ have the same class if and only if they become equal in some $S_j$.

**Theorem (Factorization through a stage).** Let $X$ be $\kappa$-presentable and let $c$ be a colimit cocone on $F : J \to C$, where $J$ is $\kappa$-filtered and essentially small.

1. Each morphism $f : X \to c$ is $\iota_j \circ f'$ for some $j$ and some $f' : X \to F(j)$.
2. If $\iota_{i} \circ f_1 = \iota_{i'} \circ f_2$ for $f_1 : X \to F(i)$ and $f_2 : X \to F(i')$, then there are $u : i \to j$ and $v : i' \to j$ with $F(u) \circ f_1 = F(v) \circ f_2$.

*Proof.* The functor $\mathrm{Hom}(X, -)$ preserves the colimit, so $\mathrm{Hom}(X, c)$ is the colimit of the sets $\mathrm{Hom}(X, F(j))$, with the maps $f' \mapsto \iota_j \circ f'$. A $\kappa$-filtered category is filtered by the corollary and the change of cardinal. Statement 1 says that each element of the colimit of sets is the class of an element of some stage. Statement 2 is the description of equality in a filtered colimit of sets. $\square$

**Theorem (Presentable sets).** A set $X$ is $\kappa$-presentable in $\mathbf{Set}$ if and only if $|X| < \kappa$.

*Proof.* Suppose that $|X| < \kappa$. Let $c$ be a colimit cocone on $F : J \to \mathbf{Set}$, where $J$ is $\kappa$-filtered. It is necessary to show that the map $\Phi : \mathrm{colim}_j \mathrm{Hom}(X, F(j)) \to \mathrm{Hom}(X, c)$ is bijective.

For surjectivity, let $f : X \to c$. For each $x \in X$, choose $j_x$ and $y_x \in F(j_x)$ with $\iota_{j_x}(y_x) = f(x)$. By condition 1, there is $k$ with morphisms $t_x : j_x \to k$. Put $g(x) = F(t_x)(y_x)$. Then $\iota_k(g(x)) = \iota_{j_x}(y_x) = f(x)$, so $f = \Phi[g]$.

For injectivity, it is enough to take two maps $g, g' : X \to F(j)$ at the same stage with $\iota_j \circ g = \iota_j \circ g'$, because $J$ is filtered. For each $x$, the elements $g(x)$ and $g'(x)$ have the same class, so there is $u_x : j \to k_x$ with $F(u_x)(g(x)) = F(u_x)(g'(x))$. By condition 1, there are morphisms $h_x : k_x \to m$. By condition 2 for the family $(h_x \circ u_x)$, there are $a : m \to n$ and $b : j \to n$ with $a \circ h_x \circ u_x = b$ for each $x$. Then $F(b)(g(x)) = F(a \circ h_x) F(u_x)(g(x)) = F(a \circ h_x) F(u_x)(g'(x)) = F(b)(g'(x))$. So $F(b) \circ g = F(b) \circ g'$, and $[g] = [g']$.

Conversely, suppose that $X$ is $\kappa$-presentable. Let $S$ be the set of the subsets of $X$ with fewer than $\kappa$ elements, ordered by inclusion. A family of fewer than $\kappa$ members of $S$ has its union as an upper bound, and the union is in $S$ because $\kappa$ is regular. So $S$ is $\kappa$-filtered. The set $X$ is the colimit of the inclusions $A \to X$ for $A \in S$, because each element $x$ is in $\{x\}$, and if $x \in A$ and $x \in B$, then the two copies of $x$ become equal in $A \cup B$. By the factorization theorem, $1_X$ factors through some $A \in S$. So $A = X$, and $|X| < \kappa$. $\square$

In particular, the finitely presentable sets are the finite sets. The set $\mathbb{N}$ is not finitely presentable, but it is $\aleph_1$-presentable.

A strong generator of $C$ is a property $P$ of objects with two properties. First, two morphisms $f, g : Y \to Z$ are equal if $f \circ t = g \circ t$ for each $t : G \to Y$ with $G$ in $P$. Second, a monomorphism $i : Y \to Z$ is an isomorphism if each morphism $G \to Z$ with $G$ in $P$ factors through $i$. Mathlib proves the next criterion.

**Theorem (Criterion by a strong generator).** Let $C$ be a locally small category with all small colimits. Then $C$ is locally $\kappa$-presentable if and only if it has a strong generator $P$ that is a small set of $\kappa$-presentable objects.

*Proof (outline).* If $C$ is locally $\kappa$-presentable, Mathlib shows that a small $\kappa$-filtered generator is a strong generator. For the converse, let $\overline{P}$ be the closure of $P$ under the colimits of diagrams with fewer than $\kappa$ morphisms. The objects of $\overline{P}$ are $\kappa$-presentable, and $\overline{P}$ is essentially small. For each object $X$, the category of the morphisms $G \to X$ with $G$ in $\overline{P}$ is $\kappa$-filtered, because $\overline{P}$ is closed under the colimits of diagrams with fewer than $\kappa$ morphisms. Mathlib then uses the strong generator property to show that $X$ is the colimit of the canonical diagram on this category. $\square$

**Theorem (Sets and presheaves).** For each regular cardinal $\kappa$, the category $\mathbf{Set}$ is locally $\kappa$-presentable. For a small category $C$, the category of presheaves of sets on $C$ is locally $\kappa$-presentable.

*Proof.* The category $\mathbf{Set}$ has all small colimits. The one-point set $1$ is a strong generator. Two maps $f, g : Y \to Z$ with $f \circ t = g \circ t$ for each point $t : 1 \to Y$ are equal. If $i : Y \to Z$ is a monomorphism and each point of $Z$ factors through $i$, then $i$ is injective and surjective, so it is an isomorphism. The set $1$ is $\kappa$-presentable by the theorem on presentable sets. The criterion gives the first statement.

For presheaves, colimits exist and are computed objectwise. The representable presheaf $yX = \mathrm{Hom}(-, X)$ is $\kappa$-presentable, because $\mathrm{Hom}(yX, P) \cong P(X)$ by the Yoneda lemma (Volume 24, Chapter 3), and evaluation at $X$ preserves colimits. The representable presheaves are a strong generator. If $f \circ t = g \circ t$ for each $t : yX \to P$, then $f$ and $g$ agree on each element of each $P(X)$, so $f = g$. If $i : P \to Q$ is a monomorphism and each $t : yX \to Q$ factors through $i$, then each $i_X$ is injective and surjective, so $i$ is an isomorphism. The objects $X$ of $C$ are a small set, and the criterion gives the second statement. $\square$

### Examples

**Example ($\omega$ as a filtered category).** The ordered set $\mathbb{N}$ is filtered, so it is $\aleph_0$-filtered. It is not $\aleph_1$-filtered, because the countable family of all its elements has no upper bound. The well-ordered set of the ordinals less than $\kappa$ is $\kappa$-filtered, because a set of fewer than $\kappa$ such ordinals has a supremum less than $\kappa$, since $\kappa$ is regular.

**Example (Terminal objects).** A category with a terminal object $t$ is $\kappa$-filtered for each $\kappa$. For each functor $F$, the unique morphisms $F(x) \to t$ are a cocone, and the naturality equations are true because all morphisms to $t$ are equal.

**Example (Under categories).** If $J$ is $\kappa$-filtered and $j_0$ is an object of $J$, then the category of the morphisms $j_0 \to j$ is $\kappa$-filtered. Mathlib gives this as an instance.

**Example (Modules and rings).** A module over a ring is finitely presentable in the category of modules if and only if it is finitely presented. In the category of commutative rings, the finitely presentable objects are the rings of finite presentation over $\mathbb{Z}$. The lemma `CommRingCat.isFinitelyPresentable_hom` in `Mathlib.Algebra.Category.Ring.FinitePresentation` proves one direction for the under category of a ring $R$: a morphism $R \to S$ of finite presentation is a finitely presentable object. For modules, the index of this edition has no declaration for the statement above.

**Counterexample (Topological spaces).** The category of topological spaces has all small colimits, but it is not locally presentable. The book of Adámek and Rosický shows that no set of presentable spaces generates all spaces by filtered colimits. The index of this edition has no declaration for this statement.

**Example (The universe of the cardinal).** For $C$ with morphisms in `Type v`, the statement `IsFinitelyPresentable.{v} X` is equivalent to the statement that `coyoneda.obj (op X)` preserves filtered colimits. The universe parameter fixes the size of the index categories.

### The library around it

::: mathlib
`CategoryTheory.IsCardinalPresentable` · `Mathlib.CategoryTheory.Presentable.Basic`

The definition `IsCardinalPresentable X κ` is the statement `(coyoneda.obj (op X)).IsCardinalAccessible κ`. The class `Functor.IsCardinalAccessible` gives `PreservesColimitsOfShape J F` for each small `κ`-filtered `J`. The lemmas `IsCardinalPresentable.exists_hom_of_isColimit` and `IsCardinalPresentable.exists_eq_of_isColimit` are the two parts of the factorization theorem.

<?decl CategoryTheory.IsCardinalPresentable?>
:::

::: mathlib
`CategoryTheory.IsCardinalLocallyPresentable` · `Mathlib.CategoryTheory.Presentable.LocallyPresentable`

The class extends `HasCardinalFilteredGenerator C κ` and `HasColimitsOfSize.{w, w} C`. The class `IsCardinalAccessibleCategory C κ` replaces the second parent by `HasCardinalFilteredColimits C κ`. The classes `IsLocallyPresentable` and `IsAccessibleCategory` state that a suitable regular cardinal exists. Instances give that a locally presentable category is accessible, and that each object of an accessible category is presentable.

<?decl CategoryTheory.IsCardinalLocallyPresentable?>
:::

::: mathlib
`CategoryTheory.IsCardinalLocallyPresentable.iff_exists_isStrongGenerator` · `Mathlib.CategoryTheory.Presentable.StrongGenerator`

For `C` with `HasColimitsOfSize.{w, w} C` and `LocallySmall.{w} C`, the category is locally `κ`-presentable if and only if there is a `w`-small `P : ObjectProperty C` with `P.IsStrongGenerator` and `P ≤ isCardinalPresentable C κ`. The property `ObjectProperty.IsStrongGenerator` is in `Mathlib.CategoryTheory.Generator.StrongGenerator`.

<?decl CategoryTheory.IsCardinalLocallyPresentable.iff_exists_isStrongGenerator?>
:::

::: mathlib
`CategoryTheory.Types.isCardinalPresentable_iff` · `Mathlib.CategoryTheory.Presentable.Type`

For `X : Type u` and `κ : Cardinal.{u}`, the statement is `IsCardinalPresentable X κ ↔ HasCardinalLT X κ`. The same file proves `Types.isStrongGenerator_punit` and gives the instances `IsCardinalLocallyPresentable (Type u) κ` and `IsLocallyPresentable.{u} (Type u)`. The file `Presentable.Presheaf` gives the instance for `Cᵒᵖ ⥤ A` when `A` is locally `κ`-presentable and has pullbacks.

<?decl CategoryTheory.Types.isCardinalPresentable_iff?>
:::

The lemma `isCardinalFiltered_iff` is the theorem on the two conditions, and `isCardinalFiltered_aleph0_iff` is the finite case. The lemma `isCardinalFiltered_preorder` gives the $\kappa$-filtered property of an ordered set from upper bounds of small families. The abbreviation `IsFinitelyPresentable X` is `IsCardinalPresentable X ℵ₀`, and `isFinitelyPresentable_iff_preservesFilteredColimits` relates it to `PreservesFilteredColimits`.

Common errors of a learner:

- Each definition needs the instance `[Fact κ.IsRegular]`. For $\aleph_0$, the instance is `Cardinal.fact_isRegular_aleph0`.
- The cardinal `κ : Cardinal.{w}` fixes the universe `w` of the index categories. A mismatch of `w` with the universe of the morphisms of `C` blocks the instances for `Type u`, which need `κ : Cardinal.{u}`.
- A locally presentable category has all small colimits, but an accessible category has only the $\kappa$-filtered colimits. The two classes are different.
- `HasCardinalLT X κ` compares the cardinal of `X` with `κ` after a universe lift. For `X` and `κ` in the same universe, `hasCardinalLT_iff_cardinal_mk_lt` gives `Cardinal.mk X < κ`.

### Exercises

1. (A) Show that each $\kappa$-filtered category is filtered. *Hint:* use the change of cardinal and the finite case.
2. (A) Show that an object isomorphic to a $\kappa$-presentable object is $\kappa$-presentable.
3. (A) Show that the empty set and each finite set are finitely presentable in $\mathbf{Set}$, and that $\mathbb{N}$ is not.
4. (B) Show that a retract of a $\kappa$-presentable object is $\kappa$-presentable. *Hint:* a retract of a bijection of sets is a bijection.
5. (B) Show that a coproduct of two finitely presentable objects is finitely presentable. *Hint:* $\mathrm{Hom}(X \sqcup Y, -) \cong \mathrm{Hom}(X, -) \times \mathrm{Hom}(Y, -)$, and finite products commute with filtered colimits of sets.
6. (B) Let $X$ be a set. Show that the ordered set of the finite subsets of $X$ is filtered, and that $X$ is its colimit in $\mathbf{Set}$.
7. (C) Show that in $\mathbf{Set}$, colimits over a $\kappa$-filtered category commute with limits of diagrams with fewer than $\kappa$ morphisms. *Hint:* follow the proof of the theorem on presentable sets, and use the regularity of $\kappa$ to bound the number of choices.

### Notes and history

Locally presentable categories are due to Gabriel and Ulmer, *Lokal präsentierbare Kategorien*, Lecture Notes in Mathematics 221 (1971). Accessible categories are in the book of Makkai and Paré, *Accessible categories* (1989). The standard reference, which the source files follow, is the book of Adámek and Rosický, *Locally presentable and accessible categories* (1994). Locally presentable categories have the adjoint functor theorem in a simple form, and the small object argument of Chapter 3 works in each of them.

The Mathlib Authors line of `Presentable.IsCardinalFiltered`, `Presentable.Basic`, `Presentable.CardinalFilteredPresentation`, `Presentable.LocallyPresentable`, `Presentable.StrongGenerator`, `Presentable.Type` and `Presentable.Presheaf` names Joël Riou. The file `Presentable.Finite` is by Andrew Yang.

### Reference

<?reference?>
