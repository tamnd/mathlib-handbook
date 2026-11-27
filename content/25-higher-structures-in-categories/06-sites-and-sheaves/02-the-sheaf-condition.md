---
title: The sheaf condition
kind: theory
modules:
  - Mathlib.CategoryTheory.Sites.IsSheafFor
  - Mathlib.CategoryTheory.Sites.SheafOfTypes
  - Mathlib.CategoryTheory.Sites.EqualizerSheafCondition
  - Mathlib.CategoryTheory.Sites.Sheaf
  - Mathlib.CategoryTheory.Sites.Canonical
  - Mathlib.CategoryTheory.Sites.Subcanonical
explains:
  E3: [CategoryTheory.Presieve.FamilyOfElements, CategoryTheory.Presieve.FamilyOfElements.Compatible, CategoryTheory.Presieve.FamilyOfElements.IsAmalgamation, CategoryTheory.Presieve.IsSheafFor, CategoryTheory.Presieve.IsSheaf, CategoryTheory.Presieve.isSheafFor_iff_generate, CategoryTheory.Presieve.isSheaf_pretopology, CategoryTheory.Equalizer.Presieve.sheaf_condition, CategoryTheory.Presheaf.IsSheaf, CategoryTheory.Sheaf, CategoryTheory.Sheaf.canonicalTopology, CategoryTheory.GrothendieckTopology.Subcanonical]
  E2: [CategoryTheory.Presieve.FamilyOfElements.SieveCompatible, CategoryTheory.Presieve.compatible_iff_sieveCompatible, CategoryTheory.Presieve.IsSeparatedFor, CategoryTheory.Presieve.isSheafFor_subsieve, CategoryTheory.Presieve.isSheafFor_subsieve_aux, CategoryTheory.Presieve.pullbackCompatible_iff, CategoryTheory.Presieve.YonedaSheafCondition, CategoryTheory.Presieve.isSheafFor_iff_yonedaSheafCondition, CategoryTheory.Presieve.isSheafFor_trans, CategoryTheory.Presieve.isSheafFor_top, CategoryTheory.Presieve.isSheafFor_iso, CategoryTheory.Presieve.IsSeparated, CategoryTheory.Presieve.isSheaf_bot, CategoryTheory.Presieve.isSheaf_of_le, CategoryTheory.Equalizer.Sieve.equalizer_sheaf_condition, CategoryTheory.Equalizer.Presieve.Arrows.sheaf_condition, CategoryTheory.sheafToPresheaf, CategoryTheory.fullyFaithfulSheafToPresheaf, CategoryTheory.Presheaf.isSheaf_iff_isLimit, CategoryTheory.isSheaf_iff_isSheaf_of_type, CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget, CategoryTheory.sheafBotEquivalence, CategoryTheory.Sheaf.isTerminalOfBotCover, CategoryTheory.Sheaf.finestTopologySingle, CategoryTheory.Sheaf.finestTopology, CategoryTheory.Sheaf.le_finestTopology, CategoryTheory.Sheaf.isSheaf_yoneda_obj, CategoryTheory.GrothendieckTopology.yoneda, CategoryTheory.GrothendieckTopology.yonedaFullyFaithful, CategoryTheory.GrothendieckTopology.yonedaEquiv]
  E1: auto
families: []
requires: [V13, V24.C03, V24.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The sheaf condition

### Overview

A presheaf assigns a set to each object and a restriction map to each morphism. A sheaf is a presheaf in which local data that agree on overlaps glue to a unique global datum. On a topological space this is the familiar property of continuous functions: functions on the members of an open cover that agree on the intersections come from exactly one function on the union.

This section states the condition for a presieve on an object of any category, then for a Grothendieck topology. It proves that a presieve and the sieve it generates give the same condition, it gives the equalizer form of the condition, and it proves that a pretopology needs a check only on its covering families. The case of an open set covered by two open sets is worked in detail. At the end, the canonical topology is the largest topology for which each representable presheaf is a sheaf.

In the text $g \circ f$ is the textbook composite, and Mathlib writes `f ≫ g`. For a presheaf $P : C^{op} \to \mathbf{Set}$, a morphism $f : Y \to X$ and $s \in P(X)$, the *restriction* of $s$ along $f$ is $s|_f = P(f)(s) \in P(Y)$. Then $(s|_f)|_g = s|_{f \circ g}$ and $s|_{1_X} = s$.

### Definitions

Let $P : C^{op} \to \mathbf{Set}$ be a presheaf, let $X$ be an object and let $R$ be a presieve on $X$.

**Definition (Family of elements).** A *family of elements* of $P$ for $R$ is a choice of an element $x_f \in P(Y)$ for each $f : Y \to X$ in $R$.

**Definition (Compatible family).** A family $x$ is *compatible* if for all $f_1 : Y_1 \to X$ and $f_2 : Y_2 \to X$ in $R$ and all $g_1 : Z \to Y_1$ and $g_2 : Z \to Y_2$ with $f_1 \circ g_1 = f_2 \circ g_2$, the equality $x_{f_1}|_{g_1} = x_{f_2}|_{g_2}$ holds.

**Definition (Amalgamation).** An *amalgamation* of a family $x$ is an element $t \in P(X)$ with $t|_f = x_f$ for each $f$ in $R$.

**Definition (Sheaf for a presieve).** The presheaf $P$ is *separated for* $R$ if each family for $R$ has at most one amalgamation. It is a *sheaf for* $R$ if each compatible family for $R$ has exactly one amalgamation.

An amalgamation $t$ makes the family compatible, because $x_{f_1}|_{g_1} = t|_{f_1 \circ g_1} = t|_{f_2 \circ g_2} = x_{f_2}|_{g_2}$. So the condition "compatible" is necessary for the existence of an amalgamation.

**Definition (Sheaf on a site).** Let $J$ be a Grothendieck topology on $C$. The presheaf $P$ is a *sheaf* for $J$ if it is a sheaf for each covering sieve of $J$, and it is *separated* for $J$ if it is separated for each covering sieve.

**Definition (Sheaf with values in a category).** Let $A$ be a category and let $P : C^{op} \to A$. Then $P$ is a sheaf for $J$ if for each object $E$ of $A$ the presheaf of sets $U \mapsto \mathrm{Hom}_A(E, P(U))$ is a sheaf for $J$. The sheaves form the full subcategory $\mathrm{Sh}(C, J; A)$ of the category of presheaves.

Equivalently, for each covering sieve $S$ on $X$, the object $P(X)$ with the restriction maps is a limit of the values $P(Y)$ over the morphisms $f : Y \to X$ in $S$. When $A$ is a category of algebraic structures such as groups or rings, the forgetful functor to sets preserves limits and reflects isomorphisms. Then $P$ is a sheaf if and only if its underlying presheaf of sets is a sheaf.

::: mathlib
`CategoryTheory.Presieve.IsSheafFor` · `Mathlib.CategoryTheory.Sites.IsSheafFor`

A family of elements is the type `FamilyOfElements P R`, which is the type `∀ ⦃Y⦄ (f : Y ⟶ X), R f → P.obj (op Y)`. The predicates `x.Compatible` and `x.IsAmalgamation t` are the definitions above, and `IsSheafFor P R` is `∀ x, x.Compatible → ∃! t, x.IsAmalgamation t`. The separated form is `IsSeparatedFor P R`. The file also gives `YonedaSheafCondition`, which states the condition as an extension of natural transformations along the inclusion of the sieve into the representable presheaf.

<?decl CategoryTheory.Presieve.IsSheafFor?>
:::

::: mathlib
`CategoryTheory.Sheaf` · `Mathlib.CategoryTheory.Sites.Sheaf`

`Presheaf.IsSheaf J P` is the condition for `P : Cᵒᵖ ⥤ A`, defined with `coyoneda` as above. `Sheaf J A` is the full subcategory `ObjectProperty.FullSubcategory (Presheaf.IsSheaf J)`, so a sheaf `F` has the presheaf `F.obj`. The inclusion is `sheafToPresheaf J A`, and `fullyFaithfulSheafToPresheaf` states that it is fully faithful. The limit form is `Presheaf.isSheaf_iff_isLimit`, and the form for a forgetful functor is `Presheaf.isSheaf_iff_isSheaf_forget`. For presheaves of types, `isSheaf_iff_isSheaf_of_type` links `Presheaf.IsSheaf` to `Presieve.IsSheaf`.

<?decl CategoryTheory.Sheaf?>
:::

### Theorems and proofs

Fix a presheaf of sets $P$ on $C$.

**Theorem (Compatible families on a sieve).** Let $S$ be a sieve on $X$. A family $x$ for $S$ is compatible if and only if $x_{f \circ g} = x_f|_g$ for each $f : Y \to X$ in $S$ and each $g : Z \to Y$.

*Proof.* Let $x$ be compatible, and let $f$ be in $S$ and $g : Z \to Y$. Then $f \circ g$ is in $S$. Apply the compatibility to $f_1 = f$, $g_1 = g$, $f_2 = f \circ g$ and $g_2 = 1_Z$. This gives $x_f|_g = x_{f \circ g}|_{1_Z} = x_{f \circ g}$. Conversely, let the equality hold, and let $f_1 \circ g_1 = f_2 \circ g_2 = h$. Then $x_{f_1}|_{g_1} = x_h = x_{f_2}|_{g_2}$. $\square$

**Theorem (A presieve and its sieve).** Let $R$ be a presieve on $X$ and let $\bar R$ be the sieve generated by $R$. Then $P$ is a sheaf for $R$ if and only if $P$ is a sheaf for $\bar R$. The same is true for the property "separated".

*Proof.* The proof gives a bijection between the compatible families for $R$ and the compatible families for $\bar R$ that keeps the amalgamations.

Let $x$ be a compatible family for $R$. Each $h$ in $\bar R$ has the form $h = f \circ g$ with $f$ in $R$. Put $y_h = x_f|_g$. This does not depend on the choice of $f$ and $g$. If $h = f \circ g = f' \circ g'$, then $x_f|_g = x_{f'}|_{g'}$ by the compatibility of $x$. The family $y$ satisfies $y_{h \circ k} = y_h|_k$, because $h \circ k = f \circ (g \circ k)$. So $y$ is compatible by the previous theorem. For $f$ in $R$, $y_f = x_f|_{1} = x_f$.

Conversely, the restriction to $R$ of a compatible family $y$ for $\bar R$ is compatible for $R$, and the two maps are inverse to each other. If $y_h = y_{f \circ g}$ comes from $x$, then the previous theorem gives $y_{f \circ g} = y_f|_g = x_f|_g$.

Last, $t$ is an amalgamation of $x$ if and only if it is an amalgamation of $y$. One direction is clear, since $R \subseteq \bar R$. For the other, if $t|_f = x_f$ for each $f$ in $R$, then $t|_{f \circ g} = (t|_f)|_g = x_f|_g = y_{f \circ g}$. $\square$

**Theorem (The equalizer condition).** Let $R = \{ f_i : Y_i \to X \}_{i \in I}$, and let each pair $f_i, f_j$ have a pullback $Y_i \times_X Y_j$ with projections $p_{ij}$ and $q_{ij}$. Then $P$ is a sheaf for $R$ if and only if the diagram

$$P(X) \xrightarrow{\ e\ } \prod_{i} P(Y_i) \rightrightarrows \prod_{i,j} P(Y_i \times_X Y_j)$$

is an equalizer of sets. Here $e(t) = (t|_{f_i})_i$, and the two maps send $(x_i)$ to $(x_i|_{p_{ij}})_{i,j}$ and to $(x_j|_{q_{ij}})_{i,j}$.

*Proof.* An element $(x_i)$ of the product is a family of elements for $R$. It is equalized by the two maps when $x_i|_{p_{ij}} = x_j|_{q_{ij}}$ for all $i, j$. This condition is equivalent to compatibility. Compatibility gives it, because $f_i \circ p_{ij} = f_j \circ q_{ij}$. Conversely, let $g_1 : Z \to Y_i$ and $g_2 : Z \to Y_j$ with $f_i \circ g_1 = f_j \circ g_2$. The universal property gives $u : Z \to Y_i \times_X Y_j$ with $p_{ij} \circ u = g_1$ and $q_{ij} \circ u = g_2$. Then $x_i|_{g_1} = (x_i|_{p_{ij}})|_u = (x_j|_{q_{ij}})|_u = x_j|_{g_2}$.

An element $t$ of $P(X)$ is an amalgamation of $(x_i)$ exactly when $e(t) = (x_i)$. So $P$ is a sheaf for $R$ if and only if $e$ is a bijection onto the set of equalized elements, which is the statement that the diagram is an equalizer. $\square$

**Theorem (Sheaves on a larger presieve).** Let $S$ be a sieve on $X$ and let $R$ be a presieve on $X$ with $S \subseteq R$. Let $P$ be a sheaf for $S$, and let $P$ be separated for $f^* S$ for each $f$ in $R$. Then $P$ is a sheaf for $R$.

*Proof.* Let $x$ be a compatible family for $R$. Two amalgamations of $x$ are amalgamations of the restriction of $x$ to $S$, so they are equal. For the existence, let $t$ be the amalgamation of the restriction of $x$ to $S$. Let $f : Y \to X$ be in $R$. Compare $t|_f$ and $x_f$ on the sieve $f^* S$. For $g$ in $f^* S$, the morphism $f \circ g$ is in $S$, so $(t|_f)|_g = t|_{f \circ g} = x_{f \circ g}$. The morphisms $f$ and $f \circ g$ are in $R$, and $f \circ g = (f \circ g) \circ 1_Z$. So the compatibility of $x$ gives $x_f|_g = x_{f \circ g}$. So $t|_f$ and $x_f$ are amalgamations of the same family for $f^* S$, and they are equal because $P$ is separated for $f^* S$. $\square$

**Theorem (Sheaves for a pretopology).** Let $C$ have pullbacks, let $K$ be a pretopology and let $J_K$ be the topology it generates. Then $P$ is a sheaf for $J_K$ if and only if $P$ is a sheaf for each covering family $R \in K(X)$.

*Proof.* If $P$ is a sheaf for $J_K$, then it is a sheaf for the sieve generated by $R \in K(X)$, which is in $J_K(X)$. By the theorem on a presieve and its sieve, $P$ is a sheaf for $R$.

Conversely, let $S \in J_K(X)$, so that $S$ contains some $R \in K(X)$. Let $\bar R \subseteq S$ be the sieve generated by $R$. For each $f : Y \to X$, the pullback $f^* \bar R$ is the sieve generated by the family of projections $\{Y \times_X X_r \to Y\}$. Section 1 shows one inclusion. For the other, if $f \circ g = r \circ k$ with $r$ in $R$, then $g$ factors through the projection by the universal property of the pullback. That family is in $K(Y)$, so $P$ is a sheaf for it and for $f^* \bar R$. Now use the previous theorem with $\bar R \subseteq S$. The case $f = 1_X$ shows that $P$ is a sheaf for $\bar R$, and the other cases give the separation. $\square$

**Theorem (The finest topology of a presheaf).** For each $X$, let $J_P(X)$ be the set of sieves $S$ on $X$ such that $P$ is a sheaf for $f^* S$ for each morphism $f$ with target $X$. Then $J_P$ is a Grothendieck topology. It is the largest topology for which $P$ is a sheaf.

*Proof (outline).* $P$ is a sheaf for each maximal sieve, because the identity is in it. The definition is stable under pullback, because $g^*(f^* S) = (f \circ g)^* S$. The proof of the transitivity axiom is the longest step. Let $S \in J_P(X)$ and let $R$ satisfy the hypothesis of axiom 3. After a pullback, it is enough to show that $P$ is a sheaf for $R$. Let $B$ be the sieve of the composites $f \circ g$ with $f$ in $S$ and $g$ in $f^* R$, as in Section 1. Then $B \subseteq R$. The proof shows first that $P$ is a sheaf for $B$, and then it uses the theorem on larger presieves for $B \subseteq R$. If $J$ is a topology for which $P$ is a sheaf, then each $S \in J(X)$ has all its pullbacks in $J$, so $J \subseteq J_P$. $\square$

The *canonical topology* of $C$ is the intersection of the topologies $J_{\mathrm{Hom}(-, X)}$ over all objects $X$. It is the largest topology for which each representable presheaf is a sheaf. A topology $J$ is *subcanonical* if $J$ is inside the canonical topology. For a subcanonical topology, the Yoneda embedding takes values in sheaves, and it is fully faithful.

### Examples

**Example (The sheaf condition on a two-set cover).** Let $T$ be a topological space, let $U = U_1 \cup U_2$ with $U_1, U_2$ open, and let $S$ be the sieve on $U$ generated by the two inclusions. In the topology of open covers, $S$ is a covering sieve. Let $P$ be a presheaf of sets on the open sets of $T$, and write $U_{12} = U_1 \cap U_2$.

By the theorem on a presieve and its sieve, $P$ is a sheaf for $S$ if and only if it is a sheaf for the presieve $R = \{U_1 \to U, U_2 \to U\}$. In the poset of open sets, the pullback of $V \to U$ and $W \to U$ is $V \cap W$. So the equalizer condition is about the diagram

$$P(U) \to P(U_1) \times P(U_2) \rightrightarrows P(U_1) \times P(U_{12}) \times P(U_{12}) \times P(U_2),$$

where the factors on the right belong to the pairs $(1,1)$, $(1,2)$, $(2,1)$ and $(2,2)$. Since $U_1 \cap U_1 = U_1$, the two maps agree on the factor $(1,1)$, and also on the factor $(2,2)$. The factors $(1,2)$ and $(2,1)$ give the same condition. So the sheaf condition for $S$ is this statement:

> For each $s_1 \in P(U_1)$ and $s_2 \in P(U_2)$ with $s_1|_{U_{12}} = s_2|_{U_{12}}$, there is exactly one $s \in P(U)$ with $s|_{U_1} = s_1$ and $s|_{U_2} = s_2$.

In other words, the square of sets with corners $P(U)$, $P(U_1)$, $P(U_2)$ and $P(U_{12})$ is a pullback square.

For the presheaf $C^0$ of continuous real functions, this is the gluing lemma for open sets. Two continuous functions that agree on $U_{12}$ give a function on $U$, it is continuous because continuity is a local property, and it is unique. For the presheaf of constant integer valued functions, with $P(\emptyset)$ a point, the condition fails when $U_1$ and $U_2$ are nonempty and disjoint. The functions $0$ on $U_1$ and $1$ on $U_2$ agree on $U_{12} = \emptyset$, but no constant function on $U$ restricts to both. The locally constant functions form a sheaf, and Section 3 shows that they are the sheafification of the constant functions.

The file `Mathlib.CategoryTheory.Sites.MayerVietorisSquare` takes this square as a definition on a general site. A Mayer-Vietoris square is a commutative square in $C$ such that each sheaf takes it to a pullback square.

**Example (The empty cover).** The empty sieve covers the empty open set. A family for the empty presieve has no elements, and it is compatible. So a sheaf $P$ has exactly one element in $P(\emptyset)$. On a general site, if the empty sieve covers $X$, then $F(X)$ is a terminal object for each sheaf $F$.

**Example (The trivial and discrete topologies).** For the trivial topology, each presheaf is a sheaf, because each presheaf is a sheaf for a maximal sieve. The identity is in the sieve, and $x_{1_X}$ is the only amalgamation. So the sheaves for the trivial topology are all presheaves. For the discrete topology, the empty sieve covers each object, and each sheaf is a terminal object.

**Example (Representable presheaves on a space).** Let $V$ be an open subset of $T$. The representable presheaf of $V$ on the poset of open sets has the value "one point" on $W$ if $W \subseteq V$, and the value $\emptyset$ otherwise. It is a sheaf: if $W$ is covered by open sets $W_i$ with $W_i \subseteq V$ for each $i$, then $W \subseteq V$. So the topology of open covers is subcanonical.

**Example (The canonical topology on sets).** On the category of sets, a sieve $S$ on a set $A$ is a covering sieve of the canonical topology if and only if the morphisms in $S$ are jointly surjective. One direction is in Exercise 5.

### The library around it

::: mathlib
`CategoryTheory.Equalizer.Presieve.sheaf_condition` · `Mathlib.CategoryTheory.Sites.EqualizerSheafCondition`

This is the equalizer condition for a presieve with pairwise pullbacks, with `FirstObj` and `SecondObj` as the two products and `firstMap` and `secondMap` as the two maps. The statement is `R.IsSheafFor P ↔ Nonempty (IsLimit (Fork.ofι _ (w P R)))`. The version for a sieve, `Equalizer.Sieve.equalizer_sheaf_condition`, needs no pullbacks and uses the product over all pairs of a morphism in the sieve and a morphism into its source. The version `Equalizer.Presieve.Arrows.sheaf_condition` is for an indexed family.

<?decl CategoryTheory.Equalizer.Presieve.sheaf_condition?>
:::

::: mathlib
`CategoryTheory.Sheaf.canonicalTopology` · `Mathlib.CategoryTheory.Sites.Canonical`

`Sheaf.finestTopologySingle P` is the topology $J_P$, and `Sheaf.finestTopology Ps` is the intersection for a set of presheaves. The canonical topology is `finestTopology (Set.range yoneda.obj)`. The class `J.Subcanonical` has the field `le_canonical`, and for a subcanonical topology, `J.yoneda : C ⥤ Sheaf J (Type v)` is fully faithful by `J.yonedaFullyFaithful`. The file `Sites.Subcanonical` gives the Yoneda bijection `J.yonedaEquiv` for sheaves.

<?decl CategoryTheory.Sheaf.canonicalTopology?>
:::

The theorem on pretopologies is `Presieve.isSheaf_pretopology`. The theorem on larger presieves is `Presieve.isSheafFor_subsieve_aux`, and `isSheafFor_subsieve` is its form with all pullbacks. The topology on `Type u` of jointly surjective families is `typesGrothendieckTopology` in `Mathlib.CategoryTheory.Sites.Types`, and the lemma `typesGrothendieckTopology_eq_canonical` states that it is the canonical topology.

Common errors of a learner:

- `Presieve.IsSheaf J P` is for presheaves of types, and `Presheaf.IsSheaf J P` is for presheaves with values in any category. Use `isSheaf_iff_isSheaf_of_type` to pass between them.
- A family of elements takes a proof `R f` as an argument. Two proofs of `R f` are equal, but a rewrite of `f` changes the type of the proof.
- The compatibility condition in Mathlib uses all pairs $g_1, g_2$ with $f_1 \circ g_1 = f_2 \circ g_2$. It does not need pullbacks. Use `pullbackCompatible_iff` to pass to the form with pullbacks when they exist.
- An object of `Sheaf J A` is a presheaf with a proof of the sheaf condition. Write `F.obj` for the presheaf of a sheaf `F`, and `F.property` for the proof.

### Exercises

1. (A) Show that each presheaf is a sheaf for the presieve $\{1_X\}$, and for each presieve that contains an isomorphism with target $X$.
2. (A) Let $P$ be a sheaf for $J$, and let $J' \subseteq J$ be a smaller topology. Show that $P$ is a sheaf for $J'$.
3. (A) Show that the presheaf of bounded real functions on the open sets of $\mathbb{R}$ satisfies the condition for each cover by two open sets, but is not a sheaf for the topology of open covers.
4. (B) Let $P$ be the presheaf on the open sets of $T$ with $P(U) = \mathbb{Z}$ for each $U$ and identity restrictions. Show that $P$ is a sheaf for each nonempty covering sieve. *Hint:* a nonempty sieve contains the empty open set. Then show that $P$ is not separated for the empty sieve on $\emptyset$.
5. (B) Let $S$ be a sieve on a set $A$ in the category of sets, and let the morphisms in $S$ be jointly surjective. Show that each representable presheaf $\mathrm{Hom}(-, B)$ is a sheaf for $S$. *Hint:* a function on $A$ is the same as a compatible family of functions on the sources of the morphisms in $S$.
6. (B) Let $P$ be a presheaf of abelian groups on the open sets of $T$. Write the sheaf condition for a two-set cover as the exactness of a sequence $0 \to P(U) \to P(U_1) \oplus P(U_2) \to P(U_{12})$, with the map $(s_1, s_2) \mapsto s_1|_{U_{12}} - s_2|_{U_{12}}$.
7. (C) Let $J$ be a topology on $C$ and let $P$ be separated for $J$. Show that $P$ is a sheaf for $J$ if and only if each compatible family on each covering sieve has an amalgamation, without the uniqueness.

### Notes and history

The gluing condition for sheaves on a space is due to Leray, in his work of the 1940s on the cohomology of spaces, and the form with open sets is in the seminar of Cartan in the early 1950s. Grothendieck extended the condition to sites. The definitions of this section are those of SGA 4, and the families of elements follow the book *Sheaves in Geometry and Logic* by Mac Lane and Moerdijk (1992) and Part C of *Sketches of an Elephant* by Johnstone (2002). The source files cite the Stacks project for the definition of a sheaf with values in a category and for the canonical topology.

The Mathlib Authors of `Sites.IsSheafFor`, `Sites.SheafOfTypes`, `Sites.EqualizerSheafCondition` and `Sites.Canonical` are Bhavik Mehta. The file `Sites.Sheaf` is by Kevin Buzzard and Bhavik Mehta, and `Sites.Subcanonical` is by Dagur Asgeirsson.

### Reference

<?reference?>
