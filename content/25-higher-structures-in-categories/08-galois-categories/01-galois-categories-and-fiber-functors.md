---
title: Galois categories and fiber functors
kind: theory
modules:
  - Mathlib.CategoryTheory.Galois.Basic
  - Mathlib.CategoryTheory.Galois.Decomposition
  - Mathlib.CategoryTheory.Galois.GaloisObjects
  - Mathlib.CategoryTheory.Galois.Examples
explains:
  E3: [CategoryTheory.PreGaloisCategory, CategoryTheory.PreGaloisCategory.FiberFunctor, CategoryTheory.PreGaloisCategory.IsConnected, CategoryTheory.GaloisCategory, CategoryTheory.PreGaloisCategory.IsGalois, CategoryTheory.PreGaloisCategory.has_decomp_connected_components, CategoryTheory.PreGaloisCategory.exists_galois_representative, CategoryTheory.PreGaloisCategory.isGalois_iff_pretransitive, CategoryTheory.FintypeCat.Action.isConnected_iff_transitive]
  E2: [CategoryTheory.GaloisCategory.getFiberFunctor, CategoryTheory.PreGaloisCategory.PreservesIsConnected, CategoryTheory.PreGaloisCategory.initial_iff_fiber_empty, CategoryTheory.PreGaloisCategory.evaluation_injective_of_isConnected, CategoryTheory.PreGaloisCategory.evaluation_aut_injective_of_isConnected, CategoryTheory.PreGaloisCategory.epi_of_nonempty_of_isConnected, CategoryTheory.PreGaloisCategory.surjective_on_fiber_of_epi, CategoryTheory.PreGaloisCategory.surjective_of_nonempty_fiber_of_isConnected, CategoryTheory.PreGaloisCategory.isIso_of_mono_of_eq_card_fiber, CategoryTheory.PreGaloisCategory.card_hom_le_card_fiber_of_connected, CategoryTheory.PreGaloisCategory.card_aut_le_card_fiber_of_connected, CategoryTheory.PreGaloisCategory.has_non_trivial_subobject_of_not_isConnected_of_not_initial, CategoryTheory.PreGaloisCategory.card_fiber_coprod_eq_sum, CategoryTheory.PreGaloisCategory.fiber_in_connected_component, CategoryTheory.PreGaloisCategory.connected_component_unique, CategoryTheory.PreGaloisCategory.exists_hom_from_galois_of_fiber, CategoryTheory.PreGaloisCategory.natTrans_ext_of_isGalois, CategoryTheory.PreGaloisCategory.autMulFiber, CategoryTheory.PreGaloisCategory.evaluationEquivOfIsGalois, CategoryTheory.PreGaloisCategory.evaluation_aut_bijective_of_isGalois, CategoryTheory.PreGaloisCategory.stabilizer_normal_of_isGalois, CategoryTheory.PreGaloisCategory.exists_autMap, CategoryTheory.PreGaloisCategory.autMap, CategoryTheory.PreGaloisCategory.autMap_surjective_of_isGalois, CategoryTheory.FintypeCat.instPreGaloisCategoryActionFintypeCat, CategoryTheory.FintypeCat.instGaloisCategoryActionFintypeCat, CategoryTheory.FintypeCat.Action.pretransitive_of_isConnected, CategoryTheory.FintypeCat.Action.isConnected_of_transitive, CategoryTheory.FintypeCat.isoQuotientStabilizerOfIsConnected, CategoryTheory.FintypeCat.Action.imageComplement]
  E1: auto
families: []
requires: [V05, V24.C04, V24.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Galois categories and fiber functors

### Overview

Two classical theories have the same form. Let $K$ be a field with a separable closure $K^s$, and let $\Gamma$ be the Galois group of $K^s$ over $K$. Then the finite separable extensions of $K$, and more generally the finite étale $K$-algebras, correspond to the finite sets with a continuous action of $\Gamma$. Let $T$ be a connected and locally simply connected space with a base point. Then the finite covering spaces of $T$ correspond to the finite sets with an action of the fundamental group of $T$. In each case a functor sends an object to a finite set: the set of the $K$-algebra maps to $K^s$, or the fiber of the covering over the base point. The group acts on these finite sets, and the functor is an equivalence onto the finite sets with an action.

Grothendieck put the common part of the two theories into axioms in SGA 1. A Galois category is a category with some finite limits and colimits, and a fiber functor is a functor to finite sets that preserves them and reflects isomorphisms. The main theorem, in Section 2, says that the automorphism group of the fiber functor is a profinite group $\pi$, and that the fiber functor gives an equivalence of the category with the finite sets with a continuous action of $\pi$.

This section gives the axioms and the first consequences. It shows that each object is a finite coproduct of connected objects, it defines Galois objects, and it shows that the fiber of each object is represented by a Galois object. The example is the category of finite $G$-sets. The source files follow the notes of Lenstra, *Galois theory for schemes*.

In the text $g \circ f$ is the textbook composite, and Mathlib writes `f ≫ g`. Finite limits and colimits are in Volume 24, Chapter 4, and group actions are in Volume 5.

### Definitions

For a finite group $G$ that acts on an object $X$ by a homomorphism $G \to \mathrm{Aut}(X)$, the quotient $X/G$ is the colimit of the functor from the one-object category of $G$ to $C$ that sends the object to $X$. So a morphism $X/G \to Y$ is a morphism $X \to Y$ that is invariant under $G$.

**Definition (Pre-Galois category).** A category $C$ is pre-Galois if these axioms are true.

- (G1) $C$ has a terminal object and pullbacks. So $C$ has all finite limits.
- (G2) $C$ has finite coproducts, and quotients by finite groups of automorphisms.
- (G3) For each monomorphism $i : X \to Y$ there are an object $Z$ and a morphism $u : Z \to Y$ such that $i$ and $u$ make $Y$ a coproduct $X \sqcup Z$.

Axiom (G3) says that each subobject is a direct summand. The empty coproduct is an initial object, so $C$ has an initial object $0$.

**Definition (Fiber functor).** Let $C$ be pre-Galois. A fiber functor is a functor $F : C \to \mathbf{FinSet}$ with these properties.

- (G4) $F$ preserves the terminal object and pullbacks.
- (G5) $F$ preserves finite coproducts, epimorphisms, and quotients by finite groups.
- (G6) $F$ reflects isomorphisms: if $F(f)$ is bijective, then $f$ is an isomorphism.

The set $F(X)$ is the fiber of $X$. By (G4), $F$ preserves all finite limits.

**Definition (Galois category).** A Galois category is a pre-Galois category that has a fiber functor.

**Definition (Connected object).** An object $X$ is connected if it is not initial, and each monomorphism $Y \to X$ with $Y$ not initial is an isomorphism.

So a connected object has no subobjects other than $0$ and itself. The group $\mathrm{Aut}(X)$ acts on the fiber $F(X)$ by $\sigma \cdot x = F(\sigma)(x)$.

**Definition (Galois object).** A connected object $X$ is Galois if the quotient $X / \mathrm{Aut}(X)$ is a terminal object.

For $X$ connected, the group $\mathrm{Aut}(X)$ is finite (see the theorem on evaluation below), so the quotient exists by (G2).

::: mathlib
`CategoryTheory.PreGaloisCategory` · `Mathlib.CategoryTheory.Galois.Basic`

The class of the axioms (G1) to (G3). The fields are `hasTerminal`, `hasPullbacks`, `hasFiniteCoproducts`, `hasQuotientsByFiniteGroups` and `monoInducesIsoOnDirectSummand`. A quotient by a finite group `G` is the statement `HasColimitsOfShape (SingleObj G) C`. The first four fields are instances.

<?decl CategoryTheory.PreGaloisCategory?>
:::

### Theorems and proofs

In this part $C$ is pre-Galois and $F$ is a fiber functor. The first result relates the initial object to the fiber.

**Proposition (Empty fibers).** An object $X$ is initial if and only if $F(X)$ is empty.

*Proof.* The initial object $0$ is the empty coproduct, and $F$ preserves finite coproducts. So $F(0)$ is the empty coproduct of finite sets, which is the empty set. Thus if $X$ is initial, $F(X)$ is empty. Conversely, suppose that $F(X)$ is empty. Let $u : 0 \to X$ be the unique morphism. Then $F(u)$ is a map from the empty set to the empty set, so it is bijective. By (G6), $u$ is an isomorphism, and $X$ is initial. $\square$

**Proposition (Faithfulness).** If $f, g : X \to Y$ and $F(f) = F(g)$, then $f = g$.

*Proof.* Let $e : E \to X$ be an equalizer of $f$ and $g$. It exists because $C$ has finite limits. The functor $F$ preserves finite limits, so $F(e)$ is an equalizer of $F(f)$ and $F(g)$. These maps are equal, so their equalizer is a bijection. By (G6), $e$ is an isomorphism. Then $f \circ e = g \circ e$ gives $f = g$. $\square$

The same argument shows that $F$ reflects monomorphisms. A morphism $f$ is a monomorphism if and only if the first projection of the pullback of $f$ with $f$ is an isomorphism. The functor $F$ preserves this pullback and reflects isomorphisms.

The next theorem is the most used lemma of the theory. A morphism from a connected object is determined by its value at one point of the fiber.

**Theorem (Evaluation at one point).** Let $A$ be connected and let $a \in F(A)$. If $f, g : A \to X$ and $F(f)(a) = F(g)(a)$, then $f = g$.

*Proof.* Let $e : E \to A$ be an equalizer of $f$ and $g$. Then $e$ is a monomorphism. The fiber $F(E)$ is the equalizer of $F(f)$ and $F(g)$, which contains $a$. So $F(E)$ is not empty, and $E$ is not initial by the proposition on empty fibers. Because $A$ is connected, $e$ is an isomorphism, and $f = g$. $\square$

**Corollary (Finiteness).** For $A$ connected and each $X$, the map $\mathrm{Hom}(A, X) \to F(X)$, $f \mapsto F(f)(a)$, is injective. So $|\mathrm{Hom}(A, X)| \le |F(X)|$ and $|\mathrm{Aut}(A)| \le |F(A)|$. In particular, $\mathrm{Aut}(A)$ acts freely on $F(A)$.

*Proof.* The fiber $F(A)$ is not empty, because $A$ is not initial. Choose $a$ in it and apply the theorem. If $\sigma \cdot x = x$ for some $x$, then $\sigma$ and $1_A$ agree at $x$, so $\sigma = 1_A$. $\square$

**Proposition (Morphisms to connected objects).** Let $A$ be connected, and let $f : X \to A$ with $F(X)$ not empty. Then $f$ is an epimorphism, and $F(f)$ is surjective.

*Proof.* Let $u, v : A \to Z$ with $u \circ f = v \circ f$. Choose $x \in F(X)$ and put $a = F(f)(x)$. Then $F(u)(a) = F(u \circ f)(x) = F(v \circ f)(x) = F(v)(a)$, so $u = v$ by the theorem on evaluation. Thus $f$ is an epimorphism. By (G5), $F(f)$ is an epimorphism of finite sets, so it is surjective. $\square$

**Proposition (Counting).** Let $i : X \to Y$ be a monomorphism with $|F(X)| = |F(Y)|$. Then $i$ is an isomorphism.

*Proof.* The functor $F$ preserves monomorphisms, because it preserves pullbacks. So $F(i)$ is an injective map between finite sets with the same number of elements. Thus $F(i)$ is bijective, and $i$ is an isomorphism by (G6). $\square$

The decomposition into connected components is an induction on the size of the fiber.

**Theorem (Connected components).** Each object $X$ is a finite coproduct of connected objects.

*Proof.* The proof is by induction on $n = |F(X)|$. If $n = 0$, then $X$ is initial, and it is the empty coproduct. Suppose that $n > 0$, so $X$ is not initial. If $X$ is connected, the result is true. If $X$ is not connected, there is a monomorphism $i : Y \to X$ with $Y$ not initial, and $i$ is not an isomorphism. By (G3), $X$ is a coproduct $Y \sqcup Z$ with the injections $i$ and $u : Z \to X$. The functor $F$ preserves this coproduct, so $|F(X)| = |F(Y)| + |F(Z)|$. The fiber $F(Y)$ is not empty, so $|F(Z)| < n$. If $|F(Y)| = n$, then $i$ is an isomorphism by the proposition on counting, which is false. So $|F(Y)| < n$. By the induction hypothesis, $Y$ and $Z$ are finite coproducts of connected objects, and thus $X$ is also one. $\square$

The proof uses $F$ only to measure the size of objects. So the result is true for each Galois category, and Mathlib states it with a fiber functor that it selects by choice.

**Corollary (Components of a point).** For each $x \in F(X)$ there are a connected object $Y$, a monomorphism $i : Y \to X$ and $y \in F(Y)$ with $F(i)(y) = x$. If $(Y', i', y')$ is a second such triple, then there is an isomorphism $\varphi : Y \to Y'$ with $F(\varphi)(y) = y'$.

*Proof.* Write $X = \coprod_k Y_k$ with $Y_k$ connected. The functor $F$ preserves the coproduct, so $F(X)$ is the disjoint union of the sets $F(Y_k)$, and $x$ is in one of them. In a Galois category the injections of a coproduct are monomorphisms, and Mathlib gives this as an instance of `MonoCoprod`. This gives the first statement.

For the second statement, let $P$ be the pullback of $i$ and $i'$, with projections $p : P \to Y$ and $p' : P \to Y'$. These projections are monomorphisms, because $i$ and $i'$ are monomorphisms. The fiber $F(P)$ is the set of the pairs $(z, z')$ with $F(i)(z) = F(i')(z')$, and it contains $(y, y')$. So $P$ is not initial. Because $Y$ and $Y'$ are connected, $p$ and $p'$ are isomorphisms. Put $\varphi = p' \circ p^{-1}$. Then $F(\varphi)(y) = y'$. $\square$

Now consider Galois objects. Recall that $\mathrm{Aut}(X)$ acts on $F(X)$.

**Theorem (Galois objects and transitivity).** A connected object $X$ is Galois if and only if $\mathrm{Aut}(X)$ acts transitively on $F(X)$.

*Proof.* The group $H = \mathrm{Aut}(X)$ is finite. By (G5), $F(X/H)$ is the quotient of $F(X)$ by $H$, which is the set of the orbits of $H$ on $F(X)$. Let $t : X/H \to 1$ be the morphism to the terminal object. The functor $F$ preserves the terminal object, so $F(1)$ is a one-point set. Then $X/H$ is terminal if and only if $t$ is an isomorphism. By (G6) and because $F$ preserves isomorphisms, this is true if and only if $F(X/H)$ has exactly one element. The fiber $F(X)$ is not empty, so this is true if and only if $H$ has exactly one orbit on $F(X)$. $\square$

**Corollary (Galois objects as torsors).** If $A$ is Galois and $a \in F(A)$, then the map $\mathrm{Aut}(A) \to F(A)$, $\sigma \mapsto F(\sigma)(a)$, is bijective. So $|\mathrm{Aut}(A)| = |F(A)|$.

*Proof.* The map is injective by the theorem on evaluation, and surjective by transitivity. $\square$

The next theorem is the key step for Section 2. The fiber functor is not representable in general, but it is represented by a Galois object on each single object.

**Theorem (Galois representative).** For each object $X$ there are a Galois object $A$ and $a \in F(A)$ such that the map $\mathrm{Hom}(A, X) \to F(X)$, $f \mapsto F(f)(a)$, is bijective.

*Proof.* Let $S = F(X)$, a finite set. Let $P = \prod_{s \in S} X$ be the product of copies of $X$ indexed by $S$, with projections $\pi_s$. Then $F(P) = \prod_{s \in S} F(X)$, which is the set of the maps $S \to F(X) = S$. Let $p \in F(P)$ be the identity map of $S$, so $p_s = s$. By the corollary on components, there are a connected $A$, a monomorphism $i : A \to P$ and $a \in F(A)$ with $F(i)(a) = p$.

The map $f \mapsto F(f)(a)$ from $\mathrm{Hom}(A, X)$ is injective by the theorem on evaluation. It is surjective, because for $s \in S$ the morphism $\pi_s \circ i$ sends $a$ to $p_s = s$.

It remains to show that $A$ is Galois. Let $b \in F(A)$ and put $q = F(i)(b)$, a map $S \to S$. Suppose that $q_s = q_t$. Then $\pi_s \circ i$ and $\pi_t \circ i$ agree at $b$, so they are equal by the theorem on evaluation, and thus they agree at $a$. This gives $s = t$. So $q$ is injective, and it is a permutation of the finite set $S$. Let $\tau : P \to P$ be the automorphism with $\pi_s \circ \tau = \pi_{q(s)}$ for each $s$. It permutes the factors. Then $F(\tau)(p)_s = p_{q(s)} = q_s$, so $F(\tau \circ i)(a) = q = F(i)(b)$. The morphisms $\tau \circ i$ and $i$ are monomorphisms from the connected object $A$. By the second part of the corollary on components, there is $\varphi \in \mathrm{Aut}(A)$ with $F(\varphi)(a) = b$. So $\mathrm{Aut}(A)$ is transitive on $F(A)$, and $A$ is Galois. $\square$

**Corollary.** Each element $x \in F(X)$ is $F(f)(a)$ for some Galois $A$, some $f : A \to X$ and some $a \in F(A)$. So two natural transformations $F \to G$ to a functor $G : C \to \mathbf{FinSet}$ are equal if they agree on all Galois objects.

*Proof.* The first statement follows from the theorem. For the second, let $t$ and $s$ agree on Galois objects, and let $x = F(f)(a)$ as above. By naturality, $t_X(x) = G(f)(t_A(a)) = G(f)(s_A(a)) = s_X(x)$. $\square$

### Examples

**Example (Finite $G$-sets).** Let $G$ be a group. The finite $G$-sets, with the $G$-equivariant maps, form a Galois category, and the forgetful functor to finite sets is a fiber functor. Limits, finite coproducts and quotients by finite groups are computed on the underlying sets, with the induced action. A monomorphism is an injective equivariant map, and its image is a $G$-stable subset. The complement of a $G$-stable subset is $G$-stable, so it gives (G3). Mathlib calls this complement `Action.imageComplement`.

**Example (Connected $G$-sets).** A nonempty finite $G$-set $X$ is connected if and only if $G$ acts transitively on $X$. A subobject of $X$ is a $G$-stable subset. So $X$ is connected if and only if it has no $G$-stable subset other than $\emptyset$ and $X$, which is true if and only if $X$ is one orbit. For $x \in X$, the map $G/G_x \to X$, $g G_x \mapsto g \cdot x$, is then an isomorphism of $G$-sets, where $G_x$ is the stabilizer of $x$.

**Example (Galois $G$-sets).** Let $H$ be a subgroup of finite index in $G$, and let $X = G/H$. An equivariant map $\sigma : X \to X$ is determined by $\sigma(H) = gH$, and this is well defined if and only if $g^{-1} h g \in H$ for each $h \in H$. So $\mathrm{Aut}(X) \cong N_G(H)/H$, where $N_G(H)$ is the normalizer. The orbit of $H$ under $\mathrm{Aut}(X)$ is $N_G(H)/H$. So $X$ is Galois if and only if $N_G(H) = G$, that is, if and only if $H$ is normal. Mathlib proves the general form of one direction: for a Galois object $X$ and $x \in F(X)$, the stabilizer of $x$ in the group $\mathrm{Aut}(F)$ of Section 2 is a normal subgroup.

**Example (Field extensions).** Let $C$ be the opposite category of the finite étale algebras over a field $K$, and let $F(A)$ be the set of the $K$-algebra maps $A \to K^s$. Then $C$ is a Galois category and $F$ is a fiber functor. A connected object is a finite separable field extension $L$ of $K$, and it is Galois in the sense above if and only if $L/K$ is a Galois extension. The index of this edition has no declaration that gives a Galois category outside the folder `Mathlib.CategoryTheory.Galois`, so this example is not in Mathlib.

**Example (The automorphisms of a component).** Let $f : A \to B$ with $A$ connected and $B$ Galois. For each $\sigma \in \mathrm{Aut}(A)$ there is a unique $\tau \in \mathrm{Aut}(B)$ with $\tau \circ f = f \circ \sigma$. Choose $a \in F(A)$. By the corollary on torsors, there is a unique $\tau$ with $F(\tau)(F(f)(a)) = F(f \circ \sigma)(a)$, and the theorem on evaluation at $a$ gives $\tau \circ f = f \circ \sigma$. Mathlib calls this $\tau$ `autMap f σ`, and it proves that $\sigma \mapsto \tau$ is surjective when $A$ is also Galois.

### The library around it

::: mathlib
`CategoryTheory.PreGaloisCategory.FiberFunctor` · `Mathlib.CategoryTheory.Galois.Basic`

The class of the axioms (G4) to (G6) for a functor `F : C ⥤ FintypeCat.{w}`. The fields are `preservesTerminalObjects`, `preservesPullbacks`, `preservesFiniteCoproducts`, `preservesEpis`, `preservesQuotientsByFiniteGroups` and `reflectsIsos`. From them Mathlib derives the instances `F.Faithful`, `ReflectsMonomorphisms F` and the action of `Aut F` on each fiber.

<?decl CategoryTheory.PreGaloisCategory.FiberFunctor?>
:::

::: mathlib
`CategoryTheory.PreGaloisCategory.IsConnected` · `Mathlib.CategoryTheory.Galois.Basic`

The class of connected objects. The field `notInitial` says that `X` is not initial, and `noTrivialComponent` says that a monomorphism `Y ⟶ X` with `Y` not initial is an isomorphism. The class needs only a category, not a Galois category.

<?decl CategoryTheory.PreGaloisCategory.IsConnected?>
:::

::: mathlib
`CategoryTheory.GaloisCategory` · `Mathlib.CategoryTheory.Galois.Basic`

A pre-Galois category with the field `hasFiberFunctor`, which says that a fiber functor to `FintypeCat.{u₂}` exists. Here `u₂` is the universe of the morphisms of `C`. The function `GaloisCategory.getFiberFunctor C` selects one fiber functor by choice.

<?decl CategoryTheory.GaloisCategory?>
:::

::: mathlib
`CategoryTheory.PreGaloisCategory.IsGalois` · `Mathlib.CategoryTheory.Galois.GaloisObjects`

The class of Galois objects. It extends `IsConnected X`, and its field `quotientByAutTerminal` says that the colimit of the action of `Aut X` on `X` is terminal. The definition needs `[GaloisCategory C]`, because the finiteness of `Aut X` uses a fiber functor.

<?decl CategoryTheory.PreGaloisCategory.IsGalois?>
:::

::: mathlib
`CategoryTheory.PreGaloisCategory.has_decomp_connected_components` · `Mathlib.CategoryTheory.Galois.Decomposition`

The theorem on connected components. It gives a type `ι` with `Finite ι`, a family `f : ι → C` of connected objects and morphisms `g i : f i ⟶ X` such that `Cofan.mk X g` is a colimit. The variant `has_decomp_connected_components'` gives an isomorphism `∐ f ≅ X`.

<?decl CategoryTheory.PreGaloisCategory.has_decomp_connected_components?>
:::

::: mathlib
`CategoryTheory.PreGaloisCategory.exists_galois_representative` · `Mathlib.CategoryTheory.Galois.Decomposition`

The theorem on the Galois representative. For a fiber functor `F` and an object `X`, it gives `A`, `a : F.obj A`, a proof of `IsGalois A`, and a proof that `fun f : A ⟶ X ↦ F.map f a` is bijective.

<?decl CategoryTheory.PreGaloisCategory.exists_galois_representative?>
:::

::: mathlib
`CategoryTheory.PreGaloisCategory.isGalois_iff_pretransitive` · `Mathlib.CategoryTheory.Galois.GaloisObjects`

For a connected `X`, the statement `IsGalois X` is equivalent to `MulAction.IsPretransitive (Aut X) (F.obj X)`. The action is the instance `autMulFiber`.

<?decl CategoryTheory.PreGaloisCategory.isGalois_iff_pretransitive?>
:::

::: mathlib
`CategoryTheory.FintypeCat.Action.isConnected_iff_transitive` · `Mathlib.CategoryTheory.Galois.Examples`

For `X : Action FintypeCat G` with `[Nonempty X.V]`, the object `X` is connected if and only if `G` acts transitively on `X.V`. The instances `PreGaloisCategory`, `FiberFunctor` and `GaloisCategory` for `Action FintypeCat G` are in the same file.

<?decl CategoryTheory.FintypeCat.Action.isConnected_iff_transitive?>
:::

The theorem on empty fibers is `initial_iff_fiber_empty`. The theorem on evaluation is `evaluation_injective_of_isConnected`, and its corollaries are `evaluation_aut_injective_of_isConnected`, `card_hom_le_card_fiber_of_connected` and `card_aut_le_card_fiber_of_connected`. The proposition on morphisms to connected objects is `epi_of_nonempty_of_isConnected` with `surjective_of_nonempty_fiber_of_isConnected`, and the proposition on counting is `isIso_of_mono_of_eq_card_fiber`. The corollary on components is `fiber_in_connected_component` with `connected_component_unique`. The corollary on torsors is `evaluation_aut_bijective_of_isGalois`, and `evaluationEquivOfIsGalois` gives the bijection as an equivalence. The isomorphism $X \cong G/G_x$ for a connected $G$-set is `isoQuotientStabilizerOfIsConnected`.

Common errors of a learner:

- The names are in the namespace `CategoryTheory.PreGaloisCategory`, but `GaloisCategory` itself is `CategoryTheory.GaloisCategory`. The examples for $G$-sets are in `CategoryTheory.FintypeCat`.
- A lemma with an explicit argument `F` needs `[PreGaloisCategory C]` and `[FiberFunctor F]`. A lemma without `F`, such as `has_decomp_connected_components`, needs `[GaloisCategory C]`.
- The fiber `F.obj X` is an object of `FintypeCat`. To apply a map to an element, write `F.map f x`. Lemmas such as `FintypeCat.comp_apply` move between composition and application.
- The connected objects in this section are not the connected categories of Volume 24. The class `PreGaloisCategory.IsConnected` is about an object.

### Exercises

1. (A) Show that a coproduct $X \sqcup Y$ with $X$ and $Y$ not initial is not connected.
2. (A) Show that the terminal object of a Galois category is Galois. *Hint:* its fiber has one element.
3. (A) Let $A$ be connected. Show that each endomorphism of $A$ is an automorphism. *Hint:* use the proposition on morphisms to connected objects and the finiteness of $F(A)$.
4. (B) Show that in a pre-Galois category the injections of a binary coproduct are monomorphisms, by the use of (G3) and a fiber functor.
5. (B) Let $G$ be the symmetric group on three letters, and let $X$ be the set $\{1, 2, 3\}$ with the natural action. Find $\mathrm{Aut}(X)$ in the category of $G$-sets, and show that $X$ is connected but not Galois. Find a Galois representative of $X$.
6. (B) Let $f : A \to B$ with $A$ and $B$ Galois. Show that the map $\mathrm{Aut}(A) \to \mathrm{Aut}(B)$, $\sigma \mapsto \tau$, of the last example is a surjective group homomorphism.
7. (C) Let $X$ be an object with $n$ elements in its fiber. Show that the Galois representative of $X$ constructed in the proof has at most $n!$ elements in its fiber, and give an example in finite $G$-sets with exactly $n!$ elements.

### Notes and history

Galois categories are due to Grothendieck, in Exposé V of SGA 1, *Revêtements étales et groupe fondamental* (1961). His aim was the étale fundamental group of a scheme, which unifies the Galois group of a field and the fundamental group of a space. The axioms in Mathlib follow the notes of H. W. Lenstra, *Galois theory for schemes*, Definition 3.1. The book of Szamuely, *Galois groups and fundamental groups* (2009), gives the same theory with many examples.

The Mathlib Authors line of `Galois.Basic`, `Galois.Decomposition`, `Galois.GaloisObjects` and `Galois.Examples` names Christian Merten.

### Reference

<?reference?>
