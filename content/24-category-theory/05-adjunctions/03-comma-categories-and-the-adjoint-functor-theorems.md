---
title: Comma categories and the adjoint functor theorems
kind: theory
modules:
  - Mathlib.CategoryTheory.Comma.Basic
  - Mathlib.CategoryTheory.Comma.Over.Basic
  - Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
  - Mathlib.CategoryTheory.Adjunction.Comma
  - Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
  - Mathlib.CategoryTheory.Limits.Constructions.WeaklyInitial
explains:
  E3: [CategoryTheory.Comma, CategoryTheory.StructuredArrow, CategoryTheory.isRightAdjoint_iff_hasInitial_structuredArrow, CategoryTheory.SolutionSetCondition, CategoryTheory.isRightAdjoint_of_preservesLimits_of_solutionSetCondition]
  E2: [CategoryTheory.CommaMorphism, CategoryTheory.Comma.fst, CategoryTheory.Comma.snd, CategoryTheory.Comma.hom, CategoryTheory.Over, CategoryTheory.Over.mk, CategoryTheory.Over.forget, CategoryTheory.Over.homMk, CategoryTheory.Under, CategoryTheory.Under.mk, CategoryTheory.StructuredArrow.mk, CategoryTheory.StructuredArrow.homMk, CategoryTheory.StructuredArrow.proj, CategoryTheory.CostructuredArrow, CategoryTheory.isLeftAdjoint_iff_hasTerminal_costructuredArrow, CategoryTheory.leftAdjointOfStructuredArrowInitials, CategoryTheory.adjunctionOfStructuredArrowInitials, CategoryTheory.mkInitialOfLeftAdjoint, CategoryTheory.solutionSetCondition_of_isRightAdjoint, CategoryTheory.isRightAdjoint_of_preservesLimits_of_isCoseparating, CategoryTheory.isLeftAdjoint_of_preservesColimits_of_isSeparating, CategoryTheory.hasInitial_of_weakly_initial_and_hasWideEqualizers, CategoryTheory.has_weakly_initial_of_weakly_initial_set_and_hasProducts]
  E1: auto
families: []
requires: [V24.C01, V24.C02, V24.C03, V24.C04, V05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Comma categories and the adjoint functor theorems

### Overview

Section 2 showed that a right adjoint preserves limits. This section proves a converse, Freyd's general adjoint functor theorem: a functor $G : D \to C$ from a complete, locally small category that preserves limits has a left adjoint if it satisfies one condition of size, the solution set condition. The tool is the comma category $A \downarrow G$ of arrows from $A$ to $G$. A left adjoint exists exactly when each $A \downarrow G$ has an initial object, and the theorem builds this initial object as a limit. An application gives the free group.

### Definitions

**Definition (Comma category).** Let $S : A \to C$ and $T : B \to C$ be functors. The *comma category* $S \downarrow T$ has as objects the triples $(a, b, f)$ with $a$ in $A$, $b$ in $B$ and $f : S(a) \to T(b)$. A morphism $(a, b, f) \to (a', b', f')$ is a pair $\alpha : a \to a'$, $\beta : b \to b'$ with $f' \circ S(\alpha) = T(\beta) \circ f$.

- The *slice category* $C / X$ is $1_C \downarrow X$: its objects are maps $f : Y \to X$, and its morphisms are maps $g$ with $f' \circ g = f$.
- The *coslice category* $X / C$ is $X \downarrow 1_C$.
- For $G : D \to C$ and an object $A$ of $C$, the category of *structured arrows* $A \downarrow G$ has objects $(Y, f)$ with $f : A \to G(Y)$, and a morphism $(Y, f) \to (Y', f')$ is a map $g : Y \to Y'$ with $G(g) \circ f = f'$.

**Definition (Weakly initial set).** A family $(B_i)_{i \in I}$ of objects of $E$ indexed by a set is *weakly initial* if each object $X$ admits a morphism $B_i \to X$ for some $i$.

**Definition (Solution set condition).** $G : D \to C$ satisfies the *solution set condition* if for each object $A$ of $C$ there are a set $I$ and maps $f_i : A \to G(B_i)$, $i \in I$, such that every $h : A \to G(X)$ factors as $h = G(g) \circ f_i$ for some $i$ and some $g : B_i \to X$. Equivalently, the $(B_i, f_i)$ form a weakly initial set in $A \downarrow G$.

A category is *locally small* if its Hom sets are sets, not proper classes.

::: mathlib
`CategoryTheory.Comma` · `Mathlib.CategoryTheory.Comma.Basic`

`Comma S T` has fields `left`, `right` and `hom : S.obj left ⟶ T.obj right`, and `Comma.fst`, `Comma.snd` project; a `CommaMorphism` has `left`, `right` and the condition `w`. `Over X` and `Under X` are the slice and the coslice, with `Over.mk`, `Over.homMk`, `Over.forget` and `Under.mk`.

<?decl CategoryTheory.Comma?>
:::

::: mathlib
`CategoryTheory.StructuredArrow` · `Mathlib.CategoryTheory.Comma.StructuredArrow.Basic`

`StructuredArrow S T` for `S : D` and `T : C ⥤ D` is `Comma (Functor.fromPUnit S) T`. Objects are built with `StructuredArrow.mk f` and morphisms with `StructuredArrow.homMk g w`, where `w : f ≫ T.map g = f'`. `StructuredArrow.proj S T` forgets the arrow. The dual is `CostructuredArrow`.

<?decl CategoryTheory.StructuredArrow?>
:::

::: mathlib
`CategoryTheory.SolutionSetCondition` · `Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems`

`SolutionSetCondition.{w} G` is the proposition `∀ A : C, ∃ (ι : Type w) (B : ι → D) (f : ∀ i, A ⟶ G.obj (B i)), ∀ X (h : A ⟶ G.obj X), ∃ i (g : B i ⟶ X), f i ≫ G.map g = h`. The index type in `Type w` is the set. `solutionSetCondition_of_isRightAdjoint` is the easy direction of the theorem below.

<?decl CategoryTheory.SolutionSetCondition?>
:::

### Theorems and proofs

**Theorem (Adjoints and initial objects).** $G : D \to C$ has a left adjoint if and only if $A \downarrow G$ has an initial object for every object $A$ of $C$.

*Proof.* ($\Rightarrow$) Let $F \dashv G$ with unit $\eta$. The object $(F A, \eta_A)$ is initial in $A \downarrow G$. A morphism $(F A, \eta_A) \to (Y, f)$ is a map $g : F A \to Y$ with $G(g) \circ \eta_A = f$, that is, with $\varphi(g) = f$ by the formula of Section 1. Since $\varphi$ is a bijection, there is exactly one such $g$.

($\Leftarrow$) For each $A$ choose an initial object $(F A, \eta_A)$ of $A \downarrow G$. For $h : A \to A'$, the pair $(F A', \eta_{A'} \circ h)$ is an object of $A \downarrow G$. Let $F(h) : F A \to F A'$ be the unique morphism $(F A, \eta_A) \to (F A', \eta_{A'} \circ h)$, so that $G F(h) \circ \eta_A = \eta_{A'} \circ h$. The maps $F(1_A)$ and $1_{F A}$ are both morphisms from $(F A, \eta_A)$ to itself, so they are equal. For $h' : A' \to A''$, both $F(h' \circ h)$ and $F(h') \circ F(h)$ are morphisms from $(F A, \eta_A)$ to $(F A'', \eta_{A''} \circ h' \circ h)$, so they are equal. Thus $F$ is a functor, and $\eta$ is natural. Define
$$\varphi_{A, Y} : \mathrm{Hom}(F A, Y) \to \mathrm{Hom}(A, G Y), \qquad g \mapsto G(g) \circ \eta_A.$$
Initiality of $(F A, \eta_A)$ says exactly that $\varphi_{A, Y}$ is a bijection. For naturality, let $k : Y \to Y'$ and $h : A' \to A$. Then $G(k \circ g) \circ \eta_A = G(k) \circ \varphi(g)$, and
$$\varphi(g \circ F(h)) = G(g) \circ G F(h) \circ \eta_{A'} = G(g) \circ \eta_A \circ h = \varphi(g) \circ h.$$
So $F \dashv G$. $\square$

**Lemma (Initial object from a weakly initial set).** Let $E$ be a locally small category with all small limits, and let $(B_i)_{i \in I}$ be a weakly initial set in $E$. Then $E$ has an initial object.

*Proof.* *A weakly initial object.* Let $P = \prod_i B_i$. For each $X$ there are $i$ and $t : B_i \to X$, and $t \circ p_i : P \to X$. So $P$ is weakly initial.

*Equalize the endomorphisms.* The endomorphisms of $P$ form a set, by local smallness. Let $e : T \to P$ be their joint equalizer, the limit of the diagram with one object $P$ and all endomorphisms as arrows into a second copy of $P$. So $u \circ e = e$ for every $u : P \to P$, and $e$ is a monomorphism, by the same argument as for equalizers (Chapter 4, Section 2). The object $T$ is weakly initial, since $P$ is and there is the map $e : T \to P$.

*Uniqueness.* Let $f, g : T \to X$. Let $k : K \to T$ be an equalizer of $f$ and $g$. Since $P$ is weakly initial, there is $s : P \to K$. The composite $e \circ k \circ s$ is an endomorphism of $P$, so $(e \circ k \circ s) \circ e = e = e \circ 1_T$. Since $e$ is monic, $k \circ s \circ e = 1_T$. So $k$ has a right inverse, and from $f \circ k = g \circ k$ follows $f = f \circ k \circ s \circ e = g \circ k \circ s \circ e = g$. Hence $T$ is initial. $\square$

**Lemma (Comma categories are complete).** If $D$ has all small limits and $G : D \to C$ preserves them, then each $A \downarrow G$ has all small limits, and the projection to $D$ preserves them. If $D$ is locally small, so is $A \downarrow G$.

*Proof.* Let $K : J \to A \downarrow G$, with $K(j) = (Y_j, f_j)$, and let $(L, \pi)$ be a limit of the $Y_j$ in $D$. Then $(G L, G \pi)$ is a limit of the $G Y_j$. The maps $f_j : A \to G Y_j$ form a cone: for $u : j \to k$, the morphism $K(u) = g_u$ satisfies $G(g_u) \circ f_j = f_k$. So there is a unique $f : A \to G L$ with $G(\pi_j) \circ f = f_j$. This makes $(L, f)$ an object and each $\pi_j$ a morphism $(L, f) \to (Y_j, f_j)$. Let $(M, m)$ with $\rho_j : M \to Y_j$ be another cone in $A \downarrow G$. There is a unique $v : M \to L$ with $\pi_j \circ v = \rho_j$. It is a morphism of $A \downarrow G$: $G(\pi_j) \circ G(v) \circ m = G(\rho_j) \circ m = f_j = G(\pi_j) \circ f$, and the $G(\pi_j)$ are jointly monic, so $G(v) \circ m = f$. Hom sets of $A \downarrow G$ are subsets of Hom sets of $D$. $\square$

**Theorem (General adjoint functor theorem).** Let $D$ be locally small with all small limits, and let $G : D \to C$ preserve small limits. Then $G$ has a left adjoint if and only if $G$ satisfies the solution set condition.

*Proof.* If $F \dashv G$, the single $(F A, \eta_A)$ is a solution set, since $h = G(\varphi^{-1} h) \circ \eta_A$. Conversely, fix $A$. The solution set at $A$ is a weakly initial set in $A \downarrow G$. By the second lemma, $A \downarrow G$ is locally small and has all small limits. By the first lemma, it has an initial object. By the theorem on initial objects, $G$ has a left adjoint. $\square$

Without a solution set, the proof would need a product over all objects of $A \downarrow G$.

**Theorem (Special adjoint functor theorem).** Let $D$ be locally small, complete and well-powered, with a small coseparating set of objects, and let $C$ be locally small. Then every functor $G : D \to C$ that preserves small limits has a left adjoint.

Its proof, not given here, checks the solution set condition with subobjects of products of the coseparating objects.

::: mathlib
`CategoryTheory.isRightAdjoint_iff_hasInitial_structuredArrow` · `Mathlib.CategoryTheory.Adjunction.Comma`

The statement is `G.IsRightAdjoint ↔ ∀ A, HasInitial (StructuredArrow A G)`. The direction from an adjunction is `mkInitialOfLeftAdjoint`, and the other direction is built by `leftAdjointOfStructuredArrowInitials` and `adjunctionOfStructuredArrowInitials`. The dual is `isLeftAdjoint_iff_hasTerminal_costructuredArrow`.

<?decl CategoryTheory.isRightAdjoint_iff_hasInitial_structuredArrow?>
:::

::: mathlib
`CategoryTheory.isRightAdjoint_of_preservesLimits_of_solutionSetCondition` · `Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems`

The hypotheses are `[HasLimitsOfSize.{w, w} D]`, `[PreservesLimitsOfSize.{w, w} G]`, `hG : SolutionSetCondition.{w} G` and `[LocallySmall.{w} D]`, and the conclusion is `G.IsRightAdjoint`. The two steps of the lemma are `has_weakly_initial_of_weakly_initial_set_and_hasProducts` and `hasInitial_of_weakly_initial_and_hasWideEqualizers`. The special theorem is `isRightAdjoint_of_preservesLimits_of_isCoseparating`, with `LocallySmall` for `C` and `D`, `WellPowered D` and a small coseparating `ObjectProperty`. Its dual is `isLeftAdjoint_of_preservesColimits_of_isSeparating`.

<?decl CategoryTheory.isRightAdjoint_of_preservesLimits_of_solutionSetCondition?>
<?decl CategoryTheory.isRightAdjoint_of_preservesLimits_of_isCoseparating?>
:::

### Examples

**Example (Free groups from the theorem).** Let $U : \mathbf{Grp} \to \mathbf{Set}$. $\mathbf{Grp}$ is locally small and complete, and $U$ preserves limits. For the solution set condition, fix a set $A$ and let $\kappa$ be an infinite cardinal with $\kappa \ge |A|$. Let $h : A \to U(X)$ be any map. The subgroup $\langle h(A) \rangle$ of $X$ consists of finite products of elements of $h(A)$ and their inverses. There are at most $\kappa$ of them, so $\langle h(A) \rangle$ is isomorphic to a group whose underlying set is a subset of $\kappa$. Let the solution set be all pairs $(B, f)$ where $B$ is a group structure on a subset of $\kappa$ and $f : A \to U(B)$ is a map. This is a set. Each $h$ factors as $A \to \langle h(A) \rangle \hookrightarrow X$ through one of its members. By the theorem, $U$ has a left adjoint: the free group.

**Counterexample (Complete Boolean algebras).** The category of complete Boolean algebras, with maps that preserve all joins and meets, is complete, and its forgetful functor to $\mathbf{Set}$ preserves limits. Gaifman and Hales proved that there is no free complete Boolean algebra on a countably infinite set. So the forgetful functor has no left adjoint, and by the theorem the solution set condition fails: the complete Boolean algebras generated by countably many elements have no bound on their size.

### The library around it

Kan extensions are also defined with comma categories: a left Kan extension of $F$ along $K$ is an initial object among extensions, in Mathlib `Functor.LeftExtension` with `Functor.IsLeftKanExtension`; `Functor.leftKanExtension` chooses one.

Common errors of a learner:

- The order in `StructuredArrow S T`: `S` is an object and `T` a functor, and the arrows go from `S`. The text's $A \downarrow G$ is `StructuredArrow A G`.
- Forgetting `LocallySmall` in the general theorem. Without it, the equalizer of all endomorphisms is not a small limit.

### Exercises

1. (A) Show that $C / X$ has a terminal object, and that it has binary products if $C$ has pullbacks.
2. (A) Show that the initial object of $A \downarrow U$ for $U : \mathbf{Ab} \to \mathbf{Set}$ is the free abelian group on $A$ with the inclusion of generators.
3. (B) Prove the dual of the theorem on initial objects: $F : C \to D$ has a right adjoint if and only if each $F \downarrow Y$ has a terminal object.
4. (B) Use the general theorem to prove that the forgetful functor from commutative rings to sets has a left adjoint.
5. (B) Show that the inclusion of abelian groups into groups satisfies the solution set condition, and deduce again that abelianization exists.
6. (C) Show that the forgetful functor from compact Hausdorff spaces to sets has a left adjoint. Hint: use the general theorem and bound $|X|$ by $2^{2^{|A|}}$ for a compact Hausdorff space $X$ in which the image of $A$ is dense.

### Notes and history

The adjoint functor theorems are due to Freyd, who gave the general theorem and the special one. Mac Lane's book (1971) uses the notation $A \downarrow G$. The existence of free complete Boolean algebras was disproved by Gaifman and, independently, by Hales.

### Reference

<?reference?>
