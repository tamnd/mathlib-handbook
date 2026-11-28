---
title: Lifting properties and the small object argument
kind: theory
modules:
  - Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
  - Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem
  - Mathlib.CategoryTheory.MorphismProperty.Factorization
  - Mathlib.CategoryTheory.MorphismProperty.Retract
  - Mathlib.CategoryTheory.MorphismProperty.RetractArgument
  - Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
  - Mathlib.CategoryTheory.SmallObject.Basic
explains:
  E3: [CategoryTheory.MorphismProperty.llp, CategoryTheory.MorphismProperty.rlp, CategoryTheory.MorphismProperty.le_llp_iff_le_rlp, CategoryTheory.MorphismProperty.IsWeakFactorizationSystem, CategoryTheory.MorphismProperty.IsWeakFactorizationSystem.mk', CategoryTheory.RetractArrow.ofLeftLiftingProperty, CategoryTheory.MorphismProperty.IsStableUnderRetracts, CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape, CategoryTheory.MorphismProperty.HasSmallObjectArgument, CategoryTheory.MorphismProperty.llp_rlp_of_hasSmallObjectArgument]
  E2: [CategoryTheory.MorphismProperty.gc_llp_rlp, CategoryTheory.MorphismProperty.le_llp_rlp, CategoryTheory.MorphismProperty.rlp_llp_rlp, CategoryTheory.MorphismProperty.antitone_llp, CategoryTheory.MorphismProperty.llp_of_isIso, CategoryTheory.MorphismProperty.llp_isMultiplicative, CategoryTheory.MorphismProperty.llp_isStableUnderCobaseChange, CategoryTheory.MorphismProperty.llp_isStableUnderRetracts, CategoryTheory.MorphismProperty.llp_isStableUnderCoproductsOfShape, CategoryTheory.MorphismProperty.rlp_isStableUnderBaseChange, CategoryTheory.MorphismProperty.retracts, CategoryTheory.MorphismProperty.retracts_le_llp_rlp, CategoryTheory.RetractArrow.ofRightLiftingProperty, CategoryTheory.MorphismProperty.llp_eq_of_le_llp_of_hasFactorization_of_isStableUnderRetracts, CategoryTheory.MorphismProperty.rlp_eq_of_le_rlp_of_hasFactorization_of_isStableUnderRetracts, CategoryTheory.MorphismProperty.hasLiftingProperty_of_wfs, CategoryTheory.MorphismProperty.llp_eq_of_wfs, CategoryTheory.MorphismProperty.transfiniteCompositionsOfShape, CategoryTheory.MorphismProperty.IsStableUnderTransfiniteComposition, CategoryTheory.MorphismProperty.smallObjectκ, CategoryTheory.MorphismProperty.llp_rlp_of_hasSmallObjectArgument']
  E1: auto
families: []
requires: [V07, V24.C01, V24.C04, V25.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Lifting properties and the small object argument

### Overview

A projective module $P$ is one for which each map to the target of a surjection lifts through the surjection. This is a *lifting property* of the morphism $0 \to P$ with respect to the surjections. The same form describes cofibrations and fibrations of topological spaces, injective objects, and the classes of a model category. This section studies the two classes $T^{\mathrm{rlp}}$ and ${}^{\mathrm{llp}}T$ of morphisms with a lifting property against a class $T$, and the *weak factorization systems*, pairs of classes that determine each other by lifting and factor each morphism. The retract argument identifies the two classes from a factorization. The small object argument of Quillen builds the factorization from a set of morphisms by a transfinite construction, and Mathlib proves it in full generality.

The section uses the properties of morphisms of Section 1. In the text $g \circ f$ is the textbook composite, and Mathlib writes `f ≫ g`.

### Definitions

**Definition (Lifting property).** A morphism $i : A \to B$ has the *left lifting property* with respect to $p : X \to Y$, and $p$ has the *right lifting property* with respect to $i$, if for each commutative square $p \circ u = v \circ i$ with $u : A \to X$ and $v : B \to Y$ there is a *lift* $\ell : B \to X$ with $\ell \circ i = u$ and $p \circ \ell = v$. For a class $T$ of morphisms, ${}^{\mathrm{llp}}T$ (in Mathlib `T.llp`) is the class of morphisms with the left lifting property with respect to each element of $T$, and $T^{\mathrm{rlp}}$ (`T.rlp`) is the class with the right lifting property.

**Definition (Retract of a morphism).** A morphism $f : X \to Y$ is a *retract* of $g : Z \to W$ if $f$ is a retract of $g$ in the arrow category: there are morphisms $a : X \to Z$, $a' : Z \to X$, $b : Y \to W$ and $b' : W \to Y$ with $a' \circ a = 1_X$, $b' \circ b = 1_Y$, $g \circ a = b \circ f$ and $f \circ a' = b' \circ g$. A class $W$ is *stable under retracts* if each retract of an element of $W$ is in $W$.

**Definition (Weak factorization system).** A pair $(L, R)$ of classes of morphisms is a *weak factorization system* if $L^{\mathrm{rlp}} = R$, ${}^{\mathrm{llp}}R = L$, and each morphism $f$ factors as $f = p \circ i$ with $i \in L$ and $p \in R$.

**Definition (Transfinite composition).** Let $J$ be a well-ordered set with a least element $\bot$. A morphism $f : X \to Y$ is a *transfinite composition of shape $J$* of morphisms in $W$ if there is a functor $F : J \to C$ such that $F(\bot) = X$, $F$ is continuous (for each limit element $j$, $F(j)$ is the colimit of $F(k)$ for $k < j$), each map $F(j) \to F(j+1)$ is in $W$ when $j$ is not maximal, $Y$ is a colimit of $F$ and $f$ is the map from $F(\bot)$ to this colimit.

For $J = \{0 < 1 < \cdots < n\}$, a transfinite composition is an ordinary composite of $n$ morphisms. For $J = \mathbb{N}$ with an added top element, it is the colimit of an infinite sequence.

::: mathlib
`CategoryTheory.MorphismProperty.llp` · `Mathlib.CategoryTheory.MorphismProperty.LiftingProperty`

`T.llp` is the property `fun _ _ f ↦ ∀ ⦃X Y : C⦄ (g : X ⟶ Y) (_ : T g), HasLiftingProperty f g`, and `T.rlp` is the property with the arguments of `HasLiftingProperty` in the other order. The class `HasLiftingProperty i p`, from the folder `LiftingProperties`, asks for a lift for each commutative square `CommSq`.

<?decl CategoryTheory.MorphismProperty.llp?>
:::

### Theorems and proofs

**Theorem (Galois connection).** For classes $T$ and $T'$, $T \le {}^{\mathrm{llp}}T'$ if and only if $T' \le T^{\mathrm{rlp}}$. Thus $T \le {}^{\mathrm{llp}}(T^{\mathrm{rlp}})$, the maps $T \mapsto T^{\mathrm{rlp}}$ and $T \mapsto {}^{\mathrm{llp}}T$ reverse the order, and $({}^{\mathrm{llp}}(T^{\mathrm{rlp}}))^{\mathrm{rlp}} = T^{\mathrm{rlp}}$.

*Proof.* Both sides say that each $i \in T$ has the left lifting property with respect to each $p \in T'$. For the second claim, take $T' = T^{\mathrm{rlp}}$. The maps reverse the order because a property against a larger class is a stronger condition. For the last claim, $T \le {}^{\mathrm{llp}}(T^{\mathrm{rlp}})$ gives $({}^{\mathrm{llp}}(T^{\mathrm{rlp}}))^{\mathrm{rlp}} \le T^{\mathrm{rlp}}$ by the reversal of the order, and the inequality $T^{\mathrm{rlp}} \le ({}^{\mathrm{llp}}(T^{\mathrm{rlp}}))^{\mathrm{rlp}}$ is the dual of the second claim, $T' \le ({}^{\mathrm{llp}}T')^{\mathrm{rlp}}$, for $T' = T^{\mathrm{rlp}}$. ∎

**Theorem (Closure of a left class).** For each class $T$, the class ${}^{\mathrm{llp}}T$ contains the isomorphisms and is stable under composition, cobase change, coproducts, retracts and transfinite composition. Dually, $T^{\mathrm{rlp}}$ contains the isomorphisms and is stable under composition, base change, products and retracts.

*Proof.* Fix $p : X \to Y$ in $T$. If $i$ is an isomorphism, $\ell = u \circ i^{-1}$ is a lift.

For composition, let $i : A \to B$ and $j : B \to B'$ have the left lifting property against $p$, and let $p \circ u = v \circ j \circ i$. First lift in the square $p \circ u = (v \circ j) \circ i$ to get $\ell_1 : B \to X$ with $\ell_1 \circ i = u$ and $p \circ \ell_1 = v \circ j$. Then lift in the square $p \circ \ell_1 = v \circ j$ to get $\ell : B' \to X$ with $\ell \circ j = \ell_1$ and $p \circ \ell = v$. Then $\ell \circ j \circ i = u$.

For cobase change, let $i' : A' \to B'$ be the pushout of $i : A \to B$ along $c : A \to A'$, with $c' : B \to B'$. Given $p \circ u = v \circ i'$, lift in the square $p \circ (u \circ c) = (v \circ c') \circ i$ to get $\ell_0 : B \to X$. The maps $u : A' \to X$ and $\ell_0 : B \to X$ agree on $A$, since $\ell_0 \circ i = u \circ c$. So they give $\ell : B' \to X$ with $\ell \circ i' = u$ and $\ell \circ c' = \ell_0$. Then $p \circ \ell = v$, since both sides agree after $i'$ and after $c'$.

For retracts, let $f$ be a retract of $g \in {}^{\mathrm{llp}}T$ with $a, a', b, b'$ as in the definition, and let $p \circ u = v \circ f$. The square $p \circ (u \circ a') = (v \circ b') \circ g$ commutes, since $v \circ b' \circ g = v \circ f \circ a' = p \circ u \circ a'$. Let $\ell'$ be a lift and put $\ell = \ell' \circ b$. Then $\ell \circ f = \ell' \circ g \circ a = u \circ a' \circ a = u$ and $p \circ \ell = v \circ b' \circ b = v$.

For coproducts, lift on each summand and use the universal property. For transfinite composition, lift step by step along $J$: at a successor step lift as in the case of composition, and at a limit step use the universal property of the colimit. The dual claims follow by applying these to $C^{\mathrm{op}}$. ∎

**Theorem (The retract argument).** Let $f = p \circ i$. If $f$ has the left lifting property with respect to $p$, then $f$ is a retract of $i$. Dually, if $f$ has the right lifting property with respect to $i$, then $f$ is a retract of $p$.

*Proof.* Let $f : X \to Z$, $i : X \to Y$ and $p : Y \to Z$. The square $p \circ i = 1_Z \circ f$ commutes, so there is $\ell : Z \to Y$ with $\ell \circ f = i$ and $p \circ \ell = 1_Z$. Take $a = a' = 1_X$, $b = \ell$ and $b' = p$. Then $b' \circ b = p \circ \ell = 1_Z$, $i \circ a = i = \ell \circ f = b \circ f$, and $f \circ a' = f = p \circ i = b' \circ i$. So $f$ is a retract of $i$. The dual claim is the same proof in $C^{\mathrm{op}}$. ∎

**Theorem (Recognition of a weak factorization system).** Let $L$ and $R$ be classes that are stable under retracts, such that each element of $L$ has the left lifting property with respect to each element of $R$, and each morphism factors as $p \circ i$ with $i \in L$ and $p \in R$. Then $(L, R)$ is a weak factorization system.

*Proof.* By hypothesis $L \le {}^{\mathrm{llp}}R$. Let $f \in {}^{\mathrm{llp}}R$ and factor $f = p \circ i$ with $i \in L$ and $p \in R$. Then $f$ has the left lifting property against $p$, so $f$ is a retract of $i$ by the retract argument. Since $L$ is stable under retracts, $f \in L$. Thus ${}^{\mathrm{llp}}R = L$. The equality $L^{\mathrm{rlp}} = R$ follows in the same way from the dual form of the retract argument. ∎

**Theorem (The small object argument).** Let $I$ be a class of morphisms that permits the small object argument. This holds, for example, when $I$ is essentially small, $C$ has the needed colimits, and there is a regular cardinal $\kappa$ such that $\mathrm{Hom}(A, -)$ preserves the colimits of $\kappa$-indexed transfinite compositions of pushouts of coproducts of elements of $I$, for each source $A$ of an element of $I$. Then:

1. each morphism $f$ factors, functorially in $f$, as $f = p \circ i$ with $i \in {}^{\mathrm{llp}}(I^{\mathrm{rlp}})$ and $p \in I^{\mathrm{rlp}}$;
2. ${}^{\mathrm{llp}}(I^{\mathrm{rlp}})$ is the class of retracts of transfinite compositions of pushouts of coproducts of elements of $I$;
3. $({}^{\mathrm{llp}}(I^{\mathrm{rlp}}), I^{\mathrm{rlp}})$ is a weak factorization system.

*Outline of proof.* Let $f : X \to Y$. Let $S$ be the set of commutative squares from an element $j : A_s \to B_s$ of $I$ to $f$. Form the pushout $X_1$ of $\coprod_s A_s \to \coprod_s B_s$ along the map $\coprod_s A_s \to X$. The map $X \to X_1$ is a pushout of a coproduct of elements of $I$, and $f$ factors through it as $X \to X_1 \to Y$. Repeat with $X_1 \to Y$ in place of $f$, and take colimits at limit steps, along the well-ordered set of the ordinals below $\kappa$. Let $X_\kappa$ be the colimit, with $i : X \to X_\kappa$ and $p : X_\kappa \to Y$. Then $i$ is a transfinite composition of pushouts of coproducts of elements of $I$, so it is in ${}^{\mathrm{llp}}(I^{\mathrm{rlp}})$ by the closure theorem. For a square from $j : A \to B$ in $I$ to $p$, the map $A \to X_\kappa$ factors through some $X_\alpha$ with $\alpha < \kappa$, by the condition on $\mathrm{Hom}(A, -)$. The square is then one of the squares used at step $\alpha + 1$, and the pushout gives the lift $B \to X_{\alpha + 1} \to X_\kappa$. So $p \in I^{\mathrm{rlp}}$. This proves part 1. Part 2 follows from part 1 and the retract argument as in the previous proof: an element $f$ of ${}^{\mathrm{llp}}(I^{\mathrm{rlp}})$ is a retract of the map $i$ of its factorization. Part 3 follows from parts 1 and 2 with the recognition theorem. ∎

Mathlib proves the theorem in the files of the folder `SmallObject`. The functor `Arrow C ⥤ Arrow C` of one step is in `SmallObject.Construction`, the transfinite iteration is in `SmallObject.TransfiniteIteration`, the stability of left classes under transfinite composition is in `SmallObject.TransfiniteCompositionLifting`, and `SmallObject.Basic` collects the results.

### Examples

**Example (Injections and surjections of sets).** In the category of sets, let $L$ be the injections and $R$ the surjections. Given an injection $i : A \to B$, a surjection $p : X \to Y$ and a square $p \circ u = v \circ i$, define $\ell$ on $i(A)$ by $\ell(i(a)) = u(a)$, and for $b \notin i(A)$ choose $\ell(b) \in p^{-1}(v(b))$. This set is not empty since $p$ is surjective. So injections lift against surjections. Each $f : X \to Y$ factors as $X \to X \sqcup Y \to Y$, the inclusion followed by the map that is $f$ on $X$ and the identity on $Y$. The first map is injective and the second is surjective. Both classes are stable under retracts, so $(L, R)$ is a weak factorization system by the recognition theorem.

**Example (A small object argument in sets).** Let $I = \{\emptyset \to \{\ast\}\}$. A square from $\emptyset \to \{\ast\}$ to $p : X \to Y$ is a point $y \in Y$, and a lift is a point of $p^{-1}(y)$. So $I^{\mathrm{rlp}}$ is the class of surjections. A pushout of a coproduct of copies of $\emptyset \to \{\ast\}$ is an inclusion $X \to X \sqcup S$. The first step of the small object argument gives the factorization $X \to X \sqcup Y \to Y$ of the previous example, and the second map is already surjective. The later steps add more copies of the points of $Y$, so the factorization of the argument is functorial but not economical. The class ${}^{\mathrm{llp}}(I^{\mathrm{rlp}})$ is the class of injections, which are retracts of such inclusions, in agreement with part 2.

**Example (Projective and injective modules).** In the category of $R$-modules, the morphism $0 \to P$ is in ${}^{\mathrm{llp}}(\text{surjections})$ if and only if $P$ is projective, since a square from $0 \to P$ to $p : M \to N$ is a map $P \to N$, and a lift is a lift through $p$. Dually, $Q \to 0$ is in $(\text{injections})^{\mathrm{rlp}}$ if and only if $Q$ is injective. For $R = \mathbb{Z}$ and $I = \{0 \to \mathbb{Z}\}$, the first step of the small object argument factors $M \to N$ as $M \to M \oplus F \to N$ with $F$ free on the elements of $N$.

### The library around it

::: mathlib
`CategoryTheory.MorphismProperty.IsWeakFactorizationSystem` · `Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem`

`IsWeakFactorizationSystem W₁ W₂` has the fields `rlp : W₁.rlp = W₂`, `llp : W₂.llp = W₁` and `hasFactorization : HasFactorization W₁ W₂`. The constructor `IsWeakFactorizationSystem.mk'` is the recognition theorem above, with `IsStableUnderRetracts` on both classes.

<?decl CategoryTheory.MorphismProperty.IsWeakFactorizationSystem?>
:::

::: mathlib
`CategoryTheory.MorphismProperty.llp_rlp_of_hasSmallObjectArgument` · `Mathlib.CategoryTheory.SmallObject.Basic`

For `I` with `HasSmallObjectArgument.{w} I`, `I.rlp.llp = (transfiniteCompositions.{w} (coproducts.{w} I).pushouts).retracts`. The variant with a prime fixes the shape of the transfinite compositions to `I.smallObjectκ.ord.ToType`. An instance gives `HasFunctorialFactorization I.rlp.llp I.rlp`.

<?decl CategoryTheory.MorphismProperty.llp_rlp_of_hasSmallObjectArgument?>
:::

The class `HasSmallObjectArgument.{w} I` asks for a regular cardinal `κ` with `IsCardinalForSmallObjectArgument I κ`. The condition on `Hom(A, -)` holds for a suitable `κ` when each source `A` is a presentable object, which is the subject of Chapter 7. The retract argument is `RetractArrow.ofLeftLiftingProperty` and `RetractArrow.ofRightLiftingProperty`.

The factorization axiom lives in the module `Mathlib.CategoryTheory.MorphismProperty.Factorization`. For classes $W_1$ and $W_2$, a term of `MapFactorizationData W₁ W₂ f` is an object `Z` with maps `i` in $W_1$ and `p` in $W_2$ and the equation `fac : i ≫ p = f`. The class `HasFactorization W₁ W₂` asks for such a factorization of each map, and `factorizationData` chooses one. The class `W₁.comp W₂` holds the maps with a factorization, and `comp_eq_top_iff` says that `W₁.comp W₂ = ⊤` if and only if `HasFactorization W₁ W₂`. A functorial factorization, `FunctorialFactorizationData W₁ W₂`, is a functor `Z` on the arrow category with natural maps `i` and `p`, and `HasFunctorialFactorization W₁ W₂` implies `HasFactorization W₁ W₂` by an instance. The construction `FunctorialFactorizationData.functorCategory` extends a functorial factorization to each functor category $J \to C$ objectwise. The equivalence `MapFactorizationData.opEquiv` turns a factorization in $C$ into one in $C^{\mathrm{op}}$ with the roles of $W_1$ and $W_2$ exchanged, and `MapFactorizationData.ofIsEquivalence` moves a factorization along an equivalence of categories.

Common errors of a learner:

- In `HasLiftingProperty i p`, the first argument is the left map. `T.llp f` quantifies over `g` in `T` with `HasLiftingProperty f g`.
- `T.retracts` is the class of retracts of elements of `T`, and `IsStableUnderRetracts T` says `T.retracts ≤ T`. They are different statements.
- The transfinite compositions of Mathlib need a shape `J` with `LinearOrder`, `SuccOrder`, `OrderBot` and `WellFoundedLT`, in a fixed universe. The universe parameter `w` must often be given by hand.

### Exercises

1. (A) Show that ${}^{\mathrm{llp}}T$ is the class of isomorphisms when $T$ is the class of all morphisms.
2. (A) Prove that $T^{\mathrm{rlp}}$ is stable under base change, by the dual of the proof for cobase change.
3. (B) In the category of sets, show that $\{\{0, 1\} \to \{\ast\}\}^{\mathrm{rlp}}$ is the class of injections.
4. (B) Let $(L, R)$ be a weak factorization system. Show that a morphism in $L$ and in $R$ is an isomorphism.
5. (B) Show that in the category of $R$-modules the pair (injections with projective cokernel, surjections) is a weak factorization system. *Hint:* factor $f : M \to N$ as $M \to M \oplus F \to N$ with $F$ free.
6. (C) Let $T$ be a class of morphisms and let $X_0 \to X_1 \to X_2 \to \cdots$ be a sequence of morphisms in ${}^{\mathrm{llp}}T$ with colimit $X_\infty$. Prove that the map $X_0 \to X_\infty$ is in ${}^{\mathrm{llp}}T$. *Hint:* build the lifts $X_n \to X$ by induction and use the universal property of the colimit.

### Notes and history

Lifting properties are in Quillen's *Homotopical algebra* of 1967, with the small object argument for countable sequences. The transfinite form of the argument is in Grothendieck's proof of 1957 that a category with AB5 and a generator has enough injectives, and it goes back to Baer's criterion for injective modules, as the Mathlib file states. Weak factorization systems were named and studied by Bousfield, Adámek, Herrlich, Rosický and Tholen, and others.

The Mathlib files are by Jack McKoen and Joël Riou (lifting properties), Jack McKoen (retracts) and Joël Riou (weak factorization systems, the retract argument, transfinite compositions and the small object argument).

### Reference

<?reference?>
