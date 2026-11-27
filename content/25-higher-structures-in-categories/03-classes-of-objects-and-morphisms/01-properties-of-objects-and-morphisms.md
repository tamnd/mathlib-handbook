---
title: Properties of objects and morphisms
kind: theory
modules:
  - Mathlib.CategoryTheory.ObjectProperty.Basic
  - Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
  - Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
  - Mathlib.CategoryTheory.MorphismProperty.Basic
  - Mathlib.CategoryTheory.MorphismProperty.Composition
  - Mathlib.CategoryTheory.MorphismProperty.IsInvertedBy
explains:
  E3: [CategoryTheory.ObjectProperty, CategoryTheory.ObjectProperty.FullSubcategory, CategoryTheory.ObjectProperty.fullyFaithfulι, CategoryTheory.ObjectProperty.isoClosure, CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms, CategoryTheory.MorphismProperty, CategoryTheory.MorphismProperty.RespectsIso, CategoryTheory.MorphismProperty.IsMultiplicative, CategoryTheory.MorphismProperty.multiplicativeClosure, CategoryTheory.MorphismProperty.IsInvertedBy]
  E2: [CategoryTheory.ObjectProperty.ι, CategoryTheory.ObjectProperty.lift, CategoryTheory.ObjectProperty.ιOfLE, CategoryTheory.ObjectProperty.inverseImage, CategoryTheory.ObjectProperty.map, CategoryTheory.ObjectProperty.isClosedUnderIsomorphisms_iff_isoClosure_eq_self, CategoryTheory.MorphismProperty.isomorphisms, CategoryTheory.MorphismProperty.monomorphisms, CategoryTheory.MorphismProperty.epimorphisms, CategoryTheory.MorphismProperty.inverseImage, CategoryTheory.MorphismProperty.RespectsIso.of_respects_arrow_iso, CategoryTheory.MorphismProperty.ContainsIdentities, CategoryTheory.MorphismProperty.IsStableUnderComposition, CategoryTheory.MorphismProperty.isomorphisms_le_of_containsIdentities, CategoryTheory.MorphismProperty.multiplicativeClosure_eq_self, CategoryTheory.MorphismProperty.HasTwoOutOfThreeProperty, CategoryTheory.MorphismProperty.HasOfPostcompProperty, CategoryTheory.MorphismProperty.StableUnderInverse, CategoryTheory.MorphismProperty.naturalityProperty, CategoryTheory.MorphismProperty.IsInvertedBy.of_comp, CategoryTheory.MorphismProperty.IsInvertedBy.of_comp_of_reflectsIsomorphisms, CategoryTheory.MorphismProperty.IsInvertedBy.iff_le_inverseImage_isomorphisms, CategoryTheory.MorphismProperty.FunctorsInverting]
  E1: auto
families: []
requires: [V04, V24.C01, V24.C02, V24.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Properties of objects and morphisms

### Overview

Much of the rest of this volume is about classes. A localization inverts a class of morphisms, a model structure has three classes of morphisms, and a torsion theory or a generating family is a class of objects. This section gives the language for these classes. A property of objects is a predicate on the objects of a category, and it gives a full subcategory. A property of morphisms is a predicate on all the morphisms. Each kind of property is a complete lattice under implication, and the section studies the closure conditions that come up again and again: closure under isomorphisms, under identities and under composition, the two-out-of-three property, and the condition that a functor sends each morphism of the class to an isomorphism.

The proofs are short, and later sections use the definitions with no change. In the text $g \circ f$ is the textbook composite, and Mathlib writes `f ≫ g`.

### Definitions

**Definition (Property of objects).** A *property of objects* of a category $C$ is a function $P$ from the objects of $C$ to propositions. The properties are ordered by $P \le Q$ when $P(X)$ implies $Q(X)$ for each $X$. The *full subcategory* $C_P$ has as objects the pairs $(X, h)$ with $h$ a proof of $P(X)$, and $\mathrm{Hom}_{C_P}((X,h),(Y,k)) = \mathrm{Hom}_C(X, Y)$. The inclusion is $\iota_P : C_P \to C$.

For a functor $F : C \to D$ and a property $Q$ of objects of $D$, the *inverse image* $F^{-1}Q$ holds at $X$ when $Q(FX)$ holds. For a property $P$ of objects of $C$, the *image* $F(P)$ holds at $Y$ when $Y \cong FX$ for some $X$ with $P(X)$.

**Definition (Closure under isomorphisms).** A property $P$ is *closed under isomorphisms* if $X \cong Y$ and $P(X)$ imply $P(Y)$. The *isomorphism closure* $\bar P$ holds at $X$ when $X \cong Y$ for some $Y$ with $P(Y)$.

**Definition (Property of morphisms).** A *property of morphisms* $W$ of $C$ gives, for each pair of objects $X, Y$ and each $f : X \to Y$, a proposition $W(f)$. The order is again implication. The main examples are the isomorphisms, the monomorphisms and the epimorphisms of $C$. For $F : C \to D$ and a property $W'$ of morphisms of $D$, the inverse image $F^{-1}W'$ holds at $f$ when $W'(Ff)$ holds.

**Definition (Closure conditions).** Let $W$ be a property of morphisms.

1. $W$ *respects isomorphisms* if $W(f)$ implies $W(f \circ e)$ and $W(e' \circ f)$ for all isomorphisms $e$ and $e'$ for which the composites are defined.
2. $W$ *contains identities* if $W(1_X)$ for each object $X$.
3. $W$ is *stable under composition* if $W(f)$ and $W(g)$ imply $W(g \circ f)$.
4. $W$ is *multiplicative* if it contains identities and is stable under composition. Then $W$ is the class of morphisms of a wide subcategory of $C$.
5. $W$ has the *two-out-of-three property* if, for composable $f$ and $g$, when two of $f$, $g$ and $g \circ f$ are in $W$, the third is in $W$ too.

**Definition (Inverted by a functor).** A functor $F : C \to D$ *inverts* $W$ if $Ff$ is an isomorphism for each $f$ with $W(f)$. The functors that invert $W$ form a full subcategory of the functor category $D^C$.

::: mathlib
`CategoryTheory.MorphismProperty` · `Mathlib.CategoryTheory.MorphismProperty.Basic`

`MorphismProperty C` is the type `∀ ⦃X Y : C⦄ (_ : X ⟶ Y), Prop`, with an instance of `CompleteBooleanAlgebra`. The order is implication, so `W ≤ W'` means `∀ f, W f → W' f`. The property of objects `ObjectProperty C` is the abbreviation `C → Prop`, and it gets its lattice structure from the lattice of functions to `Prop`.

<?decl CategoryTheory.MorphismProperty?>
:::

### Theorems and proofs

**Theorem (Full subcategories).** The inclusion $\iota_P : C_P \to C$ is full and faithful. If $F : D \to C$ is a functor and $P(FX)$ holds for each $X$, then $F$ factors as $\iota_P \circ \tilde F$ for a unique functor $\tilde F : D \to C_P$, and $\tilde F$ is full or faithful when $F$ is. If $P \le P'$, the evident functor $C_P \to C_{P'}$ is full and faithful.

*Proof.* The map $\mathrm{Hom}_{C_P}((X,h),(Y,k)) \to \mathrm{Hom}_C(X,Y)$ given by $\iota_P$ is the identity, so it is bijective. Put $\tilde F X = (FX, h_X)$ with $h_X$ the given proof, and $\tilde F f = Ff$. Then $\iota_P \circ \tilde F = F$ on the nose. Uniqueness holds because an object of $C_P$ is determined by its underlying object, since any two proofs of $P(X)$ are equal, and a morphism of $C_P$ is a morphism of $C$. Since $\iota_P$ is the identity on Hom sets, the maps on Hom sets of $\tilde F$ and of $F$ are the same maps, which gives the claim about full and faithful. The last claim follows as the first one did. ∎

In Mathlib $\iota_P$ is `ObjectProperty.ι P`, the proof of the first claim is `ObjectProperty.fullyFaithfulι`, the factorization is `ObjectProperty.lift`, and the comparison for $P \le P'$ is `ObjectProperty.ιOfLE`.

**Theorem (Isomorphism closure).** The isomorphism closure $\bar P$ is the smallest property that is closed under isomorphisms and greater than or equal to $P$. In particular, $P$ is closed under isomorphisms if and only if $\bar P = P$.

*Proof.* Since $X \cong X$, $P \le \bar P$. If $X' \cong X$ and $\bar P(X)$ holds, then $X \cong Y$ with $P(Y)$, so $X' \cong Y$ by composition, and $\bar P(X')$ holds. Thus $\bar P$ is closed under isomorphisms. If $Q \ge P$ is closed under isomorphisms and $\bar P(X)$ holds with $X \cong Y$ and $P(Y)$, then $Q(Y)$ holds, so $Q(X)$ holds. Thus $\bar P \le Q$. For the last claim, if $P$ is closed under isomorphisms, take $Q = P$ to get $\bar P \le P$, and so $\bar P = P$. The converse holds because $\bar P$ is closed under isomorphisms. ∎

The inverse image $F^{-1}Q$ is closed under isomorphisms when $Q$ is, since a functor sends isomorphisms to isomorphisms. The image $F(P)$ is closed under isomorphisms by its definition, whatever $P$ is.

**Theorem (A test by isomorphisms of arrows).** A property of morphisms $W$ respects isomorphisms if and only if it is closed under isomorphisms in the arrow category $\mathrm{Arr}(C)$. That is, if $f : X \to Y$ and $g : X' \to Y'$ and there are isomorphisms $a : X \to X'$ and $b : Y \to Y'$ with $g \circ a = b \circ f$, then $W(f)$ implies $W(g)$.

*Proof.* Suppose $W$ respects isomorphisms. With $a$, $b$ as in the statement, $g = b \circ f \circ a^{-1}$, so $W(g)$ follows from $W(f)$ in two steps. Conversely, suppose the arrow condition. Let $e : X' \to X$ be an isomorphism and $W(f)$ with $f : X \to Y$. The square with $a = e^{-1}$ and $b = 1_Y$ commutes, since $(f \circ e) \circ e^{-1} = f$. So $W(f \circ e)$. The case of $e' \circ f$ uses $a = 1_X$ and $b = e'$. ∎

**Theorem (Identities and isomorphisms).** If $W$ contains identities and respects isomorphisms, then $W$ contains each isomorphism of $C$. If $W$ is stable under composition and contains each isomorphism, then $W$ respects isomorphisms.

*Proof.* For an isomorphism $e : X \to Y$, write $e = e \circ 1_X$. Since $W(1_X)$ holds and $W$ respects isomorphisms, $W(e)$ holds. For the second claim, if $W(f)$ and $e$ is an isomorphism, then $W(e)$ holds, so $W(f \circ e)$ and $W(e \circ f)$ hold by stability under composition. ∎

**Theorem (Multiplicative closure).** For each property $W$ there is a smallest multiplicative property $W^{\ast}$ with $W \le W^{\ast}$. A morphism is in $W^{\ast}$ if and only if it is an identity or a finite composite $f_n \circ \cdots \circ f_1$ with $n \ge 1$ and each $f_i$ in $W$. And $W^{\ast} = W$ if and only if $W$ is multiplicative.

*Proof.* Let $V$ be the class of identities and finite composites of morphisms in $W$. It contains $W$ (take $n = 1$) and the identities. A composite of two finite composites is a finite composite, and a composite with an identity changes nothing, so $V$ is multiplicative. A multiplicative $W' \ge W$ contains each identity and, by induction on $n$, each composite $f_n \circ \cdots \circ f_1$ with $f_i \in W$. So $V \le W'$, and $V$ is the smallest one, which is $W^{\ast}$. If $W$ is multiplicative, take $W' = W$ to get $W^{\ast} \le W$, so $W^{\ast} = W$. The converse holds because $W^{\ast}$ is multiplicative. ∎

Mathlib defines `multiplicativeClosure W` as an inductive predicate with three rules: each element of $W$, each identity, and $g \circ f$ for $f$ in the closure and $g$ in $W$. The induction in the proof above is the induction on these rules. The variant `multiplicativeClosure'` adds the new factor on the other side, and the two are equal.

**Theorem (Inverting functors).** Let $F : C \to D$ and $G : D \to E$ be functors, and let $W$ be a property of morphisms of $C$.

1. $F$ inverts $W$ if and only if $W \le F^{-1}(\mathrm{Iso}_D)$, where $\mathrm{Iso}_D$ is the class of isomorphisms of $D$.
2. If $F$ inverts $W$, then $G \circ F$ inverts $W$.
3. If $G$ reflects isomorphisms and $G \circ F$ inverts $W$, then $F$ inverts $W$.
4. The property $F^{-1}(\mathrm{Iso}_D)$ is multiplicative, respects isomorphisms and has the two-out-of-three property. Each functor inverts $\mathrm{Iso}_C$.

*Proof.* Part 1 is the definition read in the order of properties. For part 2, a functor sends isomorphisms to isomorphisms, so $G(Ff)$ is an isomorphism when $Ff$ is. For part 3, if $W(f)$, then $G(Ff)$ is an isomorphism, and since $G$ reflects isomorphisms, $Ff$ is an isomorphism.

For part 4, $F(1_X) = 1_{FX}$ is an isomorphism, and $F(g \circ f) = Fg \circ Ff$ is an isomorphism when $Ff$ and $Fg$ are. So the property is multiplicative. For two-out-of-three, it is sufficient to show that the isomorphisms of $D$ have it. If $u$ and $v \circ u$ are isomorphisms, then $v = (v \circ u) \circ u^{-1}$ is an isomorphism. If $v$ and $v \circ u$ are isomorphisms, then $u = v^{-1} \circ (v \circ u)$ is an isomorphism. The case with $u$ and $v$ in the class is closure under composition. The property respects isomorphisms by the previous theorem. Last, if $e$ is an isomorphism of $C$, then $Fe$ has the inverse $F(e^{-1})$. ∎

Part 4 shows that a class can be inverted by some functor only if it is contained in a multiplicative class with two-out-of-three. Chapter 4 constructs the universal functor that inverts $W$, the localization.

### Examples

**Example (Finite sets and finite-dimensional spaces).** In the category of sets, the property "$X$ is finite" is closed under isomorphisms, and its full subcategory is equivalent to the category with objects $\{1, \dots, n\}$. The property "$X$ has exactly the elements $1, \dots, n$ for some $n$" is not closed under isomorphisms. Its closure is the property "finite". Its full subcategory is still equivalent to the full subcategory of finite sets, since each finite set is isomorphic to such a set.

**Example (Monomorphisms and two-out-of-three).** The monomorphisms of a category are multiplicative and respect isomorphisms. If $g \circ f$ is a monomorphism, then $f$ is a monomorphism, since $f \circ a = f \circ b$ gives $g \circ f \circ a = g \circ f \circ b$. In Mathlib this is the condition `HasOfPostcompProperty` for the monomorphisms. But the monomorphisms do not have the two-out-of-three property in the category of sets. The inclusion $f : \{0\} \to \{0, 1\}$ and the map $g : \{0, 1\} \to \{0\}$ give $g \circ f = 1_{\{0\}}$, which is a monomorphism, and $f$ is a monomorphism, but $g$ is not.

**Example (A functor and its inverted class).** Let $F$ be the abelianization functor from groups to abelian groups. For each group $G$, the quotient map $q_G : G \to G^{\mathrm{ab}}$ is inverted by $F$, because $F q_G$ is an isomorphism $G^{\mathrm{ab}} \to (G^{\mathrm{ab}})^{\mathrm{ab}}$. The class $F^{-1}(\mathrm{Iso})$ consists of the homomorphisms $\varphi : G \to H$ that induce isomorphisms $G^{\mathrm{ab}} \to H^{\mathrm{ab}}$. It contains the inclusion $A_5 \to A_5 \times A_5$ as the first factor, since both groups are perfect and have trivial abelianization. So $F$ inverts morphisms that are not isomorphisms of groups, and the class $F^{-1}(\mathrm{Iso})$ is much larger than the class of isomorphisms.

**Example (Naturality as a property).** For functors $F_1, F_2 : C \to D$ and a family of morphisms $\alpha_X : F_1 X \to F_2 X$, the property $N_\alpha(f) : F_2 f \circ \alpha_X = \alpha_Y \circ F_1 f$ is a property of morphisms. It is multiplicative, and it is stable under inverses: if $e$ is an isomorphism with $N_\alpha(e)$, then $N_\alpha(e^{-1})$. So $\alpha$ is natural if it is natural for a class of morphisms whose multiplicative closure, together with inverses, is all of $C$. This is the Mathlib name `naturalityProperty`, and it is a common tool to prove naturality on a generating class only.

### The library around it

::: mathlib
`CategoryTheory.ObjectProperty.FullSubcategory` · `Mathlib.CategoryTheory.ObjectProperty.FullSubcategory`

The structure `FullSubcategory P` has the fields `obj : C` and `property : P obj`. A morphism of `FullSubcategory P` is a structure with one field `hom`, so `f.hom` is the underlying morphism of `C`. The constructor `homMk` goes the other way, and `isoMk` makes an isomorphism from an isomorphism of `C`. The inclusion `P.ι` has `P.fullyFaithfulι : P.ι.FullyFaithful`.

<?decl CategoryTheory.ObjectProperty.FullSubcategory?>
:::

::: mathlib
`CategoryTheory.MorphismProperty.IsInvertedBy` · `Mathlib.CategoryTheory.MorphismProperty.IsInvertedBy`

`W.IsInvertedBy F` is `∀ ⦃X Y : C⦄ (f : X ⟶ Y), W f → IsIso (F.map f)`. The lemma `IsInvertedBy.iff_le_inverseImage_isomorphisms` is the first part of the theorem above, and it holds by `Iff.rfl`. The full subcategory of the functors that invert `W` is `W.FunctorsInverting D`, built with `ObjectProperty.FullSubcategory`.

<?decl CategoryTheory.MorphismProperty.IsInvertedBy?>
:::

In `Mathlib.CategoryTheory.MorphismProperty.Basic`, `RespectsIso P` is the abbreviation `P.Respects (isomorphisms C)`. The class `Respects P Q` asks for stability under composition on both sides with elements of `Q`, and it splits into `RespectsLeft` and `RespectsRight`. In `Mathlib.CategoryTheory.MorphismProperty.Composition`, `HasTwoOutOfThreeProperty W` extends `IsStableUnderComposition W`, `HasOfPostcompProperty W W` and `HasOfPrecompProperty W W`. The file `MorphismProperty.Limits` adds stability under base change and cobase change, which Section 3 and Chapter 6 use.

Common errors of a learner:

- `W ≤ W'` for properties of morphisms is a statement for all objects and all morphisms. To use it at one `f`, write `h f hf`, with the implicit objects filled in by unification.
- The properties `ObjectProperty.map` and `MorphismProperty.map` are closed under isomorphisms by definition. The strict image `strictMap` is not, and it is the right choice only when equality of objects matters.

### Exercises

1. (A) Show that a property of objects $P$ and its isomorphism closure $\bar P$ give equivalent full subcategories.
2. (A) Show that the epimorphisms of a category are multiplicative and respect isomorphisms, and that $W(g \circ f)$ implies $W(g)$ for $W$ the epimorphisms.
3. (B) Let $W$ be a property of morphisms that respects isomorphisms. Show that $W^{\ast}$ respects isomorphisms.
4. (B) Show that the isomorphisms of a category have the *two-out-of-six property*: if $f : W \to X$, $g : X \to Y$ and $h : Y \to Z$ are such that $g \circ f$ and $h \circ g$ are isomorphisms, then $f$, $g$, $h$ and $h \circ g \circ f$ are isomorphisms.
5. (B) Let $F \dashv G$ be an adjunction with unit $\eta$. Show that $F$ inverts each $\eta_X$ if $G$ is full and faithful. *Hint:* use the counit and a triangle identity.
6. (C) Let $C$ have two objects $X$ and $Y$ and the morphisms $1_X$, $1_Y$, $f : X \to Y$, $g : Y \to X$ and $e = f \circ g : Y \to Y$, with $g \circ f = 1_X$. Let $W$ be the class $\{1_X, 1_Y, e\}$. Show that $W$ is multiplicative and has the two-out-of-three property, but that no functor $F$ with domain $C$ has $W = F^{-1}(\mathrm{Iso})$. *Hint:* an idempotent that is an isomorphism is an identity.

### Notes and history

Classes of morphisms closed under composition and identities are as old as categories, since a wide subcategory is such a class. The two-out-of-three property is a part of Quillen's axioms for model categories of 1967, and the Gabriel-Zisman book of 1967 on the calculus of fractions studies the classes inverted by a functor. The Mathlib files put these notions in one place so that the localization of Chapter 4, the triangulated categories of Chapter 5 and the topologies of Chapter 6 use the same names.

The Mathlib files are by Joël Riou (the basic file on properties of objects, closure under isomorphisms and inverted classes), Kim Morrison, Reid Barton and Joël Riou (full subcategories), Andrew Yang (properties of morphisms) and Andrew Yang, Joël Riou and Aras Ergus (composition).

### Reference

<?reference?>
