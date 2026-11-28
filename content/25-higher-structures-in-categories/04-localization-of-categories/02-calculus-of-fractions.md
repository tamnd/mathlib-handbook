---
title: Calculus of fractions
kind: theory
modules:
  - Mathlib.CategoryTheory.Localization.CalculusOfFractions
  - Mathlib.CategoryTheory.Localization.CalculusOfFractions.Fractions
  - Mathlib.CategoryTheory.Localization.CalculusOfFractions.Preadditive
  - Mathlib.CategoryTheory.Localization.Preadditive
  - Mathlib.CategoryTheory.Localization.CalculusOfFractions.OfAdjunction
  - Mathlib.CategoryTheory.Localization.CalculusOfFractions.ComposableArrows
explains:
  E3: [CategoryTheory.MorphismProperty.LeftFraction, CategoryTheory.MorphismProperty.HasLeftCalculusOfFractions, CategoryTheory.MorphismProperty.LeftFractionRel, CategoryTheory.Localization.exists_leftFraction, CategoryTheory.MorphismProperty.LeftFraction.map_eq_iff, CategoryTheory.MorphismProperty.map_eq_iff_postcomp, CategoryTheory.Localization.exists_leftFraction₂, CategoryTheory.Localization.preadditive, CategoryTheory.Localization.functor_additive]
  E2: [CategoryTheory.MorphismProperty.RightFraction, CategoryTheory.MorphismProperty.HasRightCalculusOfFractions, CategoryTheory.MorphismProperty.LeftFraction.map, CategoryTheory.MorphismProperty.LeftFraction.ofHom, CategoryTheory.MorphismProperty.LeftFraction.ofInv, CategoryTheory.MorphismProperty.RightFraction.exists_leftFraction, CategoryTheory.MorphismProperty.LeftFraction.Localization.Q, CategoryTheory.MorphismProperty.LeftFraction.Localization.Hom, CategoryTheory.MorphismProperty.LeftFraction.Localization.homMk_comp_homMk, CategoryTheory.MorphismProperty.LeftFraction₂, CategoryTheory.MorphismProperty.LeftFraction₃, CategoryTheory.Functor.faithful_of_comp_of_hasLeftCalculusOfFractions, CategoryTheory.Localization.functor_additive_iff, CategoryTheory.MorphismProperty.LeftFraction₂.add, CategoryTheory.Localization.liftNatTrans_add]
  E1: auto
families: []
requires: [V24.C01, V24.C04, V25.C01, V25.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Calculus of fractions

### Overview

The construction of Section 1 describes a morphism of $C[W^{-1}]$ as a zigzag of any length, modulo relations that are hard to use. For many classes $W$ a much better description exists. Each morphism is a single fraction $s^{-1} \circ f$, and two fractions are equal when they become equal after one more step. This is the case for the localization of a commutative ring at a multiplicative set, and Ore found the conditions for noncommutative rings. Gabriel and Zisman stated the same conditions for categories. With them, the localization of a preadditive category is preadditive, and two morphisms of $C$ have the same image when a morphism in $W$ equalizes them. This is the basis of the description of morphisms in the derived category of Volume 26.

In the text $g \circ f$ is the textbook composite, and Mathlib writes `f ≫ g`. Thus the left fraction $s^{-1} \circ f$ of the text is the composite `L.map f ≫ inv (L.map s)` in Mathlib.

### Definitions

**Definition (Fractions).** Let $W$ be a class of morphisms of $C$. A *left fraction* from $X$ to $Y$ is a triple $(Y', f, s)$ with $f : X \to Y'$ and $s : Y \to Y'$ in $W$. It stands for $s^{-1} \circ f$. A *right fraction* from $X$ to $Y$ is a triple $(X', s, f)$ with $s : X' \to X$ in $W$ and $f : X' \to Y$. It stands for $f \circ s^{-1}$. For a functor $L$ that inverts $W$, the image of a left fraction is $L(s)^{-1} \circ L(f)$.

**Definition (Left calculus of fractions).** The class $W$ has a *left calculus of fractions* if it is multiplicative and:

1. (Ore condition) for each right fraction $(X', s, f)$ from $X$ to $Y$, there is a left fraction $(Y', g, t)$ from $X$ to $Y$ with $t \circ f = g \circ s$;
2. (cancellation) if $f_1, f_2 : X \to Y$ and $s : X' \to X$ is in $W$ with $f_1 \circ s = f_2 \circ s$, there is $t : Y \to Y'$ in $W$ with $t \circ f_1 = t \circ f_2$.

The *right calculus of fractions* is the dual notion. The class $W$ has a left calculus of fractions if and only if $W^{\mathrm{op}}$ has a right calculus of fractions in $C^{\mathrm{op}}$.

**Definition (Equivalence of left fractions).** Two left fractions $(Y_1, f_1, s_1)$ and $(Y_2, f_2, s_2)$ from $X$ to $Y$ are *equivalent* if there are $t_1 : Y_1 \to Z$ and $t_2 : Y_2 \to Z$ with $t_1 \circ s_1 = t_2 \circ s_2$, $t_1 \circ f_1 = t_2 \circ f_2$ and $t_1 \circ s_1 \in W$.

The Ore condition says that a "wrong way" fraction $f \circ s^{-1}$ can be written the right way as $t^{-1} \circ g$. It is used to compose fractions. The cancellation says that if $s$ becomes invertible, then $f_1 \circ s = f_2 \circ s$ forces $f_1 = f_2$ in the localization, and it must be visible in $C$ by a morphism of $W$.

::: mathlib
`CategoryTheory.MorphismProperty.HasLeftCalculusOfFractions` · `Mathlib.CategoryTheory.Localization.CalculusOfFractions`

The class extends `W.IsMultiplicative` and has the fields `exists_leftFraction`, which for `φ : W.RightFraction X Y` gives `ψ : W.LeftFraction X Y` with `φ.f ≫ ψ.s = φ.s ≫ ψ.f`, and `ext`, which is the cancellation. A `LeftFraction W X Y` has the fields `Y'`, `f : X ⟶ Y'`, `s : Y ⟶ Y'` and `hs : W s`.

<?decl CategoryTheory.MorphismProperty.HasLeftCalculusOfFractions?>
:::

### Theorems and proofs

**Theorem (The category of fractions).** Let $W$ have a left calculus of fractions. The equivalence of left fractions is an equivalence relation. Let $C_W$ be the category whose objects are those of $C$ and whose morphisms $X \to Y$ are the classes of left fractions. The composite of the classes of $(Y', f, s) : X \to Y$ and $(Z', g, t) : Y \to Z$ is the class of $(Z'', h \circ f, u \circ t)$, where $u : Z' \to Z''$ in $W$ and $h : Y' \to Z''$ satisfy $u \circ g = h \circ s$, given by the Ore condition. Then $C_W$ is a category, and the functor $C \to C_W$, $f \mapsto (Y, f, 1_Y)$, is a localization functor for $W$.

*Outline of proof.* Reflexivity and symmetry of the relation are clear. For transitivity, let $(t_1, t_2)$ relate the first and the second fraction and $(t_2', t_3')$ relate the second and the third. Apply the Ore condition to the right fraction formed by $t_2 \circ s_2 \in W$ and $t_2' \circ s_2$, which gives a common target for both relations. The two maps from $Y_2$ to this target agree after $s_2$. They need not agree, and the cancellation gives one more morphism of $W$ that makes them equal. Composing with it gives the relation between the first and the third fraction.

The composite does not depend on the choice of $u$ and $h$, or on the representatives. Each check has the same form: two choices give two fractions, the Ore condition gives a common target, and the cancellation corrects the maps. Associativity and the identity laws follow in the same way.

The functor $C \to C_W$ inverts $W$: for $s : X \to Y$ in $W$, the class of $(Y, 1_Y, s)$ from $Y$ to $X$ is an inverse of the class of $(Y, s, 1_Y)$. Let $F : C \to E$ invert $W$. The functor $\bar F$ sends the class of $(Y', f, s)$ to $F(s)^{-1} \circ F(f)$. This does not depend on the representative: if $t_1 \circ s_1 = t_2 \circ s_2 = w \in W$ and $t_1 \circ f_1 = t_2 \circ f_2$, then $F(t_i)$ is invertible because $F(s_i)$ and $F(w)$ are, and $F(s_1)^{-1} \circ F(f_1) = F(w)^{-1} \circ F(t_1 f_1) = F(w)^{-1} \circ F(t_2 f_2) = F(s_2)^{-1} \circ F(f_2)$. Each class is the composite of the image of $f$ and the inverse of the image of $s$, so $\bar F$ is unique. This is the strict universal property, so the functor is a localization functor. ∎

**Theorem (Morphisms in the localization).** Let $W$ have a left calculus of fractions and let $L : C \to D$ be a localization functor for $W$.

1. Each morphism $LX \to LY$ is $L(s)^{-1} \circ L(f)$ for a left fraction $(Y', f, s)$.
2. Two left fractions have the same image if and only if they are equivalent.
3. For $f_1, f_2 : X \to Y$, $L f_1 = L f_2$ if and only if there is $s : Y \to Z$ in $W$ with $s \circ f_1 = s \circ f_2$.
4. Any two morphisms $LX \to LY$ have the forms $L(s)^{-1} \circ L(f)$ and $L(s)^{-1} \circ L(f')$ with a common $s$.

*Proof.* Parts 1 and 2 hold for the localization $C_W$ of the previous theorem. They hold for $L$ because $L$ and $C \to C_W$ differ by an equivalence, by the uniqueness theorem of Section 1, and the equivalence is compatible with the images of fractions.

For part 3, $L f_i$ is the image of the left fraction $(Y, f_i, 1_Y)$. By part 2, $L f_1 = L f_2$ if and only if there are $t_1, t_2 : Y \to Z$ with $t_1 = t_2$, $t_1 \circ f_1 = t_2 \circ f_2$ and $t_1 \in W$. This is the claim with $s = t_1$.

For part 4, write the two morphisms as $L(s_1)^{-1} \circ L(f_1)$ and $L(s_2)^{-1} \circ L(f_2)$ with $s_i : Y \to Y_i$. Apply the Ore condition to the right fraction $(Y, s_1, s_2)$ from $Y_1$ to $Y_2$. It gives $u : Y_2 \to Z$ in $W$ and $v : Y_1 \to Z$ with $u \circ s_2 = v \circ s_1$. Put $s = u \circ s_2 \in W$. Then $v \circ s_1 = s$, so $L(v)$ is invertible, and $L(s_1)^{-1} \circ L(f_1) = L(s)^{-1} \circ L(v \circ f_1)$. Similarly, $L(s_2)^{-1} \circ L(f_2) = L(s)^{-1} \circ L(u \circ f_2)$. ∎

**Theorem (The localization of a preadditive category).** Let $C$ be preadditive, let $W$ have a left calculus of fractions, and let $L : C \to D$ be a localization functor. Then $D$ has a unique preadditive structure for which $L$ is additive. A functor $G : D \to E$ to a preadditive category is additive if and only if $G \circ L$ is additive.

*Proof.* Each object of $D$ is isomorphic to some $LX$, so it is sufficient to define the addition on $\mathrm{Hom}(LX, LY)$ and to transport it along isomorphisms. By part 4 of the previous theorem, two morphisms are $L(s)^{-1} \circ L(f)$ and $L(s)^{-1} \circ L(f')$ with a common $s$. Define their sum as $L(s)^{-1} \circ L(f + f')$. This does not depend on the choices: two common denominators are related by the Ore condition and the cancellation, as in the theorem on the category of fractions, and the relations respect sums because composition in $C$ is bilinear. The sum is associative and commutative, with $0 = L(0)$ and $-(L(s)^{-1} \circ L(f)) = L(s)^{-1} \circ L(-f)$. Bilinearity of composition in $D$ follows from bilinearity in $C$ after one more use of the Ore condition to put composites in the form of a fraction. The functor $L$ is additive by the definition with $s = 1_Y$. Uniqueness holds because each morphism is $L(s)^{-1} \circ L(f)$ and an additive $L$ forces the formula.

For the last claim, if $G \circ L$ is additive, then $G(L(s)^{-1} \circ L(f + f')) = G(L(s))^{-1} \circ (GL(f) + GL(f'))$, which is the sum of the images. ∎

The same holds with a right calculus of fractions. In Volume 26, the quasi-isomorphisms of the homotopy category of complexes have a left and a right calculus of fractions, and this theorem makes the derived category preadditive.

### Examples

**Example (Localization of a commutative ring).** Let $R$ be a commutative ring, viewed as a preadditive category with one object $\ast$ and $\mathrm{End}(\ast) = R$, and let $W$ be a multiplicative subset $S \subseteq R$. The Ore condition holds: for $s \in S$ and $f \in R$, take $t = s$ and $g = f$, since $s f = f s$. The cancellation holds: if $f_1 s = f_2 s$, then $s f_1 = s f_2$ by commutativity, so take $t = s$. A left fraction is a pair $(f, s)$, and $(f_1, s_1)$ and $(f_2, s_2)$ are equivalent if there are $t_1, t_2$ with $t_1 s_1 = t_2 s_2 \in S$ and $t_1 f_1 = t_2 f_2$. This is the usual relation $u(f_1 s_2 - f_2 s_1) = 0$ for some $u \in S$. So the localized category is the ring $S^{-1}R$, and part 3 of the theorem is the statement that $f/1 = 0$ in $S^{-1}R$ if and only if $u f = 0$ for some $u \in S$.

**Example (Failure of the Ore condition).** Let $C$ have objects $X, Y$ and two morphisms $u, v : X \to Y$ other than identities, as in Section 1, and let $W$ consist of $u$ and the identities. The right fraction $(X, u, v)$ from $Y$ to $Y$ would need $t : Y \to Y'$ in $W$ and $g : Y \to Y'$ with $t \circ v = g \circ u$. The only morphisms out of $Y$ are $1_Y$, so $v = u$, which is false. The left fractions from $X$ to $X$ give only the two morphisms $1_X$ and $a = u^{-1} \circ v$ of the localization, which also contains $a^2$. So the description by fractions fails when the Ore condition fails.

**Example (Faithful localizations).** Let $W$ have a left calculus of fractions, and suppose that each element of $W$ is a monomorphism. If $L f_1 = L f_2$, part 3 gives $s \in W$ with $s \circ f_1 = s \circ f_2$, so $f_1 = f_2$. Thus $L$ is faithful. For a commutative ring $R$ and $S$ with no zero divisors, this says that $R \to S^{-1}R$ is injective.

### The library around it

::: mathlib
`CategoryTheory.MorphismProperty.map_eq_iff_postcomp` · `Mathlib.CategoryTheory.Localization.CalculusOfFractions`

For `L : C ⥤ D` with `[L.IsLocalization W]` and `[W.HasLeftCalculusOfFractions]`, `L.map f₁ = L.map f₂ ↔ ∃ (Z : C) (s : Y ⟶ Z) (_ : W s), f₁ ≫ s = f₂ ≫ s`. This is part 3 of the theorem above. Parts 1 and 2 are `Localization.exists_leftFraction` and `LeftFraction.map_eq_iff`.

<?decl CategoryTheory.MorphismProperty.map_eq_iff_postcomp?>
:::

The file `CalculusOfFractions.Fractions` has `LeftFraction₂` and `LeftFraction₃`, fractions with two or three numerators and one denominator, and `Localization.exists_leftFraction₂` is part 4 of the theorem. The file `CalculusOfFractions.Preadditive` gives `Localization.preadditive L W`, a definition and not an instance, and `Localization.functor_additive`. For the chosen localization `W.Localization` there are instances. The file `Localization.Preadditive` shows that `liftNatTrans` respects sums and zero.

An adjunction gives a calculus of fractions. Let $G \dashv F$ be an adjunction with $G : C_1 \to C_2$, and let $W$ be a multiplicative class of morphisms of $C_1$ that $G$ inverts and that contains each component $\eta_X : X \to F G X$ of the unit. Then `Adjunction.hasLeftCalculusOfFractions` states that $W$ has a calculus of left fractions. In the proof of the Ore condition, the unit $\eta_Y$ is the new denominator. When $F$ is also fully faithful, `Adjunction.isLocalization_leftAdjoint` states that $G$ is a localization functor for $W$. The primed forms `Adjunction.hasLeftCalculusOfFractions'` and `Adjunction.isLocalization_leftAdjoint'` take for $W$ the class of morphisms that $G$ sends to isomorphisms, and `Adjunction.hasRightCalculusOfFractions` and `Adjunction.isLocalization_rightAdjoint` are the dual statements for a right adjoint. The file `CalculusOfFractions.ComposableArrows` proves that a localization functor $L$ with a calculus of left or of right fractions induces an essentially surjective functor on the categories of $n$ composable arrows. The statements are `Localization.essSurj_mapComposableArrows` and `Localization.essSurj_mapComposableArrows_of_hasRightCalculusOfFractions`, about `Functor.mapComposableArrows`. Thus each chain $L X_0 \to L X_1 \to \dots \to L X_n$ in the localization is isomorphic to the image of a chain of $C$.

Common errors of a learner:

- In Mathlib, a left fraction `φ` maps to `φ.map L hL`, which is `L.map φ.f ≫ inv (L.map φ.s)`. In the order of the text this is $L(s)^{-1} \circ L(f)$, and the word "left" refers to the side of the inverse in the Mathlib order.
- `Localization.preadditive L W` must be put in place by `letI` before `L.Additive` makes sense. It is irreducible after its definition, so equalities about it go through the lemmas of the file.
- The calculus of fractions needs a multiplicative class. To use a class that only generates the right one, first replace it by its multiplicative closure, which has the same localization.

### Exercises

1. (A) Let $W$ have a left calculus of fractions. Show that the left fractions $(Y', f, s)$ and $(Y'', t \circ f, t \circ s)$ are equivalent when $t \circ s \in W$.
2. (A) Show that the class of isomorphisms of $C$ has a left and a right calculus of fractions, and that each left fraction is equivalent to one with $s = 1_Y$.
3. (B) Show that $W$ has a left calculus of fractions if and only if $W^{\mathrm{op}}$ has a right calculus of fractions.
4. (B) Let $R$ be a ring that is not commutative and $S \subseteq R$ multiplicative. State the Ore condition and the cancellation for $S$ in the category with one object, and show that they hold when $S$ is contained in the center of $R$.
5. (B) Let $W$ have a left calculus of fractions and let $C$ have a terminal object $1$. Show that $L(1)$ is terminal in $D$ if each morphism $1 \to Z$ in $W$ is an isomorphism. *Hint:* write a morphism $LX \to L(1)$ as a fraction.
6. (C) Prove in detail that the equivalence of left fractions is transitive when $W$ has a left calculus of fractions.

### Notes and history

The Ore condition is from Ore's paper of 1931 on noncommutative rings of fractions. Gabriel and Zisman, in *Calculus of fractions and homotopy theory* of 1967, stated it for categories and proved the description of morphisms. Verdier used it for the derived category, where the quasi-isomorphisms of the homotopy category form a class with a calculus of fractions. Mathlib follows the presentation of Kashiwara and Schapira, *Categories and Sheaves*, Chapter 7.

All the Mathlib files of this section are by Joël Riou.

### Reference

<?reference?>
