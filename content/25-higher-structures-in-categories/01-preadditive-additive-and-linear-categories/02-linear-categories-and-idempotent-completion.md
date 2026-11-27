---
title: Linear categories and idempotent completion
kind: theory
modules:
  - Mathlib.CategoryTheory.Linear.Basic
  - Mathlib.CategoryTheory.Linear.LinearFunctor
  - Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
  - Mathlib.CategoryTheory.Idempotents.Basic
  - Mathlib.CategoryTheory.Idempotents.Karoubi
  - Mathlib.CategoryTheory.Idempotents.KaroubiKaroubi
explains:
  E3: [CategoryTheory.Linear, CategoryTheory.Functor.Linear, CategoryTheory.preadditiveYoneda, CategoryTheory.full_preadditiveYoneda, CategoryTheory.IsIdempotentComplete, CategoryTheory.Idempotents.isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent, CategoryTheory.Idempotents.Karoubi, CategoryTheory.Idempotents.toKaroubi, CategoryTheory.Idempotents.instIsIdempotentCompleteKaroubi, CategoryTheory.Idempotents.toKaroubi_isEquivalence]
  E2: [CategoryTheory.Linear.preadditiveIntLinear, CategoryTheory.Linear.leftComp, CategoryTheory.Linear.instAlgebraEnd, CategoryTheory.Functor.mapLinearMap, CategoryTheory.preadditiveYonedaObj, CategoryTheory.faithful_preadditiveYoneda, CategoryTheory.preadditiveCoyoneda, CategoryTheory.Idempotents.idem_of_id_sub_idem, CategoryTheory.Idempotents.isIdempotentComplete_iff_idempotents_have_kernels, CategoryTheory.Idempotents.isIdempotentComplete_of_abelian, CategoryTheory.Idempotents.isIdempotentComplete_iff_opposite, CategoryTheory.Idempotents.Karoubi.Hom, CategoryTheory.Idempotents.fullyFaithfulToKaroubi, CategoryTheory.Idempotents.Karoubi.decompId, CategoryTheory.Idempotents.Karoubi.retract, CategoryTheory.Idempotents.instPreadditiveKaroubi, CategoryTheory.Idempotents.KaroubiKaroubi.equivalence]
  E1: auto
families: []
requires: [V06, V07, V24.C02, V24.C03, V24.C04, V24.C08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Linear categories and idempotent completion

### Overview

In many categories of algebra the morphisms form modules over a commutative ring, not only abelian groups. Such a category is *linear* over the ring. This section gives the definition, the linear functors, and the Yoneda embedding of a preadditive category into functors with values in abelian groups. The second half is about idempotents. An idempotent $p = p \circ p$ in a category of modules always has an image, and $X$ is the direct sum of the images of $p$ and $1 - p$. In a general category an idempotent need not split. The *Karoubi envelope* adds the missing images in a universal way.

In the text $g \circ f$ is the textbook composite, and Mathlib writes `f ≫ g`.

### Definitions

**Definition (Linear category).** Let $R$ be a semiring and $C$ a preadditive category. An *$R$-linear structure* on $C$ is an $R$-module structure on each $\mathrm{Hom}(X, Y)$ such that $g \circ (r f) = r (g \circ f)$ and $(r g) \circ f = r (g \circ f)$ for all $r \in R$.

Each preadditive category is $\mathbb{Z}$-linear in exactly one way, by the multiples $n f$. Mathlib records this as `Linear.preadditiveIntLinear`. For a commutative ring $R$, the endomorphism ring $\mathrm{End}(X)$ of an object of an $R$-linear category is an $R$-algebra.

**Definition (Linear functor).** An additive functor $F$ between $R$-linear categories is *linear* if $F(r f) = r F(f)$. Then $F$ gives an $R$-linear map $\mathrm{Hom}(X, Y) \to \mathrm{Hom}(FX, FY)$, called `Functor.mapLinearMap`.

**Definition (Idempotent, splitting).** An *idempotent* is an endomorphism $p : X \to X$ with $p \circ p = p$. A *splitting* of $p$ is an object $Y$ with maps $i : Y \to X$ and $e : X \to Y$ such that $e \circ i = 1_Y$ and $i \circ e = p$. The category is *idempotent complete* if each idempotent has a splitting.

**Definition (Karoubi envelope).** The *Karoubi envelope* $\mathrm{Kar}(C)$ has as objects the pairs $(X, p)$ with $p$ an idempotent of $X$. A morphism $(X, p) \to (Y, q)$ is a map $f : X \to Y$ of $C$ with $f = q \circ f \circ p$. Composition is the composition of $C$, and the identity of $(X, p)$ is $p$. The functor $\iota : C \to \mathrm{Kar}(C)$ sends $X$ to $(X, 1_X)$ and $f$ to $f$.

The condition $f = q f p$ is equivalent to the two conditions $q f = f$ and $f p = f$. With it, $p$ is a two-sided unit: $f \circ p = f$ and $q \circ f = f$. So $\mathrm{Kar}(C)$ is a category, and $\iota$ is full and faithful, since a morphism $(X, 1) \to (Y, 1)$ is any map $X \to Y$.

::: mathlib

`CategoryTheory.Idempotents.Karoubi` · `Mathlib.CategoryTheory.Idempotents.Karoubi`

A structure with fields `X`, `p` and `idem : p ≫ p = p`. A morphism `Karoubi.Hom P Q` has a field `f` and the condition `comm : f = P.p ≫ f ≫ Q.p`. The functor `toKaroubi C` is fully faithful by `fullyFaithfulToKaroubi`. If `C` is preadditive, so is `Karoubi C`, and `toKaroubi C` is additive.

<?decl CategoryTheory.Idempotents.Karoubi?>
:::

### Theorems and proofs

**Theorem (Preadditive Yoneda embedding).** Let $C$ be preadditive. The functor $C \to \mathrm{Fun}(C^{\mathrm{op}}, \mathrm{Ab})$, $Y \mapsto \mathrm{Hom}(-, Y)$, is full and faithful.

*Proof.* Each $\mathrm{Hom}(X, Y)$ is an abelian group, and precomposition with $u : X' \to X$ is a group homomorphism by bilinearity, so the functor is well defined. Compose it with the forgetful functor $\mathrm{Ab} \to \mathrm{Set}$ applied pointwise. The result is the Yoneda embedding of Volume 24, Chapter 3, which is full and faithful. A natural transformation $\alpha : \mathrm{Hom}(-, Y) \to \mathrm{Hom}(-, Y')$ of group valued functors is in particular a natural transformation of set valued functors. By Yoneda, $\alpha_X(g) = f \circ g$ for $f = \alpha_Y(1_Y)$. So $\alpha$ is the image of $f$, and the functor is full. Two maps with the same image have the same image in $\mathrm{Set}$, so they are equal by Yoneda. $\square$

The value $\mathrm{Hom}(-, Y)$ has more structure: $\mathrm{End}(Y)$ acts by $s \cdot g = s \circ g$, and precomposition commutes with this action. Mathlib uses this in `preadditiveYonedaObj`, which has values in modules over `End Y`.

**Theorem (Splitting by equalizers).** An idempotent $p : X \to X$ splits if and only if the equalizer of $1_X$ and $p$ exists. Hence $C$ is idempotent complete if and only if these equalizers exist for all idempotents.

*Proof.* Let $p = i \circ e$ with $e \circ i = 1$. Then $p \circ i = i \circ e \circ i = i$. Let $g : T \to X$ with $p \circ g = g$. Then $g = i \circ (e \circ g)$, so $g$ factors through $i$. The factor is unique, because $i$ has the left inverse $e$ and is a monomorphism. So $i$ is an equalizer of $1$ and $p$. Conversely, let $i : Y \to X$ be an equalizer of $1$ and $p$. Since $p \circ p = 1 \circ p$, the map $p$ factors as $p = i \circ e$ for a unique $e : X \to Y$. Then $i \circ e \circ i = p \circ i = i = i \circ 1_Y$, and $i$ is mono as an equalizer, so $e \circ i = 1_Y$. $\square$

**Corollary (Kernels of idempotents).** A preadditive category is idempotent complete if and only if each idempotent has a kernel. In particular, an abelian category is idempotent complete.

*Proof.* In a preadditive category, the equalizer of $a$ and $b$ is the kernel of $a - b$. If $p$ is idempotent, then $1 - p$ is idempotent, because $(1 - p)(1 - p) = 1 - 2p + p^2 = 1 - p$. The equalizer of $1$ and $1 - p$ is the kernel of $p$. As $p$ runs over all idempotents, so does $1 - p$. The theorem gives the claim. Abelian categories have all kernels. $\square$

**Theorem (Karoubi envelope).** The category $\mathrm{Kar}(C)$ is idempotent complete. Each object $(X, p)$ is a retract of $\iota X$. If $C$ is idempotent complete, then $\iota$ is an equivalence.

*Proof.* Let $\varphi$ be an idempotent of $(X, p)$, so $\varphi = p \varphi p$ and $\varphi \circ \varphi = \varphi$ in $C$. Then $(X, \varphi)$ is an object. The map $\varphi$ is a morphism $i : (X, \varphi) \to (X, p)$, since $p \varphi \varphi = \varphi$, and a morphism $e : (X, p) \to (X, \varphi)$, since $\varphi \varphi p = \varphi$. Now $e \circ i = \varphi \circ \varphi = \varphi$, the identity of $(X, \varphi)$, and $i \circ e = \varphi$. So $\varphi$ splits.

For the retract, $p$ is a morphism $(X, p) \to (X, 1)$ and a morphism $(X, 1) \to (X, p)$. Their composite $(X, p) \to (X, 1) \to (X, p)$ is $p \circ p = p$, the identity of $(X, p)$.

Let $C$ be idempotent complete. The functor $\iota$ is full and faithful, so it remains to show that it is essentially surjective. Let $(X, p)$ be an object and $p = i \circ e$ a splitting in $C$, with $e \circ i = 1_Y$. Then $i : (Y, 1) \to (X, p)$ is a morphism, since $p \circ i \circ 1 = i e i = i$. Also $e : (X, p) \to (Y, 1)$ is a morphism, since $e \circ p = e i e = e$. The composites are $e \circ i = 1_Y$ and $i \circ e = p$, the two identities. So $(X, p) \cong \iota Y$. $\square$

Apply the theorem to $\mathrm{Kar}(C)$, which is idempotent complete. Then $\iota : \mathrm{Kar}(C) \to \mathrm{Kar}(\mathrm{Kar}(C))$ is an equivalence. This is `KaroubiKaroubi.equivalence`.

### Examples

**Example (Modules over a commutative ring).** Let $R$ be commutative. Then `ModuleCat R` is $R$-linear, the action on $\mathrm{Hom}(M, N)$ being $(r f)(m) = r f(m)$. It is abelian, so it is idempotent complete. A splitting of $p$ is the submodule $p(M)$, with the inclusion and the map $m \mapsto p(m)$.

**Counterexample (Free modules over a product ring).** Let $A = \mathbb{Z} \times \mathbb{Z}$ and let $C$ be the full subcategory of `ModuleCat A` of the free modules of finite rank. The idempotent $p(a, b) = (a, 0)$ of $A$ does not split in $C$. A splitting would make $Y$ isomorphic to $p(A) = \mathbb{Z} \times 0$. For a free module $F \cong A^n$, the parts $(1, 0) F \cong \mathbb{Z}^n$ and $(0, 1) F \cong \mathbb{Z}^n$ have the same rank. For $\mathbb{Z} \times 0$ the ranks are $1$ and $0$. So $C$ is not idempotent complete. Its Karoubi envelope is equivalent to the category of finitely generated projective $A$-modules, because each such module is the image of an idempotent matrix.

**Example (One object).** Let $C$ have one object with endomorphism ring $R$. An object of $\mathrm{Kar}(C)$ is an idempotent $e \in R$, and a morphism $e \to f$ is an element $x$ with $x = f x e$. For $R = k \times k$ with a field $k$, the idempotents $(1, 0)$ and $(0, 1)$ are new objects with the endomorphism ring $k$, and the object $(1, 1)$ is their biproduct.

### The library around it

::: mathlib

`CategoryTheory.IsIdempotentComplete` · `Mathlib.CategoryTheory.Idempotents.Basic`

A class with one field, `idempotents_split`. Note the Mathlib order: the splitting is `i : Y ⟶ X`, `e : X ⟶ Y` with `i ≫ e = 𝟙 Y` and `e ≫ i = p`. The file proves `isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent`, `isIdempotentComplete_iff_idempotents_have_kernels`, the instance `isIdempotentComplete_of_abelian`, and the invariance under equivalence and under the opposite category.

<?decl CategoryTheory.IsIdempotentComplete?>
:::

::: mathlib

`CategoryTheory.Idempotents.karoubiUniversal` · `Mathlib.CategoryTheory.Idempotents.FunctorExtension`

The universal property: for an idempotent complete `D`, extension of functors along `toKaroubi C` gives an equivalence `(C ⥤ D) ≌ (Karoubi C ⥤ D)`. The file `Idempotents.Biproducts` shows that `Karoubi C` has finite biproducts when `C` has them. Together with `Mat_` from Section 1, this gives the idempotent complete additive envelope of a preadditive category.

<?decl CategoryTheory.Idempotents.karoubiUniversal?>
:::

::: mathlib

`CategoryTheory.Linear` · `Mathlib.CategoryTheory.Linear.Basic`

A class over a semiring `R` with fields `homModule`, `smul_comp` and `comp_smul`. The linear maps of composition are `Linear.leftComp` and `Linear.rightComp`. The class `Functor.Linear R F` is in `Linear.LinearFunctor`.

<?decl CategoryTheory.Linear?>
:::

Common errors of a learner:

- The identity of `P : Karoubi C` is `P.p`, not `𝟙 P.X`. The lemma `Karoubi.id_f` states this. A morphism `P ⟶ Q` with `f = 𝟙` exists only if the idempotents allow it.
- `preadditiveYoneda` has values in `AddCommGrpCat`. The plain `yoneda` has values in types. For the module structure over `End Y`, use `preadditiveYonedaObj`.

### Exercises

1. (A) Show that an identity morphism is an idempotent with the trivial splitting, and that a splitting of $p$ is unique up to a unique isomorphism compatible with $i$ and $e$.
2. (A) In a preadditive category, show that an idempotent $p$ and $1 - p$ have $p (1 - p) = 0 = (1 - p) p$.
3. (B) Let $C$ be preadditive and idempotent complete, with binary biproducts. Let $p$ split through $Y$ and $1 - p$ split through $Z$. Show that $X \cong Y \oplus Z$. *Hint:* use the total identity of Section 1.
4. (B) Prove that $C$ is idempotent complete if and only if $C^{\mathrm{op}}$ is idempotent complete.
5. (B) Let $R$ be a commutative ring and $C$ an $R$-linear category. Show that the opposite category is $R$-linear with the same modules of morphisms.
6. (C) Let $R$ be a ring. Show that the Karoubi envelope of the category of free $R$-modules of finite rank is equivalent to the category of finitely generated projective $R$-modules.

### Notes and history

The splitting of idempotents is an old tool of ring theory, where a decomposition $1 = e + (1 - e)$ splits a module into two summands. The construction of $\mathrm{Kar}(C)$ is named after Max Karoubi, who used it in algebraic K-theory. An idempotent complete additive category is also called *pseudo-abelian*, and in enriched category theory the construction is part of the *Cauchy completion*.

The Mathlib files are by Kim Morrison (linear categories and linear functors), Markus Himmel (the preadditive Yoneda embedding) and Joël Riou (idempotents and the Karoubi envelope).

### Reference

<?reference?>
