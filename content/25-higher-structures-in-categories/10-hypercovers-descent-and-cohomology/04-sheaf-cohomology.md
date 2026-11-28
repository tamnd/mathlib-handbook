---
title: Sheaf cohomology
kind: api
modules:
  - Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
  - Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
  - Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
  - Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
  - Mathlib.CategoryTheory.Sites.MayerVietorisSquare
  - Mathlib.CategoryTheory.Sites.NonabelianCohomology.H1
explains:
  E2: [CategoryTheory.Sheaf.H, CategoryTheory.Sheaf.H.equiv₀, CategoryTheory.Sheaf.instSubsingletonHHAddNatOfNat, CategoryTheory.Sheaf.H.longSequence_exact, CategoryTheory.GrothendieckTopology.MayerVietorisSquare, CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sequence_exact, CategoryTheory.cechComplexFunctor, CategoryTheory.PresheafOfGroups.H1, CategoryTheory.PresheafOfGroups.OneCocycle.class_eq_iff]
  E1: auto
families: []
requires: [V24.C04, V25.C02, V25.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Sheaf cohomology

### Overview

Let $C$ be a category with a Grothendieck topology $J$. The category of abelian sheaves on $(C, J)$ is abelian, and it often has enough injectives. The library defines the cohomology of an abelian sheaf $F$ as a group of extensions: $H^n(F) = \operatorname{Ext}^n(\underline{\mathbb Z}, F)$, where $\underline{\mathbb Z}$ is the constant sheaf with value $\mathbb Z$. This definition does not choose an injective resolution. It uses the groups `Abelian.Ext` of an abelian category, so it needs only the instance `HasExt` on the category of sheaves. Volume 26 treats these `Abelian.Ext` groups in general.

The five modules of this section build on this definition. The first module defines the cohomology groups, their functoriality in $F$, and the cohomology presheaf $U \mapsto H^n(U, F)$. The second module defines the Čech complex of a presheaf for a family of objects. The third module gives the long exact sequence of a short exact sequence of sheaves. The fourth module gives the Mayer Vietoris sequence of a Mayer Vietoris square. The last module defines the first cohomology of a presheaf of groups, which need not be abelian, by cocycles.

The section uses the sheaves and the sheafification of Chapter 6 and the abelian categories of Chapter 2. The hypercovers of the first two sections of this chapter are the natural tool to compare Čech cohomology with the derived functor cohomology, but the library does not make this comparison yet.

### The library around it

**Cohomology groups.** The module `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic` works with a site $(C, J)$ such that `HasSheafify J AddCommGrpCat` holds and the category `Sheaf J AddCommGrpCat` has `HasExt`. For an abelian sheaf `F` and `n : ℕ`, the type `Sheaf.H F n` is the abbreviation for the `Abelian.Ext` group of degree $n$ from the constant sheaf with value `ULift ℤ` to `F`. The `ULift` fixes the universe of the constant sheaf. The type is an additive commutative group by the instances of `Abelian.Ext`. With dot notation, the reader writes `F.H n`.

The library also gives a relative version. For an object $U$ of $C$, the free abelian sheaf on the representable sheaf of $U$ plays the part of $\underline{\mathbb Z}$ on $U$. The bifunctor `Sheaf.cohomologyPresheafFunctor` sends `F` and `U` to the `Abelian.Ext` group of degree $n$ from this free sheaf to `F`. For a fixed `F`, the abbreviation `Sheaf.cohomologyPresheaf F n` is the resulting presheaf $C^{\mathrm{op}} \to \mathsf{Ab}$, and `Sheaf.H' F n X` is its value at `X`, written $H^n(X, F)$ in the docstrings. The Mayer Vietoris sequence below is stated with `Sheaf.H'`.

A morphism `f : F ⟶ G` of sheaves gives `Sheaf.H.map f n : F.H n →+ G.H n`, which is the composition with `f` in `Abelian.Ext`. The functor form is `Sheaf.functorH J n`, and the related functor with values in `AddCommGrpCat` is `Sheaf.cohomologyFunctor J n`. Two basic facts follow from the general theory of `Abelian.Ext`. If `F` is a zero object, then each `F.H n` is a subsingleton: this is `Sheaf.subsingleton_H_of_isZero`. If `F` is an injective object, then `F.H (n + 1)` is a subsingleton: this is the instance `Sheaf.instSubsingletonHHAddNatOfNat`. The proof of the second fact is short: an `Abelian.Ext` group of positive degree with an injective target is zero, because each extension of positive degree splits against an injective object.

In degree $0$, the theory gives back the global sections. Let $T$ be a terminal object of $C$. Then `Sheaf.H.equiv₀ F hT` is an additive equivalence $H^0(F) \simeq F(T)$, where `hT : IsTerminal T`. The lemma `Sheaf.H.equiv₀_naturality` says that it commutes with `Sheaf.H.map`. Here is the proof sketch. The group $\operatorname{Ext}^0(\underline{\mathbb Z}, F)$ is the group of morphisms $\underline{\mathbb Z} \to F$. The constant sheaf $\underline{\mathbb Z}$ is the free abelian sheaf on the representable sheaf of $T$, because the representable presheaf of a terminal object is the terminal presheaf. By the free and forgetful adjunction and the Yoneda lemma, a morphism from this free sheaf to $F$ is the same as an element of $F(T)$.

**The Čech complex.** The module `Mathlib.CategoryTheory.Sites.SheafCohomology.Cech` does not use a topology. Let $C$ have finite products, and let $A$ be a preadditive category with products. For a family `U : ι → C`, the functor `cechComplexFunctor U : (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ` sends a presheaf $P$ to its Čech complex. In degree $n$ the complex is the product $\prod_{i : \mathrm{Fin}(n+1) \to \iota} P\bigl(\prod_{a} U_{i(a)}\bigr)$. The differential is the alternating sum of the maps that the face maps induce. The construction goes through formal coproducts: a family of objects is a simplicial object in `Limits.FormalCoproduct C`, and the functors `Limits.FormalCoproduct.cosimplicialObjectFunctor` and `Limits.FormalCoproduct.cochainComplexFunctor` evaluate a presheaf on such a simplicial object. The Čech complex is the special case of the Čech nerve of the family. The module does not yet compare the cohomology of this complex with `Sheaf.H`.

**The long exact sequence.** The module `Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences` takes a short complex `S` of abelian sheaves with `hS : S.ShortExact`. The connecting map is `Sheaf.H.δ hS n₀ n₁ h : S.X₃.H n₀ →+ S.X₁.H n₁`, where `h : n₀ + 1 = n₁`. The composable arrows `Sheaf.H.longSequence hS n₀ n₁ h` form the sequence

$$H^{n_0}(X_1) \to H^{n_0}(X_2) \to H^{n_0}(X_3) \xrightarrow{\delta} H^{n_1}(X_1) \to H^{n_1}(X_2) \to H^{n_1}(X_3),$$

and `Sheaf.H.longSequence_exact` says that it is exact. The proof is the long exact sequence of `Abelian.Ext` in the second variable. Two indices $n_0$ and $n_1$ with a proof of $n_0 + 1 = n_1$ appear in place of $n$ and $n + 1$, so that the user can give a degree as a numeral and not as a sum. This is the usual convention of the homology library.

The long sequence takes values in `AddCommGrpCat`, so its objects are the bundled groups. In practice it is often simpler to work with elements. The lemmas `Sheaf.H.longSequence_exact₁`, `Sheaf.H.longSequence_exact₂` and `Sheaf.H.longSequence_exact₃` give exactness at the three kinds of terms in element form. For example, `Sheaf.H.longSequence_exact₁` says that a class `x₁ : S.X₁.H n₁` with `Sheaf.H.map S.f n₁ x₁ = 0` comes from $\delta$ of a class in degree $n_0$. The lemma `Sheaf.H.longSequence_equiv₀_exact₃` is a form in degree $0$ with sections over a terminal object $T$: a section of $X_3$ over $T$ whose image under $\delta$ is zero lifts to a section of $X_2$ over $T$. For naturality, `Sheaf.H.δ_naturality` says that $\delta$ commutes with a morphism of short exact sequences, `Sheaf.H.longSequenceHom` is the induced morphism of long sequences, and `Sheaf.H.longSequenceFunctor` is the functor form.

**Mayer Vietoris squares.** The module `Mathlib.CategoryTheory.Sites.MayerVietorisSquare` defines the structure `GrothendieckTopology.MayerVietorisSquare J`. A term `S : J.MayerVietorisSquare` is a commutative square $X_1 \to X_2 \to X_4$, $X_1 \to X_3 \to X_4$ in $C$ such that $X_1 \to X_3$ is a monomorphism (the field `GrothendieckTopology.MayerVietorisSquare.mono_f₁₃`) and such that the square becomes a pushout after the passage to sheaves of sets (the field `GrothendieckTopology.MayerVietorisSquare.isPushout`). The standard example is an open set $X_4$ that is the union of two open sets $X_2$ and $X_3$, with $X_1 = X_2 \cap X_3$. The constructor `GrothendieckTopology.MayerVietorisSquare.mk_of_isPullback` takes a pullback square of two monomorphisms $X_2 \to X_4$ and $X_3 \to X_4$ that together cover $X_4$, and `GrothendieckTopology.MayerVietorisSquare.mk'` takes a square that each sheaf of types sends to a pullback. The condition is not symmetric in $X_2$ and $X_3$, so that it also includes the distinguished squares of the Nisnevich topology on schemes.

For a presheaf $P$, the proposition `GrothendieckTopology.MayerVietorisSquare.SheafCondition S P` says that $P$ sends the square to a pullback square, and `GrothendieckTopology.MayerVietorisSquare.sheafCondition_of_sheaf` says that each sheaf satisfies it. For a presheaf of types, `GrothendieckTopology.MayerVietorisSquare.sheafCondition_iff_bijective_toPullbackObj` restates the condition as a bijection $P(X_4) \to P(X_2) \times_{P(X_1)} P(X_3)$, and `GrothendieckTopology.MayerVietorisSquare.SheafCondition.glue` glues two sections that agree on $X_1$. With abelian coefficients, `GrothendieckTopology.MayerVietorisSquare.shortComplex` is the short complex $\mathbb Z[X_1] \to \mathbb Z[X_2] \oplus \mathbb Z[X_3] \to \mathbb Z[X_4]$ of free abelian sheaves, where $\mathbb Z[X]$ is the free abelian sheaf on the representable sheaf of $X$, and `GrothendieckTopology.MayerVietorisSquare.shortComplex_shortExact` says that it is short exact.

**The Mayer Vietoris sequence.** The module `Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris` defines the maps of the sequence:

| Lean name | Map |
| --- | --- |
| `GrothendieckTopology.MayerVietorisSquare.toBiprod` | $H^n(X_4, F) \to H^n(X_2, F) \oplus H^n(X_3, F)$, the sum of the restrictions |
| `GrothendieckTopology.MayerVietorisSquare.fromBiprod` | $H^n(X_2, F) \oplus H^n(X_3, F) \to H^n(X_1, F)$, the difference of the restrictions |
| `GrothendieckTopology.MayerVietorisSquare.δ` | $H^{n_0}(X_1, F) \to H^{n_1}(X_4, F)$, the connecting map |

The abbreviation `GrothendieckTopology.MayerVietorisSquare.sequence S F n₀ n₁ h` is the sequence of these maps, and `GrothendieckTopology.MayerVietorisSquare.sequence_exact` says that it is exact. The proof sketch: start from the short exact sequence `GrothendieckTopology.MayerVietorisSquare.shortComplex` above. The injectivity on the left uses the monomorphism $X_1 \to X_3$, and the exactness on the right uses the pushout condition. The long exact sequence of `Abelian.Ext` in the first variable applied to this short exact sequence gives the Mayer Vietoris sequence. The isomorphism `GrothendieckTopology.MayerVietorisSquare.sequenceIso` makes this comparison with the `Abelian.Ext` sequence explicit. The lemmas `GrothendieckTopology.MayerVietorisSquare.δ_toBiprod` and `GrothendieckTopology.MayerVietorisSquare.fromBiprod_δ` say that consecutive maps compose to zero.

**Nonabelian first cohomology.** The module `Mathlib.CategoryTheory.Sites.NonabelianCohomology.H1` treats a presheaf of groups `G : Cᵒᵖ ⥤ GrpCat`, which need not be abelian, and a family `U : I → C`. Neither a sheaf condition nor a covering condition is necessary. The definitions are the classical cocycle definitions, adapted to a category with no fibre products:

1. A zero cochain, `PresheafOfGroups.ZeroCochain G U`, is a family of sections $\alpha_i \in G(U_i)$. It is a group under pointwise multiplication.
2. A one cochain, `PresheafOfGroups.OneCochain G U`, gives an element $\gamma_{ij}(a, b) \in G(T)$ for each pair of morphisms $a : T \to U_i$ and $b : T \to U_j$. The field `ev` holds these elements, and `ev_precomp` says that they are compatible with a morphism $T' \to T$. One cochains form a group under pointwise operations, with the simp lemmas `one_ev`, `mul_ev` and `inv_ev`.
3. A one cocycle, `PresheafOfGroups.OneCocycle G U`, is a one cochain with $\gamma_{ij}(a, b)\,\gamma_{jk}(b, c) = \gamma_{ik}(a, c)$. This is the field `PresheafOfGroups.OneCocycle.ev_trans`. The lemmas `PresheafOfGroups.OneCocycle.ev_refl` and `PresheafOfGroups.OneCocycle.ev_symm` give $\gamma_{ii}(a, a) = 1$ and $\gamma_{ij}(a, b) = \gamma_{ji}(b, a)^{-1}$.

Two cochains $\gamma_1$ and $\gamma_2$ satisfy `PresheafOfGroups.OneCohomologyRelation γ₁ γ₂ α` when $G(a)(\alpha_i)\,\gamma_{1,ij}(a, b) = \gamma_{2,ij}(a, b)\,G(b)(\alpha_j)$ for all $a$ and $b$. Two cocycles are cohomologous, `PresheafOfGroups.OneCocycle.IsCohomologous`, when such an $\alpha$ exists. The lemma `PresheafOfGroups.OneCocycle.equivalence_isCohomologous` says that this is an equivalence relation: take $\alpha = 1$ for reflexivity, $\alpha^{-1}$ for symmetry and the product for transitivity. The set `PresheafOfGroups.H1 G U` is the quotient. It is a pointed set: its distinguished element is the class of the trivial cocycle. It is not a group, because the product of two cocycles is not a cocycle when $G$ is not abelian. The map `PresheafOfGroups.OneCocycle.class` sends a cocycle to its class, and `PresheafOfGroups.OneCocycle.class_eq_iff` says that two classes are equal if and only if the cocycles are cohomologous.

#### Common errors

1. A user expects `Sheaf.H F n` to be an object of `AddCommGrpCat`. It is a type with an additive group structure. The long exact sequence lives in `AddCommGrpCat`, so the element forms `Sheaf.H.longSequence_exact₁` to `Sheaf.H.longSequence_exact₃` are often easier to use than `Sheaf.H.longSequence_exact`.
2. A user tries to give the degrees as `n` and `n + 1` in `Sheaf.H.δ`. The API takes two degrees `n₀` and `n₁` and a proof `h : n₀ + 1 = n₁`. The proof is often `rfl` or found by `omega`.
3. A user tries to multiply two classes in `PresheafOfGroups.H1 G U`. The set has only a distinguished element. A group structure exists only when $G$ is a presheaf of abelian groups, and the library does not give it.

### Exercises

1. (A) Use `Sheaf.instSubsingletonHHAddNatOfNat` to show that `F.H 1` is a subsingleton for an injective abelian sheaf `F`.
2. (A) Show that `Sheaf.H.map (𝟙 F) n` is the identity map of `F.H n`.
3. (B) Let `0 → F₁ → F₂ → F₃ → 0` be a short exact sequence of abelian sheaves with `F₁` injective. Use the long exact sequence to show that the map $H^0(F_2) \to H^0(F_3)$ is surjective.
4. (B) Write out the Čech complex of `cechComplexFunctor U` in degrees $0$ and $1$ for a family of two objects $U_1$, $U_2$, and identify its $H^0$ for a sheaf with the equalizer of the sheaf condition.
5. (B) Prove that `PresheafOfGroups.OneCocycle.IsCohomologous` is symmetric: given $\alpha$ with `OneCohomologyRelation γ₁ γ₂ α`, show `OneCohomologyRelation γ₂ γ₁ α⁻¹`.
6. (C) For a presheaf of abelian groups `G` and a family `U`, define a group structure on `PresheafOfGroups.H1 G U` and show that `PresheafOfGroups.OneCocycle.class` is compatible with it.

### Reference

<?reference?>
