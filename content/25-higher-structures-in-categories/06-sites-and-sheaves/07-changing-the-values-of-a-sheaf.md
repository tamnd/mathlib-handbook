---
title: Changing the values of a sheaf
kind: api
modules:
  - Mathlib.CategoryTheory.Sites.Whiskering
  - Mathlib.CategoryTheory.Sites.Preserves
  - Mathlib.CategoryTheory.Sites.PreservesLimits
  - Mathlib.CategoryTheory.Sites.PreservesSheafification
  - Mathlib.CategoryTheory.Sites.CompatiblePlus
  - Mathlib.CategoryTheory.Sites.CompatibleSheafification
explains:
  E2: [CategoryTheory.GrothendieckTopology.HasSheafCompose, CategoryTheory.sheafCompose, CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize, CategoryTheory.fullyFaithfulSheafCompose, CategoryTheory.Presieve.isSheafFor_iff_preservesProduct, CategoryTheory.GrothendieckTopology.PreservesSheafification, CategoryTheory.sheafifyComposeIso, CategoryTheory.GrothendieckTopology.plusCompIso, CategoryTheory.GrothendieckTopology.sheafifyCompIso]
  E1: auto
families: []
requires: [V24.C04, V24.C05, V25.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Changing the values of a sheaf

### Overview

A sheaf of rings has an underlying sheaf of abelian groups and an underlying sheaf of sets. Many proofs pass between these: a property of sheaves of modules is checked on the underlying sheaves of sets, where sections are elements. The general question is this. Let $F : A \to B$ be a functor and let $P$ be a sheaf on $(C, J)$ with values in $A$. When is $P \circ F$, the presheaf $X \mapsto F(P(X))$, a sheaf with values in $B$? And when does $F$ commute with sheafification, so that the sheafification of $P \circ F$ is the composite of $F$ with the sheafification of $P$?

The answers are limit conditions. The sheaf condition says that $P(X)$ is a limit of a multicospan diagram built from a covering sieve. So $P \circ F$ is a sheaf when $F$ preserves these limits, and the forgetful functors of algebraic categories do. The plus construction of Section 3 is a filtered colimit of such limits. So $F$ commutes with the plus construction, and then with sheafification, when it preserves these limits and the filtered colimits over the covers. The forgetful functors of algebraic categories also preserve filtered colimits, and this gives the standard result that the underlying sheaf of sets of the sheafification of a presheaf of groups is the sheafification of the underlying presheaf of sets.

This section gives the functor `sheafCompose J F` on sheaf categories, the class `J.PreservesSheafification F`, and the comparison isomorphisms for the plus construction and for sheafification. It also gives a second link between sheaves and limits: for a disjoint coproduct, the sheaf condition is the preservation of the product. The section uses the limits and adjunctions of Volume 24, the class $W_J$ of Section 5 and the localization of Chapter 4.

### The library around it

**Composition with a functor.** In `Mathlib.CategoryTheory.Sites.Whiskering`, the class `GrothendieckTopology.HasSheafCompose J F` asks that $P \circ F$ is a sheaf for each sheaf $P$, and `GrothendieckTopology.HasSheafCompose.isSheaf` is the field. Then `sheafCompose J F : Sheaf J A ⥤ Sheaf J B` is the functor, and `sheafCompose_id` and `sheafCompose_comp` give its behavior for the identity and for a composition. A natural transformation $F \to G$ gives `sheafCompose_map`, a natural transformation of the two functors on sheaves.

There are two sources of the class. The instance `hasSheafCompose_of_preservesMulticospan` asks that $F$ preserves the limit of each multicospan diagram `(S.index P).multicospan` of a cover $S$. The isomorphisms `GrothendieckTopology.Cover.multicospanComp` and `GrothendieckTopology.Cover.mapMultifork` compare the diagram for $P \circ F$ with the image of the diagram for $P$. The instance `hasSheafCompose_of_preservesLimitsOfSize` asks for the preservation of all limits of the size of the hom types of $C$. It is not an instance by default for every functor that preserves limits of another size, so the universe levels are part of the statement. The instance `instHasSheafComposeForgetOfIsCorepresentable` gives the class for the forgetful functor of a concrete category when that functor is corepresentable, as for groups, rings and modules.

When $F$ is faithful, `sheafCompose J F` is faithful, and when $F$ is full and faithful it is full, by `instFaithfulSheafSheafCompose` and `instFullSheafSheafComposeOfFaithful`. The definition `fullyFaithfulSheafCompose` builds the fully faithful structure from one for $F$. The instance `instReflectsIsomorphismsSheafSheafCompose` says that `sheafCompose J F` reflects isomorphisms when $F$ does. For a concrete category, `Sheaf.isSeparated` says that the underlying presheaf of sets of a sheaf is separated, and `Presheaf.IsSheaf.isSeparated` is the same for a presheaf.

**Disjoint coproducts and products.** The module `Mathlib.CategoryTheory.Sites.Preserves` works with a presheaf of types $F$ on $C$. Let $I$ be an initial object and suppose that $F$ is a sheaf for the empty presieve on $I$. Then `Presieve.isTerminal_of_isSheafFor_empty_presieve` and `Presieve.preservesTerminal_of_isSheaf_for_empty` say that $F(I)$ is terminal. For a cofan $c$ of objects $X_a$ that is a colimit, with disjoint pairwise pullbacks, `Presieve.isSheafFor_iff_preservesProduct` says: $F$ is a sheaf for the presieve of the coprojections if and only if $F$ preserves the product of the $X_a$ in $C^{\mathrm{op}}$, that is,
$$F\Big(\coprod_a X_a\Big) \to \prod_a F(X_a)$$
is a bijection. The two directions are `Presieve.preservesProduct_of_isSheafFor` and `Presieve.isSheafFor_of_preservesProduct`, and `Presieve.firstMap_eq_secondMap` gives the key step: for disjoint coprojections, the two maps of the equalizer diagram agree, so the equalizer is the whole product. Section 9 uses this for the extensive topology.

**The sheaf Yoneda functor and limits.** The module `Mathlib.CategoryTheory.Sites.PreservesLimits` assumes a subcanonical topology, so that each representable presheaf is a sheaf and the Yoneda functor `GrothendieckTopology.yoneda` of Section 2 lands in sheaves. The instance `instPreservesLimitsOfShapeSheafTypeYoneda` says that this functor preserves all limits. The instance `instPreservesColimitsOfShapeSheafTypeYonedaOfPreservesLimitsOfShapeOppositeObjFunctorIsSheaf` says that it preserves the colimits of a shape $K$ when each sheaf sends the colimits of shape $K$ in $C$ to limits. The instance `instPreservesFiniteCoproductsSheafTypeYonedaOfPreservesFiniteProductsOppositeObjFunctorIsSheaf` is the case of finite coproducts, and the `uliftYoneda` family repeats the three facts with a universe lift.

**Preservation of sheafification.** In `Mathlib.CategoryTheory.Sites.PreservesSheafification`, the class `GrothendieckTopology.PreservesSheafification J F` asks that the composition with $F$ sends $W_J$ for $A$ into $W_J$ for $B$: if $f : P_1 \to P_2$ becomes an isomorphism after sheafification, so does $f \circ F$. The field is `GrothendieckTopology.PreservesSheafification.le`, and `GrothendieckTopology.W_of_preservesSheafification` is its use. In the language of Chapter 4, the functor on presheaves induced by $F$ then descends to the localization. The functor `Sheaf.composeAndSheafify J F` sends a sheaf $X$ to the sheafification of $X \circ F$. The natural transformation `toPresheafToSheafCompComposeAndSheafify` is then an isomorphism, and `presheafToSheafCompComposeAndSheafifyIso` is the isomorphism between the two composites $\mathrm{Psh}(A) \to \mathrm{Sh}(B)$.

If $F$ also preserves sheaves, `sheafComposeNatTrans J F adj₁ adj₂` compares the two functors from presheaves with values in $A$ to sheaves with values in $B$, for any left adjoints of the inclusions. The lemma `GrothendieckTopology.preservesSheafification_iff_of_adjunctions` says that $F$ preserves sheafification exactly when this natural transformation is an isomorphism, and `sheafComposeNatIso` is the resulting isomorphism. The isomorphism `sheafifyComposeIso J F P` states the result for one presheaf:
$$\operatorname{sheafify}(P \circ F) \cong \operatorname{sheafify}(P) \circ F.$$
The lemma `GrothendieckTopology.W_isInvertedBy_whiskeringRight_presheafToSheaf` and the instance `instLiftingFunctorOppositeSheafPresheafToSheafWCompObjWhiskeringRightComposeAndSheafify` give the localization form. At the end of the module, an instance gives `J.PreservesSheafification F` for a functor between concrete categories with good limits and colimits, and the instance `GrothendieckTopology.instPreservesSheafificationForgetOfPreservesLimitsOfHasColimitsOfShapeOfPreservesColimitsOfShapeOppositeCoverOfHasLimitsOfShapeWalkingMulticospanOfReflectsIsomorphisms` is the case of the forgetful functor.

**The plus construction and sheafification.** The modules `Mathlib.CategoryTheory.Sites.CompatiblePlus` and `Mathlib.CategoryTheory.Sites.CompatibleSheafification` give the explicit comparison for the plus construction of Section 3. They assume that $F$ preserves the multicospan limits of the covers and the colimits over the opposite categories of covers. The isomorphism `GrothendieckTopology.diagramCompIso` compares the diagram that defines $P^+$, composed with $F$, with the diagram for $P \circ F$. Then `GrothendieckTopology.plusCompIso J F P` is an isomorphism $P^+ \circ F \cong (P \circ F)^+$, and `GrothendieckTopology.plusFunctorWhiskerLeftIso` and `GrothendieckTopology.plusFunctorWhiskerRightIso` make it natural in $F$ and in $P$. The lemmas `GrothendieckTopology.ι_plusCompIso_hom`, `GrothendieckTopology.plusCompIso_whiskerLeft` and `GrothendieckTopology.plusCompIso_whiskerRight` compute it. Two applications give `GrothendieckTopology.sheafifyCompIso J F P`, the isomorphism between the sheafification of $P$ composed with $F$ and the sheafification of $P \circ F$, with the natural forms `GrothendieckTopology.sheafificationWhiskerLeftIso` and `GrothendieckTopology.sheafificationWhiskerRightIso`. The lemma `GrothendieckTopology.whiskerRight_toSheafify_sheafifyCompIso_hom` says that this isomorphism is compatible with the two maps from $P \circ F$.

#### Common errors

1. `hasSheafCompose_of_preservesLimitsOfSize` fixes the universe levels of the limits. A functor that preserves limits in another universe does not give the class, and the user must check the levels in the error message.
2. `sheafifyComposeIso` needs `J.PreservesSheafification F` and the two `HasWeakSheafify` instances, while `GrothendieckTopology.sheafifyCompIso` needs the limits and colimits of the plus construction and uses the plus construction itself. The two isomorphisms are for different settings.
3. `Presieve.isSheafFor_iff_preservesProduct` has two hypotheses that are easy to forget: the sheaf condition for the empty presieve on an initial object, and the disjointness of the coproduct.

### Exercises

1. (A) Use `instHasSheafComposeForgetOfIsCorepresentable` to state that the underlying presheaf of sets of a sheaf of groups is a sheaf.
2. (A) Show that `sheafCompose J (𝟭 A)` is isomorphic to the identity of `Sheaf J A`, with `sheafCompose_id`.
3. (B) On the open sets of a space $X$, apply `Presieve.isSheafFor_iff_preservesProduct` to two disjoint open sets $U$ and $V$, and state the result as $F(U \cup V) \cong F(U) \times F(V)$.
4. (B) Prove on paper that a functor that preserves the multicospan limits of all covers has `GrothendieckTopology.HasSheafCompose`.
5. (B) Explain why a functor that preserves limits but not filtered colimits need not commute with the plus construction, and name the hypothesis of `GrothendieckTopology.plusCompIso` that fails.
6. (C) Let $F$ preserve sheafification and reflect isomorphisms, and let $f$ be a morphism of presheaves with values in $A$. Show with `GrothendieckTopology.W_of_preservesSheafification` and `sheafifyComposeIso` that $f$ is in $W_J$ if and only if $f \circ F$ is in $W_J$.

### Reference

<?reference?>
