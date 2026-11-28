---
title: The construction in the small object argument
kind: api
modules:
  - Mathlib.CategoryTheory.SmallObject.Construction
  - Mathlib.CategoryTheory.SmallObject.IsCardinalForSmallObjectArgument
  - Mathlib.CategoryTheory.SmallObject.Iteration.Basic
  - Mathlib.CategoryTheory.SmallObject.Iteration.ExtendToSucc
  - Mathlib.CategoryTheory.SmallObject.Iteration.FunctorOfCocone
  - Mathlib.CategoryTheory.SmallObject.Iteration.Nonempty
  - Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting
  - Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
  - Mathlib.CategoryTheory.SmallObject.WellOrderInductionData
explains:
  E2: [CategoryTheory.SmallObject.functorObj, CategoryTheory.SmallObject.ιFunctorObj_extension, CategoryTheory.MorphismProperty.IsCardinalForSmallObjectArgument, CategoryTheory.SmallObject.rlp_πObj, CategoryTheory.SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument, CategoryTheory.SmallObject.SuccStruct, CategoryTheory.SmallObject.SuccStruct.Iteration, CategoryTheory.SmallObject.SuccStruct.iteration, CategoryTheory.Functor.WellOrderInductionData, CategoryTheory.MorphismProperty.isStableUnderTransfiniteCompositionOfShape_llp]
  E1: auto
families: []
requires: [V04, V24.C01, V24.C04, V25.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The construction in the small object argument

### Overview

Section 3 states the small object argument: if $I$ is a small class of morphisms whose sources are small enough, then each morphism $f$ factors as a morphism in $\operatorname{llp}(\operatorname{rlp}(I))$ followed by a morphism in $\operatorname{rlp}(I)$. This section describes the parts of the library that construct the factorization. There are three layers. The first layer is one step: a functor on the arrow category that attaches one cell along each commutative square from a member of $I$. The second layer is the transfinite iteration of a step, indexed by a well-ordered type. The third layer is the typeclass `MorphismProperty.IsCardinalForSmallObjectArgument`, which collects the hypotheses on a regular cardinal $\kappa$ and gives the factorization from the iteration of length $\kappa$.

Two auxiliary results complete the proof. The class $\operatorname{llp}(W)$ is stable under transfinite composition, so the first factor is in $\operatorname{llp}(\operatorname{rlp}(I))$. The proof of this fact builds a lift step by step, and the library puts this kind of construction in the structure `Functor.WellOrderInductionData`, which gives a section of an inverse system of types indexed by a well-ordered type. The section uses the lifting properties and the transfinite compositions of Section 3, the colimits of Volume 24, and the well-ordered types and successor orders of Volume 4.

### The library around it

**One step.** The module `Mathlib.CategoryTheory.SmallObject.Construction` takes a family `f : ∀ i, A i ⟶ B i` and a morphism `πX : X ⟶ S`. The type `SmallObject.FunctorObjIndex f πX` contains the commutative squares from some `f i` to `πX`: an index `i`, a top map `t : A i ⟶ X` and a bottom map `b : B i ⟶ S`. The object `SmallObject.functorObj f πX` is the pushout of the coproduct of the maps `f i` over all squares along the map to $X$:
$$\coprod_{(i,t,b)} A_i \to X, \qquad \coprod_{(i,t,b)} A_i \to \coprod_{(i,t,b)} B_i.$$
The lemma `SmallObject.functorObj_isPushout` states that this square is a pushout. The map `SmallObject.ιFunctorObj f πX : X ⟶ functorObj f πX` is the inclusion, and `SmallObject.πFunctorObj f πX` is the map down to $S$, with `SmallObject.ιFunctorObj_πFunctorObj` as the factorization. The key lemma is `SmallObject.ιFunctorObj_extension`. A square from `f i` to `πX` does not have a lift $B_i \to X$ in general, but it has a tautological lift $B_i \to$ `functorObj f πX`. So one step solves each lifting problem, one stage later.

The map `ιFunctorObj` attaches cells: `SmallObject.attachCellsιFunctorObj` gives it as a structure `HomotopicalAlgebra.AttachCells`, which is a pushout of a coproduct of members of the family. When $C$ is locally $t$-small and the index type is $t$-small, `SmallObject.attachCellsιFunctorObjOfSmall` gives the same structure with a $t$-small index. With all pushouts, `SmallObject.functor f : Arrow C ⥤ Arrow C` is the step as a functor, `SmallObject.functorMap` is its action on morphisms, and `SmallObject.ε f : 𝟭 (Arrow C) ⟶ functor f` is the natural map from the identity.

**Successor structures.** The module `Mathlib.CategoryTheory.SmallObject.Iteration.Basic` defines `SmallObject.SuccStruct C`. It has an object `X₀`, a map `succ : C → C` and a morphism `toSucc X : X ⟶ succ X` for each object. The map `toSucc` does not have to be natural. A functor with a natural transformation `ε : 𝟭 C ⟶ F` gives `SmallObject.SuccStruct.ofNatTrans ε`, a successor structure on `C ⥤ C` with `X₀ = 𝟭 C` and `succ G = G ⋙ F`. The class `SmallObject.SuccStruct.prop` contains the maps `toSucc X`.

For a well-ordered type $J$ and $j : J$, the structure `SmallObject.SuccStruct.Iteration j` contains a functor `F : Set.Iic j ⥤ C` with three conditions: `obj_bot` says that the value at $\bot$ is `X₀`, `arrowSucc_eq` says that the map from $i$ to its successor is `toSucc`, and `arrowMap_limit` says that the value at a limit element is the colimit of the earlier values. The conditions are equalities of objects and of arrows, not isomorphisms. This is necessary because `toSucc` is not natural: two isomorphic objects can have successors that are not isomorphic. The construction needs colimits indexed by $J$ and by `Set.Iio j` at each limit element; the class `Limits.HasIterationOfShape J C` asks for them.

**Existence and the iteration.** The instance `SmallObject.SuccStruct.Iteration.subsingleton` says that there is at most one iteration up to $j$. The module `Mathlib.CategoryTheory.SmallObject.Iteration.Nonempty` proves the instance `SmallObject.SuccStruct.Iteration.nonempty` by transfinite induction, with the three cases `mkOfBot`, `mkOfSucc` and `mkOfLimit`. The successor case uses `SmallObject.SuccStruct.extendToSucc` from `Mathlib.CategoryTheory.SmallObject.Iteration.ExtendToSucc`, which extends a functor on `Set.Iic j` to `Set.Iic (Order.succ j)` by a morphism out of the top value. The limit case uses `SmallObject.SuccStruct.ofCocone` from `Mathlib.CategoryTheory.SmallObject.Iteration.FunctorOfCocone`, which extends a functor on `Set.Iio j` to `Set.Iic j` by a cocone.

The module `Mathlib.CategoryTheory.SmallObject.TransfiniteIteration` assembles these pieces. The functor `Φ.iterationFunctor J : J ⥤ C` takes its values from the iterations, and `SmallObject.SuccStruct.iteration Φ J` is its colimit. The instance of `Functor.IsWellOrderContinuous` says that the functor is continuous at limit elements, `SmallObject.SuccStruct.iterationFunctorObjBotIso` identifies its value at $\bot$ with `X₀`, and `iterationFunctorObjSuccIso` identifies a successor value. The map `SuccStruct.ιIteration Φ J : Φ.X₀ ⟶ Φ.iteration J` is a transfinite composition of maps in `Φ.prop`, by `SmallObject.SuccStruct.transfiniteCompositionOfShapeιIteration`.

**The suitable cardinals.** The module `Mathlib.CategoryTheory.SmallObject.IsCardinalForSmallObjectArgument` defines the class `MorphismProperty.IsCardinalForSmallObjectArgument I κ` for a regular cardinal $\kappa$. Its fields ask that $I$ is $w$-small, that $C$ is locally $w$-small, that $C$ has pushouts, coproducts of size $w$ and `HasIterationOfShape κ.ord.ToType C`, and that for each source $A$ of a map in $I$ the functor `coyoneda.obj (op A)` preserves the colimits of the relative $I$-cell complexes of length $\kappa$. The last condition holds when $\kappa$ is the successor of an infinite cardinal $c$ and each source is $c$-presentable, in the sense of Chapter 7.

With this class, `SmallObject.succStruct I κ` is the successor structure on `Arrow C ⥤ Arrow C` from the step functor of the family `I.homFamily`, and `SmallObject.iteration I κ` is its iteration of length `κ.ord.ToType`. For `f : X ⟶ Y`, the object `SmallObject.obj I κ f` is the left part of the iteration, with maps `SmallObject.ιObj I κ f` and `SmallObject.πObj I κ f` and `SmallObject.ιObj_πObj` for the factorization. The first map is a relative cell complex (`SmallObject.relativeCellComplexιObj`), so `SmallObject.llp_rlp_ιObj` puts it in `I.rlp.llp`. The second map has the right lifting property, by `SmallObject.rlp_πObj`. The proof of this lemma uses the colimit condition: a map from a source $A$ to the colimit factors through one stage, and the next stage gives the lift by `ιFunctorObj_extension`.

The factorization is functorial: `SmallObject.objMap`, `SmallObject.functorialFactorizationData` and `SmallObject.hasFunctorialFactorization` give `HasFunctorialFactorization I.rlp.llp I.rlp`. The lemma `SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument` says that `I.rlp.llp` is the class of retracts of transfinite compositions of pushouts of coproducts of maps in $I$. The primed version fixes the shape `κ.ord.ToType`, and `SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument_aleph0` uses the shape `ℕ` when $\kappa = \aleph_0$.

**Lifting along a transfinite composition.** The module `Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting` gives the instance `MorphismProperty.isStableUnderTransfiniteCompositionOfShape_llp`: for each $W$, the class `W.llp` is stable under transfinite compositions of shape $J$. The main lemma is `HasLiftingProperty.transfiniteComposition.hasLiftingProperty_ι_app_bot`. For a lifting problem against $p$, the structure `SqStruct c p f g j` contains the partial lifts from the stage $j$, and `HasLiftingProperty.transfiniteComposition.sqFunctor` makes them an inverse system $J^{\mathrm{op}} \to$ `Type`. Consequences are `MorphismProperty.transfiniteCompositions_le_llp_rlp` and `MorphismProperty.retracts_transfiniteComposition_pushouts_coproducts_le_llp_rlp`, which give the easy inclusion of the main theorem.

**Induction data.** The module `Mathlib.CategoryTheory.SmallObject.WellOrderInductionData` gives the general tool. For `F : Jᵒᵖ ⥤ Type v`, the structure `Functor.WellOrderInductionData F` has two fields of data. The field `succ` is a section of the restriction from `F.obj (op (Order.succ j))` to `F.obj (op j)`, and `lift` gives an element at a limit element $j$ from a compatible family below $j$. The lemmas `map_succ` and `map_lift` say that these are sections. From an element `val₀` at $\bot$, the structure `Extension val₀ j` contains the compatible families up to $j$, and it is unique by an instance. The lemma `Functor.WellOrderInductionData.surjective` says that the map from `F.sections` to `F.obj (op ⊥)` is surjective, and `Functor.WellOrderInductionData.sectionsMk` gives the section. The constructor `WellOrderInductionData.ofExists` makes the data from existence statements.

#### Common errors

1. `SmallObject.SuccStruct.Iteration` uses equalities such as `obj_bot : F.obj ⟨⊥, _⟩ = Φ.X₀`. A proof that changes the object only up to isomorphism does not give an iteration, and a rewrite with `Arrow.mk_eq_mk_iff` is often necessary.
2. The lemma `SmallObject.rlp_πObj` needs the instance `[Fact κ.IsRegular]` and an `OrderBot` instance on `κ.ord.ToType`. For $\kappa = \aleph_0$ the library gives this instance locally with `Cardinal.orderBotAleph0OrdToType`.
3. `MorphismProperty.IsCardinalForSmallObjectArgument` asks for colimit preservation only along relative cell complexes, not along all filtered colimits. Do not replace it by a presentability hypothesis without a proof that the hypothesis implies it.

### Exercises

1. (A) Use `SmallObject.ιFunctorObj_extension` to show that each lifting problem from a map `f i` to `πX` has a solution after one composition with `SmallObject.πFunctorObj`.
2. (A) Write `SmallObject.SuccStruct.ofNatTrans ε` for the identity natural transformation of `𝟭 C`, and describe its iteration of any length.
3. (B) Prove by hand that `SmallObject.SuccStruct.Iteration j` is a subsingleton when $J$ is `ℕ`, by induction on $j$.
4. (B) Let `F : ℕᵒᵖ ⥤ Type v` have surjective transition maps. Construct a term of `Functor.WellOrderInductionData F` with `WellOrderInductionData.ofExists`, and deduce that `F.sections` is not empty when `F.obj (op 0)` is not empty.
5. (B) Deduce `MorphismProperty.transfiniteCompositions_le_llp_rlp` from `MorphismProperty.isStableUnderTransfiniteCompositionOfShape_llp` and `MorphismProperty.le_llp_rlp`.
6. (C) Explain why `SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument` follows from `SmallObject.rlp_πObj`, `SmallObject.llp_rlp_ιObj` and the retract argument of Section 3.

### Reference

<?reference?>
