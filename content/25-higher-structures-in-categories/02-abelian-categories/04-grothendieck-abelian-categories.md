---
title: Grothendieck abelian categories in the library
kind: api
modules:
  - Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
  - Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Connected
  - Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
  - Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Indization
  - Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.PresheafOfModules
  - Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
  - Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
  - Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
  - Mathlib.CategoryTheory.Abelian.Indization
  - Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject
  - Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Monomorphisms
  - Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ColimCoyoneda
  - Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
  - Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
  - Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
  - Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HomologyFunctorAccessible
  - Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
  - Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.Opposite
explains:
  E2: [CategoryTheory.Limits.IsColimit.mono_ι_app_of_isFiltered, CategoryTheory.Limits.IsColimit.pullback_hom_ext, CategoryTheory.IsGrothendieckAbelian.mono_of_isColimit_monoOver, CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms_rlp, CategoryTheory.IsGrothendieckAbelian.llp_rlp_monomorphisms, CategoryTheory.IsGrothendieckAbelian.enoughInjectives, CategoryTheory.ShortComplex.instPreservesColimitsOfShapeHomologyFunctor]
  E1: auto
families: []
requires: [V07, V24.C04, V24.C05, V24.C08, V25.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Grothendieck abelian categories in the library

### Overview

Section 3 defined the axioms AB4 and AB5 and the class `IsGrothendieckAbelian`: an abelian category with small hom sets, exact filtered colimits and a separator. This section goes through the library that grows on this definition. It has three parts. The first part translates exactness of colimits into statements about arbitrary colimit cocones, and it gives the examples: types, functor categories, ind-objects, sheaves, presheaves of modules and sheaves of modules. The second part studies subobjects and monomorphisms in a Grothendieck category, and it proves the theorem of Grothendieck that such a category has enough injectives. The third part gives the consequences: a coseparator, small Ext groups, accessible homology functors, and the theorem of Gabriel and Popescu, which embeds a Grothendieck category into a category of modules.

The proofs use the lifting properties and the small object argument of Chapter 3, and the cardinal filtered categories of Chapter 7. The examples use the sheaves of Chapter 6. In the text $g \circ f$ is the textbook composite, and Mathlib writes `f ≫ g`. The category $C$ is abelian.

### The library around it

#### Exactness of colimits for arbitrary cocones

The class `HasExactColimitsOfShape J C` says that the functor `colim : (J ⥤ C) ⥤ C` preserves finite limits. The API of Mathlib states this for the chosen colimits. The module `Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim` restates it for any colimit cocones. Let $S = (X_1 \to X_2 \to X_3)$ be a short complex of functors $J \to C$, and let $c_1, c_2, c_3$ be colimit cocones. Maps $f$ and $g$ between the cone points that are compatible with the cocones give a short complex `colim.mapShortComplex`. The theorem `colim.exact_mapShortComplex` says that it is exact when $S$ is exact. In the same way, `colim.map_mono'` and `colim.map_epi'` say that a compatible map between colimit points is a monomorphism or an epimorphism when the natural transformation is one in each degree. The instances `MorphismProperty.instIsStableUnderCoproductsMonomorphismsOfAB4OfSize` and `MorphismProperty.instIsStableUnderFilteredColimitsMonomorphismsOfAB5OfSize` say that under AB4 a coproduct of monomorphisms is a monomorphism, and under AB5 a filtered colimit of monomorphisms is a monomorphism.

**Proposition.** Let $J$ be filtered, and let $X : J \to C$ be a diagram in which each transition map $X(\varphi)$ is a monomorphism. Assume that `colim` preserves monomorphisms, as it does under AB5. Then each coprojection $\iota_{j_0} : X_{j_0} \to \operatorname{colim} X$ is a monomorphism.

*Proof.* Restrict $X$ to the category $j_0 / J$ of arrows $j_0 \to j$. Since $J$ is filtered, this restriction is cofinal, so it has the same colimit. The maps $X(\varphi) : X_{j_0} \to X_j$ form a natural transformation from the constant diagram at $X_{j_0}$ to the restriction, and it is a monomorphism in each degree. The category $j_0 / J$ is filtered and hence connected, so the colimit of the constant diagram is $X_{j_0}$. The induced map of colimits is $\iota_{j_0}$, and `colim` keeps monomorphisms. $\square$

This is `IsColimit.mono_ι_app_of_isFiltered`.

The module `Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Connected` gives an extensionality principle for maps *into* a colimit. Let $c$ be a colimit cocone over $F : J \to C$, and let $f : X \to c_{\mathrm{pt}}$. The pullbacks of $\iota_j$ along $f$ form a cocone with point $X$. The definition `IsColimit.pullbackOfHasExactColimitsOfShape` proves that this cocone is a colimit when $J$ is connected and colimits of shape $J$ are exact. The reason is that a pullback is a finite limit, and exact colimits commute with it. The colimit of the constant diagram at $f$ is $f$ itself, because $J$ is connected.

**Corollary.** Under these hypotheses, let $g, h : c_{\mathrm{pt}} \to Y$. If $g f$ and $h f$ agree after composition with each projection $X \times_{c_{\mathrm{pt}}} F_j \to X$, then $g f = h f$.

*Proof.* The projections are the coprojections of the colimit cocone with point $X$, so maps out of $X$ agree when they agree on each of them. $\square$

This is `IsColimit.pullback_hom_ext`, with the special case `IsColimit.pullback_zero_ext` for $h = 0$. The duals for limits and pushouts are `IsLimit.pushoutOfHasExactLimitsOfShape`, `IsLimit.pushout_hom_ext` and `IsLimit.pushout_zero_ext`. The module docstring shows that connectedness is necessary: in abelian groups, take the diagonal $\mathbb{Z} \to \mathbb{Z} \oplus \mathbb{Z}$ and the coproduct of two copies of $\mathbb{Z}$.

#### Examples of Grothendieck categories

Most examples come as instances, so a user rarely names them. The table lists them by module.

| Lean name | Statement |
|---|---|
| `Limits.instAB5Type` | filtered colimits of types commute with finite limits |
| `instHasExactColimitsOfShapeFunctorOfHasFiniteLimits` | exact colimits of shape $J$ in $A$ give exact colimits of shape $J$ in `C ⥤ A` |
| `instHasExactLimitsOfShapeFunctorOfHasFiniteColimits` | the dual statement for limits |
| `Limits.instAB5IndOfHasFiniteLimits` | `Ind C` satisfies AB5 when $C$ has finite limits |
| `instAbelianInd` | `Ind C` is abelian for a small abelian category $C$ |
| `Limits.isGrothendieckAbelian_ind` | `Ind C` is Grothendieck abelian for a small abelian $C$ |
| `Sheaf.hasExactColimitsOfShape` | sheafification keeps exact colimits of shape $K$ |
| `Sheaf.instIsGrothendieckAbelian` | `Sheaf J A` is Grothendieck for a small site and a Grothendieck $A$ |
| `Sheaf.isGrothendieckAbelian_of_essentiallySmall` | the same for an essentially small site |
| `PresheafOfModules.instIsGrothendieckAbelian` | presheaves of modules over a presheaf of rings |
| `SheafOfModules.instIsGrothendieckAbelian` | sheaves of modules over a sheaf of rings |

All of them come from one pattern. A functor category inherits AB5 from its target, because colimits and finite limits are computed objectwise. A category of sheaves is a reflective subcategory of presheaves, the reflector `presheafToSheaf` is exact, and colimits of sheaves are sheafifications of colimits of presheaves. So exact colimits pass to sheaves. The ind-objects are the free filtered cocompletion, and the file `Mathlib.CategoryTheory.Abelian.Indization` proves that `Ind C` is abelian by the instance `instIsIsoIndCoimageImageComparison`: the comparison of coimage and image is an isomorphism in `Ind C`. This example is the step of the proof of the Freyd-Mitchell theorem that turns a small abelian category into a Grothendieck one.

#### Subobjects and monomorphisms

For an object $X$ of a Grothendieck category, the subobjects of $X$ form a complete lattice. The module `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject` relates filtered colimits of subobjects to suprema. Let $F : J \to$ `MonoOver X` be a functor from a filtered category, and let $c$ be a colimit of the underlying objects, with the induced map $f : c_{\mathrm{pt}} \to X$.

**Proposition.** The map $f$ is a monomorphism, and its subobject is the supremum $\bigvee_j F_j$.

*Proof.* Each $F_j \to X$ is a monomorphism, and so is the natural transformation from $F$ to the constant diagram at $X$. By AB5 the colimit of this transformation is a monomorphism. The colimit of the constant diagram is $X$, since $J$ is connected, and the induced map is $f$. For the supremum, each $F_j$ factors through $f$, so $\bigvee_j F_j \le [f]$. Conversely, a subobject $A$ that contains each $F_j$ gives a cocone on $F$ with point $A$, so $f$ factors through $A$. $\square$

The two parts are `IsGrothendieckAbelian.mono_of_isColimit_monoOver` and `IsGrothendieckAbelian.subobjectMk_of_isColimit_eq_iSup`. The definition `IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup` gives the converse colimit statement. The theorem `IsGrothendieckAbelian.exists_isIso_of_functor_from_monoOver` adds a cardinal bound: if $J$ is $\kappa$-filtered for a regular cardinal $\kappa$ larger than the number of subobjects of $X$, and $f$ is an epimorphism, then one $F_j$ is already all of $X$. The module `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Monomorphisms` has one instance, `IsGrothendieckAbelian.instIsStableUnderTransfiniteCompositionMonomorphisms`: a transfinite composition of monomorphisms is a monomorphism.

The module `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ColimCoyoneda` applies the cardinal bound to the functor $\mathrm{Hom}(X, -)$. Let $\kappa$ be regular and larger than the number of subobjects of $X$, and let $Y : J \to C$ be $\kappa$-filtered with colimit $c$. Then `IsGrothendieckAbelian.IsPresentable.injectivity` says that two maps $X \to Y_{j_0}$ with the same image in $c_{\mathrm{pt}}$ agree in some later $Y_j$. When the transition maps of $Y$ are monomorphisms, `IsGrothendieckAbelian.IsPresentable.surjectivity` says that each map $X \to c_{\mathrm{pt}}$ factors through some $Y_{j_0}$. Together they give `IsGrothendieckAbelian.preservesColimit_coyoneda_obj_of_mono`: $\mathrm{Hom}(X, -)$ preserves the colimit of such a diagram. This is a weak form of the statement that each object is $\kappa$-presentable, and it is enough for the small object argument below.

#### Enough injectives

Let $G$ be a separator. The class `IsGrothendieckAbelian.generatingMonomorphisms G` consists of the inclusions $A \to G$ of the subobjects of $G$. It is a small class, by the instance `IsGrothendieckAbelian.instIsSmallGeneratingMonomorphismsOfSmallSubobject`, and it consists of monomorphisms, by `IsGrothendieckAbelian.generatingMonomorphisms_le_monomorphisms`. Recall from Chapter 3 that `MorphismProperty.rlp` is the class of morphisms with the right lifting property against a class, and `MorphismProperty.llp` is the dual.

**Theorem (Baer criterion for Grothendieck categories).** A morphism has the right lifting property against all monomorphisms if and only if it has it against the inclusions of the subobjects of $G$.

*Proof sketch.* One direction is clear. For the other, the key step is `IsGrothendieckAbelian.generatingMonomorphisms.exists_larger_subobject`. Let $A \subsetneq X$ be a proper subobject. Since $G$ is a separator, some map $G \to X$ does not factor through $A$. Its pullback along $A \to X$ is a subobject $B$ of $G$, and the pushout of $B \to G$ along $B \to A$ embeds into $X$ as a strictly larger subobject $A'$. So $A \to A'$ is a pushout of a generating monomorphism. Iterate this by transfinite induction, with suprema at limit stages. A cardinal argument shows that the process stops at $X$. Thus each monomorphism is a transfinite composition of pushouts of generating monomorphisms, which is `IsGrothendieckAbelian.generatingMonomorphisms.exists_transfiniteCompositionOfShape`. The class of maps with the left lifting property against a fixed $p$ is stable under pushouts and transfinite compositions, so it contains all monomorphisms as soon as it contains the generating ones. $\square$

The theorem is `IsGrothendieckAbelian.generatingMonomorphisms_rlp`. Its corollary `IsGrothendieckAbelian.llp_rlp_monomorphisms` says that the monomorphisms are exactly the maps with the left lifting property against the class $\mathrm{Mono}^{\perp}$.

**Theorem (Grothendieck).** A Grothendieck abelian category has enough injectives.

*Proof.* The small object argument of Chapter 3 applies to the small class of generating monomorphisms, by the instance `IsGrothendieckAbelian.instHasSmallObjectArgumentGeneratingMonomorphisms`. It factors each $X \to 0$ as $X \to I \to 0$. The first map is a transfinite composition of pushouts of monomorphisms, so it is a monomorphism by AB5. The second map has the right lifting property against the generating monomorphisms, hence against all monomorphisms by the previous theorem. An object $I$ for which $I \to 0$ has this property is injective. $\square$

In Mathlib this is the instance `IsGrothendieckAbelian.enoughInjectives`. The factorization itself is the instance `IsGrothendieckAbelian.instHasFunctorialFactorizationMonomorphismsRlp`, and `IsGrothendieckAbelian.monoMapFactorizationDataRlp f` is the chosen factorization of a morphism $f$.

#### Consequences

Three short modules use the injectives. The instance `IsGrothendieckAbelian.instHasCoseparator` gives a coseparator. The proof applies `Abelian.has_injective_coseparator`, which builds an injective coseparator from a separator, all limits and enough injectives. The instance `IsGrothendieckAbelian.hasExt` gives `HasExt C`, so the Ext groups of Volume 26 are small, for the universe of the class. The module `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HomologyFunctorAccessible` shows that the cycles, opcycles and homology functors are accessible, for short complexes and for homological complexes.

**Proposition.** If colimits of shape $J$ are exact, then the homology functor on short complexes preserves colimits of shape $J$.

*Proof.* The homology of $X_1 \xrightarrow{f} X_2 \xrightarrow{g} X_3$ is the cokernel of the map from $X_1$ to the kernel of $g$. A kernel is a finite limit, which commutes with colimits of shape $J$ by exactness. A cokernel is a colimit, which commutes with all colimits. $\square$

This is `ShortComplex.instPreservesColimitsOfShapeHomologyFunctor`. With AB5 it gives the instance `ShortComplex.instIsCardinalAccessibleHomologyFunctorAleph0`: homology preserves filtered colimits. The names for cycles, opcycles and for `HomologicalComplex` follow the same pattern, as `HomologicalComplex.instIsAccessibleHomologyFunctor` shows.

#### The Gabriel-Popescu theorem

Let $G$ be a separator of a Grothendieck category $C$, with $R = \mathrm{End}(G)^{\mathrm{op}}$. The functor `preadditiveCoyonedaObj G` sends $X$ to the right $\mathrm{End}(G)$-module $\mathrm{Hom}(G, X)$. The module `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu` proves the following statements, by the elementary proof of Mitchell.

1. `IsGrothendieckAbelian.tensorObj G` is a functor from modules over $R$ to $C$, and `IsGrothendieckAbelian.tensorObjPreadditiveCoyonedaObjAdjunction G` makes it left adjoint to $\mathrm{Hom}(G, -)$.
2. `IsGrothendieckAbelian.GabrielPopescu.full` says that $\mathrm{Hom}(G, -)$ is full. It is faithful because $G$ is a separator.
3. `IsGrothendieckAbelian.GabrielPopescu.preservesFiniteLimits` says that the left adjoint is exact. A left adjoint is right exact, so the content is left exactness.
4. `IsGrothendieckAbelian.GabrielPopescu.preservesInjectiveObjects` says that $\mathrm{Hom}(G, -)$ sends injectives to injectives.

The text states these results without the proof. The consequence is that $C$ is a reflective subcategory of a module category with an exact reflector, so it is a localization of modules at a Serre class. The module `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.Opposite` gives the dual tool that the proof of the Freyd-Mitchell theorem needs. For a functor $F : D \to C^{\mathrm{op}}$ from a small nonempty category, `Abelian.IsGrothendieckAbelian.OppositeModuleEmbedding.embedding F` is a functor from $C^{\mathrm{op}}$ to modules over the ring `Abelian.IsGrothendieckAbelian.OppositeModuleEmbedding.EmbeddingRing F`. It is faithful and exact, and `Abelian.IsGrothendieckAbelian.OppositeModuleEmbedding.full_embedding` says that its composite with $F$ is full when $F$ is full.

#### Common errors

1. The class `IsGrothendieckAbelian.{w} C` has a universe parameter $w$ for the size of the colimits. The Gabriel-Popescu statements need `IsGrothendieckAbelian.{v} C`, where $v$ is the universe of the hom types. A category of sheaves can have a larger hom universe than its site, so check the universes in the instance that applies.
2. `IsColimit.mono_ι_app_of_isFiltered` needs both a filtered $J$ and monomorphisms as transition maps. `IsColimit.pullback_hom_ext` needs a connected $J$. Without these hypotheses the statements are false, even for abelian groups.
3. The results of `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ColimCoyoneda` are not a proof that each object is presentable. The surjectivity part needs transition maps that are monomorphisms. For a general $\kappa$-filtered diagram only the injectivity part holds.

### Exercises

1. (A) Use `IsGrothendieckAbelian.mono_of_isColimit_monoOver` to show that in `ModuleCat R` the union of a chain of submodules is the colimit of the chain.
2. (A) Show that an object $I$ is injective if and only if $I \to 0$ has the right lifting property against the inclusions of the ideals of $R$ into $R$, in `ModuleCat R` with the separator $R$. Compare with the Baer criterion of Volume 7.
3. (B) Prove that a functor category `C ⥤ A` with $C$ small and $A$ Grothendieck abelian has a separator. *Hint:* use the coproducts of representable functors tensored with a separator of $A$.
4. (B) Give a filtered diagram of monomorphisms in abelian groups for which $\mathrm{Hom}(\mathbb{Q}, -)$ does not preserve the colimit. *Hint:* the subgroups $\frac{1}{n!}\mathbb{Z}$ of $\mathbb{Q}$.
5. (B) Show that the homology functor on short complexes of abelian groups preserves products. Then give a cofiltered diagram of short complexes of abelian groups for which it does not preserve the limit.
6. (C) Let $G$ be a separator of a Grothendieck category $C$, and let $L$ be the left adjoint of $\mathrm{Hom}(G, -)$. Use the full faithfulness of $\mathrm{Hom}(G, -)$ to show that the counit $L(\mathrm{Hom}(G, X)) \to X$ is an isomorphism for each $X$. Deduce that $C$ is equivalent to the full subcategory of modules $M$ for which the unit $M \to \mathrm{Hom}(G, LM)$ is an isomorphism.

### Reference

<?reference?>
