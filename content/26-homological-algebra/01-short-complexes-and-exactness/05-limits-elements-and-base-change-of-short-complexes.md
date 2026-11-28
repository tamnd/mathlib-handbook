---
title: Limits, elements and base change of short complexes
kind: api
modules:
  - Mathlib.Algebra.Homology.ShortComplex.Limits
  - Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
  - Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory
  - Mathlib.Algebra.Homology.ShortComplex.HomologyCofork
  - Mathlib.Algebra.Homology.ShortComplex.Pullback
  - Mathlib.Algebra.Homology.ShortComplex.Pushout
  - Mathlib.Algebra.Homology.ShortComplex.Retract
  - Mathlib.Algebra.Homology.Refinements
  - Mathlib.Algebra.Homology.ImageToKernel
explains:
  E2: [CategoryTheory.ShortComplex.isLimitOfIsLimitπ, CategoryTheory.ShortComplex.functorEquivalence, CategoryTheory.ShortComplex.exact_iff_of_hasForget, CategoryTheory.ShortComplex.ShortExact.pull, CategoryTheory.ShortComplex.ShortExact.push, CategoryTheory.ShortComplex.quasiIso_of_retract, HomologicalComplex.exactAt_iff_exact_up_to_refinements, imageToKernel]
  E1: auto
families: []
requires: [V24.C08, V25.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Limits, elements and base change of short complexes

### Overview

This section collects the smaller tools around short complexes. They answer practical questions. Does the category of short complexes have limits? How does one prove exactness with elements when the objects are modules or groups? How does a short exact sequence change under a pullback or a pushout? How does one test exactness in a general abelian category, where there are no elements?

The modules fall into four groups. The first two give limits and colimits of short complexes and the equivalence between short complexes of functors and functors to short complexes. The next two give the element calculus in a concrete category and the description of homology as a cokernel of a natural transformation. The next three give base change and retracts. The last two give refinements for complexes and the older map from the image to the kernel.

The sections before this one are the background: Section 1 for homology data, Section 2 for exactness and Section 4 for the functors that preserve homology.

### The library around it

#### Limits and colimits

A short complex in $C$ is a diagram of shape $\bullet \to \bullet \to \bullet$ with a zero composite. So a limit of short complexes is computed in each of the three places. Let $F : J \to \mathrm{ShortComplex}(C)$ be a diagram, and write $\pi_1$, $\pi_2$, $\pi_3$ for the three projections to $C$.

**Proposition.** A cone $c$ over $F$ is a limit cone as soon as $\pi_1 c$, $\pi_2 c$ and $\pi_3 c$ are limit cones in $C$.

*Proof.* Let $s$ be another cone. The universal properties in $C$ give three maps $u_i$ from the vertex of $s$ to the vertex of $c$ in each place. The two squares commute because both sides of each square are maps into a limit that agree after each projection. Uniqueness holds in each place, so it holds for the morphism of short complexes. $\square$

In Lean this is `CategoryTheory.ShortComplex.isLimitOfIsLimitπ`, and `CategoryTheory.ShortComplex.isColimitOfIsColimitπ` is the dual. When the three limits exist in $C$, `CategoryTheory.ShortComplex.limitCone` builds the cone and `CategoryTheory.ShortComplex.isLimitLimitCone` proves that it is a limit. The instances `CategoryTheory.ShortComplex.hasLimitsOfShape`, `CategoryTheory.ShortComplex.hasFiniteLimits` and their colimit forms follow. The projections preserve these limits, which gives instances such as `CategoryTheory.ShortComplex.instPreservesFiniteLimitsπ₁`. The projections also preserve monomorphisms and epimorphisms (`CategoryTheory.ShortComplex.preservesMonomorphisms_π₁` and `CategoryTheory.ShortComplex.preservesEpimorphisms_π₂`).

The module `Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence` gives the equivalence `CategoryTheory.ShortComplex.functorEquivalence J C` between $\mathrm{ShortComplex}(J \to C)$ and $J \to \mathrm{ShortComplex}(C)$. A short complex of functors $F_1 \to F_2 \to F_3$ goes to the functor $j \mapsto (F_1 j \to F_2 j \to F_3 j)$. The functors `CategoryTheory.ShortComplex.FunctorEquivalence.functor` and `CategoryTheory.ShortComplex.FunctorEquivalence.inverse` and the two isomorphisms `CategoryTheory.ShortComplex.FunctorEquivalence.unitIso` and `CategoryTheory.ShortComplex.FunctorEquivalence.counitIso` make it explicit.

The module `Mathlib.Algebra.Homology.ShortComplex.HomologyCofork` describes the homology functor as a universal object. Let $C$ be a category in which every short complex has homology. The natural transformation from the cycles functor to the homology functor is the cokernel of the natural map $X_1 \to Z$: this is `CategoryTheory.ShortComplex.homologyFunctorCofork` with `CategoryTheory.ShortComplex.isColimitHomologyFunctorCofork`. The dual statement for opcycles is `CategoryTheory.ShortComplex.homologyFunctorFork` with `CategoryTheory.ShortComplex.isLimitHomologyFunctorFork`. The cycles functor is in the same way the kernel of a natural transformation (`CategoryTheory.ShortComplex.cyclesFunctorFork`).

#### Elements in a concrete category

Let $C$ be a concrete preadditive category with a forgetful functor to abelian groups, `forget₂ C Ab`, that preserves homology. Modules over a ring are the main case. Then a short complex is exact if and only if its image in abelian groups is exact (`CategoryTheory.ShortComplex.exact_iff_exact_map_forget₂`). The element form is `CategoryTheory.ShortComplex.exact_iff_of_hasForget`:
$$S \text{ exact} \iff \forall x_2 \in X_2,\ g(x_2) = 0 \Rightarrow \exists x_1 \in X_1,\ f(x_1) = x_2.$$
The proof is the case of abelian groups, where homology is the quotient $\ker g / \operatorname{im} f$.

The same module translates monomorphisms and epimorphisms. The lemmas `CategoryTheory.Preadditive.mono_iff_injective` and `CategoryTheory.Preadditive.epi_iff_surjective` say that a map is mono if and only if it is injective and epi if and only if it is surjective. For a short exact sequence $S$, `CategoryTheory.ShortComplex.ShortExact.injective_f` and `CategoryTheory.ShortComplex.ShortExact.surjective_g` give the injectivity of $f$ and the surjectivity of $g$. An element $x_2$ with $g(x_2) = 0$ defines a cycle `CategoryTheory.ShortComplex.cyclesMk`, and `CategoryTheory.ShortComplex.i_cyclesMk` says that its image in $X_2$ is $x_2$. The lemma `CategoryTheory.ShortComplex.SnakeInput.δ_apply'` computes the connecting map of the snake lemma of Section 3 on elements: lift, apply the middle map, and pull back.

#### Base change and retracts

Let $S = (X_1 \xrightarrow{f} X_2 \xrightarrow{g} X_3)$ and let $u : Y \to X_3$. The pullback of $S$ along $u$ is `CategoryTheory.ShortComplex.pull S u`, the short complex
$$X_1 \to X_2 \times_{X_3} Y \to Y.$$
The first map is $(f, 0)$ and the second map is the projection. The module `Mathlib.Algebra.Homology.ShortComplex.Pullback` proves `CategoryTheory.ShortComplex.ShortExact.pull`: in an abelian category, the pullback of a short exact sequence is short exact. This is the pullback of an extension along $u$, the operation that makes $\operatorname{Ext}^1(-, X_1)$ a functor.

*Proof sketch.* The map $X_2 \times_{X_3} Y \to Y$ is the pullback of the epimorphism $g$, and in an abelian category a pullback of an epimorphism is an epimorphism. The kernel of the projection to $Y$ is the kernel of $g$, which is $X_1$. $\square$

Dually, for $v : X_1 \to Y$, `CategoryTheory.ShortComplex.push S v` is $Y \to Y \sqcup_{X_1} X_2 \to X_3$, and `CategoryTheory.ShortComplex.ShortExact.push` says that it is short exact. The instances `CategoryTheory.instMonoFPull` and `CategoryTheory.instEpiGPush` record the easy halves, and simp lemmas such as `CategoryTheory.ShortComplex.pull_X₂` and `CategoryTheory.ShortComplex.push_f` give the objects and maps.

The module `Mathlib.Algebra.Homology.ShortComplex.Retract` holds one result, `CategoryTheory.ShortComplex.quasiIso_of_retract`: a retract of a quasi-isomorphism of short complexes is a quasi-isomorphism. The reason is that $H$ is a functor, so it sends a retract diagram of arrows to a retract diagram, and a retract of an isomorphism is an isomorphism.

#### Refinements for complexes

In an abelian category there are no elements, but a morphism $x : A \to X$ can serve as one. The method of refinements replaces "there is a preimage" by "there is a preimage after an epimorphism $A' \to A$". The module `Mathlib.CategoryTheory.Abelian.Refinements` develops the method for short complexes. The module `Mathlib.Algebra.Homology.Refinements` gives the forms for a homological complex $K$. Let $i \to j \to k$ be the indices around $j$. Then `HomologicalComplex.exactAt_iff_exact_up_to_refinements` says that $K$ is exact at $j$ if and only if for each $x_2 : A \to K_j$ with $d\, x_2 = 0$ there are an epimorphism $\pi : A' \to A$ and $x_1 : A' \to K_i$ with $x_2 \pi = d\, x_1$.

The other lemmas of the module follow the same pattern for maps on homology. The lemmas `HomologicalComplex.mono_homologyMap_iff_up_to_refinements` and `HomologicalComplex.epi_homologyMap_iff_up_to_refinements` test the injectivity and surjectivity of $H_j(\varphi)$. The lemmas `HomologicalComplex.comp_homologyπ_eq_zero_iff_up_to_refinements` and `HomologicalComplex.comp_homologyπ_eq_iff_up_to_refinements` say when a cycle has zero class or when two cycles have the same class.

#### The map from the image to the kernel

The module `Mathlib.Algebra.Homology.ImageToKernel` is an older interface to homology, by subobjects. Let $f : A \to B$ and $g : B \to C$ with $g f = 0$. Then the image subobject of $f$ is contained in the kernel subobject of $g$ (`image_le_kernel`), and `imageToKernel f g w` is the inclusion map between them. The lemma `imageToKernel_arrow` says that the inclusion followed by the arrow of the kernel is the arrow of the image. The lemmas `imageToKernel_comp_right`, `imageToKernel_comp_left` and `imageToKernel_comp_mono` describe how the map changes when $g$ or $f$ is composed with another map. The instances `imageToKernel_epi_of_zero_of_mono` and `imageToKernel_epi_of_epi_of_zero` treat two degenerate cases. The homology of Section 1 does not use this map, but some older files still do.

#### Common errors

1. `CategoryTheory.ShortComplex.exact_iff_of_hasForget` needs the instance that `forget₂ C Ab` preserves homology. For `ModuleCat R` the instance exists. For a new concrete category a proof must supply it.
2. `CategoryTheory.ShortComplex.pull S u` takes $u$ with target $X_3$, and `CategoryTheory.ShortComplex.push S v` takes $v$ with source $X_1$. The pullback needs `HasPullback u S.g` in the form that Lean expects, and the argument order of the pullback matters.
3. The refinement lemmas take the indices $i$ and $k$ together with proofs `c.prev j = i` and `c.next j = k`. For a cochain complex indexed by $\mathbb{Z}$ the simplifier proves them, but a wrong index gives a goal that it cannot close.

### Exercises

1. (A) Use `CategoryTheory.ShortComplex.exact_iff_of_hasForget` to show that $\mathbb{Z} \xrightarrow{2} \mathbb{Z} \to \mathbb{Z}/2$ is exact in abelian groups.
2. (A) Show that the product of two exact short complexes of abelian groups is exact, by the limit description of this section.
3. (B) Let $0 \to \mathbb{Z} \xrightarrow{2} \mathbb{Z} \to \mathbb{Z}/2 \to 0$ and let $u : \mathbb{Z}/2 \to \mathbb{Z}/2$ be zero. Compute the pullback sequence and show that it splits.
4. (B) Prove that a retract of an exact short complex is exact.
5. (B) Describe the cokernel of `imageToKernel f g w` for $f = 0 : 0 \to \mathbb{Z}$ and $g = 0 : \mathbb{Z} \to 0$.
6. (C) Prove `HomologicalComplex.exactAt_iff_exact_up_to_refinements` from the version for short complexes and the short complex `K.sc j`.

### Reference

<?reference?>
