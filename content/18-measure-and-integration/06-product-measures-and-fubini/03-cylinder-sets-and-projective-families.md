---
title: Cylinder sets and projective families
kind: api
modules:
  - Mathlib.MeasureTheory.Constructions.Cylinders
  - Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
  - Mathlib.MeasureTheory.Constructions.Projective
  - Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
  - Mathlib.MeasureTheory.Constructions.KolmogorovExtension
explains:
  E2: [MeasureTheory.cylinder, MeasureTheory.generateFrom_measurableCylinders, MeasureTheory.IsProjectiveMeasureFamily, MeasureTheory.IsProjectiveLimit, MeasureTheory.projectiveFamilyContent, MeasureTheory.projectiveLimit, MeasureTheory.isCompactSystem_closedCompactCylinders]
  E1: auto
families: []
requires: [V13, V18.C01, V18.C02, V18.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Cylinder sets and projective families

### Overview

Section 1 builds the product of finitely many measures. Probability theory needs more. A sequence of random variables lives on an infinite product $\prod_{i \in \iota} \alpha_i$, and the index type $\iota$ can be $\mathbb{N}$, $\mathbb{R}$ or any other type. On such a product a measure is usually known only through its finite-dimensional marginals: for each finite set $J \subseteq \iota$ there is a measure $P_J$ on $\prod_{j \in J} \alpha_j$. The question is whether one measure $\mu$ on the whole product has exactly these marginals.

Two conditions are necessary. The family must be consistent: if $J \subseteq I$, then $P_J$ is the image of $P_I$ under the restriction from $I$ to $J$. Such a family is *projective*. The theorem of Kolmogorov says that this condition is also sufficient when every $\alpha_i$ is a Polish space with its Borel σ-algebra and the measures are finite. The limit is then unique.

This section explains the Mathlib API for the three parts of the proof. The first part is the cylinder sets, which generate the product σ-algebra and form a set algebra. The second part is the content on the cylinders that a projective family defines. The third part is the extension of this content to a measure, which uses inner regularity and compact systems. The section needs the product σ-algebra and the π-λ theorem of Chapter 1, the extension theorem of Carathéodory of Chapter 2, the regular measures of Chapter 4 and the compact sets of Volume 13.

### The library around it

#### Cylinders

For a finite set `s : Finset ι` and a set `S` of functions on `s`, the set `MeasureTheory.cylinder s S` contains the functions on all of `ι` whose restriction to `s` is in `S`. It is the preimage of `S` under `Finset.restrict s`. The lemma `MeasureTheory.mem_cylinder` gives this as an equivalence: `f ∈ cylinder s S ↔ s.restrict f ∈ S`. The coordinates outside `s` are free.

The Boolean operations on cylinders reduce to operations on the base sets. The lemma `MeasureTheory.compl_cylinder` says that the complement of `cylinder s S` is `cylinder s Sᶜ`. The lemmas `MeasureTheory.inter_cylinder` and `MeasureTheory.union_cylinder` treat two cylinders with different bases. They first move both cylinders to the base `s₁ ∪ s₂` with `Finset.restrict₂`, which is the restriction from a larger finite set to a smaller one. The lemma `MeasureTheory.cylinder_eq_cylinder_union` states this change of base for one cylinder. The versions `MeasureTheory.inter_cylinder_same` and `MeasureTheory.union_cylinder_same` are for two cylinders with the same base.

A cylinder does not determine its base. The same set is `cylinder s S` and `cylinder (s ∪ t) S'` for the preimage `S'` of `S`. Results that compare cylinders must allow for this. The lemma `MeasureTheory.cylinder_eq_empty_iff` says that a cylinder is empty if and only if its base set is empty, under the hypothesis that the product is nonempty. The lemma `MeasureTheory.disjoint_cylinder_iff` gives the same reduction for disjointness.

The set `MeasureTheory.measurableCylinders α` contains the cylinders with a measurable base set. The lemma `MeasureTheory.mem_measurableCylinders` unfolds the membership: `t` is in the set if there are `s` and a measurable `S` with `t = cylinder s S`. For an element `t`, the functions `MeasureTheory.measurableCylinders.finset` and `MeasureTheory.measurableCylinders.set` choose a base and a base set. The choice is arbitrary, so a proof that uses it must not depend on it.

The two main facts are these:

| Lean name | Statement |
|---|---|
| `MeasureTheory.isPiSystem_measurableCylinders` | the measurable cylinders are closed under intersection |
| `MeasureTheory.generateFrom_measurableCylinders` | the measurable cylinders generate `MeasurableSpace.pi` |
| `MeasureTheory.isSetAlgebra_measurableCylinders` | the measurable cylinders form a set algebra |
| `MeasurableSet.cylinder` | a cylinder with a measurable base is measurable in the product |

Together with the uniqueness lemma `MeasureTheory.ext_of_generate_finite` of Chapter 1, the first two facts show that two finite measures on the product are equal if they agree on all measurable cylinders. This is how uniqueness in the theorem of Kolmogorov is proved.

For the index type `ℕ`, the lemma `MeasureTheory.measurableCylinders_nat` says that every measurable cylinder has a base of the form `Finset.Iic a`. Proofs about sequences then use only initial segments.

#### Square cylinders

A second family of generators uses products of sets instead of arbitrary base sets. For a family `C i` of sets of sets, `MeasureTheory.squareCylinders C` contains the sets $\{f \mid f(i) \in A_i \text{ for } i \in s\}$ with $A_i \in C_i$. The lemma `MeasureTheory.squareCylinders_eq_iUnion_image` writes them as images of `Set.pi`. If each `C i` is a π-system that contains the whole space, `MeasureTheory.isPiSystem_squareCylinders` shows that the square cylinders form a π-system. The lemma `MeasureTheory.generateFrom_squareCylinders` shows that the square cylinders with measurable sides generate the product σ-algebra. This form is the convenient one when a measure is known on boxes, such as an infinite product of probability measures.

#### Events that depend on some coordinates

For a set of indices `Δ : Set ι`, the σ-algebra `MeasureTheory.cylinderEvents Δ` is the smallest σ-algebra on the product for which every coordinate in `Δ` is measurable. Its events depend only on the coordinates in `Δ`. The lemma `MeasureTheory.cylinderEvents_le_pi` says that it is smaller than the product σ-algebra. The lemma `MeasureTheory.cylinderEvents_univ` says that it is equal for `Δ = Set.univ`, and `MeasureTheory.cylinderEvents_mono` says that it grows with `Δ`.

The lemma `MeasureTheory.measurable_cylinderEvents_iff` characterizes the maps into the product that are measurable for this σ-algebra: each coordinate in `Δ` must be measurable. The lemma `MeasureTheory.measurable_cylinderEvent_apply` gives the measurability of one coordinate. Results of this kind are the base of tail σ-algebras and of the zero-one laws of probability theory.

#### Projective families and projective limits

A family `P : (J : Finset ι) → Measure ((j : J) → α j)` assigns a measure to each finite set of indices. The predicate `MeasureTheory.IsProjectiveMeasureFamily P` says that for `J ⊆ I` the measure `P J` is the image of `P I` under `Finset.restrict₂`. The predicate `MeasureTheory.IsProjectiveLimit μ P` says that for every `I` the image of `μ` under `Finset.restrict I` is `P I`. The two predicates use `MeasureTheory.Measure.map`, so the restriction maps must be measurable. Mathlib proves this once for all finite sets.

The main lemmas on these predicates are:

| Lean name | Statement |
|---|---|
| `MeasureTheory.IsProjectiveMeasureFamily.congr_cylinder` | if `cylinder I S = cylinder J T` with measurable bases, then `P I S = P J T` |
| `MeasureTheory.IsProjectiveMeasureFamily.measure_univ_eq` | all measures of the family have the same total mass |
| `MeasureTheory.IsProjectiveLimit.measure_cylinder` | the limit gives the cylinder `cylinder I s` the measure `P I s` |
| `MeasureTheory.IsProjectiveLimit.unique` | two projective limits of a family of finite measures are equal |
| `MeasureTheory.IsProjectiveLimit.isProbabilityMeasure` | the limit of a family of probability measures is a probability measure |

The first lemma is the key step. It says that the value of the family on a cylinder does not depend on the choice of the base. The proof moves both bases to `I ∪ J` and uses the projective property twice.

#### The content of a projective family

By `MeasureTheory.IsProjectiveMeasureFamily.congr_cylinder`, a projective family defines a function on the measurable cylinders: the value at `cylinder I S` is `P I S`. The function `MeasureTheory.projectiveFamilyFun P` is this function on all sets, with the value zero outside the measurable cylinders. The structure `MeasureTheory.projectiveFamilyContent hP` packages it as a `MeasureTheory.AddContent` on `measurableCylinders α`, which is a finitely additive function on a set ring. The lemma `MeasureTheory.projectiveFamilyContent_cylinder` computes it on a cylinder. The lemmas `MeasureTheory.projectiveFamilyContent_mono`, `MeasureTheory.projectiveFamilyContent_sdiff` and `MeasureTheory.projectiveFamilyContent_ne_top` give the usual rules of a finite content. The ring structure comes from `MeasureTheory.isSetRing_measurableCylinders` and `MeasureTheory.isSetSemiring_measurableCylinders`.

A content on a semiring that is σ-subadditive extends to a measure by the construction `MeasureTheory.AddContent.measure` of Chapter 2. The whole difficulty is σ-subadditivity. Finite additivity is free, but countable additivity fails for general projective families on general measurable spaces. Topology enters at this point.

#### Compact systems and the theorem of Kolmogorov

A family of sets is a *compact system* if every countable subfamily with empty intersection has a finite subfamily with empty intersection. The predicate is `IsCompactSystem`. Compact sets in a Hausdorff space form a compact system. The set `MeasureTheory.closedCompactCylinders X` contains the cylinders whose base set is closed and compact, and the lemma `MeasureTheory.isCompactSystem_closedCompactCylinders` shows that they form a compact system. The proof uses the compactness of products of compact sets from Volume 13.

The proof of σ-subadditivity has two steps:

1. If every `P J` is inner regular for closed compact sets, then the content is inner regular for closed compact cylinders. This is `MeasureTheory.innerRegular_projectiveFamilyContent`.
2. A finite content that is inner regular for a compact system is σ-subadditive. The lemma `MeasureTheory.isSigmaSubadditive_projectiveFamilyContent_of_innerRegular` applies this to projective families.

On a Polish space, finite Borel measures are inner regular for compact sets. With this, `MeasureTheory.isSigmaSubadditive_projectiveFamilyContent` and `MeasureTheory.projectiveFamilyContent_iUnion_eq_tsum` hold with no regularity hypothesis on the family.

The measure `MeasureTheory.projectiveLimit P` is the extension of the content. Its hypotheses are type classes on each `α i`: a topology, `SecondCountableTopology`, `TopologicalSpace.IsCompletelyPseudoMetrizableSpace` and `BorelSpace`, together with `IsFiniteMeasure (P J)` for all `J`. These classes together say that each factor is a Polish space with its Borel sets. The theorem `MeasureTheory.isProjectiveLimit_projectiveLimit` takes the proof of the projective property and says that the measure is a projective limit. The instances `MeasureTheory.isFiniteMeasure_projectiveLimit` and `MeasureTheory.isProbabilityMeasure_projectiveLimit` give the type of the limit.

The definition takes `P` as an explicit argument and the projective property only in the theorem. If the property fails, `projectiveLimit P` is still a measure, but no lemma describes it.

Mathlib has two other ways to build measures on infinite products. The measure `MeasureTheory.Measure.infinitePi` is the product of a family of probability measures on arbitrary measurable spaces, and `MeasureTheory.Measure.infinitePi_cylinder` computes it on cylinders. The kernel `ProbabilityTheory.Kernel.traj` builds the law of a Markov chain on $\prod_n X_n$ by the theorem of Ionescu-Tulcea. Neither needs topology. When the factors are Polish and only the marginals are known, `projectiveLimit` is the tool.

#### Common errors

1. Assuming that a cylinder has a unique base. A proof that uses `MeasureTheory.measurableCylinders.finset` must show that the result does not depend on the base. The lemma `MeasureTheory.IsProjectiveMeasureFamily.congr_cylinder` is the model for this.
2. Applying `projectiveLimit` to factors that are not Polish. The definition needs the four type classes on each factor. Without them, use `MeasureTheory.Measure.infinitePi` for products of probability measures or `ProbabilityTheory.Kernel.traj` for Markov chains.
3. Proving uniqueness of a measure on a product by checking only finite products of measurable sets in a fixed finite set of coordinates. The generators must contain cylinders over all finite sets of indices.

### Exercises

1. (A) Show that `cylinder s Set.univ` is the whole product and that `cylinder s ∅` is empty.
2. (A) Show that the complement of a measurable cylinder is a measurable cylinder with the same base.
3. (B) Show that two probability measures on $\prod_{n \in \mathbb{N}} X_n$ are equal if they have the same image under `Finset.restrict (Finset.Iic a)` for every `a`.
4. (B) Let $P_J$ be the product of the Gaussian measures $\mathcal{N}(0, 1)$ on $\mathbb{R}^J$. Show that the family is projective and describe its projective limit.
5. (B) Show that a function on the product that is measurable for `cylinderEvents Δ` does not change when a coordinate outside `Δ` changes, for a finite set `Δ`.
6. (C) Give a family of compact sets in a Hausdorff space and prove from the definition that it is a compact system. Explain why the open intervals of $\mathbb{R}$ are not a compact system.

### Reference

<?reference?>
