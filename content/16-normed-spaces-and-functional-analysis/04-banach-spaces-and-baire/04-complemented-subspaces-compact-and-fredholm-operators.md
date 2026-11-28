---
title: Complemented subspaces, compact operators and Fredholm operators
kind: api
modules:
  - Mathlib.Analysis.Normed.Module.Complemented
  - Mathlib.Analysis.Normed.Module.ContinuousInverse
  - Mathlib.Analysis.Normed.Operator.Compact.Basic
  - Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
  - Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
  - Mathlib.Analysis.Normed.Operator.Fredholm.Basic
  - Mathlib.Analysis.Normed.Operator.Fredholm.Open
  - Mathlib.Analysis.Normed.Operator.Perturbation.StrictByFinite
explains:
  E2: [Submodule.closedComplemented_iff_isClosed_exists_isClosed_isCompl, ContinuousLinearMap.HasLeftInverse.of_injective_of_isClosed_range_of_closedComplement_range, IsCompactOperator, isClosed_setOfPred_isCompactOperator, isCompactOperator_id_iff_finiteDimensional, IsCompactOperator.hasEigenvalue_or_mem_resolventSet, ContinuousLinearMap.IsFredholm, ContinuousLinearMap.isFredholm_iff_exists_isQuasiInverse, ContinuousLinearMap.isOpen_setOfPred_isFredholm, ContinuousLinearMap.isStrictMap_isClosed_range_iff_of_finiteRangeSetoid]
  E1: auto
families: []
requires: [V07, V13, V16.C02, V16.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Complemented subspaces, compact operators and Fredholm operators

### Overview

In linear algebra each subspace has a complement. In a Banach space a closed subspace need not have a closed complement, and the closed subspaces with a closed complement are the ranges of continuous projections. The open mapping theorem of section 3 makes the two notions agree: a closed subspace with a closed algebraic complement is the range of a continuous projection. This section starts with these complemented subspaces and with the maps that have a continuous left or right inverse.

The section then treats two classes of operators. A compact operator maps a neighborhood of $0$ into a compact set. The compact operators form a closed subspace of the operators, the identity is compact only in finite dimension, and the Fredholm alternative holds: for a compact $T$ and $\mu \ne 0$, either $\mu$ is an eigenvalue of $T$ or $T - \mu$ is invertible. A Fredholm operator is invertible up to finite dimensional spaces. Mathlib defines Fredholm operators on topological vector spaces, proves the four standard forms of the definition, and proves that the Fredholm operators between Banach spaces form an open set on which the index is locally constant.

### The library around it

The predicate `Submodule.ClosedComplemented p` states that there is a continuous linear projection of $E$ onto $p$. The predicate `Submodule.IsTopCompl p q` states that $p$ and $q$ are complements and that the map $p \times q \to E$ is a homeomorphism. In a Banach space, `Submodule.isTopCompl_iff_isCompl_isClosed` states that $p$ and $q$ are topological complements if and only if they are algebraic complements and both are closed. The lemma `Submodule.closedComplemented_iff_isClosed_exists_isClosed_isCompl` states that $p$ is complemented if and only if $p$ is closed and has a closed algebraic complement. The lemma `Submodule.ClosedComplemented.of_isCompl_isClosed` gives one direction. The map `ContinuousLinearMap.equivProdOfSurjectiveOfIsCompl` uses two surjective maps with complementary kernels to give an isomorphism of $E$ with a product. A finite dimensional subspace of a normed space over $\mathbb{R}$ or $\mathbb{C}$ is complemented, by `Submodule.ClosedComplemented.of_finiteDimensional`, and that result uses the theorem of Hahn-Banach.

The module on continuous inverses defines `ContinuousLinearMap.HasLeftInverse f` and `ContinuousLinearMap.HasRightInverse f`. These predicates state that $f$ has a left or a right inverse that is itself a continuous linear map. A map with a continuous left inverse has a closed range, by `ContinuousLinearMap.HasLeftInverse.isClosed_range`, and the range is complemented, by `ContinuousLinearMap.HasLeftInverse.closedComplemented_range`. The converse is `ContinuousLinearMap.HasLeftInverse.of_injective_of_isClosed_range_of_closedComplement_range`: an injective map with a closed and complemented range has a continuous left inverse. A map with a continuous right inverse is surjective. In finite dimension the conditions are simple: `ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional` and `ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional` give the inverses for injective and for surjective maps. Both predicates are stable under composition and products, and each continuous linear equivalence satisfies both. The differential geometry of volume 23 uses these predicates to define immersions and submersions.

A map $f$ is a compact operator, `IsCompactOperator f`, when the preimage of some compact set is a neighborhood of $0$. For a linear map between normed spaces this means that the image of the unit ball has compact closure. The lemma `isCompactOperator_iff_isCompact_closure_image_closedBall` gives this form for each ball of positive radius. A compact linear operator is continuous, by `IsCompactOperator.continuous`. The compact operators form a submodule `compactOperator` of the continuous linear maps. When the codomain is complete, this submodule is closed in the operator norm, by `isClosed_setOfPred_isCompactOperator`. So a limit of operators of finite rank is compact, and `isCompactOperator_of_tendsto` states the general form for limits. The composition of a compact operator with a continuous linear map on each side is compact, by `IsCompactOperator.comp_clm` and `IsCompactOperator.clm_comp`.

The identity map is compact if and only if the space is locally compact, by `isCompactOperator_id_iff_locallyCompactSpace`. With the theorem of Riesz of chapter 3, this gives `isCompactOperator_id_iff_finiteDimensional`: the identity of a normed space is compact if and only if the space has finite dimension. The module on the Fredholm alternative proves three results for a compact operator $T$ on a Banach space and a scalar $\mu \ne 0$. The lemma `IsCompactOperator.antilipschitz_of_not_hasEigenvalue` states that $T - \mu$ is bounded below when $\mu$ is not an eigenvalue. The lemma `IsCompactOperator.hasEigenvalue_or_mem_resolventSet` states that $\mu$ is an eigenvalue or a point of the resolvent set. The lemma `IsCompactOperator.hasEigenvalue_iff_mem_spectrum` states that the nonzero points of the spectrum are the nonzero eigenvalues.

The structure `ContinuousLinearMap.IsFredholm u` has five fields. The map $u$ is strict, its range is closed, its kernel has finite dimension, its range has finite codimension, and its kernel is complemented. A map is strict when it induces a homeomorphism from the quotient by its kernel onto its range. Over $\mathbb{R}$ or $\mathbb{C}$ the last field follows from the finite dimension of the kernel, but Mathlib keeps it so that the theory holds over each complete field. The statement `ContinuousLinearMap.isFredholm_tfae` gives four equivalent forms. The most useful is `ContinuousLinearMap.isFredholm_iff_exists_isQuasiInverse`: $u$ is Fredholm if and only if there is a continuous $v$ such that $v u - 1$ and $u v - 1$ have finite rank. The predicate for this is `LinearMap.IsQuasiInverse`. A `ContinuousLinearMap.FredholmPackage` gives decompositions of the two spaces in which $u$ is an isomorphism on one part and zero on a finite dimensional part. Use `ContinuousLinearMap.IsFredholm.nonempty_fredholmPackage` to get one from a Fredholm operator.

The index of $u$ is $\dim \ker u - \operatorname{codim} \operatorname{range} u$, the integer `LinearMap.index`. The lemma `ContinuousLinearMap.IsFredholm.index_comp` states that the index of a composite of Fredholm operators is the sum of the indices. The invertible operators are the bijective Fredholm operators, by `ContinuousLinearMap.isInvertible_iff_isFredholm_and_bijective`. A Fredholm operator plus an operator of finite rank is Fredholm, by `ContinuousLinearMap.IsFredholm.add_hasFiniteRange`. Between Banach spaces, `ContinuousLinearMap.isOpen_setOfPred_isFredholm` states that the Fredholm operators form an open set, and `ContinuousLinearMap.index_continuousOn_isFredholm` states that the index is locally constant on this set.

The module on perturbations holds the step that makes the finite rank results work. The lemma `ContinuousLinearMap.isStrictMap_isClosed_range_iff_of_finiteRangeSetoid` states that, when $u - v$ has finite rank, $u$ is strict with closed range if and only if $v$ is. The lemmas `ContinuousLinearMap.isStrictMap_isClosed_range_iff_restrict` and `ContinuousLinearMap.isStrictMap_isClosed_range_iff_quotient` do the same for a restriction to a closed subspace of finite codimension and for a quotient by a complemented finite dimensional subspace.

#### Common errors

1. Expecting each closed subspace to be complemented. The subspace $c_0$ of $\ell^\infty$ is closed and has no closed complement. Prove `Submodule.ClosedComplemented` from a projection, from a closed complement, or from finite dimension.
2. Using `IsCompactOperator` with the image of the whole space. The definition uses a neighborhood of $0$, and the image of the whole space is compact only for the zero map. Use the lemmas on balls, such as `isCompactOperator_iff_isCompact_closure_image_closedBall`.
3. Forgetting that the index is an integer. `LinearMap.index` has values in $\mathbb{Z}$, so a subtraction of dimensions needs a cast. The index is the dimension of the kernel minus the codimension of the range, and not the opposite.

### Exercises

1. (A) Show that the identity of $\mathbb{R}^n$ is a compact operator with `isCompactOperator_id_iff_finiteDimensional`.
2. (A) Show that the inclusion `ContinuousLinearMap.inl` of $E$ into $E \times F$ has a continuous left inverse, and give it.
3. (B) Prove that an operator of finite rank between normed spaces is compact, and then that each norm limit of such operators into a Banach space is compact.
4. (B) Compute the index of the right shift and of the left shift on $\ell^2$, and check `ContinuousLinearMap.IsFredholm.index_comp` on their composite.
5. (B) Let $T$ be compact on a Banach space and $\mu \ne 0$. Use `IsCompactOperator.hasEigenvalue_or_mem_resolventSet` to show that $T - \mu$ is invertible when it is injective.
6. (C) Prove from `ContinuousLinearMap.isFredholm_iff_exists_isQuasiInverse` that $1 + K$ is Fredholm for each operator $K$ of finite rank, and that its index is $0$.

### Reference

<?reference?>
