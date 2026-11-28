---
title: Gelfand duality, the GNS construction and positive maps
kind: api
modules:
  - Mathlib.Analysis.CStarAlgebra.GelfandDuality
  - Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
  - Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
  - Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
  - Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
explains:
  E2: [gelfandTransform_isometry, gelfandTransform_bijective, gelfandStarTransform, WeakDual.CharacterSpace.compContinuousMap, PositiveLinearMap.GNS, PositiveLinearMap.gnsStarAlgHom, PositiveLinearMap.cauchy_schwarz_star_mul, ContinuousLinearMap.monotone_iff_opNorm_eq_map_one, PositiveLinearMap.toContinuousLinearMap, CompletelyPositiveMap]
  E1: auto
families: []
requires: [V07, V13, V16.C01, V16.C02, V16.C04, V16.C06, V16.C09]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Gelfand duality, the GNS construction and positive maps

### Overview

Two theorems describe C*-algebras in terms of more concrete objects. The commutative Gelfand Naimark theorem says that a commutative unital C*-algebra $A$ is isomorphic to $C(X)$, where $X$ is its character space, the compact space of nonzero multiplicative linear functionals with the weak star topology. The isomorphism is the Gelfand transform $a \mapsto \hat a$, with $\hat a(\varphi) = \varphi(a)$. The general Gelfand Naimark theorem says that every C*-algebra is isomorphic to a closed star subalgebra of $B(H)$ for a Hilbert space $H$. Its proof uses the GNS construction.

The proof of the commutative theorem has four steps. The Gelfand transform is a homomorphism of algebras into $C(X)$ for every commutative Banach algebra, by Chapter 9. It preserves the star, because each character sends a self-adjoint element to a real number: the spectrum of a self-adjoint element is real, and $\varphi(a)$ is in the spectrum. It is an isometry, because $\|\hat a\|_\infty$ is the spectral radius of $a$, which is $\|a\|$ for the normal element $a$. So its image is closed. The image separates the points of $X$, contains the constants and is closed under conjugation, so it is dense by the Stone Weierstrass theorem, and so equal to $C(X)$.

The construction is functorial. A star homomorphism $\psi : A \to B$ gives a continuous map $\psi^* : X_B \to X_A$, $\varphi \mapsto \varphi \circ \psi$, and a continuous map $f : X \to Y$ gives a star homomorphism $C(Y) \to C(X)$, $g \mapsto g \circ f$. Up to these isomorphisms the two constructions are inverse to each other. This is Gelfand duality: the category of commutative unital C*-algebras is equivalent to the opposite of the category of compact Hausdorff spaces.

The GNS construction starts with a positive linear functional $f$ on $A$, a linear map with $f(a^* a) \ge 0$ for all $a$. The form $\langle a, b \rangle = f(a^* b)$ is a positive semidefinite sesquilinear form on $A$. The Cauchy Schwarz inequality $|f(a^* b)|^2 \le f(a^* a) f(b^* b)$ holds for it. The quotient of $A$ by the null vectors, completed, is a Hilbert space $H_f$, and left multiplication by $a$ gives a bounded operator $\pi_f(a)$ on $H_f$. The map $\pi_f$ is a star homomorphism from $A$ to $B(H_f)$. The general Gelfand Naimark theorem takes the direct sum of the $\pi_f$ over all states $f$.

A positive linear map between C*-algebras is automatically bounded, and for a positive functional on a unital algebra, $\|f\| = f(1)$. A linear map $\varphi$ is completely positive when each of its matrix extensions $M_n(A) \to M_n(B)$ is positive. Star homomorphisms are completely positive, and positive maps need not be: the transpose map on $2 \times 2$ matrices is positive but not completely positive.

### The library around it

The file `Mathlib.Analysis.CStarAlgebra.GelfandDuality` proves the commutative theorem for a commutative C*-algebra `A`. The Gelfand transform `WeakDual.gelfandTransform ℂ A` is defined for Banach algebras. Here `gelfandTransform_map_star` shows that it preserves the star, `gelfandTransform_isometry` shows that it is an isometry, and `gelfandTransform_bijective` shows that it is a bijection. The bundled result is `gelfandStarTransform`, a star algebra equivalence from `A` to `C(characterSpace ℂ A, ℂ)`. The surjectivity proof uses two facts on characters: `WeakDual.CharacterSpace.exists_apply_eq_zero` gives a character that vanishes at a non invertible element, constructed with `Ideal.toCharacterSpace` from a maximal ideal, and `WeakDual.CharacterSpace.mem_spectrum_iff_exists` says that the spectrum is the set of values of characters. The lemma `spectrum.gelfandTransform_eq` says that the range of $\hat a$ is the spectrum of $a$.

The functorial part is `WeakDual.CharacterSpace.compContinuousMap`, which turns a star algebra homomorphism `A →⋆ₐ[𝕜] B` into a continuous map between the character spaces in the other direction. The lemmas `WeakDual.CharacterSpace.compContinuousMap_id` and `WeakDual.CharacterSpace.compContinuousMap_comp` say that this respects identities and composition. The naturality statements are `gelfandStarTransform_naturality`, for the algebra side, and `WeakDual.CharacterSpace.homeoEval_naturality`, for the space side, where `WeakDual.CharacterSpace.homeoEval` is the homeomorphism from a compact space `X` onto the character space of `C(X, 𝕜)`. Together these give the duality, stated as lemmas and not as an equivalence of categories.

The same file proves a norm fact on orthogonal elements. The predicate `IsStarOrtho a b` says that $a b^* = 0$ and $b^* a = 0$. For such elements, `IsStarOrtho.norm_add` gives $\|a + b\| = \max(\|a\|, \|b\|)$, and `IsStarOrtho.norm_sub` and `IsStarOrtho.nnNorm_sum` are its variants.

The file `Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal` is the GNS construction for a positive linear map `f : A →ₚ[ℂ] ℂ`. The type `PositiveLinearMap.PreGNS f` is a copy of `A`, with `PositiveLinearMap.toPreGNS` and `PositiveLinearMap.ofPreGNS` as the maps in each direction. Its inner product is $f(a^* b)$, and `PositiveLinearMap.preGNSpreInnerProdSpace` makes it a pre inner product space, with `PositiveLinearMap.preGNS_norm_sq` for the square of the norm. The Cauchy Schwarz inequality is `PositiveLinearMap.cauchy_schwarz_star_mul`, with `PositiveLinearMap.cauchy_schwarz_mul_star` for the other order. The space has a seminorm and not a norm, since the null vectors are not removed. The Hilbert space `PositiveLinearMap.GNS f` is the completion `UniformSpace.Completion`, which makes the quotient by the null vectors on the way. Left multiplication `PositiveLinearMap.leftMulMapPreGNS` extends to the completion, and the representation is `PositiveLinearMap.gnsStarAlgHom`, a star algebra homomorphism into `f.GNS →L[ℂ] f.GNS`. For non-unital `A`, `PositiveLinearMap.gnsNonUnitalStarAlgHom` is the non-unital form. The file does not construct the cyclic vector of the representation.

The file `Mathlib.Analysis.CStarAlgebra.PositiveLinearMap` proves automatic continuity. `PositiveLinearMap.exists_norm_apply_le` says that a positive linear map between C*-algebras is bounded, and `PositiveLinearMap.toContinuousLinearMap` and `PositiveLinearMap.toPositiveContinuousLinearMap` give the bundled continuous maps. The lemma `PositiveLinearMap.norm_apply_le_of_nonneg` gives $\|f(x)\| \le \|f(1)\| \|x\|$ for $x \ge 0$, and `PositiveLinearMap.apply_le_of_isSelfAdjoint` gives $f(x) \le f(\|x\|)$ for self-adjoint $x$. The proof of boundedness writes each element as a combination of four positive elements of norm at most $\|x\|$, by Section 3, and bounds $f$ on each.

The file `Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional` treats functionals. `ContinuousLinearMap.monotone_iff_opNorm_eq_map_one` says that a continuous functional on a unital C*-algebra is positive if and only if its norm is its value at $1$, and `PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one` is the direction from positivity. The lemma `PositiveContinuousLinearMap.norm_map_sq_le_opNorm_mul` gives $|f(x)|^2 \le \|f\| f(x^* x)$. For non-unital algebras, `PositiveContinuousLinearMap.tendsto_nhds_opNorm` replaces $f(1)$ by the limit of $f$ along an increasing approximate unit, the topic of Section 6.

The file `Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap` defines the structure `CompletelyPositiveMap A₁ A₂`, with the notation `A₁ →CP A₂` in the scope `CStarAlgebra`, and the class `CompletelyPositiveMapClass`. The field `CompletelyPositiveMap.map_cstarMatrix_nonneg` says that the entrywise image of a positive matrix in `CStarMatrix n n A₁` of Section 4 is positive. The instance `CompletelyPositiveMapClass.instOrderHomClass` shows that a completely positive map is positive, and `NonUnitalStarAlgHomClass.instCompletelyPositiveMapClass` shows that a star homomorphism is completely positive. The lemma `OrderHomClass.of_map_cstarMatrix_nonneg` is the converse of the first instance, stated for maps that are positive at all matrix sizes.

#### Common errors

1. `gelfandStarTransform A` needs `CommCStarAlgebra A`. For a single normal element of a noncommutative algebra, use the continuous functional calculus of Section 2, which applies the theorem to the subalgebra generated by the element.
2. `PositiveLinearMap.PreGNS f` is not a Hausdorff space, because the null vectors are not removed. Lemmas that need a normed group, and not a seminormed group, apply only to `PositiveLinearMap.GNS f`.
3. A positive map `A →ₚ[ℂ] B` is bounded by `PositiveLinearMap.exists_norm_apply_le`, but it is not a continuous linear map by definition. Use `PositiveLinearMap.toContinuousLinearMap` before lemmas on `→L[ℂ]`.

### Exercises

1. (A) Prove that the spectrum of an element of a commutative C*-algebra is the range of its Gelfand transform, with `spectrum.gelfandTransform_eq`.
2. (A) Show that `‖a + b‖ = max ‖a‖ ‖b‖` for two orthogonal projections with $p q = 0$, with `IsStarOrtho.norm_add`.
3. (B) Prove that evaluation at a point of a compact space `X` is a positive functional on `C(X, ℂ)` of norm $1$, with `ContinuousLinearMap.monotone_iff_opNorm_eq_map_one`.
4. (B) Show that the transpose map on $2 \times 2$ complex matrices is positive and not completely positive, with the matrix that has entries $E_{ij}$ in position $(i, j)$.
5. (B) For the trace on $2 \times 2$ matrices, compute the GNS space and show that it has dimension $4$.
6. (C) Prove that two compact Hausdorff spaces are homeomorphic if their algebras of continuous complex functions are star isomorphic, with `WeakDual.CharacterSpace.homeoEval` and `WeakDual.CharacterSpace.compContinuousMap`.

### Reference

<?reference?>
