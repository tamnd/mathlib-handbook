---
title: C*-rings, C*-algebras and the first examples
kind: api
modules:
  - Mathlib.Analysis.CStarAlgebra.Basic
  - Mathlib.Analysis.CStarAlgebra.Classes
  - Mathlib.Analysis.CStarAlgebra.Hom
  - Mathlib.Analysis.CStarAlgebra.Unitization
  - Mathlib.Analysis.CStarAlgebra.ContinuousMap
  - Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
  - Mathlib.Analysis.CStarAlgebra.lpSpace
  - Mathlib.Analysis.CStarAlgebra.Spectrum
  - Mathlib.Analysis.CStarAlgebra.Exponential
  - Mathlib.Analysis.CStarAlgebra.Matrix
  - Mathlib.Analysis.CStarAlgebra.Multiplier
explains:
  E2: [CStarRing, CStarRing.norm_star_mul_self, CStarAlgebra, NonUnitalCStarAlgebra, IsSelfAdjoint.spectralRadius_eq_nnNorm, IsSelfAdjoint.mem_spectrum_eq_re, NonUnitalStarAlgHom.isometry, Unitization.instCStarAlgebra, DoubleCentralizer, selfAdjoint.expUnitary]
  E1: auto
families: []
requires: [V07, V13, V16.C01, V16.C02, V16.C06, V16.C07, V16.C09]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## C*-rings, C*-algebras and the first examples

### Overview

A C*-algebra is a complex Banach algebra $A$ with an involution $a \mapsto a^*$ that is conjugate linear, reverses products, and satisfies the C*-identity $\|a^* a\| = \|a\|^2$. The two basic examples are the algebra $B(H)$ of bounded operators on a Hilbert space, where $a^*$ is the adjoint of Chapter 7, and the algebra $C(X)$ of continuous complex functions on a compact space, where $a^*$ is the complex conjugate. The algebra of $n \times n$ complex matrices with the operator norm is a special case of $B(H)$. A closed subalgebra of a C*-algebra that is closed under the involution is again a C*-algebra.

The C*-identity is a strong condition. It ties the norm to the algebra, and the consequences come from the spectral theory of Banach algebras in Chapter 9. Let $a$ be self-adjoint, that is $a^* = a$. Then $\|a^2\| = \|a^* a\| = \|a\|^2$, and by induction $\|a^{2^n}\| = \|a\|^{2^n}$. The Gelfand formula $r(a) = \lim_n \|a^n\|^{1/n}$ for the spectral radius, applied along the subsequence $2^n$, gives $r(a) = \|a\|$. For any $a$, the element $a^* a$ is self-adjoint, so $\|a\|^2 = r(a^* a)$. The spectral radius depends only on the algebra, so the norm of a C*-algebra is determined by its algebraic structure. A consequence is that a star homomorphism between C*-algebras has norm at most $1$, and an injective one is an isometry.

The spectrum of a self-adjoint element is real. A proof sketch: if $a$ is self-adjoint, then $u = \exp(i a)$ is unitary, that is $u^* u = u u^* = 1$. For a unitary, $\|u\| = \|u^{-1}\| = 1$, so the spectrum of $u$ is on the unit circle. The spectral mapping theorem for the exponential says that the spectrum of $u$ is the set of $e^{i z}$ for $z$ in the spectrum of $a$, and $|e^{i z}| = 1$ forces $z$ to be real.

A C*-algebra need not have a unit. The compact operators on an infinite dimensional Hilbert space and the functions on a locally compact space that vanish at infinity are examples without a unit. There are two standard ways to add a unit: the unitization $A \oplus \mathbb{C}$, which is the smallest one, and the multiplier algebra, which is the largest one in a precise sense.

### The library around it

The file `Mathlib.Analysis.CStarAlgebra.Basic` defines the class `NormedStarGroup E`, a normed group with a star operation that preserves the norm, with `norm_star` and `nnNorm_star`, and the linear isometric equivalence `starₗᵢ`. The class `CStarRing E` has one field, the inequality $\|x^* x\| \ge \|x\|^2$, and the file derives the identity `CStarRing.norm_star_mul_self`, its forms `CStarRing.norm_self_mul_star` and `CStarRing.norm_star_mul_self'`, and the instance `CStarRing.to_normedStarGroup`. The proof that the star preserves the norm is short: $\|x\|^2 \le \|x^* x\| \le \|x^*\| \|x\|$ gives $\|x\| \le \|x^*\|$, and the same with $x^*$ gives the reverse. The constructor `CStarRing.of_le_norm_mul_star_self` uses the other order of the factors. In a nontrivial C*-ring the unit has norm $1$, `CStarRing.norm_one`. A unitary has norm $1$ and does not change norms by multiplication, by `CStarRing.norm_coe_unitary`, `CStarRing.norm_coe_unitary_mul` and `CStarRing.norm_mem_unitary_mul`. For self-adjoint elements, `IsSelfAdjoint.norm_mul_self` and `IsSelfAdjoint.norm_pow_two_pow` are the identities of the overview. The instances `instCStarRingReal`, `Pi.cstarRing`, `Prod.cstarRing` and `StarSubalgebra.to_cstarRing` give the first examples. The product and the finite product use the supremum norm.

The file `Mathlib.Analysis.CStarAlgebra.Classes` bundles the conditions in four classes: `NonUnitalCStarAlgebra`, `NonUnitalCommCStarAlgebra`, `CStarAlgebra` and `CommCStarAlgebra`. Each class extends a normed ring, a star ring, `CompleteSpace`, `CStarRing` and the scalar action of `ℂ` with `StarModule ℂ A`. So a C*-algebra in Mathlib is always complex and complete. The parent projections are instances, so `CStarAlgebra.toNonUnitalCStarAlgebra` and `CommCStarAlgebra.toCStarAlgebra` make every lemma for the weaker class available for the stronger one. The file gives instances for products, `MulOpposite.instCStarAlgebra`, closed star subalgebras with `StarSubalgebra.cstarAlgebra` and `NonUnitalStarSubalgebra.nonUnitalCStarAlgebra`, and for `ℂ` itself with `instCommCStarAlgebraComplex`.

The examples are spread over several files. The file `Mathlib.Analysis.CStarAlgebra.ContinuousMap` gives `ContinuousMap.instCommCStarAlgebra` for `C(X, ℂ)` with `X` compact, `ContinuousMap.instCStarAlgebra` for functions into any C*-algebra, the bounded continuous functions with `BoundedContinuousFunction.instCommCStarAlgebra`, and the functions that vanish at infinity with `ZeroAtInftyContinuousMap.instNonUnitalCommCStarAlgebra`. The file `Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap` holds one instance, `instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace`, which makes `E →L[ℂ] E` a C*-algebra for a complex Hilbert space `E`. The file `Mathlib.Analysis.CStarAlgebra.lpSpace` makes `lp A ∞`, the bounded families of elements of C*-algebras, a C*-algebra.

The file `Mathlib.Analysis.CStarAlgebra.Matrix` puts the operator norm on matrices. The map `Matrix.toEuclideanCLM` sends a matrix to the operator on `EuclideanSpace 𝕜 n`, and the norm `Matrix.instL2OpNormedRing` is the norm of this operator, with `Matrix.l2_opNorm_def` and `Matrix.cstar_norm_def`. The norm is not an instance by default, because `Matrix` already has other norms. The command `open scoped Matrix.Norms.L2Operator` activates it, together with `Matrix.instCStarRing` and `Matrix.instCStarAlgebra`. The lemma `Matrix.l2_opNorm_conjTranspose_mul_self` is the C*-identity, and `Matrix.l2_opNorm_mulVec`, `Matrix.l2_opNorm_mul` and `Matrix.l2_opNorm_diagonal` are the basic bounds. The lemma `entry_norm_bound_of_unitary` says that each entry of a unitary matrix has norm at most $1$.

The file `Mathlib.Analysis.CStarAlgebra.Spectrum` proves the spectral facts of the overview. `IsSelfAdjoint.spectralRadius_eq_nnNorm` and `IsStarNormal.spectralRadius_eq_nnNorm` give $r(a) = \|a\|$ for self-adjoint and for normal elements. `CStarAlgebra.toReal_spectralRadius_star_mul_self_eq_norm_sq` gives $r(a^* a) = \|a\|^2$ for all `a`. `spectrum.subset_circle_of_unitary` and `Unitary.spectrum_subset_circle` put the spectrum of a unitary on the circle. `IsSelfAdjoint.mem_spectrum_eq_re` and `IsSelfAdjoint.im_eq_zero_of_mem_spectrum` say that the spectrum of a self-adjoint element is real, and `IsSelfAdjoint.isConnected_spectrum_compl` says that its complement in `ℂ` is connected. The lemma `StarSubalgebra.spectrum_eq` is spectral permanence: the spectrum of an element of a closed star subalgebra is the same in the subalgebra and in the whole algebra. Its proof uses the connected complement. For maps, `NonUnitalStarAlgHom.nnNorm_apply_le` says that a star homomorphism is contractive, and `StarAlgEquiv.isometry` says that a star equivalence is isometric. The characters of a commutative C*-algebra preserve the star by `WeakDual.Complex.instStarHomClass`.

The file `Mathlib.Analysis.CStarAlgebra.Hom` strengthens the result for injective maps. `NonUnitalStarAlgHom.isometry` says that an injective star homomorphism between C*-algebras is an isometry, with `NonUnitalStarAlgHom.norm_map` for the norm form. `IsSelfAdjoint.map_spectrum_real` says that the real spectrum of a self-adjoint element does not change under such a map.

The file `Mathlib.Analysis.CStarAlgebra.Exponential` defines `selfAdjoint.expUnitary`, which sends a self-adjoint `a` to the unitary $\exp(i a)$, with `selfAdjoint.expUnitary_coe` for its value and `selfAdjoint.continuous_expUnitary` for continuity. `Commute.expUnitary_add` says that the map turns a sum of two commuting elements into a product.

The file `Mathlib.Analysis.CStarAlgebra.Unitization` adds a unit. For a non-unital C*-algebra `A`, `Unitization.instCStarRing` and `Unitization.instCStarAlgebra` make `Unitization ℂ A` a C*-algebra, and the notation `A⁺¹` for it needs `open scoped CStarAlgebra`. The norm is the operator norm of left multiplication on $A \oplus \mathbb{C}$, so the proof first shows that the map of `ContinuousLinearMap.isometry_mul_flip` is an isometry, which needs `CStarRing.instRegularNormedAlgebra`, and then proves the C*-identity with `Unitization.norm_splitMul_snd_sq`.

The file `Mathlib.Analysis.CStarAlgebra.Multiplier` defines the multiplier algebra as the type `DoubleCentralizer 𝕜 A` of pairs of continuous linear maps $(L, R)$ with $R(x) y = x L(y)$, the field `DoubleCentralizer.central`. The notation `𝓜(𝕜, A)` needs `open scoped MultiplierAlgebra`. Each element of `A` gives the pair of left and right multiplication, `DoubleCentralizer.coe`. The norm is the norm of `DoubleCentralizer.toProd`, and `DoubleCentralizer.norm_fst_eq_snd` says that both components have the same norm when `A` is a C*-ring. With `DoubleCentralizer.instCStarRing`, `DoubleCentralizer.instCompleteSpace` and `DoubleCentralizer.instCStarAlgebraComplex`, the multiplier algebra of a C*-algebra is a C*-algebra.

#### Common errors

1. `CStarRing` alone has no completeness and no scalars. A lemma on the spectrum needs `CStarAlgebra A` or `NonUnitalCStarAlgebra A`, which include `CompleteSpace A` and the action of `ℂ`.
2. The C*-norm on `Matrix n n ℂ` is a scoped instance. Without `open scoped Matrix.Norms.L2Operator`, Lean finds no norm, or a different one from another scope, and `Matrix.instCStarAlgebra` does not apply.
3. `NonUnitalStarAlgHom.isometry` needs injectivity. A star homomorphism that is not injective is only contractive, by `NonUnitalStarAlgHom.nnNorm_apply_le`.

### Exercises

1. (A) Prove from `CStarRing.norm_star_mul_self` that $\|a^*\| = \|a\|$ in a C*-ring, and compare with `norm_star`.
2. (A) Show that a unitary element `u` of a nontrivial C*-algebra has norm $1$ with `CStarRing.norm_coe_unitary`.
3. (B) Prove that the spectral radius of a normal $2 \times 2$ complex matrix is its operator norm, with `IsStarNormal.spectralRadius_eq_nnNorm` and the scoped instances that `open scoped Matrix.Norms.L2Operator` activates.
4. (B) Give a $2 \times 2$ complex matrix whose spectral radius is $0$ and whose norm is $1$, and explain why it is not normal.
5. (B) Prove that a star isomorphism between two C*-algebras preserves the norm, with `StarAlgEquiv.isometry`.
6. (C) Prove that a C*-algebra has at most one norm that makes it a C*-algebra for the given involution, with `CStarAlgebra.toReal_spectralRadius_star_mul_self_eq_norm_sq`.

### Reference

<?reference?>
