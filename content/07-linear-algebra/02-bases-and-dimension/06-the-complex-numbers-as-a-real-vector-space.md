---
title: The complex numbers as a real vector space
kind: api
modules:
  - Mathlib.LinearAlgebra.Complex.Module
  - Mathlib.LinearAlgebra.Complex.FiniteDimensional
explains:
  E2: [Complex.basisOneI, Complex.equivRealProdLm, Complex.finrank_real_complex, Complex.lift, Complex.real_algHom_eq_id_or_conj, Module.complexToReal, finrank_real_of_complex, realPart, imaginaryPart, Complex.rank_rat_complex]
  E1: auto
families: []
requires: [V02, V06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The complex numbers as a real vector space

### Overview

The field $\mathbb{C}$ of Volume 2 is a vector space of dimension $2$ over $\mathbb{R}$, with basis $1, i$. Each complex vector space is a real vector space by restriction of scalars, of twice the dimension. These facts are short, but many parts of Mathlib use them: complex analysis, Hilbert spaces, spectral theory, the orientation of the plane. The two modules of this section state them in a form that the rest of the library can apply.

The module `Mathlib.LinearAlgebra.Complex.Module` defines the module structures on $\mathbb{C}$, the real-linear maps `Complex.reLm` and `Complex.imLm`, the equivalence $\mathbb{C} \cong \mathbb{R}^2$, the basis `Complex.basisOneI`, the universal property of $\mathbb{C}$ as an $\mathbb{R}$-algebra, and the decomposition $a = \Re a + i \Im a$ in each complex module with a star operation. The module `Mathlib.LinearAlgebra.Complex.FiniteDimensional` computes the dimensions: $\dim_{\mathbb{R}} \mathbb{C} = 2$, $\dim_{\mathbb{R}} E = 2 \dim_{\mathbb{C}} E$, and the dimension of $\mathbb{C}$ over $\mathbb{Q}$.

### The library around it

#### Module structures and the standard basis

The instance `Complex.instModule` makes $\mathbb{C}$ a module over each semiring $R$ that acts on $\mathbb{R}$, with $r \cdot (x + y i) = r x + (r y) i$. The case $R = \mathbb{R}$ is the real vector space; the case $R = \mathbb{C}$ is the module of $\mathbb{C}$ over itself, and the two agree on real scalars by `Complex.coe_smul`. The instance `Complex.instAlgebraOfReal` makes $\mathbb{C}$ an $R$-algebra for each such $R$, and `Complex.coe_algebraMap` says that the map $\mathbb{R} \to \mathbb{C}$ of the algebra is the coercion `Complex.ofReal`. The bundled forms are `Complex.ofRealAm`, the inclusion as an algebra map, and the two real-linear maps `Complex.reLm` and `Complex.imLm`.

The coordinates give an isomorphism with the plane.

**Definition (`Complex.equivRealProdLm`).** The real-linear equivalence `Complex.equivRealProdLm : ℂ ≃ₗ[ℝ] ℝ × ℝ` sends $z$ to $(\Re z, \Im z)$.

Its inverse sends $(a, b)$ to $a + b i$ (`Complex.equivRealProdLm_symm_apply`). Through it, a basis of $\mathbb{R} \times \mathbb{R}$ gives a basis of $\mathbb{C}$.

**Definition (`Complex.basisOneI`).** The basis `Complex.basisOneI : Module.Basis (Fin 2) ℝ ℂ` has the vectors $1$ and $i$.

The lemma `Complex.coe_basisOneI` lists the vectors as `![1, Complex.I]`, and `Complex.coe_basisOneI_repr` says that the coordinates of $z$ are `![z.re, z.im]`. The matrix of a real-linear map $\mathbb{C} \to \mathbb{C}$ in this basis is a $2 \times 2$ real matrix. For complex conjugation it is the diagonal matrix with entries $1$ and $-1$ (`Complex.toMatrix_conjAe`). The bundled conjugation `Complex.conjAe` is an element of the Galois group of $\mathbb{C}$ over $\mathbb{R}$.

#### Dimensions

The basis gives the first dimension count.

**Theorem (`Complex.finrank_real_complex`).** `Module.finrank ℝ ℂ = 2`.

*Proof.* The basis `Complex.basisOneI` is indexed by `Fin 2`, and the finite rank of a free module is the number of vectors of a basis (Section 3). $\square$

The cardinal form is `Complex.rank_real_complex`, and `Complex.instFiniteDimensionalReal` is the instance `FiniteDimensional ℝ ℂ`. The instance `Complex.finrank_real_complex_fact` provides the same equation as a `Fact`, for the parts of the library that take the dimension as an instance argument, such as the orientation of the plane in volume 22.

Each complex vector space is a real one.

**Definition (`Module.complexToReal`).** For a $\mathbb{C}$-module $E$, `Module.complexToReal E` is the $\mathbb{R}$-module structure obtained by restriction of scalars along $\mathbb{R} \to \mathbb{C}$.

It is an instance, with the compatibility instances `IsScalarTower.complexToReal`, `SMulCommClass.complexToReal` and `StarModule.complexToReal`, and the instance `FiniteDimensional.complexToReal` says that a finite dimensional complex space is finite dimensional over $\mathbb{R}$. The structure `Algebra.complexToReal` does the same for algebras; it is not an instance, to avoid two paths to the same algebra structure.

**Theorem (`finrank_real_of_complex`).** For a complex vector space $E$, `Module.finrank ℝ E = 2 * Module.finrank ℂ E`.

*Proof.* This is the tower law `Module.finrank_mul_finrank` of Section 5 for $\mathbb{R} \subseteq \mathbb{C}$ and $E$, with $\dim_{\mathbb{R}} \mathbb{C} = 2$. Concretely, if $e_1, \dots, e_n$ is a complex basis of $E$, then $e_1, i e_1, \dots, e_n, i e_n$ is a real basis. $\square$

The cardinal form is `rank_real_of_complex`. Over the rationals the dimensions are large: `Complex.rank_rat_complex` and `Real.rank_rat_real` say that $\mathbb{C}$ and $\mathbb{R}$ both have dimension the continuum over $\mathbb{Q}$. Their proofs use `cardinalMk_eq_cardinalMk_field_pow_rank` from Section 5: a vector space of infinite dimension $\kappa$ over a countable field has cardinality $\kappa$. Two $\mathbb{Q}$-vector spaces of the same dimension are isomorphic, so `Complex.nonempty_linearEquiv_real` gives a $\mathbb{Q}$-linear isomorphism $\mathbb{C} \cong \mathbb{R}$, a map with no explicit description.

#### Algebra maps out of the complex numbers

An $\mathbb{R}$-algebra map out of $\mathbb{C}$ is determined by the image of $i$, which must square to $-1$.

**Theorem (`Complex.lift`).** For a real algebra $A$, the $\mathbb{R}$-algebra maps $\mathbb{C} \to A$ correspond to the elements $I' \in A$ with $I' \cdot I' = -1$.

*Proof sketch.* The map for $I'$ is `Complex.liftAux I' h`, which sends $x + y i$ to $x + y I'$ (`Complex.liftAux_apply`). It is multiplicative because $I'^2 = -1$. An algebra map $f$ is determined by $f(i)$, since $f$ is real-linear and $1, i$ is a basis; this is `Complex.algHom_ext`. $\square$

The lemma `Complex.range_liftAux` says that the range of the map for $I'$ is the subalgebra generated by $I'$, and `Complex.adjoin_I` that $i$ generates $\mathbb{C}$ over $\mathbb{R}$. For $A = \mathbb{C}$ the only square roots of $-1$ are $i$ and $-i$, so there are two maps.

**Corollary (`Complex.real_algHom_eq_id_or_conj`).** An $\mathbb{R}$-algebra endomorphism of $\mathbb{C}$ is the identity or complex conjugation.

The lemma `Complex.liftAux_neg_I` says that $-i$ gives conjugation. The corollary computes the Galois group of $\mathbb{C}$ over $\mathbb{R}$, which volume 11 uses.

#### Real and imaginary parts in star modules

Let $A$ be a complex module with a star operation compatible with conjugation, for example the complex matrices with the conjugate transpose, or the operators on a Hilbert space with the adjoint. An element is self adjoint when $a^* = a$. The module `Mathlib.LinearAlgebra.Complex.Module` defines the real and imaginary parts.

**Definition (`realPart` and `imaginaryPart`).** The real-linear maps `realPart : A →ₗ[ℝ] selfAdjoint A` and `imaginaryPart : A →ₗ[ℝ] selfAdjoint A` send $a$ to $\frac{1}{2}(a + a^*)$ and to $-\frac{i}{2}(a - a^*)$ (`realPart_apply_coe` and `imaginaryPart_apply_coe`).

The main identity is `realPart_add_I_smul_imaginaryPart`: $a = \Re a + i \Im a$. The decomposition is unique, by `ComplexStarModule.ext`. The notation `ℜ a` and `ℑ a` in the scope ComplexStarModule abbreviates the two maps. Both maps are surjective (`realPart_surjective` and `imaginaryPart_surjective`), the imaginary part vanishes exactly on the self adjoint elements (`imaginaryPart_eq_zero_iff`), and complex scalars act by the rule `realPart_smul`. Two consequences link the parts to the product: `star_mul_self_eq_realPart_sq_add_imaginaryPart_sq` writes $a^* a$ as $(\Re a)^2 + (\Im a)^2$ when $a$ is normal, and `isStarNormal_iff_commute_realPart_imaginaryPart` says that $a$ is normal if and only if $\Re a$ and $\Im a$ commute. For $A = \mathbb{C}$, `Complex.selfAdjointEquiv` identifies the self adjoint complex numbers with $\mathbb{R}$. In ordered star modules, `nonneg_iff_realPart_imaginaryPart` says that $a \ge 0$ if and only if $\Re a \ge 0$ and $\Im a = 0$.

#### Common errors

1. A complex vector space has two module structures in view, over $\mathbb{C}$ and over $\mathbb{R}$. `Module.finrank ℂ E` and `Module.finrank ℝ E` are different numbers; give the ring of scalars explicitly.
2. `Complex.basisOneI` is a real basis. It is not a basis of $\mathbb{C}$ over $\mathbb{C}$, where the basis has one vector.
3. `realPart a` is an element of the subtype `selfAdjoint A`, not of $A$. Write `(realPart a : A)` with a coercion to use it in a sum with elements of $A$.

### Exercises

1. (A) Compute the coordinates of $3 - 2i$ in the basis `Complex.basisOneI`.
2. (A) Prove that `Module.finrank ℝ (Fin 3 → ℂ) = 6`.
3. (B) Show that $\Re(i a) = -\Im a$ in a complex star module, with `realPart_I_smul`.
4. (B) Show that the real-linear map $z \mapsto i z$ on $\mathbb{C}$ has matrix with rows $(0, -1)$ and $(1, 0)$ in the basis `Complex.basisOneI`.
5. (B) Let $A$ be the real algebra of $2 \times 2$ real matrices. Find an element $J \in A$ with $J^2 = -1$, and describe the algebra map $\mathbb{C} \to A$ that `Complex.lift` gives.
6. (C) Prove that each real-linear map $f : \mathbb{C} \to \mathbb{C}$ can be written as $f(z) = a z + b \bar z$ for unique $a, b \in \mathbb{C}$.

### Reference

<?reference?>
