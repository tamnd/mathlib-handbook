---
title: Graded algebras and their maps
kind: api
modules:
  - Mathlib.RingTheory.GradedAlgebra.Basic
  - Mathlib.RingTheory.GradedAlgebra.AlgHom
  - Mathlib.RingTheory.GradedAlgebra.RingHom
  - Mathlib.RingTheory.GradedAlgebra.TensorProduct
  - Mathlib.RingTheory.GradedAlgebra.FiniteType
  - Mathlib.RingTheory.GradedAlgebra.Noetherian
  - Mathlib.RingTheory.FilteredAlgebra.Basic
explains:
  E2: [GradedRing, GradedAlgebra, DirectSum.decomposeAlgEquiv, GradedRing.projZeroRingHom, GradedRing.GradeZero.isNoetherianRing, GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_ne_zero, GradedRingHom, DirectSum.decompose_map, GradedAlgebra.baseChange, IsRingFiltration]
  E1: auto
families: []
requires: [V06, V07, V08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Graded algebras and their maps

### Overview

A graded ring is a ring $A$ with a decomposition $A = \bigoplus_{i \in \iota} A_i$ into additive subgroups, such that $1 \in A_0$ and $A_i A_j \subseteq A_{i+j}$. The polynomial ring $k[X_0, \dots, X_n]$ graded by total degree is the main example. Its homogeneous ideals describe the closed subsets of projective space, and its homogeneous localizations give the affine charts. The tensor, exterior and Clifford algebras of Volume 8 are graded in the same way.

In Mathlib the grading is internal. The ring $A$ is a type, and the grading is a family `𝒜 : ι → σ` of subobjects of $A$, for example `𝒜 : ℕ → Submodule R A`. The class `GradedRing 𝒜` says that this family is a grading. This section describes the class, the decomposition of an element into its homogeneous components, the degree zero part, the maps that preserve a grading, base change, and the related notion of a filtered ring. The next two sections treat homogeneous ideals and homogeneous localization.

### The library around it

#### The class GradedRing

Let $\iota$ be an additive monoid with decidable equality and let $A$ be a semiring. A family `𝒜 : ι → σ`, where `σ` is a type of additive submonoids of $A$ such as `Submodule R A` or `AddSubgroup A`, is a grading when two conditions hold.

1. The family is multiplicative: $1 \in A_0$ and $A_iA_j \subseteq A_{i+j}$. This is the class `SetLike.GradedMonoid 𝒜`.
2. Every element is in a unique way a finite sum of elements $a_i \in A_i$. This is the class `DirectSum.Decomposition 𝒜`, with the map `DirectSum.decompose 𝒜 : A ≃ ⨁ i, 𝒜 i`.

The class `GradedRing 𝒜` extends both. For a family of submodules of an $R$-algebra, `GradedAlgebra 𝒜` is the same class under another name. An element $a$ is homogeneous of degree $i$ when $a \in A_i$, and `SetLike.IsHomogeneousElem 𝒜 a` says that $a$ is homogeneous of some degree.

The decomposition respects the ring structure. The lemmas `DirectSum.decompose_one` and `DirectSum.decompose_mul` say that it sends $1$ to $1$ and a product to the product in the direct sum, and `DirectSum.decompose_algebraMap` does the same for scalars. The bundled forms are `DirectSum.decomposeRingEquiv 𝒜 : A ≃+* ⨁ i, 𝒜 i` and `DirectSum.decomposeAlgEquiv 𝒜 : A ≃ₐ[R] ⨁ i, 𝒜 i`. The component of degree $i$ is the projection `GradedRing.proj 𝒜 i : A →+ A`, and `GradedAlgebra.proj 𝒜 i` is its $R$-linear form. The simp lemma `GradedRing.proj_apply` unfolds the projection to the coercion of `DirectSum.decompose 𝒜 r i`, so the simp normal form of the $i$-th component of $r$ is `(decompose 𝒜 r i : A)`.

There are two ways to build an instance. If the family is a `SetLike.GradedMonoid` and the sum of the $A_i$ is direct and equal to $A$ in the sense of `DirectSum.IsInternal`, then `DirectSum.IsInternal.gradedAlgebra` gives the grading, through the algebra isomorphism `DirectSum.IsInternal.coeAlgEquiv`. If a decomposition map $A \to \bigoplus_i A_i$ is known as an algebra map, `GradedAlgebra.ofAlgHom` checks only that it is a right inverse of the sum map and that it sends $x \in A_i$ to the term $x$ in degree $i$. The library has the instances `MvPolynomial.gradedAlgebra`, `TensorAlgebra.gradedAlgebra`, `ExteriorAlgebra.gradedAlgebra` and `CliffordAlgebra.gradedAlgebra`, and the weighted grading `MvPolynomial.weightedGradedAlgebra`.

#### Products with a homogeneous element

Let $a \in A_i$ and $b = \sum_j b_j$. Then $ab = \sum_j ab_j$ with $ab_j \in A_{i+j}$. When addition in $\iota$ is cancellative, the index $i + j$ determines $j$, so $(ab)_{i+j} = ab_j$. These formulas are the core of many proofs with gradings.

| Lean name | Statement |
|---|---|
| `DirectSum.coe_decompose_mul_add_of_left_mem` | $a \in A_i \Rightarrow (ab)_{i+j} = a\,b_j$ |
| `DirectSum.coe_decompose_mul_add_of_right_mem` | $b \in A_j \Rightarrow (ab)_{i+j} = a_i\,b$ |
| `DirectSum.coe_decompose_mul_of_left_mem_zero` | $a \in A_0 \Rightarrow (ab)_j = a\,b_j$ |
| `DirectSum.coe_decompose_mul_of_left_mem` | for $\iota = \mathbb{N}$ and similar: $(ab)_n = a\,b_{n-i}$ if $i \le n$, else $0$ |
| `DirectSum.coe_decompose_mul_of_left_mem_of_not_le` | $a \in A_i$ and $i \not\le n \Rightarrow (ab)_n = 0$ |
| `DirectSum.decompose_mul_add_left` | the same as the first line, with $a$ a term of $A_i$ |

The lemmas with `_of_le` and `_of_not_le` ask for a canonically ordered index, such as $\mathbb{N}$, with a truncated subtraction.

#### The degree zero part

Let $\iota$ be canonically ordered, for example $\iota = \mathbb{N}$. Then the map $a \mapsto a_0$ is a ring homomorphism. The proof is short: $1 \in A_0$ gives $1_0 = 1$, and for a product, $(ab)_0 = \sum_{i+j=0} a_ib_j = a_0b_0$, because in a canonically ordered monoid $i + j = 0$ forces $i = j = 0$. The map is `GradedRing.projZeroRingHom 𝒜 : A →+* A`, and `GradedRing.projZeroRingHom' 𝒜 : A →+* 𝒜 0` is the same map with values in the subring $A_0$. It is surjective, `GradedRing.projZeroRingHom'_surjective`, since it is the identity on $A_0$.

**Proposition.** If $A$ is a Noetherian ring graded by a canonically ordered monoid, then $A_0$ is Noetherian.

*Proof.* The ring $A_0$ is the image of the surjective ring map $a \mapsto a_0$. A quotient of a Noetherian ring is Noetherian. $\square$

This is the instance `GradedRing.GradeZero.isNoetherianRing`, the only declaration of the module `Mathlib.RingTheory.GradedAlgebra.Noetherian`. Its proof is `isNoetherianRing_of_surjective` applied to `GradedRing.projZeroRingHom'`.

**Proposition.** Let $S$ be a graded commutative ring that is of finite type over $S_0$. Then $S$ is generated over $S_0$ by finitely many homogeneous elements, and these can be chosen of nonzero degree.

*Proof.* Let $s_1, \dots, s_m$ generate $S$ over $S_0$. Each $s_k$ is the finite sum of its components, and these components are in the subalgebra that they generate. So the finite set of all components generates $S$. A generator of degree $0$ is in $S_0$, so it can be removed. $\square$

The two forms are `GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous` and `GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_ne_zero`, both with the hypothesis `[Algebra.FiniteType (𝒜 0) S]`. They are the input of the finiteness result for homogeneous localizations in Section 3.

#### Graded ring homomorphisms

A ring homomorphism $f : A \to B$ between graded rings is graded when $f(A_i) \subseteq B_i$ for every $i$. The structure `GradedRingHom 𝒜 ℬ`, with notation `𝒜 →+*ᵍ ℬ`, is a ring homomorphism with the field `map_mem`. The library does not define a separate class of graded homomorphisms. A lemma about an arbitrary graded map uses the three classes `[FunLike F A B] [GradedFunLike F 𝒜 ℬ] [RingHomClass F A B]`, where `GradedFunLike` records the condition $f(A_i) \subseteq B_i$. The structures `GradedRingHom` and `GradedAlgHom` are instances of these classes.

A graded map commutes with the decomposition: $f(x)_i = f(x_i)$. Indeed, $f(x) = \sum_i f(x_i)$ with $f(x_i) \in B_i$, and the decomposition in $B$ is unique. This is `DirectSum.decompose_map`, which writes the decomposition of $f(x)$ as `DirectSum.map` of the restrictions of $f$ to the components, and `GradedRingHom.map_directSumDecompose`, which is the form for one component. The restriction to degree $i$ is `GradedRingHom.gradedAddHom f i : 𝒜 i →+ ℬ i`, and the restriction to degree $0$ is the ring map `GradedRingHom.gradedZeroRingHom f`.

The API follows that of `RingHom`: `GradedRingHom.id`, `GradedRingHom.comp`, the lemmas `GradedRingHom.comp_assoc`, `GradedRingHom.id_comp` and `GradedRingHom.comp_id`, the extensionality lemma `GradedRingHom.ext`, `GradedRingHom.copy` to change the underlying function to a propositionally equal one, and `GradedRingHom.ofClass` to bundle a map of a class. The coercion to `A →+* B` is `GradedRingHom.toRingHom`. The graded endomorphisms of $A$ form a monoid under composition, by `GradedRingHom.instMonoid`.

The structure `GradedAlgHom 𝒜 ℬ`, with notation `𝒜 →ₐᵍ[R] ℬ`, is the graded version of an $R$-algebra homomorphism. It has the same API, with `GradedAlgHom.toAlgHom` and `GradedAlgHom.toGradedRingHom` as the forgetful maps. The constructor `GradedAlgHom.mk'` builds one from a graded ring map that is $R$-linear. The map `GradedAlgHom.restrictScalars` restricts the scalars along a tower $R_0 \to R$, and `GradedAlgHom.toEnd` is the monoid map from graded endomorphisms to all algebra endomorphisms.

#### Base change

Let $A$ be a graded $R$-algebra and $S$ a commutative $R$-algebra. Then $S \otimes_R A$ is a graded $S$-algebra, with degree $i$ part the image of $S \otimes_R A_i$. This image is `Submodule.baseChange S (𝒜 i)`, and the instance is `GradedAlgebra.baseChange`. For example, $S \otimes_R R[X_1, \dots, X_n] \cong S[X_1, \dots, X_n]$, with the grading by degree. The module also gives the ring and algebra instances on the degree zero part of the base change directly, since unification finds them slowly.

The map $a \mapsto 1 \otimes a$ is graded, `GradedAlgHom.includeRight`. The equivalence `GradedAlgHom.liftEquiv` is the universal property: graded $R$-algebra maps $A \to B$, for a graded $S$-algebra $B$ seen over $R$, correspond to graded $S$-algebra maps $S \otimes_R A \to B$. In the words of category theory, base change is left adjoint to restriction of scalars, also for graded algebras.

#### Filtered rings

A filtration is the increasing analogue of a grading. A family $(F_i)_{i \in \iota}$ of subobjects is a filtration when it is monotone, and the module `Mathlib.RingTheory.FilteredAlgebra.Basic` records it with a second family $F_{<j}$ that plays the role of $\bigcup_{i<j} F_i$. The class `IsFiltration F F_lt` asks that $F$ is monotone (`IsFiltration.mono`), that $F_i \le F_{<j}$ for $i < j$ (`IsFiltration.is_le`), and that $F_{<j}$ is the least upper bound of these $F_i$ (`IsFiltration.is_sup`). The lemma `IsFiltration.F_lt_le_F` gives $F_{<j} \le F_j$.

The class `IsRingFiltration F F_lt` adds the condition $F_iF_j \subseteq F_{i+j}$ and $1 \in F_0$, as a `SetLike.GradedMonoid` instance. The class `IsModuleFiltration F F_lt FM FM_lt` is the form for a module $M$ over a filtered ring: $F_i \cdot FM_j \subseteq FM_{i + j}$. For the index $\mathbb{Z}$ the second family is $F_{<n} = F_{n-1}$, and the constructors `IsFiltration.mk_int`, `IsRingFiltration.mk_int` and `IsModuleFiltration.mk_int` need only monotonicity and the multiplicative condition. An example: for an ideal $I$ of $A$, put $F_n = I^{-n}$ for $n \le 0$ and $F_n = A$ for $n \ge 0$. This is an increasing ring filtration indexed by $\mathbb{Z}$. The $I$-adic filtrations of Chapter 6 use the other convention, a decreasing sequence indexed by $\mathbb{N}$, with the structure `Ideal.Filtration`.

#### Common errors

1. The grading is a family of subobjects, not of types. A component `decompose 𝒜 a i` is a term of the subtype `𝒜 i`, and a proof often needs its coercion `(decompose 𝒜 a i : A)`. Most simp lemmas are stated for the coerced form.
2. `GradedRing 𝒜` is data, not a proposition, because it contains the decomposition map. Two instances on the same family are equal in fact, but not by definition. Do not build a second instance next to a library instance such as `MvPolynomial.gradedAlgebra`.
3. The degree zero ring map `GradedRing.projZeroRingHom` needs a canonically ordered index. For a grading by $\mathbb{Z}$, the map $a \mapsto a_0$ is not multiplicative: in $k[X, X^{-1}]$, the product $X \cdot X^{-1}$ has degree $0$ part $1$, but the factors have degree $0$ parts $0$.

### Exercises

1. (A) Show that the homogeneous components of $1$ in a graded ring are $1$ in degree $0$ and $0$ elsewhere, with `DirectSum.decompose_one`.
2. (A) Let $f : A \to B$ be a graded ring map. Show that $f$ sends a homogeneous element of degree $i$ to a homogeneous element of degree $i$.
3. (B) Let $A$ be graded by $\mathbb{N}$. Show that $A_+ = \bigoplus_{i > 0} A_i$ is the kernel of `GradedRing.projZeroRingHom`, and that $A/A_+ \cong A_0$.
4. (B) Show that $k[X, Y]$ is graded by $\mathbb{N}$ with $X$ of degree $2$ and $Y$ of degree $3$, and find the dimension of each graded piece of degree at most $6$.
5. (B) Let $A$ be graded by $\mathbb{N}$ and generated over $A_0$ by finitely many elements of degree $1$. Show that each $A_n$ is a finite $A_0$-module.
6. (C) Let $A$ be graded by $\mathbb{N}$. Show that $A$ is Noetherian if and only if $A_0$ is Noetherian and $A$ is of finite type over $A_0$.

### Reference

<?reference?>
