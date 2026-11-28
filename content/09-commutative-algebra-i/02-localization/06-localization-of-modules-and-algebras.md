---
title: Localization of modules and algebras
kind: api
modules:
  - Mathlib.RingTheory.Localization.Module
  - Mathlib.RingTheory.Localization.BaseChange
  - Mathlib.RingTheory.Localization.Algebra
  - Mathlib.RingTheory.Localization.Finiteness
  - Mathlib.RingTheory.Localization.Free
  - Mathlib.RingTheory.Localization.Integral
  - Mathlib.RingTheory.Localization.LocalizationLocalization
  - Mathlib.RingTheory.Localization.NormTrace
  - Mathlib.RingTheory.Localization.Submodule
  - Mathlib.RingTheory.Localization.AtPrime.Extension
explains:
  E2: [isLocalizedModule_iff_isBaseChange, IsLocalization.tensorRight, LinearIndependent.localization, IsLocalization.ker_map, Module.Finite.of_isLocalization, Module.Finite.of_localizationSpan, IsLocalization.integerNormalization_spec, IsLocalization.isLocalization_of_is_exists_mul_mem, Algebra.trace_localization, IsLocalization.coeSubmodule_mul]
  E1: auto
families: []
requires: [V07.C01, V07.C08, V08.C02, V09.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Localization of modules and algebras

### Overview

Volume 7 defines the localization $M_S$ of a module $M$ through the predicate `IsLocalizedModule S f`, and Section 1 defines the localization $S^{-1} R$ of a ring. The modules of this section connect the two notions. They identify $M_S$ with the base change $S^{-1} R \otimes_R M$, they localize an $R$-algebra $A$ at the image of $S$, and they show which properties pass from $M$ or $A$ to the localization: linear independence, bases, finite generation, integrality, norms and traces.

A second theme is the local nature of some properties. A module is finitely generated when its localizations at a finite family of elements that generate the unit ideal are finitely generated. Statements of this kind reduce a global question to a question over the rings $R_f$, and they prepare the local methods of the later chapters.

Throughout, $S$ is a submonoid of $R$, $R_S$ is a localization of $R$ at $S$, and for an $R$-algebra $A$ the symbol $A_S$ is the localization of $A$ at the image `Algebra.algebraMapSubmonoid A S` of $S$.

### The library around it

#### Base change

The module `Mathlib.RingTheory.Localization.BaseChange` proves that localization is base change. The central result is `isLocalizedModule_iff_isBaseChange`: for an $R$-linear map $f : M \to M'$ into an $R_S$-module $M'$, $f$ is a localization at $S$ exactly when it is a base change along $R \to R_S$. Proof sketch: both conditions say that $f$ is universal among $R$-linear maps from $M$ into $R_S$-modules. For the localization this is the universal property of `IsLocalizedModule`, because an $R_S$-module is the same as an $R$-module on which each element of $S$ acts bijectively. For the base change it is the universal property of the tensor product with $R_S$.

The concrete form is `LocalizedModule.equivTensorProduct`, an isomorphism of `Localization S`-modules between `LocalizedModule S M` and `TensorProduct R (Localization S) M`. The instance `IsLocalization.tensorProduct_isLocalizedModule` says that $m \mapsto 1 \otimes m$ is a localization of modules, and `IsLocalizedModule.isBaseChange` gives the other direction.

For algebras, the same result reads: `Algebra.isLocalization_iff_isPushout` says that an algebra $B$ over $T$ and $R_S$ is the localization of $T$ at the image of $S$ exactly when the square of $R$, $T$, $R_S$ and $B$ is a pushout. So the instance `IsLocalization.tensorRight` says that $R_S \otimes_R T$ is a localization of $T$ at the image of $S$, and `IsLocalization.Away.tensor` is the version for one element $r$. The concrete isomorphism `Localization.tensorLeftAlgEquiv` identifies $T \otimes_R S^{-1} R$ with the localization of $T$ at the image of $S$.

#### Linear maps, independence and bases

The module `Mathlib.RingTheory.Localization.Module` holds the linear algebra of localized modules. An $R$-linear map between two $R_S$-modules is automatically $R_S$-linear. This is `LinearMap.extendScalarsOfIsLocalization`, with the equivalence version `LinearEquiv.extendScalarsOfIsLocalization`. The reason: for $s \in S$ and $x \in M$, the element $f(s^{-1} x)$ satisfies $s f(s^{-1} x) = f(x)$, and $s$ acts bijectively on the target. The functor `LocalizedModule.map` sends an $R$-linear map to the induced $R_S$-linear map, and `IsLocalizedModule.mapEquiv` does the same for an isomorphism between two models.

Linear independence passes to the localization: `LinearIndependent.localization` says that a family that is independent over $R$ in an $R_S$-module stays independent over $R_S$. Proof: a relation $\sum (r_i / s) b_i = 0$ gives $\sum r_i b_i = 0$ after multiplication by $s$, so all $r_i = 0$. For a fraction field, the converse also holds, and `LinearIndependent.iff_fractionRing` states the equivalence. A basis of $M$ gives a basis of the localization: `Module.Basis.ofIsLocalizedModule` for a module and `Module.Basis.localizationLocalization` for an algebra $A_S$ over $R_S$. The lemma `span_eq_top_localization_localization` says that a spanning set of $A$ over $R$ spans $A_S$ over $R_S$.

#### Localization of algebras

The module `Mathlib.RingTheory.Localization.Algebra` localizes algebra maps. An $R$-algebra map $f : A \to B$ induces an $R_S$-algebra map `IsLocalization.mapₐ` from $A_S$ to $B_S$. It is injective when $f$ is injective, `IsLocalization.mapₐ_injective_of_injective`, and surjective when $f$ is surjective, `IsLocalization.mapₐ_surjective_of_surjective`. The kernel of a localized ring map is the localization of the kernel: `IsLocalization.ker_map` says that $\ker(S^{-1} g) = \ker(g) \cdot S^{-1} R$. Proof: if $g(r)/s' = 0$ in the target, then $t g(r) = g(u r) = 0$ for some $u$ in $S$, with $t = g(u)$. So $u r \in \ker g$ and $r / s = (u r)/(u s)$ is in the extended ideal. The map `AlgHom.toKerIsLocalization` makes the same statement as a map of modules on the kernels. Polynomial rings commute with localization: `Polynomial.isLocalization` says that $A[X]$ is a localization of $R[X]$ at the constants in $S$ when $A$ is a localization of $R$.

#### Ideals as submodules

The module `Mathlib.RingTheory.Localization.Submodule` sends an ideal $I$ of $R$ to the $R$-submodule `IsLocalization.coeSubmodule S I` of $S$, the image of $I$. Its membership lemma is `IsLocalization.mem_coeSubmodule`. The map respects products and spans: `IsLocalization.coeSubmodule_mul` states $\iota(I J) = \iota(I) \iota(J)$, and `IsLocalization.coeSubmodule_span` gives the image of `Ideal.span s`. The proof of the product rule: both sides are spanned by the images $\iota(a b)$ with $a \in I$ and $b \in J$, since $\iota$ is a ring map. For a fraction field the map is injective, `IsFractionRing.coeSubmodule_injective`. When $S$ has no zero divisors, $I$ is principal exactly when its image is principal, `IsLocalization.coeSubmodule_isPrincipal`. When $R \to R_S$ is injective, $I$ is finitely generated exactly when its image is finitely generated, `IsLocalization.coeSubmodule_fg`. These facts are the base of the theory of fractional ideals. The module also proves that a localization of a Noetherian ring is Noetherian, `IsLocalization.isNoetherianRing`, and `Algebra.EssFiniteType.isNoetherianRing` extends this to algebras of essentially finite type over a Noetherian ring.

#### Finiteness and local criteria

The module `Mathlib.RingTheory.Localization.Finiteness` has two kinds of results. The first kind passes finiteness to a localization. `Module.Finite.of_isLocalization` says that $A_S$ is finite over $R_S$ when $A$ is finite over $R$: the images of generators of $A$ over $R$ generate $A_S$, because each element of $A_S$ is $a/s$ with $a \in A$ and $s \in S$. The module version is `Module.Finite.of_isLocalizedModule`, and `Submodule.localized_fg` says that a finitely generated submodule has a finitely generated localization.

The second kind goes back from the localizations to $M$. Let $t \subseteq R$ generate the unit ideal. Then `Module.Finite.of_localizationSpan` says that $M$ is finite over $R$ when each `LocalizedModule.Away g M` is finite over $R_g$, for $g \in t$. The proof sketch: since the ideal generated by $t$ is $R$, a finite subset of $t$ already generates $R$. For each $g$ of this subset, choose finitely many elements of $M$ whose images generate $M_g$, by `multiple_mem_span_of_mem_localization_span`. Let $N$ be the submodule that all these elements generate. Then $(M/N)_g = 0$ for each $g$, so each element of $M/N$ is killed by a power of each $g$. The powers generate the unit ideal, so $M/N = 0$. The same method gives `Ideal.fg_of_localizationSpan` for ideals and `RingHom.ker_fg_of_localizationSpan` for kernels.

The module `Mathlib.RingTheory.Localization.Free` adds the spreading out of a free localization. If $M$ is finitely presented and $M_S$ is free over $R_S$, then `Module.FinitePresentation.exists_free_localizedModule_powers` gives one $r \in S$ such that $M_r$ is already free over $R_r$, with the same rank. The version `Module.FinitePresentation.exists_basis_localizedModule_powers` lifts a given basis.

#### Integrality and localization

The module `Mathlib.RingTheory.Localization.Integral` clears denominators in polynomials. For a polynomial $p$ over $R_S$, `IsLocalization.integerNormalization S p` is a polynomial over $R$, and `IsLocalization.integerNormalization_spec` says that its image is $b \cdot p$ for some $b \in S$. The proof applies `IsLocalization.exist_integer_multiples_of_finset` to the finite set of coefficients of $p$. So a root of $p$ is also a root of the new polynomial, by `IsLocalization.integerNormalization_aeval_eq_zero`. As a consequence, `IsFractionRing.isAlgebraic_iff` says that an element is algebraic over a domain $A$ exactly when it is algebraic over the fraction field of $A$.

Integrality passes to localizations: `isIntegral_localization` says that $R_S \to A_S$ is integral when $A$ is integral over $R$. In the other direction, `IsIntegral.exists_multiple_integral_of_isLocalization` says that an element integral over $R_S$ has a multiple by an element of $S$ that is integral over $R$. Integral closure commutes with localization, `IsLocalization.integralClosure`. For a finite extension $L$ of the fraction field $K$ of $A$, `integralClosure.isFractionRing_of_finite_extension` says that $L$ is the fraction field of the integral closure of $A$ in $L$.

#### Localization of a localization

The module `Mathlib.RingTheory.Localization.LocalizationLocalization` shows that a localization of $R_M$ at a submonoid $N$ is again a localization of $R$. The submonoid of $R$ is `IsLocalization.localizationLocalizationSubmodule M N`, an explicit submonoid built from $M$ and $N$, and `IsLocalization.localization_localization_isLocalization` states the result. When $M \leq N$, `IsLocalization.isLocalization_of_submonoid_le` says that a localization at $N$ is a localization of $R_M$ at the image of $N$. Also, `IsLocalization.isLocalization_of_is_exists_mul_mem` says that a localization at $M$ is a localization at a larger $N$ when each element of $N$ has a multiple in $M$. Proof: each $x \in N$ has $m x \in M$ for some $m$, so the image of $x$ divides a unit and is a unit. The other conditions of the predicate hold because $M \leq N$.

The prime form is `IsLocalization.localizationLocalizationAtPrimeIsoLocalization`: for a prime $\mathfrak{q}$ of $R_M$ with contraction $\mathfrak{p}$, the localization of $R$ at $\mathfrak{p}$ is isomorphic to the localization of $R_M$ at $\mathfrak{q}$. The instance `IsLocalization.isLocalization_atPrime_localization_atPrime` states the same thing as a predicate. For fraction fields, `IsFractionRing.isFractionRing_of_isLocalization` says that the fraction field of $R$ is also the fraction field of $R_M$ when $M$ has no zero divisor.

#### Norm, trace and extension of primes

Let $A$ be a free $R$-algebra of finite rank. The module `Mathlib.RingTheory.Localization.NormTrace` says that norm and trace commute with localization: `Algebra.norm_localization` and `Algebra.trace_localization` give $\operatorname{Tr}_{A_S / R_S}(a) = \operatorname{Tr}_{A/R}(a)$ for $a \in A$, through the maps to $R_S$ and $A_S$. The proof: a basis $b$ of $A$ gives the basis `Module.Basis.localizationLocalization` of $A_S$, and `Algebra.map_leftMulMatrix_localization` says that the matrix of multiplication by $a$ in the new basis is the image of the old matrix. Trace and determinant commute with ring maps. The discriminant follows the same rule, `Algebra.discr_localizationLocalization`.

The module `Mathlib.RingTheory.Localization.AtPrime.Extension` compares primes of $A$ over a prime $\mathfrak{p}$ of $R$ with primes of $A_{\mathfrak{p}}$ over the maximal ideal of $R_{\mathfrak{p}}$. For an integral extension, `IsLocalization.AtPrime.mem_primesOver_of_isPrime` says that each maximal ideal of $A_{\mathfrak{p}}$ lies over the maximal ideal of $R_{\mathfrak{p}}$. For a maximal $\mathfrak{P}$ over $\mathfrak{p}$, `IsLocalization.AtPrime.equivQuotientMapOfIsMaximal` identifies $A/\mathfrak{P}$ with $A_{\mathfrak{p}} / \mathfrak{P} A_{\mathfrak{p}}$. So the inertia degree and the ramification index do not change: `IsLocalization.AtPrime.inertiaDeg_map_eq_inertiaDeg` and `IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx`.

#### Common errors

1. The localization of an $R$-algebra $A$ at $S$ is a localization of $A$ at the submonoid `Algebra.algebraMapSubmonoid A S`, not at `S`. Hypotheses such as `[IsLocalization (Algebra.algebraMapSubmonoid A S) Aₛ]` must use this submonoid, and the scalar towers `[IsScalarTower R Rₛ Aₛ]` and `[IsScalarTower R A Aₛ]` must be given too.
2. `LocalizedModule.Away g M` is a module over `Localization.Away g`. A statement for a general model `Rₛ` needs `IsLocalizedModule` and the scalar tower, and a lemma such as `Module.Finite.of_localizationSpan` takes the concrete types. Convert with `IsLocalizedModule.iso` when the model is different.
3. `LinearIndependent.localization` goes from $R$ to $R_S$ only. The converse fails when $S$ contains a zero divisor. Take $R = \mathbb{Z}/6$ and $S$ the powers of $2$, so that $R_S \cong \mathbb{Z}/3$. The family $(1)$ in $R_S$ is independent over $R_S$, but $3 \cdot 1 = 0$ with $3 \neq 0$ in $R$. Use `LinearIndependent.iff_fractionRing` for the case of a fraction field.

### Exercises

1. (A) Let $R$ be a ring and $S$ a submonoid. Use `isLocalizedModule_iff_isBaseChange` to prove that $R_S \otimes_R R^n$ is a localization of $R^n$ at $S$, and compute it.
2. (A) Let $A = R[X]$. Use `Polynomial.isLocalization` and `IsLocalization.tensorRight` to give two descriptions of $R_S[X]$, and compare them.
3. (B) Let $g : R \to P$ be a ring map with kernel $I$, and let $S$ be a submonoid of $R$. Use `IsLocalization.ker_map` to prove that $S^{-1} g$ is injective exactly when each element of $I$ is killed by an element of $S$.
4. (B) Let $p = X^2 + \tfrac{1}{2} X + \tfrac{1}{3}$ over $\mathbb{Q}$. Find a polynomial over $\mathbb{Z}$ with the same roots, as `IsLocalization.integerNormalization_spec` gives, and explain why $b$ depends on a choice.
5. (B) Let $f_1, \dots, f_n$ generate the unit ideal of $R$, and let $I$ be an ideal of $R$ such that each $I R_{f_i}$ is principal. Is $I$ finitely generated? Use `Ideal.fg_of_localizationSpan`.
6. (C) Let $A$ be a free $R$-algebra of rank $n$ and $\mathfrak{p}$ a prime of $R$. Prove with `Algebra.trace_localization` and `Algebra.discr_localizationLocalization` that the trace form of $A_{\mathfrak{p}}$ over $R_{\mathfrak{p}}$ is nondegenerate when the discriminant of $A$ over $R$ is not in $\mathfrak{p}$.

### Reference

<?reference?>
