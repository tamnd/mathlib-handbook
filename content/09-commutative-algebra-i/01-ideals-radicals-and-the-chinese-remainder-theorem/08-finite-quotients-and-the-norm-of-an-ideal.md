---
title: Finite quotients and the norm of an ideal
kind: api
modules:
  - Mathlib.RingTheory.Ideal.Quotient.Index
  - Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
  - Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
  - Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Norm
  - Mathlib.RingTheory.Ideal.Norm.AbsNorm
  - Mathlib.RingTheory.Ideal.Norm.RelNorm
  - Mathlib.RingTheory.Ideal.Int
explains:
  E2: [Ideal.finite_quotient_pow, Ring.HasFiniteQuotients.maximalOfPrime, Submodule.cardQuot, cardQuot_mul_of_coprime, Ideal.absNorm, Ideal.absNorm_mem, Ideal.absNorm_dvd_absNorm_of_le, Ideal.relNorm_algebraMap, Int.card_ideal_quot, Int.cast_mem_ideal_iff]
  E1: auto
families: []
requires: [V05.C04, V06.C02, V06.C04, V07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Finite quotients and the norm of an ideal

### Overview

For a nonzero integer $n$, the quotient $\mathbb{Z}/n\mathbb{Z}$ has $|n|$ elements. The number of elements of $R/I$ is thus a measure of the size of an ideal $I$: a smaller ideal has a larger quotient. This number is the absolute norm $N(I) = |R/I|$. In the ring of integers of a number field it is finite for each nonzero ideal, it is multiplicative, $N(IJ) = N(I) N(J)$, and the norm of a principal ideal $(r)$ is the absolute value of the norm of the element $r$. These facts are the start of the arithmetic of number fields.

This section describes the files of the library that count the elements of quotients. The first part treats finite quotients in any commutative ring: the quotient by a power or by a product of ideals with finite quotients is again finite. The second part treats the class `Ring.HasFiniteQuotients` of rings in which every nonzero ideal has a finite quotient, such as $\mathbb{Z}$. The third part defines the absolute norm `Ideal.absNorm` and the relative norm `Ideal.relNorm`, which takes an ideal of $S$ to an ideal of a subring $R$. The last part computes the norms of the ideals of $\mathbb{Z}$. The multiplicativity of the norm needs unique factorization of ideals in a Dedekind domain, a subject of Volume 10, so this section states those results without proof. It uses the operations on ideals of Section 1, the quotient rings of Section 7 and the index of a subgroup from Volume 5.

### The library around it

#### Finite quotients by powers and products

The module `Mathlib.RingTheory.Ideal.Quotient.Index` works in a commutative ring $R$ with no other hypothesis. Its main result is `Ideal.finite_quotient_pow`: if $I$ is finitely generated and $R/I$ is finite, then $R/I^n$ is finite for each $n$.

Proof sketch. The quotient $R/I^n$ has a filtration by the images of $I^k$ for $k = 0, 1, \dots, n$. Each step $I^k/I^{k+1}$ is a module over $R/I$, and it is finitely generated because $I$ is finitely generated. A finitely generated module over a finite ring is finite. So each step is finite, and $R/I^n$ is finite.

The library proves a quantitative form. The lemma `Ideal.index_pow_le` bounds the index of $I^n$ as an additive subgroup: if $I$ is the span of a finset $s$, then

$$[R : I^n] \le [R : I]^{\,\sum_{i < n} |s|^i}.$$

The module version `Submodule.index_smul_le` bounds the index of $I \cdot N$ in a module $M$ by $[R : I]^{|s|} \cdot [M : N]$, when $N$ is the span of $s$. The lemma `Submodule.finite_quotient_smul` says that $M/(I \cdot N)$ is finite when $R/I$ and $M/N$ are finite and $N$ is finitely generated. For products, `Ideal.finite_quotient_prod` says that the quotient by $\prod_{i \in s} I_i$ is finite when each $I_i$ is finitely generated and each $R/I_i$ is finite. The index is the `AddSubgroup.index` of `Submodule.toAddSubgroup I`, so the results of Volume 5 on the index apply.

#### Rings with finite quotients

The module `Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients` has no declarations of its own. It imports the two modules below, and it is the common import for the class. The module `Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic` defines the class `Ring.HasFiniteQuotients R`. Its one field, `Ring.HasFiniteQuotients.finiteQuotient`, says that $R/I$ is finite for each ideal $I \ne 0$. A finite ring has the property (`Ring.HasFiniteQuotients.instOfFinite`), and so does $\mathbb{Z}$ (`Ring.HasFiniteQuotients.instInt`). The property passes up along finite extensions: `Ring.HasFiniteQuotients.of_module_finite` says that a domain $S$ that is a finite $R$-module has finite quotients when $R$ has them. So the ring of integers of a number field has finite quotients. The instance `Ring.HasFiniteQuotients.instFiniteQuotientIdealOfNeZero` gives `Finite (R ⧸ I)` from the instance `NeZero I`, so a user can put the hypothesis $I \ne 0$ in the instance context.

The class has strong consequences. The first one is `Ring.HasFiniteQuotients.maximalOfPrime`: a nonzero prime ideal $P$ is maximal.

Proof. The quotient $R/P$ is a domain because $P$ is prime, and it is finite because $P \ne 0$. A finite domain is a field: multiplication by a nonzero $a$ is injective, so it is a bijection of the finite set $R/P$, and some $b$ has $a b = 1$. So $P$ is maximal.

From this, the instance `Ring.HasFiniteQuotients.instDimensionLEOne` gives `Ring.DimensionLEOne R`. The instance `Ring.HasFiniteQuotients.instIsNoetherianRing` says that $R$ is Noetherian. The idea: for $I \ne 0$, the ideals that contain $I$ correspond to ideals of the finite ring $R/I$, so an ascending chain above a nonzero ideal stops. The lemmas `Ideal.finiteIndex` and `Ideal.isFiniteRelIndex` state the finiteness in the language of subgroups: a nonzero ideal has finite index as an additive subgroup. The instance `Ring.HasFiniteQuotients.instPerfectFieldResidueFieldOfFractionRing` says that the residue field of a prime is perfect when the fraction field is perfect.

#### The cardinality of a quotient

The module `Mathlib.RingTheory.Ideal.Norm.AbsNorm` starts with a definition for any module. For a submodule $N$ of $M$, `Submodule.cardQuot N` is the natural number `Nat.card (M ⧸ N)`, as `Submodule.cardQuot_apply` says. The function `Nat.card` takes the value $0$ on an infinite type, so `Submodule.cardQuot` is $0$ when the quotient is infinite. Thus `Submodule.cardQuot_bot` says that the quotient by $0$ has cardinality $0$ when $M$ is infinite, and `Submodule.cardQuot_top` says that $M/M$ has one element. The lemma `Submodule.cardQuot_eq_one_iff` says that the cardinality is $1$ exactly when $N = M$.

For coprime ideals the cardinality is multiplicative in any commutative ring. This is `cardQuot_mul_of_coprime`: if $I + J = R$, then $|R/IJ| = |R/I| \cdot |R/J|$. Proof: coprime ideals satisfy $IJ = I \cap J$, and the Chinese remainder theorem of Section 3 gives $R/(I \cap J) \cong R/I \times R/J$. Count both sides. In a Dedekind domain the coprimality is not needed. The lemma `cardQuot_pow_of_prime` says that $|R/P^i| = |R/P|^i$ for a nonzero prime $P$, and `cardQuot_mul` says that $|R/IJ| = |R/I| \cdot |R/J|$ for all ideals of an infinite Dedekind domain. The proof factors $I$ and $J$ into prime powers and uses the coprime case. For the prime powers, it uses the two lemmas `Ideal.exists_mul_add_mem_pow_succ` and `Ideal.mul_add_mem_pow_succ_unique`, which build an isomorphism $P^i/P^{i+1} \cong R/P$.

#### The absolute norm

For a Dedekind domain $S$, `Ideal.absNorm` is the absolute norm. Its type is `Ideal S →*₀ ℕ`, a monoid homomorphism with zero. So the multiplicativity $N(IJ) = N(I) N(J)$ is `map_mul`, and $N(S) = 1$ is `map_one`. For an infinite $S$, `Ideal.absNorm_apply` says that the norm is `Submodule.cardQuot I`, and `Ideal.absNorm_eq_natCard` and `Ideal.absNorm_eq_index` give the same value as `Nat.card (S ⧸ I)` and as an index. The special values are `Ideal.absNorm_bot` and `Ideal.absNorm_top`, and `Ideal.absNorm_eq_one_iff` says that $N(I) = 1$ exactly when $I = S$. In a ring with finite quotients, `Ideal.absNorm_eq_zero_iff` says that $N(I) = 0$ exactly when $I = 0$.

Three properties of the norm have short proofs. The first is `Ideal.absNorm_mem`: the integer $N(I)$ is an element of $I$. Proof: $S/I$ is an additive group with $N(I)$ elements, so $N(I) \cdot \bar 1 = 0$ in $S/I$ by Lagrange's theorem. The image of the integer $N(I)$ in $S/I$ is $N(I) \cdot \bar 1$, so $N(I) \in I$. When $S/I$ is infinite, $N(I) = 0 \in I$. The second is `Ideal.absNorm_dvd_absNorm_of_le`: if $J \subseteq I$, then $N(I)$ divides $N(J)$. Proof: in a Dedekind domain $J \subseteq I$ means that $I$ divides $J$, so $J = I K$ for an ideal $K$, and $N(J) = N(I) N(K)$. The third is `Ideal.isPrime_of_irreducible_absNorm`: if $N(I)$ is a prime number, then $I$ is a prime ideal, because a factorization of $I$ gives a factorization of $N(I)$.

When $S$ is a free $\mathbb{Z}$-module of finite rank, such as the ring of integers of a number field, the norm is computed by determinants. The lemma `Ideal.natAbs_det_equiv` expresses $N(I)$ as the absolute value of the determinant of an additive isomorphism $S \to I$. From this, `Ideal.absNorm_span_singleton` gives

$$N\big((r)\big) = \big|\mathrm{N}_{S/\mathbb{Z}}(r)\big|,$$

where `Algebra.norm ℤ` is the norm of an element. The lemma `Ideal.absNorm_span_natCast` gives $N((n)) = n^d$, with $d$ the rank of $S$. The lemma `Ideal.absNorm_dvd_norm_of_mem` says that $N(I)$ divides the norm of each element of $I$. For a maximal ideal $P$, `Ideal.exists_prime_and_absNorm_eq_pow` gives a prime number $p \in P$ and an exponent $n > 0$ with $N(P) = p^n$. The finiteness results `Ring.HasFiniteQuotients.finite_absNorm_le` and `Ring.HasFiniteQuotients.finite_absNorm_eq` say that only finitely many ideals have norm at most $B$, or equal to $B$. The module `Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Norm` records these facts as instances of the class `Northcott` for `Submodule.cardQuot` and for `Ideal.absNorm`.

#### The relative norm

The module `Mathlib.RingTheory.Ideal.Norm.RelNorm` treats a finite extension $R \subseteq S$ of integrally closed domains, with $S$ torsion free over $R$. The ideal `Ideal.spanNorm R I` is the ideal of $R$ that is spanned by the norms of the elements of $I$, and `Ideal.spanNorm_singleton` says that the span norm of $(r)$ is the principal ideal of the norm `Algebra.intNorm R S r`. When $R$ and $S$ are Dedekind domains, the span norm is multiplicative by `Ideal.spanNorm_mul`, and the library packs it as `Ideal.relNorm R : Ideal S →*₀ Ideal R`. The lemma `Ideal.spanNorm_eq` says that the two definitions agree.

| Lean name | Statement |
| --- | --- |
| `Ideal.relNorm_singleton` | $N_{S/R}((r)) = (\mathrm{N}_{S/R}(r))$ |
| `Ideal.relNorm_algebraMap` | $N_{S/R}(I S) = I^{[S:R]}$ for an ideal $I$ of $R$ |
| `Ideal.relNorm_relNorm` | $N_{T/R} \circ N_{S/T} = N_{S/R}$ for a tower $R \subseteq T \subseteq S$ |
| `Ideal.relNorm_int` | $N_{S/\mathbb{Z}}(I) = (N(I))$ |
| `Ideal.absNorm_relNorm` | $N(N_{S/R}(I)) = N(I)$ |
| `Ideal.relNorm_eq_pow_of_isMaximal` | $N_{S/R}(P) = p^{f}$, with $f$ the inertia degree of $P$ over $p$ |
| `Ideal.relNorm_le_comap` | $N_{S/R}(I) \subseteq I \cap R$ |

The idea of `Ideal.relNorm_algebraMap`: the extension $I S$ is generated by the elements of $I$, and the norm of an element $a$ of $R$ is $a^{[S:R]}$. The multiplicativity then gives the power of $I$. In the lemma, the exponent is `Module.finrank R S`. The lemma `Ideal.exists_relNorm_eq_pow_of_isPrime` says that the norm of a prime over $p$ is a power of $p$ in general, and `Ideal.relNorm_eq_pow_of_isPrime_isGalois` treats a Galois extension.

#### The ideals of the integers

The module `Mathlib.RingTheory.Ideal.Int` computes with $\mathbb{Z}$. The lemma `Int.card_ideal_quot` says that $|\mathbb{Z}/(n)| = n$ for each natural number $n$. For $n > 0$ the classes of $0, 1, \dots, n - 1$ are the distinct elements. For $n = 0$ both sides are $0$, because $\mathbb{Z}$ is infinite and `Nat.card` is $0$. The lemma `Int.ringChar_idealQuot` gives the characteristic of $\mathbb{Z}/(n)$ as $n$, and `Int.ideal_span_isMaximal_of_prime` is the instance that $(p)$ is maximal for a prime $p$.

For an ideal $I$ of any ring $R$, the contraction `Ideal.under ℤ I` is an ideal of $\mathbb{Z}$, and its norm is the least positive integer in $I$, or $0$ if there is none. This is `Int.absNorm_under_eq_sInf`. The lemma `Int.cast_mem_ideal_iff` says that an integer $d$ is in $I$ exactly when this norm divides $d$. Proof: the ideal `Ideal.under ℤ I` is principal, generated by its norm, by `Int.ideal_span_absNorm_eq_self`, and $d \in I$ means $d \in$ `Ideal.under ℤ I`. The lemma `Ideal.ringChar_quot` says that the characteristic of $S/I$ is the same number. The lemma `Nat.absNorm_under_prime` says that the number is prime when $P$ is a nonzero prime of a domain that is integral over $\mathbb{Z}$. The lemma `Int.absNorm_under_dvd_absNorm` says that it divides $N(I)$ in a Dedekind domain.

#### Common errors

1. A learner forgets that `Submodule.cardQuot` and `Ideal.absNorm` use `Nat.card`, which is $0$ on an infinite type. The value $0$ does not mean that the quotient is empty. It means that the quotient is infinite, or that the ideal is $0$ in a ring with finite quotients. A lemma such as `Ideal.absNorm_eq_zero_iff` needs the instance `Ring.HasFiniteQuotients S`.
2. A learner applies `map_mul` to `Ideal.absNorm` in a ring that is not a Dedekind domain. The definition needs `IsDedekindDomain S`. In a general commutative ring the only product formula is `cardQuot_mul_of_coprime`, with a coprimality hypothesis.
3. A learner confuses the norm of an element with the norm of an ideal. `Algebra.norm ℤ r` is an integer and can be negative, while `Ideal.absNorm (Ideal.span {r})` is a natural number. The link is `Ideal.absNorm_span_singleton`, which takes the absolute value of the element norm.

### Exercises

1. (A) Use `Int.card_ideal_quot` and `cardQuot_mul_of_coprime` to compute $|\mathbb{Z}/(12)|$ from the coprime factors $(4)$ and $(3)$.
2. (A) Show from `Ideal.absNorm_mem` that a proper nonzero ideal of a ring of integers contains a positive integer.
3. (B) Prove that a finite commutative ring has `Ring.DimensionLEOne` directly: show that each prime ideal is maximal, with the argument of `Ring.HasFiniteQuotients.maximalOfPrime`.
4. (B) In $\mathbb{Z}[i]$, compute $N((2 + i))$ with `Ideal.absNorm_span_singleton`, and deduce from `Ideal.isPrime_of_irreducible_absNorm` that $(2 + i)$ is a prime ideal.
5. (B) Prove `Int.cast_mem_ideal_iff` for $R = \mathbb{Z}/(12)$ and the ideal generated by the class of $8$: find the least positive integer in it.
6. (C) Prove the bound of `Ideal.index_pow_le` for $n = 2$: if $I$ is spanned by a finset $s$, show that $[R : I^2] \le [R : I]^{1 + |s|}$.

### Reference

<?reference?>
