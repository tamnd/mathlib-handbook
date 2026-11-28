---
title: Quotient rings in the library
kind: api
modules:
  - Mathlib.RingTheory.Ideal.Quotient.Defs
  - Mathlib.RingTheory.Ideal.Quotient.Basic
  - Mathlib.RingTheory.Ideal.Quotient.Operations
  - Mathlib.RingTheory.Ideal.Quotient.Nilpotent
  - Mathlib.RingTheory.Ideal.Quotient.PowTransition
  - Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
  - Mathlib.RingTheory.Ideal.IsAugmentation
  - Mathlib.RingTheory.Ideal.Cotangent
  - Mathlib.RingTheory.Ideal.CotangentBaseChange
explains:
  E2: [Ideal.Quotient.lift, Ideal.Quotient.eq, Ideal.Quotient.maximal_ideal_iff_isField_quotient, Ideal.Quotient.isDomain_iff_prime, RingHom.quotientKerEquivOfSurjective, DoubleQuot.quotQuotEquivQuotOfLE, IsNilpotent.isUnit_quotient_mk_iff, Ideal.quotEquivPowQuotPowSucc, Ideal.toCotangent_eq_zero]
  E1: auto
families: []
requires: [V06.C02, V06.C03, V07.C01, V07.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Quotient rings in the library

### Overview

Volume 6 built the quotient ring $R/I$ and proved the isomorphism theorems. This chapter uses quotients in almost every proof: the Chinese remainder theorem is an isomorphism of quotients, a prime ideal is an ideal with a domain as quotient, and the radical of $I$ is the preimage of the nilradical of $R/I$. This section describes the files of the library that hold the quotient ring, its universal property, the isomorphism theorems in the form that Mathlib uses, and some quotients built from powers of an ideal.

The last part of the section treats the cotangent module $I/I^2$. It is a module over $R/I$, and for the maximal ideal $\mathfrak{m}$ of a local ring it gives the cotangent space $\mathfrak{m}/\mathfrak{m}^2$, a vector space over the residue field. Its dimension is the least number of generators of $\mathfrak{m}$ when $R$ is Noetherian, a fact that links this section to Nakayama's lemma in Chapter 4.

### The library around it

#### The quotient ring and its universal property

The module `Mathlib.RingTheory.Ideal.Quotient.Defs` defines the ring `R ⧸ I` through the instance `Ideal.instHasQuotient`, with the ring structures `Ideal.Quotient.ring` and `Ideal.Quotient.commRing`. The quotient map is the ring homomorphism `Ideal.Quotient.mk I : R →+* R ⧸ I`, and `Ideal.Quotient.mk_surjective` says that it is onto. For a noncommutative ring the ideal must be two-sided, so many statements carry the hypothesis `[I.IsTwoSided]`. In a commutative ring an instance supplies it.

**Theorem.** `Ideal.Quotient.eq`: $\bar x = \bar y$ in $R/I$ if and only if $x - y \in I$. `Ideal.Quotient.lift`: a ring homomorphism $f : R \to S$ with $f(I) = 0$ factors as $f = \bar f \circ \pi$ through a unique $\bar f : R/I \to S$.

*Proof.* The quotient is the quotient of the additive group by the subgroup $I$, so the first statement is the definition of the cosets. For the second, put $\bar f(\bar x) = f(x)$. If $\bar x = \bar y$, then $x - y \in I$ and $f(x) - f(y) = f(x - y) = 0$, so $\bar f$ is well defined. It is a ring homomorphism since $f$ and $\pi$ are. It is unique because $\pi$ is onto. $\square$

The computation rule is `Ideal.Quotient.lift_mk`, and the uniqueness is `Ideal.Quotient.ringHom_ext`: two maps out of `R ⧸ I` agree when they agree after `Ideal.Quotient.mk I`. A proof that two such maps are equal usually starts with `Ideal.Quotient.ringHom_ext`. When $I \le J$, the map `Ideal.Quotient.factor` sends $R/I$ onto $R/J$, with `Ideal.Quotient.factor_mk`. An equality of ideals $I = J$ gives the isomorphism `Ideal.quotEquivOfEq`. This avoids a rewrite inside the type `R ⧸ I`, which often fails.

The module `Mathlib.RingTheory.Ideal.Quotient.Basic` gives the facts that link the quotient and the ideal.

**Theorem.** `Ideal.Quotient.isDomain_iff_prime`: $R/I$ is a domain if and only if $I$ is prime. `Ideal.Quotient.maximal_ideal_iff_isField_quotient`: for a commutative ring, $R/I$ is a field if and only if $I$ is maximal.

*Proof.* In $R/I$, $\bar x \bar y = 0$ means $x y \in I$, and $\bar x = 0$ means $x \in I$. The ring $R/I$ is nonzero if and only if $1 \notin I$. These translate the definition of a domain into the definition of a prime. For the second statement, let $I$ be maximal and $x \notin I$. Then $I + (x) = R$, so $1 = i + a x$ with $i \in I$, and $\bar a \bar x = 1$. Conversely, if $R/I$ is a field and $J > I$, pick $x \in J \setminus I$. Then $\bar x$ is a unit, so $1 - a x \in I \subseteq J$ for some $a$, and $1 \in J$. $\square$

The instances `Ideal.Quotient.isDomain` and the definition `Ideal.Quotient.field` give the structures. The field is a definition, not an instance, since the class `Ideal.IsMaximal` is not always available. Other lemmas of the module are `Ideal.Quotient.zero_eq_one_iff` and `Ideal.Quotient.subsingleton_iff`, both for $I = R$, `Ideal.Quotient.exists_inv` for the inverses in $R/I$ when $I$ is maximal, and `finite_iff_ideal_quotient`: $R$ is finite if and only if $I$ and $R/I$ are finite. For the module $R^\iota$, `Ideal.piQuotEquiv` identifies $R^\iota / I^\iota$ with $(R/I)^\iota$.

#### The isomorphism theorems

The module `Mathlib.RingTheory.Ideal.Quotient.Operations` holds the isomorphism theorems and the algebra structures. Its names have a pattern: a name in `RingHom` or `Ideal` gives a ring isomorphism, and a name with the subscript ₐ or with the word Alg gives the $R$-algebra form.

| Lean name | Statement |
|---|---|
| `RingHom.kerLift` | $R/\ker f \to S$ induced by $f$ |
| `RingHom.kerLift_injective` | this map is injective |
| `RingHom.quotientKerEquivRange` | $R/\ker f \cong f(R)$ |
| `RingHom.quotientKerEquivOfSurjective` | $R/\ker f \cong S$ for a surjective $f$ |
| `Ideal.quotientKerAlgEquivOfSurjective` | the same for an algebra map |
| `RingEquiv.quotientBot` | $R/0 \cong R$ |
| `DoubleQuot.quotQuotEquivQuotSup` | $(R/I)/\bar J \cong R/(I + J)$ |
| `DoubleQuot.quotQuotEquivQuotOfLE` | $(R/I)/(J/I) \cong R/J$ when $I \le J$ |
| `DoubleQuot.quotQuotEquivComm` | $(R/I)/\bar J \cong (R/J)/\bar I$ |
| `Ideal.quotientMap` | $R/I \to S/J$ induced by $f$ with $I \le f^{-1}(J)$ |
| `Ideal.quotientEquiv` | $R/I \cong S/J$ induced by an isomorphism $f$ with $J = f(I)$ |
| `Ideal.quotientInfEquivQuotientProd` | $R/(I \cap J) \cong R/I \times R/J$ for coprime $I, J$ |
| `Ideal.quotientMulEquivQuotientProd` | $R/IJ \cong R/I \times R/J$ for coprime $I, J$ |

Here $\bar J$ is the image `Ideal.map (Ideal.Quotient.mk I) J`. The ideals of $R/I$ correspond to the ideals of $R$ that contain $I$: `Ideal.comap_map_mk` gives $\pi^{-1}(\pi(J)) = J$ for $J \ge I$, and `Ideal.mem_quotient_iff_mem_sup` gives $\bar x \in \bar J$ if and only if $x \in J + I$. The lemma `Ideal.isPrime_map_quotientMk_of_isPrime` says that a prime above $I$ maps to a prime, and `Ideal.bot_quotient_isMaximal_iff` says that $0$ is maximal in $R/I$ if and only if $I$ is maximal.

**Theorem.** `RingHom.quotientKerEquivOfSurjective`: a surjective ring homomorphism $f : R \to S$ gives $R/\ker f \cong S$. `DoubleQuot.quotQuotEquivQuotOfLE`: for $I \le J$, $(R/I)/(J/I) \cong R/J$.

*Proof.* The map $\bar f$ of `Ideal.Quotient.lift` is onto since $f$ is, and $\bar f(\bar x) = 0$ means $x \in \ker f$, so $\bar f$ is injective. For the second statement, apply the first to the factor map $R/I \to R/J$. It is onto, and its kernel is $J/I$, which is the image of $J$ (`Ideal.Quotient.factor_ker`). $\square$

The algebra structure on `A ⧸ I` is the instance `Ideal.Quotient.algebra`, and `Ideal.Quotient.algebraMap_eq` says that the algebra map of `R ⧸ I` over $R$ is `Ideal.Quotient.mk I`. The quotient map as an algebra map is `Ideal.Quotient.mkₐ`, and the lift is `Ideal.Quotient.liftₐ`. The Chinese remainder maps `Ideal.quotientInfToPiQuotient` and `Ideal.quotientInfRingEquivPiQuotient` also live in this module, with their proofs in Section 3.

#### Units and nilpotents in quotients

The module `Mathlib.RingTheory.Ideal.Quotient.Nilpotent` studies units modulo a nilpotent ideal.

**Theorem.** `IsNilpotent.isUnit_quotient_mk_iff`: let $I$ be a nilpotent ideal. Then $x$ is a unit of $R$ if and only if $\bar x$ is a unit of $R/I$.

*Proof.* One direction is clear. Let $x y = 1 - n$ with $n \in I$. Then $n$ is nilpotent, so $1 - n$ is a unit, with inverse $1 + n + n^2 + \dots + n^{k-1}$ when $n^k = 0$. So $x$ divides a unit, and $x$ is a unit. $\square$

The lemma `Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk` gives the same for $R/I^n \to R/I$ with $n \ne 0$, and `Ideal.Quotient.isUnit_mk_pow_iff_notMem` says that, for a maximal ideal $\mathfrak{m}$, $x$ is a unit modulo $\mathfrak{m}^n$ if and only if $x \notin \mathfrak{m}$. So $R/\mathfrak{m}^n$ is a local ring. The principle `Ideal.IsNilpotent.induction_on` proves a statement for nilpotent ideals from the case $I^2 = 0$. The lemma `Ideal.isRadical_iff_quotient_reduced` says that $I$ equals its radical if and only if $R/I$ is reduced.

#### Quotients by powers

For $n \le m$ the inclusion $I^m \le I^n$ gives the factor map `Ideal.Quotient.factorPow` from $R/I^m$ to $R/I^n$, and `Ideal.Quotient.factorPowSucc` is the step $R/I^{n+1} \to R/I^n$. The module `Mathlib.RingTheory.Ideal.Quotient.PowTransition` defines these maps, with the module forms `Submodule.factorPow` for $M/I^n M$. The inclusion `Submodule.powSMulQuotInclusion` embeds $I^a N / I^{a+b} N$ in $M / I^{a+b} N$, and `Submodule.powSMulQuotInclusion_injective` says that it is injective. These maps form the inverse system whose limit is the $I$-adic completion.

The module `Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient` treats a principal ideal $I = (\pi) \ne 0$ in a domain.

**Theorem.** `Ideal.quotEquivPowQuotPowSucc`: for each $n$, multiplication by $\pi^n$ gives an isomorphism of $R$-modules $R/I \cong I^n/I^{n+1}$.

*Proof.* The map $x \mapsto x \pi^n$ sends $R$ onto $I^n = (\pi^n)$. Its composite with $I^n \to I^n/I^{n+1}$ is onto and kills $I$. If $x \pi^n \in (\pi^{n+1})$, then $x \pi^n = y \pi^{n+1}$, and cancellation in the domain gives $x = y \pi \in I$. $\square$

The module `Mathlib.RingTheory.Ideal.Quotient.Operations` has the general map `Ideal.powQuotPowSuccEquivMapMkPowSuccPow`, which identifies $I^n / I^{n+1}$ with the image of $I^n$ in $R/I^{n+1}$. In a discrete valuation ring each $I^n/I^{n+1}$ is a copy of the residue field, so the length of $R/I^n$ is $n$.

#### Augmentation ideals

The module `Mathlib.RingTheory.Ideal.IsAugmentation` defines `Ideal.IsAugmentation R I` for an ideal $I$ of an $R$-algebra $A$. By `Ideal.isAugmentation_iff`, it holds when $A = R \cdot 1 \oplus I$ as $R$-modules, so that $A/I \cong R$. The ideal of the polynomials without constant term is an example in $R[X]$. The lemma `Ideal.isAugmentation_subalgebra_iff` gives the form for a subalgebra $S$ in place of $R$.

#### The cotangent module

For an ideal $I$ of $R$, `Ideal.Cotangent I` is the $R$-module $I/I^2$, with the quotient map `Ideal.toCotangent I`. The module `Mathlib.RingTheory.Ideal.Cotangent` defines it and its structure.

**Theorem.** `Ideal.toCotangent_eq_zero`: for $x \in I$, the class of $x$ in $I/I^2$ is zero if and only if $x \in I^2$. `Ideal.isTorsionBySet_cotangent`: $I$ kills $I/I^2$, so $I/I^2$ is a module over $R/I$.

*Proof.* The first statement is the definition of the quotient of $I$ by the submodule $I^2$. For the second, let $a \in I$ and $x \in I$. Then $a x \in I^2$, so $a$ kills the class of $x$. $\square$

The instance `Ideal.instModuleQuotientCotangent` gives the $R/I$-module structure. The isomorphism `Ideal.cotangentEquivIdeal` identifies $I/I^2$ with the ideal $I/I^2$ of $R/I^2$, named `Ideal.cotangentIdeal`, and `Ideal.quotCotangent` gives $(R/I^2)/(I/I^2) \cong R/I$. A map of algebras $f$ with $f(I_1) \le I_2$ induces `Ideal.mapCotangent`, and a linear map on $I$ that kills the products $x y$ factors through `Ideal.Cotangent.lift`. The lemma `Ideal.cotangent_subsingleton_iff` says that $I/I^2 = 0$ if and only if $I = I^2$.

For a local ring $R$ with maximal ideal $\mathfrak{m}$ and residue field $k$, `IsLocalRing.CotangentSpace R` is the $k$-vector space $\mathfrak{m}/\mathfrak{m}^2$. When $R$ is Noetherian, `IsLocalRing.rank_cotangentSpace_eq_spanrank_maximalIdeal` says that its dimension is the least number of generators of $\mathfrak{m}$, and `IsLocalRing.finrank_cotangentSpace_le_one_iff` says that the dimension is at most $1$ if and only if $\mathfrak{m}$ is principal. The proofs use Nakayama's lemma: `IsLocalRing.CotangentSpace.span_image_eq_top_iff` says that elements of $\mathfrak{m}$ generate $\mathfrak{m}$ if and only if their classes span $\mathfrak{m}/\mathfrak{m}^2$. These facts lead to the definition of a regular local ring.

The module `Mathlib.RingTheory.Ideal.CotangentBaseChange` treats a flat base change $R \to T$. The map `Ideal.tensorCotangentHom` goes from $T \otimes_R I/I^2$ to the cotangent module of the extended ideal of $T \otimes_R S$. It is onto (`Ideal.tensorCotangentHom_surjective`), and it is injective when $T$ is flat (`Ideal.tensorCotangentHom_injective_of_flat`). The isomorphism is `Ideal.tensorCotangentEquiv`.

#### Common errors

1. A rewrite with `h : I = J` inside the type `R ⧸ I` often fails with a motive error. Use the isomorphism `Ideal.quotEquivOfEq h` or `Ideal.quotientEquiv` instead.
2. `Ideal.Quotient.field I` is a definition. To use the field structure, install it with `letI := Ideal.Quotient.field I`, and give the instance `[I.IsMaximal]` first.
3. `RingHom.quotientKerEquivOfSurjective` and `Ideal.quotientKerAlgEquivOfSurjective` have different types: the first is a ring isomorphism and the second is an algebra isomorphism. A goal about algebra maps needs the second.

### Exercises

1. (A) Use `RingHom.quotientKerEquivOfSurjective` and the map $\mathbb{Z}[X] \to \mathbb{Z}$, $X \mapsto 0$, to prove that $\mathbb{Z}[X]/(X) \cong \mathbb{Z}$.
2. (A) Prove that $(\mathbb{Z}/12)/(\bar 4) \cong \mathbb{Z}/4$ with `DoubleQuot.quotQuotEquivQuotOfLE`.
3. (B) Prove that $R/\mathfrak{m}^n$ is a local ring for a maximal ideal $\mathfrak{m}$, with `Ideal.Quotient.isUnit_mk_pow_iff_notMem`.
4. (B) Let $R = k[x, y]_{(x, y)}$. Compute the cotangent space $\mathfrak{m}/\mathfrak{m}^2$ and its dimension over $k$.
5. (B) Show that the ideal $(X)$ of $R[X]$ is an augmentation ideal in the sense of `Ideal.IsAugmentation`.
6. (C) Let $I = (p)$ in $\mathbb{Z}$. Use `Ideal.quotEquivPowQuotPowSucc` to prove that $\mathbb{Z}/p^n$ has a chain of ideals with each quotient of order $p$, and deduce that it has $p^n$ elements.

### Reference

<?reference?>
