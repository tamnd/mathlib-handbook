---
title: Completions at primes, finite adeles and S-integers
kind: api
modules:
  - Mathlib.RingTheory.DedekindDomain.AdicValuation
  - Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
  - Mathlib.RingTheory.DedekindDomain.AdicValuation.Ramification
  - Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
  - Mathlib.RingTheory.DedekindDomain.SInteger
  - Mathlib.RingTheory.DedekindDomain.SelmerGroup
  - Mathlib.RingTheory.DedekindDomain.GaussLemma
explains:
  E2: [IsDedekindDomain.HeightOneSpectrum.adicCompletion, IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers, IsDedekindDomain.HeightOneSpectrum.valuation_liesOver, IsDedekindDomain.FiniteAdeleRing, IsDedekindDomain.FiniteAdeleRing.isUnit_iff, IsDedekindDomain.HeightOneSpectrum.Support.finite, Set.integer, Set.unitEquivUnitsInteger, IsDedekindDomain.selmerGroup, Polynomial.contentIdeal_eq_top_iff_forall_gaussNorm_eq_one]
  E1: auto
families: []
requires: [V10.C03, V14]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Completions at primes, finite adeles and S-integers

### Overview

Let $R$ be a Dedekind domain with fraction field $K$. Section 3 attaches to each nonzero prime $v$ of $R$ the $v$-adic valuation of $K$. This section collects the constructions that the library builds on these valuations. The first is the completion $K_v$ of $K$ for the $v$-adic valuation, with its valuation ring $\mathcal{O}_v$. For $R = \mathbb{Z}$ and $v = (p)$, these are $\mathbb{Q}_p$ and $\mathbb{Z}_p$. The second is the ring of finite adeles, the restricted product of all the $K_v$. The third is a family of subrings and subgroups of $K$ that are cut out by conditions at all primes outside a set $S$: the $S$-integers, the $S$-units and the Selmer group $K(S, n)$. The section ends with a form of Gauss's lemma that uses the valuations at all primes.

These objects are the basic language of algebraic number theory and of the arithmetic of function fields. Volume 12 uses them for number fields. The topology of a valued field and of its completion is in Volume 14; this section uses only the facts that a completion is complete and that $K$ is dense in it.

### The library around it

#### The type of primes and its valuations

The primes are the terms of `IsDedekindDomain.HeightOneSpectrum R`, the nonzero prime ideals of $R$. A term `v` has the ideal `v.asIdeal`. In this section the prefix `IsDedekindDomain.HeightOneSpectrum` is long, so the text writes the short names of the namespace when the meaning is clear; the index has the full names. Section 3 defines `IsDedekindDomain.HeightOneSpectrum.intValuation` on $R$ and `IsDedekindDomain.HeightOneSpectrum.valuation` on $K$. Both take values in $\mathbb{Z}_{m0}$, the multiplicative group $\mathbb{Z}$ with a zero adjoined. The convention is multiplicative: $v(x) = \exp(-\mathrm{ord}_v(x))$, so $v(x) \le 1$ means that $x$ is integral at $v$, and $v(x) < 1$ means that $v$ divides $x$.

The module `Mathlib.RingTheory.DedekindDomain.AdicValuation` has no declarations. It imports the definition of the valuation and the completion, so a file that imports it gets both.

#### The completion at a prime

The completion `IsDedekindDomain.HeightOneSpectrum.adicCompletion K v` is the field $K_v$. It is a structure that wraps the completion `(IsDedekindDomain.HeightOneSpectrum.valuation K v).Completion` of the type copy `WithVal` of $K$. The wrapper keeps the two types apart: a term of $K_v$ is built with the constructor `IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion` and unwrapped with `IsDedekindDomain.HeightOneSpectrum.adicCompletion.toCompletion`. The ring equivalence `IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv` and the uniform equivalence `IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformEquiv` give the same identification with more structure. A coercion sends $K$ into $K_v$.

The instances make $K_v$ a field, a uniform space, a complete space (`IsDedekindDomain.HeightOneSpectrum.adicCompletion.instCompleteSpace`) and a valued field with values in $\mathbb{Z}_{m0}$. For each algebra $S \to K$, the instance `IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion` makes $K_v$ an $S$-algebra, so $K_v$ is an $R$-algebra and a $K$-algebra. The valuation of $K_v$ extends the valuation of $K$:

| Lean name | Statement |
|---|---|
| `IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe` | for $k \in K$, the valuation of $k$ in $K_v$ is $v(k)$ |
| `IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation` | the same for $r \in R$ |
| `IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective` | the valuation of $K_v$ takes every value of $\mathbb{Z}_{m0}$ |
| `IsDedekindDomain.HeightOneSpectrum.adicCompletion_valueGroup_eq` | $K_v$ and $K$ have the same value group |
| `IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap` | $K$ is dense in $K_v$ |
| `IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext_iff` | two terms are equal if and only if their unwrapped completions are equal |

The valuation ring is `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v`, a `ValuationSubring` of $K_v$. Its membership lemma `IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers` says $x \in \mathcal{O}_v \iff v(x) \le 1$, and `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one` says that the units of $\mathcal{O}_v$ are the elements of valuation $1$. The image of $R$ lies in $\mathcal{O}_v$, `IsDedekindDomain.HeightOneSpectrum.coe_mem_adicCompletionIntegers`, and $\mathcal{O}_v$ is an $R$-algebra. The lemma `IsDedekindDomain.HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers` says that each $a \in K_v$ becomes integral after multiplication by a nonzero element of $R$: take $b \in v^k$ for $k$ large.

The definitions for the value groups, such as `IsDedekindDomain.HeightOneSpectrum.adicCompletion.valueGroupOrderMonoidIso`, compare the value group of $K_v$ with the value group of the extended valuation of the completion. A user needs them only to move a result between the two descriptions of $K_v$.

#### Valuations in an extension

Let $A \subseteq B$ be an extension of Dedekind domains with fraction fields $K \subseteq L$. Let $w$ be a prime of $B$ over the prime $v$ of $A$, with ramification index $e = e(w \mid v)$. The module `Mathlib.RingTheory.DedekindDomain.AdicValuation.Ramification` proves the relation between the two valuations.

**Proposition.** For $x \in K$, $w(x) = v(x)^e$.

*Proof.* Both sides are multiplicative, so it suffices to take $x \in A$ nonzero. Write $xA = v^a \mathfrak{a}$ with $v \nmid \mathfrak{a}$. Then $xB = (vB)^a \mathfrak{a}B$. The ideal $vB$ is $w^e$ times a product of primes different from $w$, and $\mathfrak{a}B$ is prime to $w$, because a prime of $B$ over a prime of $A$ different from $v$ is different from $w$. So the exponent of $w$ in $xB$ is $ae$. $\square$

The Lean form is `IsDedekindDomain.HeightOneSpectrum.valuation_liesOver`, with the version `IsDedekindDomain.HeightOneSpectrum.intValuation_liesOver` on $A$. The hypothesis is the instance `[w.asIdeal.LiesOver v.asIdeal]`, and the index is `Ideal.ramificationIdx`. The consequence `IsDedekindDomain.HeightOneSpectrum.uniformContinuous_algebraMap_liesOver` says that $K \to L$ is uniformly continuous for the $v$-adic and the $w$-adic structures, so it extends to the completions.

#### The finite adele ring

An element $k \in K$ is integral at almost every prime. The set of primes where it is not integral is `IsDedekindDomain.HeightOneSpectrum.Support R k`, the set $\{v \mid v(k) > 1\}$, and `IsDedekindDomain.HeightOneSpectrum.Support.finite` says that it is finite. Proof: write $k = a/b$ with $a, b \in R$ and $b \neq 0$. If $v(k) > 1$, then $v$ divides $b$. The ideal $bR$ has finitely many prime factors.

This fact makes the diagonal map $K \to \prod_v K_v$ land in the restricted product
$$\mathbb{A}_{K,f} = \Big\{ (x_v) \in \prod_v K_v \ \Big|\ x_v \in \mathcal{O}_v \text{ for all but finitely many } v \Big\}.$$
This is `IsDedekindDomain.FiniteAdeleRing R K`, with the notation `𝔸ᶠ[R, K]`. It is defined as the restricted product `Πʳ v, [v.adicCompletion K, v.adicCompletionIntegers K]` of Volume 14, and it inherits the commutative ring structure and the restricted product topology. The instances make it a topological ring, a $K$-algebra and an $R$-algebra. A finite adele is a function on primes, through a `DFunLike` instance, so `a v` is its component at `v`; `IsDedekindDomain.FiniteAdeleRing.ext` is the extensionality lemma.

| Lean name | Statement |
|---|---|
| `IsDedekindDomain.FiniteAdeleRing.algebraMap_apply` | the component of $k \in K$ at $v$ is the image of $k$ in $K_v$ |
| `IsDedekindDomain.FiniteAdeleRing.cofinite_mem_adicCompletionIntegers` | each finite adele is integral at all but finitely many $v$ |
| `IsDedekindDomain.FiniteAdeleRing.finite_valued_one_lt` | the set $\{v \mid v(a_v) > 1\}$ is finite |
| `IsDedekindDomain.FiniteAdeleRing.isUnit_iff` | $a$ is a unit if and only if each $a_v \neq 0$ and $v(a_v) = 1$ for almost all $v$ |
| `IsDedekindDomain.FiniteAdeleRing.infinite_valued_ne_one_of_not_isUnit` | a nonunit with nonzero components has $v(a_v) \neq 1$ at infinitely many $v$ |
| `IsDedekindDomain.FiniteAdeleRing.ofAdicCompletion` | the monoid map $K_v \to \mathbb{A}_{K,f}$ that puts $x$ at $v$ and $1$ elsewhere |
| `IsDedekindDomain.FiniteAdeleRing.unitEmbedding` | the map $K^\times \to \mathbb{A}_{K,f}^\times$ |

The proof of `IsDedekindDomain.FiniteAdeleRing.isUnit_iff` is short. If $ab = 1$, then each $a_v \neq 0$, and for almost all $v$ both $a_v$ and $b_v$ lie in $\mathcal{O}_v$, so $v(a_v) \le 1$, $v(b_v) \le 1$ and $v(a_v)v(b_v) = 1$, which forces $v(a_v) = 1$. Conversely, the componentwise inverse $(a_v^{-1})$ is integral wherever $v(a_v) = 1$, so it is a finite adele. If $R$ is a field, there are no primes, and the restricted product over the empty set is the zero ring. Only the case of dimension one is of interest.

#### S-integers and S-units

Let $S$ be a set of primes of $R$. An $S$-integer is an $x \in K$ with $v(x) \le 1$ for every $v \notin S$, and an $S$-unit is an $x \in K^\times$ with $v(x) = 1$ for every $v \notin S$. The definitions are in the namespace `Set`, so that dot notation works on `S`:

1. `Set.integer` gives `S.integer K`, a subalgebra of $K$ over $R$. By `Set.integer_eq`, its underlying subring is the intersection of the valuation subrings of the $v \notin S$.
2. `Set.unit` gives `S.unit K`, a subgroup of $K^\times$, with `Set.unit_eq` the same description by unit groups.
3. `Set.unitEquivUnitsInteger` is the group isomorphism between the $S$-units and the units of the ring of $S$-integers.
4. `IsDedekindDomain.integer_empty` says that the $\emptyset$-integers are the image of $R$. This is the statement $R = \bigcap_v R_v$ for a Dedekind domain. `IsDedekindDomain.integer_univ` says that the $S$-integers for all primes form $K$.

When every class of the class group of Chapter 5 has finite order, the ring of $S$-integers is a localization of $R$. The submonoid is `Localization.submonoid S`, the nonzero elements of $R$ that lie in no prime outside $S$. The instance `IsDedekindDomain.isLocalizationSInteger` gives the localization, and `IsDedekindDomain.isDedekindDomainSInteger` shows that the $S$-integers form a Dedekind domain. Both need the hypothesis `[Fact (IsMulTorsion (ClassGroup R))]`, and an instance supplies it when the class group is finite. The idea of the proof: let $x$ be an $S$-integer. Its denominator ideal $\mathfrak{b}$ is a product of primes in $S$. Some power $\mathfrak{b}^h$ is principal, say $\mathfrak{b}^h = (s)$, and $s$ lies in no prime outside $S$. Then $x = a/s^m$ for some $a \in R$ and some $m$. This is `IsDedekindDomain.exists_mul_algebraMap_eq_algebraMap`.

#### The Selmer group

For $n \ge 1$, the Selmer group is
$$K(S, n) = \{ x(K^\times)^n \in K^\times/(K^\times)^n \mid \mathrm{ord}_v(x) \equiv 0 \pmod n \text{ for all } v \notin S \}.$$
The quotient $K^\times/(K^\times)^n$ is `Units.ModPow K n`, and `IsDedekindDomain.selmerGroup` is the subgroup, with notation `K⟮S, n⟯`. The condition uses `IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero`, the valuation as a homomorphism $K^\times \to \mathrm{Multiplicative}\ \mathbb{Z}$, and its reduction `IsDedekindDomain.HeightOneSpectrum.valuationOfNeZeroMod` modulo $n$.

The results are the first steps of the exact sequence $1 \to R^\times/(R^\times)^n \to K(\emptyset, n) \to \mathrm{Cl}(R)[n]$. The map `IsDedekindDomain.selmerGroup.fromUnit` sends a unit of $R$ to its class, `IsDedekindDomain.selmerGroup.fromUnit_ker` says that its kernel is the group of $n$-th powers, and `IsDedekindDomain.selmerGroup.fromUnitLift_injective` gives the injective map from $R^\times/(R^\times)^n$. The map `IsDedekindDomain.selmerGroup.valuation` records the valuations modulo $n$ at the primes of $S$, and `IsDedekindDomain.selmerGroup.valuation_ker_eq` says that its kernel is $K(\emptyset, n)$ inside $K(S, n)$. The docstring lists the map to the class group and the exactness of the full sequence as work to do, and the index of this edition has no declaration for them. `IsDedekindDomain.selmerGroup.monotone` says that $K(S, n)$ grows with $S$.

#### Gauss's lemma

The module `Mathlib.RingTheory.DedekindDomain.GaussLemma` states Gauss's lemma with absolute values. For $b > 1$, `IsDedekindDomain.HeightOneSpectrum.intAdicAbv` turns the valuation of $R$ at $v$ into a real absolute value with $|r|_v = b^{-\mathrm{ord}_v(r)}$. The Gauss norm `Polynomial.gaussNorm` of a polynomial $p = \sum a_iX^i$ at $c = 1$ is $\max_i |a_i|_v$. The content ideal `Polynomial.contentIdeal` is the ideal generated by the coefficients.

**Theorem.** If $R$ is not a field, the content ideal of $p \in R[X]$ is $R$ if and only if $\max_i |a_i|_v = 1$ for every prime $v$.

*Proof.* Each $|a_i|_v \le 1$, so the Gauss norm is at most $1$, which is `Polynomial.gaussNorm_intAdicAbv_le_one`. It is less than $1$ exactly when $v$ divides every coefficient, that is, when the content ideal is contained in $v$; this is `Polynomial.gaussNorm_lt_one_iff_contentIdeal_le`. An ideal is $R$ if and only if no maximal ideal contains it. In a Dedekind domain that is not a field, the maximal ideals are the nonzero primes, and the content ideal is not zero when it is all of $R$. $\square$

The Lean form is `Polynomial.contentIdeal_eq_top_iff_forall_gaussNorm_eq_one`. For a principal ideal domain, `Polynomial.isPrimitive_iff_forall_gaussNorm_eq_one` replaces the content ideal by the condition `Polynomial.IsPrimitive`. Since the Gauss norm is multiplicative, the theorem gives the classical lemma: the product of two polynomials with content $R$ has content $R$.

#### Common errors

1. `IsDedekindDomain.HeightOneSpectrum.adicCompletion K v` is a structure, not the completion itself. A lemma about `UniformSpace.Completion` does not apply to it at once. Move the terms with `IsDedekindDomain.HeightOneSpectrum.adicCompletion.toCompletion` and `IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion`, or with `IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv`.
2. The valuations are multiplicative with values in $\mathbb{Z}_{m0}$. The condition "$x$ is divisible by $v$" is `v.valuation K x < 1`, not an inequality of orders. The order itself comes from `IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero`, which is defined only on $K^\times$.
3. `Set.integer` and `Set.unit` take the set of excluded primes $S$, and the condition is at the primes outside $S$. With $S = \emptyset$ the result is $R$, not $K$.

### Exercises

1. (A) Show that $\{v \mid v(k) \neq 1\}$ is finite for $k \in K^\times$, with `IsDedekindDomain.HeightOneSpectrum.Support.finite` applied to $k$ and $k^{-1}$.
2. (A) Show that the image of $K^\times$ under `IsDedekindDomain.FiniteAdeleRing.unitEmbedding` meets $\prod_v \mathcal{O}_v^\times$ exactly in the image of $R^\times$.
3. (B) For $R = \mathbb{Z}$ and $S = \{(2), (3)\}$, describe the $S$-integers and the $S$-units of $\mathbb{Q}$.
4. (B) Prove that $\mathbb{Q}(\emptyset, 2)$ is $\{\pm 1\}$ modulo squares, and that $\mathbb{Q}(\{(2)\}, 2)$ has order $4$.
5. (B) Let $w$ lie over $v$ with ramification index $e$. Use `IsDedekindDomain.HeightOneSpectrum.valuation_liesOver` to show that a uniformizer of $K_v$ has $w$-adic valuation $\exp(-e)$ in $L_w$.
6. (C) Show that the finite adele ring of $\mathbb{Z}$ is the tensor product $\hat{\mathbb{Z}} \otimes_{\mathbb{Z}} \mathbb{Q}$, where $\hat{\mathbb{Z}} = \prod_p \mathbb{Z}_p$.

### Reference

<?reference?>
