---
title: The basic API of ideals
kind: api
modules:
  - Mathlib.RingTheory.Ideal.Defs
  - Mathlib.RingTheory.Ideal.Basic
  - Mathlib.RingTheory.Ideal.Span
  - Mathlib.RingTheory.Ideal.Lattice
  - Mathlib.RingTheory.Ideal.Prime
  - Mathlib.RingTheory.Ideal.Maximal
  - Mathlib.RingTheory.Ideal.Nonunits
  - Mathlib.RingTheory.Ideal.IsPrincipal
  - Mathlib.RingTheory.Ideal.Prod
  - Mathlib.RingTheory.Ideal.Pointwise
  - Mathlib.RingTheory.Ideal.Basis
  - Mathlib.RingTheory.Ideal.BigOperators
  - Mathlib.RingTheory.Ideal.Finsupp
  - Mathlib.RingTheory.Ideal.NatInt
explains:
  E2: [Ideal.span_le, Ideal.mem_span_singleton, Ideal.exists_le_maximal, Ideal.IsMaximal.isPrime, Ideal.isPrime_of_maximally_disjoint, Ideal.ideal_prod_prime, Ideal.isPrime_int_iff, Ideal.add_pow_add_pred_mem_of_pow_mem]
  E1: auto
families: []
requires: [V06.C02, V06.C03, V04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The basic API of ideals

### Overview

The sections before this one use ideals freely: their sums and products, their spans, prime and maximal ideals. This section describes the files of the library that define these objects and give their first properties. The files are small, but almost every proof in commutative algebra uses them. A reader who knows the names of this section can write the first lines of most proofs about ideals.

In Mathlib an ideal of a semiring $R$ is a submodule of $R$ over itself. So `Ideal R` is an abbreviation for `Submodule R R`, and the order, the lattice operations and the span come from the theory of submodules of Volume 7. The files add the facts that need the multiplication of $R$: primes, maximal ideals, principal ideals, the ideals of a product, and the action of a group on the ideals. Most results hold for a semiring, and many of them for a noncommutative one. The text states them for a commutative ring when the general form adds nothing.

### The library around it

#### Ideals as submodules

The module `Mathlib.RingTheory.Ideal.Defs` defines `Ideal` and the membership lemmas. The names follow the closure properties: `Ideal.zero_mem`, `Ideal.add_mem`, `Ideal.sub_mem`, `Ideal.neg_mem_iff` and `Ideal.mul_mem_left`, which says that $b \in I$ gives $a b \in I$. Since an ideal is a left submodule, the right form `Ideal.mul_mem_right` needs the class `Ideal.IsTwoSided`. This class has an instance `Ideal.instIsTwoSided` for each commutative semiring, so in commutative algebra a reader never sees it. Two ideals are equal when they have the same members: `Ideal.ext`. The lemmas `Ideal.mul_unit_mem_iff_mem` and `Ideal.unit_mul_mem_iff_mem` remove a unit factor, `Ideal.mem_of_dvd` says that $a \mid b$ and $a \in I$ give $b \in I$, and `Ideal.pow_mem_of_mem` gives $a^n \in I$ for $n > 0$.

The module `Mathlib.RingTheory.Ideal.Lattice` restates the membership lemmas of the lattice operations for ideals: `Ideal.mem_bot`, `Ideal.mem_inf`, `Ideal.mem_iInf`, `Ideal.mem_sInf`, `Ideal.mem_sup_left` and `Ideal.mem_iSup_of_mem`. The lemma `Ideal.ne_top_iff_one` says that $I \ne R$ if and only if $1 \notin I$. This is the usual way to prove that an ideal is proper. The module `Mathlib.RingTheory.Ideal.BigOperators` adds `Ideal.sum_mem`: a finite sum of members of $I$ is in $I$.

#### Spans

For a subset $s \subseteq R$, `Ideal.span s` is the smallest ideal that contains $s$. The module `Mathlib.RingTheory.Ideal.Span` gives its universal property and the descriptions of the span of one or two elements.

**Theorem.** `Ideal.span_le`: $\operatorname{span}(s) \le I$ if and only if $s \subseteq I$. `Ideal.mem_span_singleton`: in a commutative semiring, $x \in (y)$ if and only if $y \mid x$.

*Proof.* The span is the intersection of the ideals that contain $s$ (`Ideal.mem_span`), so it lies in each such ideal $I$. Conversely $s \subseteq \operatorname{span}(s)$ by `Ideal.subset_span`. For the second statement, the set $\{a y : a \in R\}$ is an ideal that contains $y$, and each ideal that contains $y$ contains it. So $(y) = \{a y\}$, and $x = a y$ means $y \mid x$. $\square$

The lemmas on spans fall into families.

| Lean name | Statement |
|---|---|
| `Ideal.mem_span_pair` | $z \in (x, y)$ if and only if $z = a x + b y$ for some $a, b$ |
| `Ideal.mem_span_singleton_sup` | $x \in (y) + I$ if and only if $x = a y + b$ with $b \in I$ |
| `Ideal.span_singleton_le_span_singleton` | $(x) \le (y)$ if and only if $y \mid x$ |
| `Ideal.span_singleton_eq_span_singleton` | in a domain, $(x) = (y)$ if and only if $x$ and $y$ are associated |
| `Ideal.span_singleton_eq_top` | $(x) = R$ if and only if $x$ is a unit |
| `Ideal.span_singleton_eq_bot` | $(x) = 0$ if and only if $x = 0$ |
| `Ideal.span_singleton_lt_span_singleton` | in a domain, $(x) < (y)$ if and only if $y$ is a strict divisor of $x$ |
| `Ideal.span_insert` | $\operatorname{span}(\{x\} \cup s) = (x) + \operatorname{span}(s)$ |
| `Ideal.iSup_eq_span` | a supremum of ideals is the span of their union |
| `Ideal.span_eq_top_iff_finite` | if $\operatorname{span}(s) = R$, then a finite subset of $s$ spans $R$ |

The last result comes from `Ideal.isCompactElement_top`: the ideal $R$ is a compact element of the lattice of ideals, since it is generated by $1$. A large family of lemmas `Ideal.span_pair_add_mul_left`, `Ideal.span_pair_sub_mul_right` and their variants does the row operations of the Euclidean algorithm: $(x, y + z x) = (x, y)$. The class `IsPrincipalIdealRing` also lives here, with `isPrincipalIdealRing_iff`: each ideal is principal.

The module `Mathlib.RingTheory.Ideal.Basic` holds facts that combine spans and powers. The binomial theorem gives:

**Theorem.** `Ideal.add_pow_add_pred_mem_of_pow_mem`: if $a^m \in I$ and $b^n \in I$, then $(a + b)^{m + n - 1} \in I$.

*Proof.* Expand $(a + b)^{m+n-1} = \sum_k \binom{m+n-1}{k} a^k b^{m+n-1-k}$. In each term, either $k \ge m$, or $k \le m - 1$ and then $m + n - 1 - k \ge n$. So each term has a factor $a^m$ or $b^n$, and lies in $I$. $\square$

This is the key step in the proof that the radical of an ideal is an ideal. The same module proves `Ideal.span_pow_eq_top`: if $s$ spans $R$, then so do the $n$-th powers of the members of $s$. It also relates fields and ideals: `Ring.isField_iff_maximal_bot` says that $R$ is a field if and only if $0$ is a maximal ideal, `Ring.isField_iff_isSimpleOrder_ideal` says that a field has exactly two ideals, and `Ideal.equivFinTwo` makes this an equivalence with `Fin 2`. For a family of rings $R_i$, `Ideal.pi` is the product ideal $\prod_i I_i$, with `Ideal.mem_pi`.

#### Prime and maximal ideals

The module `Mathlib.RingTheory.Ideal.Prime` defines the class `Ideal.IsPrime`. Its fields give `Ideal.IsPrime.ne_top` and `Ideal.IsPrime.mem_or_mem`, and `Ideal.isPrime_iff` gives the textbook form: $P \ne R$, and $x y \in P$ implies $x \in P$ or $y \in P$. Derived lemmas are `Ideal.IsPrime.mem_of_pow_mem`, `Ideal.IsPrime.mul_mem_iff_mem_or_mem` and `Ideal.IsPrime.mul_notMem`. The complement of a prime is a submonoid, `Ideal.primeCompl`, the submonoid at which Chapter 2 localizes. For a set of primes, `Ideal.sInfPrimeCompl` is the submonoid of the elements outside all of them, with `Ideal.mem_sInfPrimeCompl_iff`. The lemma `IsDomain.of_bot_isPrime` says that a ring whose zero ideal is prime is a domain.

The module `Mathlib.RingTheory.Ideal.Maximal` defines `Ideal.IsMaximal` as a coatom of the lattice of ideals, and proves the existence theorems by Zorn's lemma.

**Theorem.** `Ideal.exists_le_maximal`: each proper ideal lies in a maximal ideal. `Ideal.IsMaximal.isPrime`: in a commutative ring, each maximal ideal is prime.

*Proof.* The lattice of ideals is coatomic, `Ideal.instIsCoatomic`. The reason is that the union of a chain of proper ideals does not contain $1$, so it is proper, and Zorn's lemma applies above $I$. For the second statement, let $M$ be maximal and $x y \in M$ with $x \notin M$. Then $M + (x) = R$, so $1 = m + a x$ with $m \in M$ (`Ideal.IsMaximal.exists_inv`). So $y = m y + a x y \in M$. $\square$

The proof of the existence of primes is the same with a different family of ideals.

**Theorem.** `Ideal.isPrime_of_maximally_disjoint`: let $S$ be a submonoid of $R$ and $I$ an ideal disjoint from $S$. If no ideal $J > I$ is disjoint from $S$, then $I$ is prime.

*Proof.* Let $x, y \notin I$. Then $I + (x)$ and $I + (y)$ meet $S$: $s = i + a x$ and $t = j + b y$ with $s, t \in S$. The product $s t \in S$ is $i'+ a b x y$ with $i' \in I$. If $x y \in I$, then $s t \in I$, a contradiction. $\square$

With Zorn's lemma this gives `Ideal.exists_le_prime_disjoint`, used in Section 2. The module also has `Ideal.exists_maximal` (a nontrivial ring has a maximal ideal), `Ideal.IsMaximal.coprime_of_ne` (two different maximal ideals are coprime), `Ideal.sInf_isPrime_of_isChain` (the intersection of a chain of primes is prime), and `Ideal.span_singleton_prime`: for $p \ne 0$, the ideal $(p)$ is prime if and only if $p$ is a prime element. In a principal ideal ring, `Ideal.isPrime_iff_of_isPrincipalIdealRing` says that the nonzero primes are the ideals $(p)$ with $p$ prime.

The module `Mathlib.RingTheory.Ideal.Nonunits` defines the set `nonunits R` of the elements that are not units, with `mem_nonunits_iff`. The lemma `exists_max_ideal_of_mem_nonunits` says that each nonunit lies in a maximal ideal. A ring is local exactly when `nonunits R` is closed under addition.

#### Principal ideals of a domain

In a domain $R$, an element $x$ and the ideal $(x)$ determine each other up to a unit. The module `Mathlib.RingTheory.Ideal.IsPrincipal` makes this an isomorphism of monoids. `Ideal.isPrincipalSubmonoid R` is the submonoid of the principal ideals under the product of ideals, and `Ideal.associatesMulEquivIsPrincipal` is the isomorphism from `Associates R` to it. The equivalence `Ideal.associatesEquivIsPrincipal` is the same map as a bijection, and `Ideal.associatesEquivIsPrincipal_mul` says that it respects products. The form with nonzero divisors, `Ideal.associatesNonZeroDivisorsEquivIsPrincipal`, excludes the zero ideal. For a principal ideal $I \ne 0$, `Ideal.isoBaseOfIsPrincipal` is an isomorphism of $R$-modules $R \cong I$, multiplication by a generator. The module `Mathlib.RingTheory.Ideal.Basis` gives the corresponding fact for an algebra: if $S$ is a domain with an $R$-basis $b$ and $x \ne 0$, then `Ideal.basisSpanSingleton b x` is the $R$-basis $b_i x$ of the ideal $(x)$ of $S$. The lemma `Basis.mem_ideal_iff` writes the members of an ideal with a basis as linear combinations.

#### Ideals of a product and pointwise actions

The module `Mathlib.RingTheory.Ideal.Prod` treats $R \times S$. Each ideal of $R \times S$ is a product $I \times J$: `Ideal.ideal_prod_eq`, with `Ideal.prod` and `Ideal.mem_prod`, and `Ideal.idealProdEquiv` is the order isomorphism between `Ideal (R × S)` and `Ideal R × Ideal S`.

**Theorem.** `Ideal.ideal_prod_prime`: the prime ideals of $R \times S$ are the ideals $P \times S$ with $P$ prime in $R$, and the ideals $R \times Q$ with $Q$ prime in $S$.

*Proof.* Let $I \times J$ be prime. The product $(1, 0)(0, 1) = 0$ lies in it, so $1 \in I$ or $1 \in J$. Say $J = S$. Then $(R \times S)/(I \times S) \cong R/I$, so $I$ is prime. The converse is the same computation. $\square$

The instance `instIsPrincipalIdealRingProd` says that a product of two principal ideal rings is one, and `RingHom.ker_prodMap` computes the kernel of a product of maps.

The module `Mathlib.RingTheory.Ideal.Pointwise` lets a group $G$ that acts on $R$ by ring automorphisms act on the ideals: `Ideal.pointwiseMulSemiringAction`. The lemma `Ideal.pointwise_smul_eq_comap` writes $g \cdot I$ as the preimage of $I$ under $g^{-1}$, and the instance `Ideal.IsPrime.smul` says that $g \cdot P$ is prime when $P$ is. The inertia subgroup `Ideal.inertia G P`, defined in `Mathlib.RingTheory.Ideal.Defs`, is the subgroup of the $g$ with $g x - x \in P$ for each $x$ (`Ideal.mem_inertia`). It lies in the stabilizer of $P$ (`Ideal.inertia_le_stabilizer`) and is normal in it. These are the decomposition and inertia groups of algebraic number theory. The module `Mathlib.RingTheory.Ideal.Finsupp` has one lemma, `Finsupp.submodule_smul`, which moves the product $I \cdot N$ through the finitely supported functions.

#### The ideals of the integers and the natural numbers

The module `Mathlib.RingTheory.Ideal.NatInt` lists the prime ideals of $\mathbb{Z}$ and of the semiring $\mathbb{N}$.

**Theorem.** `Ideal.isPrime_int_iff`: a prime ideal of $\mathbb{Z}$ is $0$ or $(p)$ for a prime number $p$.

*Proof.* The ring $\mathbb{Z}$ is a principal ideal domain, so a nonzero prime ideal is $(n)$ for a prime element $n$ by `Ideal.isPrime_iff_of_isPrincipalIdealRing`, and $n = \pm p$ with $p$ a prime number. $\square$

The case of $\mathbb{N}$ is a surprise. The set $\{n : n \ne 1\}$ is an ideal of $\mathbb{N}$, since it is closed under addition and under multiplication by any $n$. So $\mathbb{N}$ is a local semiring (`instIsLocalRingNat`), its maximal ideal is $(2, 3)$ (`Nat.maximalIdeal_eq_span_two_three`), and `Ideal.isPrime_nat_iff` says that the primes are $0$, the maximal ideal and the ideals $(p)$. The chain $0 < (2) < (2, 3)$ gives `ringKrullDim_nat`: $\mathbb{N}$ has dimension $2$.

#### Common errors

1. `Ideal.mem_span_singleton` needs a commutative semiring. In a noncommutative ring, use `Ideal.mem_span_singleton'`, which writes the members as $a y$.
2. `Ideal.IsPrime` and `Ideal.IsMaximal` are classes. A hypothesis `hP : P.IsPrime` is not found by instance search unless it is in square brackets or installed with `haveI`, and lemmas such as `Ideal.primeCompl` need the instance.
3. `Ideal.span {x, y}` is the span of a set with two members. The lemmas on pairs use this form, and `Ideal.span_pair_comm` swaps the members.

### Exercises

1. (A) Prove that $(6, 10) = (2)$ in $\mathbb{Z}$ with `Ideal.span_pair_add_mul_left` and `Ideal.span_pair_comm`.
2. (A) Prove that a proper ideal $I$ of $R$ with $x \notin I$ has $I + (x) = R$ when $I$ is maximal, with `Ideal.IsMaximal.exists_inv`.
3. (B) Use `Ideal.ideal_prod_prime` to list the prime ideals of $\mathbb{Z} \times \mathbb{Q}$.
4. (B) Prove that the intersection of a nonempty chain of prime ideals is prime, and compare the proof with `Ideal.sInf_isPrime_of_isChain`.
5. (B) Show that $\{n \in \mathbb{N} : n \ne 1\}$ is an ideal of $\mathbb{N}$ and that it equals $(2, 3)$.
6. (C) Let $R$ be a domain. Prove that the map from `Associates R` to the principal ideals is an isomorphism of monoids, as in `Ideal.associatesMulEquivIsPrincipal`.

### Reference

<?reference?>
