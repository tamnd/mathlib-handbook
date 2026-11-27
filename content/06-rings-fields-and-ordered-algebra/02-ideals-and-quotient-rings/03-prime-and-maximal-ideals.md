---
title: Prime and maximal ideals
kind: theory
modules: []
explains:
  E1: [Ideal.IsPrime, Ideal.isPrime_iff, Ideal.IsPrime.mem_or_mem, Ideal.IsPrime.ne_top, Ideal.IsMaximal, Ideal.isMaximal_iff, Ideal.isMaximal_def, Ideal.IsMaximal.ne_top, Ideal.IsMaximal.isPrime, Ideal.exists_le_maximal, Ideal.Quotient.isDomain_iff_prime, Ideal.Quotient.maximal_ideal_iff_isField_quotient, Ideal.Quotient.field, Ideal.Quotient.maximal_of_isField, Ideal.span_singleton_prime, Int.ideal_span_isMaximal_of_prime, Ideal.IsPrime.comap, Ideal.comap_isMaximal_of_surjective, Ideal.ideal_prod_eq, Ideal.isPrime_ideal_prod_top, Ideal.bot_isMaximal]
families: []
requires: [V06.C01, V05.C05]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Prime and maximal ideals

### Overview

The quotient $\mathbb{Z}/n$ is a field when $n$ is prime and has zero divisors when $n$ is composite. This section finds the property of an ideal that decides such questions for each commutative ring. An ideal $P$ is prime when $a b \in P$ forces $a \in P$ or $b \in P$, and then $R/P$ has no zero divisors. An ideal $M$ is maximal when no ideal lies strictly between $M$ and $R$, and then $R/M$ is a field. Each maximal ideal is prime.

The main theorem of the section is the existence of maximal ideals: each proper ideal of a commutative ring is contained in a maximal ideal. The proof uses Zorn's lemma, and the section gives it in full. The examples determine the prime and the maximal ideals of $\mathbb{Z}$, of $\mathbb{Z}/12$, of $\mathbb{Z} \times \mathbb{Z}$, and of some ideals of $\mathbb{Z}[X]$, where $(X)$ is prime but not maximal.

All rings in this section are commutative.

### Definitions

**Definition (Integral domain).** A commutative ring $D$ is an integral domain if $0 \ne 1$ in $D$ and, for all $a, b \in D$, $a b = 0$ implies $a = 0$ or $b = 0$.

Chapter 3 studies integral domains in detail. Here the definition is enough. Each field is an integral domain: if $a b = 0$ and $a \ne 0$, then $b = a^{-1} a b = 0$.

**Definition (Prime ideal).** An ideal $P$ of $R$ is prime if $P \ne R$ and, for all $a, b \in R$, $a b \in P$ implies $a \in P$ or $b \in P$.

**Definition (Maximal ideal).** An ideal $M$ of $R$ is maximal if $M \ne R$ and, for each ideal $J$ with $M \subseteq J \subseteq R$, either $J = M$ or $J = R$.

Both definitions require a proper ideal. The unit ideal $R$ satisfies the condition on products, but it is not prime, in the same way as $1$ is not a prime number. With this choice, $R/P$ is never the zero ring.

An equivalent form of primality: if $a \notin P$ and $b \notin P$, then $a b \notin P$. So the complement $R \setminus P$ contains $1$ and is closed under products. And for ideals: if $I J \subseteq P$, then $I \subseteq P$ or $J \subseteq P$ (Exercise 4).

::: mathlib
`Ideal.IsPrime` · `Mathlib.RingTheory.Ideal.Prime`

A class: `[I.IsPrime]` is an instance argument, so a theorem about a prime ideal takes the primality from instance search. The fields are `ne_top'` and `mem_or_mem'`. Use `Ideal.IsPrime.ne_top` and `Ideal.IsPrime.mem_or_mem : I.IsPrime → x * y ∈ I → x ∈ I ∨ y ∈ I`, and `Ideal.isPrime_iff` to prove primality. The zero ideal of a domain is prime by the instance `Ideal.isPrime_bot`.

<?decl Ideal.IsPrime?>
:::

::: mathlib
`Ideal.IsMaximal` · `Mathlib.RingTheory.Ideal.Maximal`

Also a class. Its definition is `IsCoatom I` in the lattice `Ideal R`: `I ≠ ⊤` and each `J > I` is `⊤`, which is `Ideal.isMaximal_def`. The form with elements is `Ideal.isMaximal_iff`: $1 \notin I$, and each ideal $J \supseteq I$ that contains an element $x \notin I$ contains $1$. In a field the zero ideal is maximal, `Ideal.bot_isMaximal`.

<?decl Ideal.IsMaximal?>
:::

### Theorems and proofs

**Theorem (Prime ideals and integral domains).** An ideal $P$ of $R$ is prime if and only if $R/P$ is an integral domain.

*Proof.* Write $\bar a = a + P$. First, $\bar 1 \ne \bar 0$ in $R/P$ if and only if $1 \notin P$, if and only if $P \ne R$. Second, $\bar a \bar b = \bar 0$ means $a b \in P$, and $\bar a = \bar 0$ means $a \in P$. So the condition "$\bar a \bar b = \bar 0$ implies $\bar a = \bar 0$ or $\bar b = \bar 0$" is the condition "$a b \in P$ implies $a \in P$ or $b \in P$". $\square$

::: mathlib
`Ideal.Quotient.isDomain_iff_prime` · `Mathlib.RingTheory.Ideal.Quotient.Basic`

The theorem as `IsDomain (R ⧸ I) ↔ I.IsPrime`, for a two-sided ideal of a ring. `IsDomain` is the class of Chapter 3. For a prime ideal the instance `Ideal.Quotient.isDomain` gives the domain structure on the quotient with no extra step.

<?decl Ideal.Quotient.isDomain_iff_prime?>
:::

**Theorem (Maximal ideals and fields).** An ideal $M$ of $R$ is maximal if and only if $R/M$ is a field.

*Proof.* First proof, by the correspondence theorem. The ideals of $R/M$ correspond to the ideals $J$ of $R$ with $M \subseteq J$, by an order bijection that sends $M$ to $0$ and $R$ to $R/M$. So $R/M$ has exactly the two ideals $0 \ne R/M$ if and only if $M \ne R$ and no ideal lies strictly between $M$ and $R$. By the theorem on fields of Section 1, this says that $R/M$ is a field if and only if $M$ is maximal.

Second proof, with elements, for the direction from maximal to field. Let $M$ be maximal and $a \notin M$. The ideal $M + (a)$ contains $M$ and $a$, so it is strictly larger than $M$, and so it is $R$. Then $1 = m + r a$ for some $m \in M$ and $r \in R$. Hence $\bar r \bar a = \bar 1 - \bar m = \bar 1$ in $R/M$. So each nonzero class $\bar a$ has an inverse. And $\bar 1 \ne \bar 0$ since $M \ne R$. $\square$

::: mathlib
`Ideal.Quotient.maximal_ideal_iff_isField_quotient` · `Mathlib.RingTheory.Ideal.Quotient.Basic`

The theorem as `I.IsMaximal ↔ IsField (R ⧸ I)`. For a maximal ideal the field structure is `Ideal.Quotient.field I`, an abbreviation that is not a global instance, so a proof writes `letI := Ideal.Quotient.field I` when it needs `Field (R ⧸ I)`. The converse direction alone is `Ideal.Quotient.maximal_of_isField`.

<?decl Ideal.Quotient.maximal_ideal_iff_isField_quotient?>
:::

**Corollary (Maximal implies prime).** Each maximal ideal is prime.

*Proof.* If $M$ is maximal, then $R/M$ is a field, so it is an integral domain, and $M$ is prime. $\square$

The converse is false: $(0)$ is prime in $\mathbb{Z}$ but not maximal, since $(0) \subsetneq (2) \subsetneq \mathbb{Z}$.

::: mathlib
`Ideal.IsMaximal.isPrime` · `Mathlib.RingTheory.Ideal.Maximal`

The corollary for a commutative semiring, `I.IsMaximal → I.IsPrime`, proved in Mathlib with elements and not through the quotient. There is also an instance from `IsMaximal` to `IsPrime`, so a maximal ideal can be used where a prime ideal is expected.

<?decl Ideal.IsMaximal.isPrime?>
:::

**Theorem (Primes and maximal ideals of $\mathbb{Z}$).** Let $n \ge 0$. The ideal $(n)$ of $\mathbb{Z}$ is prime if and only if $n = 0$ or $n$ is a prime number. It is maximal if and only if $n$ is a prime number.

*Proof.* Each ideal of $\mathbb{Z}$ is $(n)$ with $n \ge 0$ (Section 1). The ideal $(0)$ is prime since $\mathbb{Z}/(0) \cong \mathbb{Z}$ is a domain. The ideal $(1) = \mathbb{Z}$ is not prime and not maximal. If $n = a b$ with $1 < a, b < n$, then $a b \in (n)$, but $a, b \notin (n)$, since $0 < a, b < n$. So $(n)$ is not prime, and not maximal. If $n = p$ is prime and $p \mid a b$, then $p \mid a$ or $p \mid b$ by Euclid's lemma (Volume 2), so $(p)$ is prime. For maximality, $(p) \subseteq (m)$ with $m \ge 0$ means $m \mid p$, so $m = 1$ or $m = p$. Hence $(p)$ is maximal. Finally $(0)$ is not maximal. $\square$

So $\mathbb{Z}/p$ is a field for each prime $p$. Chapter 4 proves this again with Bezout's identity and studies the field $\mathbb{Z}/p$.

::: mathlib
`Ideal.span_singleton_prime` · `Mathlib.RingTheory.Ideal.Maximal`

For each commutative semiring and `p ≠ 0`, `(span {p}).IsPrime ↔ Prime p`. Here `Prime p` is the prime element of Chapter 6: a nonzero nonunit with $p \mid a b \Rightarrow p \mid a \lor p \mid b$. For $\mathbb{Z}$ the instance `Int.ideal_span_isMaximal_of_prime` gives `(span {(p : ℤ)}).IsMaximal` from `[Fact (Nat.Prime p)]`.

<?decl Ideal.span_singleton_prime?>
:::

**Theorem (Preimages).** Let $f : R \to S$ be a ring homomorphism. If $Q$ is a prime ideal of $S$, then $f^{-1}(Q)$ is a prime ideal of $R$. If $f$ is surjective and $N$ is a maximal ideal of $S$, then $f^{-1}(N)$ is maximal.

*Proof.* $f^{-1}(Q)$ is an ideal, and it does not contain $1$, since $f(1) = 1 \notin Q$. If $a b \in f^{-1}(Q)$, then $f(a) f(b) \in Q$, so $f(a) \in Q$ or $f(b) \in Q$. For the second statement, the map $R \to S \to S/N$ is surjective with kernel $f^{-1}(N)$. So $R / f^{-1}(N) \cong S/N$, which is a field. $\square$

The preimage of a maximal ideal need not be maximal when $f$ is not surjective: for the inclusion $\mathbb{Z} \to \mathbb{Q}$, the preimage of the maximal ideal $(0)$ of $\mathbb{Q}$ is $(0)$, which is not maximal in $\mathbb{Z}$.

::: mathlib
`Ideal.IsPrime.comap` · `Mathlib.RingTheory.Ideal.Maps`

The first statement as an instance: `[K.IsPrime]` gives `(comap f K).IsPrime`. The second is `Ideal.comap_isMaximal_of_surjective`.

<?decl Ideal.IsPrime.comap?>
:::

**Theorem (Krull, existence of maximal ideals).** Let $I$ be a proper ideal of a commutative ring $R$. Then there is a maximal ideal $M$ with $I \subseteq M$. In particular each nonzero ring has a maximal ideal, and each nonunit $a$ of $R$ is in a maximal ideal.

The proof uses Zorn's lemma (Volume 4): if each chain in a nonempty partially ordered set has an upper bound, then the set has a maximal element. A chain is a subset in which any two elements are comparable.

*Proof.* Let $\mathcal{P}$ be the set of the proper ideals $J$ of $R$ with $I \subseteq J$, ordered by inclusion. It is nonempty, since $I \in \mathcal{P}$.

Let $\mathcal{C} \subseteq \mathcal{P}$ be a chain. If $\mathcal{C}$ is empty, then $I$ is an upper bound. Otherwise let $U = \bigcup_{J \in \mathcal{C}} J$. Then $U$ is an ideal. It contains $0$. Let $a, b \in U$, say $a \in J_1$ and $b \in J_2$ with $J_1, J_2 \in \mathcal{C}$. Since $\mathcal{C}$ is a chain, one of $J_1, J_2$ contains the other, say $J_1 \subseteq J_2$. Then $a, b \in J_2$, so $a - b \in J_2 \subseteq U$. For $r \in R$, $r a \in J_1 \subseteq U$. Next, $U$ is proper: each $J \in \mathcal{C}$ is proper, so $1 \notin J$, and so $1 \notin U$. And $I \subseteq U$. So $U \in \mathcal{P}$, and $U$ is an upper bound of $\mathcal{C}$.

By Zorn's lemma $\mathcal{P}$ has a maximal element $M$. It is a proper ideal that contains $I$. Let $J$ be an ideal with $M \subseteq J \ne R$. Then $J \in \mathcal{P}$, and so $J = M$ by the maximality of $M$ in $\mathcal{P}$. Hence $M$ is a maximal ideal.

For the last claims: in a nonzero ring the ideal $(0)$ is proper. A nonunit $a$ gives a proper ideal $(a)$, since $1 \in (a)$ would mean $1 = r a$ for some $r$. $\square$

The proof uses $1$ at one point only: to show that the union $U$ is proper. A counterexample below shows that the theorem fails for rings without $1$. For a Noetherian ring (Volume 9) the theorem needs no Zorn's lemma, but for an arbitrary ring it needs some form of the axiom of choice.

::: mathlib
`Ideal.exists_le_maximal` · `Mathlib.RingTheory.Ideal.Maximal`

The theorem as `I ≠ ⊤ → ∃ M, M.IsMaximal ∧ I ≤ M`, for each semiring. Mathlib proves it from the general fact that a coatomic lattice has coatoms above each element different from `⊤`. The ideal lattice is coatomic since `⊤` is compact: it is generated by the single element $1$. The form of Zorn's lemma used for such arguments in Mathlib is `zorn_le_nonempty₀`. The existence of a maximal ideal in a nonzero ring is `Ideal.exists_maximal`.

<?decl Ideal.exists_le_maximal?>
:::

### Examples

**Example (The ideals of $\mathbb{Z} \times \mathbb{Z}$).** Let $K$ be an ideal of $R = \mathbb{Z} \times \mathbb{Z}$. If $(a, b) \in K$, then $(a, 0) = (1, 0)(a, b) \in K$ and $(0, b) = (0, 1)(a, b) \in K$. So with $I = \{ a : (a, 0) \in K \}$ and $J = \{ b : (0, b) \in K \}$, which are ideals of $\mathbb{Z}$, this shows $K \subseteq I \times J$. Conversely, for $a \in I$ and $b \in J$, $(a, b) = (a, 0) + (0, b) \in K$. So $K = I \times J$. Hence each ideal is $(m) \times (n)$ with $m, n \ge 0$. The quotient is $R / ((m) \times (n)) \cong \mathbb{Z}/m \times \mathbb{Z}/n$, by the map $(a, b) \mapsto ([a], [b])$. A product of two rings is a domain only if one factor is the zero ring, since $(1, 0)(0, 1) = 0$. So the prime ideals of $\mathbb{Z} \times \mathbb{Z}$ are $(p) \times \mathbb{Z}$ and $\mathbb{Z} \times (p)$ with $p = 0$ or $p$ prime, and the maximal ideals are those with $p$ prime. The zero ideal $(0) \times (0)$ is not prime.

**Example (The ideal $(X)$ in $\mathbb{Z}[X]$).** The evaluation $\mathbb{Z}[X] \to \mathbb{Z}$, $f \mapsto f(0)$, is surjective, and its kernel is the set of the polynomials with constant term $0$, which is $(X)$. So $\mathbb{Z}[X]/(X) \cong \mathbb{Z}$. This is a domain and not a field. Hence $(X)$ is prime but not maximal. An ideal strictly between is $(2, X)$, the polynomials with even constant term. The composite $\mathbb{Z}[X] \to \mathbb{Z} \to \mathbb{Z}/2$ has kernel $(2, X)$, so $\mathbb{Z}[X]/(2, X) \cong \mathbb{Z}/2$, a field, and $(2, X)$ is maximal. In the same way $(p, X)$ is maximal for each prime $p$. The ideal $(X^2)$ is not prime, since $X \cdot X \in (X^2)$ and $X \notin (X^2)$.

**Example (The prime ideals of $\mathbb{Z}/12$).** By the correspondence theorem and the theorem on preimages, the prime ideals of $\mathbb{Z}/12$ correspond to the prime ideals $(d)$ of $\mathbb{Z}$ with $(12) \subseteq (d)$. These are $(2)$ and $(3)$. So $\mathbb{Z}/12$ has the two prime ideals $([2]) = \{[0], [2], \dots, [10]\}$ and $([3]) = \{[0], [3], [6], [9]\}$, and both are maximal, with quotients $\mathbb{Z}/2$ and $\mathbb{Z}/3$. The ideal $([6])$ is not prime: $[2][3] = [6] \in ([6])$, but $[2], [3] \notin ([6])$.

**Example (A maximal ideal of $\mathbb{R}[X]$).** By the preview example of Section 2, $\mathbb{R}[X]/(X^2 + 1) \cong \mathbb{C}$. This is a field, so $(X^2 + 1)$ is maximal in $\mathbb{R}[X]$. In $\mathbb{C}[X]$ the ideal $(X^2 + 1)$ is not prime, since $X^2 + 1 = (X - i)(X + i)$ and neither factor is a multiple of $X^2 + 1$.

**Counterexample (No maximal ideals without a unit).** Let $A$ be the additive group $\mathbb{Q}$ with the product $a b = 0$ for all $a, b$. This satisfies all ring axioms except the existence of $1$. Its ideals are exactly its additive subgroups. Suppose that $M$ is a maximal proper subgroup. Then $\mathbb{Q}/M$ has no subgroups other than $0$ and itself, by the correspondence for groups (Volume 5), so it is cyclic of prime order $p$. But $\mathbb{Q}/M$ is divisible: each class $x + M$ is $p$ times the class $x/p + M$. A cyclic group of order $p$ is not divisible, since $p$ times each element is $0$. This is a contradiction. So $A$ has no maximal ideal, and Krull's theorem needs the unit $1$.

### The library around it

The prime and maximal ideals of Mathlib are classes on `Ideal R`, not subtypes. A theorem about a prime ideal takes `(P : Ideal R) [P.IsPrime]`, and instances carry the primality through `comap` and the quotient. The set of all prime ideals is the type `PrimeSpectrum R` of Volume 9, which carries the Zariski topology, and the maximal ideals form `MaximalSpectrum R`.

The ideals of a product are handled in `Mathlib/RingTheory/Ideal/Prod.lean`. The theorem `Ideal.ideal_prod_eq` writes each ideal of `R × S` as `Ideal.prod I J`, as in the example, and `Ideal.isPrime_ideal_prod_top : I.IsPrime → (I.prod ⊤).IsPrime` gives the prime ideals of the first kind.

Common errors of a learner:

- `Ideal.IsPrime P` is a class. Writing `(h : P.IsPrime)` as an explicit hypothesis works, but then instance search does not see `h`. Use `[P.IsPrime]`, or `haveI := h`.
- `Ideal.Quotient.field` is not an instance. Without `letI := Ideal.Quotient.field M` the goal `Field (R ⧸ M)` fails, even for a maximal `M`.
- `Prime p` for an element and `(Ideal.span {p}).IsPrime` differ at `p = 0`: the zero ideal of a domain is prime, but `0` is not a prime element.
- `Nat.Prime p` and `Prime (p : ℤ)` are different statements. The bridge is `Int.prime_iff_natAbs_prime` (Volume 2).

### Exercises

1. (A) Find all prime and all maximal ideals of $\mathbb{Z}/30$, and the quotient by each.
2. (A) Show that $(X^2 + X + 1)$ is maximal in $(\mathbb{Z}/2)[X]$. Hint: the quotient has four elements; check that each nonzero class has an inverse.
3. (A) Show that $(3, X)$ is maximal and that $(X^2 - 2)$ is prime in $\mathbb{Z}[X]$, using quotients. Hint: $\mathbb{Z}[X]/(X^2 - 2) \cong \mathbb{Z}[\sqrt 2]$.
4. (B) Let $P$ be prime and $I, J$ ideals with $I J \subseteq P$. Show $I \subseteq P$ or $J \subseteq P$. Deduce: if $I \cap J \subseteq P$, then $I \subseteq P$ or $J \subseteq P$.
5. (B) Show that in a finite commutative ring each prime ideal is maximal. Hint: a finite integral domain is a field (Chapter 3), or prove directly that multiplication by $a \ne 0$ is injective on $R/P$.
6. (B) Let $R$ be the ring of all functions $[0, 1] \to \mathbb{R}$. Show that $M_c = \{ f : f(c) = 0 \}$ is maximal for each $c \in [0, 1]$, and find a proper ideal of $R$ that is not contained in any $M_c$. Hint: the functions that vanish outside a finite set.
7. (B) Show that the intersection of all prime ideals of $R$ contains each nilpotent element of $R$.
8. (C) Show that the intersection of all prime ideals of $R$ is the set of the nilpotent elements. Hint: for $a$ not nilpotent, apply Zorn's lemma to the ideals that contain no power of $a$, and show that a maximal one is prime.
9. (C) Let $R$ be the ring of the continuous functions $[0, 1] \to \mathbb{R}$. Show that each maximal ideal of $R$ is $M_c$ for some $c$. Hint: if $M$ is not contained in any $M_c$, use compactness to find $f_1, \dots, f_n \in M$ with no common zero, and look at $f_1^2 + \dots + f_n^2$.
10. (C) Show that the ideal $(X, Y)$ of $\mathbb{Z}[X, Y]$ is prime and not maximal, and find a chain of three distinct prime ideals $(0) \subsetneq P_1 \subsetneq P_2 \subsetneq P_3$ in $\mathbb{Z}[X, Y]$.

### Notes and history

Prime ideals generalize prime numbers, and Dedekind proved in 1871 that in the ring of integers of a number field each nonzero ideal is a product of prime ideals in exactly one way. The definitions for an arbitrary commutative ring, and the link between maximal ideals and fields, are due to Emmy Noether and Wolfgang Krull in the 1920s. Krull proved the existence of maximal ideals in 1929 with the well-ordering theorem. The proof with Zorn's lemma is the standard one today. Hodges showed in 1979 that Krull's theorem for all commutative rings is equivalent to the axiom of choice. Standard references are Atiyah and Macdonald, *Introduction to Commutative Algebra*, Chapter 1, Theorem 1.3, and Dummit and Foote, *Abstract Algebra*, Section 7.4.

In Mathlib the classes `Ideal.IsPrime` and `Ideal.IsMaximal` come from the Lean 3 file `ring_theory/ideals.lean` by Kenny Lau, Chris Hughes and Mario Carneiro. The files were later split into `Mathlib/RingTheory/Ideal/Prime.lean` and `Mathlib/RingTheory/Ideal/Maximal.lean`.

### Reference

<?reference?>
