---
title: Lying over, going up and incomparability
kind: theory
modules:
  - Mathlib.RingTheory.IntegralClosure.GoingDown
explains:
  E3: [Algebra.IsIntegral.isField_iff_isField, instHasGoingDownOfIsDomainOfFaithfulSMulOfIsIntegralOfIsIntegrallyClosed]
  E2: [isField_of_isIntegral_of_isField, Algebra.IsIntegral.quotient]
  E1: [Ideal.exists_ideal_over_prime_of_isIntegral, Ideal.isMaximal_comap_of_isIntegral_of_isMaximal, Ideal.IsIntegral.under_lt_under, Algebra.HasGoingUp, Algebra.HasGoingUp.of_isIntegral, Algebra.HasGoingDown, Ideal.LiesOver, Ideal.primesOver, Ideal.under]
families: []
requires: [V06, V07]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Lying over, going up and incomparability

### Overview

Let $A \subseteq B$ be an integral extension. Every prime ideal $\mathfrak q$ of $B$ contracts to a prime ideal $\mathfrak q \cap A$ of $A$. This section studies the converse: which primes of $A$ are contractions, and how the chains of primes of $A$ and $B$ compare. The answers are the theorems of Cohen and Seidenberg. Every prime of $A$ is the contraction of a prime of $B$ (lying over). A chain of primes of $A$ lifts to a chain of primes of $B$ (going up). Two different primes of $B$ over the same prime of $A$ are not contained in one another (incomparability). And a prime of $B$ is maximal if and only if its contraction is maximal.

The example to keep in mind is $\mathbb{Z} \subseteq \mathbb{Z}[i]$. Over the prime $(5)$ lie the two primes $(2 + i)$ and $(2 - i)$, over $(2)$ lies the single prime $(1 + i)$, and over $(3)$ lies $(3)$. Chapter 4 turns this picture into the factorization of $p\mathbb{Z}[i]$, and Chapter 7 uses the theorems to prove that $A$ and $B$ have the same Krull dimension.

### Definitions

**Definition (Contraction, lying over).** Let $f : A \to B$ be a ring map and $\mathfrak q$ an ideal of $B$. The contraction of $\mathfrak q$ is $f^{-1}(\mathfrak q)$, an ideal of $A$, written $\mathfrak q \cap A$ when $f$ is an inclusion. The ideal $\mathfrak q$ lies over an ideal $\mathfrak p$ of $A$ if $f^{-1}(\mathfrak q) = \mathfrak p$.

The contraction of a prime ideal is prime: if $ab \in f^{-1}(\mathfrak q)$ then $f(a)f(b) \in \mathfrak q$, so $f(a)$ or $f(b)$ lies in $\mathfrak q$. The contraction of a maximal ideal need not be maximal: the zero ideal of $\mathbb{Q}$ is maximal, and it contracts to the zero ideal of $\mathbb{Z}$.

**Definition (Going up, going down).** The map $A \to B$ has going up if for primes $\mathfrak p_1 \subseteq \mathfrak p_2$ of $A$ and a prime $\mathfrak q_1$ of $B$ over $\mathfrak p_1$ there is a prime $\mathfrak q_2 \supseteq \mathfrak q_1$ over $\mathfrak p_2$. It has going down if for primes $\mathfrak p_1 \subseteq \mathfrak p_2$ of $A$ and a prime $\mathfrak q_2$ of $B$ over $\mathfrak p_2$ there is a prime $\mathfrak q_1 \subseteq \mathfrak q_2$ over $\mathfrak p_1$.

::: mathlib
`Ideal.LiesOver` · `Mathlib.RingTheory.Ideal.Over`

`Ideal.under A Q` is the contraction `Q.comap (algebraMap A B)`, and `Q.LiesOver p` is the class `p = Q.under A`. The set of primes over `p` is `Ideal.primesOver p B`. These modules have their home in Volume 9, Commutative algebra I. Since `LiesOver` is a class, a theorem can take `[Q.LiesOver p]` as an instance argument.

<?decl Ideal.LiesOver?>
:::

### Theorems and proofs

In this part $A \subseteq B$ is a subring and $B$ is integral over $A$. The results hold for any injective integral map, with the same proofs.

**Theorem (Fields in an integral extension).** Let $A \subseteq B$ be domains with $B$ integral over $A$. Then $A$ is a field if and only if $B$ is a field.

*Proof.* Let $A$ be a field and $y \in B$ nonzero. Choose an equation $y^n + a_{n-1}y^{n-1} + \cdots + a_0 = 0$ of least degree $n$. If $a_0 = 0$, then $y(y^{n-1} + \cdots + a_1) = 0$, and since $B$ is a domain and $y \ne 0$, the element $y$ satisfies an equation of degree $n - 1$. This contradicts minimality, so $a_0 \ne 0$. Then
$$y \cdot \left(y^{n-1} + a_{n-1}y^{n-2} + \cdots + a_1\right) = -a_0,$$
and $y^{-1} = -a_0^{-1}(y^{n-1} + \cdots + a_1) \in B$.

Let $B$ be a field and $x \in A$ nonzero. Then $x^{-1} \in B$ is integral over $A$: $x^{-m} + a_{m-1}x^{-m+1} + \cdots + a_0 = 0$ with $a_i \in A$. Multiply by $x^{m-1}$:
$$x^{-1} = -\left(a_{m-1} + a_{m-2}x + \cdots + a_0 x^{m-1}\right) \in A. \qquad \square$$

::: mathlib
`Algebra.IsIntegral.isField_iff_isField` · `Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic`

The theorem for `[Algebra.IsIntegral R S] [IsDomain S]` and an injective `algebraMap R S`. Only `S` needs to be a domain: a subring of a domain is a domain. `IsField R` is the predicate form of a field, used when `R` already has a `CommRing` structure and a `Field` instance would be a second structure.

<?decl Algebra.IsIntegral.isField_iff_isField?>
:::

**Corollary (Maximal ideals).** Let $\mathfrak q$ be a prime of $B$ and $\mathfrak p = \mathfrak q \cap A$. Then $\mathfrak q$ is maximal if and only if $\mathfrak p$ is maximal.

*Proof.* The map $A/\mathfrak p \to B/\mathfrak q$ is injective, since its kernel is $(\mathfrak q \cap A)/\mathfrak p = 0$. Both rings are domains, and $B/\mathfrak q$ is integral over $A/\mathfrak p$: reduce an equation of $b$ modulo $\mathfrak q$. By the theorem, $A/\mathfrak p$ is a field if and only if $B/\mathfrak q$ is a field. $\square$

::: mathlib
`Ideal.isMaximal_comap_of_isIntegral_of_isMaximal` · `Mathlib.RingTheory.Ideal.GoingUp`

One direction, for a ring map `f` with `f.IsIntegral`: the contraction of a maximal ideal is maximal. The converse is `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap`. The integrality of the quotient map used in the proof is the instance `Algebra.IsIntegral.quotient`.

<?decl Ideal.isMaximal_comap_of_isIntegral_of_isMaximal?>
:::

**Corollary (Incomparability).** Let $\mathfrak q \subseteq \mathfrak q'$ be primes of $B$ with $\mathfrak q \cap A = \mathfrak q' \cap A$. Then $\mathfrak q = \mathfrak q'$.

*Proof.* Put $\mathfrak p = \mathfrak q \cap A$ and $S = A \setminus \mathfrak p$. Localize at $S$: the ring $B_{\mathfrak p} = S^{-1}B$ is integral over $A_{\mathfrak p} = S^{-1}A$ (divide an equation of $b$ by $s^n$), and $A_{\mathfrak p} \to B_{\mathfrak p}$ is injective because localization preserves injective maps (Volume 9, Commutative algebra I). The ideals $\mathfrak q$ and $\mathfrak q'$ do not meet $S$, so $S^{-1}\mathfrak q \subseteq S^{-1}\mathfrak q'$ are primes of $B_{\mathfrak p}$. Both contract to $\mathfrak p A_{\mathfrak p}$, the maximal ideal of the local ring $A_{\mathfrak p}$. By the previous corollary, both are maximal, so they are equal. Primes of $B$ that do not meet $S$ correspond one to one to primes of $S^{-1}B$, so $\mathfrak q = \mathfrak q'$. $\square$

**Theorem (Lying over).** For every prime $\mathfrak p$ of $A$ there is a prime $\mathfrak q$ of $B$ with $\mathfrak q \cap A = \mathfrak p$.

*Proof.* Let $S = A \setminus \mathfrak p$. In the square
$$\begin{array}{ccc} A & \longrightarrow & B \\ \downarrow & & \downarrow \\ A_{\mathfrak p} & \longrightarrow & B_{\mathfrak p} \end{array}$$
the bottom map is injective and integral, as in the proof of incomparability. Since $A_{\mathfrak p} \ne 0$ and it embeds in $B_{\mathfrak p}$, the ring $B_{\mathfrak p}$ is not zero, and it has a maximal ideal $\mathfrak n$. By the corollary on maximal ideals, $\mathfrak n \cap A_{\mathfrak p}$ is maximal, so it is $\mathfrak p A_{\mathfrak p}$, the only maximal ideal. Let $\mathfrak q$ be the inverse image of $\mathfrak n$ in $B$. It is prime. The square commutes, so the inverse image of $\mathfrak q$ in $A$ is the inverse image of $\mathfrak p A_{\mathfrak p}$ in $A$, which is $\mathfrak p$. $\square$

**Theorem (Going up).** Let $\mathfrak p_1 \subseteq \mathfrak p_2$ be primes of $A$ and $\mathfrak q_1$ a prime of $B$ with $\mathfrak q_1 \cap A = \mathfrak p_1$. Then there is a prime $\mathfrak q_2 \supseteq \mathfrak q_1$ of $B$ with $\mathfrak q_2 \cap A = \mathfrak p_2$.

*Proof.* The map $\bar A = A/\mathfrak p_1 \to \bar B = B/\mathfrak q_1$ is injective, since $\mathfrak q_1 \cap A = \mathfrak p_1$, and integral. Apply lying over to the prime $\mathfrak p_2/\mathfrak p_1$ of $\bar A$: there is a prime $\bar{\mathfrak q}_2$ of $\bar B$ over it. Its inverse image $\mathfrak q_2$ in $B$ is a prime that contains $\mathfrak q_1$, and $\mathfrak q_2 \cap A = \mathfrak p_2$. $\square$

By induction, a chain $\mathfrak p_1 \subsetneq \mathfrak p_2 \subsetneq \cdots \subsetneq \mathfrak p_n$ of primes of $A$ lifts to a chain $\mathfrak q_1 \subseteq \cdots \subseteq \mathfrak q_n$ of primes of $B$ with $\mathfrak q_i \cap A = \mathfrak p_i$. The inclusions are strict, since the contractions differ.

::: mathlib
`Ideal.exists_ideal_over_prime_of_isIntegral` · `Mathlib.RingTheory.Ideal.GoingUp`

Lying over and going up in one statement: for `[Algebra.IsIntegral R S]`, a prime `P` of `R` and an ideal `I` of `S` with `I.under R ≤ P`, there is a prime `Q ≥ I` with `Q.under R = P`. With `I = ⊥` it is lying over, under the hypothesis that the kernel of `algebraMap R S` lies in `P`. The class `Algebra.HasGoingUp R S` packages the going up property, and `Algebra.HasGoingUp.of_isIntegral` gives it for an integral algebra. Incomparability is `Ideal.IsIntegral.under_lt_under`: a strict inclusion of primes gives a strict inclusion of contractions.

<?decl Ideal.exists_ideal_over_prime_of_isIntegral?>
:::

**Theorem (Going down).** Let $A \subseteq B$ be domains, with $A$ integrally closed and $B$ integral over $A$. Then $A \subseteq B$ has going down.

The proof needs more than this chapter: one shows that $\mathfrak p_1 B_{\mathfrak q_2} \cap A = \mathfrak p_1$, using the minimal polynomials of the elements of $B$ over the field of fractions of $A$, whose coefficients lie in $\mathfrak p_1$ by the integral closedness of $A$. See Atiyah and Macdonald, Theorem 5.16. The hypothesis that $A$ is integrally closed is needed, and the standard counterexample without it starts from a ring like the nodal cubic of Exercise 7.

::: mathlib
`instHasGoingDownOfIsDomainOfFaithfulSMulOfIsIntegralOfIsIntegrallyClosed` · `Mathlib.RingTheory.IntegralClosure.GoingDown`

The theorem is an instance of `Algebra.HasGoingDown R S`, with the hypotheses `[IsDomain S] [FaithfulSMul R S] [Algebra.IsIntegral R S] [IsIntegrallyClosed R]`. The name is generated from the statement, as for every unnamed instance. `FaithfulSMul R S` says that `algebraMap R S` is injective.

<?decl instHasGoingDownOfIsDomainOfFaithfulSMulOfIsIntegralOfIsIntegrallyClosed?>
:::

### Examples

**Example (The Gaussian integers).** Let $A = \mathbb{Z}$ and $B = \mathbb{Z}[i]$, integral since $i^2 + 1 = 0$. The nonzero primes of $\mathbb{Z}[i]$, a PID, are generated by the Gaussian primes $\pi$ (Volume 6, Chapter 6), and $(\pi) \cap \mathbb{Z} = (p)$ for the prime $p$ that divides $N(\pi) = \pi\bar\pi$.

- Over $(2)$: since $2 = -i(1 + i)^2$, the only prime is $(1 + i)$.
- Over $(5)$: since $5 = (2 + i)(2 - i)$, there are two primes, $(2 + i)$ and $(2 - i)$. They are distinct, because $(2 + i)/(2 - i) = (3 + 4i)/5 \notin \mathbb{Z}[i]$, and by incomparability neither contains the other.
- Over $(3)$: the ideal $(3)$ is prime in $\mathbb{Z}[i]$, since $\mathbb{Z}[i]/(3) \cong \mathbb{F}_3[X]/(X^2 + 1)$ is a field.
- Over $(0)$: only $(0)$, since a nonzero ideal of $\mathbb{Z}[i]$ contains the nonzero integer $N(z) = z\bar z$ for each of its nonzero elements $z$.

The chain $(0) \subsetneq (5)$ lifts to $(0) \subsetneq (2 + i)$ and to $(0) \subsetneq (2 - i)$. Each nonzero prime of $\mathbb{Z}[i]$ is maximal, as the corollary predicts from the fact that each nonzero prime of $\mathbb{Z}$ is maximal.

**Example (Integrality is needed).** Let $A = \mathbb{Z}$ and $B = \mathbb{Z}[1/2]$, not integral by Section 1. The prime $(2)$ of $\mathbb{Z}$ has no prime over it: a prime $\mathfrak q$ of $B$ with $2 \in \mathfrak q$ contains the unit $2$, so $\mathfrak q = B$. Lying over fails. The corollary on maximal ideals fails for $\mathbb{Z} \subseteq \mathbb{Q}$: the maximal ideal $(0)$ of $\mathbb{Q}$ contracts to the non-maximal ideal $(0)$ of $\mathbb{Z}$.

**Example (A geometric picture).** Let $k$ be an algebraically closed field, $A = k[x]$ and $B = k[x, y]/(y^2 - x)$. Then $B \cong k[y]$ is integral over $A$, with $y^2 = x$. The maximal ideal $(x - a)$ of $A$ is the point $a$ of the line. The primes of $B$ over it are $(y - b)$ with $b^2 = a$: two of them for $a \ne 0$ and one, $(y)$, for $a = 0$. This is the map $b \mapsto b^2$ from a line to a line, and lying over says that it is surjective on points.

### The library around it

The files `Mathlib/RingTheory/Ideal/GoingUp.lean`, `Ideal/Over.lean` and `Ideal/HasGoingUp.lean` hold these theorems. They have their home in Volume 9, Commutative algebra I, and this section uses them. The lemma names follow two patterns. The older pattern names the conclusion and the hypothesis, such as `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`. The newer one uses `under` for the contraction and `LiesOver` for the relation, such as `Ideal.IsIntegral.under_lt_under`. The classes `Algebra.HasGoingUp` and `Algebra.HasGoingDown` turn the properties of the definitions into instances, so that Chapter 7 can use them for any algebra that has them.

Common errors of a learner:

- `Ideal.comap f Q` takes the ring map first, and `Ideal.under A Q` takes the base ring first. They agree for `f = algebraMap A B`.
- Lying over needs the kernel of `A → B` inside the prime. For a non-injective map, primes that do not contain the kernel are never contractions.
- Incomparability is about primes with the same contraction. Two primes of $B$ over different primes of $A$ can be comparable.

### Exercises

1. (A) Find all primes of $\mathbb{Z}[i]$ over $(13)$ and over $(7)$.
2. (A) Let $A \subseteq B$ be integral with $B$ a domain, and let $\mathfrak b$ be a nonzero ideal of $B$. Show that $\mathfrak b \cap A \ne 0$. Hint: take the constant term of a minimal equation of a nonzero element of $\mathfrak b$.
3. (A) Show that the Jacobson radical of $A$ is the contraction of the Jacobson radical of $B$ when $B$ is integral over $A$.
4. (B) Let $G$ be a finite group of automorphisms of $B$ and $A = B^G$. Show that $B$ is integral over $A$. Hint: $b$ is a root of $\prod_{g \in G}(X - g(b))$.
5. (B) In the situation of Exercise 4, show that $G$ acts transitively on the primes of $B$ over a given prime $\mathfrak p$ of $A$. Hint: if $\mathfrak q'$ is not in the orbit of $\mathfrak q$, use prime avoidance to find $x \in \mathfrak q'$ outside every $g(\mathfrak q)$, and look at $\prod_g g(x)$.
6. (B) Let $A \subseteq B$ be integral and $\mathfrak p$ a prime of $A$. Show that the primes of $B$ over $\mathfrak p$ are exactly the maximal elements among the primes of $B$ whose contraction lies in $\mathfrak p$. Hint: use going up and incomparability.
7. (C) Let $k$ be a field, $B = k[t]$, and $A = k[t^2 - 1, t(t^2 - 1)] \subseteq B$, the ring of the nodal cubic $y^2 = x^2(x + 1)$. Show that $B$ is integral over $A$, that the two primes $(t - 1)$ and $(t + 1)$ of $B$ lie over the same maximal ideal $(t^2 - 1, t(t^2 - 1))$ of $A$, and that $A$ is not integrally closed. Hint: $t$ is a root of $X^2 - 1 - (t^2 - 1)$, and $t = t(t^2 - 1)/(t^2 - 1)$ lies in the fraction field of $A$. A ring of this kind is the base of the standard counterexample to going down without the hypothesis of integral closedness.

### Notes and history

The lying over, going up and going down theorems are due to Irvin Cohen and Abraham Seidenberg, in a paper of 1946 in the Bulletin of the American Mathematical Society. Krull had proved related results for integrally closed domains in the 1930s. The proofs of this section follow Atiyah and Macdonald, Chapter 5. Matsumura, *Commutative Ring Theory*, Theorem 9.4, gives the same theorems with going down for flat extensions as well.

In Mathlib the theorems are proved for any `Algebra R S` with `[Algebra.IsIntegral R S]`, without the hypothesis that `S` is a domain where it is not needed.

### Reference

<?reference?>
