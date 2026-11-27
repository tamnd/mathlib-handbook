---
title: Computing a class group
kind: theory
modules:
  - Mathlib.RingTheory.ClassGroup.Basic
explains:
  E3: [ClassGroup.mk0_eq_mk0_iff, ClassGroup.mk0_surjective, ClassGroup.induction]
  E2: [ClassGroup.mk0_eq_mk0_inv_iff, mem_principal_ideals_iff, ClassGroup.integralRep, ClassGroup.mk0_integralRep, ClassGroup.mk_mk0, ClassGroup.exists_mk0_eq_and_isCoprime]
  E1: auto
families: []
requires: [V10.C04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Computing a class group

### Overview

This section computes the class group of $A = \mathbb{Z}[\sqrt{-5}]$ and finds that it has order $2$. The method works for every ring of integers of a number field. First, find a bound $B$ such that every class contains an ideal of norm at most $B$. Second, list the ideals of norm at most $B$ by factoring the small primes. Third, decide which of these ideals are principal and which are in the same class.

For $\mathbb{Z}[\sqrt{-5}]$ the bound comes from a pigeonhole argument in the lattice $A \cong \mathbb{Z}^2$. The general bound, due to Minkowski, uses the geometry of numbers and is the subject of Volume 12.

### Definitions

Throughout, $A = \mathbb{Z}[\sqrt{-5}] = \mathbb{Z} \oplus \mathbb{Z}\sqrt{-5}$. It is the ring of integers of $\mathbb{Q}(\sqrt{-5})$, because $-5 \equiv 3 \pmod 4$, so it is a Dedekind domain (Chapter 4, Section 1). Write $\sigma$ for the conjugation $a + b\sqrt{-5} \mapsto a - b\sqrt{-5}$.

**Definition (Norm of an element).** For $\alpha = a + b\sqrt{-5}$, $N(\alpha) = \alpha\sigma(\alpha) = a^2 + 5b^2$. It is multiplicative, and $N(\alpha) = 1$ if and only if $\alpha = \pm 1$.

**Definition (Norm of an ideal).** For a nonzero ideal $I$ of a Dedekind domain $A$ whose additive group is $\mathbb{Z}^n$, the norm is the index $N(I) = |A/I|$, a positive integer.

Three facts about the norm of ideals are needed. They hold for every ring of integers, and Volume 9 has them in the library.

1. $N(\alpha A) = |N(\alpha)|$ for $\alpha \ne 0$. For $A = \mathbb{Z}[\sqrt{-5}]$: multiplication by $\alpha = a + b\sqrt{-5}$ has the matrix $\begin{pmatrix} a & -5b \\ b & a \end{pmatrix}$ in the basis $1, \sqrt{-5}$, and the index of the image of a lattice map is the absolute value of its determinant, here $a^2 + 5b^2$.
2. $N(IJ) = N(I)N(J)$. By the Chinese remainder theorem it is enough to treat powers of one prime $\mathfrak p$, and each quotient $\mathfrak p^k/\mathfrak p^{k+1}$ is a one-dimensional vector space over $A/\mathfrak p$, so $N(\mathfrak p^k) = N(\mathfrak p)^k$.
3. If $\mathfrak p$ is a nonzero prime, then $\mathfrak p \cap \mathbb{Z} = p\mathbb{Z}$ for a prime number $p$, and $N(\mathfrak p)$ divides $N(pA) = p^2$. So $N(\mathfrak p) \in \{p, p^2\}$.

::: mathlib
`Ideal.absNorm` · `Mathlib.RingTheory.Ideal.Norm.AbsNorm`

`Ideal.absNorm : Ideal S →*₀ ℕ` is the index of an ideal, for a Dedekind domain `S` that is a free finite `ℤ`-module. It is multiplicative, and `Ideal.absNorm_span_singleton` says that `Ideal.absNorm (span {r}) = (Algebra.norm ℤ r).natAbs`.

<?decl Ideal.absNorm?>
:::

### Theorems and proofs

**Theorem (Lattice bound).** Every class in $\operatorname{Cl}(A)$ contains an ideal $J$ with $N(J) \le 6$.

*Proof.* Let $c$ be a class. Choose a nonzero ideal $I$ in the class $c^{-1}$ (every class contains an integral ideal) and let $n = N(I)$ and $m = \lfloor \sqrt n \rfloor$, so $(m + 1)^2 > n$. The $(m + 1)^2$ elements $a + b\sqrt{-5}$ with $0 \le a, b \le m$ cannot lie in distinct cosets of $I$, since $A/I$ has $n$ elements. So two of them are congruent modulo $I$, and their difference $\alpha = a + b\sqrt{-5}$ is a nonzero element of $I$ with $|a|, |b| \le m$. Then
$$N(\alpha) = a^2 + 5b^2 \le 6m^2 \le 6n.$$
Since $\alpha \in I$, the ideal $I$ divides $\alpha A$ (to contain is to divide, Chapter 4, Section 3), so $\alpha A = IJ$ for an ideal $J$. By the facts on the norm, $N(J) = N(\alpha)/N(I) \le 6$. In the class group, $[I][J] = [\alpha A] = 1$, so $[J] = [I]^{-1} = c$. $\square$

::: mathlib
`ClassGroup.mk0_eq_mk0_inv_iff` · `Mathlib.RingTheory.ClassGroup.Basic`

The last step of the proof in the library: `mk0 I = (mk0 J)⁻¹ ↔ ∃ x, x ≠ 0 ∧ I * J = span {x}`. The same step for two classes is `ClassGroup.mk0_eq_mk0_iff`, `mk0 I = mk0 J ↔ ∃ x y, x ≠ 0 ∧ y ≠ 0 ∧ span {x} * I = span {y} * J`.

<?decl ClassGroup.mk0_eq_mk0_inv_iff?>
:::

**Theorem (Small primes).** In $A = \mathbb{Z}[\sqrt{-5}]$, let
$$\mathfrak p = (2, 1 + \sqrt{-5}), \quad \mathfrak q = (3, 1 + \sqrt{-5}), \quad \mathfrak q' = (3, 1 - \sqrt{-5}), \quad \mathfrak r = (\sqrt{-5}).$$
These are primes with $N(\mathfrak p) = 2$, $N(\mathfrak q) = N(\mathfrak q') = 3$, $N(\mathfrak r) = 5$, and
$$(2) = \mathfrak p^2, \quad (3) = \mathfrak q\mathfrak q', \quad (5) = \mathfrak r^2, \quad \mathfrak p\mathfrak q = (1 + \sqrt{-5}), \quad \mathfrak p\mathfrak q' = (1 - \sqrt{-5}).$$
They are the only primes of norm at most $6$.

*Proof.* Write $A = \mathbb{Z}[X]/(X^2 + 5)$. Then $A/\mathfrak p = \mathbb{Z}[X]/(2, 1 + X, X^2 + 5)$. Modulo $1 + X$, $X = -1$ and $X^2 + 5 = 6$, so $A/\mathfrak p = \mathbb{Z}/(2, 6) = \mathbb{F}_2$. In the same way $A/\mathfrak q = \mathbb{Z}/(3, 6) = \mathbb{F}_3$, $A/\mathfrak q' = \mathbb{F}_3$ (with $X = 1$), and $A/\mathfrak r = \mathbb{Z}/(5)$. So all four are maximal, with the stated norms.

The products: $\mathfrak p^2 = (4, 2 + 2\sqrt{-5}, (1 + \sqrt{-5})^2) = (4, 2 + 2\sqrt{-5}, -4 + 2\sqrt{-5})$. All three generators are multiples of $2$, and $2 = (2 + 2\sqrt{-5}) - (-4 + 2\sqrt{-5}) - 4$, so $\mathfrak p^2 = (2)$. Next, $1 + \sqrt{-5}$ lies in $\mathfrak p$ and in $\mathfrak q$, so $(1 + \sqrt{-5}) \subseteq \mathfrak p \cap \mathfrak q = \mathfrak p\mathfrak q$, where the equality holds because $\mathfrak p$ and $\mathfrak q$ are distinct maximal ideals. Both sides have norm $6$, so they are equal. The same argument gives $\mathfrak p\mathfrak q' = (1 - \sqrt{-5})$. The ideal $\mathfrak q + \mathfrak q'$ contains $(1 + \sqrt{-5}) + (1 - \sqrt{-5}) = 2$ and $3$, so $\mathfrak q + \mathfrak q' = A$ and the two primes are distinct. So $(3) \subseteq \mathfrak q \cap \mathfrak q' = \mathfrak q\mathfrak q'$, and both sides have norm $9$. Finally $\mathfrak r^2 = (-5) = (5)$.

A prime $\mathfrak P$ of norm at most $6$ has norm $p$ or $p^2$ with $p \in \{2, 3, 5\}$, by fact 3, and it contains $p$. A prime that contains $2$ divides $(2) = \mathfrak p^2$, so it is $\mathfrak p$. In the same way the primes that contain $3$ are $\mathfrak q$ and $\mathfrak q'$, and the prime that contains $5$ is $\mathfrak r$. $\square$

**Theorem (Class group of $\mathbb{Z}[\sqrt{-5}]$).** $\operatorname{Cl}(\mathbb{Z}[\sqrt{-5}])$ is cyclic of order $2$, generated by $[\mathfrak p]$.

*Proof.* By the lattice bound, every class contains an ideal of norm at most $6$. Such an ideal is a product of primes of norm at most $6$, whose norms multiply to at most $6$. By the theorem on small primes, the ideals of norm at most $6$ are
$$A, \quad \mathfrak p, \quad \mathfrak q, \quad \mathfrak q', \quad \mathfrak p^2 = (2), \quad \mathfrak r = (\sqrt{-5}), \quad \mathfrak p\mathfrak q = (1 + \sqrt{-5}), \quad \mathfrak p\mathfrak q' = (1 - \sqrt{-5}).$$
Five of them are principal. For the other three, $[\mathfrak p]^2 = [(2)] = 1$, so $[\mathfrak p] = [\mathfrak p]^{-1}$, and $[\mathfrak q] = [\mathfrak p]^{-1} = [\mathfrak p]$ from $\mathfrak p\mathfrak q = (1 + \sqrt{-5})$, and $[\mathfrak q'] = [\mathfrak p]$ in the same way. So $\operatorname{Cl}(A) = \{1, [\mathfrak p]\}$.

It remains to show that $\mathfrak p$ is not principal. If $\mathfrak p = (\alpha)$, then $N(\alpha) = N(\mathfrak p) = 2$. But $a^2 + 5b^2 = 2$ has no integer solution: $b = 0$ gives $a^2 = 2$, and $b \ne 0$ gives a value at least $5$. So $[\mathfrak p] \ne 1$. $\square$

::: mathlib
`ClassGroup.mk0_surjective` · `Mathlib.RingTheory.ClassGroup.Basic`

`Function.Surjective (ClassGroup.mk0 (R := R))` for a Dedekind domain: every class is the class of a nonzero integral ideal. The proof uses `ClassGroup.integralRep`, which sends a fractional ideal to the integral ideal of its numerators, with `ClassGroup.mk0_integralRep` and `ClassGroup.mk_mk0` comparing the two class maps. The sharper `ClassGroup.exists_mk0_eq_and_isCoprime` finds, for every class and nonzero ideal `J`, an ideal in the class that is coprime to `J`.

<?decl ClassGroup.mk0_surjective?>
:::

::: mathlib
`ClassGroup.induction` · `Mathlib.RingTheory.ClassGroup.Basic`

To prove a statement for every element of `ClassGroup R`, it is enough to prove it for `ClassGroup.mk K I` with `I` a unit fractional ideal. The membership criterion for the subgroup of principal ideals is `mem_principal_ideals_iff : I ∈ (toPrincipalIdeal R K).range ↔ ∃ x, spanSingleton _ x = I`.

<?decl ClassGroup.induction?>
:::

::: mathlib
`NumberField.exists_ideal_in_class_of_norm_le` · `Mathlib.NumberTheory.NumberField.ClassNumber`

The general form of the lattice bound, in Volume 12: for a number field `K`, every class `C` of the ring of integers contains an ideal `I` with `Ideal.absNorm I ≤ NumberField.minkowskiNormBound K`. For $\mathbb{Q}(\sqrt{-5})$ the Minkowski bound is $\frac{4}{\pi}\sqrt 5 \approx 2.85$, which reduces the list to the primes over $2$.

<?decl NumberField.exists_ideal_in_class_of_norm_le?>
:::

### Examples

**Example (Gaussian integers).** For $\mathbb{Z}[i]$ the same argument gives elements $a + bi$ with $|a|, |b| \le m$ and $N(a + bi) = a^2 + b^2 \le 2m^2 \le 2n$. So every class contains an ideal of norm at most $2$. The only ideal of norm $2$ is $(1 + i)$, which is principal, so $\operatorname{Cl}(\mathbb{Z}[i]) = 1$ and $\mathbb{Z}[i]$ is a PID. The same conclusion follows from the Euclidean algorithm (Volume 9).

**Example ($\mathbb{Z}[\sqrt{-6}]$).** For $A = \mathbb{Z}[\sqrt{-6}]$, the same pigeonhole argument gives $N(\alpha) \le 7m^2 \le 7n$, so every class contains an ideal of norm at most $7$. The primes of norm at most $7$ are $\mathfrak p_2 = (2, \sqrt{-6})$ and $\mathfrak p_3 = (3, \sqrt{-6})$, with $\mathfrak p_2^2 = (2)$ and $\mathfrak p_3^2 = (3)$; the two primes $(5, 2 \pm \sqrt{-6})$ of norm $5$, since $-6 \equiv 2^2 \pmod 5$; and the two primes $(7, 1 \pm \sqrt{-6})$ of norm $7$, since $-6 \equiv 1 \pmod 7$. The primes of norm $7$ are principal, generated by $1 \pm \sqrt{-6}$, of norm $7$. The equation $a^2 + 6b^2 = 2$ has no solution, so $\mathfrak p_2$ is not principal. Next, $\sqrt{-6}$ lies in $\mathfrak p_2$ and $\mathfrak p_3$ and has norm $6$, so $\mathfrak p_2\mathfrak p_3 = (\sqrt{-6})$ and $[\mathfrak p_3] = [\mathfrak p_2]$. In the same way $2 + \sqrt{-6}$ has norm $10$ and lies in $\mathfrak p_2$ and in $(5, 2 + \sqrt{-6})$, so the class of $(5, 2 + \sqrt{-6})$ is $[\mathfrak p_2]$, and the conjugate prime is in the same class. So $\operatorname{Cl}(\mathbb{Z}[\sqrt{-6}])$ has order $2$ as well.

**Example (Class number one).** The imaginary quadratic fields $\mathbb{Q}(\sqrt{-d})$ with $d > 0$ squarefree and class number $1$ are those with $d = 1, 2, 3, 7, 11, 19, 43, 67, 163$. The list was proved complete by Heegner (1952), Baker (1966) and Stark (1967). The lattice bound proves class number $1$ for the first few by hand, as in Exercise 3.

### The library around it

The steps of the computation correspond to library lemmas: `ClassGroup.mk0_surjective` for "every class contains an integral ideal", the containment-divides lemma `Ideal.dvd_iff_le` of Chapter 4 for $\alpha A = IJ$, and `ClassGroup.mk0_eq_one_iff` for the principal test. The norm of ideals is in Volume 9. The general Minkowski bound, the finiteness of the class group of a number field and the class number are in Volume 12.

The index of this edition has no declaration for the class group of $\mathbb{Z}[\sqrt{-5}]$ itself. A formal version of this section would build $\mathbb{Z}[\sqrt{-5}]$ as the ring of integers of a quadratic field, compute the norms of the small primes, and run the case analysis on the norms of ideals.

Common errors of a learner:

- The lattice bound needs a nonzero element of $I$, which the pigeonhole principle supplies. The bound $6m^2 \le 6n$ uses $m^2 \le n$, which holds since $m = \lfloor \sqrt n \rfloor$.
- The list of ideals of norm at most $B$ must include products, not only primes.
- To show that two ideals are in the same class, find an element $\alpha$ with $IJ = (\alpha)$ and use $[I] = [J]^{-1}$; do not try to find a generator of $I$.

### Exercises

1. (A) Show that $\mathfrak q = (3, 1 + \sqrt{-5})$ is not principal by a norm argument.
2. (A) Find an element of $\mathfrak q^2$ that generates it, and conclude again that $[\mathfrak q]^2 = 1$.
3. (A) Use the lattice bound to show that $\mathbb{Z}[\sqrt{-2}]$ is a PID.
4. (B) Adapt the lattice bound to $\mathbb{Z}[\sqrt{-d}]$ with $d > 0$, and show that every class contains an ideal of norm at most $1 + d$.
5. (B) Show that $\mathbb{Z}[\sqrt{-3}]$ is not integrally closed, and that the argument of this section fails for it. Compute the norm bound for the ring of integers $\mathbb{Z}[\omega]$ with the basis $1, \omega$, and show that it is a PID.
6. (B) Find all the classes of ideals of norm $7$ and $29$ in $\mathbb{Z}[\sqrt{-5}]$.
7. (C) Show that $\operatorname{Cl}(\mathbb{Z}[\sqrt{-14}])$ is cyclic of order $4$, using a sharper bound or a longer list.

### Notes and history

The class number of quadratic forms of a given discriminant was studied by Gauss in the *Disquisitiones Arithmeticae* (1801), which contains the computations in this section in the language of binary quadratic forms: the two classes of $\mathbb{Z}[\sqrt{-5}]$ correspond to the forms $x^2 + 5y^2$ and $2x^2 + 2xy + 3y^2$. Minkowski's geometry of numbers (1896) gave the general bound that makes the class group computable for every number field.

### Reference

<?reference?>
