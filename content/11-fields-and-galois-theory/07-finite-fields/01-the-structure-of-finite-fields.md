---
title: The structure of finite fields
kind: theory
modules:
  - Mathlib.FieldTheory.Finite.Basic
  - Mathlib.FieldTheory.Finite.Polynomial
  - Mathlib.FieldTheory.ChevalleyWarning
  - Mathlib.FieldTheory.Finite.Valuation
  - Mathlib.FieldTheory.AxGrothendieck
explains:
  E3: [FiniteField.card, FiniteField.pow_card, FiniteField.sum_pow_units, char_dvd_card_solutions_of_sum_lt, ax_grothendieck_univ]
  E2: [FiniteField.isPrimePow_card, FiniteField.pow_card_sub_one_eq_one, FiniteField.roots_X_pow_card_sub_X, FiniteField.sum_pow_lt_card_sub_one, FiniteField.prod_univ_units_id_eq_neg_one, FiniteField.isSquare_iff, FiniteField.exists_nonsquare, FiniteField.odd_card_of_char_ne_two, ZMod.sq_add_sq, FiniteField.exists_root_sum_quadratic, MvPolynomial.sum_eval_eq_zero, char_dvd_card_solutions, ax_grothendieck_of_locally_finite, FiniteField.valuation_algebraMap_eq_one]
  E1: auto
families: []
requires: [V06.C04, V06.C05, V07.C02, V11.C01]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The structure of finite fields

### Overview

A finite field $F$ has a prime characteristic $p$, so it contains the prime field $\mathbb{F}_p = \mathbb{Z}/p$, and it is a finite dimensional vector space over $\mathbb{F}_p$. So $|F| = p^n$. This section derives the rest of the structure of one finite field from two facts: the group $F^\times$ is cyclic (Volume 6, Chapter 5), and it has $q - 1$ elements, where $q = |F|$. From these come the identity $x^q = x$, the factorization of $X^q - X$ and the sums $\sum_{x \in F} x^k$.

The sums of powers give the theorem of Chevalley and Warning: a system of polynomial equations over $F$ with few degrees compared with the number of variables has a number of solutions divisible by $p$. The section also counts the squares in $F$ and proves the theorem of Wilson in the form $\prod_{x \in F^\times} x = -1$.

The section uses the characteristic (Volume 6, Chapter 4), the cyclic group of units (Volume 6, Chapter 5), dimension (Volume 7, Chapter 2), and the language of extensions (Chapter 1).

### Definitions

**Definition (Finite field, $q$).** A finite field is a field with finitely many elements. Here $q = |F|$, and $\mathbb{F}_q$ names a field with $q$ elements, unique by Section 2.

::: mathlib
`FiniteField.card` · `Mathlib.FieldTheory.Finite.Basic`

The statement: for `[Field K] [Fintype K] [CharP K p]`, there is `n : ℕ+` with `Nat.Prime p` and `Fintype.card K = p ^ n`. The exponent has type `ℕ+`, so $n \geq 1$. `FiniteField.isPrimePow_card` is the form without the characteristic.

<?decl FiniteField.card?>
:::

**Definition (Square).** An element $a \in F$ is a square if $a = b^2$ for some $b \in F$.

### Theorems and proofs

**Theorem (Size).** A finite field $F$ has $p^n$ elements, where $p$ is its characteristic and $n = [F : \mathbb{F}_p] \geq 1$.

*Proof.* The characteristic of a finite domain is a prime $p$ (Volume 6, Chapter 4), so the image of $\mathbb{Z} \to F$ is a field $\mathbb{F}_p$ with $p$ elements. Then $F$ is a vector space over $\mathbb{F}_p$, of finite dimension $n$ since $F$ is finite. A basis gives a bijection $\mathbb{F}_p^n \to F$, so $|F| = p^n$. $\square$

**Theorem (Fermat's identity).** Let $|F| = q$. Then $a^{q-1} = 1$ for each $a \in F^\times$, and $a^q = a$ for each $a \in F$. In $F[X]$,
$$X^q - X = \prod_{a \in F} (X - a).$$

*Proof.* The group $F^\times$ has order $q - 1$, so by Lagrange $a^{q-1} = 1$ for $a \neq 0$. So $a^q = a$ for all $a \in F$, also for $a = 0$. The monic polynomial $X^q - X$ of degree $q$ has the $q$ distinct roots $a \in F$, so by the factor theorem it is $\prod_a (X - a)$. $\square$

::: mathlib
`FiniteField.pow_card` · `Mathlib.FieldTheory.Finite.Basic`

The identity `a ^ Fintype.card K = a`, stated for a finite group with zero. The version for units is `FiniteField.pow_card_sub_one_eq_one`, and the factorization is `FiniteField.roots_X_pow_card_sub_X`: the multiset of the roots of $X^q - X$ is the whole field. Volume 6 uses the special case `ZMod.pow_card` for $\mathbb{F}_p$.

<?decl FiniteField.pow_card?>
:::

So $F$ is a splitting field of $X^q - X$ over $\mathbb{F}_p$, the starting point of Section 2. Comparing constant terms in $X^{q-1} - 1 = \prod_{a \in F^\times} (X - a)$ gives $\prod_{a \in F^\times} a = -1$, since $(-1)^{q-1} = 1$ when $q$ is odd and $-1 = 1$ when $q$ is even. For $F = \mathbb{F}_p$ this is Wilson's theorem, $(p-1)! \equiv -1 \pmod p$.

**Theorem (Sums of powers).** Let $|F| = q$ and $k \geq 0$, with the convention $0^0 = 1$. Then
$$\sum_{x \in F} x^k = \begin{cases} -1 & \text{if } k \geq 1 \text{ and } (q-1) \mid k, \\ 0 & \text{otherwise.} \end{cases}$$

*Proof.* For $k = 0$ the sum is $q \cdot 1 = 0$ in $F$. Let $k \geq 1$, so $0^k = 0$ and the sum runs over $F^\times$. If $(q - 1) \mid k$, each $x^k = 1$ and the sum is $q - 1 = -1$. Otherwise let $g$ generate the cyclic group $F^\times$. Then $g^k \neq 1$, and $x \mapsto gx$ permutes $F^\times$, so $S = \sum_{x \in F^\times} x^k$ satisfies $g^k S = \sum_x (gx)^k = S$. So $(g^k - 1) S = 0$ and $S = 0$. $\square$

In particular $\sum_{x \in F} x^k = 0$ for $0 \leq k < q - 1$.

::: mathlib
`FiniteField.sum_pow_units` · `Mathlib.FieldTheory.Finite.Basic`

The statement `∑ x : Kˣ, (x : K) ^ i = if Fintype.card K - 1 ∣ i then -1 else 0`, over the units. The sum over all of `K` for `i < q - 1` is `FiniteField.sum_pow_lt_card_sub_one`.

<?decl FiniteField.sum_pow_units?>
:::

**Theorem (Chevalley and Warning).** Let $F$ be a finite field of characteristic $p$ with $q$ elements, and let $f_1, \dots, f_r \in F[x_1, \dots, x_n]$ with $\sum_i \deg f_i < n$. Then the number $N$ of common zeros of $f_1, \dots, f_r$ in $F^n$ is divisible by $p$.

*Proof.* Put $P = \prod_{i=1}^r (1 - f_i^{q-1})$. For $x \in F^n$, each $f_i(x)^{q-1}$ is $0$ if $f_i(x) = 0$ and $1$ otherwise. So $P(x) = 1$ if $x$ is a common zero and $P(x) = 0$ otherwise. Hence $N \cdot 1 = \sum_{x \in F^n} P(x)$ in $F$.

The degree of $P$ is at most $(q-1) \sum_i \deg f_i < (q - 1) n$. So $P$ is a linear combination of monomials $x_1^{a_1} \cdots x_n^{a_n}$ with $a_1 + \dots + a_n < (q-1)n$, each with some $a_j < q - 1$. For this monomial
$$\sum_{x \in F^n} x_1^{a_1} \cdots x_n^{a_n} = \prod_{i=1}^n \Big( \sum_{t \in F} t^{a_i} \Big),$$
and the factor with $i = j$ is $0$ by the theorem on sums of powers. So $\sum_x P(x) = 0$, and $N \cdot 1 = 0$ in $F$, that is, $p \mid N$. $\square$

**Corollary (Quadratic forms).** Each quadratic form in $n \geq 3$ variables over a finite field has a zero other than $0$.

*Proof.* The form $Q$ has degree $2 < n$, so the number of its zeros is divisible by $p$. The zero $0$ is one of them, so there are at least $p \geq 2$. $\square$

::: mathlib
`char_dvd_card_solutions_of_sum_lt` · `Mathlib.FieldTheory.ChevalleyWarning`

The statement for a finite family `f : ι → MvPolynomial σ K` with `∑ i ∈ s, (f i).totalDegree < Fintype.card σ`: the characteristic `p` divides the number of common zeros. The one polynomial version is `char_dvd_card_solutions`, and the lemma on sums is `MvPolynomial.sum_eval_eq_zero`: the sum of a polynomial over $K^\sigma$ is zero when its total degree is less than $(q-1)|\sigma|$.

<?decl char_dvd_card_solutions_of_sum_lt?>
:::

**Theorem (Squares).** Let $F$ be a finite field with $q$ elements. If $q$ is even, each element of $F$ is a square. If $q$ is odd, exactly $(q-1)/2$ elements of $F^\times$ are squares, and $a \in F^\times$ is a square if and only if $a^{(q-1)/2} = 1$. In both cases each element of $F$ is a sum of two squares.

*Proof.* If $q$ is even, the characteristic is $2$, and $x \mapsto x^2$ is the Frobenius map, which is injective, so bijective on the finite set $F$. Let $q$ be odd and $g$ a generator of $F^\times$. The squares in $F^\times$ are the $g^{2k}$, a subgroup of index $2$, so there are $(q-1)/2$ of them. An element $a = g^m$ satisfies $a^{(q-1)/2} = g^{m(q-1)/2} = 1$ if and only if $(q - 1) \mid m(q-1)/2$, if and only if $m$ is even.

For the sums: with $0$, there are $(q+1)/2$ squares in $F$. Let $c \in F$. The sets $\{a^2\}$ and $\{c - b^2\}$ each have $(q+1)/2 > q/2$ elements, so they meet. $\square$

::: mathlib
`FiniteField.isSquare_iff` · `Mathlib.FieldTheory.Finite.Basic`

The criterion of Euler, `IsSquare a ↔ a ^ (Fintype.card F / 2) = 1` for `a ≠ 0` in odd characteristic, with `q / 2 = (q-1)/2` as natural numbers since $q$ is odd (`FiniteField.odd_card_of_char_ne_two`). The existence of a nonsquare is `FiniteField.exists_nonsquare`, and the sums of two squares are `ZMod.sq_add_sq` for $\mathbb{F}_p$ and, more generally, `FiniteField.exists_root_sum_quadratic`.

<?decl FiniteField.isSquare_iff?>
:::

**Theorem (Ax and Grothendieck).** Let $K$ be an algebraically closed field and $P : K^n \to K^n$ a map given by polynomials. If $P$ is injective, it is surjective.

For the algebraic closure $K$ of a finite field the proof is short: the finitely many coefficients of $P$ and the coordinates of a point $y$ lie in a finite subfield $F \subseteq K$, by Section 2. The map $P$ sends the finite set $F^n$ into itself injectively, so bijectively, and $y$ has a preimage. The general case follows by model theory, which this section does not give.

::: mathlib
`ax_grothendieck_univ` · `Mathlib.FieldTheory.AxGrothendieck`

The statement for `[IsAlgClosed K]` and a finite index type `ι`: if `fun v i ↦ eval v (p i)` is injective, it is surjective. The case of a locally finite ring is `ax_grothendieck_of_locally_finite`. The general proof uses the model theory of `Mathlib.ModelTheory`.

<?decl ax_grothendieck_univ?>
:::

### Examples

**Example (The field with nine elements).** The polynomial $X^2 + 1$ has no root in $\mathbb{F}_3$, since $0^2 + 1, 1^2 + 1, 2^2 + 1 = 1, 2, 2$, so it is irreducible, and $F = \mathbb{F}_3[X]/(X^2 + 1) = \{a + bi : a, b \in \mathbb{F}_3\}$ with $i^2 = -1$ is a field with $9$ elements. The element $i$ has order $4$, but $g = 1 + i$ generates $F^\times$: $g^2 = 1 + 2i + i^2 = 2i$, and $g^4 = (2i)^2 = 4i^2 = -4 = -1$, so $g$ has order $8$. The squares in $F^\times$ are $g^0, g^2, g^4, g^6 = 1, 2i, 2, i$, four elements, as the theorem says, and $2 = -1$ is a square in $\mathbb{F}_9$ although it is not one in $\mathbb{F}_3$.

**Example (The degree bound is needed).** Over $\mathbb{F}_3$, the polynomial $f = x^2 + y^2$ in $n = 2$ variables has degree $2$, which is not less than $n$. Its only zero is $(0, 0)$, since $-1$ is not a square in $\mathbb{F}_3$, so $N = 1$ is not divisible by $3$. So the hypothesis $\sum \deg f_i < n$ in the theorem of Chevalley and Warning is needed. With a third variable, $x^2 + y^2 + z^2$ has $N = 9$ zeros in $\mathbb{F}_3^3$: $(0,0,0)$ and the $8$ points with all three coordinates in $\{\pm 1\}$, since $1 + 1 + 1 = 0$.

**Example (Wilson's theorem).** In $\mathbb{F}_7$, the elements of $\mathbb{F}_7^\times$ pair up with their inverses: $2 \cdot 4 = 1$, $3 \cdot 5 = 1$, and $1, 6$ are their own inverses. So $\prod_{x \neq 0} x = 1 \cdot 6 = -1$, and $6! = 720 = 103 \cdot 7 - 1$.

::: mathlib
`ZMod.wilsons_lemma` · `Mathlib.NumberTheory.Wilson`

The statement `((p - 1)! : ZMod p) = -1`. The form for all finite fields, and more generally for a domain whose group of units is finite, is `FiniteField.prod_univ_units_id_eq_neg_one`.

<?decl ZMod.wilsons_lemma?>
:::

### The library around it

The file `Mathlib.FieldTheory.Finite.Basic` holds the results of this section and the Frobenius automorphisms of Section 2. The file `Mathlib.FieldTheory.Finite.Polynomial` studies the functions $F^n \to F$ given by polynomials, each given by a unique polynomial of degree less than $q$ in each variable. The file `Mathlib.FieldTheory.Finite.Valuation` proves that each valuation is trivial on a finite field, `FiniteField.valuation_algebraMap_eq_one`. The reference table lists the declarations of the section.

### Exercises

1. (A) Find a generator of $\mathbb{F}_{11}^\times$ and the squares in $\mathbb{F}_{11}$.
2. (A) Show that $-1$ is a square in $\mathbb{F}_q$, $q$ odd, if and only if $q \equiv 1 \pmod 4$.
3. (A) Show that $X^4 + 1$ is reducible over each $\mathbb{F}_p$. Hint: one of $-1$, $2$, $-2$ is a square in $\mathbb{F}_p$.
4. (B) Show that each function $F^n \to F$ is given by a polynomial in $x_1, \dots, x_n$ of degree less than $q$ in each variable. Hint: use $1 - (x - a)^{q-1}$.
5. (B) Let $f \in \mathbb{F}_q[x_1, \dots, x_n]$ have degree $d < n$ and no constant term. Show that $f$ has a zero other than $0$.
6. (B) Show that the number of solutions of $x^2 + y^2 = 1$ in $\mathbb{F}_q$, $q$ odd, is $q - 1$ or $q + 1$. Hint: parametrize the circle by lines through $(-1, 0)$.
7. (C) Prove the theorem of Erdős, Ginzburg and Ziv for a prime $p$: among $2p - 1$ integers, some $p$ have a sum divisible by $p$. Hint: apply Chevalley and Warning to $\sum_i a_i x_i^{p-1}$ and $\sum_i x_i^{p-1}$ over $\mathbb{F}_p$, in $2p - 1$ variables.

### Notes and history

Fermat stated the identity $a^p \equiv a \pmod p$ in 1640, and Euler proved it. Galois introduced finite fields beyond $\mathbb{F}_p$ in 1830, so they are also called Galois fields. Chevalley proved his theorem in 1935, as a conjecture of Artin, and Warning strengthened it to the divisibility by $p$ in the same year. Ax proved the theorem on polynomial maps in 1968, and Grothendieck gave another proof.

### Reference

<?reference?>
