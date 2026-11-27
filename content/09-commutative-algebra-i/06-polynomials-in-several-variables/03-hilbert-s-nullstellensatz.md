---
title: Hilbert's Nullstellensatz
kind: theory
modules: []
explains:
  E3: [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton, MvPolynomial.IsPrime.vanishingIdeal_zeroLocus, finite_of_finite_type_of_isJacobsonRing]
  E2: [MvPolynomial.radical_le_vanishingIdeal_zeroLocus, MvPolynomial.mem_vanishingIdeal_singleton_iff, MvPolynomial.pointToPoint, MvPolynomial.vanishingIdeal_pointToPoint, MvPolynomial.pointToPoint_zeroLocus_le, IsJacobsonRing, isJacobsonRing_iff, MvPolynomial.isJacobsonRing, Ideal.radical_eq_jacobson]
  E1: [MvPolynomial.zeroLocus, MvPolynomial.vanishingIdeal, MvPolynomial.zeroLocus_bot, MvPolynomial.zeroLocus_top, MvPolynomial.vanishingIdeal_empty, MvPolynomial.aeval, MvPolynomial.comp_C_integral_of_surjective_of_isJacobsonRing, Ideal.radical, Ideal.jacobson, Ideal.IsMaximal, Ideal.exists_le_maximal, Ideal.IsPrime.radical, Ideal.Quotient.field, RingHom.ker_isMaximal_of_surjective, IsAlgClosed, Algebra.FiniteType, Module.Finite]
families: []
requires: [V06.C05, V09.C01, V09.C03, V09.C05]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Hilbert's Nullstellensatz

### Overview

Let $k$ be a field and $A = k[x_1, \dots, x_n]$, with the maps $V$ and $I$ of Section 2. The inclusion $\sqrt{J} \subseteq I(V(J))$ holds over every field. Over $\mathbb{R}$ it is strict: the ideal $(x^2 + 1)$ is proper, but $V(x^2 + 1)$ is empty. Hilbert's Nullstellensatz (theorem of zeros) says that over an algebraically closed field this is the only loss. A proper ideal has a common zero, the maximal ideals are the ideals of points, and $I(V(J)) = \sqrt{J}$.

The section proves the key algebraic step for uncountable fields such as $\mathbb{C}$, states it for all fields, and derives the three forms.

### Definitions

**Definition (Ideal of a point).** For $a = (a_1, \dots, a_n) \in k^n$ put $\mathfrak{m}_a = I(\{a\}) = \{ f \in A : f(a) = 0 \}$.

**Definition (Jacobson ring).** A commutative ring $R$ is a Jacobson ring if every radical ideal of $R$ is the intersection of the maximal ideals that contain it.

The Jacobson radical $\operatorname{Jac}(J)$ of Chapter 1, Section 2, is the intersection of the maximal ideals that contain $J$. So $R$ is a Jacobson ring exactly when $\operatorname{Jac}(J) = J$ for every radical ideal $J$. Fields and $\mathbb{Z}$ are Jacobson rings. A local domain that is not a field is not one, since $0$ is radical but is not the maximal ideal.

::: mathlib
`IsJacobsonRing` · `Mathlib.RingTheory.Jacobson.Ring`

The class `IsJacobsonRing R` has the field `I.IsRadical → I.jacobson = I`, and `isJacobsonRing_iff` states it as an equivalence. In a Jacobson ring, `Ideal.radical_eq_jacobson` gives `I.radical = I.jacobson` for every ideal. The instance `MvPolynomial.isJacobsonRing` says that `MvPolynomial σ R` is a Jacobson ring when `R` is one and `σ` is finite.

<?decl IsJacobsonRing?>
:::

### Theorems and proofs

**Lemma (Points give maximal ideals).** For $a \in k^n$, $\mathfrak{m}_a = (x_1 - a_1, \dots, x_n - a_n)$, and $\mathfrak{m}_a$ is a maximal ideal with $A/\mathfrak{m}_a \cong k$. For an ideal $J$, $a \in V(J)$ if and only if $J \subseteq \mathfrak{m}_a$.

*Proof.* The evaluation $\operatorname{ev}_a : A \to k$, $f \mapsto f(a)$, is a surjective ring map, since it sends the constant $c$ to $c$. Its kernel is $\mathfrak{m}_a$, so $A/\mathfrak{m}_a \cong k$ is a field and $\mathfrak{m}_a$ is maximal. Put $\mathfrak{n} = (x_1 - a_1, \dots, x_n - a_n)$. Then $\mathfrak{n} \subseteq \mathfrak{m}_a$. Modulo $\mathfrak{n}$ each $x_i$ is congruent to $a_i$, so each $f$ is congruent to $f(a)$. If $f(a) = 0$, then $f \in \mathfrak{n}$. The last claim is the definition of $V(J)$. $\square$

**Theorem (Zariski's lemma).** Let $k$ be a field and $L$ a field that is a finitely generated $k$-algebra. Then $L$ is a finite extension of $k$.

The proof in the general case uses integral extensions, the subject of Volume 10, Chapter 1. The case used below has a short proof.

**Proposition (Zariski's lemma for uncountable fields).** Let $k$ be an uncountable algebraically closed field and $\mathfrak{m}$ a maximal ideal of $A$. Then the map $k \to A/\mathfrak{m}$ is an isomorphism.

*Proof.* Put $L = A/\mathfrak{m}$, a field that contains $k$. The images of the monomials span $L$ over $k$, and there are countably many monomials. Suppose that $t \in L$ is not in $k$. If $t$ were algebraic over $k$, its minimal polynomial would be irreducible over the algebraically closed field $k$, so of degree $1$, and $t \in k$. So $t$ is transcendental over $k$, and $t - a \ne 0$ in $L$ for every $a \in k$.

The elements $1/(t - a)$, $a \in k$, are linearly independent over $k$. Suppose that $\sum_{i=1}^r c_i/(t - a_i) = 0$ with distinct $a_i$ and $c_i \in k$. Multiply by $\prod_j (t - a_j)$ to get $g(t) = 0$ with $g(T) = \sum_i c_i \prod_{j \ne i}(T - a_j) \in k[T]$. As $t$ is transcendental, $g = 0$ in $k[T]$. Evaluate at $T = a_i$: $c_i \prod_{j \ne i}(a_i - a_j) = 0$, so $c_i = 0$.

In a vector space spanned by a countable set, every linearly independent set is countable: it is no larger than a basis, which can be chosen inside the spanning set. This contradicts the uncountable independent set above. So $L = k$. $\square$

**Theorem (Weak Nullstellensatz).** Let $k$ be algebraically closed.

1. Every maximal ideal of $A$ is $\mathfrak{m}_a$ for exactly one $a \in k^n$.
2. If $J$ is a proper ideal of $A$, then $V(J) \ne \emptyset$.

*Proof.* (1) Let $\mathfrak{m}$ be maximal and $L = A/\mathfrak{m}$. By Zariski's lemma $L$ is finite over $k$, so each element of $L$ is algebraic over $k$ and, as in the proof above, lies in $k$. So $k \to L$ is an isomorphism. Choose $a_i \in k$ with $a_i \equiv x_i \bmod \mathfrak{m}$. Then $x_i - a_i \in \mathfrak{m}$, so $\mathfrak{m}_a \subseteq \mathfrak{m}$ by the lemma. As $\mathfrak{m}_a$ is maximal and $\mathfrak{m} \ne A$, $\mathfrak{m} = \mathfrak{m}_a$. If $\mathfrak{m}_a = \mathfrak{m}_b$, then $x_i - b_i \in \mathfrak{m}_a$, so $a_i - b_i = 0$.

(2) A proper ideal $J$ lies in a maximal ideal (Chapter 1), which is $\mathfrak{m}_a$ by (1). Then $a \in V(J)$ by the lemma. $\square$

**Theorem (Strong Nullstellensatz).** Let $k$ be algebraically closed and $J$ an ideal of $A$. Then $I(V(J)) = \sqrt{J}$.

*Proof.* Section 2 shows that $I(V(J))$ is a radical ideal that contains $J$, so it contains $\sqrt{J}$. Conversely, let $g \in I(V(J))$ with $g \ne 0$. In $B = k[x_1, \dots, x_n, y]$ let $J'$ be the ideal generated by $J$ and $1 - yg$. If $(a, b) \in V(J')$, then $a \in V(J)$, so $g(a) = 0$ and $1 - b\,g(a) = 1 \ne 0$, a contradiction. So $V(J') = \emptyset$, and $J' = B$ by the weak form in $n + 1$ variables. Thus
$$1 = \sum_{i=1}^s h_i f_i + h_0 (1 - yg)$$
with $f_i \in J$ and $h_i \in B$. Apply the $k$-algebra map $\varphi : B \to k(x_1, \dots, x_n)$ with $x_i \mapsto x_i$ and $y \mapsto 1/g$, which exists by the universal property of Section 1. It sends $1 - yg$ to $0$, so $1 = \sum_i h_i(x, 1/g) f_i$. Let $N$ be at least the degree in $y$ of every $h_i$. Then $g^N h_i(x, 1/g)$ lies in $A$, and $g^N = \sum_i g^N h_i(x, 1/g) f_i \in J$. So $g \in \sqrt{J}$. $\square$

**Corollary (Dictionary).** Let $k$ be algebraically closed.

1. $V$ and $I$ are inverse bijections between the radical ideals of $A$ and the algebraic sets in $k^n$, and both reverse inclusion.
2. For a prime ideal $P$, $I(V(P)) = P$.
3. $V(J) = \emptyset$ if and only if $1 \in J$.

*Proof.* (1) For a radical ideal $J$, $I(V(J)) = \sqrt{J} = J$. For an algebraic set $X = V(J)$, $V(I(X)) = X$ by rule 3 of Section 2. (2) A prime ideal is radical. (3) If $V(J) = \emptyset$, then $1 \in I(\emptyset) = \sqrt{J}$, so $1 \in J$. $\square$

::: mathlib
`MvPolynomial.vanishingIdeal_zeroLocus_eq_radical` · `Mathlib.RingTheory.Nullstellensatz`

For a field `k`, an algebraically closed extension `K` (`[IsAlgClosed K]`) and finite `σ`, `vanishingIdeal k (zeroLocus K I) = I.radical`. The points lie in `K^σ`, so the statement holds over $\mathbb{R}$ with complex points. The inclusion `radical_le_vanishingIdeal_zeroLocus` needs no hypothesis. `IsPrime.vanishingIdeal_zeroLocus` is part 2 of the corollary.

<?decl MvPolynomial.vanishingIdeal_zeroLocus_eq_radical?>
:::

::: mathlib
`MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton` · `Mathlib.RingTheory.Nullstellensatz`

For `I : Ideal (MvPolynomial σ K)` with `K` algebraically closed and `σ` finite, `I.IsMaximal ↔ ∃ x, I = vanishingIdeal K {x}`. This is part 1 of the weak form. The lemma `mem_vanishingIdeal_singleton_iff` says `p ∈ vanishingIdeal k {x} ↔ aeval x p = 0`.

<?decl MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton?>
:::

::: mathlib
`finite_of_finite_type_of_isJacobsonRing` · `Mathlib.RingTheory.Jacobson.Ring`

Zariski's lemma in a general form: for a Jacobson ring `R` and a field `S` that is a finitely generated `R`-algebra (`Algebra.FiniteType R S`), `S` is a finite `R`-module (`Module.Finite R S`). For `R = k` a field this is the theorem above.

<?decl finite_of_finite_type_of_isJacobsonRing?>
:::

### Examples

**Example (A point with a nonreduced ideal).** In $\mathbb{C}[x, y]$ let $J = (x^2, y)$. Then $V(J) = \{(0, 0)\}$ and $I(V(J)) = \mathfrak{m}_{(0,0)} = (x, y)$. So $\sqrt{J} = (x, y)$, as a direct check confirms. Here $J \ne \sqrt{J}$: put $y = 0$ in $x = x^2 p + y q$ to get $x = x^2 p(x, 0)$, which is false by degree.

**Example (Rabinowitsch's trick).** In $\mathbb{C}[x]$ take $J = (x^2)$ and $g = x$, which vanishes on $V(J) = \{0\}$. In $\mathbb{C}[x, y]$, $1 = y^2 \cdot x^2 + (1 + xy)(1 - xy)$. Put $y = 1/x$: $1 = x^{-2} \cdot x^2$. Multiply by $x^2$ to get $x^2 = 1 \cdot x^2 \in J$. 

**Counterexample (The field must be algebraically closed).** In $\mathbb{R}[x]$ the ideal $(x^2 + 1)$ is maximal, as $x^2 + 1$ is irreducible, and $V(x^2 + 1) = \emptyset$. So both parts of the weak form fail. In $\mathbb{R}[x, y]$, $V(x^2 + y^2) = \{(0, 0)\}$, so $I(V(x^2 + y^2)) = (x, y)$. But $x^2 + y^2$ is irreducible: a product of two factors of degree $1$ over $\mathbb{R}$ would vanish on a real line. So $(x^2 + y^2)$ is prime, hence radical, and differs from $(x, y)$. With complex points, as in Mathlib, $V(x^2 + y^2)$ is the lines $y = \pm i x$.

**Counterexample (The number of variables must be finite).** Let $k = \overline{\mathbb{Q}}$, which is countable, and let $B = k[t, x_a : a \in k]$. Let $J$ be the ideal generated by the elements $(t - a) x_a - 1$, $a \in k$. The $k$-algebra map $B \to k(t)$ with $t \mapsto t$ and $x_a \mapsto 1/(t - a)$ kills $J$, so $J$ is proper. A common zero would have $t = b \in k$, and then $(b - b) x_b - 1 = -1 \ne 0$. So $V(J) = \emptyset$.

### The library around it

The proof of `vanishingIdeal_zeroLocus_eq_radical` avoids Rabinowitsch's trick. As `MvPolynomial σ k` is a Jacobson ring, `Ideal.radical_eq_jacobson` writes $\sqrt{J}$ as the intersection of the maximal ideals over $J$, each the ideal of a point of $V(J)$. Behind both steps is the integrality statement `MvPolynomial.comp_C_integral_of_surjective_of_isJacobsonRing`.

`MvPolynomial.pointToPoint` sends a point to the prime ideal of `PrimeSpectrum (MvPolynomial σ k)` given by its vanishing ideal. With `vanishingIdeal_pointToPoint` and `pointToPoint_zeroLocus_le` it links the sets of this section to the Zariski topology of Chapter 2, Section 3.

The index of this edition has no declaration for the weak form as a separate statement about proper ideals. It follows from `vanishingIdeal_zeroLocus_eq_radical`, `zeroLocus_top` and `vanishingIdeal_empty`, as in part 3 of the corollary.

### Exercises

1. (A) In $\mathbb{C}[x, y]$ let $J = (x^2 y, x y^2)$. Find $V(J)$ and show that $\sqrt{J} = (xy)$. Hint: $(xy)^2 = y \cdot x^2 y$, and the union of the two axes has ideal $(xy)$.
2. (A) Show that $f_1, \dots, f_s \in \mathbb{C}[x_1, \dots, x_n]$ have no common zero if and only if $\sum_i h_i f_i = 1$ for some polynomials $h_i$.
3. (B) Let $k$ be a field that is not algebraically closed. Find a proper ideal of $k[x_1, \dots, x_n]$ with no zero in $k^n$. Hint: an irreducible polynomial in $x_1$ of degree at least $2$.
4. (B) Let $k$ be an uncountable field and $\mathfrak{m}$ a maximal ideal of $k[x_1, \dots, x_n]$. Show that every element of $A/\mathfrak{m}$ is algebraic over $k$. Hint: the independence argument of the proposition does not use that $k$ is algebraically closed.
5. (B) For ideals $J, J'$ of $\mathbb{C}[x_1, \dots, x_n]$ show that $I(V(J) \cap V(J')) = \sqrt{J + J'}$. Give an example where $J + J'$ is not radical. Hint: two curves in the plane that are tangent at a point.
6. (B) Let $X = V(J)$ in $\mathbb{C}^n$. Show that $a \mapsto \mathfrak{m}_a/J$ is a bijection from $X$ to the maximal ideals of $\mathbb{C}[x_1, \dots, x_n]/J$, and that the $\mathbb{C}$-algebra maps $\mathbb{C}[x_1, \dots, x_n]/J \to \mathbb{C}$ correspond to the points of $X$.
7. (C) Show that $\mathbb{C}[x_1, \dots, x_n]$ is a Jacobson ring, and that every prime ideal $P$ of it is the intersection of the ideals $\mathfrak{m}_a$ with $a \in V(P)$. Hint: $P = I(V(P)) = \bigcap_{a \in V(P)} \mathfrak{m}_a$.

### Notes and history

Hilbert proved the Nullstellensatz in 1893, in his paper on invariant theory. Rabinowitsch published the trick with the extra variable in 1929. Zariski proved his lemma in 1947. Jacobson rings are named after Nathan Jacobson.

### Reference

<?reference?>
