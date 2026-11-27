---
title: The ring of integers modulo n
kind: theory
modules:
  - Mathlib.Algebra.Field.ZMod
explains:
  E3: [ZMod.instField]
  E2: [ZMod.instIsDomain]
  E1: auto
families: []
requires: [V06.C02, V06.C03, V02.C06]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The ring of integers modulo n

### Overview

Volume 2, Chapter 6 built $\mathbb{Z}/n$ from residues, found its units by Bézout's identity, and proved the theorems of Euler, Fermat and Wilson by counting in the group of units. This section looks at the same ring with the tools of this volume: ideals, quotients, homomorphisms and the characteristic. The ring $\mathbb{Z}/n$ is the quotient $\mathbb{Z}/n\mathbb{Z}$, the universal ring of characteristic dividing $n$. Its ideals are the divisors of $n$. It is a field exactly when it is a domain, exactly when $n$ is prime, exactly when $n \mathbb{Z}$ is a maximal ideal. The Chinese remainder theorem splits it into a product of rings $\mathbb{Z}/p^k$, and the splitting computes its units, its nilpotents and its idempotents. Fermat's theorem returns as a property of the Frobenius.

### Definitions

**Definition (The integers modulo $n$).** For $n \in \mathbb{N}$, the ring $\mathbb{Z}/n$ is the quotient ring $\mathbb{Z}/n\mathbb{Z}$ of $\mathbb{Z}$ by the ideal $n\mathbb{Z}$ (Chapter 2). The class of $a \in \mathbb{Z}$ is written $[a]$, or $a$ when the ring is clear.

For $n \ge 1$ the classes $[0], [1], \dots, [n - 1]$ are the distinct elements, so $|\mathbb{Z}/n| = n$. For $n = 0$ the ideal is $0$ and $\mathbb{Z}/0 = \mathbb{Z}$. For $n = 1$ the ideal is $\mathbb{Z}$ and $\mathbb{Z}/1$ is the zero ring.

**Definition (Maximal ideal).** An ideal $I$ of a commutative ring $R$ is *maximal* if $I \ne R$ and no ideal $J$ satisfies $I \subsetneq J \subsetneq R$. It is *prime* if $I \ne R$ and $a b \in I$ implies $a \in I$ or $b \in I$.

Chapter 2 proves that $R/I$ is a field if and only if $I$ is maximal, and a domain if and only if $I$ is prime. This section uses only the special case $R = \mathbb{Z}$, which it proves directly.

::: mathlib
`ZMod` · `Mathlib.Data.ZMod.Defs`

Mathlib does not define `ZMod n` as a quotient. It defines `ZMod 0 = ℤ` and `ZMod (n + 1) = Fin (n + 1)`, by cases on `n`, so that elements are computable and `decide` works on small cases. The isomorphism with the quotient ring is `Int.quotientSpanEquivZMod`, of Volume 2. The ring structure is `ZMod.commRing`.

<?decl ZMod?>
:::

### Theorems and proofs

**Theorem (Universal property).** Let $n \in \mathbb{N}$ and let $R$ be a ring. There is a ring homomorphism $\mathbb{Z}/n \to R$ if and only if $\operatorname{char} R$ divides $n$. In that case there is exactly one, $[a] \mapsto a \cdot 1$.

*Proof.* Let $\chi : \mathbb{Z} \to R$ be the unique homomorphism, with kernel $c \mathbb{Z}$, $c = \operatorname{char} R$ (Section 1). Let $\pi : \mathbb{Z} \to \mathbb{Z}/n$ be the quotient map.

If $\varphi : \mathbb{Z}/n \to R$ is a homomorphism, then $\varphi \circ \pi$ is a homomorphism $\mathbb{Z} \to R$, so it is $\chi$. Then $\chi(n) = \varphi([n]) = \varphi(0) = 0$, so $c \mid n$. Since $\pi$ is surjective, $\varphi$ is determined by $\varphi \circ \pi = \chi$, so $\varphi([a]) = a \cdot 1$ and $\varphi$ is unique.

Conversely, if $c \mid n$, then $n\mathbb{Z} \subseteq c\mathbb{Z} = \ker \chi$. By the factor theorem for quotients (Chapter 2), $\chi$ factors through $\pi$: the map $[a] \mapsto \chi(a)$ is well defined and a ring homomorphism. $\square$

Two consequences follow. A ring of characteristic $n$ contains a copy of $\mathbb{Z}/n$, by the first isomorphism theorem applied to $\chi$. And for $d \mid n$, there is a unique homomorphism $\mathbb{Z}/n \to \mathbb{Z}/d$, the reduction $[a]_n \mapsto [a]_d$.

**Theorem (Ideals of $\mathbb{Z}/n$).** Let $n \ge 1$. The ideals of $\mathbb{Z}/n$ are the sets $d \cdot (\mathbb{Z}/n) = \{[d a] : a \in \mathbb{Z}\}$ for the positive divisors $d$ of $n$, and different divisors give different ideals. The quotient by $d \cdot (\mathbb{Z}/n)$ is isomorphic to $\mathbb{Z}/d$.

*Proof.* By the correspondence theorem (Chapter 2), the ideals of $\mathbb{Z}/n\mathbb{Z}$ are the images $\pi(J)$ of the ideals $J$ of $\mathbb{Z}$ with $n\mathbb{Z} \subseteq J$, and $J \mapsto \pi(J)$ is a bijection. Each ideal of $\mathbb{Z}$ is $d\mathbb{Z}$ for one $d \ge 0$, and $n\mathbb{Z} \subseteq d\mathbb{Z}$ means $d \mid n$, which forces $d \ge 1$. The image of $d\mathbb{Z}$ is $d \cdot (\mathbb{Z}/n)$. By the third isomorphism theorem, $(\mathbb{Z}/n\mathbb{Z}) / (d\mathbb{Z}/n\mathbb{Z}) \cong \mathbb{Z}/d\mathbb{Z}$. $\square$

For example, $\mathbb{Z}/12$ has exactly six ideals, one for each of $1, 2, 3, 4, 6, 12$. The ideal for $d = 4$ is $\{0, 4, 8\}$ and the ideal for $d = 12$ is $\{0\}$.

**Theorem (When $\mathbb{Z}/n$ is a field).** For $n \ge 2$ the following are equivalent:

1. $n$ is prime;
2. $n\mathbb{Z}$ is a prime ideal of $\mathbb{Z}$, so $\mathbb{Z}/n$ is a domain;
3. $n\mathbb{Z}$ is a maximal ideal of $\mathbb{Z}$, so $\mathbb{Z}/n$ is a field.

*Proof.* (1 ⇒ 2) Let $n = p$ be prime and $[a][b] = 0$, that is, $p \mid ab$. By Euclid's lemma (Volume 2, Chapter 2), $p \mid a$ or $p \mid b$, so $[a] = 0$ or $[b] = 0$. Also $[1] \ne [0]$ since $p > 1$. So $\mathbb{Z}/p$ is a domain.

(2 ⇒ 3) $\mathbb{Z}/n$ is a finite domain, so it is a field by the theorem of Chapter 3.

(3 ⇒ 1) A field has no zero divisors. If $n = ab$ with $1 < a, b < n$, then $[a][b] = [n] = 0$ with $[a] \ne 0 \ne [b]$, a contradiction. So $n$ is prime.

The ideal statements follow from the ideal theorem: the ideals of $\mathbb{Z}$ that contain $p\mathbb{Z}$ are $d\mathbb{Z}$ with $d \mid p$, so $d = 1$ or $d = p$, and $p\mathbb{Z}$ is maximal. A field has only the ideals $0$ and itself, so $\mathbb{Z}/n$ a field gives only the divisors $1$ and $n$ of $n$, and $n$ is prime. $\square$

The proof does not use Bézout's identity. The inverse that it produces is not explicit: it comes from the injectivity of $x \mapsto [a] x$ on a finite set. Bézout gives the inverse as a formula, as in Volume 2, and the extended Euclidean algorithm computes it.

::: mathlib
`ZMod.instField` · `Mathlib.Algebra.Field.ZMod`

The instance `Field (ZMod p)` under the hypothesis `[Fact (Nat.Prime p)]`. The primality is a `Fact` because an instance cannot take a proof as an ordinary argument that Lean would have to find. For a concrete prime, declare `instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩`. In a proof with `hp : p.Prime`, write `haveI := Fact.mk hp`. The inverse in the field is the function `ZMod.inv` of Volume 2, which uses the extended gcd.

<?decl ZMod.instField?>
:::

::: mathlib
`ZMod.instIsDomain` · `Mathlib.Algebra.Field.ZMod`

The instance `IsDomain (ZMod p)` for `[Fact (Nat.Prime p)]`. It follows from the field instance, and it is stated separately so that instance search finds it at once.

<?decl ZMod.instIsDomain?>
:::

**Theorem (Chinese remainder theorem).** Let $m, n \ge 1$ be coprime. The map
$$\psi : \mathbb{Z}/mn \to \mathbb{Z}/m \times \mathbb{Z}/n, \qquad [a]_{mn} \mapsto ([a]_m, [a]_n),$$
is a ring isomorphism. If $mu + nv = 1$, its inverse is $([a]_m, [b]_n) \mapsto [a n v + b m u]_{mn}$.

*Proof.* The map $\mathbb{Z} \to \mathbb{Z}/m \times \mathbb{Z}/n$, $a \mapsto ([a]_m, [a]_n)$, is a ring homomorphism, since each component is. Its kernel is $m\mathbb{Z} \cap n\mathbb{Z}$, the multiples of $\operatorname{lcm}(m, n) = mn$. So by the first isomorphism theorem it induces an injective homomorphism $\psi$ on $\mathbb{Z}/mn$. Both sides have $mn$ elements, so $\psi$ is bijective.

For the formula, put $e_1 = nv$ and $e_2 = mu$. Then $e_1 = 1 - mu \equiv 1 \pmod m$ and $e_1 \equiv 0 \pmod n$. In the same way $e_2 \equiv 0 \pmod m$ and $e_2 \equiv 1 \pmod n$. So $a e_1 + b e_2 \equiv a \pmod m$ and $\equiv b \pmod n$. $\square$

The elements $\varepsilon_1 = [e_1]$ and $\varepsilon_2 = [e_2]$ of $\mathbb{Z}/mn$ correspond to $(1, 0)$ and $(0, 1)$. So they are idempotents, $\varepsilon_i^2 = \varepsilon_i$, with $\varepsilon_1 + \varepsilon_2 = 1$ and $\varepsilon_1 \varepsilon_2 = 0$. A decomposition of a ring as a product is the same as such a pair of idempotents.

::: mathlib
`ZMod.chineseRemainder` · `Mathlib.Data.ZMod.Basic`

The isomorphism `ZMod (m * n) ≃+* ZMod m × ZMod n` from `h : m.Coprime n`. For a family of pairwise coprime moduli, the version for ideals of a general commutative ring is `Ideal.quotientInfRingEquivPiQuotient` of Volume 9.

<?decl ZMod.chineseRemainder?>
:::

**Corollary (Decomposition into prime powers).** If $n = p_1^{k_1} \cdots p_r^{k_r}$ with distinct primes $p_i$, then
$$\mathbb{Z}/n \cong \mathbb{Z}/p_1^{k_1} \times \cdots \times \mathbb{Z}/p_r^{k_r},$$
and $(\mathbb{Z}/n)^\times \cong \prod_i (\mathbb{Z}/p_i^{k_i})^\times$. So $\varphi(n) = \prod_i p_i^{k_i - 1}(p_i - 1)$.

*Proof.* Induction on $r$, with the theorem applied to $p_1^{k_1}$ and $p_2^{k_2} \cdots p_r^{k_r}$, which are coprime. A ring isomorphism maps units to units, and the units of a product are the pairs of units (Chapter 3). In $\mathbb{Z}/p^k$, the class $[a]$ is a unit if and only if $p \nmid a$ (Volume 2), and there are $p^k - p^{k-1}$ such classes. $\square$

**Theorem (Nilpotents of $\mathbb{Z}/n$).** Let $n \ge 1$ and let $\operatorname{rad}(n)$ be the product of the distinct primes dividing $n$. Then $[a]$ is nilpotent in $\mathbb{Z}/n$ if and only if $\operatorname{rad}(n) \mid a$. So $\mathbb{Z}/n$ has no nonzero nilpotents if and only if $n$ is squarefree.

*Proof.* If $[a]^k = 0$, then $n \mid a^k$, so each prime $p \mid n$ divides $a^k$ and, by Euclid's lemma, $a$. Hence $\operatorname{rad}(n) \mid a$. Conversely, if $\operatorname{rad}(n) \mid a$ and $k$ is the largest exponent in $n$, then $n \mid \operatorname{rad}(n)^k \mid a^k$, so $[a]^k = 0$. The last claim: $\operatorname{rad}(n) = n$ exactly when $n$ is squarefree, and then only $[0]$ is nilpotent. $\square$

**Theorem (Fermat, by the Frobenius).** Let $p$ be prime. Then $a^p = a$ for each $a \in \mathbb{Z}/p$, and $a^{p-1} = 1$ for each $a \ne 0$.

*Proof.* The ring $\mathbb{Z}/p$ is commutative of characteristic $p$, so the Frobenius $F(a) = a^p$ is a ring homomorphism (Section 1). The identity is also a ring homomorphism $\mathbb{Z}/p \to \mathbb{Z}/p$. By the universal property there is only one, so $F$ is the identity. For $a \ne 0$, cancel $a$ in $a^p = a$, since $\mathbb{Z}/p$ is a domain. $\square$

The same argument proves more: in each commutative ring of characteristic $p$, the Frobenius fixes the elements of the prime field. Volume 2 proved Fermat's theorem from Lagrange's theorem on the group of units. The present proof uses only the binomial theorem.

::: mathlib
`ZMod.pow_card` · `Mathlib.FieldTheory.Finite.Basic`

The identity `x ^ p = x` for `x : ZMod p` and `[Fact (Nat.Prime p)]`. The form for nonzero `x` is `ZMod.pow_card_sub_one_eq_one`, and Euler's form `ZMod.pow_totient` is in the same file of Volume 11. Wilson's theorem `ZMod.wilsons_lemma` is in Volume 12, and Volume 2 proves it.

<?decl ZMod.pow_card?>
:::

### Examples

**Example (An inverse in $\mathbb{Z}/31$).** The field $\mathbb{Z}/31$ has an inverse for $[7]$. The Euclidean algorithm gives $31 = 4 \cdot 7 + 3$ and $7 = 2 \cdot 3 + 1$, so $1 = 7 - 2 \cdot 3 = 7 - 2(31 - 4 \cdot 7) = 9 \cdot 7 - 2 \cdot 31$. So $[7]^{-1} = [9]$. Check: $7 \cdot 9 = 63 = 2 \cdot 31 + 1$. Fermat gives the same answer as $[7]^{29}$, which is slower to compute by hand.

**Example (A system of congruences).** Solve $x \equiv 2 \pmod 3$ and $x \equiv 3 \pmod 5$. Here $3 \cdot 2 + 5 \cdot (-1) = 1$, so $u = 2$, $v = -1$, $e_1 = 5 \cdot (-1) = -5 \equiv 10$ and $e_2 = 3 \cdot 2 = 6$ in $\mathbb{Z}/15$. Then $x = 2 \cdot 10 + 3 \cdot 6 = 38 \equiv 8 \pmod{15}$. Check: $8 = 2 \cdot 3 + 2$ and $8 = 5 + 3$. The idempotents are $10^2 = 100 = 6 \cdot 15 + 10$ and $6^2 = 36 = 2 \cdot 15 + 6$, with $10 + 6 = 16 \equiv 1$ and $10 \cdot 6 = 60 \equiv 0$.

**Example (The structure of $\mathbb{Z}/12$).** $\mathbb{Z}/12 \cong \mathbb{Z}/4 \times \mathbb{Z}/3$. The idempotents are $0, 1, 4, 9$: indeed $4^2 = 16 \equiv 4$ and $9^2 = 81 = 6 \cdot 12 + 9$, and $4 + 9 = 13 \equiv 1$. They correspond to $(0, 0)$, $(1, 1)$, $(0, 1)$ and $(1, 0)$. The units are the pairs of units, $\{1, 3\} \times \{1, 2\}$, which are the classes $1, 5, 7, 11$, and each squares to $1$: $25 = 24 + 1$, $49 = 48 + 1$, $121 = 120 + 1$. So $(\mathbb{Z}/12)^\times$ is the Klein four group $\mathbb{Z}/2 \times \mathbb{Z}/2$, not the cyclic group of order $4$. The nilpotents are the multiples of $\operatorname{rad}(12) = 6$, namely $0$ and $6$, with $6^2 = 36 \equiv 0$.

**Example (Square roots of $-1$).** In the field $\mathbb{Z}/13$, $5^2 = 25 = 26 - 1 = -1$, so $X^2 + 1 = (X - 5)(X + 5)$ and the roots are $5$ and $8$. A polynomial of degree $2$ over a field has at most $2$ roots (Chapter 5), so there are no others. In $\mathbb{Z}/5$ the roots are $2$ and $3$. In $\mathbb{Z}/65 \cong \mathbb{Z}/5 \times \mathbb{Z}/13$ the equation $x^2 = -1$ has $2 \cdot 2 = 4$ roots, one for each pair of signs. Solving $x \equiv 2 \pmod 5$ and $x \equiv 5 \pmod{13}$ gives $x = 57$, and $x \equiv 2 \pmod 5$, $x \equiv 8 \pmod{13}$ gives $x = 47$. The four roots are $8, 18, 47, 57$. Check: $8^2 = 64 = 65 - 1$ and $18^2 = 324 = 5 \cdot 65 - 1$.

**Counterexample (The coprimality in the Chinese remainder theorem).** $\mathbb{Z}/4$ is not isomorphic to $\mathbb{Z}/2 \times \mathbb{Z}/2$. The first has characteristic $4$ and the second characteristic $\operatorname{lcm}(2, 2) = 2$, and an isomorphism preserves the characteristic. The map $[a]_4 \mapsto ([a]_2, [a]_2)$ has kernel $\{0, 2\}$.

**Counterexample (Too many roots).** In $\mathbb{Z}/8$ the polynomial $X^2 - 1$ of degree $2$ has the four roots $1, 3, 5, 7$, since $9, 25, 49$ are $1$ modulo $8$. The bound on the number of roots needs a domain, and $\mathbb{Z}/8$ is not one: $(X - 3)(X + 3) = X^2 - 9 = X^2 - 1$ and $(X - 1)(X + 1) = X^2 - 1$ are two different factorizations.

### The library around it

Mathlib spreads $\mathbb{Z}/n$ over several volumes. The type `ZMod`, its ring structure, its characteristic `ZMod.charP`, its units and the map `ZMod.castHom` are in `Mathlib.Data.ZMod.Basic`, homed in Volume 2. The field instance is the only content of `Mathlib.Algebra.Field.ZMod`, in this volume. Fermat, Euler and the structure of the multiplicative group are in `Mathlib.FieldTheory.Finite.Basic`, in Volume 11. Quadratic residues, Wilson and Euler's criterion are in `Mathlib.NumberTheory`, in Volume 12. The theorem `ZMod.ringHom_eq_of_ker_eq` of Volume 9 is the uniqueness in the universal property, in a dual form.

To compute in `ZMod n`, use `decide` for small statements such as `(7 : ZMod 31) * 9 = 1`, and `norm_num` or `ring` for identities with variables. To prove a statement about `ZMod p` for a general prime, add the `Fact` instance before using any lemma that needs the field structure.

Common errors of a learner:

- Using `ZMod 0` as the zero ring. It is `ℤ`. The zero ring is `ZMod 1`.
- Expecting `Field (ZMod n)` for a variable `n` without `[Fact n.Prime]`. Instance search does not see a hypothesis `hp : n.Prime` in the context.
- Reading `x / y` in `ZMod n` for composite `n` as a quotient. The ring has an inverse function for all `n`, and for a nonunit `y` it returns a junk value.
- Writing `(a : ZMod n) = b` with `a b : ℕ` and expecting `a = b`. The cast is not injective. The bridge is `ZMod.natCast_eq_natCast_iff`, a congruence modulo `n`.
- Applying the Chinese remainder theorem to non-coprime moduli.

### Exercises

1. (A) List the ideals of $\mathbb{Z}/18$ and find the quotient by each.
2. (A) Find $[11]^{-1}$ in $\mathbb{Z}/26$ and $[17]^{-1}$ in $\mathbb{Z}/43$.
3. (A) Solve $x \equiv 1 \pmod 4$, $x \equiv 2 \pmod 9$ with the idempotents of $\mathbb{Z}/36$.
4. (B) Show that $\mathbb{Z}/n$ has exactly $2^r$ idempotents, where $r$ is the number of distinct primes dividing $n$. Hint: the only idempotents of $\mathbb{Z}/p^k$ are $0$ and $1$, since $e(e - 1) = 0$ and $e$, $e - 1$ cannot both be divisible by $p$.
5. (B) Show that there is no ring homomorphism $\mathbb{Z}/6 \to \mathbb{Z}/4$, and find all ring homomorphisms $\mathbb{Z}/6 \to \mathbb{Z}/3$.
6. (B) Show that the maximal ideals of $\mathbb{Z}/n$ are the ideals $p \cdot (\mathbb{Z}/n)$ for the primes $p \mid n$.
7. (B) Let $p$ be an odd prime. Show that the elements of $\mathbb{Z}/p$ with $x^2 = 1$ are $1$ and $-1$, and find an odd $n$ for which $x^2 = 1$ has more than two solutions in $\mathbb{Z}/n$.
8. (C) Show that $\mathbb{Z}/m \times \mathbb{Z}/n$ is isomorphic to $\mathbb{Z}/mn$ as a ring if and only if $\gcd(m, n) = 1$. Hint: compare the characteristics.
9. (C) Let $p$ be prime. Show that in each commutative ring $R$ of characteristic $p$, $a^p = a$ for each $a$ in the image of $\mathbb{Z}/p \to R$. Show that $\{a \in R : a^p = a\}$ is the prime field if $R$ is a field. Hint: a polynomial of degree $p$ over a field has at most $p$ roots.

### Notes and history

Gauss introduced congruences and the notation $a \equiv b \pmod n$ in the *Disquisitiones Arithmeticae* (1801), and the Chinese remainder theorem is much older: it appears in the *Sunzi Suanjing*, a Chinese text of about the fourth century, in a problem about a number that leaves remainders $2, 3, 2$ when divided by $3, 5, 7$. Dedekind's theory of ideals turned congruences into quotient rings, and Noether's work of the 1920s gave the isomorphism theorems their present form, with $\mathbb{Z}/n\mathbb{Z}$ as the first example.

In Mathlib the choice to define `ZMod (n + 1)` as `Fin (n + 1)` makes small computations decidable. The price is that the quotient description must be proved, and the field structure lives in a separate file so that `ZMod` does not depend on the theory of fields.

### Reference

<?reference?>
