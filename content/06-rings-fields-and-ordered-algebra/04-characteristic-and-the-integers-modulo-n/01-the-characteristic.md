---
title: The characteristic of a ring
kind: theory
modules:
  - Mathlib.Algebra.CharP.Defs
  - Mathlib.Algebra.CharP.Lemmas
  - Mathlib.Algebra.CharP.Frobenius
  - Mathlib.Algebra.CharP.Reduced
  - Mathlib.Algebra.CharZero.Defs
explains:
  E3: [CharP, ringChar, CharZero, CharP.char_is_prime_or_zero, frobenius, add_pow_char]
  E2: [CharP.cast_eq_zero_iff, CharP.cast_eq_zero, CharP.eq, CharP.exists, ringChar.spec, ringChar.eq, CharP.char_ne_one, CharP.char_is_prime, CharP.char_is_prime_of_pos, CharP.intCast_eq_zero_iff, CharP.ringChar_zero_iff_CharZero, ExpChar, sub_pow_char, add_pow_expChar, frobenius_def, frobenius_inj, charZero_of_inj_zero, Nat.cast_injective]
  E1: auto
families: []
requires: [V06.C01, V06.C02, V06.C03, V02.C02]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The characteristic of a ring

### Overview

In $\mathbb{Z}/5$ the sum $1 + 1 + 1 + 1 + 1$ is $0$. In $\mathbb{Q}$ no sum $1 + 1 + \dots + 1$ of positive length is $0$. The characteristic measures this: it is the least $n \ge 1$ with $n \cdot 1 = 0$, or $0$ if there is no such $n$. Every ring receives a unique homomorphism from $\mathbb{Z}$ (Chapter 1), and the characteristic is the generator of its kernel.

The section proves three theorems. The characteristic of an integral domain is $0$ or a prime. A field of characteristic $0$ contains a copy of $\mathbb{Q}$, and a field of characteristic $p$ contains a copy of $\mathbb{Z}/p$. In a commutative ring of prime characteristic $p$, $(a + b)^p = a^p + b^p$, so the $p$-th power map is a ring homomorphism, the Frobenius. The last fact is the basis of the theory of finite fields in Volume 11 and of much of number theory in Volume 12.

### Definitions

For $n \in \mathbb{Z}$ and an element $a$ of a ring $R$, $n \cdot a$ is the $n$-fold sum of $a$ (Volume 5, Chapter 1). The image of $n$ under the unique ring homomorphism $\chi : \mathbb{Z} \to R$ is $\chi(n) = n \cdot 1$, written $n$ or $(n : R)$ when no confusion is possible.

**Definition (Characteristic).** Let $R$ be a ring. The *characteristic* of $R$, written $\operatorname{char} R$, is the unique $n \in \mathbb{N}$ with $\ker \chi = n \mathbb{Z}$. Equivalently: for each $m \in \mathbb{N}$, $m \cdot 1 = 0$ in $R$ if and only if $n \mid m$.

The kernel $\ker \chi$ is an ideal of $\mathbb{Z}$ (Chapter 2), and each ideal of $\mathbb{Z}$ is $n \mathbb{Z}$ for exactly one $n \ge 0$. So the definition makes sense. If $\operatorname{char} R = n > 0$, then $n$ is the least positive integer with $n \cdot 1 = 0$, since the least positive element of $n \mathbb{Z}$ is $n$. If $\operatorname{char} R = 0$, then $m \cdot 1 \ne 0$ for every $m \ge 1$, and $\chi$ is injective.

The convention "$0$ for no such $n$" is not arbitrary. It makes the second form of the definition uniform: $0$ is the only natural number whose multiples are $\{0\}$. A book that says "the characteristic is infinite" loses this uniformity.

::: mathlib
`CharP` · `Mathlib.Algebra.CharP.Defs`

`CharP R p` is a class of propositions with one field, `cast_eq_zero_iff' : ∀ x : ℕ, (x : R) = 0 ↔ p ∣ x`. This is the second form of the definition. The argument `p` is an `outParam`: when Lean searches for an instance `CharP R ?p`, it finds `p` from `R`. So the characteristic of `ZMod n` is found by instance search, with the instance `ZMod.charP` of Volume 2. The class needs only an `AddMonoidWithOne`, so it also applies to semirings such as `ℕ`.

<?decl CharP?>
:::

::: mathlib
`ringChar` · `Mathlib.Algebra.CharP.Defs`

`ringChar R : ℕ` is the characteristic as a function, chosen by `Classical.choice` from `CharP.exists`. Use `ringChar` when the characteristic is not known and must be named, for example in "let $p = \operatorname{char} K$". Use `CharP R p` as a hypothesis when `p` is given. They are linked by `ringChar.eq : [CharP R p] → ringChar R = p` and `ringChar.of_eq`.

<?decl ringChar?>
:::

**Definition (Characteristic zero).** A ring $R$ has *characteristic zero* if the map $\mathbb{N} \to R$, $m \mapsto m \cdot 1$, is injective.

For a ring this is the same as $\operatorname{char} R = 0$: injectivity implies that $m \cdot 1 = 0 = 0 \cdot 1$ forces $m = 0$, and conversely, if $m \cdot 1 = k \cdot 1$ with $m \ge k$, then $(m - k) \cdot 1 = 0$, so $m = k$.

::: mathlib
`CharZero` · `Mathlib.Algebra.CharZero.Defs`

`CharZero R` is a class with the field `cast_injective : Function.Injective (Nat.cast : ℕ → R)`. It is used much more often than `CharP R 0`, because it is the hypothesis of the cast lemmas `Nat.cast_inj`, `Nat.cast_eq_zero` and `Nat.cast_injective`. An ordered semiring such as `ℕ`, `ℚ` or `ℝ` gets it by an instance (Chapter 7). The bridge to `CharP` is `CharP.ringChar_zero_iff_CharZero` for rings, and `CharP.ofCharZero`.

<?decl CharZero?>
:::

**Definition (Exponential characteristic).** The *exponential characteristic* of a ring of characteristic $p > 0$ is $p$, and of a ring of characteristic $0$ is $1$.

The point of this convention is that $a \mapsto a^q$, with $q$ the exponential characteristic, is the Frobenius map below in prime characteristic and the identity in characteristic $0$. So statements about the Frobenius cover both cases at once.

::: mathlib
`ExpChar` · `Mathlib.Algebra.CharP.Defs`

`ExpChar R q` is an inductive class with two constructors: `ExpChar.zero` for `[CharZero R]` with `q = 1`, and `ExpChar.prime` for a prime `q` with `CharP R q`. The Frobenius map of Mathlib is defined under `ExpChar`, not `CharP`.

<?decl ExpChar?>
:::

### Theorems and proofs

**Theorem (Characteristic of a domain).** Let $R$ be a ring with $0 \ne 1$ and no zero divisors. Then $\operatorname{char} R$ is $0$ or a prime number.

*Proof.* Let $n = \operatorname{char} R$ and assume $n \ne 0$. Since $1 \cdot 1 = 1 \ne 0$, $n \ne 1$, so $n \ge 2$. Assume $n = a b$ with $1 \le a, b \le n$. Then
$$(a \cdot 1)(b \cdot 1) = (a b) \cdot 1 = n \cdot 1 = 0,$$
by the distributive law. Since $R$ has no zero divisors, $a \cdot 1 = 0$ or $b \cdot 1 = 0$. In the first case $n \mid a$, so $a = n$ and $b = 1$. In the second case $b = n$ and $a = 1$. So the only factorizations of $n$ are the trivial ones, and $n$ is prime. $\square$

::: mathlib
`CharP.char_is_prime_or_zero` · `Mathlib.Algebra.CharP.Defs`

The theorem under `[NoZeroDivisors R] [Nontrivial R]` and `[CharP R p]`: `Nat.Prime p ∨ p = 0`. The hypotheses are the two halves of `IsDomain` for a ring, and they are weaker for a semiring. The form with `[NeZero p]` that gives `Fact (Nat.Prime p)` is `CharP.char_is_prime_of_pos`.

<?decl CharP.char_is_prime_or_zero?>
:::

**Theorem (Finite rings).** A finite ring $R$ has positive characteristic. If $R$ is a finite domain, its characteristic is a prime.

*Proof.* The elements $0 \cdot 1, 1 \cdot 1, 2 \cdot 1, \dots$ of the finite set $R$ cannot all be different. So $m \cdot 1 = k \cdot 1$ for some $m > k$, and $(m - k) \cdot 1 = 0$ with $m - k \ge 1$. So $\operatorname{char} R \ne 0$. For a domain, the previous theorem then says that it is a prime. $\square$

::: mathlib
`CharP.char_is_prime` · `Mathlib.Algebra.CharP.Lemmas`

The second claim, for a `[Finite R]` ring with no zero divisors and `Nontrivial R`.

<?decl CharP.char_is_prime?>
:::

**Theorem (Prime fields).** Let $K$ be a field. If $\operatorname{char} K = 0$, there is exactly one ring homomorphism $\mathbb{Q} \to K$, and it is injective. If $\operatorname{char} K = p > 0$, the map $\mathbb{Z}/p \to K$, $[m] \mapsto m \cdot 1$, is a well defined injective ring homomorphism. In both cases the image is the smallest subfield of $K$, the *prime field* of $K$.

*Proof.* Characteristic $0$: the map $\chi : \mathbb{Z} \to K$ is injective, so by the universal property of the field of fractions (Chapter 3) it extends uniquely to $\bar\chi : \mathbb{Q} \to K$, $\bar \chi(a/b) = (a \cdot 1)(b \cdot 1)^{-1}$. A homomorphism from a field is injective (Chapter 3). Each homomorphism $\mathbb{Q} \to K$ restricts on $\mathbb{Z}$ to the unique homomorphism $\chi$, so it is $\bar \chi$ by the uniqueness part.

Characteristic $p$: the kernel of $\chi$ is $p \mathbb{Z}$. By the first isomorphism theorem (Chapter 2), $\chi$ induces an injective homomorphism $\mathbb{Z}/p\mathbb{Z} \to K$, $[m] \mapsto m \cdot 1$.

Minimality: each subfield of $K$ contains $1$, hence each $m \cdot 1$ and, in characteristic $0$, each quotient $(a \cdot 1)(b \cdot 1)^{-1}$. So each subfield contains the image. The image is a subfield: in characteristic $0$ it is the image of the field $\mathbb{Q}$, and in characteristic $p$ it is the image of $\mathbb{Z}/p$, which is a field by Section 2. $\square$

::: mathlib
`RingHom.charP` · `Mathlib.Algebra.CharP.Algebra`

An injective homomorphism `f : R →+* A` transfers the characteristic back: `CharP A p → CharP R p`. So a subring of `K` has the characteristic of `K`. The map $\mathbb{Q} \to K$ in characteristic zero is `Rat.castHom K`, and the map $\mathbb{Z}/n \to R$ for `[CharP R n]` is `ZMod.castHom`, injective by `ZMod.castHom_injective`.

<?decl RingHom.charP?>
:::

**Lemma (Binomial coefficients at a prime).** Let $p$ be prime and $0 < k < p$. Then $p \mid \binom{p}{k}$.

*Proof.* The integer $\binom pk$ satisfies $k! \, (p - k)! \binom{p}{k} = p!$. The prime $p$ divides $p!$. It does not divide $k! \, (p - k)!$, because this is a product of integers between $1$ and $p - 1$, and a prime that divides a product divides one of the factors (Volume 2, Chapter 2). So $p$ divides $\binom pk$. $\square$

**Theorem (Freshman's dream).** Let $R$ be a commutative ring of prime characteristic $p$. For all $a, b \in R$,
$$(a + b)^p = a^p + b^p, \qquad (a - b)^p = a^p - b^p.$$
So the map $F : R \to R$, $F(a) = a^p$, is a ring homomorphism, the *Frobenius* of $R$. If $R$ has no nonzero nilpotent elements, for example if $R$ is a domain, then $F$ is injective. If $R$ is a finite field, $F$ is bijective.

*Proof.* The binomial theorem holds in a commutative ring (Chapter 1):
$$(a + b)^p = a^p + \sum_{k=1}^{p-1} \binom{p}{k} a^k b^{p-k} + b^p.$$
For $0 < k < p$, $\binom pk = p m_k$ with $m_k \in \mathbb{Z}$ by the lemma, so $\binom{p}{k} a^k b^{p-k} = m_k \cdot (p \cdot 1) \cdot a^k b^{p - k} = 0$. So the middle sum is $0$.

For the difference, apply the sum rule to $a - b$ and $b$: $a^p = ((a - b) + b)^p = (a - b)^p + b^p$.

So $F$ preserves sums. It preserves products and $1$, since $R$ is commutative: $(a b)^p = a^p b^p$ and $1^p = 1$. So $F$ is a ring homomorphism. If $F(a) = 0$, then $a^p = 0$ and $a$ is nilpotent, so $a = 0$ when $R$ has no nonzero nilpotents; then $F$ is injective because it is additive. A finite field has no nonzero nilpotents, and an injective map of a finite set to itself is surjective. $\square$

Commutativity is used twice: in the binomial theorem and in $(a b)^p = a^p b^p$. By induction, $(a + b)^{p^n} = a^{p^n} + b^{p^n}$ for every $n$, since $F^n$ is a composite of homomorphisms.

::: mathlib
`add_pow_char` · `Mathlib.Algebra.CharP.Lemmas`

The identity `(x + y) ^ p = x ^ p + y ^ p` in a `CommSemiring` with `[Fact (Nat.Prime p)]` and `[CharP R p]`. The primality is a `Fact` instance, so it is found by instance search once declared with `haveI := Fact.mk hp`. The forms `add_pow_char_pow` for $p^n$ and `sub_pow_char` for a difference are in the same file. The version under `ExpChar` is `add_pow_expChar`. For a noncommutative ring the identity needs `Commute x y`, as in `add_pow_char_of_commute`.

<?decl add_pow_char?>
:::

::: mathlib
`frobenius` · `Mathlib.Algebra.CharP.Lemmas`

The bundled map `frobenius R p : R →+* R` for `[CommSemiring R] [ExpChar R p]`, with `frobenius_def : frobenius R p x = x ^ p`. With `ExpChar`, the map is the identity in characteristic $0$, so a theorem about it needs no case split. Its injectivity on a reduced ring, a ring with no nonzero nilpotents, is `frobenius_inj`.

<?decl frobenius?>
:::

### Examples

**Example (Characteristics of the standard rings).** The rings $\mathbb{Z}$, $\mathbb{Q}$, $\mathbb{R}$, $\mathbb{C}$ have characteristic $0$, since they contain $\mathbb{N}$ with its usual sums. The ring $\mathbb{Z}/n$ has characteristic $n$, since $m \cdot [1] = [m] = 0$ if and only if $n \mid m$. The field $\mathbb{F}_4$ of Chapter 3 has characteristic $2$, and its prime field is $\{0, 1\}$. The polynomial ring $(\mathbb{Z}/2)[X]$ is an infinite ring of characteristic $2$, so the converse of the theorem on finite rings fails. The zero ring has characteristic $1$, the only ring with this characteristic.

**Example (A product ring).** In $\mathbb{Z}/4 \times \mathbb{Z}/6$, $m \cdot (1, 1) = ([m], [m])$ is $0$ if and only if $4 \mid m$ and $6 \mid m$, that is, $12 \mid m$. So the characteristic is $\operatorname{lcm}(4, 6) = 12$, not $24$. The ring is not a domain, and $12$ is not prime.

**Example (The Frobenius in $\mathbb{Z}/5$).** In $\mathbb{Z}/5$: $3^5 = 243 = 48 \cdot 5 + 3$ and $4^5 = 1024 = 204 \cdot 5 + 4$, so $3^5 + 4^5 = 3 + 4 = 7 = 2$, and $(3 + 4)^5 = 2^5 = 32 = 2$. The two sides agree, as the theorem says. Here the Frobenius is the identity: $a^5 = a$ for each $a \in \mathbb{Z}/5$. This is Fermat's little theorem, which Section 2 proves. In $\mathbb{F}_4$ the Frobenius $a \mapsto a^2$ is not the identity: it fixes $0$ and $1$ and exchanges $\omega$ and $\omega + 1 = \omega^2$.

**Example (A polynomial identity).** In $(\mathbb{Z}/3)[X]$, $(X + 1)^3 = X^3 + 3X^2 + 3X + 1 = X^3 + 1$. The coefficients $\binom 31 = \binom 32 = 3$ vanish. The identity holds in the polynomial ring, not only for the values $X = 0, 1, 2$.

**Counterexample (The characteristic of a ring with zero divisors).** The ring $\mathbb{Z}/6$ has characteristic $6$, which is not prime. The step of the proof that fails is the cancellation: $(2 \cdot 1)(3 \cdot 1) = 0$ with both factors nonzero.

**Counterexample (The dream needs a prime).** In $\mathbb{Z}/4$, of characteristic $4$, $(1 + 1)^4 = 2^4 = 16 = 0$ and $1^4 + 1^4 = 2 \ne 0$. Also $(1 + 1)^2 = 0 \ne 2 = 1^2 + 1^2$. The coefficient $\binom 42 = 6$ is not divisible by $4$. In characteristic $0$ the identity fails as well: $(1 + 1)^2 = 4 \ne 2$ in $\mathbb{Z}$.

**Counterexample (The Frobenius need not be surjective).** Let $K = \mathbb{F}_p(T)$ be the field of rational functions over $\mathbb{Z}/p$ (Chapter 3). The Frobenius $F(f) = f^p$ is injective. It is not surjective: if $T = (f/g)^p$ with polynomials $f, g$, then $T g^p = f^p$, and the degree of the left side is $1 + p \deg g$ while the degree of the right side is $p \deg f$. These numbers differ modulo $p$. So the finiteness hypothesis for bijectivity is needed. Fields where $F$ is bijective are the *perfect* fields of Volume 11.

### The library around it

The files `Mathlib.Algebra.CharP.Defs` and `Lemmas` hold the API of `CharP`:

- `CharP.cast_eq_zero : ((p : ℕ) : R) = 0` and the field `CharP.cast_eq_zero_iff`;
- `CharP.intCast_eq_zero_iff`, the same for integers, in a ring;
- `CharP.eq`, the uniqueness, and `CharP.exists`, the existence;
- `CharP.char_ne_one`, the characteristic of a nontrivial ring is not $1$;
- `ringChar.spec : (x : R) = 0 ↔ ringChar R ∣ x` for the function form.

The file `Mathlib.Algebra.CharZero.Defs` gives `Nat.cast_injective` and the constructor `charZero_of_inj_zero`, which reduces `CharZero` to "$n \cdot 1 = 0$ implies $n = 0$". The file `Mathlib.Algebra.CharP.Frobenius` gives the iterates `iterateFrobenius` and the commutation of ring homomorphisms with the Frobenius, `RingHom.map_frobenius`. The file `Mathlib.Algebra.CharP.Algebra` transfers the characteristic along injective homomorphisms and algebras, with `RingHom.charP` and `Algebra.charP_iff`.

Common errors of a learner:

- Writing `[CharP R p]` without `[Fact p.Prime]` and expecting `add_pow_char`. The identity fails for composite `p`.
- Writing `ringChar R = 0` where `CharZero R` is the hypothesis of the cast lemmas. Convert with `CharP.ringChar_zero_iff_CharZero`.
- Confusing `(p : R) = 0` with `p = 0`. The first is a fact about `R`, the second about `ℕ`.
- Expecting the characteristic of a finite ring to be its cardinality. The ring $\mathbb{Z}/2 \times \mathbb{Z}/2$ has $4$ elements and characteristic $2$.

### Exercises

1. (A) Find the characteristic of $\mathbb{Z}/3 \times \mathbb{Z}/5$, of $\mathbb{Z} \times \mathbb{Z}/2$ and of $M_2(\mathbb{Z}/7)$.
2. (A) Show that a ring of characteristic $2$ satisfies $-a = a$ for each $a$.
3. (A) Show that a subring of a ring has the same characteristic as the ring.
4. (B) Show that the characteristic of $R \times S$ is $\operatorname{lcm}(\operatorname{char} R, \operatorname{char} S)$, with the convention $\operatorname{lcm}(m, 0) = 0$.
5. (B) Let $K$ be a finite field. Show that $|K| = p^n$ for $p = \operatorname{char} K$ and some $n \ge 1$. Hint: $K$ is a vector space over its prime field $\mathbb{Z}/p$.
6. (B) Let $R$ be a commutative ring of characteristic $p$ prime. Show that the set $\{a \in R : a^p = a\}$ is a subring. Hint: it is the set of fixed points of a ring homomorphism.
7. (B) Show that a Boolean ring, a ring with $a^2 = a$ for each $a$, has characteristic $2$ unless it is the zero ring. Hint: expand $(1 + 1)^2$.
8. (C) Let $R$ be a commutative ring of characteristic $p$ prime and let $a, b \in R$. Show that $(a + b)^{p^n} = a^{p^n} + b^{p^n}$ for each $n \ge 1$, and compute $(X + 1)^{9}$ in $(\mathbb{Z}/3)[X]$.
9. (C) Let $K$ be a field of characteristic $p$ and $a \in K$. Show that $X^p - a$ has at most one root in $K$. Hint: if $b^p = a = c^p$, then $(b - c)^p = 0$.

### Notes and history

The characteristic appears in Steinitz's *Algebraische Theorie der Körper* (1910), which divided fields by their prime field into those of characteristic $0$ and those of characteristic $p$. Galois had constructed the finite fields of order $p^n$ in 1830, and the identity $(a + b)^p = a^p + b^p$ is implicit there and in Gauss's work on congruences. Frobenius used the $p$-th power map in 1896 in his work on the density of primes with a given splitting, and the map now bears his name. The name *freshman's dream* comes from the error of a beginner who expands $(a + b)^n$ as $a^n + b^n$ in the real numbers.

In Mathlib, `CharP` dates from the Lean 3 library. The `outParam` on the characteristic makes `p` an output of instance search, so that a ring has at most one `CharP` instance in practice. The class `ExpChar` and the redefinition of `frobenius` under it came later, to unify the statements in characteristic $0$ and $p$.

### Reference

<?reference?>
