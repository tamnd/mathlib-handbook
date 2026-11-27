---
title: Rings and first examples
kind: theory
modules:
  - Mathlib.Algebra.Ring.Defs
  - Mathlib.Algebra.Ring.BooleanRing
  - Mathlib.Algebra.Ring.Prod
  - Mathlib.Algebra.Ring.Pi
explains:
  E3: [Semiring, Ring, CommRing, BooleanRing]
  E2: [CommSemiring, neg_mul_neg, neg_mul, mul_sub, sub_mul, BooleanRing.mul_self, BooleanRing.add_self, BooleanRing.toCommRing, Prod.instRing, Pi.ring]
  E1: auto
families: []
requires: [V05.C01, V05.C02]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Rings and first examples

### Overview

A ring is a set with an addition and a multiplication. The addition makes it a commutative group. The multiplication is associative and has a unit. The two operations are tied by the distributive laws. Other rings break rules that hold in $\mathbb{Z}$: in the ring of $2 \times 2$ matrices the product is not commutative, in $\mathbb{Z}/6$ the product of two nonzero elements can be zero, and in a Boolean ring every element is its own square.

This section defines semirings, rings and commutative rings, and derives the first consequences of the axioms: $0 \cdot a = 0$, the rule of signs, the binomial theorem, and the fact that a ring with $0 = 1$ has one element. It proves that every Boolean ring is commutative, and it builds products and rings of functions. In Mathlib these notions are the classes `Semiring`, `Ring` and `CommRing`.

### Definitions

**Definition (Semiring).** A semiring is a set $R$ with two binary operations $+$ and $\cdot$ and two elements $0$ and $1$, such that:

1. $(R, +, 0)$ is a commutative monoid: $(a + b) + c = a + (b + c)$, $a + b = b + a$ and $a + 0 = a$;
2. $(R, \cdot, 1)$ is a monoid: $(a b) c = a (b c)$ and $1 a = a = a 1$;
3. the distributive laws hold: $a (b + c) = a b + a c$ and $(a + b) c = a c + b c$;
4. zero is absorbing: $0 \cdot a = 0 = a \cdot 0$.

A semiring is commutative if $a b = b a$ for all $a, b$.

The natural numbers $\mathbb{N}$ are the main example of a semiring that is not a ring. Axiom 4 is part of the definition of a semiring because it does not follow from the others when there are no negatives.

**Definition (Ring).** A ring is a semiring $R$ in which every element $a$ has an additive inverse $-a$, with $a + (-a) = 0$. So $(R, +, 0)$ is a commutative group. A commutative ring is a ring with $a b = b a$ for all $a, b$. One writes $a - b$ for $a + (-b)$.

In this volume a ring always has a unit $1$, and a ring homomorphism keeps it. A structure with all the axioms except the unit is a non-unital ring, for example $2\mathbb{Z}$.

::: mathlib
`Semiring` · `Mathlib.Algebra.Ring.Defs`

A class on a type `R`. It extends `NonUnitalSemiring`, `NonAssocSemiring` and `MonoidWithZero`, so the instance `[Semiring R]` gives the instances of all the weaker classes at once. The class has more fields than the axioms of the text: a field `natCast : ℕ → R` with the rules `natCast_zero` and `natCast_succ`, and a field `npow` for the powers $a^n$. Each field has a default value, so an instance can omit it. The fields let an instance choose a definition that computes well: the cast `ℕ → ℤ` is the constructor `Int.ofNat`, not the sum $1 + \dots + 1$.

<?decl Semiring?>
:::

::: mathlib
`Ring` · `Mathlib.Algebra.Ring.Defs`

A ring is a `Semiring` with `Neg` and `Sub` and the axiom `neg_add_cancel`. It also extends `AddGroupWithOne`, so it carries a field `intCast : ℤ → R` and a field `zsmul` for the integer multiples. The unit is part of the structure: Mathlib writes `NonUnitalRing` for the structure without $1$.

<?decl Ring?>
:::

::: mathlib
`CommRing` · `Mathlib.Algebra.Ring.Defs`

The class `CommRing R` extends `Ring R` and `CommMonoid R`. The matching class for semirings is `CommSemiring`, with `ℕ` as the main instance. The tactic `ring` proves each identity that holds in every commutative semiring, so the reader never needs to apply the axioms one by one.

<?decl CommRing?>
:::

**Definition (Boolean ring).** A Boolean ring is a ring in which $a^2 = a$ for every $a$.

::: mathlib
`BooleanRing` · `Mathlib.Algebra.Ring.BooleanRing`

The class extends `Ring` with the one field `mul_self : a * a = a`. The theorems below are `BooleanRing.add_self` and the instance `BooleanRing.toCommRing`. The same file builds the equivalence between Boolean rings and Boolean algebras, by the symmetric difference and the meet.

<?decl BooleanRing?>
:::

### Theorems and proofs

**Theorem (First consequences of the axioms).** Let $R$ be a ring and let $a, b, c \in R$. Then:

1. $0 \cdot a = 0$ and $a \cdot 0 = 0$;
2. $(-a) b = -(a b) = a (-b)$;
3. $(-a)(-b) = a b$, and in particular $(-1)(-1) = 1$ and $(-1) a = -a$;
4. $a (b - c) = a b - a c$ and $(a - b) c = a c - b c$.

*Proof.* (1) By the distributive law, $0 \cdot a = (0 + 0) a = 0 \cdot a + 0 \cdot a$. Add $-(0 \cdot a)$ to both sides. The left side becomes $0$ and the right side becomes $0 \cdot a$. So $0 \cdot a = 0$. The proof of $a \cdot 0 = 0$ is the same. So in a ring axiom 4 follows from the others.

(2) By the distributive law and (1), $a b + (-a) b = (a + (-a)) b = 0 \cdot b = 0$. So $(-a) b$ is an additive inverse of $a b$. The inverse in a group is unique, so $(-a) b = -(a b)$. In the same way $a b + a(-b) = a (b + (-b)) = a \cdot 0 = 0$, so $a(-b) = -(a b)$.

(3) Apply (2) twice: $(-a)(-b) = -(a (-b)) = -(-(a b)) = a b$. The last step is the rule $-(-x) = x$ of a group. With $a = b = 1$ this gives $(-1)(-1) = 1$. With $b$ replaced by $a$ and $a$ by $1$, (2) gives $(-1) a = -(1 \cdot a) = -a$.

(4) $a (b - c) = a (b + (-c)) = a b + a (-c) = a b - a c$ by (2). The second identity is the same. $\square$

::: mathlib
`neg_mul_neg` · `Mathlib.Algebra.Ring.Defs`

The rule of signs, `-a * -b = a * b`. It needs only a multiplication and the class `HasDistribNeg`, which says that negation commutes with the product in each factor. The companions are `neg_mul : -a * b = -(a * b)`, `mul_neg`, `mul_sub` and `sub_mul`. The rule $0 \cdot a = 0$ is `MulZeroClass.zero_mul`, written `zero_mul` in a proof, from Volume 5.

<?decl neg_mul_neg?>
:::

**Theorem (The zero ring).** Let $R$ be a ring with $1 = 0$. Then $R = \{0\}$.

*Proof.* Let $a \in R$. Then $a = a \cdot 1 = a \cdot 0 = 0$, by the axiom of the unit and part (1) of the first theorem. $\square$

Many theorems need a ring with $0 \ne 1$. Mathlib states this hypothesis as `[Nontrivial R]`, which says that $R$ has two distinct elements. For a ring this is the same as $0 \ne 1$, by the theorem.

The next theorem shows that one axiom of a ring is redundant.

**Theorem (Commutativity of the addition).** Let $R$ satisfy all the axioms of a ring except, possibly, the commutativity $a + b = b + a$. Then the addition is commutative.

*Proof.* Let $a, b \in R$. Expand $(1 + 1)(a + b)$ in two ways. By the left distributive law and then the right one,
$$(1 + 1)(a + b) = (1 + 1) a + (1 + 1) b = (a + a) + (b + b).$$
By the right distributive law and then the left one,
$$(1 + 1)(a + b) = 1 (a + b) + 1 (a + b) = (a + b) + (a + b).$$
So $a + a + b + b = a + b + a + b$, with the brackets dropped by associativity. The addition is a group, so one can cancel $a$ on the left and $b$ on the right. This gives $a + b = b + a$. $\square$

**Theorem (Binomial theorem).** Let $R$ be a ring and let $a, b \in R$ with $a b = b a$. For each $n \ge 0$,
$$(a + b)^n = \sum_{k=0}^{n} \binom{n}{k} a^k b^{n-k}.$$
In particular the formula holds for all $a, b$ in a commutative ring.

Here $\binom{n}{k} a^k b^{n-k}$ means the sum of $\binom{n}{k}$ copies of $a^k b^{n-k}$.

*Proof.* Induction on $n$. For $n = 0$ both sides are $1$. Assume the formula for $n$. Then
$$(a + b)^{n+1} = (a + b) \sum_{k=0}^{n} \binom{n}{k} a^k b^{n-k} = \sum_{k=0}^{n} \binom{n}{k} a^{k+1} b^{n-k} + \sum_{k=0}^{n} \binom{n}{k} b\, a^k b^{n-k}.$$
Since $a b = b a$, also $b a^k = a^k b$, by induction on $k$. So the second sum is $\sum_{k=0}^{n} \binom{n}{k} a^k b^{n+1-k}$. Shift the index in the first sum, $j = k + 1$, and collect the terms with $a^j b^{n+1-j}$. The coefficient is $\binom{n}{j-1} + \binom{n}{j}$ for $1 \le j \le n$, which is $\binom{n+1}{j}$ by the rule of Pascal. The terms $j = 0$ and $j = n + 1$ have coefficient $1 = \binom{n+1}{0} = \binom{n+1}{n+1}$. This is the formula for $n + 1$. $\square$

The hypothesis $a b = b a$ is used only to move $b$ past $a^k$. A counterexample below shows that the formula fails without it.

::: mathlib
`add_pow` · `Mathlib.Data.Nat.Choose.Sum`

The theorem for a commutative semiring: `(x + y) ^ n = ∑ m ∈ range (n + 1), x ^ m * y ^ (n - m) * n.choose m`. The form for commuting elements of any semiring is `Commute.add_pow`. Both are in Volume 2.

<?decl add_pow?>
:::

**Theorem (Boolean rings).** Let $R$ be a Boolean ring. Then $a + a = 0$ for each $a \in R$, and $R$ is commutative.

*Proof.* Let $a \in R$. Then $a + a = (a + a)^2 = a^2 + a^2 + a^2 + a^2 = a + a + a + a$. Subtract $a + a$ from both sides: $0 = a + a$. So $-a = a$ for every $a$.

Let $a, b \in R$. Then
$$a + b = (a + b)^2 = a^2 + a b + b a + b^2 = a + a b + b a + b.$$
Subtract $a + b$: $a b + b a = 0$. So $a b = -(b a) = b a$, by the first part applied to $b a$. $\square$

::: mathlib
`BooleanRing.add_self` · `Mathlib.Algebra.Ring.BooleanRing`

The first claim: `a + a = 0`. The second claim is the instance `BooleanRing.toCommRing`, which gives `CommRing α` from `BooleanRing α`. Mathlib proves `add_self` with the same computation as the text.

<?decl BooleanRing.add_self?>
:::

**Definition (Product ring and ring of functions).** Let $R$ and $S$ be rings. The product $R \times S$ is a ring with the operations by components: $(r, s) + (r', s') = (r + r', s + s')$ and $(r, s)(r', s') = (r r', s s')$, with zero $(0, 0)$ and unit $(1, 1)$. More generally, let $X$ be a set and $R$ a ring. The set $R^X$ of all functions $X \to R$ is a ring with the operations at each point: $(f + g)(x) = f(x) + g(x)$ and $(f g)(x) = f(x) g(x)$.

Each axiom of the product holds because it holds in each component. For example the left distributive law in $R \times S$ is the pair of the left distributive laws in $R$ and in $S$. The same is true of $R^X$, point by point.

::: mathlib
`Prod.instRing` · `Mathlib.Algebra.Ring.Prod`

The instance `Ring (R × S)` from `[Ring R] [Ring S]`. It is a `CommRing` when both factors are. The projections are ring homomorphisms `RingHom.fst` and `RingHom.snd`.

<?decl Prod.instRing?>
:::

::: mathlib
`Pi.ring` · `Mathlib.Algebra.Ring.Pi`

The ring structure on a dependent function type `∀ i, f i` when each `f i` is a ring. The operations are pointwise: `Pi.mul_apply` says `(f * g) x = f x * g x`.

<?decl Pi.ring?>
:::

### Examples

**Example (Number rings).** The integers $\mathbb{Z}$, the rationals $\mathbb{Q}$, the reals $\mathbb{R}$ and the complex numbers $\mathbb{C}$ are commutative rings with the usual operations. The natural numbers $\mathbb{N}$ are a commutative semiring, but not a ring: $1$ has no additive inverse in $\mathbb{N}$.

**Example (The integers modulo $6$).** The set $\mathbb{Z}/6 = \{0, 1, 2, 3, 4, 5\}$ with addition and multiplication modulo $6$ is a commutative ring. Its multiplication table has new features. First, $2 \cdot 3 = 6 = 0$: a product of two nonzero elements is zero. Second, $3^2 = 9 = 3$ and $4^2 = 16 = 4$: the elements $0, 1, 3, 4$ are idempotent. Third, $5 \cdot 5 = 25 = 1$, so $5$ has an inverse, and $5 = -1$. Chapter 2 builds $\mathbb{Z}/n$ as a quotient, and Chapter 4 studies it.

**Example (Matrices are not commutative).** Let $R = M_2(\mathbb{R})$ be the ring of $2 \times 2$ real matrices with the sum and product of matrices. Its zero is the zero matrix and its unit is the identity matrix $I$. Let
$$A = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}, \qquad B = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}.$$
Then $A B = B$ and $B A = 0$. So $A B \ne B A$, and $M_2(\mathbb{R})$ is a ring that is not commutative. It also has zero divisors: $B A = 0$ with $A, B \neq 0$, and $B^2 = 0$ with $B \ne 0$.

**Counterexample (The binomial theorem needs commuting elements).** With $A$ and $B$ as in the previous example, $A^2 = A$ and $B^2 = 0$. So
$$(A + B)^2 = A^2 + A B + B A + B^2 = A + B = \begin{pmatrix} 1 & 1 \\ 0 & 0 \end{pmatrix},$$
while
$$A^2 + 2 A B + B^2 = A + 2 B = \begin{pmatrix} 1 & 2 \\ 0 & 0 \end{pmatrix}.$$
The two sides differ in the entry at the top right. The proof of the binomial theorem used $b a^k = a^k b$, and here $B A \ne A B$.

**Example (A product has zero divisors).** In $\mathbb{Z} \times \mathbb{Z}$ the elements $e = (1, 0)$ and $f = (0, 1)$ are nonzero, and $e f = (0, 0)$. They are idempotent, $e^2 = e$ and $f^2 = f$, and $e + f = (1, 1)$ is the unit. So a product of two nonzero rings always has zero divisors.

**Example (The ring of subsets).** Let $X$ be a set and let $\mathcal{P}(X)$ be the set of its subsets. Define $A + B = A \,\triangle\, B = (A \setminus B) \cup (B \setminus A)$, the symmetric difference, and $A \cdot B = A \cap B$. Then $\mathcal{P}(X)$ is a Boolean ring with zero $\varnothing$ and unit $X$. The quickest proof identifies a subset $A$ with its indicator function $1_A : X \to \mathbb{Z}/2$. Then $1_{A \triangle B} = 1_A + 1_B$ and $1_{A \cap B} = 1_A 1_B$, so $\mathcal{P}(X)$ is the ring $(\mathbb{Z}/2)^X$ of functions in another form. The additive inverse of $A$ is $A$, since $A \triangle A = \varnothing$.

### The library around it

The classes of `Mathlib.Algebra.Ring.Defs` form a lattice. The weakest are `Distrib` (a type with `+` and `*` and the two distributive laws) and `NonUnitalNonAssocSemiring`. Above them are `NonUnitalSemiring`, `NonAssocSemiring` and `Semiring`, and the same with `Ring` in place of `Semiring`, and `Comm` in front of each. Each theorem is stated for the weakest class that proves it: `mul_sub` needs only `NonUnitalNonAssocRing`.

The lemmas about the operations follow a naming pattern: `mul_add` and `add_mul` for the distributive laws, `mul_sub` and `sub_mul`, `neg_mul`, `mul_neg` and `neg_mul_neg`, `mul_comm` in a commutative structure. The casts `(n : R)` from `ℕ` and `ℤ` respect the operations by `Nat.cast_mul` and `Int.cast_mul`, and `push_cast` moves them inwards (Volume 2).

Common errors of a learner:

- The hypothesis `[Ring R]` does not give commutativity. A goal `a * b = b * a` needs `[CommRing R]` or a proof of `Commute a b`. In that case use `noncomm_ring`, not `ring`.
- The zero ring is a ring. A theorem that needs $0 \ne 1$ has the hypothesis `[Nontrivial R]`, and the error message speaks of a missing instance `Nontrivial R`.
- `ℕ` is a `CommSemiring`, not a ring. In `ℕ`, `a - b` is the truncated subtraction, and the lemma `mul_sub` for rings does not apply. The lemma `Nat.mul_sub` has the truncated form.

### Exercises

1. (A) In a ring, prove that $(a + b)^2 = a^2 + a b + b a + b^2$. Deduce that $(a + b)^2 = a^2 + 2 a b + b^2$ for all $a, b$ if and only if the ring is commutative.
2. (A) Write the multiplication table of $\mathbb{Z}/8$ for the odd classes. Show that $x^2 = 1$ for each odd $x$.
3. (A) Show that the only idempotents of $\mathbb{Z}$ are $0$ and $1$, and find all the idempotents of $\mathbb{Z}/12$.
4. (A) Let $R$ be a ring and $a \in R$ with $a^2 = 0$. Show that $(1 - a)(1 + a) = 1$.
5. (B) Show that in a ring, $(-a)^n = a^n$ if $n$ is even and $(-a)^n = -a^n$ if $n$ is odd. Hint: induction on $n$ with the rule of signs.
6. (B) Let $X$ be a set. Show that the map $A \mapsto 1_A$ from $\mathcal{P}(X)$ to $(\mathbb{Z}/2)^X$ is a bijection that sends symmetric difference to sum and intersection to product. Hint: compute $1_A(x) + 1_B(x)$ in the four cases $x \in A$ or not, $x \in B$ or not.
7. (B) Let $R$ be a ring in which $x^3 = x$ for each $x$. Show that $6 x = 0$ for each $x$. Hint: compute $(x + x)^3$ in two ways.
8. (B) Show that a non-unital ring $R$ in which every element is idempotent is commutative. Hint: the proof of the theorem on Boolean rings never uses $1$.
9. (C) Let $R$ be a ring in which $x^3 = x$ for each $x$. Show that $R$ is commutative. Hint: first show that $a^2 = 0$ implies $a = 0$. Then let $e = x^2$, an idempotent, and show that $(e y - e y e)^2 = 0$ and $(y e - e y e)^2 = 0$, so that $x^2$ is central. Expand $(x + x^2)^2$ to see that $2 x$ is central, and $(x + 1)^3 = x + 1$ to see that $3 x$ is central.

### Notes and history

The word ring (Zahlring) is due to Hilbert, in his report on algebraic number theory of 1897, for the rings of integers of number fields. The abstract definition was given by Fraenkel in 1914, and Emmy Noether made it the base of modern algebra in her papers of the 1920s on ideals. Boole introduced the algebra of logic in 1847 and 1854. Stone proved in 1936 that Boolean algebras and Boolean rings are the same, and that every Boolean ring is a ring of subsets. The commutativity of rings with $x^3 = x$, and more generally with $x^n = x$, is a theorem of Jacobson (1945). The standard references are Dummit-Foote, *Abstract Algebra*, Section 7.1, and Jacobson, *Basic Algebra I*, Chapter 2.

In Mathlib the fields `natCast`, `intCast`, `nsmul` and `zsmul` were added to the ring classes over several refactors, so that the instances on `ℕ`, `ℤ`, `ℚ` and on polynomial rings compute well. The non-unital and non-associative classes serve $C^*$-algebras and Lie algebras.

### Reference

<?reference?>
