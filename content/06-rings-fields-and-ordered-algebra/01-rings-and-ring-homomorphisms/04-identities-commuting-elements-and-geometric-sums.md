---
title: Identities, commuting elements and geometric sums
kind: api
modules:
  - Mathlib.Algebra.Ring.Basic
  - Mathlib.Algebra.Ring.Commute
  - Mathlib.Algebra.Ring.Semiconj
  - Mathlib.Algebra.Ring.Identities
  - Mathlib.Algebra.Ring.GeomSum
  - Mathlib.Algebra.Ring.Idempotent
  - Mathlib.Algebra.Ring.Associator
  - Mathlib.Algebra.Ring.Divisibility.Basic
  - Mathlib.Algebra.Ring.Divisibility.Lemmas
explains:
  E2: [Commute.add_sq, sq_eq_one_iff, Commute.geom_sum₂_mul, geom_sum_mul, sub_dvd_pow_sub_pow, IsIdempotentElem.one_sub, sum_four_sq_mul_sum_four_sq, associator_cocycle]
  E1: auto
families: []
requires: [V03, V05.C01, V05.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Identities, commuting elements and geometric sums

### Overview

Section 1 proves the first identities from the ring axioms: $0 a = 0$, the rule of signs and the binomial theorem. A working proof needs many more identities of the same kind. The square of a sum, the difference of two squares, the sum of a geometric progression and the rules for divisibility appear in almost every chapter of this volume. This section describes the modules that hold them.

In a commutative ring the tactic `ring` proves each such identity at once. The library still states them as lemmas, for two reasons. First, many of them hold in a noncommutative ring when two elements commute, and the lemma then takes a proof of `Commute a b` as a hypothesis. Second, a rewrite with a named lemma is often the shortest step inside a longer proof. The section also treats idempotent elements, the associator of a nonassociative ring, and the divisibility relation in a ring.

### The library around it

#### Commuting elements

Two elements $a, b$ of a ring commute if $a b = b a$. The predicate is `Commute a b` from Volume 5, and the more general `SemiconjBy a x y` says $a x = y a$. The module `Mathlib.Algebra.Ring.Commute` proves that commuting is stable under the ring operations: `Commute.add_right`, `Commute.add_left`, `Commute.sub_right`, `Commute.sub_left`, `Commute.neg_right` and `Commute.neg_left`, with the forms `Commute.neg_right_iff` and `Commute.neg_left_iff`. The elements $1$ and $-1$ commute with each element, by `Commute.neg_one_left` and `Commute.neg_one_right`. The module `Mathlib.Algebra.Ring.Semiconj` proves the same rules for `SemiconjBy`: `SemiconjBy.add_right`, `SemiconjBy.add_left`, `SemiconjBy.sub_right`, `SemiconjBy.neg_right` and their relatives.

For commuting elements the identities of school algebra hold. The library states each one twice: once with a hypothesis `Commute a b` in a ring, and once without a hypothesis in a commutative ring.

| Lean name | Statement |
|---|---|
| `Commute.add_sq` | $(a + b)^2 = a^2 + 2 a b + b^2$ if $a b = b a$ |
| `Commute.sub_sq` | $(a - b)^2 = a^2 - 2 a b + b^2$ if $a b = b a$ |
| `Commute.sq_sub_sq` | $a^2 - b^2 = (a + b)(a - b)$ if $a b = b a$ |
| `Commute.mul_self_sub_mul_self_eq` | $a a - b b = (a + b)(a - b)$ if $a b = b a$ |
| `sub_sq` | $(a - b)^2 = a^2 - 2 a b + b^2$ in a commutative ring |
| `sq_sub_sq` | $a^2 - b^2 = (a + b)(a - b)$ in a commutative ring |
| `mul_self_sub_one` | $a a - 1 = (a + 1)(a - 1)$ in each ring |
| `neg_sq` | $(-a)^2 = a^2$ |
| `neg_pow` | $(-a)^n = (-1)^n a^n$ |
| `neg_one_pow_eq_or` | $(-1)^n = 1$ or $(-1)^n = -1$ |

The proof of `Commute.add_sq` is the expansion $(a + b)^2 = a^2 + a b + b a + b^2$, followed by $b a = a b$. Without the hypothesis the identity fails: for $2 \times 2$ matrices with $a b \ne b a$, the two sides differ by $b a - a b$.

The difference of two squares gives the solutions of $x^2 = y^2$ in a ring with no zero divisors. The lemma `sq_eq_one_iff` states $a^2 = 1 \iff a = 1 \lor a = -1$ under `[NoZeroDivisors R]`. *Proof.* By `mul_self_sub_one`, $a^2 - 1 = (a + 1)(a - 1)$. The product is zero exactly when one factor is zero. $\square$ The same argument gives `Commute.sq_eq_sq_iff_eq_or_eq_neg`, `sq_eq_sq_iff_eq_or_eq_neg` and `mul_self_eq_mul_self_iff`. For units, `Units.inv_eq_self_iff` says that $u^{-1} = u$ only for $u = \pm 1$.

The commutator $x y - y x$ is the Lie bracket `⁅x, y⁆` of the ring. The instance `Ring.instBracket` defines it, `Ring.lie_def` unfolds it, and `commute_iff_lie_eq` says that $x$ and $y$ commute if and only if the bracket is zero.

#### The ring as maps

Multiplication by a fixed element is additive, by the distributive laws. The module `Mathlib.Algebra.Ring.Basic` bundles this fact. `AddMonoidHom.mulLeft r` is the map $x \mapsto r x$ as an additive homomorphism, `AddMonoidHom.mulRight r` is $x \mapsto x r$, and `AddMonoidHom.mul` is the multiplication as a biadditive map `R →+ R →+ R`. The forms `AddMonoid.End.mulLeft`, `AddMonoid.End.mulRight`, `AddHom.mulLeft` and `AddHom.mulRight` give the same maps in other bundled types. The lemma `AddMonoidHom.mulLeft_eq_mulRight_iff_forall_commute` says that left and right multiplication by $a$ agree if and only if $a$ is central.

The same module holds a group of facts about zero divisors. The lemma `noZeroDivisors_tfae` says that the four conditions "no zero divisors", "left cancellation", "right cancellation" and "two-sided cancellation" are equivalent in a ring. The lemma `isDomain_iff_noZeroDivisors_and_nontrivial` says that a domain is a nontrivial ring with no zero divisors, and `noZeroDivisors_iff_isDomain_or_subsingleton` adds the zero ring as the other case. The lemma `vieta_formula_quadratic` says that if $x$ is a root of $X^2 - b X + c$ in a commutative ring, then $y = b - x$ is the second root, with $x + y = b$ and $x y = c$. The signs and inverses in a division monoid with a negation are in the same file: `neg_div`, `div_neg`, `neg_div_neg_eq`, `inv_neg` and `inv_neg_one`.

#### Named identities

The module `Mathlib.Algebra.Ring.Identities` proves the product formulas for sums of squares in a commutative ring.

| Lean name | Statement |
|---|---|
| `sq_add_sq_mul_sq_add_sq` | $(x_1^2 + x_2^2)(y_1^2 + y_2^2) = (x_1 y_1 - x_2 y_2)^2 + (x_1 y_2 + x_2 y_1)^2$ |
| `sq_add_mul_sq_mul_sq_add_mul_sq` | the same with $x^2 + n y^2$ in place of $x^2 + y^2$ |
| `sum_four_sq_mul_sum_four_sq` | a product of two sums of four squares is a sum of four squares |
| `sum_eight_sq_mul_sum_eight_sq` | a product of two sums of eight squares is a sum of eight squares |
| `pow_four_add_four_mul_pow_four` | $a^4 + 4 b^4 = ((a - b)^2 + b^2)((a + b)^2 + b^2)$ |

The two-square identity is the multiplicativity of the norm $|z|^2$ of complex numbers, and the four-square identity is the multiplicativity of the quaternion norm of Chapter 8. The proof of each is `ring`. The four-square identity is the algebraic step in the proof that each natural number is a sum of four squares.

#### Geometric sums

The module `Mathlib.Algebra.Ring.GeomSum` computes the partial sums of a geometric series. The sum $\sum_{i < n} x^i$ is written `∑ i ∈ range n, x ^ i`, and the two-variable sum $\sum_{i < n} x^i y^{n - 1 - i}$ is written with `x ^ i * y ^ (n - 1 - i)`. The names contain `geom_sum` for one variable and `geom_sum₂` for two.

**Proposition.** In each ring, $\left(\sum_{i < n} x^i\right)(x - 1) = x^n - 1$.

*Proof.* Induction on $n$. For $n = 0$ both sides are $0$. For the step, $\sum_{i < n + 1} x^i = \sum_{i < n} x^i + x^n$, so the left side for $n + 1$ is $(x^n - 1) + x^n (x - 1) = x^{n + 1} - 1$. $\square$

The lemma is `geom_sum_mul`. The form with the factor on the left is `mul_geom_sum`, and the forms with $1 - x$ are `geom_sum_mul_neg` and `mul_neg_geom_sum`. For commuting $x$ and $y$, `Commute.geom_sum₂_mul` states $\left(\sum_{i < n} x^i y^{n - 1 - i}\right)(x - y) = x^n - y^n$, and `geom_sum₂_mul` is the commutative form. The proof is the same induction. In a field the sum is a quotient, but that form needs division and is in `Mathlib.Algebra.Field.GeomSum`. Over `ℕ`, `Nat.geomSum_eq` gives $\sum_{k < n} m^k = (m^n - 1)/(m - 1)$ for $m \ge 2$, with the truncated division.

The geometric sum gives divisibility results at once.

| Lean name | Statement |
|---|---|
| `sub_dvd_pow_sub_pow` | $x - y \mid x^n - y^n$ in a commutative ring |
| `Commute.sub_dvd_pow_sub_pow` | the same for commuting $x, y$ in a ring |
| `sub_one_dvd_pow_sub_one` | $x - 1 \mid x^n - 1$ |
| `pow_one_sub_dvd_pow_mul_sub_one` | $x^m - 1 \mid x^{m n} - 1$ |
| `dvd_pow_sub_one_of_dvd` | $a \mid b$ implies $r^a - 1 \mid r^b - 1$ |
| `Odd.add_dvd_pow_add_pow` | $x + y \mid x^n + y^n$ for odd $n$ |
| `Nat.sub_dvd_pow_sub_pow` | $x - y \mid x^n - y^n$ in `ℕ`, with truncated subtraction |

The proof of `sub_dvd_pow_sub_pow` is one line: `geom_sum₂_mul` writes $x^n - y^n$ as a multiple of $x - y$. For odd $n$, replace $y$ by $-y$. The lemma `neg_one_geom_sum` computes $\sum_{i < n} (-1)^i$, which is $0$ for even $n$ and $1$ for odd $n$. The lemmas `geom_sum_succ`, `geom_sum_zero`, `geom_sum_one` and `geom_sum_two` unfold small cases, and `RingHom.map_geom_sum` moves a ring homomorphism inside the sum.

#### Idempotent elements

An element $e$ is idempotent if $e^2 = e$. The predicate `IsIdempotentElem e` comes from the theory of monoids. The module `Mathlib.Algebra.Ring.Idempotent` adds the facts that use the addition. The main one is `IsIdempotentElem.one_sub`: if $e$ is idempotent, so is $1 - e$. *Proof.* $(1 - e)^2 = 1 - 2 e + e^2 = 1 - 2 e + e = 1 - e$. $\square$ The converse is in `IsIdempotentElem.one_sub_iff`, and the products are zero: `IsIdempotentElem.mul_one_sub_self` says $e (1 - e) = 0$. In the other direction, `IsIdempotentElem.of_mul_add` says that if $a b = 0$ and $a + b = 1$ then $a$ and $b$ are idempotent.

The map $e \mapsto 1 - e$ is a complement on the subtype of idempotents. The instance `IsIdempotentElem.instComplSubtype` defines it, with `IsIdempotentElem.coe_compl`, `IsIdempotentElem.compl_compl`, `IsIdempotentElem.zero_compl` and `IsIdempotentElem.one_compl`. For sums, `IsIdempotentElem.add` needs $a b + b a = 0$, and in a commutative ring `IsIdempotentElem.add_sub_mul` says that $a + b - a b$ is idempotent. This is the join of $a$ and $b$ in the Boolean algebra of idempotents of a commutative ring. Volume 9 uses these idempotents to split a ring as a product.

#### The associator

In a nonassociative ring the associator is $[x, y, z] = (x y) z - x (y z)$. The module `Mathlib.Algebra.Ring.Associator` defines `associator`, with `associator_apply` for the formula, and the trilinear form `AddMonoidHom.associator`. The lemma `associator_eq_zero_iff_associative` says that the associator vanishes exactly when the multiplication is associative, and `associator_eq_zero` records that it vanishes in a `NonUnitalRing`. The lemma `associator_cocycle` is the identity
$$a [b, c, d] - [a b, c, d] + [a, b c, d] - [a, b, c d] + [a, b, c] d = 0,$$
which holds in each nonassociative ring. The proof expands each term and cancels. The associator measures the failure of associativity in Jordan algebras and other nonassociative algebras.

#### Divisibility in a ring

The relation $a \mid b$ means $b = a c$ for some $c$. The module `Mathlib.Algebra.Ring.Divisibility.Basic` proves how it interacts with addition and negation.

| Lean name | Statement |
|---|---|
| `dvd_add` | $a \mid b$ and $a \mid c$ imply $a \mid b + c$ |
| `dvd_sub` | $a \mid b$ and $a \mid c$ imply $a \mid b - c$ |
| `dvd_add_right` | if $a \mid b$, then $a \mid b + c \iff a \mid c$ |
| `dvd_sub_comm` | $a \mid b - c \iff a \mid c - b$ |
| `dvd_neg`, `neg_dvd` | $a \mid -b \iff a \mid b$ and $-a \mid b \iff a \mid b$ |
| `Dvd.dvd.linear_comb` | $d \mid x$ and $d \mid y$ imply $d \mid a x + b y$ |
| `dvd_mul_sub_mul` | $k \mid a - b$ and $k \mid x - y$ imply $k \mid a x - b y$ |
| `min_pow_dvd_add` | $c^m \mid a$ and $c^n \mid b$ imply $c^{\min(m, n)} \mid a + b$ |

The names follow the pattern of the group lemmas: `dvd_add_right` keeps the right summand in the conclusion, and the dot forms `Dvd.dvd.add`, `Dvd.dvd.sub` and `Dvd.dvd.neg_right` work on a hypothesis `h : a ∣ b`. The lemma `dvd_mul_sub_mul` is the rule behind the compatibility of congruences with products.

The module `Mathlib.Algebra.Ring.Divisibility.Lemmas` treats nilpotent elements. If $x$ and $y$ commute and $x^n = 0$, then $(x + y)^m$ divides $y^p$ when $n + m \le p + 1$. This is `Commute.add_pow_dvd_pow_of_pow_eq_zero_right`, and the module has the variants with $x - y$ and with the roles of $x$ and $y$ swapped. The proof expands $y^p = ((x + y) - x)^p$ by the binomial theorem. The terms with $x^k$ for $k \ge n$ vanish, and the other terms have a factor $(x + y)^m$. The same module proves `dvd_mul_sub_mul_mul_left_of_dvd`: if $p$ divides $a x + b y$ and $c x + d y$, then $p$ divides $(a d - b c) x$. This is Cramer's rule for a $2 \times 2$ system. In an ordered ring, `Associated.abs_left` and `associated_abs_left_iff` say that $|x|$ is associated to $x$.

#### Common errors

1. The identities without `Commute` in the name need a commutative ring. In a ring such as the matrices, `sub_sq` does not apply, and the right lemma is `Commute.sub_sq` with a proof of `Commute a b`.
2. The geometric sum is indexed by `Finset.range n`, so it has $n$ terms, from $x^0$ to $x^{n - 1}$. The sum `∑ i ∈ range (n + 1), x ^ i` ends at $x^n$, and `geom_sum_mul` for it gives $x^{n + 1} - 1$.
3. In `ℕ` the subtraction is truncated. The lemma `sub_dvd_pow_sub_pow` needs a commutative ring, and over `ℕ` the right form is `Nat.sub_dvd_pow_sub_pow`.

### Exercises

1. (A) Prove `Commute.sq_sub_sq` from the ring axioms, and find $2 \times 2$ matrices $a, b$ with $a^2 - b^2 \ne (a + b)(a - b)$.
2. (A) Show that $x^2 = 1$ has four solutions in $\mathbb{Z}/8$, and explain why `sq_eq_one_iff` does not apply there.
3. (A) Use `geom_sum_mul` to show that $1 - x$ is a unit when $x$ is nilpotent, with inverse $\sum_{i < n} x^i$ for $x^n = 0$.
4. (B) Prove that $2^n - 1$ divides $2^{m n} - 1$, and deduce that $2^k - 1$ is not prime when $k$ is composite.
5. (B) Let $e$ be idempotent in a ring $R$. Show that $e R e$ is a ring with identity $e$, and that $e R e = R$ only when $e = 1$.
6. (C) Prove that the idempotents of a commutative ring form a Boolean algebra under $e \wedge f = e f$, $e \vee f = e + f - e f$ and $e^c = 1 - e$.

### Reference

<?reference?>
