---
title: Ordered rings
kind: theory
modules:
  - Mathlib.Algebra.Order.Ring.Defs
  - Mathlib.Algebra.Order.Ring.Abs
explains:
  E3: [IsOrderedRing, IsStrictOrderedRing, sq_nonneg]
  E2: [IsOrderedRing.of_mul_nonneg, IsStrictOrderedRing.of_mul_pos, IsOrderedRing.toCharZero, IsStrictOrderedRing.isDomain, mul_self_nonneg, mul_self_add_mul_self_eq_zero, neg_one_lt_zero, abs_mul, Int.instIsStrictOrderedRing]
  E1: auto
families: []
requires: [V06.C03, V04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Ordered rings

### Overview

The integers, the rationals and the reals carry an order that respects the ring operations: one can add an inequality to both sides, and one can multiply it by a nonnegative number. A ring with such an order is an ordered ring. This section defines ordered rings, proves the first rules of computation with inequalities, and shows that the order is a strong constraint on the ring. A nontrivial ordered ring has characteristic zero. In a linearly ordered ring every square is nonnegative, so $-1$ is negative and the complex numbers carry no such order. The positive elements of a linear order form a positive cone, and each positive cone gives a linear order. With the cones, the section proves that $\mathbb{Z}$ has exactly one ordering, and it orders $\mathbb{R}[X]$ so that $X$ is larger than every integer.

Mathlib does not have one class for "ordered ring". It has an order (a `PartialOrder` or a `LinearOrder`), a ring structure, and a mixin class, `IsOrderedRing` or `IsStrictOrderedRing`, that ties them. Each later section of the chapter uses this design.

### Definitions

**Definition (Ordered semiring).** An ordered semiring is a semiring $R$ with a partial order $\le$ such that, for all $a, b, c \in R$:

1. $a \le b$ implies $a + c \le b + c$;
2. $0 \le 1$;
3. $0 \le c$ and $a \le b$ imply $c a \le c b$ and $a c \le b c$.

An ordered ring is an ordered semiring that is a ring. If the order is linear, $R$ is a linearly ordered semiring or ring.

In a ring, condition 3 is the same as the condition "$0 \le a$ and $0 \le b$ imply $0 \le a b$". Indeed, if $a \le b$ then $0 \le b - a$ by condition 1 (add $-a$), so $0 \le c(b - a) = c b - c a$, and condition 1 again gives $c a \le c b$. The converse is the case $a = 0$ of condition 3.

**Definition (Strict ordered semiring).** A strict ordered semiring is a nontrivial semiring $R$ with a partial order such that:

1. $a < b$ implies $a + c < b + c$, and $a + c \le b + c$ implies $a \le b$;
2. $0 \le 1$;
3. $0 < c$ and $a < b$ imply $c a < c b$ and $a c < b c$.

The ring $\mathbb{Z}$ with its usual order is a strict ordered ring. So are $\mathbb{Q}$ and $\mathbb{R}$. The strict form matters: in a strict ordered ring the product of two positive elements is positive, not only nonnegative.

*Remarks.* An ordered ring in which $a b = 0$ is possible for positive $a$ and $b$ exists: take $\mathbb{Z} \times \mathbb{Z}$ with the order $(a, b) \le (c, d)$ if and only if $a \le c$ and $b \le d$. Then $(1, 0) > 0$ and $(0, 1) > 0$, but their product is $0$. This order is partial, not linear, and the ring is an ordered ring but not a strict one.

::: mathlib
`IsOrderedRing` · `Mathlib.Algebra.Order.Ring.Defs`

A mixin: `IsOrderedRing R` takes `[Semiring R] [PartialOrder R]` and is a `Prop`. Its fields are the classes `IsOrderedAddMonoid R` (condition 1), `ZeroLEOneClass R` (condition 2), and `PosMulMono R` and `MulPosMono R` (condition 3, for left and right multiplication). A linearly ordered commutative ring is written `[CommRing R] [LinearOrder R] [IsOrderedRing R]`. Since the class is a `Prop`, it adds no data: the order and the ring are given first, and the class only says that they fit.

<?decl IsOrderedRing?>
:::

::: mathlib
`IsStrictOrderedRing` · `Mathlib.Algebra.Order.Ring.Defs`

The strict form, with the fields `IsOrderedCancelAddMonoid R`, `ZeroLEOneClass R`, `Nontrivial R`, `PosMulStrictMono R` and `MulPosStrictMono R`. The instance `IsStrictOrderedRing.toIsOrderedRing` gives the weak form. The integers have the instance `Int.instIsStrictOrderedRing`, and $\mathbb{Q}$ and $\mathbb{R}$ have similar ones. Older code used bundled classes such as `LinearOrderedField`. A reader of it must translate `[LinearOrderedField K]` into `[Field K] [LinearOrder K] [IsStrictOrderedRing K]`.

<?decl IsStrictOrderedRing?>
:::

::: mathlib
`IsOrderedRing.of_mul_nonneg` · `Mathlib.Algebra.Order.Ring.Defs`

The criterion of the remark after Definition (Ordered semiring): in a ring with an ordered additive group, `0 ≤ 1` and the closure of the nonnegative elements under products give `IsOrderedRing R`. The strict analogue is `IsStrictOrderedRing.of_mul_pos`. These are the usual way to build an instance by hand.

<?decl IsOrderedRing.of_mul_nonneg?>
:::

**Definition (Positive cone).** Let $R$ be a commutative ring. A positive cone of $R$ is a subset $P \subseteq R$ with:

1. $P + P \subseteq P$ and $P P \subseteq P$;
2. $P \cup (-P) = R$;
3. $P \cap (-P) = \{0\}$.

Here $-P = \{-a : a \in P\}$.

**Definition (Absolute value).** In a linearly ordered ring, $|a| = a$ if $a \ge 0$ and $|a| = -a$ if $a < 0$. Equivalently $|a| = \max(a, -a)$.

### Theorems and proofs

**Proposition (Rules for inequalities).** Let $R$ be an ordered ring and let $a, b, c, d \in R$.

1. $a \le b$ if and only if $0 \le b - a$.
2. $a \le b$ and $c \le d$ imply $a + c \le b + d$.
3. $a \le b$ and $c \le 0$ imply $c b \le c a$.
4. $a \le b$ if and only if $-b \le -a$.

*Proof.* (1) Add $-a$ to both sides of $a \le b$ to get $0 \le b - a$. Add $a$ to both sides of $0 \le b - a$ to get back $a \le b$. (2) The inequality $a \le b$ gives $a + c \le b + c$, and $c \le d$ gives $b + c \le b + d$. Transitivity gives $a + c \le b + d$. (4) Add $-a - b$ to both sides of $a \le b$. (3) By (4), $0 \le -c$. Then $(-c) a \le (-c) b$ by condition 3, that is, $-(c a) \le -(c b)$, and (4) gives $c b \le c a$. $\square$

**Theorem (Characteristic zero).** A nontrivial ordered ring $R$ has characteristic zero: $n \cdot 1 \ne 0$ for each integer $n \ge 1$.

*Proof.* First, $1 \le n \cdot 1$ for each $n \ge 1$, by induction. For $n = 1$ it is equality. If $1 \le n \cdot 1$, then $(n + 1) \cdot 1 = n \cdot 1 + 1 \ge n \cdot 1 + 0 \ge 1$, where the first step adds $n \cdot 1$ to $1 \ge 0$. Now assume $n \cdot 1 = 0$ for some $n \ge 1$. Then $0 \le 1 \le n \cdot 1 = 0$, so $1 = 0$ by antisymmetry. This contradicts the hypothesis that $R$ is nontrivial. $\square$

So $\mathbb{Z}/n$ for $n \ge 2$ has no order that makes it an ordered ring, and neither has a finite field. The theorem uses only the partial order, not a linear one.

::: mathlib
`IsOrderedRing.toCharZero` · `Mathlib.Algebra.Order.Ring.Defs`

The theorem for a nontrivial ordered ring. For a strict ordered semiring the result is the instance `IsStrictOrderedRing.toCharZero`, so `CharZero R` is found by instance search, and lemmas such as `Nat.cast_injective` apply with no extra work.

<?decl IsOrderedRing.toCharZero?>
:::

**Theorem (Squares are nonnegative).** Let $R$ be a linearly ordered ring. Then $a^2 \ge 0$ for each $a \in R$. If $R$ is nontrivial, then $0 < 1$ and $-1 < 0$.

*Proof.* The order is linear, so $a \ge 0$ or $a \le 0$. If $a \ge 0$, then condition 3 with $c = a$ applied to $0 \le a$ gives $a \cdot 0 \le a \cdot a$, so $0 \le a^2$. If $a \le 0$, then $0 \le -a$ by the rules above, and the first case gives $0 \le (-a)(-a) = a^2$. For the second claim, $1 = 1^2 \ge 0$, and $1 \ne 0$ in a nontrivial ring, so $0 < 1$. Adding $-1$ to both sides gives $-1 < 0$. $\square$

::: mathlib
`sq_nonneg` · `Mathlib.Algebra.Order.Ring.Unbundled.Basic`

`0 ≤ a ^ 2`, stated with the small classes `PosMulMono`, `AddLeftMono` and `ExistsAddOfLE` so that it also holds for semirings such as `ℕ`. The form with a product is `mul_self_nonneg : 0 ≤ a * a`. The tactic `positivity` knows both. The second claim of the theorem is `neg_one_lt_zero`.

<?decl sq_nonneg?>
:::

**Corollary (The complex numbers are not ordered).** There is no linear order on $\mathbb{C}$ that makes it an ordered ring.

*Proof.* Assume such an order exists. The ring $\mathbb{C}$ is nontrivial, so $-1 < 0$ by the theorem. But $-1 = i^2$, and squares are nonnegative, so $-1 \ge 0$. This is a contradiction. $\square$

**Theorem (A strict linear order has no zero divisors).** Let $R$ be a linearly ordered strict ring. If $a b = 0$, then $a = 0$ or $b = 0$. So $R$ is an integral domain if it is commutative. In particular $a^2 + b^2 = 0$ implies $a = b = 0$.

*Proof.* Assume $a \ne 0$ and $b \ne 0$. By linearity each is positive or negative. If $a > 0$ and $b > 0$, then $a b > a \cdot 0 = 0$ by strict condition 3. If $a < 0$ and $b > 0$, then $-a > 0$ and $-(a b) = (-a) b > 0$, so $a b < 0$. The two other cases are the same. In each case $a b \ne 0$. For the last claim, $a^2 \ge 0$ and $b^2 \ge 0$, so $a^2 + b^2 = 0$ gives $0 \le a^2 = -b^2 \le 0$, hence $a^2 = 0$, and $a = 0$ because there are no zero divisors. In the same way $b = 0$. $\square$

::: mathlib
`IsStrictOrderedRing.isDomain` · `Mathlib.Algebra.Order.Ring.Defs`

The instance `IsDomain R` for a linearly ordered strict semiring with `ExistsAddOfLE R` (every ring has this). So the cancellation lemmas of Chapter 3 hold in each linearly ordered field. The sum of two squares is `mul_self_add_mul_self_eq_zero : a * a + b * b = 0 ↔ a = 0 ∧ b = 0`.

<?decl IsStrictOrderedRing.isDomain?>
:::

**Theorem (Positive cones and orders).** Let $R$ be a commutative ring.

1. If $\le$ is a linear order that makes $R$ an ordered ring, then $P = \{a \in R : 0 \le a\}$ is a positive cone.
2. If $P$ is a positive cone, then the relation $a \le_P b \iff b - a \in P$ is a linear order that makes $R$ an ordered ring, and its set of nonnegative elements is $P$.

*Proof.* (1) If $a, b \ge 0$, then $a + b \ge 0 + 0 = 0$ and $a b \ge 0$, so $P$ is closed under sums and products. For each $a$, either $a \ge 0$, so $a \in P$, or $a \le 0$, so $-a \in P$ and $a \in -P$. If $a \in P \cap (-P)$, then $0 \le a$ and $0 \le -a$, so $a \le 0$, and $a = 0$.

(2) Reflexivity: $0 \in P$, since $0 \in P \cup (-P)$ and $-0 = 0$. So $a - a \in P$. Transitivity: if $b - a \in P$ and $c - b \in P$, then $c - a = (c - b) + (b - a) \in P$. Antisymmetry: if $b - a \in P$ and $a - b \in P$, then $b - a \in P \cap (-P) = \{0\}$. Linearity: $b - a \in P$ or $b - a \in -P$, and the second case says $a - b \in P$. Addition: $(b + c) - (a + c) = b - a$. Products: if $a, b \in P$ then $a b \in P$, and the remark after Definition (Ordered semiring) turns this into condition 3. The condition $0 \le_P 1$: each square is in $P$, because $x \in P$ gives $x^2 \in P P \subseteq P$ and $-x \in P$ gives $x^2 = (-x)^2 \in P$. So $1 = 1^2 \in P$. Finally $0 \le_P a$ means $a - 0 = a \in P$. $\square$

**Theorem (The order of $\mathbb{Z}$ is unique).** The usual order is the only linear order that makes $\mathbb{Z}$ an ordered ring.

*Proof.* By the theorem on cones, it is enough to show that a positive cone $P$ of $\mathbb{Z}$ is $\mathbb{N} = \{0, 1, 2, \dots\}$. Squares are in $P$, so $1 \in P$. By induction $n = 1 + \dots + 1 \in P$ for each $n \ge 1$, and $0 \in P$, so $\mathbb{N} \subseteq P$. If $-n \in P$ for some $n \ge 1$, then $-n \in P$ and $-n = -(n) \in -P$, so $-n = 0$, a contradiction. So $P$ contains no negative integer, and $P = \mathbb{N}$. $\square$

**Theorem (Absolute value).** In a linearly ordered ring $R$, for all $a, b$: $|a| \ge 0$, $|a b| = |a| |b|$, $|a|^2 = a^2$, and $|a + b| \le |a| + |b|$.

*Proof.* If $a \ge 0$ then $|a| = a \ge 0$, and if $a < 0$ then $|a| = -a > 0$. For the product, $|a| = \varepsilon a$ and $|b| = \delta b$ with $\varepsilon, \delta \in \{1, -1\}$. Then $|a| |b| = \varepsilon \delta a b$, which is $\pm a b$ and is nonnegative, as a product of two nonnegative elements. For each $x$, the element $|x|$ is the only nonnegative element of the set $\{x, -x\}$: at least one of $x$ and $-x$ is nonnegative by linearity, and if both are, then $x = 0 = -x$. Apply this to $x = a b$: the element $|a| |b|$ is in $\{a b, -a b\}$ and is nonnegative, so $|a| |b| = |a b|$. Then $|a|^2 = |a| |a| = |a a| = a^2$, since $a^2 \ge 0$. For the triangle inequality: $a \le |a|$ and $b \le |b|$ give $a + b \le |a| + |b|$, and $-a \le |a|$ and $-b \le |b|$ give $-(a + b) \le |a| + |b|$. Since $|a + b|$ is $a + b$ or $-(a + b)$, it is at most $|a| + |b|$. $\square$

::: mathlib
`abs_mul` · `Mathlib.Algebra.Order.Ring.Abs`

`|a * b| = |a| * |b|` for a linearly ordered ring. The absolute value `|a|` is the lattice notation for `a ⊔ -a`, defined for any lattice-ordered additive group in Volume 4. The triangle inequality is `abs_add_le`, which needs only an ordered additive group.

<?decl abs_mul?>
:::

### Examples

**Example (An order on $\mathbb{R}[X]$).** Let $P \subseteq \mathbb{R}[X]$ be the set of the polynomials that are $0$ or have a positive leading coefficient. Then $P$ is a positive cone. Sums: let $f, g \in P$ be nonzero. If $\deg f > \deg g$, the leading coefficient of $f + g$ is that of $f$, which is positive. If the degrees are equal, the coefficient of $X^{\deg f}$ in $f + g$ is the sum of two positive numbers, so it is positive and it is the leading coefficient. Products: the leading coefficient of $f g$ is the product of the leading coefficients, because $\mathbb{R}$ is a domain. A nonzero $f$ is in $P$ or in $-P$ by the sign of its leading coefficient, and not in both. So $\mathbb{R}[X]$ is a linearly ordered ring. In this order $X - n \in P$ for each integer $n$, since its leading coefficient is $1$. So $X > n$ for every integer $n$: the element $X$ is infinitely large. Section 3 uses this example.

**Counterexample (Positive characteristic).** The ring $\mathbb{Z}/3$ has no order that makes it an ordered ring. By the theorem on the characteristic, $1 + 1 + 1 = 0$ would force $1 = 0$. To see it by hand with any partial order: $0 \le 1$ gives $1 \le 2$ and $2 \le 3 = 0$, so $1 \le 0$, and antisymmetry gives $0 = 1$.

**Counterexample (A partial order on $\mathbb{C}$).** The corollary forbids a linear order on $\mathbb{C}$, but a partial order is possible. Put $z \le w$ if $\operatorname{Re} z \le \operatorname{Re} w$ and $\operatorname{Im} z = \operatorname{Im} w$. Then the elements $\ge 0$ are the real numbers $x \ge 0$, a set closed under sums and products, and $\mathbb{C}$ is an ordered ring. The elements $i$ and $0$ are not comparable, and the square $i^2 = -1$ is not $\ge 0$. So the theorem on squares needs the linear order.

::: mathlib
`Complex.partialOrder` · `Mathlib.Analysis.Complex.Order`

The partial order of the counterexample, with `Complex.le_def : z ≤ w ↔ z.re ≤ w.re ∧ z.im = w.im`. It is a scoped instance, active only after `open scoped ComplexOrder`, because a global instance would give a wrong order to the users who never want one. It is used in the theory of positive operators and C*-algebras (Volume 16).

<?decl Complex.partialOrder?>
:::

### The library around it

The order lemmas of Mathlib are stated with the smallest classes that prove them. For multiplication these are `PosMulMono` (left multiplication by a nonnegative element is monotone), `MulPosMono` (the same on the right), and their strict forms `PosMulStrictMono` and `MulPosStrictMono`. The mixins `IsOrderedRing` and `IsStrictOrderedRing` provide all four, so a lemma stated with the small classes applies to every ordered ring. So `sq_nonneg` also applies to the semiring `ℕ`.

The names follow the shape of the statement: `mul_pos : 0 < a → 0 < b → 0 < a * b`, `mul_nonneg`, `mul_neg_of_pos_of_neg`, `mul_le_mul`. The tactics do most of the work in practice. The tactic `positivity` proves goals `0 < e` and `0 ≤ e` from the shape of `e`. The tactic `linarith` proves linear inequalities from hypotheses, and `nlinarith` adds products of pairs of hypotheses.

Common errors of a learner:

- Writing `[LinearOrderedRing R]`. The bundled classes are gone. Write `[Ring R] [LinearOrder R] [IsStrictOrderedRing R]`.
- Forgetting the side condition on the sign. `mul_le_mul_of_nonneg_left` needs `0 ≤ c`, and with `c < 0` the inequality turns. The rule (3) above is `mul_le_mul_of_nonpos_left`.
- Expecting `sq_nonneg` under `[PartialOrder R]` alone. It needs a linear order, as the partial order on $\mathbb{C}$ shows.
- Confusing `IsOrderedRing` with `IsStrictOrderedRing`. Only the strict form gives `mul_pos` and `IsDomain`.

### Exercises

1. (A) In an ordered ring, prove that $a \le b$ and $0 \le c \le d$ and $0 \le a$ imply $a c \le b d$. Hint: compare both sides with $b c$.
2. (A) Show that in a linearly ordered ring $a^2 + b^2 \ge 2 a b$. Hint: $(a - b)^2 \ge 0$.
3. (A) Show that $\mathbb{Z}[i]$ has no linear order that makes it an ordered ring.
4. (B) Show that in a strict linearly ordered ring, $0 < a < b$ implies $a^2 < b^2$, and that the converse holds for $a, b \ge 0$.
5. (B) Show that $\mathbb{Z}[\sqrt 2] = \{a + b \sqrt 2 : a, b \in \mathbb{Z}\}$ has exactly two linear orders that make it an ordered ring. Hint: a cone is determined by the sign of $\sqrt 2$, and the automorphism $\sqrt 2 \mapsto -\sqrt 2$ exchanges the two orders.
6. (B) In the order of $\mathbb{R}[X]$ above, find the signs of $X^2 - 100 X$ and of $X^3 - X^5$. Show that no $f \in \mathbb{R}[X]$ satisfies $0 < f < c$ for every real $c > 0$. Hint: a positive polynomial of degree $d \ge 1$ is larger than every constant.
7. (B) Show that a ring with a nonzero nilpotent element has no linear order that makes it a strict ordered ring.
8. (C) Show that every positive cone $P$ of a field $K$ satisfies: each nonzero sum of squares is in $P$, and $-1$ is not a sum of squares. Deduce that a field in which $-1$ is a sum of squares has no ordering. Apply it to $\mathbb{Q}(i)$ and to $\mathbb{F}_p$.
9. (C) Let $R$ be a linearly ordered strict commutative ring and let $R[X]$ have the cone of the polynomials with positive leading coefficient. Show that the inclusion $R \to R[X]$ preserves the order and that the cone of the polynomials with positive lowest nonzero coefficient gives a second order, in which $0 < X < r$ for each $r > 0$ in $R$.

### Notes and history

Ordered fields were studied by Artin and Schreier in 1926 and 1927, in the work that founded real algebra and led to Artin's solution of Hilbert's 17th problem: a polynomial that is nonnegative on $\mathbb{R}^n$ is a sum of squares of rational functions. The positive cone is their tool. Hilbert had used the order of non-archimedean fields such as $\mathbb{R}(X)$ in the *Grundlagen der Geometrie* of 1899. The textbook reference is Jacobson, *Basic Algebra I*, Chapter 5.

In Mathlib the ordered algebraic classes were bundled for many years: `OrderedSemiring`, `StrictOrderedRing`, `LinearOrderedField` and others, each extending a ring class and an order class. In 2025 the library moved to the unbundled form described here, with `IsOrderedRing` and `IsStrictOrderedRing` as `Prop` mixins over a separate order. The change removed conflicts between the order and the algebra and made the hierarchy smaller.

### Reference

<?reference?>
