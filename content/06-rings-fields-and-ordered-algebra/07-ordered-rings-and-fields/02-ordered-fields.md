---
title: Ordered fields
kind: theory
modules:
  - Mathlib.Algebra.Order.Field.Basic
  - Mathlib.Algebra.Order.Ring.Rat
  - Mathlib.Algebra.Ring.IsFormallyReal
  - Mathlib.Algebra.Ring.SumsOfSquares
  - Mathlib.Algebra.Ring.Semireal.Defs
  - Mathlib.Algebra.Ring.Subsemiring.Support
explains:
  E3: [Rat.instIsStrictOrderedRing, IsFormallyReal]
  E2: [inv_pos, inv_le_inv₀, one_div_le_one_div, div_le_iff₀, le_div_iff₀, half_pos, left_lt_add_div_two, add_div_two_lt_right, IsFormallyReal.instOfIsStrictOrderedRing]
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

## Ordered fields

### Overview

An ordered field is a field with a linear order that makes it a strict ordered ring. The rational numbers and the real numbers are the main examples. In a field one can divide, so the rules of the previous section gain rules for inverses and quotients: the inverse of a positive element is positive, and inversion reverses inequalities between positive elements. This section proves these rules, and it proves two facts about the rational numbers. First, $\mathbb{Q}$ has exactly one ordering. Second, every ordered field contains a copy of $\mathbb{Q}$, and the inclusion preserves the order. The rationals are thus the smallest ordered field. The section then orders the field $\mathbb{R}(x)$ of rational functions so that $x$ is larger than every real number. This field is the first example of an ordered field with infinite and infinitesimal elements. Last, the section defines formally real fields, the fields in which $-1$ is not a sum of squares, and states the theorem of Artin and Schreier that these are the fields that admit an order.

### Definitions

**Definition (Ordered field).** An ordered field is a field $K$ with a linear order $\le$ such that $K$ is a strict ordered ring: $a \le b$ implies $a + c \le b + c$, and $0 < a$ and $0 < b$ imply $0 < a b$.

By the previous section, an ordered field has characteristic zero, every square is nonnegative, and $1 > 0$. The set $P = \{a : a > 0\}$ is a positive cone: it is closed under addition and multiplication, and for each $a$ exactly one of $a \in P$, $a = 0$ and $-a \in P$ holds. Conversely each positive cone of a field gives a linear order by $a < b$ if and only if $b - a \in P$. So to order a field is to choose a positive cone.

**Definition (Mediant).** Let $a, c \in \mathbb{Z}$ and $b, d \in \mathbb{Z}_{>0}$. The mediant of the fractions $a/b$ and $c/d$ is the fraction $(a + c)/(b + d)$.

The mediant is a function of the pairs $(a, b)$ and $(c, d)$, not of the rational numbers $a/b$ and $c/d$. A counterexample below shows this.

**Definition (Formally real field).** A field $K$ is formally real if $-1$ is not a sum of squares in $K$.

**Definition (Infinite and infinitesimal elements).** Let $K$ be an ordered field. An element $a \in K$ is infinite if $|a| > n$ for every $n \in \mathbb{N}$. An element $a \ne 0$ is infinitesimal if $|a| < 1/n$ for every integer $n \ge 1$.

::: mathlib
`Rat.instIsStrictOrderedRing` · `Mathlib.Algebra.Order.Ring.Rat`

Mathlib has no class `LinearOrderedField` at this commit. An ordered field is written with three classes: `[Field K] [LinearOrder K] [IsStrictOrderedRing K]`. The instance `Rat.instIsStrictOrderedRing` says that the usual order on `ℚ` fits its ring structure. With `Rat.instField` and the linear order on `ℚ`, it makes `ℚ` an ordered field for instance search. Each lemma on ordered fields then applies to `ℚ` with no further work.

<?decl Rat.instIsStrictOrderedRing?>
:::

### Theorems and proofs

**Proposition (Inverses).** Let $K$ be an ordered field and let $a, b, c \in K$.

1. If $a > 0$, then $a^{-1} > 0$.
2. If $0 < a < b$, then $0 < b^{-1} < a^{-1}$.
3. If $c > 0$, then $a / c \le b$ if and only if $a \le b c$.

*Proof.* (1) The element $a^{-1}$ is not zero, since $a a^{-1} = 1 \ne 0$. Suppose $a^{-1} < 0$. Then $-a^{-1} > 0$, and the product $a \cdot (-a^{-1}) = -1$ is positive. This contradicts $1 > 0$. So $a^{-1} > 0$.

(2) By (1), $a^{-1} > 0$ and $b^{-1} > 0$, so $a^{-1} b^{-1} > 0$. Multiply the inequality $a < b$ by the positive element $a^{-1} b^{-1}$. The left side becomes $a \cdot a^{-1} b^{-1} = b^{-1}$, and the right side becomes $b \cdot a^{-1} b^{-1} = a^{-1}$. So $b^{-1} < a^{-1}$.

(3) Suppose $a / c \le b$. Multiply by $c > 0$: the left side becomes $(a c^{-1}) c = a$, so $a \le b c$. Conversely, suppose $a \le b c$. Multiply by $c^{-1}$, which is positive by (1): this gives $a c^{-1} \le b c c^{-1} = b$. $\square$

::: mathlib
`inv_pos` · `Mathlib.Algebra.Order.GroupWithZero.Basic`

The statement is `0 < a⁻¹ ↔ 0 < a`. It holds in a group with zero with a partial order and the class `PosMulReflectLT`, so it covers ordered fields and also the positive part of more general structures. The proof of the reverse direction is part (1) applied to $a^{-1}$, since $(a^{-1})^{-1} = a$.

<?decl inv_pos?>
:::

::: mathlib
`inv_le_inv₀` · `Mathlib.Algebra.Order.GroupWithZero.Basic`

The statement is `0 < a → 0 < b → (a⁻¹ ≤ b⁻¹ ↔ b ≤ a)`. The suffix `₀` marks the version for a group with zero, where both elements must be positive. The form with `1 / a` is `one_div_le_one_div`. Both are part (2) of the proposition, in the form of an equivalence.

<?decl inv_le_inv₀?>
:::

::: mathlib
`div_le_iff₀` · `Mathlib.Algebra.Order.GroupWithZero.Basic`

The statement is `0 < c → (b / c ≤ a ↔ b ≤ a * c)`. Its partner `le_div_iff₀` is `0 < c → (a ≤ b / c ↔ a * c ≤ b)`. These two lemmas clear denominators in a proof. A common pattern is `rw [div_le_iff₀ hc]` followed by a computation in the ring, often with `nlinarith` or `ring_nf`.

<?decl div_le_iff₀?>
:::

**Proposition (Density).** In an ordered field, if $a < b$ then $a < (a + b)/2 < b$.

*Proof.* The element $2 = 1 + 1$ is positive. From $a < b$ add $a$ to both sides: $2a < a + b$. Multiply by $1/2$, which is positive by part (1) of the proposition on inverses. So $a < (a + b)/2$. In the same way $a + b < 2b$ gives $(a + b)/2 < b$. $\square$

So no ordered field has a least positive element: if $a > 0$, then $0 < a/2 < a$.

::: mathlib
`left_lt_add_div_two` · `Mathlib.Algebra.Order.Field.Basic`

The statement is `a < (a + b) / 2 ↔ a < b`. Its partner `add_div_two_lt_right` is `(a + b) / 2 < b ↔ a < b`, and `half_pos` is `0 < a → 0 < a / 2`. The hypotheses are `[Semifield α] [PartialOrder α] [IsStrictOrderedRing α]`, so the lemmas hold in each ordered field and in the nonnegative part of one.

<?decl left_lt_add_div_two?>
:::

**Proposition (Mediant).** Let $b, d > 0$ be integers and $a/b < c/d$. Then
$$\frac{a}{b} < \frac{a + c}{b + d} < \frac{c}{d}.$$

*Proof.* The hypothesis $a/b < c/d$ is equivalent to $a d < b c$, by clearing the positive denominators. Compute
$$\frac{a + c}{b + d} - \frac{a}{b} = \frac{b(a + c) - a(b + d)}{b(b + d)} = \frac{b c - a d}{b(b + d)}.$$
The numerator is positive and the denominator is positive, so the difference is positive. In the same way
$$\frac{c}{d} - \frac{a + c}{b + d} = \frac{c(b + d) - d(a + c)}{d(b + d)} = \frac{b c - a d}{d(b + d)} > 0. \quad \square$$

**Theorem (The order of $\mathbb{Q}$ is unique).** The field $\mathbb{Q}$ has exactly one ordering: the usual one.

*Proof.* Let $P$ be a positive cone of $\mathbb{Q}$. It suffices to show that $P$ contains every positive rational. Then $P$ contains no negative rational $-r$, since $r$ and $-r$ are not both in $P$. And $P$ does not contain $0$. So $P$ equals the set of positive rationals.

The element $1 = 1^2$ is a nonzero square, so $1 \in P$. Since $P$ is closed under addition, $n = 1 + \dots + 1 \in P$ for each integer $n \ge 1$. By part (1) of the proposition on inverses, $1/n \in P$. A positive rational has the form $m/n = m \cdot (1/n)$ with $m, n \ge 1$. Both factors are in $P$, so $m/n \in P$. $\square$

**Theorem (Every ordered field contains $\mathbb{Q}$).** Let $K$ be an ordered field. There is a unique ring homomorphism $\varphi : \mathbb{Q} \to K$. It is injective, and $r < s$ implies $\varphi(r) < \varphi(s)$.

*Proof.* For $n \in \mathbb{Z}$ write $n_K = n \cdot 1_K$. The map $n \mapsto n_K$ is the unique ring homomorphism $\mathbb{Z} \to K$. Since $K$ has characteristic zero, $n_K \ne 0$ for $n \ne 0$. Define
$$\varphi\left(\frac{m}{n}\right) = m_K \, n_K^{-1} \quad (n \ne 0).$$
The value does not depend on the fraction. If $m/n = m'/n'$, then $m n' = m' n$ in $\mathbb{Z}$, so $m_K n'_K = m'_K n_K$ in $K$. Multiply by $n_K^{-1} n'^{-1}_K$ to get $m_K n_K^{-1} = m'_K n'^{-1}_K$. The rules for fractions in a field give
$$\varphi\left(\frac{m}{n} + \frac{m'}{n'}\right) = \frac{(m n' + m' n)_K}{(n n')_K} = \frac{m_K}{n_K} + \frac{m'_K}{n'_K}$$
and in the same way $\varphi$ respects products and sends $1$ to $1$. So $\varphi$ is a ring homomorphism. It is unique, because a ring homomorphism must send $n$ to $n_K$, and then $m/n$ to $m_K n_K^{-1}$.

Now let $r = m/n > 0$ with $m, n \ge 1$. Then $m_K = 1 + \dots + 1 > 0$ and $n_K > 0$, so $\varphi(r) = m_K n_K^{-1} > 0$ by the proposition on inverses. If $r < s$, then $s - r > 0$, so $\varphi(s) - \varphi(r) = \varphi(s - r) > 0$. This shows that $\varphi$ is strictly increasing, and so injective. $\square$

The two theorems together say that $\mathbb{Q}$ with its order is the prime field of every ordered field, and that it sits inside the order in the expected way.

::: mathlib
`Rat.cast_strictMono` · `Mathlib.Data.Rat.Cast.Order`

The map of the theorem is the coercion `Rat.cast : ℚ → K`, written `(q : K)`. As a ring homomorphism it is `Rat.castHom K`, which needs only `[DivisionRing K] [CharZero K]`. The lemma `Rat.cast_strictMono` states `StrictMono Rat.cast` for `[Field K] [LinearOrder K] [IsStrictOrderedRing K]`. The lemmas `Rat.cast_le` and `Rat.cast_lt` give the equivalences `(r : K) ≤ s ↔ r ≤ s` and `(r : K) < s ↔ r < s`. The tactic `push_cast` moves the coercion inward through sums and products.

<?decl Rat.cast_strictMono?>
:::

**Proposition (Ordered fields are formally real).** Let $K$ be an ordered field and $a_1, \dots, a_n \in K$. If $a_1^2 + \dots + a_n^2 = 0$, then every $a_i = 0$. In particular $-1$ is not a sum of squares.

*Proof.* Suppose some $a_j \ne 0$. Then $a_j^2 > 0$, and the other squares are $\ge 0$. So the sum is $\ge a_j^2 > 0$, and it is not zero. For the second claim, suppose $-1 = b_1^2 + \dots + b_n^2$. Then $1^2 + b_1^2 + \dots + b_n^2 = 0$ with $1 \ne 0$. This contradicts the first claim. $\square$

**Theorem (Artin and Schreier).** A field admits an ordering if and only if it is formally real.

The proof of the converse uses Zorn's lemma on the set of subsets of $K$ that contain every square, are closed under addition and multiplication, and do not contain $-1$. A formally real field makes this set nonempty, since the sums of squares form such a subset. A maximal element is a positive cone together with $0$. This section does not give the details.

::: mathlib
`IsFormallyReal` · `Mathlib.Algebra.Ring.IsFormallyReal`

`IsFormallyReal R` is a `Prop` class over `[AddCommMonoid R] [Mul R]`. Its field says that `0` is not a nonempty sum of nonzero squares (`¬ IsSumNonzeroSq 0`). This is the first claim of the proposition. The form avoids subtraction, so it makes sense in a semiring, and for a field it is equivalent to the definition with $-1$. The instance `IsFormallyReal.instOfIsStrictOrderedRing` is the proposition: each linearly ordered strict ring is formally real. A second instance, `IsFormallyReal.instIsReduced`, shows that a formally real ring has no nonzero nilpotent elements. The theorem of Artin and Schreier is not in Mathlib at this commit.

<?decl IsFormallyReal?>
:::

### Examples

**Example (The mediants of $0/1$ and $1/1$).** Start with the fractions $0/1$ and $1/1$. Their mediant is $1/2$. The mediants of $0/1, 1/2$ and of $1/2, 1/1$ are $1/3$ and $2/3$. One more step gives $1/4, 2/5, 3/5, 3/4$. The fractions at each step lie in increasing order:
$$\frac{0}{1} < \frac{1}{4} < \frac{1}{3} < \frac{2}{5} < \frac{1}{2} < \frac{3}{5} < \frac{2}{3} < \frac{3}{4} < \frac{1}{1}.$$
The proposition on mediants guarantees the order. Each new fraction is in lowest terms. This tree of fractions is the Stern-Brocot tree, and it contains each rational number in $[0, 1]$ exactly once. The continued fractions of Chapter 8 give another view of it.

**Counterexample (The mediant depends on the fraction).** The fractions $1/2$ and $2/4$ are the same rational number. The mediant of $1/2$ and $1/3$ is $2/5$. The mediant of $2/4$ and $1/3$ is $3/7$. Since $2 \cdot 7 = 14 \ne 15 = 5 \cdot 3$, the two mediants differ. So the mediant is not a function on $\mathbb{Q} \times \mathbb{Q}$. Both values still lie between $1/3$ and $1/2$: $1/3 < 3/7 < 2/5 < 1/2$.

**Example (The field $\mathbb{Q}(\sqrt 2)$ has two orderings).** Let $K = \{a + b\sqrt 2 : a, b \in \mathbb{Q}\}$ inside $\mathbb{R}$. The order of $\mathbb{R}$ restricts to an ordering of $K$, with $\sqrt 2 > 0$. The map $\sigma(a + b \sqrt 2) = a - b \sqrt 2$ is a field automorphism of $K$, since $(\sqrt 2)^2 = 2 = (-\sqrt 2)^2$. Define $P' = \{x \in K : \sigma(x) > 0\}$. Since $\sigma$ is a bijection that respects sums and products, $P'$ is a positive cone. In the order of $P'$ the element $\sqrt 2$ is negative, because $\sigma(\sqrt 2) = -\sqrt 2 < 0$. So the two orderings differ. The uniqueness theorem for $\mathbb{Q}$ fails for its extension $K$. In each ordering $\sqrt 2$ or $-\sqrt 2$ is positive, since one of them must be the positive square root of $2$.

**Example (The ordered field $\mathbb{R}(x)$).** Section 1 ordered $\mathbb{R}[X]$ by the cone $P_0$ of polynomials with positive leading coefficient. Extend this order to the field of fractions $\mathbb{R}(x)$. Each nonzero rational function can be written $f/g$ with $g$ of positive leading coefficient: if the leading coefficient of $g$ is negative, replace $(f, g)$ by $(-f, -g)$. Define
$$P = \{f/g : f \in P_0, \ g \in P_0\}.$$
The set $P$ is well defined. If $f/g = f'/g'$ with $g, g' \in P_0$, then $f g' = f' g$. The leading coefficient of a product is the product of the leading coefficients. So $\operatorname{lc}(f)\operatorname{lc}(g') = \operatorname{lc}(f')\operatorname{lc}(g)$, and $\operatorname{lc}(f)$ and $\operatorname{lc}(f')$ have the same sign.

The set $P$ is closed under products, since $(f/g)(f'/g') = f f'/(g g')$ and $P_0$ is closed under products. It is closed under sums, since $f/g + f'/g' = (f g' + f' g)/(g g')$ and $P_0$ is closed under sums and products. For trichotomy, write a nonzero element as $f/g$ with $g \in P_0$. Then $f \ne 0$, and exactly one of $f$ and $-f$ is in $P_0$. So $P$ is a positive cone, and $\mathbb{R}(x)$ is an ordered field.

In this order $x$ is infinite. For each $r \in \mathbb{R}$ the polynomial $x - r$ has leading coefficient $1$, so $x > r$. The element $1/x$ is infinitesimal. It is positive, and for each real $r > 0$,
$$r - \frac{1}{x} = \frac{r x - 1}{x},$$
with numerator and denominator in $P_0$. So $0 < 1/x < r$. This order is the order of the germs at $+\infty$: $f/g$ is positive if and only if $f(t)/g(t) > 0$ for all large real $t$.

### The library around it

The lemmas on ordered fields live in `Mathlib.Algebra.Order.Field.Basic`, and many general ones live in `Mathlib.Algebra.Order.GroupWithZero.Basic`. The general lemmas have the suffix `₀` and need positivity hypotheses. In a proof, the tactic `field_simp` clears denominators that it can prove nonzero, and `positivity` proves goals of the form `0 < e` and `0 ≤ e` for expressions built from positive parts. The tactic `linarith` works over each ordered field, and `nlinarith` adds products of hypotheses.

A sum of squares is nonnegative in each ordering of a ring, and the library treats the sums of squares as an inductive predicate. The module `Mathlib.Algebra.Ring.SumsOfSquares` defines `IsSumSq`, with the two constructors `IsSumSq.zero` and `IsSumSq.sq_add` for $a^2 + s$. The sums of squares are closed under sums by `IsSumSq.add`, and in a commutative semiring under products by `IsSumSq.mul`. They form the subsemiring `Subsemiring.sumSq R`, which `Subsemiring.closure_isSquare` identifies with the subsemiring generated by the squares. In a linearly ordered ring each sum of squares is nonnegative, by `IsSumSq.nonneg`. The module `Mathlib.Algebra.Ring.Semireal.Defs` defines the weaker class `IsSemireal R`: $1 + s \ne 0$ for each sum of squares $s$, which in a ring means that $-1$ is not a sum of squares (`isSemireal_iff_not_isSumSq_neg_one`). A semireal ring has characteristic zero (`instCharZeroOfIsSemireal`), and a linearly ordered ring is semireal by instance. The module `Mathlib.Algebra.Ring.Subsemiring.Support` studies a subsemiring $S$ with $a \in S$ or $-a \in S$ for each $a$, the shape of the positive cone of an ordering. Such an $S$ contains all sums of squares, by `AddSubmonoid.IsSpanning.sumSq_le`, and its support $S \cap -S$ is an ideal, `Subsemiring.supportIdeal`.

::: mathlib
`IsFormallyReal.instOfIsStrictOrderedRing` · `Mathlib.Algebra.Ring.IsFormallyReal`

The instance takes `[Ring R] [LinearOrder R] [IsStrictOrderedRing R]` and gives `IsFormallyReal R`. A lemma that needs `IsFormallyReal` thus applies to `ℝ` and `ℚ` with no work from the user.

<?decl IsFormallyReal.instOfIsStrictOrderedRing?>
:::

**Common errors of a learner.**

- Dividing an inequality by an element of unknown sign. The step from $a c \le b c$ to $a \le b$ needs $c > 0$. In Mathlib each lemma of this kind carries the hypothesis `0 < c`.
- Writing $a < b \Rightarrow 1/b < 1/a$ without the hypothesis $a > 0$. For $a = -1$ and $b = 1$ the conclusion $1 < -1$ is false.
- In Lean, forgetting that `a / 0 = 0`. The lemma `div_le_iff₀` needs `0 < c`, and a statement about `a / c` with `c = 0` is often true for the wrong reason.
- Looking for `LinearOrderedField`. At this commit the class is gone. Write `[Field K] [LinearOrder K] [IsStrictOrderedRing K]`.
- Thinking that every field of characteristic zero can be ordered. The field $\mathbb{C}$ has characteristic zero and $-1 = i^2$, so it is not formally real.

### Exercises

1. (A) In an ordered field, show that $0 < a < 1$ implies $a^2 < a$ and $1/a > 1$. Hint: multiply $a < 1$ by $a$, and apply the proposition on inverses.
2. (A) Prove that $a < b$ and $c < d$ with $a, b, c, d > 0$ do not imply $a/c < b/d$. Give an example in $\mathbb{Q}$. Hint: take $c$ small.
3. (A) Show that in an ordered field $(a + b)/2 \ge \sqrt{a b}$ in the form: $a, b \ge 0$ implies $4 a b \le (a + b)^2$.
4. (B) Show that the mediant of two consecutive fractions $a/b < c/d$ in the Stern-Brocot tree is in lowest terms, using the fact that $b c - a d = 1$ for such neighbours. Hint: a common divisor of $a + c$ and $b + d$ divides $(b + d) c - (a + c) d$.
5. (B) Show that a field of positive characteristic $p$ is not formally real. Hint: write $-1$ as $1 + \dots + 1$.
6. (B) Show that $\mathbb{Q}(i)$ has no ordering. Let $c \in \mathbb{Q}(\sqrt[3]{2})$ with $c^3 = 2$. Show that $1 < c < 2$ in every ordering of this field. Hint: if $c \le 1$, then $c^3 \le 1$.
7. (B) In the ordered field $\mathbb{R}(x)$, decide the sign of $(x^2 - 5x)/(1 - x^3)$, and show that $x^n$ is larger than $c x^m$ for each real $c$ when $n > m$.
8. (C) Define a second ordering on $\mathbb{R}(x)$ by the sign at $0^+$: $f/g > 0$ if $f(t)/g(t) > 0$ for all small $t > 0$. Show that it is a positive cone, and that $x$ is a positive infinitesimal for it.
9. (C) Show that an ordered field $K$ in which every positive element is a square has exactly one ordering. Deduce that $\mathbb{R}$ has exactly one ordering. Hint: in any ordering, a square is nonnegative.

### Notes and history

The axioms of an ordered field appear in Hilbert's *Grundlagen der Geometrie* (1899), where he studied non-archimedean ordered fields to separate the axioms of geometry. Artin and Schreier developed the algebraic theory of real fields in 1926 and 1927, and Artin used it in his solution of Hilbert's seventeenth problem: a real polynomial that is nonnegative on $\mathbb{R}^n$ is a sum of squares of rational functions. The mediant and the Stern-Brocot tree go back to Stern (1858) and to the clockmaker Brocot (1861), who used it to choose gear ratios. The field $\mathbb{R}(x)$ with the order at infinity is the simplest example of a Hardy field, a field of germs of real functions studied by Hardy in his work on orders of infinity.

### Reference

<?reference?>
