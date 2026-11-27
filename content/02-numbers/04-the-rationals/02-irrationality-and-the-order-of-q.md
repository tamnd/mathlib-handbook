---
title: The order of ℚ and irrationality
kind: theory
modules:
  - Mathlib.Data.Rat.Sqrt
  - Mathlib.Data.Rat.Floor
explains:
  E3: [Rat.isSquare_iff, Rat.sqrt]
  E2: [Rat.isSquare_natCast_iff, Rat.isSquare_intCast_iff, Rat.mul_self_num, Rat.mul_self_den, Rat.exists_mul_self, Rat.sqrt_eq, Rat.floor_def']
  E1: auto
families: []
requires: [V02.C03]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V02/C04/Examples.lean
  - MathlibHandbook/V02/C04/Exercises.lean
  - MathlibHandbook/V02/C04/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The order of ℚ and irrationality

### Overview

The rational numbers form an ordered field: they have the four operations, a linear order, and the order is compatible with the operations. The order is archimedean, so no rational number is larger than all integers, and it is dense, so between two rational numbers there is a third. These properties make $\mathbb{Q}$ look like a line. But the line has gaps. The equation $x^2 = 2$ has no solution in $\mathbb{Q}$, and the set $\{x \in \mathbb{Q} : x^2 < 2\}$ is bounded above but has no least upper bound in $\mathbb{Q}$. This defect is the reason to build $\mathbb{R}$ in Chapter 7.

This section proves that $\mathbb{Q}$ is an archimedean ordered field, that $\sqrt n$ is rational only for a perfect square $n$, and that $\mathbb{Q}$ does not have the least upper bound property. In Mathlib, the irrationality of $\sqrt 2$ is a statement about a real number, `irrational_sqrt_two`. Inside $\mathbb{Q}$, the statement is that $2$ is not a square.

### Definitions

**Definition (Positive rational numbers).** A rational number $q$ is positive if its numerator in lowest terms is positive. For $q, r \in \mathbb{Q}$, $q < r$ if $r - q$ is positive, and $q \leq r$ if $q < r$ or $q = r$.

For fractions with positive denominators this gives the rule of school: if $b, d > 0$, then $\frac{a}{b} \leq \frac{c}{d}$ if and only if $a d \leq c b$. Indeed $\frac{c}{d} - \frac{a}{b} = \frac{c b - a d}{b d}$, and the sign of a fraction with a positive denominator is the sign of its numerator, since the reduction to lowest terms divides by a positive gcd.

**Definition (Ordered field, archimedean).** An ordered field is a field with a linear order such that $x \leq y$ gives $x + z \leq y + z$, and $0 < x$, $0 < y$ give $0 < x y$. It is archimedean if each element is less than some $n \in \mathbb{N}$.

**Definition (Square, irrational).** An element $x$ of a ring is a square if $x = y \cdot y$ for some $y$ of the ring. A real number is irrational if it is not the image of a rational number.

::: mathlib
`Irrational` · `Mathlib.NumberTheory.Real.Irrational`

The definition is `Irrational x := x ∉ Set.range ((↑) : ℚ → ℝ)`, a predicate on `ℝ`. The lemma `irrational_iff_ne_rational` gives the form `x ≠ a / b`.

<?decl Irrational?>
:::

**Definition (The rational square root).** For $q \in \mathbb{Q}$ in lowest terms $a / b$, Mathlib defines `Rat.sqrt q` as the fraction $\lfloor \sqrt{a} \rfloor / \lfloor \sqrt{b} \rfloor$, with the integer square roots `Int.sqrt` and `Nat.sqrt`. If $q$ is the square of a rational number, this is its square root that is not negative. In the other cases it is a junk value: `Rat.sqrt 2 = 1`.

::: mathlib
`Rat.sqrt` · `Mathlib.Data.Rat.Sqrt`

The definition is `Rat.sqrt q = mkRat (Int.sqrt q.num) (Nat.sqrt q.den)`, and it computes. The lemma `Rat.sqrt_eq` says `Rat.sqrt (q * q) = |q|`, and `Rat.exists_mul_self` says that `x` is a square if and only if `Rat.sqrt x * Rat.sqrt x = x`.

<?decl Rat.sqrt?>
:::

### Theorems and proofs

**Theorem (ℚ is an ordered field).** The order of the definition is a linear order on $\mathbb{Q}$, and $\mathbb{Q}$ with this order is an ordered field.

*Proof.* Let $P$ be the set of positive rational numbers. (1) For each $q$ exactly one of $q \in P$, $q = 0$, $-q \in P$ holds, since the numerator of $-q$ is the negative of the numerator of $q$. (2) For $a, b, c, d > 0$, the sum $(a d + b c) / (b d)$ and the product $(a c) / (b d)$ of $a / b$ and $c / d$ are positive.

By (1), exactly one of $q < r$, $q = r$, $r < q$ holds. If $q < r$ and $r < s$, then $s - q = (s - r) + (r - q) \in P$ by (2), so the order is transitive. The compatibility with addition holds because $(y + z) - (x + z) = y - x$, and the compatibility with multiplication is (2). $\square$

::: mathlib
`Rat.instIsStrictOrderedRing` · `Mathlib.Algebra.Order.Ring.Rat`

Mathlib proves the axioms of an ordered ring for the order of `ℚ` in this instance. The rule of school is `Rat.divInt_le_divInt`.

<?decl Rat.instIsStrictOrderedRing?>
:::

**Theorem (ℚ is archimedean).** For each $q \in \mathbb{Q}$ there is $n \in \mathbb{N}$ with $q < n$. For each $\varepsilon > 0$ in $\mathbb{Q}$ there is $n \geq 1$ with $1 / n < \varepsilon$.

*Proof.* Write $q = a / b$ with $b \geq 1$. Then $q \leq |a| / b \leq |a|$, because $|a| \leq |a| b$. So $n = |a| + 1$ works. For the second claim, apply the first claim to $1 / \varepsilon$: there is $n$ with $1 / \varepsilon < n$. Then $n > 0$, and multiplication by the positive number $\varepsilon / n$ gives $1 / n < \varepsilon$. $\square$

::: mathlib
`Rat.floor_def'` · `Mathlib.Data.Rat.Floor`

The floor of a rational number is a Euclidean quotient: `⌊q⌋ = q.num / ↑q.den`. The archimedean property is the instance `instArchimedeanRat`.

<?decl Rat.floor_def'?>
:::

**Theorem (Density).** If $q < r$ in $\mathbb{Q}$, then $q < \frac{q + r}{2} < r$.

*Proof.* From $q < r$, add $q$ to get $2 q < q + r$, and add $r$ to get $q + r < 2 r$. Multiply by the positive number $\frac{1}{2}$. $\square$

**Theorem (√2 is not rational).** There is no $q \in \mathbb{Q}$ with $q^2 = 2$.

*Proof.* First a fact about parity: if $a^2$ is even, then $a$ is even. Indeed, if $a = 2 k + 1$ is odd, then $a^2 = 4 k^2 + 4 k + 1$ is odd.

Suppose $q^2 = 2$, and write $q = a / b$ in lowest terms, with $b > 0$ and $\gcd(a, b) = 1$. Then $a^2 = 2 b^2$. So $a^2$ is even, and $a$ is even by the fact. Write $a = 2 c$. Then $4 c^2 = 2 b^2$, so $b^2 = 2 c^2$. So $b^2$ is even, and $b$ is even. Then $2$ divides $a$ and $b$, which contradicts $\gcd(a, b) = 1$. $\square$

::: mathlib
`irrational_sqrt_two` · `Mathlib.NumberTheory.Real.Irrational`

The statement is `Irrational √2`, about the real number `Real.sqrt 2`, in Volume 12. Inside `ℚ`, the same mathematics is `¬ IsSquare (2 : ℚ)`.

<?decl irrational_sqrt_two?>
:::

**Theorem (Squares in ℚ).** A rational number $q$ is a square in $\mathbb{Q}$ if and only if its numerator is a square in $\mathbb{Z}$ and its denominator is a square in $\mathbb{N}$.

*Proof.* If $q.\mathrm{num} = a^2$ and $q.\mathrm{den} = b^2$, then $q = a^2 / b^2 = (a / b)^2$. Conversely, let $q = r^2$, and write $r = a / b$ in lowest terms. Then $q = a^2 / b^2$, with $b^2 > 0$. The pair $(a^2, b^2)$ is in lowest terms: a prime $p$ that divides $a^2$ and $b^2$ divides $a$ and $b$ by Euclid's lemma, and no such prime exists. By the uniqueness of lowest terms, $q.\mathrm{num} = a^2$ and $q.\mathrm{den} = b^2$. $\square$

**Corollary (Square roots of integers).** Let $n \in \mathbb{Z}$. If $n = q^2$ for some $q \in \mathbb{Q}$, then $n = m^2$ for some $m \in \mathbb{Z}$. So for $n \in \mathbb{N}$ that is not a perfect square, $\sqrt n$ is irrational.

*Proof.* The denominator of $n$ is $1$, and its numerator is $n$. By the theorem, $n$ is a square in $\mathbb{Z}$. $\square$

::: mathlib
`Rat.isSquare_iff` · `Mathlib.Data.Rat.Lemmas`

The statement uses `IsSquare`, the predicate `∃ r, q = r * r`, and the proof uses `Rat.mul_self_num` and `Rat.mul_self_den`. The form for an integer is `Rat.isSquare_intCast_iff`.

<?decl Rat.isSquare_iff?>
:::

::: mathlib
`Rat.isSquare_natCast_iff` · `Mathlib.Data.Rat.Lemmas`

The statement is `IsSquare (n : ℚ) ↔ IsSquare n`. The right side is decidable for a literal, so `decide` finishes the goal after the rewrite.

<?decl Rat.isSquare_natCast_iff?>
:::

**Theorem (Rational root theorem).** Let $f(x) = c_n x^n + \dots + c_0$ with $c_i \in \mathbb{Z}$ and $c_n \neq 0$. If $a / b$ in lowest terms is a root of $f$, then $a \mid c_0$ and $b \mid c_n$. In particular, if $c_n = 1$, each rational root of $f$ is an integer.

The proof multiplies $f(a / b) = 0$ by $b^n$ and uses $\gcd(a, b^n) = 1$. Exercise 4 asks for it.

::: mathlib
`isInteger_of_is_root_of_monic` · `Mathlib.RingTheory.Polynomial.RationalRoot`

Mathlib states the theorem for a domain with unique factorization and its field of fractions. The parts are `num_dvd_of_is_root` and `den_dvd_of_is_root`, and this lemma is the monic case.

<?decl isInteger_of_is_root_of_monic?>
:::

**Theorem (ℚ has gaps).** The set $S = \{x \in \mathbb{Q} : x^2 < 2\}$ is not empty and is bounded above in $\mathbb{Q}$, but it has no least upper bound in $\mathbb{Q}$.

*Proof.* The set contains $1$. It is bounded above by $2$: if $x \geq 2$, then $x^2 \geq 4 > 2$, so $x \notin S$. Suppose $s \in \mathbb{Q}$ is a least upper bound of $S$. Then $s \geq 1$, since $1 \in S$. By the theorem on $\sqrt 2$, $s^2 \neq 2$. So there are two cases.

Case $s^2 < 2$. The plan: a number a bit larger than $s$ is still in $S$. Let $h = \min\left(1, \frac{2 - s^2}{2 (2 s + 1)}\right)$, a positive rational number with $h \leq 1$. Then $h^2 \leq h$, and

$$(s + h)^2 = s^2 + 2 s h + h^2 \leq s^2 + h (2 s + 1) \leq s^2 + \frac{2 - s^2}{2} < 2.$$

So $s + h \in S$ and $s + h > s$. This contradicts the claim that $s$ is an upper bound.

Case $s^2 > 2$. The plan: a number a bit smaller than $s$ is still an upper bound. Let $h = \frac{s^2 - 2}{2 s} > 0$ and $t = s - h = \frac{s^2 + 2}{2 s}$. Then $t > 0$ and $t < s$. Also

$$t^2 = s^2 - 2 s h + h^2 = s^2 - (s^2 - 2) + h^2 = 2 + h^2 > 2.$$

Now $t$ is an upper bound of $S$. Let $x \in S$. If $x \leq 0$, then $x < t$. If $x > 0$ and $x > t$, then $x^2 > t^2 > 2$, because both are positive, and so $x \notin S$. Thus each $x \in S$ satisfies $x \leq t$. But $t < s$, and this contradicts the claim that $s$ is the least upper bound. $\square$

In $\mathbb{R}$, the least upper bound of $S$ is $\sqrt 2$ (Chapter 7).

### Examples

**Example (Two is not a square).** The proof in Lean moves the goal to `ℕ` with `Rat.isSquare_natCast_iff`, where the statement is decidable, and the kernel checks it.

<?lean MathlibHandbook/V02/C04/Examples.lean#not_square?>

**Example (A fraction that is a square).** The number $\frac{18}{50}$ has lowest terms $\frac{9}{25}$. The numerator $9 = 3^2$ and the denominator $25 = 5^2$ are squares, so $\frac{18}{50} = \left(\frac{3}{5}\right)^2$. So the theorem on squares needs the lowest terms. The function `Rat.sqrt` gives `Rat.sqrt (18 / 50) = 3 / 5`.

**Example (Approximations from the gap).** The proof of the case $s^2 > 2$ gives a map $s \mapsto \frac{s^2 + 2}{2 s} = \frac{s}{2} + \frac{1}{s}$, which is Newton's method for $x^2 - 2$. From $s = 2$ it gives $\frac{3}{2}$, then $\frac{17}{12}$, then $\frac{577}{408}$. Each value is an upper bound of $S$, and each is smaller than the one before: $\frac{577^2}{408^2} = \frac{332929}{166464} = 2 + \frac{1}{166464}$. The sequence of values has no limit in $\mathbb{Q}$.

### The library around it

The order of `ℚ` is in `Mathlib.Algebra.Order.Ring.Rat` and `Mathlib.Algebra.Order.Field.Rat` in Volume 6, and `exists_rat_btwn` and `exists_nat_gt` are in `Mathlib.Algebra.Order.Archimedean.Basic`. The file `Mathlib.Data.Rat.Floor` has the floor and the ceiling, and `Mathlib.Data.Rat.Sqrt` has `Rat.sqrt` with `Rat.sqrt_nonneg` and `Rat.sqrt_natCast`. The theory of irrational real numbers is in `Mathlib.NumberTheory.Real.Irrational`, with `Nat.Prime.irrational_sqrt` and `irrational_sqrt_natCast_iff`.

### Exercises

1. (A) Order the numbers $\frac{5}{8}$, $\frac{13}{21}$ and $\frac{8}{13}$, and give a rational number between the two largest. *Hint.* Use the rule of school.
2. (A) Give the values of `Rat.sqrt 2`, `Rat.sqrt (9 / 4)` and `Rat.sqrt (-4)`. *Hint.* Use the definition with `Int.sqrt` and `Nat.sqrt`.
3. (A) Find all rational roots of $2 x^2 - 3 x - 2$. *Hint.* The candidates are $\pm 1, \pm 2, \pm \frac{1}{2}$.
4. (B) Prove the rational root theorem. *Hint.* Multiply $f(a / b) = 0$ by $b^n$. All terms except $c_0 b^n$ have the factor $a$, and $\gcd(a, b^n) = 1$.
5. (B) Prove that $\sqrt[3]{2}$ and $\sqrt 2 + \sqrt 3$ are not rational. *Hint.* For the second, square twice to get a monic polynomial with integer coefficients.
6. (B) Show that the set $\{x \in \mathbb{Q} : x > 0, x^2 > 2\}$ has no greatest lower bound in $\mathbb{Q}$. *Hint.* Use the proof of the gap theorem.
7. (C) Show that for $q < r$ in $\mathbb{Q}$ there is a fraction $m / 2^k$ with $q < m / 2^k < r$. *Hint.* Find $k$ with $1 / 2^k < r - q$ by the archimedean property.
8. (L) Prove that $3$ is not a square in `ℚ`. The solution is `not_isSquare_three`.

### Notes and history

The proof that $\sqrt 2$ is irrational goes back to the Pythagoreans, and Aristotle mentions the proof by parity. Dedekind used the gap of $\{x : x^2 < 2\}$ in 1872 as the motivation for his cuts. In Mathlib, `Mathlib.Data.Rat.Sqrt` is by Johannes Hölzl and Mario Carneiro.

### Reference

<?reference?>
