---
title: The integers
kind: theory
modules:
  - Mathlib.Data.Int.Init
  - Mathlib.Data.Int.Lemmas
explains:
  E3: [Int.induction_on, Int.ediv_emod_unique'']
  E2: [Int.inductionOn', Int.emod_two_eq_zero_or_one, Int.natAbs_sq, Int.sign_mul_self_eq_natAbs]
  E1: auto
families: []
requires: [V02.C02]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V02/C03/Examples.lean
  - MathlibHandbook/V02/C03/Exercises.lean
  - MathlibHandbook/V02/C03/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The integers

### Overview

The integers add the solutions of the equations $x + m = n$ in $\mathbb{N}$, such as $x + 5 = 2$. A textbook builds $\mathbb{Z}$ from $\mathbb{N}$ as classes of pairs. The core of Lean defines `ℤ` as an inductive type with one constructor for the numbers that are not negative and one for the negative numbers, so the kernel can compute with each integer.

This section gives both constructions, induction on $\mathbb{Z}$, the absolute value, and the division algorithm: for $b \neq 0$ there are unique $q, r$ with $a = b q + r$ and $0 \leq r < |b|$. The next section uses it to define congruences.

### Definitions

**Definition (The integers as classes of pairs).** On $\mathbb{N} \times \mathbb{N}$ define the relation $(m, n) \sim (m', n')$ if $m + n' = m' + n$. The set $\mathbb{Z}$ is the set of the classes $[m, n]$ of this relation. The class $[m, n]$ stands for $m - n$.

The relation uses only addition, so it makes sense in $\mathbb{N}$. It is reflexive and symmetric by its form. It is transitive: add $m + n' = m' + n$ and $m' + n'' = m'' + n'$, and cancel $m' + n'$ on both sides. The result is $m + n'' = m'' + n$.

**Definition (The operations on classes).** For two classes put

$$[m, n] + [m', n'] = [m + m', n + n'], \qquad [m, n] \cdot [m', n'] = [m m' + n n', m n' + n m'], \qquad -[m, n] = [n, m].$$

The formula for the product comes from the expansion $(m - n)(m' - n') = m m' + n n' - (m n' + n m')$. The natural number $k$ is the class $[k, 0]$, and $[0, k]$ is $-k$.

**Definition (The integers in Lean).** The core of Lean defines `ℤ` as an inductive type with the constructors `Int.ofNat : ℕ → ℤ` and `Int.negSucc : ℕ → ℤ`. The term `Int.ofNat n` is $n$, and `Int.negSucc n` is $-(n + 1)$.

**Definition (Order).** For $a, b \in \mathbb{Z}$, $a \leq b$ if $b - a$ is the cast of a natural number.

**Definition (Absolute value and sign).** The absolute value is $|a| = a$ for $a \geq 0$ and $|a| = -a$ for $a < 0$. The sign of $a$ is $1$, $0$ or $-1$. Lean has `|a| : ℤ` and `Int.natAbs a : ℕ`.

**Definition (Euclidean division).** Lean defines `a / b` and `a % b` (`Int.ediv` and `Int.emod`) so that for $b \neq 0$ they satisfy $a = b (a / b) + a \% b$ and $0 \leq a \% b < |b|$. The junk values are $a / 0 = 0$ and $a \% 0 = a$.

### Theorems and proofs

**Theorem (The operations are well defined).** The sum, the product and the negation of classes do not depend on the choice of the pairs.

*Proof.* Negation is direct. Sum: if $m + q = p + n$, then $(m + m') + (q + n') = (p + m') + (n + n')$. Product: by symmetry it is enough to change the first argument. If $m + q = p + n$, the claim is

$$(m m' + n n') + (p n' + q m') = (p m' + q n') + (m n' + n m').$$

The left side is $(m + q) m' + (n + p) n'$. Since $m + q = p + n$, it is $(p + n) m' + (m + q) n'$, and this is the right side. $\square$

The ring axioms for $\mathbb{Z}$ follow from the ring axioms for $\mathbb{N}$ by a computation on representatives, and $[m, n] + [n, m] = [0, 0]$ gives the inverse. The map $k \mapsto [k, 0]$ is injective, and each class $[m, n]$ is $[m - n, 0]$ if $m \geq n$ and $-[n - m, 0]$ if $m < n$. This is the form of Lean, where $-k$ with $k \geq 1$ is `Int.negSucc (k - 1)`.

**Theorem (Induction on ℤ).** Let $P$ be a property of integers. If $P(0)$ holds, $P(i)$ gives $P(i + 1)$ for each $i \in \mathbb{N}$, and $P(-i)$ gives $P(-i - 1)$ for each $i \in \mathbb{N}$, then $P(n)$ holds for each $n \in \mathbb{Z}$.

*Proof.* By induction on $\mathbb{N}$ with the second hypothesis, $P(i)$ holds for each $i \in \mathbb{N}$. By induction on $\mathbb{N}$ with the third hypothesis, $P(-i)$ holds for each $i \in \mathbb{N}$, since $-i - 1 = -(i + 1)$. Each integer is $i$ or $-i$ for some $i \in \mathbb{N}$. $\square$

::: mathlib
`Int.induction_on` · `Mathlib.Data.Int.Init`

The hypotheses are the case $0$, the step up from `(i : ℤ)` and the step down from `-(i : ℤ)`, with `i : ℕ`. Use it with `induction n using Int.induction_on`. The variant `Int.inductionOn'` starts at an integer `b`.

<?decl Int.induction_on?>
:::

**Theorem (Units of ℤ).** The absolute value is multiplicative: $|a b| = |a| |b|$. If $a b = 1$ in $\mathbb{Z}$, then $a = b = 1$ or $a = b = -1$.

*Proof.* The first claim follows by the four cases of the signs. Then $|a| |b| = |a b| = 1$ in $\mathbb{N}$, so $|a| = |b| = 1$. The equation $a b = 1$ excludes the mixed signs. $\square$

::: mathlib
`Int.sign_mul_self_eq_natAbs` · `Mathlib.Data.Int.Init`

The lemma says that `a.sign * a = a.natAbs` in `ℤ`. The lemmas of `|a|` come from the theory of ordered groups, and the lemmas of `Int.natAbs` are in the files of `ℤ`, for example `Int.natAbs_sq`. The bridge is `Int.abs_eq_natAbs`.

<?decl Int.sign_mul_self_eq_natAbs?>
:::

**Theorem (The division algorithm).** Let $a, b \in \mathbb{Z}$ with $b \neq 0$. There are unique integers $q$ and $r$ with $a = b q + r$ and $0 \leq r < |b|$.

*Proof.* The plan: find a remainder that is not negative, take the least one with the well ordering of $\mathbb{N}$, and show that it is less than $|b|$. Then compare two solutions.

Existence. Let $S = \{a - b x : x \in \mathbb{Z}\} \cap \mathbb{N}$, the set of the values of $a - b x$ that are not negative. The set is not empty. Take $x = -|a|$ if $b > 0$ and $x = |a|$ if $b < 0$. In both cases $b x = -|b| |a|$, and so $a - b x = a + |b| |a| \geq a + |a| \geq 0$, because $|b| \geq 1$. By the well ordering of $\mathbb{N}$, the set $S$ has a least element $r$. Write $r = a - b q$. Then $a = b q + r$ and $r \geq 0$. Suppose that $r \geq |b|$. Let $s = \operatorname{sign}(b)$, so that $b s = |b|$. Then $a - b (q + s) = r - |b| \geq 0$, so $r - |b| \in S$. But $r - |b| < r$, because $|b| \geq 1$. This contradicts the choice of $r$. So $r < |b|$.

Uniqueness. Suppose $a = b q + r = b q' + r'$ with $0 \leq r, r' < |b|$. Then $b (q - q') = r' - r$. The two remainders are in $[0, |b|)$, so $|r' - r| < |b|$. Thus $|b| |q - q'| < |b|$, and since $|b| > 0$, the natural number $|q - q'|$ is less than $1$. So $q = q'$, and then $r = r'$. $\square$

::: mathlib
`Int.ediv_emod_unique''` · `Mathlib.Data.Int.Lemmas`

The lemma says: for `b ≠ 0`, `a / b = q ∧ a % b = r` if and only if `r + b * q = a`, `0 ≤ r` and `r < |b|`. The parts are in the core of Lean: `Int.emod_nonneg`, `Int.emod_lt_of_pos` and `Int.ediv_add_emod`. The tactic `omega` knows these facts for a literal divisor.

<?decl Int.ediv_emod_unique''?>
:::

**Corollary (Parity).** Each integer $n$ is $2 k$ or $2 k + 1$ for a unique $k$, that is, $n \% 2 \in \{0, 1\}$.

*Proof.* Apply the division algorithm with $b = 2$. The remainder is in $\{0, 1\}$. $\square$

::: mathlib
`Int.emod_two_eq_zero_or_one` · `Mathlib.Data.Int.Init`

The statement is `n % 2 = 0 ∨ n % 2 = 1`. A proof by cases uses `rcases Int.emod_two_eq_zero_or_one n with h | h`. The form with `Even` and `Odd` is `Int.even_or_odd`.

<?decl Int.emod_two_eq_zero_or_one?>
:::

### Examples

**Example (Division of a negative number).** Divide $-7$ by $2$. The multiples of $2$ that are at most $-7$ are $-8, -10, \dots$, and the largest is $-8 = 2 \cdot (-4)$. So $q = -4$ and $r = -7 - (-8) = 1$. The quotient rounds down, and the remainder is not negative.

<?lean MathlibHandbook/V02/C03/Examples.lean#div_mod?>

**Example (Three conventions).** For $7 / (-2)$, the Euclidean convention of Lean gives $q = -3$ and $r = 1$, since $0 \leq r < 2$. Truncation (`Int.tdiv`) rounds toward $0$ and gives $-7 / 2 = -3$ with remainder $-1$. Floor division (`Int.fdiv`) gives $7 / (-2) = -4$ with remainder $-1$. Only the Euclidean remainder is always in $\{0, \dots, |b| - 1\}$.

**Example (Induction on ℤ).** The product $n (n + 1)$ is even for each $n \in \mathbb{Z}$. The steps are $(i + 1)(i + 2) = i (i + 1) + 2 (i + 1)$ and $(-i - 1)(-i) = (-i)(-i + 1) + 2 i$.

<?lean MathlibHandbook/V02/C03/Examples.lean#induction_on?>

**Example (Parity).**

<?lean MathlibHandbook/V02/C03/Examples.lean#emod_two?>

**Counterexample (The hypothesis b ≠ 0).** For $b = 0$ no $r$ satisfies $0 \leq r < 0$. Lean gives the junk values $a / 0 = 0$ and $a \% 0 = a$. The identity $a = b (a / b) + a \% b$ still holds, but the bound fails, so `Int.emod_lt_of_pos` has the hypothesis $0 < b$.

### The library around it

The type `ℤ` and the lemmas of the Euclidean division are in the core of Lean, for example `Int.ediv_add_emod` and `Int.emod_emod_of_dvd`. Mathlib adds `Mathlib.Data.Int.Init` and `Mathlib.Data.Int.Lemmas` with the forms of induction, the lemmas of the sign and of `Int.natAbs`, and `Int.ediv_emod_unique''`. The units are $\pm 1$: `Int.isUnit_iff`. The tactic `omega` decides linear statements over `ℤ` with `/` and `%` by literals.

### Exercises

1. (A) Give the values of `(-7 : ℤ) / 0`, `(-7 : ℤ) % 0`, `Int.toNat (-3)` and `Int.natAbs (-3)` in Mathlib. *Hint.* Use the junk values of the Definitions.
2. (A) Compute $q$ and $r$ for $a = -23$ and $b = 5$, and for $a = 23$ and $b = -5$, in the Euclidean convention and in the convention of truncation. *Hint.* The Euclidean remainder is in $[0, 5)$.
3. (B) Show that the order on classes is well defined, and that $a \leq b$ gives $a + c \leq b + c$. *Hint.* Follow the proof that the sum is well defined.
4. (B) Show that the square of an odd integer is congruent to $1$ modulo $8$, that is, $8 \mid n^2 - 1$ for odd $n$. *Hint.* Write $n = 2 k + 1$, and use that $k (k + 1)$ is even.
5. (B) Prove the division algorithm with the condition $-|b|/2 < r \leq |b|/2$ in place of $0 \leq r < |b|$. *Hint.* Start from the Euclidean remainder and subtract $|b|$ if it is too large.
6. (L) Prove that the remainder of $n^2$ modulo $4$ is $0$ or $1$. The solution is `sq_emod_four`.

### Notes and history

The construction of $\mathbb{Z}$ from pairs of natural numbers is the Grothendieck group of $(\mathbb{N}, +)$, and Mathlib has the general form as `Algebra.GrothendieckAddGroup`. Landau gives it in full in *Grundlagen der Analysis* (1930). The division algorithm is in Book VII of Euclid's *Elements* in the form of repeated subtraction.

### Reference

<?reference?>
