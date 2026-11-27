---
title: The rationals
kind: theory
modules:
  - Mathlib.Data.Rat.Init
  - Mathlib.Data.Rat.Defs
  - Mathlib.Data.Rat.Lemmas
  - Mathlib.Data.NNRat.Defs
explains:
  E3: [NNRat]
  E2: [Rat.mkRat_eq_divInt, Rat.den_dvd, Rat.num_dvd, Rat.isSquare_iff, NNRat.coe_add]
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

## The rationals

### Overview

A textbook builds $\mathbb{Q}$ as a quotient: a fraction is a class of pairs $(a, b)$ with $b \neq 0$, and $(a, b) \sim (c, d)$ if $a d = b c$. Lean does not use a quotient. The core of Lean defines `ℚ` as a structure with a numerator, a positive denominator and a proof that the two are coprime. So each rational number has one form, and equality is equality of the fields. The type `ℚ≥0`, with the name `NNRat`, is the subtype of the rational numbers that are not negative. This section shows the structure, the functions that make a fraction, and the lemmas about the numerator and the denominator.

### Definitions

**Definition (The rationals).** A term `q : ℚ` has the fields `q.num : ℤ` and `q.den : ℕ`, and two proofs: `q.den ≠ 0` and `Nat.Coprime q.num.natAbs q.den`. The value of `q` is $q.num / q.den$.

**Definition (Fractions).** For $n \in \mathbb{Z}$ and $d \in \mathbb{N}$, `mkRat n d` is the fraction $n / d$ in lowest terms. For $n, d \in \mathbb{Z}$, `Rat.divInt n d` is the same fraction, with the notation `n /. d`. Both have the junk value $0$ at $d = 0$.

**Definition (Non negative rationals).** `NNRat` is the subtype `{q : ℚ // 0 ≤ q}`, with the notation `ℚ≥0`. The cast `(q : ℚ)` takes a term of `ℚ≥0` to its value.

### Theorems and proofs

**Theorem (Lowest terms).** Each $q \in \mathbb{Q}$ is $a / b$ for one pair $(a, b)$ with $b > 0$ and $\gcd(a, b) = 1$.

*Proof.* Write $q = c / d$ with $d > 0$, and let $g = \gcd(c, d)$. Then $a = c / g$ and $b = d / g$ are coprime, and $q = a / b$. If $a / b = a' / b'$ in lowest terms, then $a b' = a' b$. So $b \mid a b'$ and $\gcd(a, b) = 1$ give $b \mid b'$, and in the same way $b' \mid b$. Thus $b = b'$ and $a = a'$. $\square$

**Theorem (The denominator divides).** For $a, b \in \mathbb{Z}$, the denominator of $a / b$ divides $b$, and the numerator divides $a$.

*Proof.* For $b \neq 0$, the fraction in lowest terms is $(a / g) / (b / g)$ up to sign, where $g = \gcd(a, b)$. Both parts divide the original parts. For $b = 0$ the fraction is $0$, so the denominator is $1$ and the numerator is $0$. The lemma about the numerator needs $b \neq 0$. $\square$

**Theorem (Squares in ℚ).** A rational number $q$ is a square if and only if its numerator and its denominator are squares in $\mathbb{Z}$ and in $\mathbb{N}$.

*Proof.* If $q.num = a^2$ and $q.den = b^2$, then $q = (a / b)^2$. If $q = r^2$, then $q.num = r.num^2$ and $q.den = r.den^2$, because the square of a fraction in lowest terms is in lowest terms. $\square$

### Mathlib boxes

::: mathlib
`NNRat` · `Mathlib.Data.Rat.Init`

The type is a subtype, so a term is a pair of a rational number and a proof. It is an ordered semifield. The cast to `ℚ` is `NNRat.cast`, and the lemmas about the cast have the prefix `NNRat.coe_`.

<?decl NNRat?>
:::

::: mathlib
`Rat.mkRat_eq_divInt` · `Mathlib.Data.Rat.Defs`

The two functions make the same fraction. Mathlib states most of its lemmas with `Rat.divInt`, so this lemma moves a goal from `mkRat` to the form of the library.

<?decl Rat.mkRat_eq_divInt?>
:::

::: mathlib
`Rat.isSquare_iff` · `Mathlib.Data.Rat.Lemmas`

The statement uses `IsSquare`, the predicate that says $q = r \cdot r$ for some $r$. The form for a natural number is `Rat.isSquare_natCast_iff`.

<?decl Rat.isSquare_iff?>
:::

### Examples

**Example (Lowest terms).** The fraction $6 / 4$ has numerator $3$ and denominator $2$. The kernel computes them.

<?lean MathlibHandbook/V02/C04/Examples.lean#num_den?>

**Example (Two ways to make a fraction).**

<?lean MathlibHandbook/V02/C04/Examples.lean#mkRat?>

**Example (Numerator over denominator).** The lemma `Rat.num_div_den` is in `Mathlib.Algebra.Ring.Rat`, because the division is the division of the field.

<?lean MathlibHandbook/V02/C04/Examples.lean#num_div_den?>

**Example (An integer).**

<?lean MathlibHandbook/V02/C04/Examples.lean#den_eq_one?>

**Example (Two is not a square).** The proof moves the goal to `ℕ`, where it is decidable.

<?lean MathlibHandbook/V02/C04/Examples.lean#not_square?>

**Example (The cast of ℚ≥0).**

<?lean MathlibHandbook/V02/C04/Examples.lean#nnrat?>

### The library around it

The file `Mathlib.Data.Rat.Defs` has the basic lemmas, for example `Rat.den_ne_zero`, `Rat.num_ne_zero` and `Rat.den_eq_one_iff`. The field structure is `Rat.instField` in `Mathlib.Algebra.Field.Rat`, and the order is in `Mathlib.Algebra.Order.Field.Rat`. The file `Mathlib.Data.Rat.Lemmas` has `Rat.den_dvd`, `Rat.num_dvd` and `Rat.num_div_eq_of_coprime`. The function `Rat.toNNRat` takes a rational number to `ℚ≥0`, with the junk value $0$ for a negative number. The cast from `ℚ` to a field of characteristic zero is the subject of the next chapter. The tactic `norm_num` computes with fractions, and it is the normal way to prove an equation of rational numbers.

### Exercises

1. (A) Give the values of `(0 : ℚ).den`, `(-3 / 6 : ℚ).num` and `mkRat 5 0` in Mathlib.
2. (A) Explain why Lean stores a rational number in lowest terms and does not use a quotient type.
3. (B) Show that $\sqrt{2}$ is not rational, with `Rat.isSquare_iff`.
4. (B) Show that the map from `ℚ≥0` to `ℚ` is injective and keeps the order.
5. (L) Prove that $1/2 + 1/3 = 5/6$ in `ℚ`. The solution is `half_add_third`.
6. (L) Prove that $3$ is not a square in `ℚ`. The solution is `not_isSquare_three`.
7. (L) Prove that a rational number with denominator $1$ is the cast of an integer. The solution is `den_of_den_eq_one`.
8. (L) Prove that the product of two terms of `ℚ≥0` is not negative in `ℚ`. The solution is `nnrat_mul_nonneg`.

### Notes and history

The construction of $\mathbb{Q}$ as a field of fractions is the construction of the field of fractions of any integral domain, and Mathlib has the general form as `FractionRing`. The structure in lowest terms is the choice of the core of Lean, because it makes computation fast and equality decidable. Lean 3 Mathlib used the same structure.

### Reference

<?reference?>
