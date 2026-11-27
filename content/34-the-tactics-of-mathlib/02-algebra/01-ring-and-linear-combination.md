---
title: ring and linear_combination
kind: tactic
modules: [Mathlib.Tactic.Ring.Basic, Mathlib.Tactic.LinearCombination]
explains:
  E2: [Mathlib.Tactic.Ring.proveEq, Mathlib.Tactic.LinearCombination.linearCombination]
families: []
requires: [V00]
reads_with: ["MIL"]
lean: [MathlibHandbook/V34/C02/Examples.lean, MathlibHandbook/V34/C02/Solutions.lean]
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## ring and linear_combination

### Overview

The tactic `ring` proves an equation that holds in every commutative ring, or in every commutative semiring. The tactic `linear_combination` proves an equation that follows from the hypotheses by a sum of multiples of them. Together they do most of the routine algebra of a proof: the step that a written proof calls "expanding" or "a direct computation".

The section explains the normal form that `ring` computes, and it proves the theorem that makes `ring` a decision procedure: two polynomial expressions are equal in every commutative ring if and only if their normal forms are the same. Then it explains `linear_combination` as a test of membership in an ideal, with the coefficients given by the user. At the end, the reader can tell in advance whether `ring` will close a goal, and can find the coefficients for `linear_combination` by hand.

### What it does

#### Polynomial expressions and atoms

An expression for `ring` is built from atoms, numerals, $+$, $\cdot$, $-$, and powers with a natural number exponent. An atom is a subterm that `ring` does not take apart: a variable such as `x`, or a term such as `Real.sqrt 2`, `f x` or `Real.sin x`. Two subterms that are equal up to reducible definitions are the same atom. In a field, `ring` also treats the inverse $e^{-1}$: it takes the inverse of a numeral as a numeral, and the inverse of another term as a new atom.

**Definition (Normal form of ring).** Fix an order on the atoms $x_1 < x_2 < \cdots < x_k$. A monomial is a product $c \, x_1^{e_1} \cdots x_k^{e_k}$ with a numeral coefficient $c \neq 0$ and exponents $e_i \geq 0$. The normal form of an expression is the sum of its monomials, with the monomials in a fixed order and with the like terms collected.

The tactic computes the normal form of each side by recursion on the expression. For a sum it merges the two sorted lists of monomials and adds the coefficients of equal monomials. For a product it multiplies each pair of monomials and merges. For a power with a numeral exponent it uses repeated squaring. Each step comes with a proof, from the axioms of a commutative semiring, that the old expression is equal to the new one. At the end, if the two normal forms are the same term, the proof of the goal is the chain of these equations.

#### Why the normal form decides the question

**Theorem (Identities of commutative rings).** Let $p, q$ be polynomials with integer coefficients in the variables $x_1, \ldots, x_k$. The following are equivalent:

1. $p$ and $q$ have the same normal form;
2. $p = q$ in the polynomial ring $\mathbb{Z}[x_1, \ldots, x_k]$;
3. for each commutative ring $R$ and all $a_1, \ldots, a_k \in R$, $p(a_1, \ldots, a_k) = q(a_1, \ldots, a_k)$.

*Proof.* (1) implies (3). Each step of the computation of the normal form uses only the axioms of a commutative ring: associativity, commutativity, distributivity, the laws of $0$ and $1$, and the laws of powers. So for each ring $R$ and each choice of the $a_i$, the value of $p$ is the value of its normal form, and the same holds for $q$. If the normal forms are equal, the values are equal.

(3) implies (2). Take $R = \mathbb{Z}[x_1, \ldots, x_k]$ and $a_i = x_i$. Then $p(x_1, \ldots, x_k) = p$, so (3) gives $p = q$ in this ring.

(2) implies (1). The monomials $x_1^{e_1} \cdots x_k^{e_k}$ are a basis of $\mathbb{Z}[x_1, \ldots, x_k]$ as a free abelian group. This is the definition of the polynomial ring. The normal form of $p$ is the expansion of $p$ in this basis, with the zero coefficients left out and the monomials in a fixed order. Two equal elements have the same coefficients in a basis. So $p$ and $q$ have the same normal form. $\square$

The theorem says what `ring` can do and what it cannot do. It proves exactly the identities that hold in all commutative rings. An identity that holds only in some rings is out of its reach. In $\mathbb{Z}/2\mathbb{Z}$, each element satisfies $x^2 = x$, since $0^2 = 0$ and $1^2 = 1$. But $x^2 - x$ is not the zero polynomial, so `ring` fails on `x ^ 2 = x` for `x : ZMod 2`. For a statement about the finite type `ZMod 2`, the tactic `decide` checks the two cases (Chapter 3).

For a commutative semiring such as `ℕ`, the same proof works with the monomials as a basis of the free commutative monoid algebra. Subtraction is not an operation of a semiring. The truncated subtraction of `ℕ` is a new atom-like operation, and `ring` cannot reason about it.

#### linear_combination: a proof by a certificate

**Definition (Linear combination).** Let $h_1 : a_1 = b_1, \ldots, h_m : a_m = b_m$ be hypotheses in a commutative ring, and let $c_1, \ldots, c_m$ be ring expressions. The linear combination $c_1 h_1 + \cdots + c_m h_m$ is the equation $\sum c_i a_i = \sum c_i b_i$.

The call `linear_combination e`, for a combination $e$ of this form, does one thing. It forms the new goal

$$\mathrm{lhs} - \mathrm{rhs} - \Big(\sum c_i a_i - \sum c_i b_i\Big) = 0,$$

and it calls `ring1` on it. If `ring1` succeeds, the goal follows.

**Theorem (Soundness of linear_combination).** If the displayed equation is an identity of commutative rings, and each $h_i$ holds, then $\mathrm{lhs} = \mathrm{rhs}$.

*Proof.* Each hypothesis gives $a_i - b_i = 0$. So $\sum c_i (a_i - b_i) = 0$. The identity says $\mathrm{lhs} - \mathrm{rhs} = \sum c_i(a_i - b_i)$ for all values of the variables. So $\mathrm{lhs} - \mathrm{rhs} = 0$, and $\mathrm{lhs} = \mathrm{rhs}$. $\square$

In the language of algebra, the goal $f = 0$ with $f = \mathrm{lhs} - \mathrm{rhs}$ follows from the hypotheses when $f$ is in the ideal generated by the $g_i = a_i - b_i$, and the combination is a certificate of this membership: $f = \sum c_i g_i$. Finding the $c_i$ is a hard problem in general. It needs Gröbner bases. The tactic does not find them. It only checks a certificate that the user gives, and the check is fast.

The call `linear_combination (exp := n) e` checks that $f^n$, and not $f$, is the combination. This covers some goals that follow from the hypotheses in the radical of the ideal.

::: mathlib
`Mathlib.Tactic.Ring.proveEq` · `Mathlib.Tactic.Ring.Basic`

This is the frontend of `ring1`. It tries to close a goal that is an equation of commutative semirings. The tactic `ring` is `ring1`, and when that fails, it calls `ring_nf` and prints the advice "Try this: ring_nf". So a failed `ring` shows the normal forms of the two sides, which is a good hint of the cause.

<?decl Mathlib.Tactic.Ring.proveEq?>
:::

::: mathlib
`Mathlib.Tactic.LinearCombination.linearCombination` · `Mathlib.Tactic.LinearCombination`

The elaborator of `linear_combination`. It reads the expression of proofs, makes the combined equation, subtracts it from the goal and calls the closing tactic, `ring1` by default. The closing tactic can be changed with the clause `linear_combination (norm := tac) e`, for example to `ring_nf` to see what is left.

<?decl Mathlib.Tactic.LinearCombination.linearCombination?>
:::

### How to use it

Write `ring` at the end of a proof, when the goal is an identity. Write `ring_nf` to put a term in normal form without closing the goal, and `ring_nf at h ⊢` to bring a hypothesis and the goal into the same form, and then `exact h`.

To use `linear_combination`, find the coefficients by hand. The method is the method of school algebra: write the goal as $f = 0$ and the hypotheses as $g_i = 0$, and find $c_i$ with $f = \sum c_i g_i$.

1. If the hypotheses are `h1 : a + b = 3` and `h2 : a - b = 1` and the goal is `a = 2`, then $f = a - 2$, $g_1 = a + b - 3$ and $g_2 = a - b - 1$. Since $g_1 + g_2 = 2a - 4 = 2f$, the combination is $\frac12 (g_1 + g_2)$. Write `linear_combination (h1 + h2) / 2`.
2. A coefficient can contain variables. From `h : x = y`, the goal $x^2 = y^2$ has $f = x^2 - y^2 = (x + y)(x - y)$, so write `linear_combination (x + y) * h`.

If the combination is wrong, the error shows the goal that `ring1` could not prove, in the form `expr = 0`. This expression is $f - \sum c_i g_i$ in normal form. It tells how far the guess is from a correct one.

### What it cannot do

The tactic `ring` does not use the hypotheses. On the goal `a ^ 2 = b ^ 2` with the hypothesis `h : a = b`, `ring` leaves the goal open. Use `subst h` first, or `linear_combination (a + b) * h`.

The tactic `ring` does not know that `x / x = 1`. This is false for $x = 0$ in Mathlib, where `x / 0 = 0`. On `x / x = 1` for `x : ℝ`, `ring` fails, and the normal form that it prints is `x * x⁻¹ = 1`: the inverse `x⁻¹` is an atom, and the product of an atom and another atom is not $1$. Use `field_simp` with the hypothesis `x ≠ 0` (next section).

The tactic `ring` does not know the subtraction of `ℕ`. On `(a - b) * (a + b) = a ^ 2 - b ^ 2` for `a b : ℕ`, it fails and prints `(a - b) * a + (a - b) * b = a ^ 2 - b ^ 2`. The identity is in fact true in `ℕ`, but its proof needs a case split on $a \leq b$. Over `ℤ`, `ring` proves it at once. Cast to `ℤ` first, or use `Nat.sq_sub_sq`.

The tactic `ring` does not know the relations between functions. On $\sin^2 x + \cos^2 x = 1$ it fails: $\sin x$ and $\cos x$ are two atoms with no relation for `ring`. Use `Real.sin_sq_add_cos_sq`, or give the fact to `linear_combination Real.sin_sq_add_cos_sq x`.

A false identity also makes `ring` fail, and then the printed normal forms show the difference. On $(x + 1)^2 = x^2 + 2x$ over `ℝ`, the message shows `1 + x * 2 + x ^ 2 = x * 2 + x ^ 2`, and the missing $1$ is clear.

The tactic `linear_combination` does not find the coefficients. It also cannot use a hypothesis that is not an equation. On `x = 2` from `h : x ^ 2 = 4` and `0 < x`, no combination works, because the goal does not follow from `h` alone: $x = -2$ also satisfies `h`. The sign condition is an inequality, and the proof needs `nlinarith` (Chapter 3).

### Examples

**Example (The cube of a sum).** The binomial formula $(a + b)^3 = a^3 + 3a^2 b + 3 a b^2 + b^3$ holds in each commutative ring. The tactic `ring` computes the normal form of the left side by two multiplications and compares it with the right side.

<?lean MathlibHandbook/V34/C02/Examples.lean#ring_cube?>

**Example (A general ring and a field).** The identity $(x - y)(x + y) = x^2 - y^2$ holds in each commutative ring `R`. In `ℚ`, `ring` also proves $x/2 + x/2 = x$, since it treats $2^{-1}$ as the numeral $\frac12$ and $\frac12 + \frac12 = 1$.

<?lean MathlibHandbook/V34/C02/Examples.lean#ring_general?>

**Example (Normal form of a hypothesis).** From $2x + x = 6$, the call `ring_nf at h ⊢` makes both the hypothesis and the goal the same normal form, $x \cdot 3 = 6$, and `exact h` closes the goal. The normal form puts the atom before the coefficient.

<?lean MathlibHandbook/V34/C02/Examples.lean#ring_nf?>

**Example (Solving a linear system).** From $a + b = 3$ and $a - b = 1$, the goal is $a = 2$. The computation of the coefficients is in the previous part. The second proof is $x^2 = y^2$ from $x = y$.

<?lean MathlibHandbook/V34/C02/Examples.lean#linear_combination?>

A wrong guess shows the rest. With `linear_combination h1 + h2`, the message is

```text
ring failed, ring expressions not equal
⊢ 2 - a = 0
```

This is $(a - 2) - (2a - 4) = 2 - a$. The rest is $-(a - 2)$, one copy of the goal, so the coefficient must be halved.

**Example (A symmetric function).** Let $xy = 1$ and $x + y = 3$. Then $x^2 + y^2 = 7$. By hand: $x^2 + y^2 = (x + y)^2 - 2xy = 9 - 2 = 7$. For the certificate, write $f = x^2 + y^2 - 7$, $g_1 = xy - 1$ and $g_2 = x + y - 3$. Then $(x + y)^2 - 9 = (x + y + 3) g_2$, so

$$f = (x + y)^2 - 2xy - 7 = (x + y + 3) g_2 + 9 - 2(g_1 + 1) - 7 = (x + y + 3) g_2 - 2 g_1.$$

```lean
example (x y : ℝ) (h₁ : x * y = 1) (h₂ : x + y = 3) : x ^ 2 + y ^ 2 = 7 := by
  linear_combination (x + y + 3) * h₂ - 2 * h₁
```

The first guess $(x + y) g_2 - 2 g_1$ fails, and the message shows the rest $-9 + 3x + 3y$, which is $3 g_2$. Adding $3 g_2$ gives the coefficient $x + y + 3$.

**Example (A step that needs a case split).** Let $a^2 = b^2$ and $a + b \neq 0$. Then $a = b$. The proof first gets $(a - b)(a + b) = 0$ by `linear_combination`, then splits by `mul_eq_zero`, and closes each case.

```lean
example (a b : ℝ) (h : a ^ 2 = b ^ 2) (hab : a + b ≠ 0) : a = b := by
  have h2 : (a - b) * (a + b) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · linear_combination h3
  · exact absurd h3 hab
```

### Exercises

1. (L) Prove the formula for the difference of two cubes (`diff_cubes` in `Exercises.lean`).
2. (L) Solve the system `2 * x + y = 5`, `x - y = 1` for `x` (`solve_system` in `Exercises.lean`). Find the coefficients first.
3. (A) Tell what `ring_nf` does to the term `(x + 1) * (x - 1)` in `ℚ`.
4. (A) Prove $(x + 1)^2 + (x - 1)^2 = 2(x^2 + 1)$ by hand and with `ring`.
5. (B) Tell why `ring` cannot prove `x / x = 1` in `ℚ`. Give the value of `0 / 0` in Mathlib.
6. (B) Give a goal that `linear_combination` proves and `ring` does not. Tell what the coefficient is.
7. (B) Let $x + y = s$ and $xy = p$. Find the coefficients that prove $x^3 + y^3 = s^3 - 3ps$. Hint: $x^3 + y^3 = (x + y)^3 - 3xy(x + y)$.
8. (C) Prove that $x^2 = x$ holds for each $x$ in $\mathbb{Z}/2\mathbb{Z}$ and is not an identity of commutative rings. Use the theorem of the section to explain why `ring` fails on it.

### Reference

<?reference?>
