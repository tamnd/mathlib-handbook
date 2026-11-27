---
title: linarith and nlinarith
kind: tactic
modules: [Mathlib.Tactic.Linarith.Frontend]
explains:
  E2: [Mathlib.Tactic.Linarith.linarith]
  E1: [Mathlib.Tactic.Linarith.lt_irrefl, sq_nonneg]
families: []
requires: [V00]
reads_with: ["MIL"]
lean: [MathlibHandbook/V34/C03/Examples.lean, MathlibHandbook/V34/C03/Solutions.lean]
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## linarith and nlinarith

### Overview

The tactic `linarith` proves a goal that follows from the hypotheses by linear arithmetic over an ordered field. It is the step "adding the two inequalities gives the claim" of a written proof. The tactic `nlinarith` first adds products of the hypotheses, so that it can also prove some goals of degree two, such as $2ab \leq a^2 + b^2$ with the hint $(a - b)^2 \geq 0$.

The section proves the theorem behind `linarith`: a system of linear inequalities over an ordered field has no solution if and only if a combination of the inequalities with coefficients that are not negative gives the contradiction $0 < 0$. The proof is the method of elimination of Fourier and Motzkin. With this theorem, the reader knows exactly which goals `linarith` proves, and knows why it fails on a goal that needs a product, a case split or the integrality of a variable.

### What it does

#### The certificate

The tactic first collects the facts. It takes each hypothesis of the context of the form $a < b$, $a \leq b$, $a = b$ or $a \geq b$, $a > b$ over one ordered field, and the terms of the list in the call. It adds the negation of the goal: for the goal $a \leq b$ it adds $b < a$, and for the goal $a < b$ it adds $b \leq a$. For a goal $a = b$ it proves $a \leq b$ and $b \leq a$ in two runs. Each fact is put in the form $t < 0$, $t \leq 0$ or $t = 0$, where $t$ is a linear expression: a sum of numeral multiples of atoms and a constant. An atom is each maximal subterm that is not a sum or a numeral multiple: a variable, but also $x y$, $x^2$ or $f(x)$. The normal form of `ring` decides which terms are the same atom.

**Definition (Certificate of linarith).** Let $t_1 \mathrel{R_1} 0, \ldots, t_m \mathrel{R_m} 0$ be the facts, with $R_i \in \{<, \leq, =\}$. A certificate is a list of rational numbers $c_1, \ldots, c_m$ such that $c_i \geq 0$ when $R_i$ is $<$ or $\leq$, the sum $\sum c_i t_i$ is the zero expression, and $c_i > 0$ for at least one $i$ with $R_i$ equal to $<$.

From a certificate, the contradiction follows at once. The sum $\sum c_i t_i$ is a sum of terms that are negative, not positive or zero, and at least one of them is negative. So the sum is negative: $\sum c_i t_i < 0$. But the sum is the zero expression, so $0 < 0$. This is false by `Mathlib.Tactic.Linarith.lt_irrefl`. The tactic checks the identity $\sum c_i t_i = 0$ with `ring`. So the proof that `linarith` makes has three parts: the facts, the coefficients, and a call of `ring`.

To find the coefficients, `linarith` solves a linear program with the simplex method. An older oracle uses the elimination of Fourier and Motzkin. The next theorem says that the search always succeeds when the facts have no common solution.

#### The completeness theorem

To deal with constants, the tactic adds the fact $-1 < 0$. With it, a fact such as $3 \leq 0$ has the certificate $1 \cdot 3 + 3 \cdot (-1) = 0$, with a positive coefficient of the strict fact $-1 < 0$.

**Theorem (Fourier-Motzkin).** Let $K$ be an ordered field, and let $t_1, \ldots, t_m$ be affine functions on $K^n$, that is, $t_i(x) = a_i \cdot x + b_i$ with $a_i \in K^n$ and $b_i \in K$. Let $R_i \in \{<, \leq\}$ for each $i$, and assume that one of the facts is $-1 < 0$. If there is no $x \in K^n$ with $t_i(x) \mathrel{R_i} 0$ for all $i$, then there are $c_1, \ldots, c_m \geq 0$ with $\sum c_i t_i = 0$ as a function, and $c_i > 0$ for some $i$ with $R_i$ equal to $<$.

An equation $t = 0$ is the pair $t \leq 0$ and $-t \leq 0$, so the theorem covers equations too.

*Proof.* Call a list of coefficients as in the conclusion a certificate of the system. The proof is by induction on $n$.

Case $n = 0$. Each $t_i$ is a constant $b_i$. Since the system has no solution, one fact $b_i \mathrel{R_i} 0$ is false. If $R_i$ is $\leq$, then $b_i > 0$. Take $c_i = 1$, the coefficient $b_i$ for the fact $-1 < 0$, and $0$ for the other facts. The sum is $b_i - b_i = 0$, and the strict fact has the positive coefficient $b_i$. If $R_i$ is $<$, then $b_i \geq 0$. If $b_i > 0$, take the same coefficients. If $b_i = 0$, take $c_i = 1$ and $0$ for the others: the sum is $0$, and the strict fact $t_i < 0$ has a positive coefficient.

Step from $n - 1$ to $n$. Write $x = (x', y)$ with $x' \in K^{n-1}$ and $y \in K$. Divide each fact by the absolute value of its coefficient of $y$, when it is not zero. This does not change the set of solutions, and a certificate of the new system gives one of the old system, by a multiplication of the coefficients. So the facts are of three kinds:

1. $P$: $y + p_i(x') \mathrel{R_i} 0$, that is, $y \mathrel{R_i} -p_i(x')$, an upper bound for $y$;
2. $N$: $-y + q_j(x') \mathrel{R_j} 0$, that is, $q_j(x') \mathrel{R_j} y$, a lower bound for $y$;
3. $Z$: $r_k(x') \mathrel{R_k} 0$, with no $y$.

Form the new system $S'$ in the variables $x'$: the facts of $Z$, and for each pair $(i, j) \in P \times N$ the sum $p_i(x') + q_j(x') \mathrel{R_{ij}} 0$, where $R_{ij}$ is $<$ if $R_i$ or $R_j$ is $<$, and $\leq$ otherwise. The fact $-1 < 0$ is in $Z$, so it is in $S'$.

Claim: if $S'$ has a solution $x'$, then the old system has a solution $(x', y)$. Let $x'$ solve $S'$. The facts of $Z$ hold. It remains to find $y$ with $q_j(x') \mathrel{R_j} y$ for $j \in N$ and $y \mathrel{R_i} -p_i(x')$ for $i \in P$. If $N$ is empty, take $y$ smaller than each $-p_i(x')$. If $P$ is empty, take $y$ larger than each $q_j(x')$. Otherwise let $m = \max_j q_j(x')$ and $M = \min_i (-p_i(x'))$. The facts of $S'$ give $q_j(x') \leq -p_i(x')$ for all pairs, so $m \leq M$. If $m < M$, take $y = (m + M)/2$: then $q_j(x') \leq m < y < M \leq -p_i(x')$, and all the bounds hold, strict or not. If $m = M$, take $y = m$. For each index $j$ with $q_j(x') = m$ and each index $i$ with $-p_i(x') = M$, the sum $p_i(x') + q_j(x')$ is $0$. The fact of the pair $(i, j)$ holds at $x'$, so it is not strict, and both $R_i$ and $R_j$ are $\leq$. So each bound that $y = m$ meets with equality is a bound $\leq$, and each other bound holds strictly. This proves the claim.

So, since the old system has no solution, $S'$ has no solution. By the hypothesis of induction, $S'$ has a certificate. Each fact of $S'$ is a fact of the old system, or a sum of two facts of the old system. Replace each fact of $S'$ in the certificate by these old facts, with the same coefficient. The coefficients stay not negative. The sum of the old facts with these coefficients is the same function of $x'$ as before, and the variable $y$ cancels in each pair $(y + p_i) + (-y + q_j)$, so the sum is zero. A strict fact of $S'$ with a positive coefficient is in $Z$, or it is a pair with a strict member, and this member gets a positive coefficient. This is a certificate of the old system. $\square$

The theorem has two consequences for the user. If the goal follows from the facts by linear reasoning over an ordered field, `linarith` proves it, whatever the number of variables. If `linarith` fails, then there is a point of $\mathbb{Q}^n$ that satisfies all the facts and the negation of the goal, with each atom as a free variable. This point is the counterexample that explains the failure.

#### nlinarith

The tactic `nlinarith` adds facts before the call of `linarith`. For each pair of facts $t_1 \mathrel{R_1} 0$ and $t_2 \mathrel{R_2} 0$ in the list of hypotheses, the terms of the call and the negated goal, it adds the product $t_1 t_2$ with the right sign: the product of two non-positive terms is not negative, and the product of two negative terms is positive. For each square $s^2$ or $s \cdot s$ that occurs in the facts, it adds $0 \leq s^2$. Then it puts all the facts in the normal form of `ring`, where each monomial such as $x^2$ or $xy$ is an atom, and it runs the procedure of `linarith`.

**Theorem (Soundness of nlinarith).** Let $s_i \geq 0$ and $u_j > 0$ be the facts, and let $\lambda_{ij} \geq 0$ for each product. If a combination of the facts and of their pairwise products with coefficients that are not negative is the zero polynomial, and one strict fact or one product of two strict facts has a positive coefficient, then the facts are contradictory.

*Proof.* Each product of two facts that are not negative is not negative, by the rule of signs. Each product of two positive facts is positive. So the combination is a sum of terms that are not negative, with at least one positive term, and it is positive. It is also the zero polynomial, so its value is $0$. This gives $0 > 0$, a contradiction. $\square$

This is a small part of the Positivstellensatz of real algebra. The full theorem allows products of any length and sums of squares of any polynomial. The tactic `nlinarith` uses only products of degree two of the given facts. So it depends on the hints: the square $(a - b)^2$ that a proof by hand uses must be in the list.

::: mathlib
`Mathlib.Tactic.Linarith.linarith` · `Mathlib.Tactic.Linarith.Frontend`

This is the core procedure. It takes the goal and a list of terms, and it runs on all the suitable hypotheses of the context unless the flag `only_on` is true. The tactic `nlinarith` is the same procedure with a preprocessing step for the products. Before the search, a chain of preprocessing steps moves the facts from `ℕ` to `ℤ`, makes the strict inequalities of `ℤ` non-strict with a $+1$, and removes the negations.

<?decl Mathlib.Tactic.Linarith.linarith?>
:::

::: mathlib
`Mathlib.Tactic.Linarith.lt_irrefl` · `Mathlib.Tactic.Linarith.Lemmas`

The last step of each proof of `linarith`: $0 < 0$ is false. The certificate gives a proof of `0 < 0` in the ordered field, and this lemma turns it into `False`.

<?decl Mathlib.Tactic.Linarith.lt_irrefl?>
:::

::: mathlib
`sq_nonneg` · `Mathlib.Algebra.Order.Ring.Unbundled.Basic`

The square of each element of a linearly ordered ring is not negative. This is the most common hint for `nlinarith` and for `linarith`: `sq_nonneg (a - b)` is the fact $0 \leq (a - b)^2$.

<?decl sq_nonneg?>
:::

### How to use it

Write `linarith` when the goal is a linear consequence of the context. Put a fact that is not in the context into the list: `linarith [sq_nonneg b]` adds `0 ≤ b ^ 2`, and `linarith [h x]` adds the instance `h x` of a hypothesis with a quantifier, which `linarith` does not instantiate by itself. Write `linarith only [h1, h2]` to use only these facts, which is faster in a large context.

Write `nlinarith` when the proof needs a product. Give it the square or the product that a proof by hand uses: `nlinarith [sq_nonneg (a - b)]` proves `2 * a * b ≤ a ^ 2 + b ^ 2`. A product of two hypotheses can be given as a term, such as `mul_nonneg ha hb : 0 ≤ a * b`.

The tactic `linarith` also works on `ℕ` and `ℤ`, with a preprocessing step. It is sound there, but it is not complete: it reasons as if the variables were rational. A goal that needs the integrality of a variable needs `omega` (next section).

### What it cannot do

#### A product of atoms

The tactic `linarith` does not prove a fact about a product. On `0 ≤ x ^ 2` from `0 ≤ x`, it fails: `x ^ 2` is an atom with no fact. On `x * z ≤ y * z` from `x ≤ y` and `0 ≤ z`, it fails, and the message shows the facts with the negated goal:

```text
linarith failed to find a contradiction
x y z : ℝ
h : x ≤ y
hz : 0 ≤ z
a✝ : y * z < x * z
⊢ False
```

The atoms `y * z` and `x * z` have no relation to `x`, `y` and `z` for `linarith`. The tactic `nlinarith` proves the goal, since the product of `h` and `hz` is the fact that it needs.

#### A substitution

The tactic does not substitute. On `x * y = 2 * y` with `h : x = 2`, it fails, because `x * y` and `y` are two different atoms. Use `rw [h]` or `subst h` first.

#### A fact that is not an inequality

The tactic uses only facts of the forms $<$, $\leq$, $=$ and their negations. It does not use $x \neq y$. On `x < y` from `x ≠ y` and `x ≤ y`, it fails: the point $x = y$ satisfies the facts that it sees. Use `lt_of_le_of_ne`. It does not use a fact with a quantifier, or an `∧` inside a hypothesis: take them apart first (Chapter 5).

#### A goal that needs a case split or integrality

A goal that needs a case split is out of reach. On `a ≤ |a|` it fails unless the fact `le_abs_self a` is given. Over `ℤ`, the parity fact $2a + 1 \neq 2b$ is not linear over the rationals: the point $a = 0$, $b = \frac12$ satisfies $2a + 1 = 2b$. So `linarith` fails on `2 * a + 1 = 2 * b → False`, and `omega` proves it.

#### nlinarith without the right hint

The tactic `nlinarith` does not find the right square by itself in all cases. On `2 * a * b ≤ a ^ 2 + b ^ 2` with no hint, it fails: it adds $a^2 \geq 0$ and $b^2 \geq 0$, but not $(a - b)^2 \geq 0$. It multiplies only pairs, so on `0 ≤ a * b * c` from `0 ≤ a`, `0 ≤ b` and `0 ≤ c`, it fails too. Give it the product `mul_nonneg (mul_nonneg ha hb) hc`, or use `positivity`. On `x ^ 3 ≤ x` from `0 ≤ x` and `x ≤ 1`, it fails with no hint, because the proof is $x - x^3 = x(1 - x)(1 + x) \geq 0$, a product of three factors.

### Examples

**Example (Two linear facts).** From $x < y$ and $y \leq 3$, $x < 3$: the sum of the two facts. From $a + 2b \leq c$ and $0 \leq b$, $a \leq c$: the certificate is $1 \cdot (a + 2b - c) + 2 \cdot (-b) + 1 \cdot (c - a) = 0$, where the last fact is the negated goal $c < a$.

<?lean MathlibHandbook/V34/C03/Examples.lean#linarith?>

**Example (A failure that is a counterexample).** From $2x + y \leq 4$ and $x - y \leq -1$, the sum gives $3x \leq 3$, so $x \leq 1$, and `linarith` proves it. But it does not prove $x < 1$:

```text
linarith failed to find a contradiction
h1 : 2 * x + y ≤ 4
h2 : x - y ≤ -1
a✝ : 1 ≤ x
⊢ False
```

The point $x = 1$, $y = 2$ satisfies all three facts. By the theorem, this is the reason of the failure: the goal is false.

**Example (A hint).** From $a^2 + b^2 = 0$, $a^2 \leq 0$. The atoms are $a^2$ and $b^2$. The hint `sq_nonneg b` adds $0 \leq b^2$, and then the goal is linear in the two atoms: $a^2 = -b^2 \leq 0$.

<?lean MathlibHandbook/V34/C03/Examples.lean#linarith_terms?>

**Example (Products).** The inequality $2ab \leq a^2 + b^2$ needs the hint $(a - b)^2 \geq 0$. In normal form the hint is $a^2 - 2ab + b^2 \geq 0$, linear in the atoms $a^2$, $ab$ and $b^2$, and it is the goal. The second goal, $x^2 \leq x$ from $0 \leq x \leq 1$, needs no hint: the product of $x \geq 0$ and $1 - x \geq 0$ is $x - x^2 \geq 0$, and `nlinarith` adds it.

<?lean MathlibHandbook/V34/C03/Examples.lean#nlinarith?>

**Example (Three squares).** For $a, b, c \in \mathbb{R}$, $ab + bc + ca \leq a^2 + b^2 + c^2$. On paper: $2(a^2 + b^2 + c^2 - ab - bc - ca) = (a - b)^2 + (b - c)^2 + (c - a)^2 \geq 0$. The three squares are the hints.

```lean
example (a b c : ℝ) : a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
```

The certificate is the sum of the three hints with the coefficient $\frac12$ each, and the negated goal with the coefficient $1$.

**Example (A fraction).** For $x > 0$, $x + \frac1x \geq 2$. The tactic `nlinarith [sq_nonneg (x - 1)]` fails here, because $\frac1x$ is an atom with no relation to $x$. The proof by hand is $x + \frac1x - 2 = \frac{(x - 1)^2}{x} \geq 0$. In Lean, prove this identity with `field_simp` and `ring`, prove the sign with `positivity`, and close with `linarith`.

```lean
example (x : ℝ) (hx : 0 < x) : x + 1 / x ≥ 2 := by
  have key : x + 1 / x - 2 = (x - 1) ^ 2 / x := by
    field_simp
    ring
  have : 0 ≤ (x - 1) ^ 2 / x := by positivity
  linarith
```

### Exercises

1. (L) Prove `x < z + 1` from `x ≤ y` and `y < z` (`lt_add_one_of_le_of_lt` in `Exercises.lean`).
2. (L) Prove `x ^ 3 ≤ x` from `0 ≤ x` and `x ≤ 1` (`cube_le_self` in `Exercises.lean`). Find the products that `nlinarith` needs.
3. (A) Tell why `linarith` fails on `x * y = 2 * y` with `h : x = 2`, and give a proof.
4. (A) Give the linear combination that `linarith` finds for the goal `a ≤ c` from `a + 2 * b ≤ c` and `0 ≤ b`.
5. (A) Apply one step of the elimination of Fourier and Motzkin to the system $x + y \leq 2$, $-x + y \leq 0$, $-y < -1$, eliminating $x$. Decide whether the system has a solution.
6. (B) Tell why `nlinarith` with no hint fails on `0 ≤ a * b * c` from three hypotheses of sign.
7. (B) Find a point that explains the failure of `linarith` on `x < y` from `x ≠ y` and `x ≤ y`. Give a proof with a lemma of the library.
8. (B) Prove $x^2 = 4$ and $x > 0$ imply $x = 2$, by hand with the factorization $(x - 2)(x + 2) = 0$, and with `nlinarith`.
9. (C) In the proof of the theorem, the case $m = M$ uses the strictness of the pairs. Give a system of two facts in one variable with $m = M$ that has no solution, and its certificate.

### Reference

<?reference?>
