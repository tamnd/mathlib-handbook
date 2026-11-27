---
title: Pell's equation
kind: theory
modules:
  - Mathlib.NumberTheory.Pell
  - Mathlib.NumberTheory.Zsqrtd.Basic
  - Mathlib.NumberTheory.DiophantineApproximation.Basic
explains:
  E3: [Pell.Solution₁, Pell.exists_of_not_isSquare, Pell.IsFundamental, Pell.existsUnique_pos_generator]
  E2: [Pell.is_pell_solution_iff_mem_unitary, Pell.Solution₁.x_mul, Pell.Solution₁.y_mul, Pell.Solution₁.x_inv, Pell.Solution₁.y_inv, Pell.exists_iff_not_isSquare, Pell.Solution₁.exists_pos_of_not_isSquare, Pell.IsFundamental.exists_of_not_isSquare, Pell.pos_generator_iff_fundamental, Pell.IsFundamental.subsingleton, Real.exists_int_int_abs_mul_sub_le, Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational, Real.exists_rat_eq_convergent]
  E1: auto
families: [Pell.Solution₁.*, Pell.IsFundamental.*, Zsqrtd.*]
requires: [V06.C06, V06.C08, V02.C04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Pell's equation

### Overview

Let $d$ be a positive integer that is not a square. Pell's equation is $x^2 - d y^2 = 1$, to be solved in integers. It always has the trivial solutions $(\pm 1, 0)$. This section proves two theorems. First, there is a solution with $y \ne 0$. Second, among the solutions with $x, y > 0$ there is one with $x$ least, the fundamental solution $(x_1, y_1)$, and every solution comes from it: with $\varepsilon = x_1 + y_1\sqrt d$, the solutions are the pairs $(x, y)$ with $x + y\sqrt d = \pm \varepsilon^n$ for $n \in \mathbb{Z}$.

The key idea is to read the equation in the ring $\mathbb{Z}[\sqrt d]$, where the solutions are the elements of norm $1$ and form a group. Existence comes from Dirichlet's approximation theorem. Chapter 8 shows the result as the case of a real quadratic field in Dirichlet's unit theorem.

### Definitions

**Definition (The ring $\mathbb{Z}[\sqrt d]$ and its norm).** For an integer $d$, $\mathbb{Z}[\sqrt d]$ is the ring of the expressions $x + y\sqrt d$ with $x, y \in \mathbb{Z}$, with the product $(x + y\sqrt d)(u + v\sqrt d) = (xu + dyv) + (xv + yu)\sqrt d$. The conjugate of $\alpha = x + y\sqrt d$ is $\overline\alpha = x - y\sqrt d$, and its norm is $N(\alpha) = \alpha\overline\alpha = x^2 - dy^2$.

Remarks. Conjugation is a ring automorphism, so $N(\alpha\beta) = N(\alpha)N(\beta)$, as for the Gaussian integers of Volume 6, Chapter 6, which are the case $d = -1$. An element $\alpha$ is a unit if and only if $N(\alpha) = \pm 1$: if $\alpha\beta = 1$, then $N(\alpha)N(\beta) = 1$ in $\mathbb{Z}$, and if $N(\alpha) = \pm 1$, then $\pm\overline\alpha$ is an inverse. For $d > 0$ not a square, $\sqrt d$ is irrational (Volume 2, Chapter 4), so $\mathbb{Z}[\sqrt d]$ embeds in $\mathbb{R}$, and the text compares elements by size.

::: mathlib
`Zsqrtd` · `Mathlib.NumberTheory.Zsqrtd.Basic`

The type `ℤ√d` has two integer fields `re` and `im`. It is defined for each `d : ℤ`, with no map to `ℝ`. The conjugate is `star`, and the norm is `Zsqrtd.norm`.

<?decl Zsqrtd?>
:::

**Definition (Solutions of Pell's equation).** A solution of Pell's equation for $d$ is a pair $(x, y) \in \mathbb{Z}^2$ with $x^2 - dy^2 = 1$, identified with the element $x + y\sqrt d$ of norm $1$. A solution is nontrivial if $y \ne 0$. It is fundamental if $x > 1$, $y > 0$, and $x$ is least among the solutions with $x > 1$.

Remarks. The solutions are the elements of norm $1$, so they form a subgroup of the units of $\mathbb{Z}[\sqrt d]$. In coordinates, the product and the inverse are
$$(x, y)(u, v) = (xu + dyv, \ xv + yu), \qquad (x, y)^{-1} = (x, -y).$$
The equation $x^2 - dy^2 = -1$ is a different problem. Its solutions are the units of norm $-1$, and for some $d$ there are none: for $d = 3$, $x^2 \equiv -1 \pmod 3$ has no solution.

::: mathlib
`Pell.Solution₁` · `Mathlib.NumberTheory.Pell`

`Pell.Solution₁ d` is the subgroup `unitary (ℤ√d)` as a type, so the solutions form a commutative group. The coordinates are `Pell.Solution₁.x` and `Pell.Solution₁.y`. The formulas of the remark are `Pell.Solution₁.x_mul`, `Pell.Solution₁.y_mul`, `Pell.Solution₁.x_inv` and `Pell.Solution₁.y_inv`, and the link with the equation is `Pell.is_pell_solution_iff_mem_unitary`.

<?decl Pell.Solution₁?>
:::

::: mathlib
`Pell.IsFundamental` · `Mathlib.NumberTheory.Pell`

`IsFundamental a` says `1 < a.x`, `0 < a.y`, and `a.x ≤ b.x` for each solution `b` with `1 < b.x`. The definition does not assume that `d` is a positive nonsquare; lemmas deduce this from the existence of such an `a`.

<?decl Pell.IsFundamental?>
:::

### Theorems and proofs

**Lemma (Dirichlet's approximation theorem).** Let $\xi$ be real and $n \ge 1$ an integer. There are integers $p$ and $q$ with $1 \le q \le n$ and $|q\xi - p| \le \frac{1}{n + 1}$.

*Proof.* Consider the $n + 2$ numbers $0$, $1$ and the fractional parts $\{k\xi\} = k\xi - \lfloor k\xi \rfloor$ for $k = 1, \dots, n$. All lie in $[0, 1]$. Divide $[0, 1]$ into the $n + 1$ intervals $\left[\frac{i}{n+1}, \frac{i+1}{n+1}\right]$. By the pigeonhole principle two of the $n + 2$ numbers lie in one interval. Each of the numbers has the form $k\xi - m$ with integers $0 \le k \le n$ and $m$: the number $0$ is $0\xi - 0$ and the number $1$ is $0\xi - (-1)$. Two numbers with the same $k$ are $0$ and $1$, which lie in one interval only for $n = 0$. So the two numbers are $k\xi - m$ and $k'\xi - m'$ with $k \ne k'$. Their difference is $(k - k')\xi - (m - m')$, and its absolute value is at most $\frac1{n+1}$. Put $q = |k - k'|$ and $p = \pm(m - m')$ with the same sign. $\square$

**Corollary.** If $\xi$ is irrational, there are infinitely many pairs of integers $(p, q)$ with $q \ge 1$ and $|q\xi - p| < \frac1q$.

*Proof.* The lemma gives pairs with $|q\xi - p| \le \frac{1}{n+1} < \frac1n \le \frac1q$. Suppose only finitely many pairs satisfy the inequality. Since $\xi$ is irrational, $|q\xi - p| > 0$ for each of them, so some $\frac1{n+1}$ is less than all these values, and the lemma for this $n$ gives a new pair, a contradiction. $\square$

::: mathlib
`Real.exists_int_int_abs_mul_sub_le` · `Mathlib.NumberTheory.DiophantineApproximation.Basic`

The lemma: for `0 < n`, `∃ j k, 0 < k ∧ k ≤ n ∧ |k * ξ - j| ≤ 1 / (n + 1)`. The corollary in the form with rational numbers is `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational`: the set of `q : ℚ` with `|ξ - q| < 1 / q.den ^ 2` is infinite.

<?decl Real.exists_int_int_abs_mul_sub_le?>
:::

**Theorem (Existence).** Let $d > 0$ be an integer that is not a square. Then $x^2 - dy^2 = 1$ has a solution with $y \ne 0$.

*Proof.* Step 1. By the corollary for $\xi = \sqrt d$, there are infinitely many pairs $(p, q)$ with $q \ge 1$ and $|p - q\sqrt d| < \frac1q$. For each of them $|p + q\sqrt d| \le |p - q\sqrt d| + 2q\sqrt d < \frac1q + 2q\sqrt d$, so
$$|p^2 - dq^2| = |p - q\sqrt d|\,|p + q\sqrt d| < \frac1q \left(\frac1q + 2q\sqrt d\right) \le 1 + 2\sqrt d.$$
The value $p^2 - dq^2$ is an integer, and it is not $0$ since $\sqrt d$ is irrational. So it takes one of finitely many values. Hence there is an integer $k \ne 0$ such that infinitely many of the pairs satisfy $p^2 - dq^2 = k$.

Step 2. There are only $k^2$ pairs of residues modulo $|k|$. So two different pairs $(p_1, q_1)$ and $(p_2, q_2)$ of step 1 with norm $k$ satisfy $p_1 \equiv p_2$ and $q_1 \equiv q_2 \pmod{|k|}$. Since the $q_i$ are positive and the pairs differ, $\alpha_1 = p_1 + q_1\sqrt d$ is neither $\alpha_2$ nor $-\alpha_2$. Put
$$\alpha = \frac{\alpha_1 \overline{\alpha_2}}{k} = \frac{p_1p_2 - dq_1q_2}{k} + \frac{p_2q_1 - p_1q_2}{k}\sqrt d.$$

Step 3. The coefficients are integers. Modulo $|k|$, replace $p_2$ by $p_1$ and $q_2$ by $q_1$: the first numerator becomes $p_1^2 - dq_1^2 = k \equiv 0$, and the second becomes $p_1q_1 - p_1q_1 = 0$. So $\alpha = x + y\sqrt d \in \mathbb{Z}[\sqrt d]$. Its norm is $N(\alpha_1)N(\alpha_2)/k^2 = 1$.

Step 4. $y \ne 0$. If $y = 0$, then $x^2 = 1$ and $\alpha = \pm1$. Then $\alpha_1\overline{\alpha_2} = \pm k = \pm\alpha_2\overline{\alpha_2}$, and division by $\overline{\alpha_2} \ne 0$ gives $\alpha_1 = \pm\alpha_2$, which step 2 excludes. $\square$

::: mathlib
`Pell.exists_of_not_isSquare` · `Mathlib.NumberTheory.Pell`

The theorem: `0 < d → ¬IsSquare d → ∃ x y, x ^ 2 - d * y ^ 2 = 1 ∧ y ≠ 0`. The converse also holds: for a square $d = e^2$, the equation $(x - ey)(x + ey) = 1$ forces $y = 0$. Both directions together are `Pell.exists_iff_not_isSquare`.

<?decl Pell.exists_of_not_isSquare?>
:::

**Lemma (Positive solutions).** Let $d > 0$ be a nonsquare, and let $\alpha = x + y\sqrt d$ be a solution, viewed as a real number. Then $\alpha > 0$ if and only if $x > 0$, and $\alpha > 1$ if and only if $x > 0$ and $y > 0$.

*Proof.* Since $x^2 = 1 + dy^2 > dy^2$, $|x| > |y|\sqrt d$. So $\alpha = x + y\sqrt d$ has the sign of $x$. If $x, y > 0$, then $\alpha \ge 1 + \sqrt d > 1$. Conversely, let $\alpha > 1$. Then $\overline\alpha = \alpha^{-1} \in (0, 1)$, because $\alpha\overline\alpha = 1$. So $x = \frac{\alpha + \overline\alpha}{2} > 0$ and $y\sqrt d = \frac{\alpha - \overline\alpha}{2} > 0$. $\square$

**Theorem (The fundamental solution generates).** Let $d > 0$ be a nonsquare. There is exactly one fundamental solution $\varepsilon = x_1 + y_1\sqrt d$, and the solutions are exactly the elements $\pm\varepsilon^n$ with $n \in \mathbb{Z}$.

*Proof.* By the existence theorem there is a solution with $y \ne 0$. Changing the signs of $x$ and $y$ gives one with $x > 0$ and $y > 0$, and then $x > 1$ since $x^2 = 1 + dy^2 > 1$. So the set of $x > 1$ that occur in solutions is not empty, and it has a least element $x_1$. The equation gives $y_1 = \sqrt{(x_1^2 - 1)/d} > 0$, so the fundamental solution is unique.

Let $G$ be the set of solutions $\alpha > 0$, a subgroup of the multiplicative group $\mathbb{R}_{>0}$. For $\alpha \in G$ with $\alpha > 1$ the lemma gives $x, y > 0$, and $\alpha = x + \sqrt{x^2 - 1}$ is an increasing function of $x$. So $\varepsilon$ is the least element of $G$ that is greater than $1$.

Let $\alpha \in G$. Since $\varepsilon > 1$, the powers $\varepsilon^n$ for $n \in \mathbb{Z}$ tend to $0$ and to $\infty$, so there is $n \in \mathbb{Z}$ with $\varepsilon^n \le \alpha < \varepsilon^{n+1}$. Then $\beta = \alpha\varepsilon^{-n} \in G$ and $1 \le \beta < \varepsilon$. By the minimality of $\varepsilon$, $\beta = 1$, so $\alpha = \varepsilon^n$. Every solution is $\alpha$ or $-\alpha$ with $\alpha \in G$, by the lemma. Conversely each $\pm\varepsilon^n$ has norm $(\pm1)^2 N(\varepsilon)^n = 1$. $\square$

So the group of solutions is isomorphic to $\{\pm 1\} \times \mathbb{Z}$, by $(\pm1, n) \mapsto \pm\varepsilon^n$.

::: mathlib
`Pell.existsUnique_pos_generator` · `Mathlib.NumberTheory.Pell`

The theorem: there is a unique `a₁` with `1 < a₁.x`, `0 < a₁.y` and `∀ a, ∃ n : ℤ, a = a₁ ^ n ∨ a = -a₁ ^ n`. Mathlib does not map the solutions to `ℝ`; it uses a descent on $x$ in place of the real order. The lemma `Pell.pos_generator_iff_fundamental` says that the generators of the theorem are exactly the fundamental solutions.

<?decl Pell.existsUnique_pos_generator?>
:::

**Proposition (Solutions and continued fractions).** If $x^2 - dy^2 = 1$ with $x, y > 0$, then $x/y$ is a convergent of the continued fraction of $\sqrt d$.

*Proof.* From $(x - y\sqrt d)(x + y\sqrt d) = 1$ and $x + y\sqrt d > 2y\sqrt d$,
$$0 < \frac xy - \sqrt d = \frac{1}{y(x + y\sqrt d)} < \frac{1}{2y^2\sqrt d} < \frac{1}{2y^2}.$$
Legendre's criterion says that a fraction $p/q$ with $|\xi - p/q| < \frac{1}{2q^2}$ is a convergent of $\xi$. Volume 6, Chapter 8 defines the convergents; this section uses the criterion without proof, in the Mathlib form below. $\square$

::: mathlib
`Real.exists_rat_eq_convergent` · `Mathlib.NumberTheory.DiophantineApproximation.Basic`

Legendre's criterion: `|ξ - q| < 1 / (2 * q.den ^ 2) → ∃ n, q = ξ.convergent n`. Here `Real.convergent` is defined by recursion on `ℝ`.

<?decl Real.exists_rat_eq_convergent?>
:::

### Examples

**Example ($d = 2$).** The continued fraction $\sqrt 2 = [1; 2, 2, 2, \dots]$ has the convergents $1, \frac32, \frac75, \frac{17}{12}, \dots$. Test them: $1 - 2 = -1$, $9 - 8 = 1$. So $\varepsilon = 3 + 2\sqrt 2$ is fundamental, since no solution has $1 < x < 3$ ($x = 2$ gives $2y^2 = 3$). The powers are
$$\varepsilon^2 = 17 + 12\sqrt 2, \qquad \varepsilon^3 = (17 + 12\sqrt 2)(3 + 2\sqrt 2) = 99 + 70\sqrt 2,$$
and $99^2 - 2 \cdot 70^2 = 9801 - 9800 = 1$. The convergent $\frac75$ gives $49 - 50 = -1$, a solution of the negative equation.

**Example ($d = 7$ and $d = 61$).** For $d = 7$ search $y = 1, 2, 3$: $7y^2 + 1 = 8, 29, 64$, and $64 = 8^2$. So $\varepsilon = 8 + 3\sqrt 7$. For $d = 61$ the fundamental solution is
$$x_1 = 1766319049, \qquad y_1 = 226153980,$$
and a search by $y$ would take more than $2 \cdot 10^8$ steps. The continued fraction of $\sqrt{61}$ finds it in a few lines.

**Counterexample (A square $d$).** For $d = 4$, $x^2 - 4y^2 = (x - 2y)(x + 2y) = 1$ forces $x - 2y = x + 2y = \pm1$, so $y = 0$. So the hypothesis that $d$ is not a square is needed; it enters in step 1.

**Counterexample (A negative $d$).** For $d = -2$, $x^2 + 2y^2 = 1$ has only the solutions $(\pm1, 0)$. For $d < 0$ the group of solutions is finite, so the hypothesis $d > 0$ is needed.

### The library around it

The file `Mathlib.NumberTheory.Pell` has three layers: the group `Pell.Solution₁ d` with its coordinate lemmas, existence (`Pell.exists_of_not_isSquare`, `Pell.Solution₁.exists_pos_of_not_isSquare`), and the fundamental solution (`Pell.IsFundamental.exists_of_not_isSquare`, `Pell.IsFundamental.subsingleton`). The file `Mathlib.NumberTheory.PellMatiyasevic` treats the case $d = a^2 - 1$ with explicit recursions.

Common errors of a learner:

- The definition of `Pell.IsFundamental` compares `x` only with solutions with `1 < x`. The trivial solution `1` has `x = 1` and is not compared.

### Exercises

1. (A) Find the fundamental solution for $d = 3, 5, 6, 8$ by a search on $y$.
2. (A) Compute $\varepsilon^4$ for $d = 2$ and check that it solves the equation.
3. (A) Show that the solutions $(x_n, y_n)$ given by $\varepsilon^n$ satisfy $x_{n+1} = 2x_1 x_n - x_{n-1}$ and the same recursion for $y_n$.
4. (B) Show that $x^2 - 3y^2 = -1$ and $x^2 - 7y^2 = -1$ have no solutions. Hint: work modulo $3$ and modulo $4$.
5. (B) Find all positive integers $n$ such that $1 + 2 + \cdots + n$ is a square. Hint: $n(n+1)/2 = m^2$ becomes $(2n + 1)^2 - 8m^2 = 1$.
6. (B) Show that if $x^2 - dy^2 = -1$ has a solution, then the fundamental solution of the $+1$ equation is the square of the least positive solution of the $-1$ equation.
7. (C) Let $d > 0$ be a nonsquare and $k \ne 0$. Show that the solutions of $x^2 - dy^2 = k$ fall into finitely many classes under multiplication by the solutions of Pell's equation. Hint: in each class there is a solution $\alpha$ with $1 \le |\alpha| < \varepsilon$.

### Notes and history

The equation is named after John Pell by a mistake of Euler; Pell did not work on it. Brahmagupta in the seventh century gave the composition rule that makes the solutions a group, and the cyclic method of Bhaskara II in the twelfth century solves the equation for $d = 61$. Lagrange gave the first complete proof of the existence theorem in 1768, with continued fractions. The proof by approximation in this section is due to Dirichlet. A reference is Niven, Zuckerman and Montgomery, *An Introduction to the Theory of Numbers*, Chapter 7.

### Reference

<?reference?>
