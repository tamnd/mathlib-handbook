---
title: Continued fractions
kind: theory
modules:
  - Mathlib.Algebra.ContinuedFractions.Basic
  - Mathlib.Algebra.ContinuedFractions.Computation.Basic
  - Mathlib.Algebra.ContinuedFractions.Computation.ApproximationCorollaries
  - Mathlib.Algebra.ContinuedFractions.Determinant
  - Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence
  - Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
explains:
  E3: [GenContFract, GenContFract.of, GenContFract.of_convergence]
  E2: [GenContFract.Pair, GenContFract.convs, GenContFract.nums, GenContFract.dens, SimpContFract, ContFract, GenContFract.IntFractPair.stream, SimpContFract.determinant, GenContFract.nums_recurrence, GenContFract.dens_recurrence, GenContFract.terminates_iff_rat, GenContFract.of_correctness_of_terminates, "GenContFract.abs_sub_convergents_le'", GenContFract.succ_nth_fib_le_of_nth_den]
  E1: auto
families: []
requires: [V06.C05, V06.C07]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Continued fractions

### Overview

A continued fraction writes a number as an integer plus the inverse of a number larger than $1$, and repeats:
$$x = a_0 + \cfrac{1}{a_1 + \cfrac{1}{a_2 + \cfrac{1}{\ddots}}}.$$
The integers $a_n$ come from the floor function of Chapter 7, and the algorithm that finds them is the Euclidean algorithm in another form. The truncations of the expansion, the convergents $p_n/q_n$, are the best rational approximations of $x$ in a precise sense. This section defines simple continued fractions, gives the algorithm, proves the recurrences for the convergents and the determinant identity $p_n q_{n-1} - p_{n-1} q_n = (-1)^{n-1}$, and proves that the expansion of $x$ is finite if and only if $x$ is rational. It then proves the error bound $|x - p_n/q_n| \le 1/(q_n q_{n+1})$, so the convergents tend to $x$. The expansions of $\sqrt 2$ and of the golden ratio serve as examples. Mathlib states all of this for an arbitrary linearly ordered field with a floor function.

### Definitions

**Definition (Finite simple continued fraction).** Let $a_0 \in \mathbb{Z}$ and $a_1, \dots, a_n$ be positive integers. The finite simple continued fraction with these terms is the number
$$[a_0; a_1, \dots, a_n] = a_0 + \cfrac{1}{a_1 + \cfrac{1}{\ddots + \cfrac{1}{a_n}}}.$$
Formally, $[a_0] = a_0$ and $[a_0; a_1, \dots, a_n] = a_0 + 1 / [a_1; a_2, \dots, a_n]$. The same formula makes sense when the last term $a_n$ is any real number $t > 0$.

The recursion is well defined: by induction, $[a_1; \dots, a_n] \ge a_1 \ge 1 > 0$, so the inverse exists.

**Definition (Continued fraction algorithm).** Let $x$ be a real number. Set $x_0 = x$. For $n \ge 0$, set $a_n = \lfloor x_n \rfloor$. If $x_n = a_n$, stop. Otherwise set
$$x_{n+1} = \frac{1}{x_n - a_n}.$$
The numbers $a_n$ are the partial quotients of $x$, and the $x_n$ are the complete quotients.

Since $0 < x_n - a_n < 1$ in the second case, $x_{n+1} > 1$, so $a_{n+1} \ge 1$. By construction $x_n = a_n + 1/x_{n+1}$, and an induction gives
$$x = [a_0; a_1, \dots, a_{n}, x_{n+1}]$$
for each $n$ at which the algorithm has not stopped.

**Definition (Convergents).** Given $a_0, a_1, a_2, \dots$, define integers by $p_{-2} = 0$, $p_{-1} = 1$, $q_{-2} = 1$, $q_{-1} = 0$ and
$$p_n = a_n p_{n-1} + p_{n-2}, \qquad q_n = a_n q_{n-1} + q_{n-2} \quad (n \ge 0).$$
The fraction $p_n / q_n$ is the $n$-th convergent.

Then $q_0 = 1$, $q_1 = a_1 \ge 1$, and $q_n \ge q_{n-1} + q_{n-2}$ for $n \ge 2$. So $q_n \ge 1$ for $n \ge 0$, the $q_n$ increase, and $q_n \ge F_{n+1}$, where $F_1 = F_2 = 1$ are the Fibonacci numbers.

::: mathlib
`GenContFract` · `Mathlib.Algebra.ContinuedFractions.Basic`

A generalized continued fraction `g : GenContFract K` has a head `g.h : K` and a possibly infinite sequence `g.s` of pairs `GenContFract.Pair K` with fields `a` and `b`. It stands for $h + a_0/(b_0 + a_1/(b_1 + \dots))$, with partial numerators `a` and partial denominators `b`. A `SimpContFract` is one with all partial numerators equal to `1`, and a `ContFract` is a simple one with positive partial denominators. Mathlib uses the general form so that the recurrences and the determinant are proved once, and the simple case follows.

<?decl GenContFract?>
:::

::: mathlib
`GenContFract.of` · `Mathlib.Algebra.ContinuedFractions.Computation.Basic`

`GenContFract.of v` is the expansion of `v : K` by the algorithm of this section, for `[DivisionRing K] [LinearOrder K] [FloorRing K]`. It is built from `GenContFract.IntFractPair.stream v`, the stream of pairs $(\lfloor x_n \rfloor, x_n - \lfloor x_n \rfloor)$. The stream stops when the fractional part is zero. The result has all partial numerators `1`, and the convergents are `(GenContFract.of v).convs n`.

<?decl GenContFract.of?>
:::

### Theorems and proofs

**Theorem (Convergents as values).** For $n \ge 0$ and each real $t > 0$,
$$[a_0; a_1, \dots, a_{n-1}, t] = \frac{t \, p_{n-1} + p_{n-2}}{t \, q_{n-1} + q_{n-2}}.$$
In particular $[a_0; a_1, \dots, a_n] = p_n / q_n$.

*Proof.* Induction on $n$. For $n = 0$ the left side is $[t] = t$, and the right side is $(t \cdot 1 + 0)/(t \cdot 0 + 1) = t$. Suppose the formula holds for $n$, for every $t > 0$. Then
$$[a_0; \dots, a_{n-1}, a_n, t] = [a_0; \dots, a_{n-1}, a_n + 1/t],$$
since by the recursive definition the last two terms $a_n$ and $t$ enter only through the number $a_n + 1/t$. Apply the hypothesis with $a_n + 1/t > 0$ in place of $t$:
$$\frac{(a_n + 1/t) p_{n-1} + p_{n-2}}{(a_n + 1/t) q_{n-1} + q_{n-2}} = \frac{p_n + p_{n-1}/t}{q_n + q_{n-1}/t} = \frac{t \, p_n + p_{n-1}}{t \, q_n + q_{n-1}}.$$
This is the formula for $n + 1$. The second claim is the case $t = a_n$, since $a_n p_{n-1} + p_{n-2} = p_n$. $\square$

::: mathlib
`GenContFract.nums_recurrence` · `Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence`

The recurrence in the general form: if the pair at position `n + 1` is `gp`, then `g.nums (n + 2) = gp.b * g.nums (n + 1) + gp.a * g.nums n`. For a simple continued fraction `gp.a = 1`, and this is $p_n = a_n p_{n-1} + p_{n-2}$ with a shift of index. The partner `GenContFract.dens_recurrence` is the same for the denominators `g.dens`. The convergent `g.convs n` equals `g.nums n / g.dens n`.

<?decl GenContFract.nums_recurrence?>
:::

**Theorem (Determinant identity).** For $n \ge -1$,
$$p_n q_{n-1} - p_{n-1} q_n = (-1)^{n-1}.$$
Consequently $\gcd(p_n, q_n) = 1$, and for $n \ge 1$
$$\frac{p_n}{q_n} - \frac{p_{n-1}}{q_{n-1}} = \frac{(-1)^{n-1}}{q_n q_{n-1}}.$$

*Proof.* For $n = -1$: $p_{-1} q_{-2} - p_{-2} q_{-1} = 1 \cdot 1 - 0 \cdot 0 = 1 = (-1)^{-2}$. Suppose the identity holds for $n - 1$. By the recurrences,
$$p_n q_{n-1} - p_{n-1} q_n = (a_n p_{n-1} + p_{n-2}) q_{n-1} - p_{n-1} (a_n q_{n-1} + q_{n-2}) = p_{n-2} q_{n-1} - p_{n-1} q_{n-2}.$$
The terms with $a_n$ cancel. The right side is $-(p_{n-1} q_{n-2} - p_{n-2} q_{n-1}) = -(-1)^{n-2} = (-1)^{n-1}$. This proves the identity.

A common divisor of $p_n$ and $q_n$ divides the left side, hence divides $\pm 1$. So $\gcd(p_n, q_n) = 1$. For the last formula, divide the identity by $q_n q_{n-1}$, which is positive for $n \ge 1$. $\square$

In matrix form the recurrences say
$$\begin{pmatrix} p_n & p_{n-1} \\ q_n & q_{n-1} \end{pmatrix} = \begin{pmatrix} a_0 & 1 \\ 1 & 0 \end{pmatrix} \cdots \begin{pmatrix} a_n & 1 \\ 1 & 0 \end{pmatrix},$$
and the identity is the determinant of both sides, since each factor has determinant $-1$. This explains the name.

::: mathlib
`SimpContFract.determinant` · `Mathlib.Algebra.ContinuedFractions.Determinant`

The statement is `s.nums n * s.dens (n + 1) - s.dens n * s.nums (n + 1) = (-1) ^ (n + 1)` for a simple continued fraction `s` that does not stop at `n`. In the notation of the theorem this is $p_n q_{n+1} - q_n p_{n+1} = (-1)^{n+1}$. The theorem for $n + 1$ reads $p_{n+1} q_n - p_n q_{n+1} = (-1)^n$. Multiply it by $-1$ to get the Mathlib form.

<?decl SimpContFract.determinant?>
:::

**Theorem (Rational numbers have finite expansions).** The algorithm stops on $x$ if and only if $x$ is rational.

*Proof.* If the algorithm stops at step $n$, then $x = [a_0; a_1, \dots, a_n]$, which is a rational number built from integers by sums and inverses.

Conversely, let $x = r_{-1} / r_0$ with integers $r_{-1}$ and $r_0 > 0$. Run the Euclidean algorithm: $r_{n-1} = a_n r_n + r_{n+1}$ with $0 \le r_{n+1} < r_n$, as long as $r_n > 0$. Claim: $x_n = r_{n-1} / r_n$ for each $n$ that the algorithm reaches. For $n = 0$ this is the choice of the fraction. If $x_n = r_{n-1}/r_n$, then
$$\frac{r_{n-1}}{r_n} = a_n + \frac{r_{n+1}}{r_n}, \qquad 0 \le \frac{r_{n+1}}{r_n} < 1,$$
so $\lfloor x_n \rfloor = a_n$ is the Euclidean quotient. If $r_{n+1} = 0$, the algorithm stops. Otherwise $x_{n+1} = 1/(x_n - a_n) = r_n / r_{n+1}$. This proves the claim. The remainders $r_0 > r_1 > r_2 > \dots \ge 0$ are a strictly decreasing sequence of natural numbers, so some $r_{n+1}$ is $0$, and the algorithm stops. $\square$

So an irrational number has an infinite expansion, and the partial quotients of a rational $a/b$ are the quotients of the Euclidean algorithm on $(a, b)$.

::: mathlib
`GenContFract.terminates_iff_rat` · `Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat`

The statement is `(GenContFract.of v).Terminates ↔ ∃ q : ℚ, v = q` in a linearly ordered field with a floor function. The direction from a finite expansion to the value is `GenContFract.of_correctness_of_terminates`: if the expansion stops, then `v` equals one of its convergents.

<?decl GenContFract.terminates_iff_rat?>
:::

**Theorem (Error bound).** Let $x$ be real and $n \ge 0$, and suppose the algorithm has not stopped at step $n$. Then
$$x - \frac{p_n}{q_n} = \frac{(-1)^n}{q_n (x_{n+1} q_n + q_{n-1})}, \qquad \left| x - \frac{p_n}{q_n} \right| \le \frac{1}{q_n q_{n+1}}.$$
The inequality is strict when the algorithm does not stop at step $n + 1$, and in particular when $x$ is irrational. If $x$ is irrational, then $p_n / q_n \to x$.

*Proof.* By the algorithm, $x = [a_0; \dots, a_n, x_{n+1}]$. The theorem on convergents with $t = x_{n+1}$ gives
$$x = \frac{x_{n+1} p_n + p_{n-1}}{x_{n+1} q_n + q_{n-1}}.$$
Subtract $p_n / q_n$ and bring both to the denominator $q_n (x_{n+1} q_n + q_{n-1})$:
$$x - \frac{p_n}{q_n} = \frac{q_n (x_{n+1} p_n + p_{n-1}) - p_n (x_{n+1} q_n + q_{n-1})}{q_n (x_{n+1} q_n + q_{n-1})} = \frac{p_{n-1} q_n - p_n q_{n-1}}{q_n (x_{n+1} q_n + q_{n-1})}.$$
By the determinant identity the numerator is $-(-1)^{n-1} = (-1)^n$. For the bound, $x_{n+1} \ge \lfloor x_{n+1} \rfloor = a_{n+1}$, so
$$x_{n+1} q_n + q_{n-1} \ge a_{n+1} q_n + q_{n-1} = q_{n+1}.$$
This gives $|x - p_n/q_n| \le 1/(q_n q_{n+1})$. Equality needs $x_{n+1} = a_{n+1}$, which means that the algorithm stops at step $n + 1$. If $x$ is irrational, it never stops, and $q_n \ge F_{n+1} \ge n$ for $n \ge 5$ gives $1/(q_n q_{n+1}) \to 0$. $\square$

The sign $(-1)^n$ shows that the even convergents lie below $x$ and the odd ones above. The bound also gives $|x - p_n/q_n| < 1/q_n^2$ for irrational $x$, which is the approximation theorem of Dirichlet.

::: mathlib
`GenContFract.abs_sub_convergents_le'` · `Mathlib.Algebra.ContinuedFractions.Computation.Approximations`

The statement is `|v - (of v).convs n| ≤ 1 / (b * (of v).dens n * (of v).dens n)`, where `b` is the next partial denominator $a_{n+1}$. Since $q_{n+1} \ge a_{n+1} q_n$, this is a little weaker than the bound of the theorem and has the same use. The growth of the denominators is `GenContFract.succ_nth_fib_le_of_nth_den`, the bound $q_n \ge F_{n+1}$.

<?decl GenContFract.abs_sub_convergents_le'?>
:::

::: mathlib
`GenContFract.of_convergence` · `Mathlib.Algebra.ContinuedFractions.Computation.ApproximationCorollaries`

The statement is `Filter.Tendsto (GenContFract.of v).convs Filter.atTop (nhds v)` in a linearly ordered field with a floor function and the order topology. The field need not be `ℝ`. A floor function forces the field to be archimedean, and the theorem holds in each such field. The form with an explicit $\varepsilon$ is `GenContFract.of_convergence_epsilon`.

<?decl GenContFract.of_convergence?>
:::

### Examples

**Example (The expansion of $415/93$).** The Euclidean algorithm gives
$$415 = 4 \cdot 93 + 43, \quad 93 = 2 \cdot 43 + 7, \quad 43 = 6 \cdot 7 + 1, \quad 7 = 7 \cdot 1 + 0.$$
So $415/93 = [4; 2, 6, 7]$. The recurrences give the convergents:

| $n$ | $-2$ | $-1$ | $0$ | $1$ | $2$ | $3$ |
|---|---|---|---|---|---|---|
| $a_n$ | | | $4$ | $2$ | $6$ | $7$ |
| $p_n$ | $0$ | $1$ | $4$ | $9$ | $58$ | $415$ |
| $q_n$ | $1$ | $0$ | $1$ | $2$ | $13$ | $93$ |

For instance $p_2 = 6 \cdot 9 + 4 = 58$ and $q_3 = 7 \cdot 13 + 2 = 93$. The determinant identity for $n = 3$ reads $415 \cdot 13 - 58 \cdot 93 = 5395 - 5394 = 1$. So $415 \cdot 13 \equiv 1 \pmod{93}$, and $13$ is the inverse of $415$ modulo $93$. The convergents give the Bezout coefficients of the Euclidean algorithm.

**Example ($\sqrt 2$ and the golden ratio).** For $x = \sqrt 2$: $a_0 = 1$ and $x_1 = 1/(\sqrt 2 - 1) = \sqrt 2 + 1$. Then $a_1 = 2$ and $x_2 = 1/(\sqrt 2 + 1 - 2) = \sqrt 2 + 1 = x_1$. The algorithm repeats, so $\sqrt 2 = [1; 2, 2, 2, \dots]$. The convergents are
$$\frac{1}{1}, \ \frac{3}{2}, \ \frac{7}{5}, \ \frac{17}{12}, \ \frac{41}{29}, \ \frac{99}{70}, \dots$$
They satisfy $p_n^2 - 2 q_n^2 = (-1)^{n+1}$: $9 - 8 = 1$, $49 - 50 = -1$, $289 - 288 = 1$. The error bound for $n = 4$ gives $|\sqrt 2 - 41/29| < 1/(29 \cdot 70) = 1/2030 \approx 0.000493$. The true error is about $0.000420$.

For the golden ratio $\varphi = (1 + \sqrt 5)/2$, the equation $\varphi^2 = \varphi + 1$ gives $\varphi = 1 + 1/\varphi$. So $x_1 = \varphi$ again, and $\varphi = [1; 1, 1, \dots]$. With all $a_n = 1$ the recurrences are the Fibonacci recurrence: $p_n = F_{n+2}$ and $q_n = F_{n+1}$. The convergents are $1, 2, 3/2, 5/3, 8/5, 13/8, \dots$ The determinant identity becomes Cassini's identity $F_{n+2} F_n - F_{n+1}^2 = (-1)^{n-1}$. Here $q_n = F_{n+1}$ is the least possible value. For this reason $\varphi$ is the irrational number that is hardest to approximate by rationals, in the sense of a theorem of Hurwitz.

**Counterexample (Expansions are not unique).** The equation $7 = 6 + 1/1$ gives $[4; 2, 6, 7] = [4; 2, 6, 6, 1]$. Both are finite simple continued fractions for $415/93$. In general $[a_0; \dots, a_n] = [a_0; \dots, a_n - 1, 1]$ when $a_n \ge 2$ (or $n = 0$). The algorithm never produces a last term $1$ at position $n \ge 1$, since that would need $x_n = 1$, while $x_n > 1$. So the expansion that the algorithm gives is unique among those with last term at least $2$. Infinite expansions have no such ambiguity.

### The library around it

The continued fractions of Mathlib live in the folder `Mathlib.Algebra.ContinuedFractions`. The basic file defines `GenContFract`, `SimpContFract` and `ContFract`, the convergents `convs` and the continuants `conts`, which pair `nums` and `dens`. The `Computation` subfolder defines `GenContFract.of` and proves its correctness, the equivalence with rationality, and the approximation results. The library states these results in a general linearly ordered field `K` with `[FloorRing K]`, not only in `ℝ`. Periodic expansions and quadratic irrationals are not part of this library.

**Common errors of a learner.**

- Using $\lfloor x \rfloor$ as truncation for negative $x$. For $x = -7/3$, $a_0 = -3$ and $x - a_0 = 2/3$, so $-7/3 = [-3; 1, 2]$.
- Starting the recurrences with the wrong values. The values $p_{-1} = 1$, $q_{-1} = 0$, $p_{-2} = 0$, $q_{-2} = 1$ are the ones that make $p_0/q_0 = a_0$.
- Mixing the index of Mathlib with the index of a textbook. In Mathlib `convs 0` is the head $a_0$, and the determinant lemma is shifted by one.
- Expecting `GenContFract.of` to produce integers in `ℤ`. Its partial denominators are elements of `K` that happen to be integers.
- Assuming the error bound with $\le$ is strict for rational $x$. At the second to last step it is an equality.

### Exercises

1. (A) Compute the expansion and all convergents of $67/29$, and check the determinant identity at the last step.
2. (A) Use the convergents of $89/55$ to find integers $u, v$ with $89 u + 55 v = 1$.
3. (A) Show that $\sqrt 3 = [1; 1, 2, 1, 2, \dots]$, and list the first five convergents.
4. (B) Show that $p_n/q_n$ is in lowest terms and that $q_{n+1} > q_n$ for $n \ge 1$.
5. (B) Show that $p_n q_{n-2} - p_{n-2} q_n = (-1)^n a_n$. Deduce that the even convergents increase and the odd convergents decrease.
6. (B) Show that $[a_0; a_1, \dots, a_n] = [a_0; a_1, \dots, a_n - 1, 1]$, and that the algorithm gives the first form.
7. (B) Let $x = [a_0; a_1, a_2, \dots]$ be irrational. Show that $|x - p_n/q_n| > 1/(q_n (q_n + q_{n+1}))$. Hint: $x_{n+1} < a_{n+1} + 1$.
8. (C) Show that if $x$ has an eventually periodic expansion, then $x$ is a root of a quadratic polynomial with integer coefficients. Hint: the purely periodic tail $y$ satisfies $y = (y p + p')/(y q + q')$.
9. (C) Show that the bound $|x - p_n/q_n| < 1/q_n^2$ holds for every irrational $x$ and every $n$, and give an infinite family of rationals $p/q$ with $|\sqrt 2 - p/q| < 1/q^2$.

### Notes and history

Continued fractions appear in the work of Bombelli (1572), who approximated $\sqrt{13}$, and of Cataldi (1613). Huygens used them to design the gears of a planetarium in the 1680s. Euler gave the theory its modern form in 1737, proved that a periodic expansion gives a quadratic irrational, and found the expansion of $e$. Lagrange proved the converse in 1770: each quadratic irrational has an eventually periodic expansion. He also used continued fractions to solve Pell's equation $x^2 - d y^2 = 1$, which the convergents of $\sqrt 2$ in the example solve for $d = 2$. Lambert used a continued fraction for $\tan x$ to prove in 1768 that $\pi$ is irrational. The Mathlib library of continued fractions was written by Kevin Kappelmann in 2019 and 2020.

### Reference

<?reference?>
