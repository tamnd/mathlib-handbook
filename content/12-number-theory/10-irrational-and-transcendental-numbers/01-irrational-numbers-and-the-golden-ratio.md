---
title: Irrational numbers, the golden ratio and Niven's theorem
kind: api
modules:
  - Mathlib.NumberTheory.Real.Irrational
  - Mathlib.NumberTheory.Real.GoldenRatio
  - Mathlib.NumberTheory.Niven
  - Mathlib.NumberTheory.Rayleigh
explains:
  E2: [irrational_nrt_of_notint_nrt, irrational_sqrt_natCast_iff, Real.goldenRatio_irrational, Real.coe_fib_eq, niven, irrational_cos_rat_mul_pi, Irrational.beattySeq_symmDiff_beattySeq_pos]
  E1: auto
families: []
requires: [V02.C04, V15.C06, V11]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Irrational numbers, the golden ratio and Niven's theorem

### Overview

A real number is irrational when it is not a quotient of two integers. Volume 2 defined the predicate `Irrational` and proved that $\sqrt2$ is irrational. This section describes the rest of the library on irrational numbers: the closure rules under the field operations with rational numbers, the criterion for $n$-th roots of integers, and a decision procedure for square roots of numerals.

Three modules then apply the predicate. The golden ratio $\varphi = \frac{1 + \sqrt5}{2}$ and its conjugate $\psi = \frac{1 - \sqrt5}{2}$ are irrational, and they give Binet's formula for the Fibonacci numbers. Niven's theorem says that $\cos(\pi r)$ for rational $r$ is rational only for five values. Rayleigh's theorem says that two Beatty sequences $\lfloor k r \rfloor$ and $\lfloor k s \rfloor$ with $\frac1r + \frac1s = 1$ and $r$ irrational partition the positive integers. The next section of this chapter goes from irrational numbers to transcendental numbers.

### The library around it

#### The predicate and its closure rules

`Irrational x` for `x : ℝ` is the statement `x ∉ Set.range ((↑) : ℚ → ℝ)`. The lemma `irrational_iff_ne_rational` gives the paper form: $x \ne a/b$ for all integers $a$ and $b \ne 0$. The rational numbers, the integers and the natural numbers are not irrational (`Rat.not_irrational`, `Int.not_irrational`, `Nat.not_irrational`, `not_irrational_zero`, `not_irrational_one`, `not_irrational_ofNat`). In the other direction, `exists_rat_of_not_irrational` gives a rational $q$ with $x = q$ from `¬Irrational x`. Between two real numbers there is an irrational number (`exists_irrational_btwn`), and a transcendental number is irrational (`Transcendental.irrational`).

The closure rules form one family with a regular naming pattern. Let $x$ be irrational and $q$ rational. Then $q + x$, $x + q$, $q - x$, $x - q$ and $-x$ are irrational, and $q x$, $x q$, $q / x$, $x / q$ and $x^{-1}$ are irrational when $q \ne 0$. Each rule has three forms, for a cast from `ℚ`, `ℤ` and `ℕ`, and the name says which cast and on which side it is.

| Lean name | Statement |
|---|---|
| `Irrational.ratCast_add` | $x$ irrational implies $q + x$ irrational |
| `Irrational.add_intCast` | $x$ irrational implies $x + m$ irrational, for $m \in \mathbb{Z}$ |
| `Irrational.natCast_sub` | $x$ irrational implies $n - x$ irrational, for $n \in \mathbb{N}$ |
| `Irrational.mul_ratCast` | $x$ irrational and $q \ne 0$ imply $x q$ irrational |
| `Irrational.intCast_div` | $x$ irrational and $m \ne 0$ imply $m / x$ irrational |
| `Irrational.of_ratCast_add` | $q + x$ irrational implies $x$ irrational |
| `irrational_ratCast_add_iff` | $q + x$ is irrational if and only if $x$ is irrational |
| `irrational_mul_natCast_iff` | $x n$ is irrational if and only if $n \ne 0$ and $x$ is irrational |

The names without a prefix go forward from $x$. The names with `of_` go backward to $x$. The names `irrational_..._iff` state both directions, and they are the form to give to `simp`. Several rules go backward from an operation of two real numbers: `Irrational.add_cases` says that if $x + y$ is irrational, then $x$ or $y$ is irrational, and `Irrational.mul_cases` and `Irrational.div_cases` are the same for the product and the quotient. The rules `Irrational.of_pow`, `Irrational.of_zpow` and `Irrational.of_mul_self` come from the fact that a power of a rational number is rational. The lemmas `Irrational.ne_rat`, `Irrational.ne_int`, `Irrational.ne_nat`, `Irrational.ne_zero` and `Irrational.ne_one` turn the predicate into inequalities.

#### Roots of integers

**Proposition.** Let $x \in \mathbb{R}$, $n \ge 1$ and $m \in \mathbb{Z}$ with $x^n = m$. If $x$ is not an integer, then $x$ is irrational.

*Proof.* Suppose that $x = a/b$ with $b \ge 1$ and $\gcd(a, b) = 1$. Then $a^n = m b^n$, so $b^n \mid a^n$. Since $\gcd(a^n, b^n) = 1$, $b^n = 1$, so $b = 1$ and $x = a$ is an integer. $\square$

This is `irrational_nrt_of_notint_nrt`. The form `irrational_nrt_of_n_not_dvd_multiplicity` replaces the hypothesis on $x$ by a hypothesis on $m$: if $n$ does not divide the multiplicity of a prime $p$ in $m$, then $m$ is not an $n$-th power and $x$ is irrational. For square roots the criterion is an equivalence: `irrational_sqrt_natCast_iff` says that $\sqrt n$ is irrational if and only if $n$ is not a square (`¬IsSquare n`). The forms `irrational_sqrt_intCast_iff` and `irrational_sqrt_ratCast_iff` add the condition $0 \le z$ or $0 \le q$, because `Real.sqrt` of a negative number is $0$. The special cases `irrational_sqrt_two` and `Nat.Prime.irrational_sqrt` are the ones of Volume 2. The lemma `one_lt_natDegree_of_irrational_root` says that an irrational root of a nonzero integer polynomial forces the degree to be at least $2$.

The module has `Decidable` instances for `Irrational √n` with `n` a numeral or a cast of a natural number, an integer or a rational number (`instDecidableIrrationalSqrtCastReal`, `instDecidableIrrationalSqrtOfNatReal`). With them `decide` proves a statement such as `Irrational √8` or `¬Irrational √9`. The module docstring warns that the square root function of the natural numbers is sealed for the kernel, so the proof needs a command that unseals it before the theorem.

#### The golden ratio and Binet's formula

`Real.goldenRatio` is $\varphi = \frac{1 + \sqrt5}{2}$ and `Real.goldenConj` is $\psi = \frac{1 - \sqrt5}{2}$. After `open goldenRatio`, the notations `φ` and `ψ` denote them. Both are roots of $X^2 - X - 1$, so the library has the identities of a quadratic pair.

| Lean name | Statement |
|---|---|
| `Real.goldenRatio_sq` | $\varphi^2 = \varphi + 1$ |
| `Real.goldenConj_sq` | $\psi^2 = \psi + 1$ |
| `Real.goldenRatio_add_goldenConj` | $\varphi + \psi = 1$ |
| `Real.goldenRatio_mul_goldenConj` | $\varphi \psi = -1$ |
| `Real.goldenRatio_sub_goldenConj` | $\varphi - \psi = \sqrt5$ |
| `Real.inv_goldenRatio` | $\varphi^{-1} = -\psi$ |
| `Real.one_sub_goldenConj` | $1 - \psi = \varphi$ |
| `Real.goldenRatio_pow_sub_goldenRatio_pow` | $\varphi^{n+2} - \varphi^{n+1} = \varphi^n$ |

The order facts are `Real.one_lt_goldenRatio`, `Real.goldenRatio_lt_two`, `Real.goldenRatio_pos`, `Real.goldenConj_neg` and `Real.neg_one_lt_goldenConj`. Both numbers are irrational (`Real.goldenRatio_irrational`, `Real.goldenConj_irrational`): $\sqrt5$ is irrational by `irrational_sqrt_natCast_iff`, since $5$ is not a square, and $\varphi = \frac12 + \frac12\sqrt5$ is irrational by the closure rules.

**Theorem (Binet's formula).** For each $n \in \mathbb{N}$, $F_n = \dfrac{\varphi^n - \psi^n}{\sqrt5}$, where $F_0 = 0$, $F_1 = 1$ and $F_{n+2} = F_{n+1} + F_n$.

*Proof.* The sequences $\varphi^n$ and $\psi^n$ satisfy $u_{n+2} = u_{n+1} + u_n$, because $\varphi^2 = \varphi + 1$ and $\psi^2 = \psi + 1$. So $v_n = (\varphi^n - \psi^n)/\sqrt5$ satisfies the same recurrence. Also $v_0 = 0$ and $v_1 = (\varphi - \psi)/\sqrt5 = 1$. A solution of a recurrence of order $2$ is determined by its first two terms, so $v_n = F_n$ for all $n$. $\square$

In Lean the statement is `Real.coe_fib_eq`, with `Nat.fib` on the left. The proof uses the type `LinearRecurrence` of the library: `Real.fibRec` is the recurrence $u_{n+2} = u_{n+1} + u_n$, `Real.fib_isSol_fibRec`, `Real.geom_goldenRatio_isSol_fibRec` and `Real.geom_goldenConj_isSol_fibRec` say that the three sequences are solutions in the sense of `LinearRecurrence.IsSolution`, and `Real.fibRec_charPoly_eq` computes the characteristic polynomial $X^2 - (X + 1)$. The form `Real.coe_intFib_eq` extends the formula to `Int.fib` and integer $n$. The identities `Real.goldenRatio_mul_fib_succ_add_fib` ($\varphi F_{n+1} + F_n = \varphi^{n+1}$) and `Real.fib_succ_sub_goldenRatio_mul_fib` ($F_{n+1} - \varphi F_n = \psi^n$) are the matrix form of the same computation.

#### Niven's theorem

The module `Mathlib.NumberTheory.Niven` begins with algebraic facts on the values of the trigonometric functions at rational multiples of $\pi$. For $q \in \mathbb{Q}$, $z = e^{i \pi q}$ satisfies $z^{2d} = 1$ with $d$ the denominator of $q$ (`Complex.exp_rat_mul_pi_mul_I_pow_two_mul_den`), so $z$ is an algebraic integer (`Complex.isIntegral_exp_rat_mul_pi_mul_I`). Then $2 \cos(\pi q) = z + z^{-1}$ and $2 \sin(\pi q)$ are algebraic integers (`Real.isIntegral_two_mul_cos_rat_mul_pi`, `Real.isIntegral_two_mul_sin_rat_mul_pi`), and the values of $\cos$, $\sin$ and $\tan$ are algebraic (`Real.isAlgebraic_cos_rat_mul_pi`, `Real.isAlgebraic_tan_rat_mul_pi`). Each of these has a complex form in the namespace `Complex`.

**Theorem (Niven).** Let $\theta = \pi r$ with $r \in \mathbb{Q}$. If $\cos\theta$ is rational, then $\cos\theta \in \{-1, -\frac12, 0, \frac12, 1\}$.

*Proof.* The number $2\cos\theta$ is an algebraic integer by the facts above. A rational algebraic integer is an integer, since $\mathbb{Z}$ is integrally closed. So $2\cos\theta$ is an integer in $[-2, 2]$, and $2\cos\theta \in \{-2, -1, 0, 1, 2\}$. $\square$

The Lean statement `niven` takes the hypotheses in the form `∃ r : ℚ, θ = r * π` and `∃ q : ℚ, cos θ = q`. The form `niven_sin` is the same for the sine. The forms `niven_angle_eq` and `niven_angle_div_pi_eq` give the angles: for $\theta \in [0, \pi]$ with a rational cosine, $\theta \in \{0, \frac\pi3, \frac\pi2, \frac{2\pi}3, \pi\}$. The form `niven_fract_angle_div_pi_eq` states it for the fractional part `Int.fract r`. A consequence is `irrational_cos_rat_mul_pi`: if the denominator of $r$ is greater than $3$, then $\cos(\pi r)$ is irrational. For example, $\cos\frac\pi5 = \frac\varphi2$ is irrational, as the previous paragraph also shows.

#### Beatty sequences and Rayleigh's theorem

For a real number $r$, `beattySeq r k` is $\lfloor k r \rfloor$ and `beattySeq' r k` is $\lceil k r \rceil - 1$, for $k \in \mathbb{Z}$. The two sequences differ only at the $k$ with $k r \in \mathbb{Z}$, and `Irrational.beattySeq'_pos_eq` says that for irrational $r$ the sets of positive terms are equal. The hypothesis $\frac1r + \frac1s = 1$ with $r, s > 0$ is written `r.HolderConjugate s` in Lean, the name of the same condition for the exponents of Hölder's inequality.

**Theorem (Rayleigh).** Let $r, s > 0$ with $\frac1r + \frac1s = 1$ and $r$ irrational. Then each positive integer is in exactly one of the sets $\{\lfloor k r \rfloor : k \ge 1\}$ and $\{\lfloor k s \rfloor : k \ge 1\}$.

*Proof.* Here $r, s > 1$, and $s = r/(r - 1)$ is irrational. Both sequences are strictly increasing in $k$, since $r, s > 1$. Fix an integer $n \ge 1$. Then $\lfloor k r \rfloor < n$ if and only if $k r < n$, that is $k < n/r$. Since $n/r$ is irrational, the number of such $k \ge 1$ is $\lfloor n/r \rfloor$. In the same way, $\lfloor n/s \rfloor$ terms of the second sequence are less than $n$. Since $n/r + n/s = n$ and both terms are not integers, $\lfloor n/r \rfloor + \lfloor n/s \rfloor = n - 1$. So, for each $n$, exactly $n - 1$ terms of the two sequences together are less than $n$, and exactly $n$ terms are less than $n + 1$. So exactly one term is equal to $n$. $\square$

The Lean statement `Irrational.beattySeq_symmDiff_beattySeq_pos` says that the symmetric difference of the two sets of positive terms is the set of positive integers: they are disjoint, and their union is everything. The library proves first the general forms `compl_beattySeq` and `compl_beattySeq'` without irrationality, for all $k \in \mathbb{Z}$: the complement of $\{\lfloor k r \rfloor\}$ is $\{\lceil k s \rceil - 1\}$. The forms `beattySeq_symmDiff_beattySeq'_pos` and `beattySeq'_symmDiff_beattySeq_pos` are the versions for positive terms with one sequence of each kind. For $r = \varphi$, $s = \varphi^2$, and the theorem splits the positive integers into $1, 3, 4, 6, 8, \dots$ and $2, 5, 7, 10, 13, \dots$.

#### Common errors

1. `Irrational` is a predicate on `ℝ` only. For an element of another field, such as `ℂ`, the statement must go through a real number or through `Transcendental ℚ`.
2. `Real.sqrt` of a negative number is $0$, which is rational. So `irrational_sqrt_intCast_iff` has the condition `0 ≤ z`, and a statement about $\sqrt{-2}$ is false in Lean.
3. In Niven's theorem the angle must be a rational multiple of $\pi$ in the form `↑r * π`. The theorem says nothing about $\cos q$ for rational $q$ in radians.

### Exercises

1. (A) Use the closure rules to show that $3 - \frac{\sqrt2}{5}$ is irrational, and name the Lean lemmas of each step.
2. (A) Show that $\sqrt[3]{2}$ is irrational with the proposition on roots of integers.
3. (A) Show that $\varphi^n = F_n \varphi + F_{n-1}$ for $n \ge 1$, and deduce that $\varphi^n$ is irrational for $n \ge 1$.
4. (B) Show that $\cos\frac{2\pi}{7}$ is irrational with Niven's theorem, and compute the degree of $2\cos\frac{2\pi}7$ over $\mathbb{Q}$.
5. (B) Let $r = \sqrt2$. Find $s$ with $\frac1r + \frac1s = 1$, and write the first eight terms of each Beatty sequence.
6. (A) Show that Rayleigh's theorem fails for rational $r$: for $r = s = 2$, find the integers that are in both sets or in none.

### Reference

<?reference?>
