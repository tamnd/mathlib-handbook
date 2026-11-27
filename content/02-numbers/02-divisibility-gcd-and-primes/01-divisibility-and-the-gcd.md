---
title: Divisibility, the gcd and Bézout's identity
kind: theory
modules:
  - Mathlib.Data.Nat.GCD.Basic
  - Mathlib.Data.Int.GCD
explains:
  E3: [Nat.gcd_eq_gcd_ab, Int.gcd_eq_gcd_ab]
  E2: [Nat.gcdA, Nat.gcdB, Nat.xgcd, Nat.xgcd_val, Nat.gcd_greatest, Int.gcd_dvd_iff, Int.gcd_least_linear, Nat.Coprime.dvd_mul_left, Nat.Coprime.dvd_mul_right, Nat.Coprime.lcm_eq_mul, Nat.exists_mul_mod_eq_one_of_coprime]
  E1: auto
families: []
requires: [V02.C01]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V02/C02/Examples.lean
  - MathlibHandbook/V02/C02/Exercises.lean
  - MathlibHandbook/V02/C02/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Divisibility, the gcd and Bézout's identity

### Overview

This section proves three facts about $\mathbb{N}$: the division algorithm $a = bq + r$ with $r < b$; Euclid's algorithm, which computes the gcd by repeated division; and Bézout's identity, which writes the gcd of $a$ and $b$ as $ax + by$ with integers $x, y$. Their main consequence is Gauss's lemma: if $k$ divides $mn$ and has no common factor with $n$, then $k$ divides $m$.

In Lean, the division, the remainder, `Nat.gcd` and `Nat.lcm` are in the core of the language, and Mathlib adds the coefficients of Bézout.

### Definitions

**Definition (Divisibility).** For $a, b \in \mathbb{N}$, $a$ divides $b$, written $a \mid b$, if there is $c \in \mathbb{N}$ with $b = ac$.

The relation is reflexive, transitive and, on $\mathbb{N}$, antisymmetric. Each number divides $0$, and $0$ divides only $0$. If $a \mid b$ and $a \mid c$, then $a \mid bx + cy$; if $a \mid b$ and $b \neq 0$, then $a \leq b$. Lean writes `a ∣ b` with the symbol `\mid`, and the definition is the same in each monoid.

**Definition (Quotient and remainder).** For $a, b \in \mathbb{N}$ with $b > 0$, the quotient $a / b$ and the remainder $a \bmod b$ are the numbers $q$ and $r$ of the division algorithm below. Lean also defines them for $b = 0$, with the junk values $a / 0 = 0$ and $a \bmod 0 = a$.

The junk values keep the identity $b \cdot (a / b) + a \bmod b = a$ (the core lemma `Nat.div_add_mod`) true for $b = 0$. The bound $a \bmod b < b$ needs $b > 0$, as in the core lemma `Nat.mod_lt`.

**Definition (Greatest common divisor).** For $a, b \in \mathbb{N}$, a number $d$ is a greatest common divisor of $a$ and $b$ if $d \mid a$, $d \mid b$, and each common divisor of $a$ and $b$ divides $d$.

The order here is divisibility, for which $0$ is the greatest element, so $\gcd(0, 0) = 0$ is not a junk value. A greatest common divisor is unique, because two of them divide each other.

**Definition (Coprime, lcm).** The numbers $a$ and $b$ are coprime if $\gcd(a, b) = 1$. The least common multiple is $\operatorname{lcm}(a, b) = ab / \gcd(a, b)$, with $\operatorname{lcm}(0, 0) = 0$.

::: mathlib
`Nat.gcd_greatest` · `Mathlib.Data.Nat.GCD.Basic`

The core of Lean defines `Nat.gcd` by Euclid's algorithm, below, and proves the three parts of the definition as `Nat.gcd_dvd_left`, `Nat.gcd_dvd_right` and `Nat.dvd_gcd`. This lemma is the converse: a number with the three properties is the gcd. Coprimality is `Nat.Coprime a b`, which unfolds to `Nat.gcd a b = 1`.

<?decl Nat.gcd_greatest?>
:::

### Theorems and proofs

**Theorem (Division algorithm).** Let $a, b \in \mathbb{N}$ with $b > 0$. There are unique $q, r \in \mathbb{N}$ with $a = bq + r$ and $r < b$.

*Proof.* Existence. The set $S = \{a - bq : q \in \mathbb{N}, bq \leq a\}$ contains $a$ (with $q = 0$), so it has a least element $r = a - bq$ by the well ordering principle. Then $a = bq + r$. If $r \geq b$, then $b(q + 1) = bq + b \leq bq + r = a$, so $r - b = a - b(q + 1)$ is in $S$ and is less than $r$, because $b > 0$. This contradicts the choice of $r$. So $r < b$.

Uniqueness. Suppose $bq + r = bq' + r'$ with $r, r' < b$, and suppose $q < q'$. Then $q' = q + 1 + j$ for some $j$, so $bq + r = bq + b + bj + r'$, and cancellation gives $r = b + bj + r' \geq b$. This contradicts $r < b$. In the same way $q' < q$ is false. So $q = q'$, and cancellation gives $r = r'$. $\square$

**Theorem (Euclid's step).** For $a, b \in \mathbb{N}$ with $b > 0$, the common divisors of $a$ and $b$ are the common divisors of $b$ and $a \bmod b$.

*Proof.* Write $a = bq + r$ with $r = a \bmod b$. If $d \mid a$ and $d \mid b$, then $d$ divides $a - bq = r$. If $d \mid b$ and $d \mid r$, then $d$ divides $bq + r = a$. $\square$

**Theorem (Existence of the gcd).** For all $a, b \in \mathbb{N}$, a greatest common divisor of $a$ and $b$ exists, and Euclid's algorithm computes it: $\gcd(0, b) = b$, and $\gcd(a, b) = \gcd(b \bmod a, a)$ for $a > 0$.

*Proof.* Strong induction on $a$. For $a = 0$, the number $b$ divides $0$ and $b$, and each common divisor of $0$ and $b$ divides $b$. So $b$ is a greatest common divisor. For $a > 0$, let $r = b \bmod a$. Then $r < a$, so the hypothesis gives a greatest common divisor $d$ of $r$ and $a$. By Euclid's step, the pairs $(a, b)$ and $(r, a)$ have the same common divisors. So $d$ divides $a$ and $b$, and each common divisor of $a$ and $b$ divides $d$. $\square$

The induction is also the proof that the algorithm stops: the first argument decreases at each step.

**Theorem (Bézout's identity).** For all $a, b \in \mathbb{Z}$ there are $x, y \in \mathbb{Z}$ with $\gcd(a, b) = ax + by$. If $a \neq 0$ or $b \neq 0$, then $\gcd(a, b)$ is the least positive number of the form $ax + by$.

*Proof.* If $a = b = 0$, take $x = y = 0$. Otherwise the set $S = \{ax + by : x, y \in \mathbb{Z}\} \cap \mathbb{N}_{>0}$ is not empty, because it contains $a^2 + b^2 > 0$. Let $d = ax_0 + by_0$ be its least element. Divide $a$ by $d$: $a = dq + r$ with $0 \leq r < d$. Then $r = a - dq = a(1 - qx_0) + b(-qy_0)$ is a combination of $a$ and $b$. If $r > 0$, then $r \in S$ and $r < d$, which contradicts the choice of $d$. So $r = 0$ and $d \mid a$. In the same way $d \mid b$. Each common divisor of $a$ and $b$ divides $ax_0 + by_0 = d$. So $d$ is the greatest common divisor, and it is a combination. $\square$

The extended Euclidean algorithm computes the coefficients: if $\gcd(r, a) = rx' + ay'$ with $r = b - a \lfloor b / a \rfloor$, then
$$\gcd(a, b) = (b - a \lfloor b / a \rfloor) x' + a y' = a (y' - \lfloor b / a \rfloor x') + b x'.$$
For $a = 0$, $\gcd(0, b) = 0 \cdot 0 + b \cdot 1$.

::: mathlib
`Nat.gcd_eq_gcd_ab` · `Mathlib.Data.Int.GCD`

The coefficients are `Nat.gcdA a b` and `Nat.gcdB a b`, two integers. They come from the extended Euclidean algorithm `Nat.xgcd`, and `Nat.xgcd_val` says that `Nat.xgcd a b` is the pair of the two. The identity is in `ℤ`. The form for two integers is `Int.gcd_eq_gcd_ab`, and `Int.gcd_dvd_iff` says that the numbers of the form $ax + by$ are exactly the multiples of the gcd.

<?decl Nat.gcd_eq_gcd_ab?>
:::

::: mathlib
`Int.gcd_least_linear` · `Mathlib.Data.Int.GCD`

This is the second part of the theorem, in the language of `IsLeast`: for `a ≠ 0`, the gcd is the least element of the set of positive combinations, a set of natural numbers.

<?decl Int.gcd_least_linear?>
:::

**Theorem (Gauss's lemma).** Let $k, m, n \in \mathbb{N}$. If $k \mid mn$ and $\gcd(k, n) = 1$, then $k \mid m$.

*Proof.* Bézout gives $x, y \in \mathbb{Z}$ with $kx + ny = 1$. Multiply by $m$: $m = kmx + mny$. The number $k$ divides $kmx$, and it divides $mn$, so it divides $mny$. So $k$ divides the sum $m$. $\square$

::: mathlib
`Nat.Coprime.dvd_mul_right` · `Mathlib.Data.Nat.GCD.Basic`

The statement is an equivalence: if `Nat.Coprime k n`, then `k ∣ m * n ↔ k ∣ m`. The form `Nat.Coprime.dvd_mul_left` has the coprime factor on the left of the product.

<?decl Nat.Coprime.dvd_mul_right?>
:::

**Theorem (gcd and lcm).** For all $a, b \in \mathbb{N}$, $\gcd(a, b) \cdot \operatorname{lcm}(a, b) = ab$. The number $\operatorname{lcm}(a, b)$ is a common multiple of $a$ and $b$, and it divides each common multiple. If $a$ and $b$ are coprime, then $\operatorname{lcm}(a, b) = ab$.

*Proof.* If $a = 0$ or $b = 0$, all values are $0$, and $0$ is the only common multiple. Otherwise let $d = \gcd(a, b) > 0$, $a = da'$ and $b = db'$. Then $\operatorname{lcm}(a, b) = da'b' = ab' = a'b$, a common multiple, and the identity holds. Also $\gcd(a', b') = 1$, since $d \gcd(a', b')$ is a common divisor of $a$ and $b$, so it divides $d$. If $a \mid c$ and $b \mid c$, then $c = da'u = db'v$, so $b' \mid a'u$, and Gauss's lemma gives $b' \mid u$. So $da'b' \mid c$. The last claim is the case $d = 1$. $\square$

::: mathlib
`Nat.Coprime.lcm_eq_mul` · `Mathlib.Data.Nat.GCD.Basic`

The identity $\gcd \cdot \operatorname{lcm} = ab$ is the core lemma `Nat.gcd_mul_lcm`, and `Nat.lcm` is defined as `a * b / Nat.gcd a b`. This lemma is the coprime case.

<?decl Nat.Coprime.lcm_eq_mul?>
:::

### Examples

**Example (Euclid's algorithm).** Compute $\gcd(252, 198)$:
$$252 = 1 \cdot 198 + 54, \quad 198 = 3 \cdot 54 + 36, \quad 54 = 1 \cdot 36 + 18, \quad 36 = 2 \cdot 18 + 0.$$
The last nonzero remainder is $18$, so $\gcd(252, 198) = 18$. Go back through the steps to find the coefficients:
$$18 = 54 - 36 = 54 - (198 - 3 \cdot 54) = 4 \cdot 54 - 198 = 4 \cdot (252 - 198) - 198 = 4 \cdot 252 - 5 \cdot 198.$$
Check: $4 \cdot 252 = 1008$ and $5 \cdot 198 = 990$. The coefficients are not unique. Since $252 = 14 \cdot 18$ and $198 = 11 \cdot 18$, each pair $(4 + 11t, -5 - 14t)$ with $t \in \mathbb{Z}$ also works. Also $\operatorname{lcm}(252, 198) = 2772$.

<?lean MathlibHandbook/V02/C02/Examples.lean#bezout?>

**Example (Junk values).** In Lean, `7 / 0 = 0`, `7 % 0 = 7` and `Nat.gcd 0 0 = 0`. The identity `0 * (7 / 0) + 7 % 0 = 7` holds. The bound `7 % 0 < 0` is false, and this is why `Nat.mod_lt` asks for `0 < b`.

**Counterexample (Gauss's lemma needs coprimality).** The number $6$ divides $4 \cdot 3 = 12$, but $6 \nmid 4$ and $6 \nmid 3$. Here $\gcd(6, 3) = 3 \neq 1$ and $\gcd(6, 4) = 2 \neq 1$, so the lemma does not apply to either factor.

### The library around it

The core of Lean has the lemmas `Nat.div_add_mod`, `Nat.mod_lt`, `Nat.gcd_comm` and `Nat.gcd_rec`, and Mathlib adds many lemmas on `Nat.Coprime` in `Mathlib.Data.Nat.GCD.Basic`. For integers, `Int.gcd a b` is the gcd of the absolute values, a natural number. The inverse of a unit modulo $k$ is `Nat.exists_mul_mod_eq_one_of_coprime`, and Chapter 3 treats it. The tactics `decide` and `norm_num` compute `Nat.gcd` of literals, and `omega` handles `/` and `%` by a literal.

### Exercises

1. (A) Compute $\gcd(1071, 462)$ with Euclid's algorithm, and write it as $1071x + 462y$. *Hint.* The algorithm takes three divisions.
2. (A) Prove that $\gcd(a, b) = \gcd(a, b - a)$ for $a \leq b$. *Hint.* Compare the common divisors, as in Euclid's step.
3. (B) Prove that $\gcd(ka, kb) = k \gcd(a, b)$. *Hint.* Use Bézout for one divisibility and the definition for the other.
4. (B) Prove that $\gcd(n, n + 1) = 1$ and that $\gcd(2n + 1, 3n + 1) = 1$. *Hint.* Find a combination equal to $1$.
5. (B) Prove that if $a$ and $b$ are coprime, $a \mid c$ and $b \mid c$, then $ab \mid c$. *Hint.* Write $c = au$ and apply Gauss's lemma to $b \mid au$.
6. (B) Show that the equation $ax + by = c$ has a solution in integers if and only if $\gcd(a, b) \mid c$. Find all solutions of $6x + 10y = 14$. *Hint.* The difference of two solutions is a solution of $6x + 10y = 0$.
7. (C) Prove that if Euclid's algorithm on $(a, b)$ with $a > b$ takes $k$ divisions, then $b \geq F_{k+1}$, where $F_n$ are the Fibonacci numbers. *Hint.* Induction on $k$; each quotient is at least $1$.

### Notes and history

The division algorithm and Euclid's algorithm are in Book VII of Euclid's *Elements*, Propositions 1 and 2, as repeated subtraction. Bachet de Méziriac gave the identity for integers in 1624, and Bézout proved the form for polynomials in 1779. Gauss stated his lemma in the *Disquisitiones Arithmeticae* (1801). Lamé (1844) bounded the number of steps of Euclid's algorithm with the argument of Exercise 7.

### Reference

<?reference?>
