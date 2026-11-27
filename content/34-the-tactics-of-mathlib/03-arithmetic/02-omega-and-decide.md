---
title: omega and decide
kind: tactic
modules: []
explains:
  E1: [Nat.decidablePrime, Nat.decidableLoHi]
families: []
requires: [V00]
reads_with: ["LLR"]
lean: [MathlibHandbook/V34/C03/Examples.lean, MathlibHandbook/V34/C03/Solutions.lean]
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## omega and decide

### Overview

The tactic `omega` decides linear arithmetic over `ℤ` and `ℕ`. It knows that the variables are integers, so it proves the goals that `linarith` does not prove for this reason: $2a + 1 \neq 2b$, $n \bmod 4 = 3 \Rightarrow n \bmod 2 = 1$, and the facts about the truncated subtraction of `ℕ`. The tactic `decide` evaluates a proposition with no free variable, such as $17 \mid 221$ or $\forall n < 10,\ n^2 \bmod 3 \neq 2$, by a computation that the kernel checks.

The two tactics are decision procedures. Each one has an exact class of goals, and inside this class it always gives an answer. The section gives the two classes, the theorems that make the procedures correct, and the messages of failure outside the classes.

### What it does

#### The class of omega

**Definition (Linear integer problem).** A linear integer problem is a finite set of facts $t \leq 0$, $t = 0$, $t < 0$, $t \neq 0$ and their combinations by $\wedge$, $\vee$, $\neg$ and $\to$, where each $t$ is a linear expression $a_1 x_1 + \cdots + a_n x_n + b$ with integer coefficients, and the variables range over $\mathbb{Z}$. A variable of `ℕ` is a variable of $\mathbb{Z}$ with the fact $0 \leq x$.

The tactic accepts the operations $+$, $-$ and the multiplication by a numeral, and also $x / k$ and $x \bmod k$ for a numeral $k$, the truncated subtraction of `ℕ`, the casts from `ℕ` to `ℤ`, and `min`, `max` and `|·|` in some forms. It replaces each of these by new variables with linear facts. A product $xy$ of two variables is an atom: `omega` treats it as a new variable with no fact.

The method has two parts. First it removes the operations that are not linear, with the next two theorems. Then it decides the linear problem by the omega test of Pugh: it eliminates the equations exactly, and it eliminates the variables of the inequalities by a variant of Fourier and Motzkin (previous section) that respects integrality.

**Theorem (Division with remainder).** Let $n \in \mathbb{Z}$ and let $k$ be a positive integer. Then $q = n / k$ and $r = n \bmod k$ are the unique integers with $n = kq + r$ and $0 \leq r < k$.

*Proof.* Existence. Let $q$ be the largest integer with $kq \leq n$. It exists, since $k(-|n|) \leq n$ and $kq \leq n$ is false for $q > |n|$. Let $r = n - kq$. Then $r \geq 0$ by the choice of $q$, and $r < k$, since otherwise $k(q + 1) \leq n$. Uniqueness. If $n = kq + r = kq' + r'$ with $0 \leq r, r' < k$, then $k(q - q') = r' - r$, and $|r' - r| < k$. A multiple of $k$ with absolute value less than $k$ is $0$. So $q = q'$ and $r = r'$. $\square$

So `omega` replaces the term $n \bmod 4$ by a new variable $r$, the term $n / 4$ by a new variable $q$, and it adds the facts $n = 4q + r$, $0 \leq r$ and $r < 4$. For the truncated subtraction $a - b$ of `ℕ`, it adds a new variable $t$ and the fact $(b \leq a \wedge t = a - b) \vee (a < b \wedge t = 0)$, with an integer subtraction inside. This gives a case split.

**Theorem (Tightening).** Let $a_1, \ldots, a_n, b$ be integers, not all $a_i$ equal to $0$, and let $g = \gcd(a_1, \ldots, a_n)$. For integers $x_i$, the fact $\sum a_i x_i \leq b$ is equivalent to $\sum (a_i / g) x_i \leq \lfloor b / g \rfloor$. The fact $\sum a_i x_i < b$ is equivalent to $\sum a_i x_i \leq b - 1$.

*Proof.* The second claim: the left side and $b$ are integers, and for integers $u < b$ is equivalent to $u \leq b - 1$. The first claim: let $s = \sum (a_i / g) x_i$. It is an integer, and the fact is $g s \leq b$, that is, $s \leq b / g$ since $g > 0$. For an integer $s$ and a rational $c$, $s \leq c$ is equivalent to $s \leq \lfloor c \rfloor$, by the definition of the floor as the largest integer not above $c$. $\square$

This theorem is the difference with `linarith`. The fact $2a + 1 = 2b$ is the pair $2a - 2b \leq -1$ and $2b - 2a \leq 1$. The tightening with $g = 2$ makes them $a - b \leq \lfloor -1/2 \rfloor = -1$ and $b - a \leq \lfloor 1/2 \rfloor = 0$. The sum is $0 \leq -1$, a contradiction. Over the rationals there is no tightening, and the point $a = 0$, $b = 1/2$ is a solution.

The omega test then eliminates variables. An equation with a coefficient $\pm 1$ gives a substitution. Other equations are reduced by a step similar to the algorithm of Euclid. For inequalities, the elimination of a variable $y$ from the pair $c\,y \geq \ell$ and $d\,y \leq u$ is exact over the rationals, but over the integers an integer $y$ between $\ell / c$ and $u / d$ can fail to exist. The test handles this gap with the "dark shadow" and a finite search. The implementation in Lean does the exact eliminations, and when an exact step is not possible it uses the dark shadow and the finite case analysis. The result is a decision procedure: for each linear integer problem, `omega` proves the goal or reports a possible counterexample.

#### The class of decide

**Definition (Decidable).** A proposition `p` is decidable when there is an instance `Decidable p`. An instance is a value that is `isTrue h` with a proof `h : p`, or `isFalse h` with a proof `h : ¬ p`. The library gives instances for the equality of natural numbers, for `≤` and `<` on `ℕ` and `ℤ`, for `∣` on `ℕ`, for `∧`, `∨`, `¬`, `→` of decidable propositions, for the quantifiers over a finite type and for the bounded quantifiers `∀ n < k` on `ℕ`.

The tactic `decide` finds the instance for the goal, evaluates it in the kernel, and checks that the value is `isTrue h`. Then `h` is the proof. If the value is `isFalse`, the goal is false and the tactic says so.

**Theorem (Bounded quantifier).** Let $P$ be a predicate on $\mathbb{N}$ such that $P(n)$ is decidable for each $n$. Then $\forall n < k,\ P(n)$ is decidable for each $k$.

*Proof.* By induction on $k$. For $k = 0$, the proposition $\forall n < 0,\ P(n)$ is true, since no $n$ is less than $0$. The instance is `isTrue`. For the step, $\forall n < k + 1,\ P(n)$ is equivalent to $(\forall n < k,\ P(n)) \wedge P(k)$, since $n < k + 1$ means $n < k$ or $n = k$. By the hypothesis of induction, the first part is decidable. The second part is decidable by assumption. A conjunction of two decidable propositions is decidable: if both values are `isTrue`, the pair of the proofs proves the conjunction, and if one value is `isFalse h`, then the negation follows from `h`. $\square$

This proof is a program: to decide $\forall n < 10,\ n^2 \bmod 3 \neq 2$, it decides the ten cases $n = 0, \ldots, 9$ one by one. The cost is the cost of the computation, and the kernel does the computation step by step on the unary form of the natural numbers in the worst case. So `decide` is a tool for small instances.

::: mathlib
`Nat.decidablePrime` · `Mathlib.Data.Nat.Prime.Defs`

The instance of `Decidable (Nat.Prime p)` that the kernel can evaluate. It checks each divisor up to $p$ with a bounded quantifier. It proves `Nat.Prime 97` with `decide`. For `Nat.Prime 1009`, the computation is too long: `decide` fails with the message "maximum recursion depth has been reached", and `norm_num` proves it by the trial division of Chapter 1.

<?decl Nat.decidablePrime?>
:::

::: mathlib
`Nat.decidableLoHi` · `Mathlib.Data.Nat.Init`

The instance of `Decidable (∀ x, lo ≤ x → x < hi → P x)`, for a decidable predicate `P` on `ℕ`. It is the theorem of the bounded quantifier above, with a lower bound too. With it, `decide` proves a statement about each number of a range.

<?decl Nat.decidableLoHi?>
:::

### How to use it

Write `omega` on a goal over `ℕ` or `ℤ` that is linear after the removal of `/` and `%` by numerals. The tactic uses the hypotheses of the context of these types, and it does not need a list of terms. It does not use a hypothesis with a quantifier, and it does not use the facts about a function: `f n` is an atom. If a needed fact is a lemma, state it with `have` first.

Write `decide` on a closed goal: a goal with no free variable and no hypothesis, about numerals of `ℕ`, `ℤ`, `Fin n` or `ZMod n`, about lists with a fixed length, or about a finite type. For a large numeral, `norm_num` is better: it uses the binary form of the numerals and a proof for each step, while `decide` evaluates. The variant `decide +kernel` skips the evaluation in the elaborator and gives the work to the kernel only. It is faster on some goals.

### What it cannot do

#### omega and a product

The tactic `omega` treats a product of two variables as an atom. On `x * y = 6 → x ≤ 6` over `ℕ`, it fails, because it does not know that $y \geq 1$ follows from $xy = 6$. The message shows a possible counterexample:

```text
omega could not prove the goal:
a possible counterexample may satisfy the constraints
  a ≥ 7
where
 a := ↑x
```

The counterexample is a point of the linear problem where the atom `x * y` is free, so the fact `x * y = 6` gives no constraint on `x`. Here it is not a real counterexample. To fix it, give the fact $0 < y$ with `have : 0 < y := by rcases Nat.eq_zero_or_pos y with h' | h' <;> simp_all` and then call `nlinarith`, or write the term `Nat.le_of_dvd (by norm_num) (Dvd.intro y h)`.

On `x * y = 2 * y` with `h : x = 2`, it fails too: `x * y` is an atom with no relation to `x`. A `subst` first solves it. On $n^2 \bmod 4 \neq 2$ over `ℤ`, it fails with the message "No usable constraints found": the atom `n ^ 2` is free, and no linear fact is left. The fix is a case split on $n \bmod 4$ or on the parity of $n$, then `ring_nf` and `omega` on each case.

#### omega and a power

A power with a variable exponent is an atom. On $2^n \geq n$ the tactic fails. This is a goal for induction (Chapter 5).

#### omega and the truncated subtraction

On `a - b + b = a` over `ℕ` with no hypothesis, `omega` fails with the counterexample $b - a \geq 1$, where $a - b = 0$. This is a real counterexample: $(2 - 5) + 5 = 5$ in `ℕ`. The fix is to add the hypothesis `b ≤ a`.

#### decide and a free variable

The tactic `decide` needs a closed goal. On `n + 0 = n` with a variable `n`, it fails with "Expected type must not contain free variables". On `∀ n : ℕ, n + 0 = n` it fails because no instance exists: the message is "failed to synthesize Decidable (∀ n : ℕ, n + 0 = n)". A quantifier over all of `ℕ` is not decidable by evaluation. Use `simp` or `omega`.

#### decide and the real numbers

The order of `ℝ` is decidable only by the axiom of choice, and the kernel cannot evaluate a choice. On `(2 : ℝ) < 3`, `decide` fails with the message "Tactic `decide` failed to reduce `@decide (2 < 3) (Real.decidableLT 2 3)` to `true` or `false`", and the message says that the reduction got stuck at `Classical.choice`. Use `norm_num`.

### Examples

**Example (Three goals for omega).** A number with the remainder $3$ by $4$ is odd: the tactic introduces $n = 4q + 3$, and then $n \bmod 2 = 1$ follows from the division theorem with $n = 2(2q + 1) + 1$. The fact $2a + 1 = 2b$ is contradictory by tightening. The equation $a - b + b = a$ holds in `ℕ` when $b \leq a$.

<?lean MathlibHandbook/V34/C03/Examples.lean#omega?>

**Example (A system).** Over `ℤ`, from $3x - 2y = 1$, $x + y < 2$ and $0 \leq y$, it follows that $x = 1$. By hand: $x + y \leq 1$ by tightening, so $3x - 2y \leq 3 - 3y - 2y$ gives $1 \leq 3 - 5y$, and $y \leq 2/5$, so $y = 0$. Then $3x = 1$ has no integer solution, so the facts are contradictory, and each goal follows from them, $x = 1$ too. The tactic `omega` finds this with no hint.

```lean
example (x y : ℤ) (h1 : 3 * x - 2 * y = 1) (h2 : x + y < 2) (h3 : 0 ≤ y) : x = 1 := by
  omega
```

**Example (Division).** For $n \in \mathbb{N}$, $n / 2 + n / 2 \leq n$. The tactic adds $n = 2q + r$ with $0 \leq r < 2$, and the goal is $2q \leq 2q + r$.

```lean
example (n : ℕ) : n / 2 + n / 2 ≤ n := by
  omega
```

**Example (Two goals for decide).** The divisibility $17 \mid 221$ is a computation of $221 \bmod 17 = 0$. The statement about the squares is ten computations, by the theorem of the bounded quantifier.

<?lean MathlibHandbook/V34/C03/Examples.lean#decide?>

**Example (A finite type).** In $\mathbb{Z}/2$, each element is equal to its square. There are two elements, and `decide` checks both. The commutativity of the addition in `Fin 5` is $25$ checks.

```lean
example : ∀ x : ZMod 2, x ^ 2 = x := by decide

example : ∀ a b : Fin 5, a + b = b + a := by decide
```

### Exercises

1. (L) Prove `n % 3 = 2` from `n % 6 = 5` (`mod_three_of_mod_six` in `Exercises.lean`).
2. (L) Prove `13 ∣ 1001` with `decide` (`thirteen_dvd` in `Exercises.lean`).
3. (A) Give the facts that `omega` adds for the term `n % 6` and for the term `n / 6`. Use them to prove Exercise 1 by hand.
4. (A) Tell why `linarith` fails and `omega` succeeds on `2 * a + 1 = 2 * b → False` over `ℤ`. Give the point that `linarith` sees.
5. (A) Tell why `decide` fails on `(2 : ℝ) < 3`, and give a tactic that proves it.
6. (B) Find a real counterexample to `a - b + b = a` in `ℕ`, and state the hypothesis that makes `omega` succeed.
7. (B) Prove the equivalence $3x \leq 7 \iff x \leq 2$ for $x \in \mathbb{Z}$ with the tightening theorem. Check it with `omega`.
8. (C) Prove `∀ n : ℤ, n ^ 2 % 4 ≠ 2`. The tactic `omega` alone fails. Split on the parity of `n` with `Int.even_or_odd`, write $n = 2k$ or $n = 2k + 1$, and expand.
9. (C) Write the proof by induction of the theorem of the bounded quantifier as a proof of `Decidable (∀ n < k, P n)` in Lean, with a `match` on `k`.

### Reference

<?reference?>
