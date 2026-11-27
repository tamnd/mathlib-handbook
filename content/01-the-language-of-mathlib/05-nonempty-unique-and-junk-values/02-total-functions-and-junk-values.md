---
title: Total functions and junk values
kind: theory
modules: []
explains:
  E1: [div_zero, inv_zero, zero_div, div_self, div_mul_cancel₀, mul_div_assoc, tsub_add_cancel_of_le, Real.sqrt, Real.sqrt_eq_zero_of_nonpos, Real.sqrt_sq, Real.sq_sqrt, Real.log, Real.log_zero, Real.log_neg_eq_log, Real.log_mul, Real.exp_log, Finset.sum_empty, List.headI, Nat.cast_sub]
families: []
requires: [V01.C04]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V01/C05/Examples.lean
  - MathlibHandbook/V01/C05/Exercises.lean
  - MathlibHandbook/V01/C05/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Total functions and junk values

### Overview

In a textbook, $a / b$ is defined only when $b \neq 0$, and $\log x$ only when $x > 0$. In Lean every function is total: a function $f : \alpha \to \beta$ gives a value at every element of $\alpha$. Mathlib could use the subtype $\{b : K \mid b \neq 0\}$ as the domain of division, but then every use of $a / b$ would need a proof of $b \neq 0$ inside the term. Mathlib chooses a value at the bad points instead. This value is a *junk value*. So $a / 0 = 0$, $0^{-1} = 0$, $\sqrt{-1} = 0$, $\log 0 = 0$, and $3 - 5 = 0$ in $\mathbb{N}$.

The junk values do not make any theorem false. A theorem about $a / b$ that holds only for $b \neq 0$ has the hypothesis $b \neq 0$, as in the textbook. The difference is that the hypothesis is in the theorem, not in the term. This section states the junk values of the main functions, proves that the convention is consistent, and shows how to read a statement that has no hypothesis.

### Definitions

**Definition (Total function and junk value).** A *total extension* of a partial function $f : D \to \beta$, where $D \subseteq \alpha$, is a function $g : \alpha \to \beta$ with $g(x) = f(x)$ for $x \in D$. The values $g(x)$ for $x \notin D$ are the *junk values* of $g$.

**Definition (Truncated subtraction).** On $\mathbb{N}$, $m - n$ is $m - n$ when $n \leq m$ and $0$ otherwise. In general Mathlib calls this operation `tsub`, and its lemmas have `tsub` in the name.

**Definition (Integer division).** On $\mathbb{Z}$, $a / b$ for $b > 0$ is the greatest integer $q$ with $q b \leq a$, so it rounds down. The remainder `a % b` is then in $[0, b)$. Also $a / 0 = 0$, so `a % 0 = a`.

**Definition (Real square root and logarithm).** `Real.sqrt x` is the nonnegative square root for $x \geq 0$, and $0$ for $x < 0$. `Real.log x` is the natural logarithm for $x > 0$, $\log 0 = 0$, and $\log x = \log(-x)$ for $x < 0$.

::: mathlib
`div_zero` · `Mathlib.Algebra.GroupWithZero.Basic`

The statement is `a / 0 = 0` in every group with zero, so in every field. It follows from `inv_zero : 0⁻¹ = 0`, which is an axiom of the class `GroupWithZero`, and from `a / b = a * b⁻¹`.

<?decl div_zero?>
:::

### Theorems and proofs

**Theorem (The convention is consistent).** Let $K$ be a field. Extend the inverse to $K$ by $0^{-1} = 0$. Then the extended inverse satisfies $(a^{-1})^{-1} = a$ and $(ab)^{-1} = a^{-1} b^{-1}$ for all $a, b \in K$, with no hypothesis.

*Proof.* For $a \neq 0$, $a^{-1} \neq 0$, since $a^{-1} = 0$ gives $1 = a a^{-1} = 0$, which a field excludes. So $(a^{-1})^{-1}$ is the inverse of $a^{-1}$, which is $a$, by uniqueness of inverses. For $a = 0$, $(0^{-1})^{-1} = 0^{-1} = 0$.

For the product, if $a \neq 0$ and $b \neq 0$, then $ab \neq 0$ since a field has no zero divisors, and $(a^{-1} b^{-1})(ab) = 1$ by commutativity, so $(ab)^{-1} = a^{-1} b^{-1}$. If $a = 0$, then both sides are $0$: $(0 \cdot b)^{-1} = 0^{-1} = 0$ and $0^{-1} b^{-1} = 0$. The case $b = 0$ is the same. $\square$

The theorem shows that the choice $0^{-1} = 0$ keeps two laws true without a hypothesis. A different choice, such as $0^{-1} = 1$, would break the first law, because $(0^{-1})^{-1} = 1^{-1} = 1 \neq 0$.

**Theorem (Junk values do not prove false statements).** Let $P(a, b)$ be a statement about real numbers that a textbook proves under the hypothesis $b \neq 0$. Then the Mathlib statement $b \neq 0 \to P(a, b)$ has the same meaning, whatever the value of $a / 0$.

*Proof.* The value of $a / 0$ appears in $P(a, b)$ only for $b = 0$. For $b = 0$ the implication holds because its hypothesis is false. For $b \neq 0$ the term $a / b$ has its textbook value. $\square$

So the junk values change only the statements that have no hypothesis. Some of these are new theorems in Mathlib. For example, `div_zero` and `zero_div` hold for all elements, and `mul_div_assoc` holds with no hypothesis.

**Theorem (Truncated subtraction).** For $m, n \in \mathbb{N}$: $m - n = 0$ if and only if $m \leq n$, and $(m - n) + n = m$ if and only if $n \leq m$.

*Proof.* If $n \leq m$, then $m - n$ is the usual difference $d$ with $d + n = m$, and $d = 0$ only when $m = n$. If $m < n$, then $m - n = 0$ and $0 + n = n \neq m$. Combine the two cases. $\square$

The hypothesis $n \leq m$ in the second law is a frequent source of errors. The lemma `tsub_add_cancel_of_le` states it, and the tactic `omega` proves such statements directly.

**Theorem (Integer division).** Let $a, b \in \mathbb{Z}$ with $b > 0$. Then $a = b \cdot (a / b) + a \% b$ and $0 \leq a \% b < b$.

*Proof.* Let $q$ be the greatest integer with $qb \leq a$. It exists because the set $\{q : qb \leq a\}$ is nonempty (it contains $-|a|$) and bounded above (by $|a|$). Let $r = a - qb$. Then $r \geq 0$. Also $(q + 1) b > a$ by maximality, so $r < b$. $\square$

### Examples

**Example (Division and inverse by zero).** In $\mathbb{R}$, $x / 0 = 0$ and $0^{-1} = 0$, by `div_zero` and `inv_zero`.

<?lean MathlibHandbook/V01/C05/Examples.lean#div_zero?>

**Example (Truncated subtraction).** In $\mathbb{N}$, $3 - 5 = 0$, by computation.

<?lean MathlibHandbook/V01/C05/Examples.lean#nat_sub?>

**Example (Rounding down).** In $\mathbb{Z}$, $7 / 2 = 3$ and $-7 / 2 = -4$, since $-4 \cdot 2 = -8 \leq -7 < -6$. Languages such as C round to zero and give $-3$.

<?lean MathlibHandbook/V01/C05/Examples.lean#int_div?>

**Example (Square root and logarithm).** $\sqrt{-1} = 0$ and $\log 0 = 0$, and $\log(-x) = \log x$. The last choice makes $\log |x|$ and $\log x$ equal, and the derivative of $\log$ is $1/x$ at every $x \neq 0$.

<?lean MathlibHandbook/V01/C05/Examples.lean#sqrt_log?>

**Counterexample (A law that needs a hypothesis).** The law $(a / b) \cdot b = a$ fails for $b = 0$ and $a \neq 0$: $(1 / 0) \cdot 0 = 0 \neq 1$. So the lemma `div_mul_cancel₀` has the hypothesis $b \neq 0$. In the same way, $\sqrt{x}^2 = x$ fails at $x = -1$, and `Real.sq_sqrt` has the hypothesis $0 \leq x$.

### The library around it

The lemmas `div_zero`, `zero_div`, `inv_zero` and `div_self` are in `Mathlib.Algebra.GroupWithZero.Basic` and nearby modules. The lemmas `Real.sqrt_eq_zero_of_nonpos`, `Real.sqrt_sq` and `Real.sq_sqrt` are in `Mathlib.Analysis.Real.Sqrt`, and `Real.log_zero`, `Real.log_neg_eq_log`, `Real.log_mul` and `Real.exp_log` are in `Mathlib.Analysis.SpecialFunctions.Log.Basic`. Other junk values: the degree of the zero polynomial is $\bot$, the sum over the empty finset is $0$ (`Finset.sum_empty`), and `List.headI` of the empty list is `default`, which needs `[Inhabited α]`.

The rule for a reader: a hypothesis such as $b \neq 0$, $0 \leq x$ or $n \leq m$ in a lemma shows the place where the junk value matters. A lemma with no such hypothesis holds also at the junk value.

#### Common errors

1. A learner proves $(a / b) \cdot b = a$ with `div_mul_cancel₀` and forgets the goal $b \neq 0$ that it produces.
2. A learner writes `n - 1` for a natural number $n$ and assumes $(n - 1) + 1 = n$. This fails for $n = 0$.
3. A learner expects `(-7 : ℤ) / 2 = -3`, as in C. Mathlib rounds down for a positive divisor.

### Exercises

1. (A) Compute in Mathlib: $5 / 0$ in $\mathbb{Q}$, $2 - 7$ in $\mathbb{N}$, $-9 / 4$ and $-9 \% 4$ in $\mathbb{Z}$, $\sqrt{-4}$ and $\log(-e)$ in $\mathbb{R}$.
2. (A) Prove that $(a / b) \cdot b = a$ in a field, for $b \neq 0$, and show by an example that the hypothesis is needed.
3. (B) Prove that $(m - n) - k = m - (n + k)$ in $\mathbb{N}$, with no hypothesis.
4. (B) Prove that $\log(xy) = \log x + \log y$ fails for $x = 0$, $y = 2$, and find the hypotheses of `Real.log_mul`.
5. (C) Show that the only extension of the inverse of a field to $0$ that keeps $(a^{-1})^{-1} = a$ is $0^{-1} = 0$.
6. (L) Prove that $2 - 7 = 0$ in $\mathbb{N}$. The solution is `nat_sub_example` in `Solutions.lean`.
7. (L) Prove that $q / 0 = 0$ for $q \in \mathbb{Q}$. The solution is `rat_div_zero_example` in `Solutions.lean`.

### Notes and history

The convention $x / 0 = 0$ is older than Lean. It is used in the proof assistant Isabelle/HOL and in other systems of the HOL family. The convention for $\log$ of a negative number was chosen in Mathlib to make $\log$ an even function, so that more lemmas hold without a hypothesis. Kevin Buzzard explained the method for mathematicians in the blog post "Division by zero in type theory: a FAQ" (2020).

### Reference

<?reference?>
