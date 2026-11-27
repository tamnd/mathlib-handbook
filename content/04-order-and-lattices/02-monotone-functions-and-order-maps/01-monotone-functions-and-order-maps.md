---
title: Monotone functions and order maps
kind: theory
modules:
  - Mathlib.Order.Monotone.Defs
  - Mathlib.Order.Monotone.Basic
explains:
  E3: [Monotone, StrictMono]
  E2: [Antitone, StrictAnti, MonotoneOn, Monotone.comp, StrictMono.injective, StrictMono.lt_iff_lt, StrictMono.le_iff_le, monotone_nat_of_le_succ]
  E1: [StrictMono.monotone, StrictMono.comp, monotone_id, monotone_const, Antitone.comp, Monotone.comp_antitone, AntitoneOn, StrictMonoOn, Monotone.reflect_lt, strictMono_nat_of_lt_succ, antitone_nat_of_succ_le, Monotone.iterate, Monotone.dual, StrictMonoOn.injOn, Monotone.strictMono_of_injective]
families: []
requires: [V04.C01]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V04/C02/Examples.lean
  - MathlibHandbook/V04/C02/Exercises.lean
  - MathlibHandbook/V04/C02/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Monotone functions

### Overview

An order on a set is a structure, and a function between two ordered sets can respect this structure or not. A function $f$ is monotone when $a \le b$ gives $f(a) \le f(b)$. Monotone functions are everywhere in analysis: the exponential, the logarithm, the cube, a distribution function of a random variable, the partial sums of a series with nonnegative terms. They are also the input of the fixed point theorems of Chapter 4 and the two halves of a Galois connection in Chapter 6.

This section defines the four predicates and their forms on a subset. It proves the rules for composition, the fact that a strictly monotone function on a linear order is injective and reflects the order, and the criterion that a sequence is monotone when each term is below the next term.

### Definitions

In this section $\alpha$, $\beta$ and $\gamma$ are preorders. The strict relation $a < b$ means $a \le b$ and not $b \le a$, as in Chapter 1.

**Definition (Monotone and antitone).** A function $f : \alpha \to \beta$ is *monotone* if $a \le b$ implies $f(a) \le f(b)$ for all $a, b \in \alpha$. It is *antitone* if $a \le b$ implies $f(b) \le f(a)$.

Older books say "increasing" or "nondecreasing" for monotone, and "decreasing" or "nonincreasing" for antitone. An antitone function $f : \alpha \to \beta$ is the same as a monotone function from $\alpha$ to the dual order $\beta^{\mathrm{op}}$, in which the order is reversed. This remark lets one prove a theorem for monotone functions and get the theorem for antitone functions for free.

::: mathlib
`Monotone` · `Mathlib.Order.Monotone.Defs`

The definition is `∀ ⦃a b⦄, a ≤ b → f a ≤ f b`. The strict implicit binders `⦃a b⦄` mean that `hf : Monotone f` does not take the points as arguments. It takes a proof `h : a ≤ b`, and Lean reads the points from the type of `h`. So `hf h : f a ≤ f b`. To prove `Monotone f`, start with `intro a b h`.

<?decl Monotone?>
:::

::: mathlib
`Antitone` · `Mathlib.Order.Monotone.Defs`

The definition is `∀ ⦃a b⦄, a ≤ b → f b ≤ f a`. The lemma `Monotone.dual` and its variants move between a monotone function and an antitone function with values in `OrderDual β`.

<?decl Antitone?>
:::

**Definition (Strictly monotone and strictly antitone).** A function $f : \alpha \to \beta$ is *strictly monotone* if $a < b$ implies $f(a) < f(b)$. It is *strictly antitone* if $a < b$ implies $f(b) < f(a)$.

A strictly monotone function need not be monotone when $\alpha$ is only a preorder. Let $\alpha = \{0, 1\}$ with $0 \le 1$ and $1 \le 0$, so that no two elements are strictly comparable. Each function on $\alpha$ is strictly monotone, because the hypothesis $a < b$ never holds. The function $f : \alpha \to \mathbb{N}$ with $f(0) = 1$ and $f(1) = 0$ is not monotone, because $0 \le 1$ and $f(0) > f(1)$. Theorem (Strict gives weak) below needs antisymmetry.

::: mathlib
`StrictMono` · `Mathlib.Order.Monotone.Defs`

The definition is `∀ ⦃a b⦄, a < b → f a < f b`, with the same binders as `Monotone`. The name `StrictAnti` is the strict form of `Antitone`. The lemma `StrictMono.monotone` needs a partial order on the domain, as the example above shows.

<?decl StrictMono?>
:::

**Definition (Monotone on a set).** Let $s \subseteq \alpha$. A function $f : \alpha \to \beta$ is *monotone on* $s$ if $a \le b$ implies $f(a) \le f(b)$ for all $a, b \in s$. The notions antitone on $s$, strictly monotone on $s$ and strictly antitone on $s$ are similar.

The function $x \mapsto x^2$ on $\mathbb{R}$ is not monotone, but it is monotone on $[0, \infty)$ and antitone on $(-\infty, 0]$. Mathlib prefers this form to a statement about the restriction to the subtype $s$, because no coercion appears.

::: mathlib
`MonotoneOn` · `Mathlib.Order.Monotone.Defs`

The definition is `∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a ≤ b → f a ≤ f b`. So `hf ha hb hab` is a proof of `f a ≤ f b`. The variants are `AntitoneOn`, `StrictMonoOn` and `StrictAntiOn`. The lemma `Monotone.monotoneOn` turns a global statement into a statement on any set.

<?decl MonotoneOn?>
:::

### Theorems and proofs

**Theorem (Composition).** Let $f : \alpha \to \beta$ and $g : \beta \to \gamma$.

1. If $f$ and $g$ are monotone, then $g \circ f$ is monotone.
2. If $f$ and $g$ are antitone, then $g \circ f$ is monotone.
3. If $f$ is antitone and $g$ is monotone, or $f$ is monotone and $g$ is antitone, then $g \circ f$ is antitone.
4. If $f$ and $g$ are strictly monotone, then $g \circ f$ is strictly monotone.

*Proof.* Let $a \le b$ in $\alpha$. For part 1, $f(a) \le f(b)$ because $f$ is monotone, and then $g(f(a)) \le g(f(b))$ because $g$ is monotone. For part 2, $f(b) \le f(a)$ because $f$ is antitone, and then $g(f(a)) \le g(f(b))$ because $g$ is antitone and reverses the inequality $f(b) \le f(a)$. For part 3 in the first case, $f(b) \le f(a)$, and $g$ keeps this inequality, so $g(f(b)) \le g(f(a))$. In the second case, $f(a) \le f(b)$, and $g$ reverses it, so $g(f(b)) \le g(f(a))$. For part 4, let $a < b$. Then $f(a) < f(b)$, and then $g(f(a)) < g(f(b))$. $\square$

The rule is the rule of signs: an even number of antitone factors gives a monotone function, and an odd number gives an antitone function.

::: mathlib
`Monotone.comp` · `Mathlib.Order.Monotone.Defs`

The statement is `Monotone g → Monotone f → Monotone (g ∘ f)`, so the outer function comes first, as in `Function.comp`. The other cases have the names `Antitone.comp`, `Monotone.comp_antitone`, `Antitone.comp_monotone` and `StrictMono.comp`. With dot notation, `hg.comp hf` reads in the same order as $g \circ f$.

<?decl Monotone.comp?>
:::

**Theorem (Strict gives weak).** Let $\alpha$ be a partial order. A strictly monotone function $f : \alpha \to \beta$ is monotone.

*Proof.* Let $a \le b$. In a partial order, $a \le b$ gives $a = b$ or $a < b$. Indeed, if $a \ne b$, then $b \le a$ fails, because $b \le a$ and $a \le b$ would give $a = b$ by antisymmetry. So $a \le b$ and not $b \le a$, which is $a < b$. In the case $a = b$, $f(a) = f(b)$, so $f(a) \le f(b)$ by reflexivity. In the case $a < b$, $f(a) < f(b)$, and this gives $f(a) \le f(b)$. $\square$

**Theorem (Strictly monotone maps on a linear order).** Let $\alpha$ be a linear order and let $f : \alpha \to \beta$ be strictly monotone. Then for all $a, b \in \alpha$:

1. $f(a) < f(b)$ if and only if $a < b$;
2. $f(a) \le f(b)$ if and only if $a \le b$;
3. $f$ is injective.

*Proof.* In a linear order, the negation of $a < b$ is $b \le a$ (Chapter 1).

1. The implication from right to left is the hypothesis. For the other implication, let $f(a) < f(b)$ and suppose that $a < b$ fails. Then $b \le a$. A linear order is a partial order, so $f$ is monotone by the theorem above, and $f(b) \le f(a)$. With $f(a) < f(b)$ this gives $f(a) < f(a)$ by mixed transitivity, which contradicts irreflexivity. So $a < b$.
2. If $a \le b$, then $f(a) \le f(b)$ because $f$ is monotone. Conversely, let $f(a) \le f(b)$ and suppose that $a \le b$ fails. Then $b < a$ in the linear order $\alpha$, so $f(b) < f(a)$. By the definition of $<$ in the preorder $\beta$, this means $f(b) \le f(a)$ and not $f(a) \le f(b)$, which contradicts the hypothesis.
3. Let $a \ne b$. By trichotomy in $\alpha$, $a < b$ or $b < a$. In the first case $f(a) < f(b)$, and in the second case $f(b) < f(a)$. If $f(a) = f(b)$, either case gives $f(a) < f(a)$, which contradicts irreflexivity. So $f(a) \ne f(b)$. $\square$

Part 1 says that a strictly monotone function on a linear order *reflects* the strict order. A monotone function also reflects the strict order on a linear order: if $f(a) < f(b)$ and $b \le a$, then $f(b) \le f(a)$, a contradiction. But a monotone function does not reflect $\le$. The floor function has $\lfloor 0.7 \rfloor \le \lfloor 0.2 \rfloor$, and $0.7 \le 0.2$ is false.

::: mathlib
`StrictMono.lt_iff_lt` · `Mathlib.Order.Monotone.Basic`

The lemma needs `LinearOrder α` and `Preorder β`. The form for `≤` is `StrictMono.le_iff_le`. To cancel a strictly monotone function in a goal, use `rw [hf.lt_iff_lt]` turns `f a < f b` into `a < b`. The lemma `Monotone.reflect_lt` is the statement for a monotone function.

<?decl StrictMono.lt_iff_lt?>
:::

::: mathlib
`StrictMono.injective` · `Mathlib.Order.Monotone.Basic`

The lemma needs a linear order on the domain and only a preorder on the codomain, as in the proof above. The lemma `StrictMonoOn.injOn` is the form on a set. The converse `Monotone.strictMono_of_injective` says that an injective monotone function with values in a partial order is strictly monotone. The domain can be any preorder there.

<?decl StrictMono.injective?>
:::

**Theorem (A sequence is monotone if each step goes up).** Let $\beta$ be a preorder and let $a : \mathbb{N} \to \beta$ satisfy $a_n \le a_{n+1}$ for each $n$. Then $a$ is monotone. If $a_n < a_{n+1}$ for each $n$, then $a$ is strictly monotone.

*Proof.* Let $m \le n$. Write $n = m + k$ with $k \in \mathbb{N}$, and prove $a_m \le a_{m+k}$ by induction on $k$. For $k = 0$ the claim is $a_m \le a_m$, which holds by reflexivity. Suppose $a_m \le a_{m+k}$. The hypothesis gives $a_{m+k} \le a_{m+k+1}$, and transitivity gives $a_m \le a_{m+k+1}$. This completes the induction.

For the strict form, let $m < n$, so $n = m + k + 1$ with $k \in \mathbb{N}$. The first part applies, because $a_j < a_{j+1}$ gives $a_j \le a_{j+1}$. So $a_m \le a_{m+k}$. The hypothesis gives $a_{m+k} < a_{m+k+1}$, and mixed transitivity gives $a_m < a_n$. $\square$

::: mathlib
`monotone_nat_of_le_succ` · `Mathlib.Order.Monotone.Basic`

The hypothesis is `∀ n, f n ≤ f (n + 1)`. The strict form is `strictMono_nat_of_lt_succ`, and the forms for antitone sequences are `antitone_nat_of_succ_le` and `strictAnti_nat_of_succ_lt`. The same file has the versions for `ℤ`, where the induction goes in both directions.

<?decl monotone_nat_of_le_succ?>
:::

### Examples

**Example (The cube).** The function $f(x) = x^3$ is strictly monotone on $\mathbb{R}$. Let $x < y$. Then
$$y^3 - x^3 = (y - x)(y^2 + xy + x^2).$$
The second factor is $y^2 + xy + x^2 = (x + \tfrac{y}{2})^2 + \tfrac{3}{4} y^2$. It is $\ge 0$, and it is $0$ only when $y = 0$ and $x + y/2 = 0$, that is $x = y = 0$. This case is excluded, because $x < y$. So the second factor is $> 0$, the first factor is $> 0$, and $y^3 - x^3 > 0$. By the theorem on linear orders, the cube is injective on $\mathbb{R}$, and $x^3 \le y^3$ if and only if $x \le y$. For example, $x^3 \le 8$ if and only if $x \le 2$.

**Example (The floor).** The floor $\lfloor x \rfloor$ is the largest integer $n$ with $n \le x$. It is monotone. Let $x \le y$. The integer $\lfloor x \rfloor$ satisfies $\lfloor x \rfloor \le x \le y$, so it is one of the integers below $y$, and it is at most the largest one, which is $\lfloor y \rfloor$. The floor is not strictly monotone, because $0 < \tfrac12$ and $\lfloor 0 \rfloor = \lfloor \tfrac12 \rfloor = 0$. It is not injective either. In Chapter 6 this proof comes back as a property of a Galois connection.

**Example (The reciprocal).** The function $x \mapsto 1/x$ is strictly antitone on $(0, \infty)$. For $0 < x < y$,
$$\frac{1}{x} - \frac{1}{y} = \frac{y - x}{xy} > 0.$$
It is also strictly antitone on $(-\infty, 0)$, by the same computation, since $xy > 0$ there too. But it is not antitone on $\mathbb{R} \setminus \{0\}$: $-1 < 1$ and $1/(-1) = -1 < 1 = 1/1$. So a function can be antitone on two sets and not on their union.

**Counterexample (Monotone and not strictly monotone).** A constant function $f(n) = c$ on $\mathbb{N}$ is monotone and antitone. It is not strictly monotone, because $0 < 1$ and $f(0) = f(1)$. On a linear order, a function that is both monotone and antitone, with values in a partial order, is constant. Indeed, any two points $a$ and $b$ are comparable, say $a \le b$, and the two properties give $f(a) \le f(b)$ and $f(b) \le f(a)$, so $f(a) = f(b)$.

**Example (A sequence by its steps).** Let $a_n = n^2 - 3n$ on $\mathbb{Z}$. Then $a_{n+1} - a_n = 2n - 2$. This is $\ge 0$ for $n \ge 1$ and $< 0$ for $n = 0$. So the sequence $n \mapsto a_n$ for $n \in \mathbb{N}$ is not monotone ($a_0 = 0 > -2 = a_1$), but the sequence $n \mapsto a_{n+1}$ is monotone by the step criterion. The values are $-2, -2, 0, 4, 10$, so the shifted sequence is monotone and not strictly monotone.

**Example (Monotone maps in Lean).** The proof starts with `intro a b h`, removes the lambda with `dsimp only`, and closes the arithmetic goal with `omega`.

<?lean MathlibHandbook/V04/C02/Examples.lean#monotone?>

**Example (A strictly monotone map).**

<?lean MathlibHandbook/V04/C02/Examples.lean#strictMono?>

**Example (An antitone map).** On `ℕ` the subtraction is truncated: $10 - 12 = 0$. The function is still antitone, and `omega` knows the truncation.

<?lean MathlibHandbook/V04/C02/Examples.lean#antitone?>

**Example (Composition).**

<?lean MathlibHandbook/V04/C02/Examples.lean#comp?>

**Example (Injectivity).**

<?lean MathlibHandbook/V04/C02/Examples.lean#injective?>

### The library around it

The definitions are in `Mathlib.Order.Monotone.Defs`, and the lemmas that need a linear order or the natural numbers are in `Mathlib.Order.Monotone.Basic`. The names follow one pattern. A lemma about a monotone function has the prefix `Monotone.`, and it applies with dot notation to a proof `hf : Monotone f`. The same lemma for the other three predicates has the prefix `Antitone.`, `StrictMono.` or `StrictAnti.`, and the form on a set has the suffix `On`, as in `StrictMonoOn.injOn`. The basic instances are `monotone_id` and `monotone_const`, and `Monotone.iterate` says that each iterate $f^{[n]}$ of a monotone map is monotone.

For example, `Monotone.add` says that the sum of two monotone functions with values in an ordered additive monoid is monotone. To prove that a concrete function is monotone, the usual route is `intro a b h` and then a tactic for the inequality: `omega` on `ℕ` and `ℤ`, `gcongr` for a goal such as `a ^ 3 + 1 ≤ b ^ 3 + 1` that has the same shape on the two sides, and `nlinarith` or `positivity` for the rest.

### Exercises

1. (A) Give a function from $\mathbb{Z}$ to $\mathbb{Z}$ that is antitone and not strictly antitone. *Hint:* use the floor of $-n/2$.
2. (A) Explain why `hf h` has the type `f a ≤ f b` when `hf : Monotone f` and `h : a ≤ b`. *Hint:* look at the binders of the definition.
3. (A) Show that $x \mapsto x^3 - 3x$ is not monotone on $\mathbb{R}$, and find the largest interval around $2$ on which it is strictly monotone. *Hint:* compare the values at $-1$ and $1$, and factor $y^3 - x^3 - 3(y - x)$.
4. (B) Show that the composition of two antitone functions is monotone, and that the composition of three is antitone.
5. (B) Let $f : \mathbb{N} \to \mathbb{N}$ be strictly monotone. Show that $n \le f(n)$ for each $n$. *Hint:* induction on $n$; use $f(n) < f(n+1)$ and that a strict inequality on $\mathbb{N}$ means $f(n) + 1 \le f(n+1)$.
6. (B) Let $f, g : \mathbb{R} \to \mathbb{R}$ be monotone with values $\ge 0$. Show that $fg$ is monotone. Give an example of two monotone functions whose product is not monotone. *Hint:* try $f(x) = g(x) = x$.
7. (B) Let $\alpha$ be a linear order and let $f : \alpha \to \beta$ be monotone and injective, with $\beta$ a partial order. Show that $f$ is strictly monotone.
8. (C) Let $f : \mathbb{R} \to \mathbb{R}$ be monotone. Show that the set of points where $f$ is not continuous is countable. *Hint:* at a point $x$ of discontinuity, the open interval between $\lim_{t \to x^-} f(t)$ and $\lim_{t \to x^+} f(t)$ is nonempty, these intervals are disjoint, and each contains a rational number.
9. (L) Prove that $n \mapsto n + 3$ is monotone on `ℕ`. The solution is `monotone_add_three`.
10. (L) Prove that the composition of two strictly monotone functions is strictly monotone. The solution is `strictMono_comp_example`.
11. (L) Prove that negation is antitone on `ℤ`. The solution is `antitone_neg_example`.

### Notes and history

Monotone functions are as old as analysis. The theorem that a bounded monotone sequence of reals converges is in Bolzano and in Cauchy, and Lebesgue proved in 1904 that a monotone function on an interval is differentiable almost everywhere. Exercise 8 is a theorem of Froda (1929), although the argument is older. The word "monotone" for maps between general ordered sets became common with the lattice theory of Birkhoff, *Lattice Theory* (1940).

In Mathlib the predicates came from the order library of Lean 3 and moved to Lean 4 with the port. In Lean 3 the names `Antitone` and `StrictAnti` replaced older names with the word "decreasing", so that each of the four predicates has a name with one meaning.

### Reference

<?reference?>
