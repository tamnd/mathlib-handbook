---
title: Successor, addition and multiplication
kind: theory
modules:
  - Mathlib.SetTheory.Ordinal.Arithmetic
explains:
  E3: [Ordinal.monoid, Ordinal.limitRecOn, Ordinal.sub, Ordinal.div, Ordinal.one_add_omega0]
  E2: [Ordinal.type_prod_lex, Ordinal.mul_succ, Ordinal.leftDistribClass, Ordinal.instIsLeftCancelAdd, Ordinal.zero_or_succ_or_isSuccLimit, Ordinal.limitRecOn_zero, Ordinal.limitRecOn_add_one, Ordinal.limitRecOn_limit, Ordinal.isNormal_add_right, Ordinal.isNormal_mul_right, Ordinal.add_le_iff_of_isSuccLimit, Ordinal.mul_le_iff_of_isSuccLimit, Ordinal.add_sub_cancel_of_le, Ordinal.sub_eq_zero_iff_le, Ordinal.mod, Ordinal.div_add_mod, Ordinal.mod_lt, Ordinal.div_zero, Ordinal.mod_zero, Ordinal.natCast_add_omega0, Ordinal.mul_two, Ordinal.isSuccLimit_omega0]
  E1: auto
families: []
requires: [V04.C01, V04.C02, V31.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Successor, addition and multiplication

### Overview

Chapter 2 built the ordinals as the order types of well-orders. This section gives them an arithmetic. The sum $\alpha + \beta$ is the type of a copy of $\alpha$ followed by a copy of $\beta$, and the product $\alpha \cdot \beta$ is the type of $\beta$ copies of $\alpha$. Both operations extend the arithmetic of $\mathbb{N}$ and obey recursive equations at successors and limits. Associativity, left distributivity and left cancellation hold. Commutativity, right cancellation and right distributivity fail: $1 + \omega = \omega < \omega + 1$. Subtraction on the left and division with remainder hold in full.

### Definitions

**Definition (Successor and limit ordinals).** The *successor* of $\alpha$ is $\alpha + 1$, the least ordinal greater than $\alpha$. An ordinal $\lambda$ is a *limit ordinal* if $\lambda \neq 0$ and $\lambda \neq \beta + 1$ for all $\beta$.

Each ordinal is $0$, a successor or a limit, and exactly one of the three. A limit $\lambda$ satisfies $\beta + 1 < \lambda$ for all $\beta < \lambda$, so $\lambda = \sup_{\beta < \lambda} \beta$. The least limit is $\omega$, the type of $\mathbb{N}$.

::: mathlib
`Order.IsSuccLimit` · `Mathlib.Order.SuccPred.Limit`

Mathlib states the notion for any order with a successor `Order.succ`. `IsSuccPrelimit a` says that `a` covers no element, and `IsSuccLimit a` adds that `a` is not minimal. So `0` is a prelimit but not a limit. For ordinals, `Order.succ o = o + 1`. `Ordinal.zero_or_succ_or_isSuccLimit` gives the three cases, and `Ordinal.isSuccLimit_omega0` says that $\omega$ is a limit.

<?decl Order.IsSuccLimit?>
:::

::: mathlib
`Ordinal.limitRecOn` · `Mathlib.SetTheory.Ordinal.Arithmetic`

Transfinite recursion in three cases: a value at `0`, a step from `o` to `o + 1`, and a value at a limit `o` from the values below `o`. The `simp` lemmas `limitRecOn_zero`, `limitRecOn_add_one` and `limitRecOn_limit` give the equations. Section 2 uses it to define the exponential.

<?decl Ordinal.limitRecOn?>
:::

Let $(A, <_A)$ and $(B, <_B)$ be well-orders of types $\alpha$ and $\beta$.

**Definition (Ordinal sum).** The *ordinal sum* $A \oplus B$ is the disjoint union, ordered by $<_A$ on $A$, by $<_B$ on $B$, and with each element of $A$ below each element of $B$. Set $\alpha + \beta = \operatorname{type}(A \oplus B)$.

**Definition (Ordinal product).** The *lexicographic product* $B \times_{\mathrm{lex}} A$ is $B \times A$ with $(b, a) < (b', a')$ if $b <_B b'$, or $b = b'$ and $a <_A a'$. Set $\alpha \cdot \beta = \operatorname{type}(B \times_{\mathrm{lex}} A)$.

Both orders are well-orders. For a nonempty $S \subseteq B \times A$, the least first coordinate $b$ in $S$ and then the least $a$ with $(b, a) \in S$ give the least element. Isomorphic factors give isomorphic results, so the operations are well defined. In the product, $B$ is the major coordinate, as in Cantor, Jech and Kunen.

::: mathlib
`Ordinal.add` · `Mathlib.SetTheory.Ordinal.Basic`

Addition is defined in the basic file, by the order `Sum.Lex r s`. The `simp` lemma `Ordinal.type_sum_lex` states the definition. The instance `Ordinal.addMonoidWithOne` gives `0`, `1`, the casts from `ℕ` and associativity.

<?decl Ordinal.type_sum_lex?>
:::

::: mathlib
`Ordinal.monoid` · `Mathlib.SetTheory.Ordinal.Arithmetic`

The product `type r * type s` is the type of `Prod.Lex s r` on `β × α`; this is the lemma `type_prod_lex`. So the right factor is the major coordinate, as in the text. The instance gives associativity and the unit; `monoidWithZero`, `leftDistribClass` and `noZeroDivisors` add the laws of `0` and the left distributive law.

<?decl Ordinal.type_prod_lex?>
:::

### Theorems and proofs

**Proposition (Algebraic laws).** For all ordinals $\alpha, \beta, \gamma$:

1. $(\alpha + \beta) + \gamma = \alpha + (\beta + \gamma)$ and $(\alpha \beta) \gamma = \alpha (\beta \gamma)$;
2. $\alpha + 0 = 0 + \alpha = \alpha$, $\alpha \cdot 1 = 1 \cdot \alpha = \alpha$ and $\alpha \cdot 0 = 0 \cdot \alpha = 0$;
3. $\alpha (\beta + \gamma) = \alpha \beta + \alpha \gamma$.

*Proof.* Take $A, B, C$ of types $\alpha, \beta, \gamma$. For 1, both $(A \oplus B) \oplus C$ and $A \oplus (B \oplus C)$ put $A$ first, then $B$, then $C$, so the identity of $A \sqcup B \sqcup C$ is an isomorphism. The map $((c, b), a) \mapsto (c, (b, a))$ is an isomorphism $(C \times_{\mathrm{lex}} B) \times_{\mathrm{lex}} A \cong C \times_{\mathrm{lex}} (B \times_{\mathrm{lex}} A)$, since both orders compare $c$ first, then $b$, then $a$. For 2, a sum with an empty summand is the other summand, a product with a one-point factor is the other factor, and a product with an empty factor is empty. For 3, $(B \oplus C) \times_{\mathrm{lex}} A$ consists of the pairs $(b, a)$, followed by the pairs $(c, a)$. This is $(B \times_{\mathrm{lex}} A) \oplus (C \times_{\mathrm{lex}} A)$. $\square$

**Lemma (Monotonicity).** Let $\beta < \gamma$. Then $\alpha + \beta < \alpha + \gamma$ and $\beta + \alpha \le \gamma + \alpha$. If $\alpha > 0$, then $\alpha \beta < \alpha \gamma$.

*Proof.* Take $C$ of type $\gamma$. Since $\beta < \gamma$, there is $c \in C$ with $\beta = \operatorname{type}(C_{<c})$, where $C_{<c} = \{y \in C : y < c\}$ (Chapter 2, Section 1). The initial segment of $A \oplus C$ below $c$ is $A \oplus C_{<c}$, so $\alpha + \beta < \alpha + \gamma$. If $\alpha > 0$, let $a_0$ be the least element of $A$. The initial segment of $C \times_{\mathrm{lex}} A$ below $(c, a_0)$ is $C_{<c} \times_{\mathrm{lex}} A$, so $\alpha \beta < \alpha \gamma$. Last, the inclusion $C_{<c} \to C$ gives an order embedding $C_{<c} \oplus A \to C \oplus A$, and an order embedding of well-orders gives the inequality of the types (Chapter 2, Section 1). $\square$

**Corollary (Left cancellation).** If $\alpha + \beta = \alpha + \gamma$, then $\beta = \gamma$. If $\alpha \beta = \alpha \gamma$ and $\alpha \neq 0$, then $\beta = \gamma$.

*Proof.* The order of the ordinals is linear. If $\beta < \gamma$ or $\gamma < \beta$, the lemma makes the two sides different. $\square$

**Theorem (Recursive equations).** For all $\alpha, \beta$ and each limit ordinal $\lambda$:
$$\alpha + (\beta + 1) = (\alpha + \beta) + 1, \qquad \alpha + \lambda = \sup_{\beta < \lambda} (\alpha + \beta),$$
$$\alpha (\beta + 1) = \alpha \beta + \alpha, \qquad \alpha \lambda = \sup_{\beta < \lambda} \alpha \beta.$$

*Proof.* The successor equations are associativity and the distributive law with $\alpha \cdot 1 = \alpha$.

Let $\sigma = \sup_{\beta < \lambda} (\alpha + \beta)$. The lemma gives $\sigma \le \alpha + \lambda$. For the converse, it is sufficient to show $\gamma < \sigma$ for each $\gamma < \alpha + \lambda$. Take $L$ of type $\lambda$. Then $\gamma = \operatorname{typein}(x)$ for some $x \in A \oplus L$. If $x \in A$, then $\gamma < \alpha \le \sigma$. If $x \in L$, the segment below $x$ is $A \oplus L_{<x}$, so $\gamma = \alpha + \beta$ with $\beta < \lambda$. As $\lambda$ is a limit, $\beta + 1 < \lambda$ and $\gamma < \alpha + (\beta + 1) \le \sigma$.

For the product, the segment of $L \times_{\mathrm{lex}} A$ below $(y, a)$ is the set of pairs $(y', a')$ with $y' < y$, followed by the pairs $(y, a')$ with $a' < a$. Its type is $\alpha \beta + \delta$ with $\beta = \operatorname{typein}(y) < \lambda$ and $\delta < \alpha$. Then $\alpha \beta + \delta < \alpha (\beta + 1) \le \sup_{\xi < \lambda} \alpha \xi$. With the lemma, this gives the limit equation. $\square$

With $\alpha + 0 = \alpha$ and $\alpha \cdot 0 = 0$, the equations determine both operations, and many texts take them as the definition. On $\mathbb{N}$ they are the usual recursions.

**Corollary (Normality in the right argument).** The map $\beta \mapsto \alpha + \beta$ is strictly increasing, and its value at a limit $\lambda$ is the supremum of its values below $\lambda$. For $\alpha > 0$, the same holds for $\beta \mapsto \alpha \beta$.

*Proof.* Combine the lemma with the theorem. $\square$

Such maps are the *normal functions* of Chapter 4.

::: mathlib
`Ordinal.isNormal_add_right` · `Mathlib.SetTheory.Ordinal.Arithmetic`

`isNormal_add_right a : IsNormal (a + ·)` and `isNormal_mul_right (h : 0 < a) : IsNormal (a * ·)`. The predicate `Order.IsNormal` is in `Mathlib.Order.IsNormal`; Chapter 4 explains it. The limit equations are `add_le_iff_of_isSuccLimit` and `mul_le_iff_of_isSuccLimit`, and the successor equation of the product is `mul_succ`.

<?decl Ordinal.isNormal_add_right?>
:::

**Proposition (Subtraction on the left).** If $\beta \le \alpha$, there is a unique $\gamma$ with $\beta + \gamma = \alpha$.

*Proof.* Take $A$ of type $\alpha$ and its initial segment $I$ of type $\beta$ (Chapter 2, Section 1). Each element of $I$ is below each element of $A \setminus I$, so $A = I \oplus (A \setminus I)$ and $\gamma = \operatorname{type}(A \setminus I)$ works. Uniqueness is left cancellation. $\square$

::: mathlib
`Ordinal.sub` · `Mathlib.SetTheory.Ordinal.Arithmetic`

`a - b` is the $\gamma$ of the proposition when `b ≤ a`, and the junk value `0` when `a < b`. So `Ordinal.sub_eq_zero_iff_le : a - b = 0 ↔ a ≤ b`, as in `ℕ`. The main lemma is `add_sub_cancel_of_le (h : b ≤ a) : b + (a - b) = a`. Since $1 + \omega = \omega$, Mathlib computes $\omega - 1 = \omega$.

<?decl Ordinal.sub?>
:::

**Theorem (Division with remainder).** Let $\beta \neq 0$. For each $\alpha$ there is a unique pair $(q, r)$ with $\alpha = \beta q + r$ and $r < \beta$.

*Proof.* Existence. Since $\beta \ge 1$, $\beta (\alpha + 1) \ge \alpha + 1 > \alpha$. Let $\xi_0$ be the least $\xi$ with $\alpha < \beta \xi$. Then $\xi_0 \neq 0$. If $\xi_0$ were a limit, then $\beta \xi \le \alpha$ for all $\xi < \xi_0$, and the limit equation would give $\beta \xi_0 \le \alpha$. So $\xi_0 = q + 1$, and $\beta q \le \alpha < \beta q + \beta$. Take $r$ with $\beta q + r = \alpha$. Then $\beta q + r < \beta q + \beta$, and $r < \beta$ by the lemma.

Uniqueness. Let $\beta q + r = \beta q' + r'$ with $r, r' < \beta$. If $q < q'$, then $\beta q + r < \beta (q + 1) \le \beta q' \le \beta q' + r'$, a contradiction. So $q = q'$ by symmetry, and $r = r'$ by left cancellation. $\square$

::: mathlib
`Ordinal.div` · `Mathlib.SetTheory.Ordinal.Arithmetic`

`a / b` is the quotient and `a % b` (`Ordinal.mod`) is `a - b * (a / b)`. The theorem is `div_add_mod a b : b * (a / b) + a % b = a` with `mod_lt a (h : b ≠ 0) : a % b < b`. The junk values `div_zero : a / 0 = 0` and `mod_zero : a % 0 = a` make `div_add_mod` true with no hypothesis. The divisor is the left factor.

<?decl Ordinal.div?>
:::

### Examples

**Example ($1 + \omega = \omega \neq \omega + 1$).** The limit equation gives $1 + \omega = \sup_n (1 + n) = \omega$: one point put before a copy of $\mathbb{N}$ gives a copy of $\mathbb{N}$. But $\omega + 1$ is a successor and $\omega$ is a limit, so $\omega + 1 \neq \omega$. So addition is not commutative, and $0 + \omega = 1 + \omega$ shows that it does not cancel on the right.

::: mathlib
`Ordinal.one_add_omega0` · `Mathlib.SetTheory.Ordinal.Arithmetic`

`one_add_omega0 : 1 + ω = ω` is a `simp` lemma, with the general forms `natCast_add_omega0 n : n + ω = ω` and `add_omega0 (h : a < ω) : a + ω = ω`. The name `Ordinal.omega0` with notation `ω` keeps the ordinal apart from the aleph function of Chapter 5.

<?decl Ordinal.one_add_omega0?>
:::

**Example ($2 \cdot \omega = \omega \neq \omega \cdot 2$).** The limit equation gives $2 \cdot \omega = \sup_n 2n = \omega$. But $\omega \cdot 2 = \omega + \omega > \omega$, which is `Ordinal.mul_two`. Right distributivity fails: $(1 + 1) \cdot \omega = \omega < \omega + \omega = 1 \cdot \omega + 1 \cdot \omega$.

**Example (A division).** Let $\omega^2 = \omega \omega$. For $n \ge 1$, $(\omega + 1) n = \omega n + 1$ by induction, as $1 + \omega = \omega$. So $(\omega + 1) \omega = \sup_n (\omega n + 1) = \omega^2$, and $\omega^2 + 3 = (\omega + 1) \omega + 3$ with $3 < \omega + 1$: the quotient is $\omega$ and the remainder is $3$.

**Counterexample (Subtraction on the right).** The hypothesis $\beta \le \alpha$ gives a solution of $\beta + x = \alpha$ only. The equation $x + 1 = \omega$ has no solution, since $\omega$ is a limit. The equation $x + \omega = \omega + 1$ has none either, since $x + \omega$ is always a limit. The equation $x + \omega = \omega$ has the solutions $x = 0, 1, 2, \ldots$.

### The library around it

The ordinals have the instances `MonoidWithZero`, `LeftDistribClass`, `NoZeroDivisors` and `IsLeftCancelAdd`, but no `AddCommMonoid` and no `Semiring`. So `ring`, `abel` and `linarith` do not apply, and a computation is a chain of `rw` with `add_assoc`, `mul_add` and the limit lemmas. The lemmas `natCast_mul`, `natCast_sub` and `natCast_mod` move the arithmetic of `ℕ` into the ordinals. `Ordinal.pred` is the predecessor, with `pred o = o` at limits.

Common errors of a learner:

- `a * b` is $b$ copies of `a`, the type of `b ×ₗ a`, and `ω * 2 ≠ 2 * ω`.
- `a - b` and `a / b` act on the left. No lemma solves `x + b = a`, because such an `x` can fail to exist.
- `a - b = 0` when `a < b`, `a / 0 = 0` and `a % 0 = a`. A lemma that needs `b ≤ a` or `b ≠ 0` says so in its hypotheses.
- `IsSuccLimit 0` is false, so `limitRecOn` treats `0` in its own case.

### Exercises

1. (A) Write $\omega + \omega \cdot 2$, $\omega \cdot 2 + \omega$, $(\omega + 1) \cdot 2$ and $2 \cdot (\omega + 1)$ in the form $\omega \cdot m + n$.
2. (A) Show that $\alpha + \beta$ is a limit if and only if $\beta$ is a limit, or $\beta = 0$ and $\alpha$ is a limit.
3. (A) Show that $\alpha < \beta$ implies $\alpha \gamma \le \beta \gamma$. Find $\alpha < \beta$ and $\gamma$ with $\alpha \gamma = \beta \gamma \neq 0$.
4. (B) Show that $\alpha + \beta = \beta$ if and only if $\alpha \cdot \omega \le \beta$. Hint: write $\beta = \alpha \omega + \delta$, and use $\alpha + \alpha \omega = \alpha (1 + \omega)$.
5. (B) Show that each ordinal is $\omega \lambda + n$ for a unique ordinal $\lambda$ and a unique $n < \omega$, and that $n = 0$ if and only if the ordinal is $0$ or a limit.
6. (B) Prove from the definition by order types that $\alpha \beta = 0$ implies $\alpha = 0$ or $\beta = 0$.
7. (C) Find all pairs $\alpha, \beta < \omega^2$ with $\alpha + \beta = \beta + \alpha$. Compare with the theorem on commuting ordinals in Section 2.

### Notes and history

Cantor defined the sum and the product of order types in the *Beiträge zur Begründung der transfiniten Mengenlehre* (1895 and 1897). The recursive equations, with $\alpha \cdot \beta$ as $\beta$ copies of $\alpha$, are the form of Jech, *Set Theory*, Chapter 2, and Kunen, *Set Theory*, Chapter I. Mathlib starts from the order types and proves the equations.

### Reference

<?reference?>
