---
title: Ordered monoids and ordered groups
kind: theory
modules:
  - Mathlib.Algebra.Order.Monoid.Defs
  - Mathlib.Algebra.Order.Group.Defs
explains:
  E3: [IsOrderedAddMonoid, IsOrderedCancelAddMonoid]
  E2: [add_le_add, sub_nonneg, neg_le_neg, IsOrderedAddMonoid.toIsOrderedCancelAddMonoid, PartialOrder.ofAddSubmonoid, add_eq_zero_iff_of_nonneg]
  E1: [IsOrderedMonoid, IsOrderedAddMonoid.add_le_add_left, IsOrderedAddMonoid.add_le_add_right, IsOrderedCancelAddMonoid.le_of_add_le_add_left, add_le_add_left, add_le_add_right, add_pos, add_nonneg, add_lt_add, sub_pos, sub_le_sub, neg_nonneg, le_sub_iff_add_le, sub_le_iff_le_add, PartialOrder.ofAddSubmonoid_le_iff]
families: []
requires: [V04.C01, V01.C04]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V04/C08/Examples.lean
  - MathlibHandbook/V04/C08/Exercises.lean
  - MathlibHandbook/V04/C08/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Ordered monoids and ordered groups

### Overview

The numbers $\mathbb{N}$, $\mathbb{Z}$, $\mathbb{Q}$ and $\mathbb{R}$ have an addition and an order, and from $a \le b$ follows $a + c \le b + c$. Most computations with inequalities use only this link: adding two inequalities, moving a term to the other side and changing signs are steps of an ordered group.

This section defines the ordered monoids and the ordered groups. It proves from the axioms that inequalities add, that a difference is nonnegative exactly when the inequality holds, and that negation reverses the order. It then shows that the order of a group is determined by its *positive cone*.

In Mathlib, an ordered group is not one class but three: one for the algebra, one for the order and one for the link.

### Definitions

**Definition (Ordered additive monoid).** An *ordered additive monoid* is an additive commutative monoid $(M, +, 0)$ with a partial order $\le$ such that for all $a, b, c \in M$, if $a \le b$ then $c + a \le c + b$.

*Remarks.* Since $+$ is commutative, the axiom also gives $a + c \le b + c$. The axiom says that each translation $x \mapsto c + x$ is monotone. It does not say that the translations reflect the order (see the counterexample on $\mathbb{N} \cup \{\infty\}$ below). Mathlib states the definition for a preorder.

**Definition (Ordered cancellative monoid).** An ordered additive monoid is *cancellative* if for all $a, b, c$, from $c + a \le c + b$ follows $a \le b$.

**Definition (Ordered group).** An *ordered additive group* is an additive commutative group $(G, +, 0, -)$ with a partial order such that $(G, +, 0, \le)$ is an ordered additive monoid. It is a *linearly ordered group* if the order is linear.

**Definition (Positive cone).** The *positive cone* of an ordered group $G$ is the set $P = \{x \in G \mid 0 \le x\}$.

The name is the standard one, although $P$ contains $0$. The multiplicative forms of the definitions use $\cdot$, $1$ and $x^{-1}$ in the place of $+$, $0$ and $-x$.

::: mathlib
`IsOrderedAddMonoid` · `Mathlib.Algebra.Order.Monoid.Defs`

The class takes `[AddCommMonoid α] [Preorder α]` as parameters and is a `Prop`, with the fields `add_le_add_left : a ≤ b → ∀ c, a + c ≤ b + c` and `add_le_add_right : a ≤ b → ∀ c, c + a ≤ c + b`. It is a *mixin*: a lemma on an ordered group takes `[AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]`, and a linearly ordered group takes `[LinearOrder α]` in the place of `[PartialOrder α]`. The multiplicative form is `IsOrderedMonoid`.

<?decl IsOrderedAddMonoid?>
:::

::: mathlib
`IsOrderedCancelAddMonoid` · `Mathlib.Algebra.Order.Monoid.Defs`

The class extends `IsOrderedAddMonoid` with the field `le_of_add_le_add_left : a + b ≤ a + c → b ≤ c`. The instances for `ℕ` are `Nat.instIsOrderedAddMonoid` and `Nat.instIsOrderedCancelAddMonoid`. For a group, the instance `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid` gives the cancellative class from the plain one, by the theorem on cancellation below.

<?decl IsOrderedCancelAddMonoid?>
:::

### Theorems and proofs

In this part, $M$ is an ordered additive monoid and $G$ is an ordered additive group.

**Theorem (Addition of inequalities).** In $M$, if $a \le b$ and $c \le d$, then $a + c \le b + d$. In particular, if $0 \le a$ and $0 \le b$, then $0 \le a + b$.

*Proof.* The axiom with the term $c$ added on the right gives $a + c \le b + c$. The axiom with the term $b$ added on the left gives $b + c \le b + d$. Transitivity gives $a + c \le b + d$. For the second claim, take $0 \le a$ and $0 \le b$, so $0 + 0 \le a + b$, and $0 + 0 = 0$. $\square$

**Theorem (Strict inequalities).** Let $M$ be cancellative. If $a < b$, then $c + a < c + b$. If $a < b$ and $c \le d$, then $a + c < b + d$.

*Proof.* From $a < b$ follows $a \le b$, so $c + a \le c + b$. Suppose $c + b \le c + a$. Cancellation gives $b \le a$, and this contradicts $a < b$. So $c + a \le c + b$ and not $c + b \le c + a$, that is, $c + a < c + b$. For the second claim, $a + c < b + c$ by the first claim and commutativity, and $b + c \le b + d$ by the axiom. Mixed transitivity gives $a + c < b + d$. $\square$

**Theorem (Cancellation in a group).** Each ordered group is cancellative: in $G$, $c + a \le c + b$ gives $a \le b$. So $c + a \le c + b$ holds if and only if $a \le b$.

*Proof.* Suppose $c + a \le c + b$. Add $-c$ on the left of both sides. The axiom gives $-c + (c + a) \le -c + (c + b)$. By associativity and $-c + c = 0$, this is $a \le b$. The converse is the axiom. $\square$

The group gives the rules for moving terms and for signs. Recall that $a - b$ means $a + (-b)$.

**Theorem (Differences and negation).** In $G$:

1. $a \le b$ if and only if $0 \le b - a$;
2. $a - c \le b$ if and only if $a \le b + c$;
3. if $a \le b$, then $-b \le -a$;
4. $0 \le -a$ if and only if $a \le 0$;
5. if $a \le b$ and $c \le d$, then $a - d \le b - c$.

*Proof.* Each step uses the theorem on cancellation in the form "$x \le y$ if and only if $x + z \le y + z$".

1. Add $-a$ to both sides of $a \le b$: the inequality is equivalent to $a + (-a) \le b + (-a)$, that is, $0 \le b - a$.

2. Add $c$ to both sides of $a - c \le b$: the inequality is equivalent to $a - c + c \le b + c$, that is, $a \le b + c$.

3. Add $-a + (-b)$ to both sides of $a \le b$. The left side is $a + (-a) + (-b) = -b$ and the right side is $b + (-a) + (-b) = -a$, by commutativity. So $-b \le -a$.

4. By part 1 with the pair $(a, 0)$, $a \le 0$ is equivalent to $0 \le 0 - a = -a$.

5. By part 3, $c \le d$ gives $-d \le -c$. The theorem on addition, applied to $a \le b$ and $-d \le -c$, gives $a + (-d) \le b + (-c)$. $\square$

Part 3 needs no multiplication by $-1$, because a group has no multiplication.

**Theorem (Sums of nonnegative elements).** In $G$, if $0 \le a$, $0 \le b$ and $a + b = 0$, then $a = 0$ and $b = 0$.

*Proof.* From $a + b = 0$ follows $a = -b$. By part 3 of the previous theorem, $0 \le b$ gives $-b \le -0 = 0$, so $a \le 0$. With $0 \le a$, antisymmetry gives $a = 0$. Then $b = -a = 0$. $\square$

The last theorem shows that the whole order of a group is in its positive cone.

**Theorem (Positive cone).** Let $G$ be an ordered group with positive cone $P$.

1. $0 \in P$, $P + P \subseteq P$, and $P \cap (-P) = \{0\}$.
2. For all $a, b$, $a \le b$ if and only if $b - a \in P$.
3. The order is linear if and only if $P \cup (-P) = G$.

Conversely, let $G$ be an additive commutative group and let $P \subseteq G$ satisfy $0 \in P$, $P + P \subseteq P$ and $P \cap (-P) = \{0\}$. Define $a \le b$ if $b - a \in P$. Then $\le$ is a partial order, $G$ with this order is an ordered group, and its positive cone is $P$.

*Proof.* 1. The element $0$ is in $P$ by reflexivity, and $P + P \subseteq P$ is the theorem on addition. Let $x \in P \cap (-P)$. Then $0 \le x$, and $x = -y$ with $0 \le y$, so $x \le 0$ by part 4 of the theorem on differences. Antisymmetry gives $x = 0$.

2. This is part 1 of the theorem on differences.

3. Suppose the order is linear and let $x \in G$. Either $0 \le x$, so $x \in P$, or $x \le 0$, so $-x \in P$ and $x \in -P$. Conversely, suppose $P \cup (-P) = G$, and let $a, b \in G$. If $b - a \in P$, then $a \le b$ by part 2. Otherwise $b - a \in -P$, so $a - b \in P$ and $b \le a$.

For the converse, there are four things to prove.

*Reflexivity.* $a - a = 0 \in P$, so $a \le a$.

*Transitivity.* If $b - a \in P$ and $c - b \in P$, then $c - a = (c - b) + (b - a) \in P + P \subseteq P$, so $a \le c$.

*Antisymmetry.* If $b - a \in P$ and $a - b \in P$, then $b - a \in P$ and $b - a = -(a - b) \in -P$. So $b - a \in P \cap (-P) = \{0\}$, and $a = b$.

*Translation.* If $b - a \in P$, then $(c + b) - (c + a) = b - a \in P$, so $c + a \le c + b$.

Finally, $0 \le x$ means $x - 0 = x \in P$, so the positive cone of the new order is $P$. $\square$

::: mathlib
`add_le_add` · `Mathlib.Algebra.Order.Monoid.Unbundled.Basic`

The lemma asks for `AddLeftMono α` and `AddRightMono α`, the monotonicity of the translations on each side, and not for `IsOrderedAddMonoid`, which gives both. Each lemma of this unbundled layer asks for the weakest property that its proof uses. The one-sided lemmas name the hypothesis, not the side of the new term: for `h : b ≤ d`, `add_le_add_left h c : b + c ≤ d + c` and `add_le_add_right h c : c + b ≤ c + d`. The tactic `gcongr` avoids the question of names.

<?decl add_le_add?>
:::

::: mathlib
`sub_nonneg` · `Mathlib.Algebra.Order.Group.Unbundled.Basic`

This is part 1 of the theorem on differences, as `0 ≤ a - b ↔ b ≤ a`, and a `simp` lemma. The strict form is `sub_pos`, and part 2 is `sub_le_iff_le_add`, with the partner `le_sub_iff_add_le`. On `ℕ`, which is not a group, the subtraction truncates and these lemmas do not apply.

<?decl sub_nonneg?>
:::

::: mathlib
`neg_le_neg` · `Mathlib.Algebra.Order.Group.Defs`

This is part 3 of the theorem on differences. The equivalence is `neg_le_neg_iff : -a ≤ -b ↔ b ≤ a`, and part 4 is `neg_nonneg`. Part 5 is `sub_le_sub`.

<?decl neg_le_neg?>
:::

::: mathlib
`IsOrderedAddMonoid.toIsOrderedCancelAddMonoid` · `Mathlib.Algebra.Order.Group.Defs`

This instance is the theorem on cancellation in a group, so each ordered group has the strict lemmas such as `add_lt_add`.

<?decl IsOrderedAddMonoid.toIsOrderedCancelAddMonoid?>
:::

::: mathlib
`add_eq_zero_iff_of_nonneg` · `Mathlib.Algebra.Order.Monoid.Unbundled.Basic`

The lemma states `0 ≤ a → 0 ≤ b → (a + b = 0 ↔ a = 0 ∧ b = 0)`. It needs no group: its proof uses $a = a + 0 \le a + b = 0$, so it holds in $\mathbb{N}$ too.

<?decl add_eq_zero_iff_of_nonneg?>
:::

::: mathlib
`PartialOrder.ofAddSubmonoid` · `Mathlib.Algebra.Order.Group.Cone`

This is the converse part of the theorem on the positive cone. The cone is an `AddSubmonoid G` with a proof of `M.IsPointed`, which states $P \cap (-P) = \{0\}$. The lemma `PartialOrder.ofAddSubmonoid_le_iff` states `a ≤ b ↔ b - a ∈ M`.

<?decl PartialOrder.ofAddSubmonoid?>
:::

### Examples

**Example (Addition of inequalities).** In $\mathbb{Z}$, from $2 \le 5$ and $-3 \le 1$ follows $2 + (-3) \le 5 + 1$, that is, $-1 \le 6$.

<?lean MathlibHandbook/V04/C08/Examples.lean#add_le_add?>

**Example (The class).** A lemma on a general ordered group takes the three instances. The lemma `add_le_add_right` adds the same term $c$ on the left of both sides.

<?lean MathlibHandbook/V04/C08/Examples.lean#class?>

**Example (A difference).** In $\mathbb{R}$, $0 \le a - b$ is the same as $b \le a$, by part 1 of the theorem on differences.

<?lean MathlibHandbook/V04/C08/Examples.lean#sub_nonneg?>

**Example (The plane with the product order).** On $\mathbb{R}^2$, define $(x_1, y_1) \le (x_2, y_2)$ if $x_1 \le x_2$ and $y_1 \le y_2$. The translations keep this partial order, one component at a time, so $\mathbb{R}^2$ is an ordered group. It is not linear: $(1, 0)$ and $(0, 1)$ are not comparable. Its positive cone is the closed quadrant $P = \{(x, y) \mid x \ge 0, y \ge 0\}$, and $P \cup (-P)$ does not contain $(1, -1)$. Mathlib has the instances `Prod.instIsOrderedAddMonoid` and `Pi.isOrderedAddMonoid`, so `ℝ × ℝ` and `Fin n → ℝ` are ordered groups.

**Example (The natural numbers).** $\mathbb{N}$ is an ordered cancellative monoid: $c + a \le c + b$ gives $a \le b$ by induction on $c$. It is not a group, since $1$ has no negative, and the theorem on differences fails for the truncated subtraction: $0 \le 2 - 5$ holds, because $2 - 5 = 0$, but $5 \le 2$ is false.

**Counterexample (An ordered monoid that is not cancellative).** Let $M = \mathbb{N} \cup \{\infty\}$, with $n + \infty = \infty + n = \infty$ and $n \le \infty$ for each $n$. This is an ordered additive monoid: a translation by $\infty$ sends each element to $\infty$, and a translation by $n \in \mathbb{N}$ keeps the order. It is not cancellative: $\infty + 1 \le \infty + 0$, but $1 \le 0$ is false. Mathlib has it as `ℕ∞`. It also shows that the strict theorem needs cancellation: $0 < 1$ but $\infty + 0 = \infty + 1$.

**Counterexample (An order that addition does not keep).** Give $\mathbb{Z}$ the order in which $a \preceq b$ if $|a| < |b|$, or $|a| = |b|$ and $a \le b$. This is a linear order: $0 \prec -1 \prec 1 \prec -2 \prec 2 \prec \cdots$. Then $-1 \preceq 1$. Add $-1$ to both sides, and the results are $-2$ and $0$. But $|0| < |-2|$, so $-2 \preceq 0$ is false, and the translation by $-1$ does not keep the order.

### The library around it

The classes are in `Mathlib.Algebra.Order.Monoid.Defs`, and most lemmas are in the unbundled files `Mathlib.Algebra.Order.Monoid.Unbundled.Basic` and `Mathlib.Algebra.Order.Group.Unbundled.Basic`, with the hypotheses `AddLeftMono`, `AddRightMono`, `AddLeftStrictMono` and `AddLeftReflectLE`.

The names follow a pattern: `add_le_add`, `add_lt_add` and `add_lt_add_of_le_of_lt` add two inequalities; `add_nonneg`, `add_pos`, `sub_nonneg`, `neg_nonneg` give a sign; the equivalences end in `_iff`. The multiplicative lemmas take a prime, as `mul_le_mul'`, since `mul_le_mul` is the lemma of ordered rings.

The tactic `linarith` proves most goals with sums and differences in a linearly ordered field, and `gcongr` works in each ordered monoid. Ordered rings use `IsOrderedRing` in the same unbundled style.

### Exercises

1. (A) Give the three instance arguments of a lemma on a linearly ordered additive group, and the two of a lemma on an ordered cancellative monoid.
2. (A) In an ordered group, show that $a \le b$ and $c < d$ give $a + c < b + d$. *Hint:* the theorem on strict inequalities and commutativity.
3. (A) In an ordered group, show that $a \le b$ if and only if $a - b \le 0$.
4. (B) In an ordered group, show that $a < b$ if and only if $-b < -a$.
5. (B) Let $G$ be an ordered group and let $n \ge 1$. Show that $0 \le a$ gives $0 \le n a$, where $n a = a + \dots + a$. Show that $n a \le n b$ follows from $a \le b$. *Hint:* induction on $n$ with the theorem on addition.
6. (B) In a linearly ordered group, show that $n a = 0$ with $n \ge 1$ gives $a = 0$. So a linearly ordered group has no element of finite order other than $0$. *Hint:* if $0 < a$, then $0 < n a$ by the strict form of exercise 5.
7. (B) Find the positive cone of $\mathbb{Z}$ with the usual order, and check the three conditions of the theorem on the cone.
8. (C) Show that the cyclic group $\mathbb{Z}/3\mathbb{Z}$ has no linear order that makes it an ordered group, and find all the partial orders that make it an ordered group. *Hint:* a cone $P$ with $x \in P$ and $x \ne 0$ contains $x + x$ and $x + x + x = 0$; check $P \cap (-P)$.
9. (L) Prove that a sum of two positive reals is positive. The solution is `add_pos_example`.

### Notes and history

Ordered groups go back to Hölder (1901), who proved that each Archimedean linearly ordered group embeds in $(\mathbb{R}, +)$, and to Hahn (1907) for the non-Archimedean case. The theory is in Birkhoff, *Lattice theory*, Chapter XIII, and in Fuchs, *Partially ordered algebraic systems* (1963).

Mathlib had the bundled classes `OrderedAddCommGroup` and `LinearOrderedAddCommGroup` for many years, with Jeremy Avigad, Leonardo de Moura, Mario Carneiro and Johannes Hölzl among the first authors of the file. In 2025 the library replaced them with the mixins `IsOrderedAddMonoid` and `IsOrderedCancelAddMonoid`, because the bundled classes needed one class for each combination of algebra and order.

### Reference

<?reference?>
