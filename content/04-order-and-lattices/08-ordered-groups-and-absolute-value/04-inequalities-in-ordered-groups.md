---
title: Inequalities in ordered groups
kind: api
modules:
  - Mathlib.Algebra.Order.Group.Unbundled.Basic
  - Mathlib.Algebra.Order.Group.Basic
  - Mathlib.Algebra.Order.Monoid.Unbundled.Pow
  - Mathlib.Algebra.Order.Group.MinMax
  - Mathlib.Algebra.Order.Group.DenselyOrdered
  - Mathlib.Algebra.Order.Group.Bounds
  - Mathlib.Algebra.Order.Group.OrderIso
  - Mathlib.Algebra.Order.Group.Lattice
  - Mathlib.Algebra.Order.Group.Cone
  - Mathlib.Algebra.Order.Group.Cyclic
explains:
  E2: [div_le_iff_le_mul, inv_le_inv_iff, le_of_forall_pos_lt_add, le_of_forall_lt_one_mul_le, IsLUB.exists_between_sub_self, OrderIso.mulLeft, inf_mul_sup, CommGroup.toDistribLattice, PartialOrder.ofSubmonoid, LinearOrderedCommGroup.Subgroup.genLTOne]
  E1: auto
families: []
requires: [V04.C02, V04.C03, V01.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Inequalities in ordered groups

### Overview

In a group, multiplication by a fixed element $c$ has an inverse map, the multiplication by $c^{-1}$. When the order is compatible with multiplication, both maps are monotone, and so multiplication by $c$ is an order isomorphism. This one fact turns most one-way lemmas of the previous section into equivalences. A term can move from one side of an inequality to the other, an inverse reverses the order, and a supremum commutes with multiplication.

This section describes the lemmas that the library proves from this fact. They ask for the covariant classes `MulLeftMono` and `MulRightMono` of the previous section, not for a bundled ordered group, and so they apply to noncommutative groups with an order that is compatible on one side only. The section also treats integer powers, the arguments with an arbitrary small $\varepsilon$, the lattice operations in a lattice-ordered group, the construction of an order from a positive cone, and the generator of a cyclic subgroup.

### The library around it

#### Moving terms across an inequality

The basic equivalences are in `Mathlib.Algebra.Order.Group.Unbundled.Basic`. The lemma `div_le_iff_le_mul` states $a / c \le b \leftrightarrow a \le b c$ in a group with `MulRightMono`. To prove it, multiply both sides on the right by $c$ for one direction and by $c^{-1}$ for the other. The other positions have their own names: `le_div_iff_mul_le` gives $a \le c / b \leftrightarrow a b \le c$, `inv_mul_le_iff_le_mul` gives $b^{-1} a \le c \leftrightarrow a \le b c$ with `MulLeftMono`, and `mul_inv_le_iff_le_mul` gives $a b^{-1} \le c \leftrightarrow a \le c b$. Their additive forms are `sub_le_iff_le_add` and `le_sub_iff_add_le`. The names say where the term goes: the part before *iff* is the hypothesis form and the part after it is the result.

The inverse reverses the order. The lemma `inv_le_inv_iff` states $a^{-1} \le b^{-1} \leftrightarrow b \le a$ and asks for both classes. For the proof, multiply $a^{-1} \le b^{-1}$ on the left by $a$ and on the right by $b$. The result is $b \le a$, and the converse is the same argument. With one class only, the library gives the comparison with the identity: `inv_le_one'` states $a^{-1} \le 1 \leftrightarrow 1 \le a$, and `one_le_inv'` is its dual. The lemmas `inv_le'` and `le_inv'` move an inverse to the other side. For a function, `Monotone.inv` turns a monotone $f$ into the antitone function $x \mapsto f(x)^{-1}$.

In a commutative group, division is monotone in the first argument and antitone in the second. The lemma `div_le_div''` gives $a / d \le b / c$ from $a \le b$ and $c \le d$, and `div_le_div_iff'` states $a / b \le c / d \leftrightarrow a d \le c b$. The lemma `div_le_div_iff_left` states $a / b \le a / c \leftrightarrow c \le b$, and `div_le_self_iff` states $a / b \le a \leftrightarrow 1 \le b$. For a linear order, `cmp_div_one'` shows that $a / b$ compares to $1$ as $a$ compares to $b$.

An additive group with `AddRightMono` has the instance `AddGroup.toOrderedSub`. So the lemmas of truncated subtraction, which Section 5 describes, also apply to groups, where the truncated difference is the usual difference.

#### Order isomorphisms

The file `Mathlib.Algebra.Order.Group.OrderIso` makes the remark of the overview into definitions. The term `OrderIso.mulLeft a` is the order isomorphism $x \mapsto a x$ of $\alpha$, and `OrderIso.mulRight a` is $x \mapsto x a$. The term `OrderIso.inv α` is an order isomorphism from $\alpha$ to the order dual `OrderDual α`, because the inverse reverses the order. The terms `OrderIso.divLeft a` and `OrderIso.divRight a` treat division in the same way. Each general lemma about order isomorphisms then applies. For example, `OrderIso.map_sup` applied to `OrderIso.mulLeft c` gives $c (a \sqcup b) = c a \sqcup c b$.

#### Arguments with a small epsilon

A common way to prove $a \le b$ is to prove $a < b + \varepsilon$ for each $\varepsilon > 0$. The lemma `le_of_forall_pos_lt_add` does this in a linearly ordered additive group, and `le_iff_forall_pos_lt_add` is its equivalence form. The proof is short. If $b < a$, then $\varepsilon = a - b$ is positive, and the hypothesis gives $a < b + (a - b) = a$, which is false. The multiplicative form is `le_of_forall_one_lt_lt_mul`.

The weak form, with $a \le b + \varepsilon$ in place of $a < b + \varepsilon$, needs a dense order. In $\mathbb{Z}$ the inequality $1 - \varepsilon \le 0$ is true for each $\varepsilon \ge 1$, but $1 \le 0$ is false. The file `Mathlib.Algebra.Order.Group.DenselyOrdered` has the dense forms. The lemma `le_of_forall_lt_one_mul_le` proves $a \le b$ from $a \varepsilon \le b$ for each $\varepsilon < 1$, and `le_of_forall_pos_sub_le` is the additive form with $a - \varepsilon \le b$. The lemma `le_mul_of_forall_lt` proves $c \le a b$ from $c \le a' b'$ for all $a' > a$ and $b' > b$. The lemma `exists_pow_lt_of_one_lt` finds, for $x > 1$ and each $n$, an element $y > 1$ with $y^n < x$. This is the multiplicative form of the division of $\varepsilon$ into $n$ parts.

The file `Mathlib.Algebra.Order.Group.Bounds` applies the same idea to bounds. The lemma `IsLUB.exists_between_sub_self` states that if $a$ is a least upper bound of $s$ and $\varepsilon > 0$, then some $b \in s$ satisfies $a - \varepsilon < b \le a$. The reason is that $a - \varepsilon < a$, and so $a - \varepsilon$ is not an upper bound of $s$. The lemma `IsGLB.exists_between_self_add` is the dual. These lemmas are the usual approximation property of a supremum in analysis, stated for any linearly ordered additive group.

#### Powers

The file `Mathlib.Algebra.Order.Monoid.Unbundled.Pow` treats natural powers in a monoid. The lemma `pow_le_pow_left'` gives $a^i \le b^i$ from $a \le b$, with both covariant classes. The lemma `pow_right_monotone` states that $n \mapsto a^n$ is monotone when $1 \le a$, and `le_self_pow` gives $a \le a^n$ for $n \ne 0$. In a linear order with the strict classes, `le_of_pow_le_pow_left'` reverses the first lemma for $n \ne 0$. The lemmas `max_pow` and `min_pow` show that the power commutes with the maximum and the minimum.

The file `Mathlib.Algebra.Order.Group.Basic` treats integer powers in an ordered commutative group. The lemma `zpow_le_zpow_right` gives $a^m \le a^n$ from $1 \le a$ and $m \le n$, and `zpow_le_zpow_iff_right` is the equivalence when $1 < a$. The lemma `zpow_left_strictMono` states that $x \mapsto x^n$ is strictly monotone for $n > 0$, and `zpow_right_strictAnti` states that $n \mapsto a^n$ is strictly antitone for $a < 1$. The same file proves `not_isCyclic_of_denselyOrdered`: a nontrivial densely ordered group is not cyclic.

#### Lattice operations

The file `Mathlib.Algebra.Order.Group.Lattice` treats a group whose order is a lattice. Because multiplication by $c$ is an order isomorphism, it commutes with both operations: `mul_sup` states $c (a \sqcup b) = c a \sqcup c b$, and `mul_inf`, `sup_mul` and `inf_mul` are the other cases. The inverse exchanges the two operations, so `inv_sup` states $(a \sqcup b)^{-1} = a^{-1} \sqcap b^{-1}$. The lemmas `div_sup` and `sup_div` treat division.

In a commutative group, `inf_mul_sup` states $(a \sqcap b)(a \sqcup b) = a b$. For real numbers this is $\min(a, b) + \max(a, b) = a + b$. A further consequence is that the lattice is distributive. The definition `CommGroup.toDistribLattice` gives this structure, and its additive form is `AddCommGroup.toDistribLattice`. The lemma `pow_two_semiclosed` states that $1 \le a^2$ gives $1 \le a$.

For a linear order, the file `Mathlib.Algebra.Order.Group.MinMax` has the forms with the maximum and the minimum. Examples are `max_inv_inv'`, which states $\max(a^{-1}, b^{-1}) = (\min(a, b))^{-1}$, and `max_zero_sub_eq_self`, which states $\max(a, 0) - \max(-a, 0) = a$. The file also has bounds such as `abs_max_sub_max_le_abs`, which says that $x \mapsto \max(x, c)$ does not increase distances.

#### Positive cones

An order on a commutative group is fixed by its set of elements that are at least $1$. The file `Mathlib.Algebra.Order.Group.Cone` goes in the other direction. A submonoid $M$ of $G$ is *pointed* if $a \in M$ and $a^{-1} \in M$ give $a = 1$, which is the predicate `Submonoid.IsMulPointed`. For a pointed submonoid, the definition `PartialOrder.ofSubmonoid` makes the order with $a \le b$ when $b / a \in M$, as `PartialOrder.ofSubmonoid_le_iff` states. The lemma `IsOrderedMonoid.ofSubmonoid` shows that this order is compatible with multiplication. If $M$ also satisfies `Submonoid.IsMulSpanning`, which gives $a \in M$ or $a^{-1} \in M$ for each $a$ by `Submonoid.IsMulSpanning.mem_or_inv_mem`, and membership is decidable, then `LinearOrder.ofSubmonoid` gives a linear order. In the converse direction, the submonoid `Submonoid.oneLE` of the elements at least $1$ of an ordered group is pointed, by `Submonoid.IsMulPointed.oneLE`, and it is spanning when the order is linear, by `Submonoid.IsMulSpanning.oneLE`. Section 1 describes the additive form `PartialOrder.ofAddSubmonoid` of this construction.

#### Cyclic subgroups

The file `Mathlib.Algebra.Order.Group.Cyclic` chooses a generator. Let $H$ be a nontrivial cyclic subgroup of a linearly ordered commutative group. If $g$ generates $H$, then $g^{-1}$ also generates $H$, and $g \ne 1$. So exactly one of $g$ and $g^{-1}$ is less than $1$. The lemma `LinearOrderedCommGroup.Subgroup.exists_generator_lt_one` states this, and `LinearOrderedCommGroup.Subgroup.genLTOne` is the generator less than $1$. The lemma `LinearOrderedCommGroup.Subgroup.genLTOne_zpowers_eq_top` shows that it generates $H$. For the whole group, `LinearOrderedCommGroup.genLTOne` is the generator and `LinearOrderedCommGroup.genLTOne_unique` states that it is unique.

#### Common errors

1. The lemma `inv_le_inv_iff` asks for both `MulLeftMono` and `MulRightMono`. In a noncommutative group with a compatible order on one side only, it does not apply. Use `inv_le_one'` and the lemmas that move a term, which ask for one class.
2. The definition `CommGroup.toDistribLattice` is a definition and not an instance, so instance search does not find it. Add it to the context with `letI := CommGroup.toDistribLattice α` when a proof needs distributivity.
3. The lemma `le_of_forall_lt_one_mul_le` asks for `DenselyOrdered`, and so it does not apply to $\mathbb{Z}$. For a discrete group, prove the strict hypothesis and use `le_of_forall_pos_lt_add`.

### Exercises

1. (A) Prove `inv_le_inv_iff` from `div_le_iff_le_mul` and `inv_mul_le_iff_le_mul`.
2. (A) Prove `le_of_forall_pos_lt_add` without the lemma `le_iff_forall_pos_lt_add`, and give the multiplicative form.
3. (B) Prove `inf_mul_sup` in a lattice-ordered commutative group. Use `inv_inf` and `mul_sup` to compute $a b (a \sqcap b)^{-1}$.
4. (B) Prove `IsLUB.exists_between_sub_self`, and show by an example in $\mathbb{Q}$ that $b < a$ need not hold.
5. (B) Prove `not_isCyclic_of_denselyOrdered`. Take a generator $g < 1$, an element $y$ with $g < y < 1$, and use `zpow_right_strictAnti`.
6. (C) Let $M$ be a submonoid of $G$ that is pointed and spanning. Show that the order of `PartialOrder.ofSubmonoid` is total, and that each nontrivial cyclic subgroup then has a generator in $M$.

### Reference

<?reference?>
