---
title: Monoids and groups
kind: theory
modules:
  - Mathlib.Algebra.Group.Defs
  - Mathlib.Algebra.Group.Basic
explains:
  E3: [Group]
  E2: [Monoid, Semigroup, CommGroup, inv_mul_cancel, mul_inv_cancel, mul_inv_rev, mul_left_cancel, left_inv_eq_right_inv]
  E1: auto
families: []
requires: [V01.C04, V01.C06]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V05/C01/Examples.lean
  - MathlibHandbook/V05/C01/Exercises.lean
  - MathlibHandbook/V05/C01/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Monoids and groups

### Overview

A group is a set with a product, a unit and inverses that obey three axioms. Groups describe symmetry: the rotations of a square, the permutations of the roots of a polynomial, the invertible matrices of a given size. The axioms are few, but they force a rigid structure. Each equation $a x = b$ has exactly one solution, the unit is unique, and each element has exactly one inverse.

This section gives the axioms in the form that Mathlib uses. Mathlib does not define a group in one step. It builds the class `Group` on a chain of smaller classes: a semigroup has an associative product, a monoid adds a unit, and a group adds an inverse. Each lemma is proved once, at the smallest class where it holds. So a lemma about monoids applies at once to groups, to the natural numbers under multiplication and to the square matrices.

The main result of the section is that a left inverse is also a right inverse. Mathlib asks only for $a^{-1} a = 1$ in the definition of a group, and it proves $a a^{-1} = 1$.

### Definitions

**Definition (Semigroup).** A semigroup is a set $S$ with a binary operation $(a, b) \mapsto a \cdot b$ that is associative: $(a \cdot b) \cdot c = a \cdot (b \cdot c)$ for all $a, b, c \in S$.

Associativity lets the reader drop the brackets. Any two ways to bracket a product $a_1 a_2 \cdots a_n$ give the same element. The proof is by induction on $n$: each bracketing equals the product in which the brackets all open on the left. Below, products are written without brackets.

::: mathlib
`Semigroup` · `Mathlib.Algebra.Group.Semigroup`

The class extends `Mul G`, the notation `*`, with the one field `mul_assoc`. The lemma `mul_assoc` states $(a b) c = a (b c)$, with the brackets of the left side to the left. In a Lean term, `a * b * c` means `(a * b) * c`, because `*` associates to the left.

<?decl Semigroup?>
:::

**Definition (Monoid).** A monoid is a semigroup $M$ with an element $1$ such that $1 \cdot a = a$ and $a \cdot 1 = a$ for each $a \in M$. The element $1$ is the unit, or identity.

For $n \in \mathbb{N}$ the power $a^n$ is defined by $a^0 = 1$ and $a^{n+1} = a^n \cdot a$. A monoid need not have inverses. The natural numbers under multiplication are a monoid with unit $1$, and $2$ has no inverse. The maps $X \to X$ of a set $X$ to itself are a monoid under composition, with the identity map as unit.

::: mathlib
`Monoid` · `Mathlib.Algebra.Group.Monoid`

The class extends `Semigroup` and `MulOneClass`, which has the fields `one_mul` and `mul_one`. It also has a field `npow` for the power $a^n$ with $n : ℕ$, and two axioms that say that `npow` satisfies the recursion above. The power is a field, not a definition, so that a concrete type can give a fast power. For example, the power on `ℕ` is the built-in power of Lean. The axioms guarantee that each choice gives the same values.

<?decl Monoid?>
:::

**Definition (Group).** A group is a monoid $G$ with a map $a \mapsto a^{-1}$ such that $a^{-1} \cdot a = 1$ for each $a \in G$. The element $a^{-1}$ is the inverse of $a$.

The definition asks for a left inverse only. The first theorem below shows that the left inverse is also a right inverse. A textbook often asks for both, and the two definitions are equivalent. The smaller set of axioms makes it easier to show that a given structure is a group: there is less to check.

::: mathlib
`Group` · `Mathlib.Algebra.Group.Defs`

The class extends `DivInvMonoid`, which has the inverse `a⁻¹`, the division `a / b` and the power `a ^ n` for `n : ℤ`. Division and the integer power are fields with axioms: `div_eq_mul_inv` says $a / b = a b^{-1}$, and the integer power agrees with the natural power and with the inverse. The one new axiom of `Group` is `inv_mul_cancel`. Mathlib puts division in the class, and does not define it as $a b^{-1}$, so that a type such as `ℚ` can use its own division and the two notions are equal by definition, not only by a theorem.

<?decl Group?>
:::

**Definition (Commutative group).** A group $G$ is commutative, or abelian, if $a \cdot b = b \cdot a$ for all $a, b \in G$. A commutative monoid is defined in the same way.

::: mathlib
`CommGroup` · `Mathlib.Algebra.Group.Defs`

The class extends `Group` and `CommMonoid`. A lemma that needs commutativity, such as `mul_mul_mul_comm` or `mul_pow`, asks for `CommMonoid` or `CommGroup`. The lemma `mul_comm` itself asks only for `CommMagma`, a type with a commutative product.

<?decl CommGroup?>
:::

**Definition (Additive group).** An additive group is a group in which the operation is written $a + b$, the unit is written $0$ and the inverse is written $-a$. The power $a^n$ becomes the multiple $n \cdot a$. A commutative group is often written additively, for example $(\mathbb{Z}, +)$.

Mathlib has the class `AddGroup A` as the additive copy of `Group`. It does not prove its lemmas again. The attribute `to_additive` on a multiplicative lemma makes the additive lemma, and it changes the name by fixed rules: `mul` becomes `add`, `one` becomes `zero`, `inv` becomes `neg`, `div` becomes `sub` and `pow` becomes `nsmul` or `zsmul`. So `inv_mul_cancel` gives `neg_add_cancel`.

### Theorems and proofs

**Lemma (The unit is unique).** Let $M$ be a monoid. If $e \in M$ satisfies $e \cdot a = a$ for each $a$, then $e = 1$.

*Proof.* Put $a = 1$. Then $e \cdot 1 = 1$. The axiom $x \cdot 1 = x$ with $x = e$ gives $e \cdot 1 = e$. So $e = e \cdot 1 = 1$. $\square$

**Lemma (Left and right inverses).** Let $M$ be a monoid and let $a, b, c \in M$. If $b \cdot a = 1$ and $a \cdot c = 1$, then $b = c$.

*Proof.* Use the unit and associativity:
$$b = b \cdot 1 = b \cdot (a \cdot c) = (b \cdot a) \cdot c = 1 \cdot c = c.$$
$\square$

The lemma says that an element of a monoid has at most one two-sided inverse. It does not say that a left inverse is a right inverse. That fails in a monoid in general, as the examples show.

::: mathlib
`left_inv_eq_right_inv` · `Mathlib.Algebra.Group.Monoid`

The lemma above, with the hypotheses `b * a = 1` and `a * c = 1`. It holds in each monoid, so it gives the uniqueness of the inverse of a unit of a ring, of an invertible matrix and of a bijection.

<?decl left_inv_eq_right_inv?>
:::

**Theorem (Right inverse).** In a group $G$, each element satisfies $a \cdot a^{-1} = 1$.

*Proof.* Put $b = a^{-1}$. The axiom of the inverse, for the element $b$, gives $b^{-1} \cdot b = 1$. For the element $a$ it gives $b \cdot a = 1$. Now compute, with associativity at each step:
$$a b = 1 \cdot (a b) = (b^{-1} b)(a b) = b^{-1} \big( (b a) b \big) = b^{-1} (1 \cdot b) = b^{-1} b = 1.$$
The first equality is the axiom of the unit. The second replaces $1$ by $b^{-1} b$. The third regroups the product $b^{-1} \cdot b \cdot a \cdot b$. The fourth uses $b a = 1$, and the fifth uses the axiom of the unit again. $\square$

So $a^{-1}$ is a two-sided inverse of $a$. By the lemma on left and right inverses, it is the only one.

::: mathlib
`mul_inv_cancel` · `Mathlib.Algebra.Group.Defs`

The right inverse $a a^{-1} = 1$. In Mathlib it is a theorem with the proof above. The name follows the statement: `mul_inv_cancel` is $a \cdot a^{-1} = 1$, with `mul` before `inv`, and `inv_mul_cancel` is $a^{-1} \cdot a = 1$. Old versions of Mathlib called the two lemmas `mul_right_inv` and `mul_left_inv`. The deprecated names may still appear in old code.

<?decl mul_inv_cancel?>
:::

::: mathlib
`inv_mul_cancel` · `Mathlib.Algebra.Group.Defs`

The axiom of the inverse. Its additive copy is `neg_add_cancel`, which says $-a + a = 0$.

<?decl inv_mul_cancel?>
:::

**Theorem (Cancellation).** In a group, $a b = a c$ implies $b = c$, and $b a = c a$ implies $b = c$.

*Proof.* Assume $a b = a c$. Multiply both sides on the left by $a^{-1}$. Then $a^{-1}(a b) = a^{-1}(a c)$. By associativity, the left side is $(a^{-1} a) b = 1 \cdot b = b$, and the right side is $c$ for the same reason. So $b = c$. For the second claim, multiply on the right by $a^{-1}$ and use $a a^{-1} = 1$ from the theorem on the right inverse. $\square$

**Corollary (Equations have one solution).** Let $a, b \in G$. The equation $a x = b$ has exactly one solution $x \in G$, namely $x = a^{-1} b$. The equation $y a = b$ has exactly one solution, namely $y = b a^{-1}$.

*Proof.* The element $x = a^{-1} b$ is a solution, because $a (a^{-1} b) = (a a^{-1}) b = b$. If $x'$ is another solution, then $a x = b = a x'$, and cancellation gives $x = x'$. The second equation is the same with the sides exchanged. $\square$

The corollary has a pleasant consequence for a finite group. In its multiplication table, each row and each column contains each element exactly once. The row of $a$ lists the products $a x$, and the corollary says that each $b$ occurs as $a x$ for exactly one $x$. A table with this property is a Latin square.

::: mathlib
`mul_left_cancel` · `Mathlib.Algebra.Group.Semigroup`

The lemma asks only for the class `IsLeftCancelMul G`. A group is an instance, and so is the additive monoid `ℕ`, which is not a group. This is the reason for the separate class: cancellation holds in more places than inverses. The form `mul_left_cancel_iff` is an equivalence, and `simp` uses it to remove a common left factor from an equation.

<?decl mul_left_cancel?>
:::

**Theorem (Inverses of inverses and products).** In a group, $(a^{-1})^{-1} = a$ and $(a b)^{-1} = b^{-1} a^{-1}$.

*Proof.* For the first claim, $a^{-1} \cdot a = 1$ and $a \cdot a^{-1} = 1$ say that $a$ is a two-sided inverse of $a^{-1}$. The inverse is unique, so $(a^{-1})^{-1} = a$. For the second claim, compute
$$(a b)(b^{-1} a^{-1}) = a (b b^{-1}) a^{-1} = a \cdot 1 \cdot a^{-1} = a a^{-1} = 1.$$
So $b^{-1} a^{-1}$ is a right inverse of $a b$. The element $(a b)^{-1}$ is a left inverse of $a b$. By the lemma on left and right inverses, the two are equal. $\square$

The order of the factors reverses. A student who writes $(a b)^{-1} = a^{-1} b^{-1}$ makes the most common error of the subject. The two sides agree only when $a$ and $b$ commute. Think of socks and shoes: to undo "socks, then shoes", remove the shoes first.

::: mathlib
`mul_inv_rev` · `Mathlib.Algebra.Group.DivInvMonoid`

The lemma holds in each `DivisionMonoid`, a class that contains the groups and also the groups with zero, such as `ℚ`. The `rev` in the name says that the order of the factors reverses. The commutative form is `mul_inv`, which keeps the order.

<?decl mul_inv_rev?>
:::

**Theorem (Exponent two).** Let $G$ be a group with $a^2 = 1$ for each $a \in G$. Then $G$ is commutative.

*Proof.* From $a a = 1$ the element $a$ is its own inverse: $a^{-1} = a$ for each $a$. Let $a, b \in G$. Then $a b$ is also its own inverse. So
$$a b = (a b)^{-1} = b^{-1} a^{-1} = b a,$$
by the theorem on the inverse of a product. $\square$

### Examples

**Example (Numbers).** The integers $(\mathbb{Z}, +)$ are a commutative group with unit $0$ and inverse $-a$. The nonzero rationals $(\mathbb{Q} \setminus \{0\}, \cdot)$ are a commutative group with inverse $1/a$. The natural numbers $(\mathbb{N}, +)$ are a commutative monoid but not a group: $1$ has no additive inverse in $\mathbb{N}$. The integers under multiplication are a monoid, and only $1$ and $-1$ have inverses.

**Example (A table).** Let $V = \{e, a, b, c\}$ with the table below, where the row gives the left factor.

| $\cdot$ | $e$ | $a$ | $b$ | $c$ |
|---|---|---|---|---|
| $e$ | $e$ | $a$ | $b$ | $c$ |
| $a$ | $a$ | $e$ | $c$ | $b$ |
| $b$ | $b$ | $c$ | $e$ | $a$ |
| $c$ | $c$ | $b$ | $a$ | $e$ |

The row and the column of $e$ copy the headings, so $e$ is the unit. The diagonal is $e$, so each element is its own inverse. The table is symmetric, so the product is commutative. Associativity needs a check. One way avoids the $64$ cases: the map $e \mapsto (0, 0)$, $a \mapsto (1, 0)$, $b \mapsto (0, 1)$, $c \mapsto (1, 1)$ turns the table into the addition of pairs modulo $2$, and that addition is associative. This group is the Klein four group.

**Example (A left inverse that is not a right inverse).** Let $M$ be the monoid of the maps $\mathbb{N} \to \mathbb{N}$ under composition. Let $s(n) = n + 1$, and let $t(n) = n - 1$ for $n \ge 1$ and $t(0) = 0$. Then $t(s(n)) = n$ for each $n$, so $t \circ s = \mathrm{id}$ and $t$ is a left inverse of $s$. But $s(t(0)) = 1$, so $s \circ t \neq \mathrm{id}$, and $t$ is not a right inverse of $s$. The map $s$ has no right inverse at all, because $s$ is not onto. So in a monoid a left inverse need not be a right inverse. The theorem on the right inverse uses that each element of a group has a left inverse, also the element $a^{-1}$ itself. In $M$ the element $t$ has no left inverse, because $t$ is not injective.

**Counterexample (Axioms on mixed sides).** The sides of the axioms matter. Let $X$ be a set with at least two elements, and put $a \cdot b = b$. This product is associative, because $(a \cdot b) \cdot c = c = a \cdot (b \cdot c)$. Fix $e \in X$. Then $e \cdot b = b$ for each $b$, so $e$ is a left unit. Each $a$ has a right inverse for $e$, since $a \cdot e = e$. But $X$ is not a group: a unit $1$ would satisfy $a \cdot 1 = a$, while $a \cdot 1 = 1$, so all elements would be equal to $1$. A left unit with left inverses gives a group. A left unit with right inverses does not.

**Example (The axioms in Lean).** The three axioms of a group are three lemmas.

<?lean MathlibHandbook/V05/C01/Examples.lean#group_axioms?>

**Example (Inverse of a product).**

<?lean MathlibHandbook/V05/C01/Examples.lean#mul_inv_rev?>

**Example (Cancellation).**

<?lean MathlibHandbook/V05/C01/Examples.lean#cancel?>

**Example (The additive copy).** The lemma `neg_add_cancel` is the additive copy of `inv_mul_cancel`.

<?lean MathlibHandbook/V05/C01/Examples.lean#additive?>

**Example (A commutative group).** The proof rewrites with `mul_comm` and then cancels.

<?lean MathlibHandbook/V05/C01/Examples.lean#comm_group?>

**Example (The tactic group).** The tactic `group` normalizes the two sides with the axioms of a group.

<?lean MathlibHandbook/V05/C01/Examples.lean#group_tactic?>

### The library around it

The classes are in `Mathlib.Algebra.Group.Defs` and the files next to it. The chain for the product is `Mul`, `Semigroup`, `MulOneClass`, `Monoid`, `DivInvMonoid`, `Group`, with the commutative forms `CommSemigroup`, `CommMonoid` and `CommGroup`. The cancellation classes `IsLeftCancelMul`, `LeftCancelMonoid` and `CancelCommMonoid` sit beside the chain. The class `DivisionMonoid` collects the lemmas on inverses that hold also in a group with zero.

The lemmas are named after their statements. The family `mul_inv_cancel_left`, `inv_mul_cancel_left`, `mul_inv_cancel_right` and `inv_mul_cancel_right` cancels a factor next to its inverse: `mul_inv_cancel_left a b` is $a (a^{-1} b) = b$. The family `mul_left_inj` and `mul_right_inj` turns an equation with a common factor into an equation without it. The lemmas `inv_mul_eq_one`, `mul_inv_eq_one` and `mul_eq_one_iff_eq_inv` turn an equation $x = 1$ into an equation between two elements.

To find a lemma, write its statement and use `exact?`. For an equation that follows from the axioms of a group only, use the tactic `group`. In a commutative group with additive notation, use `abel`. With the multiplicative notation, `simp only [mul_comm, mul_left_comm, mul_assoc]` often works, and so does `ring` in a commutative ring.

### Exercises

1. (A) Name the class of Mathlib for a type with an associative product and a unit, but with no inverse.
2. (A) Give the additive name of the lemma `mul_inv_rev`, and state it in additive notation.
3. (A) Show that in a group $(a b c)^{-1} = c^{-1} b^{-1} a^{-1}$. Hint: apply the theorem on the inverse of a product twice.
4. (B) Show that the set $\{1, -1, i, -i\}$ of complex numbers is a commutative group under multiplication, and that it is not the Klein four group. Hint: count the elements $x$ with $x^2 = 1$.
5. (B) Let $G$ be a group and let $a, b \in G$. Show that $(a b a^{-1})^n = a b^n a^{-1}$ for each $n \in \mathbb{N}$. Hint: induction on $n$, and cancel $a^{-1} a$ in the middle.
6. (B) Let $S$ be a semigroup with a left unit $e$, such that each $a$ has a left inverse $a'$ with $a' a = e$. Show that $S$ is a group. Hint: follow the proof of the theorem on the right inverse, then show that $e$ is also a right unit.
7. (C) Let $G$ be a finite semigroup in which both cancellation laws hold. Show that $G$ is a group, if $G$ is not empty. Hint: the map $x \mapsto a x$ is injective, so it is onto. Show that this fails for the infinite semigroup $(\mathbb{N} \setminus \{0\}, +)$.
8. (L) Prove that $(a^{-1})^{-1} = a$ in a group. The solution is `inv_inv_example`.
9. (L) Prove that $a \cdot b = 1$ gives $a^{-1} = b$. The solution is `inv_unique_example`.
10. (L) Prove that $-(a + b) = -b + -a$ in an additive group. The solution is `add_neg_rev_example`.
11. (L) Prove that conjugation by $g$ respects products. The solution is `conj_mul_example`.

### Notes and history

The idea of a group came from the study of permutations. Lagrange (1771), Ruffini and Cauchy used groups of permutations without the abstract notion. Cayley gave the first abstract definition in 1854, for finite groups. The modern axioms with one unit and one inverse on one side only go back to the work of Dickson and Huntington near 1905.

Mathlib takes the left inverse as the axiom and proves the right inverse, as in this section. The fields for the natural and the integer power, and for division, were added so that the instances of `ℕ`, `ℤ`, `ℚ` and `ℝ` agree with the built-in operations by definition.

### Reference

<?reference?>
