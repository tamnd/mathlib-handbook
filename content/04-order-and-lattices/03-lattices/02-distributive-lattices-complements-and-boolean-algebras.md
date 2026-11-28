---
title: Distributive lattices, complements and Boolean algebras
kind: theory
modules:
  - Mathlib.Order.Disjoint
  - Mathlib.Order.BooleanAlgebra.Defs
  - Mathlib.Order.BooleanAlgebra.Basic
  - Mathlib.Order.BooleanAlgebra.Set
  - Mathlib.Order.SymmDiff
  - Mathlib.Order.Disjointed
explains:
  E3: [DistribLattice, BooleanAlgebra, IsCompl]
  E2: [DistribLattice.ofInfSupLe, inf_sup_left, sup_inf_left, le_sup_inf, instDistribLatticeOfLinearOrder, Disjoint, disjoint_iff, Codisjoint, codisjoint_iff, IsCompl.right_unique, isCompl_compl, compl_compl, compl_inf, sdiff_eq, himp_eq, Set.instBooleanAlgebra]
  E1: auto
families: []
requires: [V04.C01]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V04/C03/Examples.lean
  - MathlibHandbook/V04/C03/Exercises.lean
  - MathlibHandbook/V04/C03/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Distributive lattices, complements and Boolean algebras

### Overview

The union and the intersection of sets satisfy the distributive law $s \cap (t \cup u) = (s \cap t) \cup (s \cap u)$. A general lattice does not, for example the lattice of subspaces of $\mathbb{R}^2$. In a distributive lattice an element has at most one complement. A distributive bounded lattice in which each element has a complement is a Boolean algebra, the algebraic form of the subsets of a set and of classical logic.

This section proves that the two distributive laws are equivalent, shows that $N_5$ and $M_3$ of Section 1 are not distributive, proves the uniqueness of complements and the laws of De Morgan, and ends with Heyting algebras, the algebras of intuitionistic logic.

### Definitions

**Definition (Distributive lattice).** A lattice $L$ is distributive if $a \sqcap (b \sqcup c) = (a \sqcap b) \sqcup (a \sqcap c)$ for all $a, b, c \in L$.

*Remarks.* The dual law $a \sqcup (b \sqcap c) = (a \sqcup b) \sqcap (a \sqcup c)$ is equivalent, by the first theorem below. In each lattice one inequality of each law holds. The lattices of subsets and of propositions are distributive, but the lattices of subspaces, of subgroups and of ideals in general are not.

::: mathlib
`DistribLattice` · `Mathlib.Order.Defs.Lattice`

The class extends `Lattice` with one field, `le_sup_inf : ∀ x y z, (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ y ⊓ z`, the half of the dual law that can fail. The equations are the lemmas `inf_sup_left` and `sup_inf_left`. To build an instance from law 1, use `DistribLattice.ofInfSupLe`.

<?decl DistribLattice?>
:::

Let $L$ be a bounded lattice. Two elements $a$ and $b$ are *disjoint* if $a \sqcap b = \bot$, and *codisjoint* if $a \sqcup b = \top$.

**Definition (Complement).** In a bounded lattice, $b$ is a complement of $a$ if $a \sqcap b = \bot$ and $a \sqcup b = \top$, that is, if $a$ and $b$ are disjoint and codisjoint. A lattice is complemented if each element has a complement.

**Definition (Boolean algebra).** A Boolean algebra is a bounded distributive lattice with a function $a \mapsto a^c$ such that $a^c$ is a complement of $a$ for each $a$. The difference is $a \setminus b = a \sqcap b^c$, and the implication is $a \Rightarrow b = a^c \sqcup b$.

::: mathlib
`Disjoint` · `Mathlib.Order.Disjoint`

Mathlib defines `Disjoint a b` in a partial order with `⊥`: each common lower bound of `a` and `b` is `⊥`. This needs no `⊓`. In a lattice, `disjoint_iff` turns it into `a ⊓ b = ⊥`. The dual is `Codisjoint`, with `codisjoint_iff : Codisjoint a b ↔ a ⊔ b = ⊤`.

<?decl Disjoint?>
:::

::: mathlib
`IsCompl` · `Mathlib.Order.Disjoint`

The structure `IsCompl a b` has the two fields `disjoint` and `codisjoint`. It is the relation "b is a complement of a", and it needs only a bounded partial order. In a Boolean algebra, `isCompl_compl` states `IsCompl x xᶜ`.

<?decl IsCompl?>
:::

::: mathlib
`BooleanAlgebra` · `Mathlib.Order.BooleanAlgebra.Defs`

The class extends `DistribLattice`, the operations `ᶜ`, `\` and `⇨`, and the bounds. Its axioms are `inf_compl_le_bot : x ⊓ xᶜ ≤ ⊥`, `top_le_sup_compl : ⊤ ≤ x ⊔ xᶜ`, `sdiff_eq : x \ y = x ⊓ yᶜ` and `himp_eq : x ⇨ y = y ⊔ xᶜ`. The difference and the implication are fields, so that an instance can choose a better definition; default values make them optional.

<?decl BooleanAlgebra?>
:::

### Theorems and proofs

**Theorem (The trivial halves).** In each lattice, $(a \sqcap b) \sqcup (a \sqcap c) \le a \sqcap (b \sqcup c)$ and $a \sqcup (b \sqcap c) \le (a \sqcup b) \sqcap (a \sqcup c)$.

*Proof.* For the first inequality, by the universal property of $\sqcup$ it is sufficient to show $a \sqcap b \le a \sqcap (b \sqcup c)$ and $a \sqcap c \le a \sqcap (b \sqcup c)$. The first follows from $a \le a$ and $b \le b \sqcup c$ by the monotonicity of $\sqcap$. The second is the same with $c \le b \sqcup c$. The second inequality is the first one in the dual order. $\square$

**Theorem (The two distributive laws).** In a lattice $L$, the following are equivalent:

1. $a \sqcap (b \sqcup c) = (a \sqcap b) \sqcup (a \sqcap c)$ for all $a, b, c$;
2. $a \sqcup (b \sqcap c) = (a \sqcup b) \sqcap (a \sqcup c)$ for all $a, b, c$.

*Proof.* Assume 1, and let $a, b, c \in L$. Apply 1 with $a \sqcup b$ in place of $a$, and $a$, $c$ in place of $b$, $c$:
$$(a \sqcup b) \sqcap (a \sqcup c) = ((a \sqcup b) \sqcap a) \sqcup ((a \sqcup b) \sqcap c).$$
By commutativity and absorption, $(a \sqcup b) \sqcap a = a \sqcap (a \sqcup b) = a$. By commutativity and 1, $(a \sqcup b) \sqcap c = c \sqcap (a \sqcup b) = (c \sqcap a) \sqcup (c \sqcap b)$. So the right side is
$$a \sqcup ((c \sqcap a) \sqcup (c \sqcap b)) = (a \sqcup (c \sqcap a)) \sqcup (c \sqcap b) = a \sqcup (c \sqcap b),$$
by associativity and the absorption $a \sqcup (a \sqcap c) = a$. Since $c \sqcap b = b \sqcap c$, this is 2. The proof that 2 gives 1 is the same proof in the dual order, because the dual of law 1 is law 2. $\square$

**Theorem (Linear orders are distributive).** Each linear order is a distributive lattice.

*Proof.* Let $a, b, c$ be elements of a linear order. The two sides of law 1 do not change when $b$ and $c$ are exchanged, so assume $b \le c$. Then $b \sqcup c = c$, and the left side is $a \sqcap c$. By monotonicity, $a \sqcap b \le a \sqcap c$, so the right side is $(a \sqcap b) \sqcup (a \sqcap c) = a \sqcap c$. The two sides are equal. $\square$

**Theorem (Distributive lattices are modular).** In a distributive lattice, $a \le c$ gives $a \sqcup (b \sqcap c) = (a \sqcup b) \sqcap c$.

*Proof.* By law 2, $a \sqcup (b \sqcap c) = (a \sqcup b) \sqcap (a \sqcup c)$. Since $a \le c$, $a \sqcup c = c$. $\square$

The law of this theorem is the modular law. The lattices of subspaces of a vector space and of normal subgroups of a group are modular, but in general not distributive. Mathlib has the class `IsModularLattice`.

**Theorem (Uniqueness of complements).** In a bounded distributive lattice, an element has at most one complement.

*Proof.* Let $b$ and $c$ be complements of $a$. Then
$$b = b \sqcap \top = b \sqcap (a \sqcup c) = (b \sqcap a) \sqcup (b \sqcap c) = \bot \sqcup (b \sqcap c) = b \sqcap c.$$
The steps use $a \sqcup c = \top$, law 1, and $b \sqcap a = a \sqcap b = \bot$. The same computation with $b$ and $c$ exchanged gives $c = c \sqcap b$. So $b = b \sqcap c = c \sqcap b = c$. $\square$

::: mathlib
`IsCompl.right_unique` · `Mathlib.Order.Disjoint`

The statement is `IsCompl x y → IsCompl x z → y = z`. In a Boolean algebra, `IsCompl.compl_eq` turns `IsCompl a b` into `aᶜ = b`. This is the standard way to compute a complement: guess it, and check the two equations.

<?decl IsCompl.right_unique?>
:::

**Theorem (Laws of a Boolean algebra).** In a Boolean algebra, for all $a, b$:

1. $(a^c)^c = a$;
2. $(a \sqcup b)^c = a^c \sqcap b^c$ and $(a \sqcap b)^c = a^c \sqcup b^c$ (De Morgan);
3. $\bot^c = \top$ and $\top^c = \bot$;
4. $a \le b$ if and only if $b^c \le a^c$;
5. for each $x$, $x \le a^c \sqcup b$ if and only if $a \sqcap x \le b$.

*Proof.* 1. The element $a$ satisfies $a^c \sqcap a = \bot$ and $a^c \sqcup a = \top$, so $a$ is a complement of $a^c$. So is $(a^c)^c$. By uniqueness, $(a^c)^c = a$.

2. Show that $a^c \sqcap b^c$ is a complement of $a \sqcup b$. By distributivity,
$$(a \sqcup b) \sqcap (a^c \sqcap b^c) = (a \sqcap a^c \sqcap b^c) \sqcup (b \sqcap a^c \sqcap b^c) = (\bot \sqcap b^c) \sqcup (a^c \sqcap \bot) = \bot,$$
after commutativity and associativity inside each term. By the dual law,
$$(a \sqcup b) \sqcup (a^c \sqcap b^c) = (a \sqcup b \sqcup a^c) \sqcap (a \sqcup b \sqcup b^c) = \top \sqcap \top = \top.$$
By uniqueness, $(a \sqcup b)^c = a^c \sqcap b^c$. Apply this to $a^c$ and $b^c$ and use 1: $(a^c \sqcup b^c)^c = a \sqcap b$. Take the complement of both sides and use 1 again: $a^c \sqcup b^c = (a \sqcap b)^c$.

3. $\bot \sqcap \top = \bot$ and $\bot \sqcup \top = \top$, so $\top$ is a complement of $\bot$. The second statement follows by 1.

4. If $a \le b$, then $a \sqcup b = b$, and by 2, $b^c = a^c \sqcap b^c$, so $b^c \le a^c$. Conversely, if $b^c \le a^c$, then the first part gives $(a^c)^c \le (b^c)^c$, that is $a \le b$ by 1.

5. Suppose $x \le a^c \sqcup b$. Then $a \sqcap x \le a \sqcap (a^c \sqcup b) = (a \sqcap a^c) \sqcup (a \sqcap b) = a \sqcap b \le b$. Conversely, suppose $a \sqcap x \le b$. Then
$$x = x \sqcap \top = x \sqcap (a \sqcup a^c) = (x \sqcap a) \sqcup (x \sqcap a^c) \le b \sqcup a^c,$$
because $x \sqcap a \le b$ and $x \sqcap a^c \le a^c$. $\square$

Part 5 says that $a \Rightarrow b = a^c \sqcup b$ is the largest $x$ with $a \sqcap x \le b$. This property makes sense in each lattice, and it defines the Heyting algebras.

**Definition (Heyting algebra).** A Heyting algebra is a bounded lattice with an operation $\Rightarrow$ such that $a \sqcap x \le b$ if and only if $x \le (a \Rightarrow b)$, for all $a, b, x$. The pseudo-complement is $\neg a = (a \Rightarrow \bot)$.

**Theorem (Heyting algebras are distributive).** Each Heyting algebra is a distributive lattice.

*Proof.* By the trivial halves it is sufficient to show $a \sqcap (b \sqcup c) \le (a \sqcap b) \sqcup (a \sqcap c)$. Let $d = (a \sqcap b) \sqcup (a \sqcap c)$. Then $a \sqcap b \le d$, so $b \le (a \Rightarrow d)$ by the defining property. In the same way $c \le (a \Rightarrow d)$. So $b \sqcup c \le (a \Rightarrow d)$, and the defining property in the other direction gives $a \sqcap (b \sqcup c) \le d$. $\square$

So a Boolean algebra is a Heyting algebra by part 5, and a Heyting algebra is a Boolean algebra exactly when $a \sqcup \neg a = \top$ for each $a$. The law of excluded middle is the difference between the two.

::: mathlib
`compl_compl` · `Mathlib.Order.BooleanAlgebra.Basic`

This is part 1 of the laws, a `simp` lemma. De Morgan is `compl_sup` and `compl_inf`, and part 4 is `compl_le_compl_iff_le`. Many of these lemmas are stated for Heyting algebras when they hold there.

<?decl compl_compl?>
:::

### Examples

**Example (Distributivity in Mathlib).** In a distributive lattice, `inf_sup_left` is law 1.

<?lean MathlibHandbook/V04/C03/Examples.lean#distrib?>

**Example (The sets of a type).** The subsets of a set $X$ form a Boolean algebra with $s^c = X \setminus s$. Law 1 holds: $x \in s \cap (t \cup u)$ means $x \in s$ and ($x \in t$ or $x \in u$), and this is ($x \in s$ and $x \in t$) or ($x \in s$ and $x \in u$). Also $s \cap s^c = \emptyset$ and $s \cup s^c = X$, and $s \Rightarrow t = s^c \cup t$. In Mathlib the instance is `Set.instBooleanAlgebra`, and `Pi.instBooleanAlgebra` covers functions into a Boolean algebra.

**Example (The propositions).** In classical logic the propositions form a Boolean algebra, with $\lor$, $\land$, $\neg$, false and true. The complement axiom $p \lor \neg p$ is the law of excluded middle, and Mathlib has `Prop.instBooleanAlgebra`. The type `Bool` is the smallest nontrivial Boolean algebra.

**Counterexample (The pentagon is not distributive).** In $N_5 = \{0, a, b, c, 1\}$ of Section 1, with $0 < a < c < 1$ and $b$ not comparable to $a$ and $c$:
$$c \sqcap (a \sqcup b) = c \sqcap 1 = c, \qquad (c \sqcap a) \sqcup (c \sqcap b) = a \sqcup 0 = a.$$
Since $a \ne c$, law 1 fails. The modular law fails too: $a \le c$, but $a \sqcup (b \sqcap c) = a$ and $(a \sqcup b) \sqcap c = c$. The element $b$ has the two complements $a$ and $c$.

**Counterexample (The diamond is not distributive).** In $M_3 = \{0, x, y, z, 1\}$:
$$x \sqcap (y \sqcup z) = x \sqcap 1 = x, \qquad (x \sqcap y) \sqcup (x \sqcap z) = 0 \sqcup 0 = 0.$$
So law 1 fails, and $x$ has the two complements $y$ and $z$, but $M_3$ is modular (Exercise 6). The subspaces of $\mathbb{R}^2$ contain a copy of $M_3$: three distinct lines through $0$. A theorem of Birkhoff, not proved here, says that a lattice is distributive if and only if it has no sublattice isomorphic to $N_5$ or $M_3$.

**Example (A Heyting algebra that is not Boolean).** The open subsets of $\mathbb{R}$ form a Heyting algebra, with $\cup$, $\cap$ and $U \Rightarrow V$ the interior of $U^c \cup V$: an open $W$ satisfies $U \cap W \subseteq V$ if and only if $W \subseteq U^c \cup V$, if and only if $W$ is inside the interior of this set. For $U = (0, \infty)$, $\neg U$ is the interior of $(-\infty, 0]$, that is $(-\infty, 0)$. Then $U \sqcup \neg U = \mathbb{R} \setminus \{0\} \ne \mathbb{R}$, so this Heyting algebra is not Boolean.

### The library around it

The lemmas of a distributive lattice are `inf_sup_left`, `inf_sup_right`, `sup_inf_left` and `sup_inf_right`. Each linear order is a distributive lattice by `instDistribLatticeOfLinearOrder`, so `min` distributes over `max` on `ℝ`. `Disjoint` has the API `Disjoint.symm`, `Disjoint.mono` and `disjoint_iff`, used for sets, subspaces and filters alike.

For a Boolean algebra the API has the families `compl_*`, `sdiff_*` and `himp_*`, with `sdiff_eq` and `himp_eq`. The class `GeneralizedBooleanAlgebra` is a Boolean algebra without `⊤`; the finite sets of a type are an instance. The Heyting algebras are in `Mathlib.Order.Heyting.Basic`.

The module `Mathlib.Order.Disjointed` makes a sequence pairwise disjoint and keeps its partial suprema. For $f : \iota \to \alpha$ with values in a generalized Boolean algebra, `disjointed f i` is $f(i) \setminus \bigsqcup_{j < i} f(j)$, by `disjointed_apply`. The main facts are `disjointed_le`, `disjoint_disjointed`, `partialSups_disjointed` and `disjointed_unique`. For sets, the lemmas `iUnion_disjointed` and `disjointed_eq_inter_compl` give the union and an explicit formula. On $\mathbb{N}$, the lemmas `disjointed_zero` and `disjointed_succ` compute the first terms, and measure theory uses this construction to write a countable union as a disjoint union.

The module `Mathlib.Order.SymmDiff` defines the symmetric difference `symmDiff a b`, with the notation `a ∆ b`, by `symmDiff_def`: $a \mathbin{\Delta} b = (a \setminus b) \sqcup (b \setminus a)$. The dual notion is `bihimp a b`, with the notation `a ⇔ b`, and `bihimp_def` gives $(b \Rightarrow a) \sqcap (a \Rightarrow b)$. On `Prop`, `symmDiff_eq_xor` says that the symmetric difference is the exclusive or, and on sets it is the usual symmetric difference. The lemmas need different classes. In a generalized co-Heyting algebra, `symmDiff_eq_sup_sdiff_inf` gives $(a \sqcup b) \setminus (a \sqcap b)$, `symmDiff_self` gives $a \mathbin{\Delta} a = \bot$, `symmDiff_eq_bot` says $a \mathbin{\Delta} b = \bot$ if and only if $a = b$, and `symmDiff_triangle` is the triangle inequality $a \mathbin{\Delta} c \le (a \mathbin{\Delta} b) \sqcup (b \mathbin{\Delta} c)$. In a generalized Boolean algebra the operation is associative, `symmDiff_assoc`, and $\sqcap$ distributes over it, `inf_symmDiff_distrib_left`. So a Boolean algebra is a Boolean ring with $\Delta$ as addition and $\sqcap$ as multiplication. The cancellation `symmDiff_symmDiff_cancel_left` gives $a \mathbin{\Delta} (a \mathbin{\Delta} b) = b$, and `compl_symmDiff` says $(a \mathbin{\Delta} b)^c = a \Leftrightarrow b$. The lemmas for `bihimp` are the duals, with the same names in which `symmDiff` becomes `bihimp`.

### Exercises

1. (A) Check the distributive law $a \sqcap (b \sqcup c) = (a \sqcap b) \sqcup (a \sqcap c)$ in $(\mathbb{N}, \mid)$ for $a = 4$, $b = 6$, $c = 10$. *Hint:* the inf is the gcd and the sup is the lcm.
2. (A) Show that in a Boolean algebra $a \setminus b = \bot$ if and only if $a \le b$. *Hint:* use part 5 of the laws with $b^c$ in place of $b$.
3. (B) Show that in a distributive lattice the cancellation law holds: $a \sqcap b = a \sqcap c$ and $a \sqcup b = a \sqcup c$ give $b = c$. Use it to give a second proof of the uniqueness of complements. *Hint:* write $b = b \sqcap (a \sqcup b)$ and distribute.
4. (B) Show that $(\mathbb{N}, \mid)$ is a distributive lattice. *Hint:* compare the exponents of each prime: the gcd takes the minimum and the lcm takes the maximum, and use the theorem on linear orders.
5. (B) Show that the lattice of the divisors of $12$ is distributive but not complemented. Which elements have a complement? *Hint:* the complement of $d$ must satisfy $\gcd(d, e) = 1$ and $\operatorname{lcm}(d, e) = 12$.
6. (B) Show that $M_3$ is modular. *Hint:* in $a \le c$, the cases $a = 0$, $c = 1$ and $a = c$ are quick, and there are no other cases.
7. (B) In a Heyting algebra, prove $a \le \neg \neg a$ and $\neg a = \neg \neg \neg a$. *Hint:* $a \sqcap \neg a \le \bot$, and $x \mapsto \neg x$ reverses the order.
8. (C) Show that each finite Boolean algebra $B$ is isomorphic to the Boolean algebra of the subsets of the set of its atoms, the elements just above $\bot$. Conclude that $B$ has $2^n$ elements. *Hint:* map $b$ to the set of atoms below $b$, and show that each element is the sup of the atoms below it.

### Notes and history

Boole introduced the algebra of logic in *The Laws of Thought* (1854). Peirce claimed that the distributive law follows from the other laws of a lattice, and Schröder showed that it does not. Dedekind found the modular law in the lattices of ideals and of modules. Stone proved in 1936 that each Boolean algebra is isomorphic to an algebra of sets, which extends Exercise 8 to the infinite case. A reference is Davey and Priestley, *Introduction to Lattices and Order*, Chapters 4 and 7.

In Mathlib the hierarchy was reworked so that a Boolean algebra is a Heyting algebra by an instance, and many lemmas about complements moved to Heyting algebras.

### Reference

<?reference?>
