---
title: Lattices and bounded lattices
kind: theory
modules:
  - Mathlib.Order.Defs.Lattice
  - Mathlib.Order.Lattice
  - Mathlib.Order.BoundedOrder.Basic
  - Mathlib.Order.BoundedOrder.Lattice
  - Mathlib.Order.Copy
  - Mathlib.Order.MinMax
  - Mathlib.Order.Notation
explains:
  E3: [Lattice, Lattice.mk']
  E2: [SemilatticeSup, SemilatticeInf, sup_le_iff, le_inf_iff, BoundedOrder, le_top, bot_le, sup_assoc, sup_idem, sup_inf_self, sup_eq_right]
  E1: [sup_le, le_sup_left, le_sup_right, inf_le_left, inf_le_right, le_inf, sup_comm, inf_comm, inf_assoc, inf_idem, inf_sup_self, inf_eq_left, sup_le_sup, inf_le_inf, OrderTop, OrderBot, LinearOrder.toLattice, SemilatticeSup.mk']
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

## Lattices and bounded lattices

### Overview

In a partial order, two elements need not have a least upper bound. In the integers it is the larger of the two, and in the subsets of a set it is the union. A lattice is a partial order in which each pair of elements has a least upper bound and a greatest lower bound.

A lattice can be defined from the order, or from two operations $\sqcup$ and $\sqcap$ with the laws of commutativity, associativity and absorption. The main theorem of this section says that the two ways give the same structures. Mathlib takes the first way. The section also defines bounded lattices and describes $N_5$ and $M_3$.

### Definitions

Let $P$ be a partial order. A least upper bound of $a, b \in P$ is an upper bound below each upper bound. By antisymmetry it is unique when it exists.

**Definition (Join semilattice).** A join semilattice is a partial order $P$ with a binary operation $\sqcup$, the sup or join, such that for all $a, b, c \in P$:

1. $a \le a \sqcup b$ and $b \le a \sqcup b$;
2. if $a \le c$ and $b \le c$, then $a \sqcup b \le c$.

So $a \sqcup b$ is the least upper bound of $a$ and $b$.

**Definition (Meet semilattice).** A meet semilattice is a partial order $P$ with a binary operation $\sqcap$, the inf or meet, such that $a \sqcap b \le a$, $a \sqcap b \le b$, and $c \le a$ and $c \le b$ give $c \le a \sqcap b$. So $a \sqcap b$ is the greatest lower bound of $a$ and $b$.

**Definition (Lattice).** A lattice is a partial order that is a join semilattice and a meet semilattice for the same order.

*Remarks.* The operation $\sqcup$ is fixed by the order, because the least upper bound is unique. Mathlib uses an operation because a function is easier to use than an existence statement. Many books write $\vee$ and $\wedge$ for $\sqcup$ and $\sqcap$.

The order dual of a lattice, with $a \le^{\mathrm{op}} b$ if and only if $b \le a$, is a lattice in which $\sqcup$ and $\sqcap$ change places. So each theorem about lattices has a dual theorem.

**Definition (Bounded order).** A partial order has a bottom element $\bot$ if $\bot \le a$ for each $a$, and a top element $\top$ if $a \le \top$ for each $a$. A bounded order has both. A bounded lattice is a lattice that is a bounded order.

*Remarks.* The bottom element is unique, and it is the least upper bound of the empty set. So in a bounded lattice each finite set has a supremum and an infimum.

::: mathlib
`Lattice` · `Mathlib.Order.Defs.Lattice`

The class `SemilatticeSup α` extends `PartialOrder α` and `Max α`, so `a ⊔ b` is notation for `max a b`. Its fields `le_sup_left`, `le_sup_right` and `sup_le` are the axioms 1 and 2 above. The class `SemilatticeInf α` is the same with `Min α`, and `Lattice α` extends both.

<?decl Lattice?>
:::

::: mathlib
`BoundedOrder` · `Mathlib.Order.BoundedOrder.Basic`

The class `OrderBot α` has `⊥` and `bot_le : ∀ a, ⊥ ≤ a`, and `OrderTop α` has `⊤` and `le_top`. The class `BoundedOrder α` extends both and needs only `LE α`. A bounded lattice is the pair of instances `[Lattice α] [BoundedOrder α]`.

<?decl BoundedOrder?>
:::

### Theorems and proofs

**Theorem (Universal property of the sup).** In a join semilattice, $a \sqcup b \le c$ if and only if $a \le c$ and $b \le c$. Dually, in a meet semilattice, $c \le a \sqcap b$ if and only if $c \le a$ and $c \le b$.

*Proof.* Suppose $a \sqcup b \le c$. The axiom gives $a \le a \sqcup b$, so $a \le c$ by transitivity. In the same way $b \le a \sqcup b \le c$. Conversely, if $a \le c$ and $b \le c$, then the second axiom gives $a \sqcup b \le c$. The statement for $\sqcap$ is the same statement in the dual order. $\square$

::: mathlib
`sup_le_iff` · `Mathlib.Order.Defs.Lattice`

The lemma is a `simp` lemma. So `simp` splits a goal `a ⊔ b ≤ c` into the two goals `a ≤ c` and `b ≤ c`. The dual lemma is `le_inf_iff`.

<?decl sup_le_iff?>
:::

Each law of the next theorem has a proof by antisymmetry and the universal property.

**Theorem (The laws of a lattice).** In a lattice, for all $a, b, c$:

1. (idempotence) $a \sqcup a = a$ and $a \sqcap a = a$;
2. (commutativity) $a \sqcup b = b \sqcup a$ and $a \sqcap b = b \sqcap a$;
3. (associativity) $(a \sqcup b) \sqcup c = a \sqcup (b \sqcup c)$ and $(a \sqcap b) \sqcap c = a \sqcap (b \sqcap c)$;
4. (absorption) $a \sqcup (a \sqcap b) = a$ and $a \sqcap (a \sqcup b) = a$;
5. (consistency) $a \le b$ if and only if $a \sqcup b = b$, if and only if $a \sqcap b = a$.

*Proof.* The laws for $\sqcap$ are the laws for $\sqcup$ in the dual order, so it is sufficient to prove the laws for $\sqcup$, and the second half of 4 and 5.

1. The axiom gives $a \le a \sqcup a$. Also $a \le a$ and $a \le a$, so the universal property gives $a \sqcup a \le a$. By antisymmetry $a \sqcup a = a$.

2. The axioms give $a \le b \sqcup a$ and $b \le b \sqcup a$. By the universal property $a \sqcup b \le b \sqcup a$. The same argument with $a$ and $b$ exchanged gives $b \sqcup a \le a \sqcup b$. By antisymmetry the two are equal.

3. Let $x = (a \sqcup b) \sqcup c$ and $y = a \sqcup (b \sqcup c)$. By the universal property, applied two times, $x \le d$ holds if and only if $a \le d$, $b \le d$ and $c \le d$. The same is true for $y$. Take $d = y$: since $y \le y$, the three inequalities $a \le y$, $b \le y$, $c \le y$ hold, so $x \le y$. Take $d = x$ in the same way to get $y \le x$. Thus $x = y$.

4. The axiom gives $a \le a \sqcup (a \sqcap b)$. Also $a \le a$ and $a \sqcap b \le a$, so $a \sqcup (a \sqcap b) \le a$. Thus $a \sqcup (a \sqcap b) = a$. For the second law, $a \sqcap (a \sqcup b) \le a$ is an axiom, and $a \le a$ and $a \le a \sqcup b$ give $a \le a \sqcap (a \sqcup b)$.

5. Suppose $a \le b$. Then $a \le b$ and $b \le b$ give $a \sqcup b \le b$, and $b \le a \sqcup b$ is an axiom, so $a \sqcup b = b$. Conversely, if $a \sqcup b = b$, then $a \le a \sqcup b = b$. The equivalence of $a \le b$ and $a \sqcap b = a$ is the dual statement. $\square$

The converse is the main theorem: the laws 2, 3 and 4 alone determine a lattice.

**Theorem (Lattices as algebras).** Let $L$ be a set with two binary operations $\sqcup$ and $\sqcap$ that are commutative and associative and that satisfy the two absorption laws $a \sqcup (a \sqcap b) = a$ and $a \sqcap (a \sqcup b) = a$. Define $a \le b$ to mean $a \sqcup b = b$. Then $\le$ is a partial order on $L$, the lattice operations of this order are $\sqcup$ and $\sqcap$, and $a \le b$ holds if and only if $a \sqcap b = a$.

*Proof.* The proof has five steps: idempotence, the second form of $\le$, the axioms of a partial order, the sup, and the inf.

*Step 1: idempotence.* The second absorption law with $b = a$ gives $a \sqcap (a \sqcup a) = a$. The first absorption law with $b = a \sqcup a$ gives $a \sqcup (a \sqcap (a \sqcup a)) = a$. Put the first equation into the second: $a \sqcup a = a$. The same argument with the roles of the two operations exchanged gives $a \sqcap a = a$.

*Step 2: the two forms of the order.* Suppose $a \sqcup b = b$. Then $a \sqcap b = a \sqcap (a \sqcup b) = a$ by the second absorption law. Conversely, suppose $a \sqcap b = a$. Then $a \sqcup b = (a \sqcap b) \sqcup b = b \sqcup (b \sqcap a) = b$, by commutativity of both operations and the first absorption law. So $a \sqcup b = b$ if and only if $a \sqcap b = a$.

*Step 3: a partial order.* Reflexivity: $a \sqcup a = a$ by Step 1, so $a \le a$. Antisymmetry: if $a \sqcup b = b$ and $b \sqcup a = a$, then $a = b \sqcup a = a \sqcup b = b$ by commutativity. Transitivity: if $a \sqcup b = b$ and $b \sqcup c = c$, then $a \sqcup c = a \sqcup (b \sqcup c) = (a \sqcup b) \sqcup c = b \sqcup c = c$ by associativity, so $a \le c$.

*Step 4: the sup.* First, $a \le a \sqcup b$, because $a \sqcup (a \sqcup b) = (a \sqcup a) \sqcup b = a \sqcup b$ by associativity and Step 1. In the same way $b \sqcup (a \sqcup b) = a \sqcup (b \sqcup b) = a \sqcup b$, after commutativity and associativity, so $b \le a \sqcup b$. Next, suppose $a \le c$ and $b \le c$, that is $a \sqcup c = c$ and $b \sqcup c = c$. Then $(a \sqcup b) \sqcup c = a \sqcup (b \sqcup c) = a \sqcup c = c$, so $a \sqcup b \le c$. Thus $a \sqcup b$ is the least upper bound of $a$ and $b$.

*Step 5: the inf.* By Step 2, $x \le y$ means $x \sqcap y = x$. First, $(a \sqcap b) \sqcap a = a \sqcap (a \sqcap b) = (a \sqcap a) \sqcap b = a \sqcap b$, so $a \sqcap b \le a$. In the same way $a \sqcap b \le b$. Next, suppose $c \le a$ and $c \le b$, that is $c \sqcap a = c$ and $c \sqcap b = c$. Then $c \sqcap (a \sqcap b) = (c \sqcap a) \sqcap b = c \sqcap b = c$, so $c \le a \sqcap b$. Thus $a \sqcap b$ is the greatest lower bound. $\square$

The two constructions are inverse to each other, by part 5 of the previous theorem and by Step 4.

::: mathlib
`Lattice.mk'` · `Mathlib.Order.Lattice`

This definition is the theorem above as a constructor. It takes `Max α`, `Min α` and proofs of the laws, and returns a `Lattice α` whose order is `a ≤ b ↔ a ⊔ b = b`. Use it only for a type with no order yet. The half for one operation is `SemilatticeSup.mk'`.

<?decl Lattice.mk'?>
:::

::: mathlib
`sup_eq_right` · `Mathlib.Order.Defs.Lattice`

This lemma is part 5 of the laws: `a ⊔ b = b ↔ a ≤ b`, with the twins `sup_eq_left`, `inf_eq_left` and `inf_eq_right`. The laws 1 to 4 are `sup_idem`, `sup_comm`, `sup_assoc` and `sup_inf_self`, and their duals.

<?decl sup_eq_right?>
:::

**Theorem (Monotonicity of the operations).** In a lattice, $a \le b$ and $c \le d$ give $a \sqcup c \le b \sqcup d$ and $a \sqcap c \le b \sqcap d$.

*Proof.* From $a \le b \le b \sqcup d$ and $c \le d \le b \sqcup d$, the universal property gives $a \sqcup c \le b \sqcup d$. The second statement is the dual. $\square$

### Examples

**Example (The least upper bound).** The axiom `sup_le` gives an upper bound from two inequalities.

<?lean MathlibHandbook/V04/C03/Examples.lean#sup_le?>

**Example (The greatest lower bound).**

<?lean MathlibHandbook/V04/C03/Examples.lean#le_inf_iff?>

**Example (A linear order).** In a linear order, $a \sqcup b = \max(a, b)$ and $a \sqcap b = \min(a, b)$. Indeed, if $a \le b$, then $b$ is an upper bound of $a$ and $b$, and each upper bound is at least $b$, so $b$ is the least upper bound. In $\mathbb{N}$, $3 \sqcup 5 = 5$ and $3 \sqcap 5 = 3$, and `decide` computes both.

<?lean MathlibHandbook/V04/C03/Examples.lean#nat?>

**Example (The lattice of sets).** The subsets of a set $X$ form a bounded lattice with $s \sqcup t = s \cup t$, $s \sqcap t = s \cap t$, $\bot = \emptyset$ and $\top = X$: each set that contains $s$ and $t$ contains $s \cup t$. For example, $\{1, 2\} \sqcup \{2, 3\} = \{1, 2, 3\}$ and $\{1, 2\} \sqcap \{2, 3\} = \{2\}$.

<?lean MathlibHandbook/V04/C03/Examples.lean#set?>

**Example (Divisibility).** Order $\mathbb{N}$ by divisibility. Each common divisor of $m$ and $n$ divides $\gcd(m, n)$, so $m \sqcap n = \gcd(m, n)$, and dually $m \sqcup n = \operatorname{lcm}(m, n)$. For example, $4 \sqcap 6 = 2$ and $4 \sqcup 6 = 12$. Each number divides $0$, so $\bot = 1$ and $\top = 0$. This lattice is not a Mathlib instance on `ℕ`, whose order is the usual one.

**Example (Subspaces).** The subspaces of a vector space form a bounded lattice with $U \sqcap W = U \cap W$. The union of the two axes of $\mathbb{R}^2$ is not a subspace, since it does not contain $(1, 1)$. The least subspace that contains $U$ and $W$ is $U + W$, so $U \sqcup W = U + W$.

**Example (Bounds).**

<?lean MathlibHandbook/V04/C03/Examples.lean#bounded?>

**Example (The pentagon $N_5$).** Let $N_5 = \{0, a, b, c, 1\}$ with $0 < a < c < 1$ and $0 < b < 1$, and with $b$ not comparable to $a$ and $c$. The only upper bound of $a$ and $b$ is $1$, so $a \sqcup b = 1$. The only lower bound of $c$ and $b$ is $0$, so $c \sqcap b = 0$. Each pair has a sup and an inf, so $N_5$ is a lattice.

**Example (The diamond $M_3$).** Let $M_3 = \{0, x, y, z, 1\}$ with $0 < x, y, z < 1$ and $x$, $y$, $z$ pairwise not comparable. Any two of $x$, $y$, $z$ have sup $1$ and inf $0$. Section 2 shows that $N_5$ and $M_3$ are not distributive.

**Counterexample (A partial order that is not a lattice).** Let $P = \{a, b, c, d\}$ with $a < c$, $a < d$, $b < c$, $b < d$, and no other strict relations. The upper bounds of $a$ and $b$ are $c$ and $d$. Neither is below the other, so $a$ and $b$ have no least upper bound, and $P$ is not a lattice.

### The library around it

The lemmas come in dual pairs, with `sup` and `inf` exchanged and `le` moved: `le_sup_left` and `inf_le_left`, `sup_le` and `le_inf`, `sup_le_iff` and `le_inf_iff`. The monotonicity lemmas are `sup_le_sup` and `inf_le_inf`. In a bounded order there are `bot_le`, `le_top`, `sup_bot_eq` and `inf_top_eq`.

Each linear order is a lattice by `LinearOrder.toLattice`. The sets, the subgroups, the submodules and the filters are lattices by instances. For sets, the simp normal form uses `∪` and `∩`.

The module `Mathlib.Order.BoundedOrder.Lattice` holds the rules that mix the bounds with $\sqcup$ and $\sqcap$. Besides `sup_bot_eq` and `inf_top_eq`, it has `sup_eq_bot_iff`, which says $a \sqcup b = \bot$ if and only if $a = \bot$ and $b = \bot$, and its dual `inf_eq_top_iff`. In a linear order the same facts are stated for `max` and `min`, with an "or" for the other side: `min_eq_bot` says $\min(a, b) = \bot$ if and only if $a = \bot$ or $b = \bot$, and `max_eq_top` is its dual, with `min_ne_bot` and `max_ne_top` as the forms with $\ne$. The module also has the induction principle `WellFoundedLT.induction_bot`: in a well-founded order with a bottom, a property that holds somewhere and can always be moved strictly down from an element other than $\bot$ holds at $\bot$. The dual is `WellFoundedGT.induction_top`.

The module `Mathlib.Order.Copy` has one definition for each order structure, such as `Lattice.copy`, `DistribLattice.copy`, `BoundedOrder.copy`, `CompleteLattice.copy` and `HeytingAlgebra.copy`. Each takes a structure, new operations and proofs that the new operations are equal to the old ones, and returns the same structure with the new operations as its fields. It is used to build an instance whose operations unfold to a chosen formula, for example the intersection of sets in place of a general infimum.

The module `Mathlib.Order.Notation` declares the notation classes that the lattice chapters use: `Top` and `Bot` for $\top$ and $\bot$, `Compl` for $a^c$, `HImp` for the implication $a \Rightarrow b$, and `HNot` for the co-Heyting negation. A class of this kind holds only the symbol and no law, so the laws come from the order classes that extend it. The lemmas `top_nonempty` and `bot_nonempty` say that a type with a top or a bottom element is not empty. The module also fixes the printing of $\sqcup$ and $\sqcap$: in a linear order, `max a b` and `a ⊔ b` are the same term, and the delaborator prints `max` there.

The module `Mathlib.Order.MinMax` holds the lemmas on `max` and `min` in a linear order. Since a linear order is a lattice with $\max = \sqcup$, most of them are lattice lemmas in the special case, but some use the linear order. `max_choice` and `min_choice` say that $\max(a, b)$ is $a$ or $b$, and `max_cases` and `min_cases` add the inequality that decides the case, so a proof can split on them. The characterizations `max_eq_left_iff`, `min_eq_right_iff`, `max_eq_iff` and `min_eq_iff` decide when the maximum is a given value. The order lemmas `le_max_of_le_left`, `lt_max_of_lt_left`, `max_le_max` and `max_lt_max`, and their duals for `min`, compare two maxima. `min_lt_max` says $\min(a, b) < \max(a, b)$ if and only if $a \ne b$. The distributive laws `max_min_distrib_left` and `min_max_distrib_left` hold because a linear order is a distributive lattice. For maps, `Monotone.map_max` gives $f(\max(a, b)) = \max(f(a), f(b))$ for a monotone $f$, and `Antitone.map_max` gives $\min(f(a), f(b))$ for an antitone $f$; the forms on a set are `MonotoneOn.map_max` and its relatives.

### Exercises

1. (A) Give the sup and the inf of $\{1, 2\}$ and $\{2, 3\}$ in the lattice of the subsets of $\mathbb{N}$, and of $4$ and $6$ in $\mathbb{N}$ with the usual order. *Hint:* in a linear order the sup is the maximum.
2. (A) In $(\mathbb{N}, \mid)$, compute $12 \sqcup 18$, $12 \sqcap 18$ and $12 \sqcup 0$. *Hint:* use the gcd and the lcm, and $0$ is the top element.
3. (A) Draw the lattice of the divisors of $12$ ordered by divisibility. Find the elements that are directly above $1$, with no element in between. *Hint:* there are six divisors.
4. (B) Prove the dual absorption law $a \sqcap (a \sqcup b) = a$ directly from the axioms, without the order dual. *Hint:* show two inequalities.
5. (B) Prove that a finite lattice is a bounded lattice. *Hint:* take the sup of all elements, by induction on the number of elements.
6. (B) Let $L$ be a lattice and let $a \le b$. Show that the interval $[a, b] = \{x \mid a \le x \le b\}$ is a lattice with the operations of $L$, and that it is bounded. *Hint:* check that $x \sqcup y$ and $x \sqcap y$ stay in $[a, b]$.
7. (C) Find all lattices with five elements, up to isomorphism. *Hint:* there are five of them.
8. (L) Prove that $a \sqcup b = b \sqcup a$. The solution is `sup_comm_example`.
9. (L) Prove that $a \sqcap b \le a \sqcup b$. The solution is `inf_le_sup_example`.
10. (L) Prove the absorption law $a \sqcup a \sqcap b = a$. The solution is `sup_inf_absorb_example`.

### Notes and history

Peirce and Schröder used the operations of a lattice in their algebra of logic in the 1880s. Dedekind studied lattices in 1897 under the name *Dualgruppe*. Birkhoff made the theory a field of algebra with *Lattice Theory* (1940). A modern text is Davey and Priestley, *Introduction to Lattices and Order*, Chapter 2.

Mathlib defines a lattice from the order, because most lattices come with an order first, and a linear order must be a lattice with its own `≤`.

### Reference

<?reference?>
