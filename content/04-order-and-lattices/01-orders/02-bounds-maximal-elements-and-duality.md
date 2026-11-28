---
title: Bounds, maximal elements and duality
kind: theory
modules:
  - Mathlib.Order.Bounds.Defs
  - Mathlib.Order.Max
  - Mathlib.Order.Bounds.Basic
  - Mathlib.Order.Bounds.Image
  - Mathlib.Order.Bounds.Lattice
  - Mathlib.Order.Bounds.OrderIso
  - Mathlib.Order.Nat
  - Mathlib.Order.OrderDual
explains:
  E3: [IsLUB, upperBounds, IsGreatest, IsMax, OrderDual]
  E2: [IsGLB, IsLeast, lowerBounds, BddAbove, BddBelow, Maximal, IsTop, IsLUB.unique, isLUB_le_iff, IsGreatest.isLUB, IsGreatest.maximal, maximal_iff, IsMax.not_lt, NoMaxOrder]
  E1: auto
families: []
requires: [V01]
reads_with: ["MIL", "TPIL"]
lean:
  - MathlibHandbook/V04/C01/Examples.lean
  - MathlibHandbook/V04/C01/Exercises.lean
  - MathlibHandbook/V04/C01/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Bounds, maximal elements and duality

### Overview

The completeness of the real numbers, the existence of a maximal ideal and the supremum in a lattice all speak of bounds. This section gives the vocabulary of bounds in an arbitrary preorder: an upper bound of a set, a greatest element, a least upper bound, and a maximal element. A greatest element is an upper bound that lies in the set. A least upper bound need not lie in the set. A maximal element has nothing strictly above it in the set, but it need not be above the other elements.

The second subject is duality. Each notion of this section has a twin with the order reversed: lower bound, least element, greatest lower bound, minimal element. The dual order of a preorder is again a preorder, so each theorem about upper bounds gives a theorem about lower bounds with no new proof.

The main results are: a least upper bound is unique in a partial order; a greatest element is a least upper bound and a maximal element; and in a linear order a maximal element is a greatest element.

### Definitions

In this part, $\alpha$ is a preorder and $S \subseteq \alpha$ is a subset.

**Definition (Upper bound).** An element $a \in \alpha$ is an upper bound of $S$ if $x \le a$ for each $x \in S$. The set of the upper bounds of $S$ is $\operatorname{upperBounds}(S)$. The set $S$ is bounded above if it has at least one upper bound. Lower bounds, $\operatorname{lowerBounds}(S)$ and bounded below are defined in the same way with $a \le x$.

An upper bound is an element of $\alpha$, not of $S$. The empty set has each element of $\alpha$ as an upper bound, because the condition "$x \le a$ for each $x \in \emptyset$" holds for each $a$. So $\operatorname{upperBounds}(\emptyset) = \alpha$.

::: mathlib
`upperBounds` · `Mathlib.Order.Bounds.Defs`

The definition is `upperBounds s = { x | ∀ ⦃a⦄, a ∈ s → a ≤ x }`. It is a set, not a predicate, so `a ∈ upperBounds s` is the statement "a is an upper bound of s", and the lemma `mem_upperBounds` unfolds it. `BddAbove s` is `(upperBounds s).Nonempty`. Mathlib needs only `LE α` for the definitions, but most lemmas ask for a preorder.

<?decl upperBounds?>
:::

**Definition (Greatest and least element).** An element $a$ is a greatest element of $S$ if $a \in S$ and $a$ is an upper bound of $S$. An element $a$ is a least element of $S$ if $a \in S$ and $a$ is a lower bound of $S$. An element $a$ of $\alpha$ is a top element if it is a greatest element of $\alpha$, that is, $x \le a$ for each $x \in \alpha$.

::: mathlib
`IsGreatest` · `Mathlib.Order.Bounds.Defs`

`IsGreatest s a` is the conjunction `a ∈ s ∧ a ∈ upperBounds s`. So `h.1` is the membership and `h.2` is the bound. `IsLeast s a` is the dual. For the whole type, `IsTop a` says `∀ b, b ≤ a`. The class `OrderTop α` of the chapter on lattices gives a chosen top element `⊤` as data.

<?decl IsGreatest?>
:::

**Definition (Least upper bound).** An element $a$ is a least upper bound, or supremum, of $S$ if $a$ is a least element of $\operatorname{upperBounds}(S)$. That is, $a$ is an upper bound of $S$, and $a \le b$ for each upper bound $b$ of $S$. A greatest lower bound, or infimum, is a greatest element of $\operatorname{lowerBounds}(S)$.

The chapters on lattices make the supremum an operation $\sup$, when each set of a certain kind has one. Here the supremum is a property of an element: "$a$ is a least upper bound of $S$".

::: mathlib
`IsLUB` · `Mathlib.Order.Bounds.Defs`

The definition is `IsLUB s a = IsLeast (upperBounds s) a`, literally the definition of the text. `IsGLB s a = IsGreatest (lowerBounds s) a`. The predicate form is the base of the supremum in each later chapter: the lemma `IsLUB.sSup_eq` of a complete lattice and the lemma `isLUB_csSup` of the real numbers both say that an operation gives an element with this property.

<?decl IsLUB?>
:::

**Definition (Maximal element).** An element $a$ is a maximal element of $S$ if $a \in S$ and, for each $x \in S$, $a \le x$ gives $x \le a$. In a partial order this says: $a \le x$ with $x \in S$ gives $x = a$. An element of $\alpha$ is maximal in $\alpha$ if it is a maximal element of $\alpha$ itself. Minimal elements are the dual notion.

It is an element with no element of $S$ strictly above it. In a preorder this is the same: $a$ is maximal if and only if there is no $x \in S$ with $a < x$, because $a < x$ means $a \le x$ and $\lnot(x \le a)$.

::: mathlib
`IsMax` · `Mathlib.Order.Max`

`IsMax a` says `∀ b, a ≤ b → b ≤ a`: maximal in the whole type. For a subset or a predicate, Mathlib uses `Maximal P a`, defined in `Mathlib.Order.Defs.Unbundled` as `P a ∧ ∀ ⦃b⦄, P b → a ≤ b → b ≤ a`. So a maximal element of a set `s` is `Maximal (· ∈ s) a`. The lemma `maximal_iff` gives the form with an equality in a partial order. The class `NoMaxOrder α` says that no element is maximal, and `IsMax.not_lt` says that nothing is strictly above a maximal element. The form with `b ≤ a` and not `b = a` makes the definition correct in a preorder.

<?decl IsMax?>
:::

**Definition (Dual order).** Let $\alpha$ be a preorder. The dual order $\alpha^{\mathrm{op}}$ is the same set with the relation $a \le^{\mathrm{op}} b$ if and only if $b \le a$.

The dual relation is a preorder: $a \le a$ holds, and $b \le a$ and $c \le b$ give $c \le a$. It is a partial order or a linear order when $\alpha$ is one. The upper bounds of $S$ in $\alpha^{\mathrm{op}}$ are the lower bounds of $S$ in $\alpha$, and the same holds for greatest and least elements, suprema and infima, maximal and minimal elements.

::: mathlib
`OrderDual` · `Mathlib.Order.OrderDual`

`OrderDual α`, written `αᵒᵈ`, is a type synonym of `α` with the reversed instances. The maps `OrderDual.toDual : α ≃ αᵒᵈ` and `OrderDual.ofDual` change the type without a change of the element, and the lemma `OrderDual.toDual_le_toDual` says `toDual a ≤ toDual b ↔ b ≤ a`. The type synonym is needed because an instance of `LE α` is unique: the reversed order must live on a type with another name.

<?decl OrderDual?>
:::

### Theorems and proofs

**Theorem (Uniqueness of the supremum).** In a partial order, a set has at most one least upper bound and at most one greatest element. In a preorder, two least upper bounds $a$ and $b$ of the same set satisfy $a \le b$ and $b \le a$.

*Proof.* Let $a$ and $b$ be least upper bounds of $S$. Then $b$ is an upper bound of $S$, and $a$ is below each upper bound, so $a \le b$. In the same way, $b \le a$. In a partial order, antisymmetry gives $a = b$. For greatest elements, let $a$ and $b$ be greatest elements of $S$. Then $b \in S$ and $a$ is an upper bound of $S$, so $b \le a$. In the same way $a \le b$, and $a = b$ in a partial order. $\square$

Because of this theorem, a partial order can speak of *the* supremum of a set, when one exists.

**Theorem (Characterization of the supremum).** Let $\alpha$ be a preorder. An element $a$ is a least upper bound of $S$ if and only if, for each $b \in \alpha$, $a \le b \iff b \in \operatorname{upperBounds}(S)$.

*Proof.* Assume that $a$ is a least upper bound. Let $b \in \alpha$. If $b$ is an upper bound, then $a \le b$ by leastness. Conversely, let $a \le b$ and let $x \in S$. Then $x \le a$ because $a$ is an upper bound, and $x \le b$ by transitivity. So $b$ is an upper bound.

Now assume the equivalence for each $b$. Put $b = a$. Since $a \le a$, the element $a$ is an upper bound. If $b$ is an upper bound, the equivalence gives $a \le b$. So $a$ is least among the upper bounds. $\square$

**Theorem (Greatest elements are suprema and maximal).** Let $\alpha$ be a preorder and let $a$ be a greatest element of $S$. Then $a$ is a least upper bound of $S$, and $a$ is a maximal element of $S$.

*Proof.* The element $a$ is an upper bound by definition. Let $b$ be an upper bound of $S$. Since $a \in S$, the bound gives $a \le b$. So $a$ is a least upper bound. For maximality, $a \in S$, and if $x \in S$ with $a \le x$, then $x \le a$ because $a$ is an upper bound. $\square$

**Theorem (Maximal elements in a linear order).** Let $\alpha$ be a linear order and let $a$ be a maximal element of $S$. Then $a$ is a greatest element of $S$. In particular, $S$ has at most one maximal element.

*Proof.* Let $x \in S$. By totality, $x \le a$ or $a \le x$. In the first case the claim holds. In the second case, maximality gives $x \le a$. So $a$ is an upper bound of $S$, and $a \in S$. The last claim follows from the uniqueness of the greatest element. $\square$

The converse statements fail in general. A least upper bound need not be in $S$, so it need not be greatest. A maximal element need not be greatest when the order is not linear.

**Theorem (Duality principle).** Let $\Phi$ be a statement about a preorder that uses only $\le$ and the logical connectives, and let $\Phi^{\mathrm{op}}$ be the statement with each $a \le b$ replaced by $b \le a$. If $\Phi$ holds in each preorder, then $\Phi^{\mathrm{op}}$ holds in each preorder. The same holds for partial orders and for linear orders.

*Proof.* Let $\alpha$ be a preorder. Its dual $\alpha^{\mathrm{op}}$ is a preorder, so $\Phi$ holds in $\alpha^{\mathrm{op}}$. A statement $a \le^{\mathrm{op}} b$ in $\alpha^{\mathrm{op}}$ is by definition the statement $b \le a$ in $\alpha$. So $\Phi$ in $\alpha^{\mathrm{op}}$ is word for word $\Phi^{\mathrm{op}}$ in $\alpha$. For partial and linear orders, use that the dual of a partial order is a partial order and the dual of a linear order is a linear order. $\square$

::: mathlib
`IsLUB.unique` · `Mathlib.Order.Bounds.Basic`

The uniqueness needs a partial order, and Mathlib asks for `PartialOrder α`. The characterization is `isLUB_iff_le_iff`, and its useful half is `isLUB_le_iff : IsLUB s a → (a ≤ b ↔ b ∈ upperBounds s)`. The theorem on greatest elements is `IsGreatest.isLUB` and `IsGreatest.maximal`.

<?decl IsLUB.unique?>
:::

### Examples

**Example (An open interval).** In $\mathbb{R}$, let $S = (0, 1) = \{x : 0 < x < 1\}$. The upper bounds of $S$ are the numbers $b \ge 1$. Indeed, each $b \ge 1$ is an upper bound. If $b < 1$, then either $b \le 0$, and $1/2 \in S$ is above $b$, or $0 < b < 1$, and $(b+1)/2$ lies in $S$ and is above $b$. So the least upper bound is $1$. It is not in $S$, so $S$ has no greatest element, and no maximal element: for $x \in S$ the number $(x+1)/2$ is in $S$ and strictly above $x$.

**Example (A set of rationals with no supremum).** In $\mathbb{Q}$, let $S = \{x \in \mathbb{Q} : x^2 < 2\}$. The set is bounded above, for example by $2$: if $x > 2$, then $x^2 > 4$. It has no least upper bound in $\mathbb{Q}$.

*Proof.* Suppose $q \in \mathbb{Q}$ is a least upper bound. Since $1 \in S$, $q \ge 1 > 0$. No rational number has square $2$, so $q^2 < 2$ or $q^2 > 2$. Put
$$r = \frac{2q + 2}{q + 2}.$$
Then $r > 0$, and two computations give
$$r - q = \frac{2 - q^2}{q + 2}, \qquad r^2 - 2 = \frac{4q^2 + 8q + 4 - 2(q^2 + 4q + 4)}{(q+2)^2} = \frac{2(q^2 - 2)}{(q+2)^2}.$$
If $q^2 < 2$, then $r > q$ and $r^2 < 2$. So $r \in S$ is above the upper bound $q$, a contradiction. If $q^2 > 2$, then $r < q$ and $r^2 > 2$. The number $r$ is an upper bound of $S$: if $x \in S$ and $x > r$, then $x > r > 0$ gives $x^2 > r^2 > 2$, which contradicts $x \in S$. So $r$ is an upper bound smaller than $q$, a contradiction. $\square$

In $\mathbb{R}$ the same set has the supremum $\sqrt 2$. This difference between $\mathbb{Q}$ and $\mathbb{R}$ is the subject of the chapter on conditionally complete lattices.

**Example (Divisibility).** In $\mathbb{N}$ with divisibility, the upper bounds of $\{a, b\}$ are the common multiples of $a$ and $b$. The least common multiple $\operatorname{lcm}(a, b)$ is a common multiple, and it divides each common multiple. So it is the least upper bound of $\{a, b\}$. For $\{4, 6\}$: the upper bounds are $12, 24, 36, \dots$ and $0$, and the least upper bound is $12$. It is not in the set, so $\{4, 6\}$ has no greatest element. Now take $S = \{2, 3, \dots, 10\}$. Its maximal elements are $6, 7, 8, 9, 10$: no other element of $S$ is a multiple of one of them, since twice each of them is above $10$. The other elements are not maximal: $2 \mid 4$, $3 \mid 6$, $4 \mid 8$, $5 \mid 10$. There are five maximal elements and no greatest element, which is possible because the order is not linear.

**Counterexample (Maximal without greatest).** Let $P$ be the set of subsets of $\{1, 2, 3\}$ with at most two elements, ordered by inclusion. The sets $\{1,2\}$, $\{1,3\}$ and $\{2,3\}$ are maximal: a set of $P$ that contains one of them has at most two elements, so it is equal to it. None of them is a greatest element, because $\{1,3\} \not\subseteq \{1,2\}$. So $P$ has three maximal elements and no greatest element. This is the usual picture for Zorn's lemma in the next section: it gives a maximal element, not a greatest one.

**Counterexample (No maximal element).** The orders $\mathbb{N}$, $\mathbb{Z}$, $\mathbb{Q}$ and $\mathbb{R}$ have no maximal element, since $n < n + 1$. In Mathlib each of them has an instance of `NoMaxOrder`. The order $\mathbb{N}$ has the least element $0$, which is its unique minimal element. The order $\mathbb{Z}$ has no minimal element.

**Example (The supremum of the empty set).** In a preorder $\alpha$, the upper bounds of $\emptyset$ are all of $\alpha$. So a least upper bound of $\emptyset$ is a least element of $\alpha$. In $\mathbb{N}$ the supremum of $\emptyset$ is $0$. In $\mathbb{Z}$ the empty set has no supremum, because $\mathbb{Z}$ has no least element.

### The library around it

The definitions are in `Mathlib.Order.Bounds.Defs` and `Mathlib.Order.Max`, and the lemmas are in `Mathlib.Order.Bounds.Basic`. The lemmas come in groups of four: a lemma about `upperBounds`, `IsGreatest`, `IsLUB` or `BddAbove` has twins about `lowerBounds`, `IsLeast`, `IsGLB` and `BddBelow`, and the names change by the same rule. The lemmas `upperBounds_empty` and `isLUB_empty` treat the empty set.

The file `Mathlib.Order.Bounds.Basic` has the rules for the set operations. The set of upper bounds reverses inclusion (`upperBounds_mono_set`), `upperBounds_union` says that $\operatorname{upperBounds}(s \cup t) = \operatorname{upperBounds}(s) \cap \operatorname{upperBounds}(t)$, and `upperBounds_singleton` and `upperBounds_insert` treat small sets. A subset of a bounded set is bounded (`BddAbove.mono`), and `BddAbove.union` and `bddAbove_insert` need the class `IsDirectedOrder`, because two upper bounds must have a common upper bound. For intervals, `isLUB_Icc` gives the supremum $b$ of $[a, b]$ when $a \le b$, and `isLUB_Iio` gives the supremum $a$ of $(-\infty, a)$ in a dense linear order. In a semilattice, `isLUB_pair` says that $a \sqcup b$ is the least upper bound of $\{a, b\}$, and `IsLUB.union` and `IsLUB.insert` compute the supremum of a union. In a linear order, `IsLUB.exists_between` says: if $a$ is the supremum of $s$ and $b < a$, then some $c \in s$ satisfies $b < c \le a$. The proof is short. If each $c \in s$ satisfies $c \le b$, then $b$ is an upper bound of $s$, so $a \le b$, which contradicts $b < a$. The file also builds structures from bounds: `SemilatticeSup.ofIsLUB` makes a semilattice from a function that gives the supremum of each pair, and `IsLeast.orderBot` makes a set with a least element into an `OrderBot`.

The file `Mathlib.Order.Bounds.Image` moves bounds along maps. A monotone map sends an upper bound of $s$ to an upper bound of $f(s)$ (`Monotone.mem_upperBounds_image`), so it keeps bounded sets (`Monotone.map_bddAbove`) and greatest elements (`Monotone.map_isGreatest`). An antitone map exchanges the two sides, as in `Antitone.map_bddAbove`, which gives `BddBelow (f '' s)`. For a strictly monotone map on a linear order the implication becomes an equivalence, as in `StrictMono.map_isGreatest`. The lemmas on `Set.image2`, such as `BddAbove.image2` and `IsLeast.image2`, treat a function of two variables that is monotone in each variable, for example the sum of two sets. For products and functions, `bddAbove_prod`, `isLUB_prod` and `bddAbove_pi` reduce to the coordinates. The file `Mathlib.Order.Bounds.Lattice` treats unions of a family: `upperBounds_iUnion` and `isLUB_iUnion_iff_of_isLUB`, and `gc_upperBounds_lowerBounds` states that `upperBounds` and `lowerBounds` form a Galois connection in the sense of Chapter 6. The file `Mathlib.Order.Bounds.OrderIso` has the forms for an isomorphism, which reflects bounds in both directions: `OrderIso.upperBounds_image`, `OrderIso.isLUB_image` and `OrderIso.isLUB_preimage`.

For maximal elements, `Mathlib.Order.Max` has `IsMax`, `IsMin`, `IsTop` and `IsBot` for the whole type,. The file `Mathlib.Order.Minimal` has the API of `Maximal` and `Minimal`.

The module `Mathlib.Order.Nat` gives the first bounds of the natural numbers. The instance `Nat.instOrderBot` makes $0$ the bottom element, and `Nat.bot_eq_zero` states $\bot = 0$. The lemma `Nat.isLeast_find` says that `Nat.find hp` is the least element of $\{n \mid p\,n\}$, and `Set.Nonempty.isLeast_natFind` says the same for a nonempty set of natural numbers.

The module `Mathlib.Order.OrderDual` defines the dual order and its first API. The equivalences `OrderDual.toDual` and `OrderDual.ofDual` are inverse, and `OrderDual.toDual_inj` says that `OrderDual.toDual` is injective. The lemmas `OrderDual.toDual_le_toDual`, `OrderDual.ofDual_le_ofDual` and `OrderDual.toDual_lt_toDual` reverse the order, and `OrderDual.toDual_le` and `OrderDual.le_toDual` move the map to the other side of an inequality. The lemmas `LE.le.dual` and `LE.le.ofDual` apply these to a hypothesis. The lemmas `OrderDual.forall` and `OrderDual.exists` turn a quantifier over the dual into a quantifier over the base type, and `OrderDual.rec` is the matching recursor. The lemmas `OrderDual.Preorder.dual_dual` and `OrderDual.instLinearOrder.dual_dual` say that the dual of the dual is the original instance, by definition. Each class of order properties has a dual instance, for example `OrderDual.denselyOrdered`. The same module transports single operations along an equivalence: `Equiv.top`, `Equiv.bot` and `Equiv.compl` define the operation on $\alpha$ from the operation on $\beta$ through an equivalence $\alpha \simeq \beta$.

### Exercises

1. (A) Find the upper bounds, the least upper bound, the greatest element and the maximal elements of $\{1 - 1/n : n \ge 1\}$ in $\mathbb{R}$. *Hint:* the supremum is not in the set.
2. (A) In the divisors of $36$ with divisibility, find the least upper bound and the greatest lower bound of $\{4, 6\}$ and of $\{9, 12\}$.
3. (A) Show that a top element of a preorder is maximal. Give a preorder with a maximal element that is not a top element.
4. (B) Show that the upper bounds of $S$ and of $\operatorname{lowerBounds}(\operatorname{upperBounds}(S))$ are the same. *Hint:* the inclusion $S \subseteq \operatorname{lowerBounds}(\operatorname{upperBounds}(S))$ is direct.
5. (B) Let $S \subseteq T$. Show that $\operatorname{upperBounds}(T) \subseteq \operatorname{upperBounds}(S)$, and that $\sup S \le \sup T$ when both exist.
6. (B) State the dual of the theorem on greatest elements, and prove it with the duality principle.
7. (B) In a partial order, let $a$ be a maximal element of $S$ that is also an upper bound of $S$. Show that $a$ is the greatest element of $S$ and the unique maximal element.
8. (C) Show that a finite nonempty subset of a partial order has a maximal element. *Hint:* induction on the number of elements, or a longest chain $x_1 < x_2 < \dots$ in the set.
9. (C) Let $\alpha$ be a partial order in which each subset has a least upper bound. Show that each subset also has a greatest lower bound. *Hint:* take the supremum of the lower bounds.

### Notes and history

Dedekind, *Stetigkeit und irrationale Zahlen* (1872), built the reals from cuts of $\mathbb{Q}$, and the set $\{x : x^2 < 2\}$ is his example. The general notions for ordered sets are in Hausdorff (1914). The duality principle for lattices is in Dedekind's work of 1897 and in Birkhoff, *Lattice Theory*, Chapter I.

In Mathlib, the file `Mathlib.Order.Bounds.Basic` comes from the Lean 3 library. The predicate `Maximal` replaced an older form with sets in 2024, so that the same definition serves sets, predicates and subtypes.

### Reference

<?reference?>
