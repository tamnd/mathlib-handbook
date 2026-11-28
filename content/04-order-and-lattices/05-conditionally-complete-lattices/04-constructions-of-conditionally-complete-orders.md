---
title: Constructions of conditionally complete orders
kind: api
modules:
  - Mathlib.Order.ConditionallyCompleteLattice.Finset
  - Mathlib.Order.ConditionallyCompleteLattice.Group
  - Mathlib.Order.ConditionallyCompleteLattice.WithTop
  - Mathlib.Order.ConditionallyCompletePartialOrder.Basic
  - Mathlib.Order.ConditionallyCompletePartialOrder.Defs
  - Mathlib.Order.Int.ConditionallyCompleteOrder
  - Mathlib.Order.Int.LeastGreatest
  - Mathlib.Order.CompleteLatticeIntervals
explains:
  E2: [Int.csSup_mem, Int.exists_least_of_bdd, WithTop.sSup_eq_top_iff, WithTop.iSup_coe_eq_top, Set.OrdConnected.csSup_image_mem, Set.Nonempty.csSup_mem, Set.Finite.map_sSup_of_monotone, ciSup_add_ciSup_le, DirectedOn.isLUB_csSup]
  E1: auto
families: []
requires: [V04.C03, V04.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Constructions of conditionally complete orders

### Overview

Sections 1 and 2 give the general theory of `sSup` and `⨆` in a conditionally complete lattice. This section describes the files that make new conditionally complete orders from old ones, and the files that compute the supremum in special cases. The integers are a conditionally complete linear order, and in $\mathbb{Z}$ the supremum of a nonempty bounded set is its greatest element. If a top element is added to a conditionally complete lattice, the result is again conditionally complete, and in some cases it is complete, as for $\mathbb{N}_\infty = $ `WithTop ℕ`. An interval $[a, b]$ of a conditionally complete lattice is a complete lattice, and an order-connected subset of a conditionally complete linear order is again conditionally complete.

The section also treats finite sets, where the supremum is a maximum, the interaction of `⨆` with a group operation, and the weaker class of conditionally complete partial orders, in which only directed sets need a supremum. The files use the bounds of Chapter 1, the lattices of Chapter 3 and the complete lattices of Chapter 4.

### The library around it

**The integers.** The file `Mathlib.Order.Int.LeastGreatest` proves the well-ordering principle for $\mathbb{Z}$ in two forms. The lemma `Int.exists_least_of_bdd` takes a predicate `P : ℤ → Prop`, a lower bound $b$ for the set of solutions and one solution, and it gives a least solution. It uses classical logic, so it needs no decidability. The function `Int.leastOfBdd` is the computable form: with `[DecidablePred P]` it returns a subtype element that is a solution and is below each solution. The lemma `Int.coe_leastOfBdd_eq` says that the value does not depend on the bound $b$, and `Int.isLeast_coe_leastOfBdd` states the result with `IsLeast`. The dual names are `Int.exists_greatest_of_bdd` and `Int.greatestOfBdd`.

The file `Mathlib.Order.Int.ConditionallyCompleteOrder` uses `Int.greatestOfBdd` to define `sSup` on `Set ℤ` and to give the instance `Int.instConditionallyCompleteLinearOrder`. The junk value is $0$: `Int.csSup_empty` and `Int.csSup_of_not_bddAbove`. When $s$ is decidable and bounded above by $b$, `Int.csSup_eq_greatestOfBdd` computes `sSup s` as the greatest element. The main fact about $\mathbb{Z}$ is that the supremum is attained.

$$s \ne \emptyset,\ s \text{ bounded above} \implies \sup s \in s \qquad (\texttt{Int.csSup\_mem}).$$

*Proof.* Let $P(z)$ be $z \in s$. The set $s$ has an upper bound and an element, so `Int.exists_greatest_of_bdd` gives $m \in s$ with $z \le m$ for each $z \in s$. Then $m$ is the greatest element of $s$, and a greatest element is the least upper bound, so $\sup s = m$ by `IsGreatest.csSup_eq`. Thus $\sup s \in s$. $\square$

The real numbers do not have this property: $\sup\,[0, 1) = 1 \notin [0, 1)$. For $\mathbb{N}$ the same statement is `Nat.sSup_mem`, in a file of Volume 1.

**Adding a top or a bottom element.** The file `Mathlib.Order.ConditionallyCompleteLattice.WithTop` defines `sSup` on `WithTop α` from `sSup` on $\alpha$. The value is $\top$ if $\top \in s$ or if the set of the finite elements of $s$ is not bounded above, and otherwise it is the coercion of the supremum of the finite elements. The lemmas `WithTop.sSup_eq_top_iff` and `WithTop.sSup_eq` state the two cases.

$$\sup s = \top \iff \top \in s \lor \neg\,\operatorname{BddAbove}(\mathrm{coe}^{-1}(s)) \qquad (\texttt{WithTop.sSup\_eq\_top\_iff}).$$

For a family $f : \iota \to \alpha$ the condition is simpler, since no term of the family is $\top$: `WithTop.iSup_coe_eq_top` says that $\bigsqcup_i f(i) = \top$ in `WithTop α` exactly when the range of $f$ is not bounded above, and `WithTop.iSup_coe_lt_top` is the negation. The coercion commutes with the supremum of a bounded set: `WithTop.coe_sSup'` and `WithTop.coe_iSup` need only `BddAbove`, and `WithTop.coe_sSup` writes the result as an indexed supremum of coercions. The lemma `WithTop.isLUB_sSup` says that each set of `WithTop α` has `sSup s` as its least upper bound when α is a `ConditionallyCompleteLinearOrderBot`.

The file then gives several instances. They differ in the hypothesis on α.

| Instance | Hypothesis on α | Result |
|---|---|---|
| `WithTop.conditionallyCompleteLattice` | `ConditionallyCompleteLattice α` | `WithTop α` is conditionally complete |
| `WithTop.instCompleteLinearOrder` | `ConditionallyCompleteLinearOrderBot α` | `WithTop α` is a complete linear order |
| `WithTop.WithBot.completeLattice` | `ConditionallyCompleteLattice α` | `WithTop (WithBot α)` is complete |
| `WithBot.WithTop.completeLattice` | `ConditionallyCompleteLattice α` | `WithBot (WithTop α)` is complete |

The second instance makes $\mathbb{N}_\infty$ and `WithTop ℝ≥0` complete linear orders. The third and the fourth make complete lattices from $\mathbb{Z}$ or $\mathbb{R}$, because the two new elements give a supremum to the empty set and to the unbounded sets. The extended reals are built this way: `EReal` is defined as `WithBot (WithTop ℝ)`. Each `WithTop` lemma has a `WithBot` twin made by the `to_dual` attribute, for example `WithBot.sSup_eq` and `WithBot.coe_sSup'`.

**Intervals and order-connected sets.** A subset $s$ of a conditionally complete lattice α is in general not conditionally complete for the induced order, because the supremum in α of a subset of $s$ can be outside $s$. The file `Mathlib.Order.CompleteLatticeIntervals` gives two ways to avoid this. The first is for intervals. If $a \le b$, then the interval $[a, b]$ is a complete lattice: each subset is bounded by $b$, and the empty set gets the supremum $a$. The instance `Set.Icc.completeLattice` needs the hypothesis $a \le b$ as an instance argument `[Fact (a ≤ b)]`, and `Set.Icc.coe_sSup` says that for a nonempty set the coercion of the supremum is the supremum in α. In a complete lattice, each interval `Set.Iic a` is also a complete lattice, by `Set.Iic.instCompleteLattice`. Chapter 7 describes the intervals themselves.

The second way is for order-connected sets in a linear order. The `abbrev` `subsetConditionallyCompleteLinearOrder` makes a nonempty subset $s$ of a conditionally complete linear order into a conditionally complete linear order, if $s$ contains the supremum of each nonempty subset of $s$ that is bounded above in $s$, and the dual condition for infima. An order-connected set satisfies this condition.

$$t \subseteq s,\ t \ne \emptyset,\ t \text{ bounded above in } s \implies \sup t \in s \qquad (\texttt{Set.OrdConnected.csSup\_image\_mem}).$$

*Proof.* Take $c \in t$ and an upper bound $B \in s$ of $t$. The supremum in α of $t$ satisfies $c \le \sup t$, because $c \in t$, and $\sup t \le B$, because $B$ is an upper bound. Thus $\sup t \in [c, B]$. The endpoints $c$ and $B$ are in $s$, and $s$ is order-connected, so $[c, B] \subseteq s$. $\square$

From this lemma the instance `Set.OrdConnected.conditionallyCompleteLinearOrder` follows; it needs `[Inhabited s]` and `[OrdConnected s]`. The lemma `Set.OrdConnected.coe_sSup` says that the supremum in $s$ agrees with the supremum in α for a nonempty set bounded above. The open interval $(0, 1)$ of $\mathbb{R}$ is an example: it is order-connected, so it is a conditionally complete linear order, but it is not complete. The default element of `Inhabited s` gives the junk value: `Set.OrdConnected.sSup_empty_of_noBotOrder` says that `sSup ∅` is `default` when $s$ has no least element.

**Finite sets.** The file `Mathlib.Order.ConditionallyCompleteLattice.Finset` compares `sSup` with the finite maxima of Volume 1. A finite set is bounded, so the supremum of a nonempty finite set is meaningful, and in a linear order it is the maximum. The lemma `Finset.Nonempty.csSup_eq_max'` says that $\sup s$ is `s.max' h`, and `Set.Nonempty.csSup_mem` says that the supremum of a nonempty finite set is an element of the set. The lemma `Set.Nonempty.isGreatest_csSup` gives the same result with `IsGreatest`. For a lattice that is not linear, `Finset.sup'_eq_csSup_image` connects the folded supremum `Finset.sup'` with `sSup` of the image.

A monotone map commutes with the supremum of a finite set, with no continuity hypothesis.

$$s \text{ finite},\ s \ne \emptyset,\ f \text{ monotone} \implies f(\sup s) = \sup f(s) \qquad (\texttt{Set.Finite.map\_sSup\_of\_monotone}).$$

*Proof.* By `Set.Nonempty.isGreatest_csSup`, $\sup s$ is the greatest element of $s$. A monotone map sends a greatest element of $s$ to a greatest element of $f(s)$. A greatest element is the supremum, so $\sup f(s) = f(\sup s)$. $\square$

For an infinite set this is false: the map $f(x) = 0$ for $x < 1$ and $f(x) = 1$ for $x \ge 1$ is monotone on $\mathbb{R}$, and $f(\sup\,[0, 1)) = 1$ but $\sup f([0, 1)) = 0$. Other lemmas of the file treat families on a finite type: `Finite.ciSup_mem` and `exists_eq_ciSup_of_finite` say that a supremum over a finite nonempty type is a value of the family, and `Finset.ciSup_union` splits a supremum over a union.

**Groups.** The file `Mathlib.Order.ConditionallyCompleteLattice.Group` has a small number of inequalities between `⨆` and a group operation. Each is written for multiplication, and the additive form comes from `to_additive`. The typical lemma is the one that bounds a sum of two suprema.

$$(\forall i\, j,\ g(i) + h(j) \le a) \implies \bigsqcup_i g(i) + \bigsqcup_j h(j) \le a \qquad (\texttt{ciSup\_add\_ciSup\_le}).$$

The index types must be nonempty, and the order must be compatible with addition on each side, `[AddLeftMono α]` and `[AddRightMono α]`. No hypothesis of boundedness is needed, because the hypothesis on $a$ gives the bound. The proof uses `ciSup_add_le` and `add_ciSup_le`: in a group, $g(i) + h \le a$ is the same as $g(i) \le a - h$, and a supremum is below $a - h$ when each term is. The other direction, $\bigsqcup_i (f(i) + g(i)) \le \bigsqcup_i f(i) + \bigsqcup_i g(i)$, needs only an addition and bounded ranges; it is `ciSup_add_le_ciSup_add_ciSup`. The infimum lemmas are `le_ciInf_add` and `le_ciInf_add_ciInf`. The lemma `csSup_add` of Section 2 for sets uses the pointwise sum; the lemmas of this file use indexed families.

**Conditionally complete partial orders.** Some orders of analysis are not lattices but have suprema of directed sets. The self-adjoint elements of a von Neumann algebra are the standard example, and the complex numbers with the partial order of the scope ComplexOrder are another. The file `Mathlib.Order.ConditionallyCompletePartialOrder.Defs` defines three classes for these orders. The class `ConditionallyCompletePartialOrderSup` asks that each nonempty directed set that is bounded above has `sSup s` as its least upper bound. The class `ConditionallyCompletePartialOrderInf` is the dual, and `ConditionallyCompletePartialOrder` has both. The field of the first class is accessible as a lemma.

$$s \text{ directed},\ s \ne \emptyset,\ s \text{ bounded above} \implies \operatorname{IsLUB}\, s\, (\sup s) \qquad (\texttt{DirectedOn.isLUB\_csSup}).$$

A conditionally complete lattice is an instance, by `ConditionallyCompleteLattice.toConditionallyCompletePartialOrder`, since each set is directed in a lattice. The lemmas of `Mathlib.Order.ConditionallyCompletePartialOrder.Basic` are the lemmas of Section 1 with an extra hypothesis of directedness, and they are in the `DirectedOn` namespace: `DirectedOn.le_csSup`, `DirectedOn.csSup_le`, `DirectedOn.le_csSup_iff`, `DirectedOn.csSup_le_csSup` and `DirectedOn.csSup_eq_of_forall_le_of_forall_lt_exists_gt`. A set with a greatest element is directed (`IsGreatest.directedOn`), so `IsGreatest.csSup_eq` needs no other hypothesis. For this reason `csSup_singleton` and `csSup_Icc` are in this file and hold in each conditionally complete partial order. The indexed forms are in the file of Section 2.

#### Common errors

1. Using a lemma for `WithTop α` with the wrong class on α. The instance `WithTop.instCompleteLinearOrder` needs `ConditionallyCompleteLinearOrderBot α`, so it applies to `WithTop ℕ` but not to `WithTop ℤ`. For $\mathbb{Z}$ or $\mathbb{R}$, use `WithBot (WithTop α)` or the conditionally complete instance.
2. Forgetting the `Fact` instance for an interval. The complete lattice on `Set.Icc a b` is found only when `Fact (a ≤ b)` is an instance. In a proof, add it with `haveI : Fact (a ≤ b) := ⟨h⟩`. The lemma `Set.Icc.coe_sSup` takes `h : a ≤ b` as an explicit argument for this reason.
3. Expecting `Int.csSup_mem` for a set with no upper bound. Then `sSup s` is $0$, which need not be in $s$; for $s = \{1, 2, 3, \dots\}$ the value $0$ is not in $s$.

### Exercises

1. (A) Use `Int.csSup_mem` to show that $\sup \{z \in \mathbb{Z} : z^2 < 10\} = 3$.
2. (A) Show that $\bigsqcup_n n = \top$ in `WithTop ℕ`, with `WithTop.iSup_coe_eq_top`.
3. (B) Prove that a nonempty finite subset of a conditionally complete linear order contains its infimum, by the dual of `Set.Nonempty.csSup_mem`.
4. (B) Let $s = (0, 1) \subseteq \mathbb{R}$. Find a nonempty subset of $s$ that is bounded above in $\mathbb{R}$ but whose supremum in $\mathbb{R}$ is not in $s$, and explain why this does not contradict `Set.OrdConnected.csSup_image_mem`.
5. (B) Prove $\sup_{x \in [0, 1]} x + \sup_{y \in [0, 1]} (-y) = 1$ in $\mathbb{R}$, with `ciSup_add_ciSup_le` for one inequality.
6. (C) Show that the order on $\mathbb{R}^2$ with $(a, b) \le (c, d)$ if and only if $a \le c$ and $b = d$ is not a lattice, and that each nonempty directed set that is bounded above has a least upper bound.

### Reference

<?reference?>
