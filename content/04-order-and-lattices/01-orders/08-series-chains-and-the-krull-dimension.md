---
title: Series, chains and the Krull dimension
kind: api
modules:
  - Mathlib.Order.RelSeries
  - Mathlib.Order.KrullDimension
  - Mathlib.Order.JordanHolder
  - Mathlib.Order.NonemptyFiniteChains
  - Mathlib.Order.Preorder.PairwiseChain
explains:
  E2: [LTSeries.length_lt_card, Order.krullDim_le_of_strictMono, Order.krullDim_orderDual, Order.height_add_one_le, Order.height_nat, Order.krullDim_le_one_iff, CompositionSeries.jordan_holder, IsChain.pairwise_sUnion]
  E1: auto
families: []
requires: [V01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Series, chains and the Krull dimension

### Overview

A chain $a_0 < a_1 < \cdots < a_n$ in an order is a finite object with a length $n$. This section studies chains as finite sequences, the form that dimension theory needs. The Krull dimension of a ring is the supremum of the lengths of chains of prime ideals. The length of a module is the length of a maximal chain of submodules. The Jordan and Hölder theorem compares two maximal chains in a group or a module.

The module `Mathlib.Order.RelSeries` defines a series for an arbitrary relation $r$: a finite sequence $a_0, \ldots, a_n$ with $r\,a_i\,a_{i+1}$ for each $i < n$. A series for `<` is an `LTSeries`. The module `Mathlib.Order.KrullDimension` defines the Krull dimension of a preorder, the height and the coheight of an element. The module `Mathlib.Order.JordanHolder` proves the Jordan and Hölder theorem once, for a lattice with an abstract notion of a maximal step. Two small modules complete the section: `Mathlib.Order.NonemptyFiniteChains` gives the poset of nonempty finite chains, and `Mathlib.Order.Preorder.PairwiseChain` gives the pairwise properties of a union of a chain of sets.

### The library around it

#### Relation series

Let $r$ be a relation on $\alpha$. In the library the relation has the type `SetRel α α`, a set of pairs, so $r\,a\,b$ is written `(a, b) ∈ r`. A term `p : RelSeries r` has three fields: the length `p.length : ℕ`, the function `p.toFun : Fin (p.length + 1) → α`, and the proof `p.step` that consecutive values are related. So a series of length $n$ has $n + 1$ entries and $n$ steps. The coercion writes `p i` for `p.toFun i`. The first and the last entries are `p.head` and `p.last`, with `RelSeries.apply_zero` and `RelSeries.apply_last` as the rewriting lemmas, and `x ∈ p` means that $x$ is an entry (`RelSeries.mem_def`).

The library builds series as lists are built. The table gives the constructions and the length of the result.

| Lean name | Construction | Length |
|---|---|---|
| `RelSeries.singleton r a` | the series $a$ | $0$ |
| `RelSeries.cons` | put $x$ in front, if $(x, a_0) \in r$ | $n + 1$ |
| `RelSeries.snoc` | put $x$ at the end, if $(a_n, x) \in r$ | $n + 1$ |
| `RelSeries.append` | join $p$ and $q$, if $(p_{\mathrm{last}}, q_{\mathrm{head}}) \in r$ | $n + m + 1$ |
| `RelSeries.smash` | join $p$ and $q$, if $p_{\mathrm{last}} = q_{\mathrm{head}}$ | $n + m$ |
| `RelSeries.tail`, `RelSeries.eraseLast` | remove the first or the last entry | $n - 1$ |
| `RelSeries.take`, `RelSeries.drop` | keep the entries up to $i$ or from $i$ | $i$ or $n - i$ |
| `RelSeries.insertNth` | insert $a$ between two entries | $n + 1$ |
| `RelSeries.reverse` | read backwards, a series for `r.inv` | $n$ |
| `RelSeries.map` | apply a relation homomorphism | $n$ |

Each construction has simp lemmas for its length, its head and its last entry, named `RelSeries.snoc_length`, `RelSeries.head_snoc`, `RelSeries.last_snoc` and so on. The function `RelSeries.toList` converts a series to a nonempty list in which consecutive entries are related, and `RelSeries.fromListIsChain` goes back. Two induction principles, `RelSeries.inductionOn` and `RelSeries.inductionOn'`, build a series from a singleton by `RelSeries.cons` or by `RelSeries.snoc`. For a transitive relation, `RelSeries.rel_of_lt` says that $r\,a_i\,a_j$ for all $i < j$, not only for consecutive indices.

A relation is *finite dimensional* (`SetRel.FiniteDimensional r`) if it has a longest series, and *infinite dimensional* (`SetRel.InfiniteDimensional r`) if it has series of each length. On a nonempty type exactly one of these holds (`SetRel.finiteDimensional_or_infiniteDimensional`). The longest series is `RelSeries.longestOf r`, and a series of length $n$ in the infinite case is `RelSeries.withLength r n`. A finite dimensional relation is well-founded, by `SetRel.IsWellFounded.of_finiteDimensional`, because an infinite descending sequence would give series of each length.

#### Series for `<`

For a preorder, `LTSeries α` is `RelSeries` for the relation $a < b$. A series of this kind is a strictly monotone map `Fin (n + 1) → α`, and `LTSeries.mk` builds it from such a map. The order classes `FiniteDimensionalOrder α` and `InfiniteDimensionalOrder α` are the two dimension classes for `<`. The function `LTSeries.map` pushes a series along a strictly monotone map, and `LTSeries.comap` pulls it back along a surjection that reflects `<`. The series `LTSeries.range n` is $0 < 1 < \cdots < n$ in `ℕ`.

**Proposition.** In a finite preorder $\alpha$, each series $a_0 < \cdots < a_n$ has $n < |\alpha|$ (`LTSeries.length_lt_card`).

*Proof.* The map $i \mapsto a_i$ on `Fin (n + 1)` is strictly monotone, so it is injective. An injective map from a set with $n + 1$ elements into $\alpha$ gives $n + 1 \le |\alpha|$. $\square$

For a partial order that is well-founded in both directions, `LTSeries.exists_relSeries_covBy` refines each series to a series of covering steps $a \lessdot b$ with the same entries in it.

#### The Krull dimension

**Definition.** Let $\alpha$ be a preorder. The *Krull dimension* of $\alpha$ is
$$\dim \alpha = \sup \{\, n \mid \text{there is a series } a_0 < a_1 < \cdots < a_n \text{ in } \alpha \,\}.$$
The *height* of $a$ is the supremum of the lengths of series with $a_n \le a$, and the *coheight* of $a$ is the supremum of the lengths of series with $a \le a_0$.

In Lean, `Order.krullDim α` has the type `WithBot ℕ∞`. The value is $\bot$ for an empty type, because the supremum of the empty set is $\bot$, and the value is $\top$ when the lengths are unbounded. The height `Order.height a` and the coheight `Order.coheight a` have the type `ℕ∞`, because each element has at least the series of length $0$. The characterisations at the two ends are `Order.krullDim_eq_bot_iff` (the type is empty) and `Order.krullDim_eq_top_iff` (the order is infinite dimensional). For a finite dimensional order, `Order.krullDim_eq_length_of_finiteDimensionalOrder` gives the dimension as the length of `LTSeries.longestOf α`.

The dimension is the supremum of the heights (`Order.krullDim_eq_iSup_height`), and also of the coheights. The height of $a$ is the dimension of the interval `Set.Iic a` (`Order.height_eq_krullDim_Iic`).

**Proposition.** If $a < b$, then $\operatorname{height} a + 1 \le \operatorname{height} b$ (`Order.height_add_one_le`).

*Proof.* Let $a_0 < \cdots < a_n$ be a series with $a_n \le a$. Then $a_n < b$, so `RelSeries.snoc` gives the series $a_0 < \cdots < a_n < b$ of length $n + 1$, which ends at $b$. Take the supremum over the series. $\square$

The converse form is `Order.height_eq_iSup_lt_height`: the height of $x$ is the supremum of $\operatorname{height} y + 1$ over $y < x$. So the height is the unique function that is $0$ on minimal elements (`Order.height_eq_zero`) and satisfies this recursion. The coheight has the dual lemmas, `Order.coheight_add_one_le` and `Order.coheight_eq_zero`, and `Order.height_toDual` turns one into the other.

**Proposition.** If $f : \alpha \to \beta$ is strictly monotone, then $\dim \alpha \le \dim \beta$ (`Order.krullDim_le_of_strictMono`). The dual order has the same dimension: $\dim \alpha^{\mathrm{op}} = \dim \alpha$ (`Order.krullDim_orderDual`).

*Proof.* The map `LTSeries.map` sends a series of length $n$ in $\alpha$ to a series of length $n$ in $\beta$, so each length that occurs in $\alpha$ occurs in $\beta$. For the dual order, `RelSeries.reverse` reads a series $a_0 < \cdots < a_n$ backwards. In $\alpha^{\mathrm{op}}$ the result is a series of the same length, and reversing twice gives back the series. $\square$

The first result gives `Order.krullDim_le_of_orderEmbedding` and `Order.krullDim_eq_of_orderIso`. The computed examples are in the table.

| Lean name | Statement |
|---|---|
| `Order.height_nat` | $\operatorname{height} n = n$ in $\mathbb{N}$ |
| `Order.krullDim_nat` | $\dim \mathbb{N} = \top$ |
| `Order.krullDim_int` | $\dim \mathbb{Z} = \top$ |
| `Order.krullDim_withBot` | $\dim (\alpha \cup \{\bot\}) = \dim \alpha + 1$ for nonempty $\alpha$ |
| `Order.krullDim_of_isSimpleOrder` | a simple order, $\{\bot, \top\}$ with $\bot \ne \top$, has dimension $1$ |
| `Order.krullDim_eq_zero_of_unique` | a type with one element has dimension $0$ |
| `Order.krullDim_of_noMaxOrder` | a nonempty order with no maximal element has dimension $\top$ |

**Proposition.** $\operatorname{height} n = n$ for $n \in \mathbb{N}$ (`Order.height_nat`).

*Proof.* The series $0 < 1 < \cdots < n$ has length $n$, so $\operatorname{height} n \ge n$. A series $a_0 < \cdots < a_k$ with $a_k \le n$ has $k$ distinct entries in $\{1, \ldots, n\}$ after $a_0$, because each step adds at least $1$ and $a_0 \ge 0$. So $k \le n$. $\square$

**Proposition.** $\dim \alpha \le 1$ if and only if each element of $\alpha$ is minimal or maximal (`Order.krullDim_le_one_iff`).

*Proof.* A series $a < b < c$ of length $2$ has a middle element $b$ that is neither minimal ($a < b$) nor maximal ($b < c$). Conversely, an element $b$ that is neither minimal nor maximal has $a < b$ and $b < c$ for some $a$ and $c$, and this is a series of length $2$. $\square$

Mathlib defines the Krull dimension `ringKrullDim R` of a commutative ring as `Order.krullDim` of its prime spectrum, so the ring theory uses this API directly. For example, a ring has dimension at most $1$, as a Dedekind domain has, exactly when each prime ideal is minimal or maximal.

#### The Jordan and Hölder theorem

The class `JordanHolderLattice X` gives a lattice $X$ with a relation `JordanHolderLattice.IsMaximal x y`, read "$x$ is a maximal element below $y$". The axioms are: a maximal step is strict; two distinct maximal elements $x, y$ below $z$ have $x \sqcup y = z$; and if $x$ and $y$ are both maximal in $x \sqcup y$, then $x \sqcap y$ is maximal in $x$. Each weakly lower modular lattice is an instance, with the covering relation `CovBy` as the maximal step, so each modular lattice is one too. The lattice of submodules of a module is modular, so it is a Jordan and Hölder lattice. For subgroups the natural step is a maximal normal subgroup, which is not a covering step, and the abstract relation leaves room for this case.

A composition series `CompositionSeries X` is a `RelSeries` for the relation `JordanHolderLattice.IsMaximal`. Its entries form a chain (`CompositionSeries.total`), and they increase strictly (`CompositionSeries.strictMono`). The relation `JordanHolderLattice.Iso` on pairs $(x, y)$ is the equivalence relation generated by the second isomorphism theorem: $(x, x \sqcup y)$ is related to $(x \sqcap y, y)$ when $x$ is maximal in $x \sqcup y$ (`JordanHolderLattice.second_iso`). Two composition series are `CompositionSeries.Equivalent` if there is a bijection of the steps that relates each step to its image.

**Theorem (Jordan and Hölder).** Two composition series with the same head and the same last entry are equivalent (`CompositionSeries.jordan_holder`). In particular they have the same length (`CompositionSeries.Equivalent.length_eq`).

*Proof sketch.* The key step is `CompositionSeries.exists_last_eq_snoc_equivalent`. Let $s$ be a composition series and let $x$ be maximal below the last entry of $s$, with $x$ above the head. Then there is a composition series $t$ from the head of $s$ to $x$, one step shorter than $s$, such that $s$ is equivalent to $t$ followed by the step from $x$ to the last entry. This lemma is proved by induction on the length of $s$. Let $y$ be the entry of $s$ before the last entry $z$. If $y = x$, take $t$ to be $s$ without its last step. If $y \ne x$, then $x \sqcup y = z$ by the second axiom, and $x \sqcap y$ is maximal in $y$ by the third. The induction hypothesis gives a series to $x \sqcap y$, and `CompositionSeries.Equivalent.snoc_snoc_swap` exchanges the two top steps $x \sqcap y < y < z$ and $x \sqcap y < x < z$, because they are related by the second isomorphism theorem. The theorem follows by induction on the length of $s_1$: apply the key step to $s_1$ and to the entry of $s_2$ before its last entry, use the induction hypothesis on the shorter series, and add the common last step with `CompositionSeries.Equivalent.snoc`. $\square$

For modules, `JordanHolderLattice.Iso.linearEquiv` turns the relation `JordanHolderLattice.Iso` into a linear isomorphism of the quotient modules. So two composition series of a module have the same simple factors up to isomorphism and order.

#### Finite chains and unions of chains

The structure `PartialOrder.NonemptyFiniteChains X` has as terms the nonempty finite subsets of $X$ whose elements are pairwise comparable. Its field `PartialOrder.NonemptyFiniteChains.finset` gives the underlying `Finset`, and the order is inclusion (`PartialOrder.NonemptyFiniteChains.le_iff`). A monotone map $X \to Y$ sends a chain to a chain, and `PartialOrder.NonemptyFiniteChains.map` is the image. The functor `PartOrd.nonemptyFiniteChainsFunctor` makes this a functor on the category of partial orders.

The module `Mathlib.Order.Preorder.PairwiseChain` is about a chain $c$ of sets for $\subseteq$.

**Proposition.** If $c$ is a chain of sets, then $\bigcup c$ is pairwise $r$ if and only if each $s \in c$ is pairwise $r$ (`IsChain.pairwise_sUnion`).

*Proof.* A subset of a pairwise $r$ set is pairwise $r$, so one direction is clear. For the other, let $a \ne b$ be in $\bigcup c$, with $a \in s$ and $b \in t$ for $s, t \in c$. Since $c$ is a chain, one of $s$ and $t$ contains the other, say $s \subseteq t$. Then $a, b \in t$, and $t$ is pairwise $r$. $\square$

The forms `IsChain.pairwise_iUnion₂`, `IsChain.pairwiseDisjoint_sUnion` and `IsChain.pairwiseDisjoint_iUnion₂` give the same statement for an indexed union and for the property `Set.PairwiseDisjoint`. They are the step in a Zorn argument where the union of a chain of disjoint families must again be disjoint.

#### Common errors

1. The length of a `RelSeries` is the number of steps, not the number of entries. A series with entries $a_0, \ldots, a_n$ has `length = n`, and its function has the domain `Fin (n + 1)`.
2. `Order.krullDim α` lives in `WithBot ℕ∞`, and `Order.height a` lives in `ℕ∞`. A comparison of a height with a dimension needs a coercion, as in `Order.height_le_krullDim`. A goal `Order.krullDim α = 0` on a type that can be empty is false, because the empty type has dimension $\bot$.
3. The relation of a `RelSeries` is a `SetRel α α`, not a function `α → α → Prop`. A step is written `(a, b) ∈ r`. For `<`, use `LTSeries` and its lemmas, which state the steps as `a < b`.

### Exercises

1. (A) Prove that a series of length $0$ has exactly one entry, with `RelSeries.subsingleton_of_length_eq_zero`.
2. (A) Compute the Krull dimension of `Fin 5` with its usual order, and the height of each element.
3. (B) Prove that $\dim (\alpha \times \beta) \ge \dim \alpha + \dim \beta$ for nonempty finite dimensional preorders, by joining a series in $\alpha$ and a series in $\beta$.
4. (B) Prove that in a finite dimensional order the height is strictly monotone: $a < b$ gives $\operatorname{height} a < \operatorname{height} b$.
5. (B) Let $V$ be a vector space of dimension $n$ over a field. Prove that the lattice of subspaces has Krull dimension $n$.
6. (C) Prove the Jordan and Hölder theorem for the lattice of subsets of a finite set, with the covering relation as the maximal step, and show that each composition series of $\{1, \ldots, n\}$ has length $n$.

### Reference

<?reference?>
