---
title: Archimedean successor orders and rooted trees
kind: api
modules:
  - Mathlib.Order.SuccPred.Archimedean
  - Mathlib.Order.SuccPred.LinearLocallyFinite
  - Mathlib.Order.SuccPred.Tree
explains:
  E2: [IsSuccArchimedean, IsSuccArchimedean.exists_succ_iterate_of_le, Succ.rec, WellFoundedGT.toIsSuccArchimedean, LinearLocallyFiniteOrder.succOrder, toZ, orderIsoIntOfLinearSuccPredArch, orderIsoNatOfLinearSuccPredArch, RootedTree, RootedTree.subtrees_disjoint]
  E1: auto
families: []
requires: [V04.C01, V04.C02, V04.C03, V04.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Archimedean successor orders and rooted trees

### Overview

In `ℕ` each $b \ge a$ is $a + n$ for some $n$: one reaches $b$ from $a$ by finitely many successor steps. The ordinals do not have this property, since no finite number of steps leads from $0$ to $\omega$. Mathlib calls a successor order with this property Archimedean, by analogy with the Archimedean property of the real numbers, where finitely many steps of a fixed length pass any bound. The class is `IsSuccArchimedean`, and its dual for the predecessor is `IsPredArchimedean`.

Archimedean successor orders support induction from any starting point. In the linear case they are small: such an order with a successor and a predecessor is countable, and it is isomorphic to `ℤ`, to `ℕ` or to a finite set $\{0, \dots, n\}$, according to its end points. The locally finite linear orders, in which each bounded interval is finite, are a source of examples. The last part of the section treats the rooted trees of Mathlib. A rooted tree is an order with a bottom, the root, in which the predecessor of a vertex is its parent, and the Archimedean property says that each vertex has finite depth.

### The library around it

#### The class

The class `IsSuccArchimedean α`, for a preorder with a successor, has one field, `IsSuccArchimedean.exists_succ_iterate_of_le`: if $a \le b$, then $\operatorname{succ}^{[n]} a = b$ for some $n$. Here $\operatorname{succ}^{[n]}$ is the $n$-fold composition. The class is a `Prop`, so it carries no data.

| Lean name | Statement |
|---|---|
| `exists_succ_iterate_iff_le` | $(\exists n, \operatorname{succ}^{[n]} a = b) \iff a \le b$ |
| `exists_succ_iterate_or` | in a linear order, $b$ is reached from $a$ or $a$ from $b$ |
| `Succ.rec` | induction from $m$: $P(m)$ and $P(n) \to P(\operatorname{succ} n)$ give $P(n)$ for $n \ge m$ |
| `Succ.rec_iff` | if $p(a) \iff p(\operatorname{succ} a)$ for all $a$, then $p(a) \iff p(b)$ for $a \le b$ |
| `monotone_of_le_succ` | $f(a) \le f(\operatorname{succ} a)$ at each non maximal $a$ gives $f$ monotone |
| `strictMono_of_lt_succ` | $f(a) < f(\operatorname{succ} a)$ at each non maximal $a$ gives $f$ strictly monotone |
| `BddAbove.exists_isGreatest_of_nonempty` | in a linear order, a nonempty set bounded above has a greatest element |

The proof of `monotone_of_le_succ` uses `Succ.rec`. Fix $a$ and prove $f(a) \le f(b)$ for $b \ge a$ by induction from $a$. The base case is $f(a) \le f(a)$. If $f(a) \le f(n)$, then $f(n) \le f(\operatorname{succ} n)$ when $n$ is not maximal, and $\operatorname{succ} n = n$ when $n$ is maximal. In both cases $f(a) \le f(\operatorname{succ} n)$.

The class `Nat.instIsSuccArchimedean` and the class `Int.instIsSuccArchimedean` give the two main instances. Two general sources are `WellFoundedGT.toIsSuccArchimedean`, for an order in which each increasing sequence is eventually constant, and `WellFoundedLT.toIsPredArchimedean`, its dual. The first is the reason that each finite order is Archimedean. The class passes to an order connected subset, `Set.OrdConnected.isSuccArchimedean`, and through an order isomorphism, `IsSuccArchimedean.of_orderIso`.

In a linear order the two Archimedean properties agree: `LinearOrder.isSuccArchimedean_iff_isPredArchimedean`, with `LinearOrder.isPredArchimedean_of_isSuccArchimedean` as an instance. The lemma `SuccOrder.forall_ne_bot_iff` says that, in an Archimedean order with a bottom, a property holds at each $i \ne \bot$ if and only if it holds at each successor. With the hypothesis `IsCodirectedOrder α`, the definition `IsSuccArchimedean.linearOrder` shows that an Archimedean successor order is linear: two elements above a common lower bound $c$ are both reached from $c$, so the shorter chain ends below the longer one.

An Archimedean successor order has no limit elements in the sense of the next section: `Order.not_isSuccLimit_of_isSuccArchimedean`. A strictly monotone map from an order without a maximum into an Archimedean order has an unbounded range, `StrictMono.not_bddAbove_range_of_isSuccArchimedean`.

#### Locally finite linear orders

A linear order is locally finite when each interval $[a, b]$ is finite. In such an order each $i$ that is not maximal has a least element above it, the first element of the finite set $(i, j]$ for any $j > i$. The definition `LinearLocallyFiniteOrder.succFn` gives this element, and `i` when $i$ is maximal. The definition `LinearLocallyFiniteOrder.succOrder ι` packages it as a `SuccOrder ι`. It is a definition, not an instance, because an order such as `ℕ` already has its own successor. By `Order.instSubsingletonSuccOrder` the two agree.

The instance `LinearLocallyFiniteOrder.instIsSuccArchimedeanOfLocallyFiniteOrder` makes each successor order on a locally finite linear order Archimedean: from $a$ to $b$ the successor steps run through the finite set $[a, b]$, so they stop. The lemma `Countable.of_linearOrder_locallyFiniteOrder` says that a locally finite linear order is countable.

#### The map to the integers

Fix a point $i_0$ of a linear Archimedean order $\iota$ with a successor and a predecessor. The map `toZ i0 : ι → ℤ` sends $i \ge i_0$ to the number of successor steps from $i_0$ to $i$, and $i < i_0$ to minus the number of predecessor steps from $i_0$ to $i$. So `toZ_iterate_succ` gives $\operatorname{toZ}_{i_0}(\operatorname{succ}^{[n]} i_0) = n$ in an order without maximum. The map is strictly monotone, `toZ_strictMono`, hence injective, `injective_toZ`. So `countable_of_linear_succ_pred_arch` follows: such an order is countable.

The image of `toZ` depends on the end points of $\iota$, and it gives three classification results.

| Lean name | Hypotheses | Result |
|---|---|---|
| `orderIsoIntOfLinearSuccPredArch` | no maximum, no minimum, nonempty | `ι ≃o ℤ` |
| `orderIsoNatOfLinearSuccPredArch` | no maximum, a bottom | `ι ≃o ℕ` |
| `orderIsoRangeOfLinearSuccPredArch` | a bottom and a top | `ι ≃o` a `Finset.range` of `ℕ` |

For the first one the proof shows that `toZ` is surjective. For $n \ge 0$ the point $\operatorname{succ}^{[n]} i_0$ maps to $n$. For $n < 0$ the point $\operatorname{pred}^{[-n]} i_0$ maps to $n$. Neither iteration gets stuck, because $\iota$ has no maximum and no minimum. A strictly monotone bijection between linear orders is an order isomorphism.

#### Rooted trees

The structure `RootedTree` packs a type with four instances:

1. `SemilatticeInf`: the infimum $u \sqcap v$ is the least common ancestor of $u$ and $v$;
2. `OrderBot`: the bottom is the root;
3. `PredOrder`: the predecessor of a vertex is its parent;
4. `IsPredArchimedean`: each vertex is reached from the root by finitely many steps.

The order is the ancestor relation: $u \le v$ when $u$ lies on the path from the root to $v$. The Archimedean property gives `le_total_of_directed`: two vertices below a common vertex $r$ are comparable, since both lie on the finite path from the root to $r$. This is the tree property: the ancestors of a vertex form a chain.

A subtree is a vertex together with everything above it. The type `SubRootedTree t` represents a subtree of `t` by its root, `SubRootedTree.root`, and `SubRootedTree.coeTree` turns it into a rooted tree on `Set.Ici r`. The function `RootedTree.subtree` sends a vertex to the subtree that it generates. The set `RootedTree.subtrees t` holds the immediate subtrees, those whose roots are atoms, that is, children of the root, and `RootedTree.subtrees_disjoint` says that they are pairwise disjoint. With decidable equality, `RootedTree.subtreeOf t v` is the subtree generated by `IsPredArchimedean.findAtom v`. It contains $v$, `RootedTree.mem_subtreeOf`, and for $v \ne \bot$ it is one of the immediate subtrees, `RootedTree.subtreeOf_mem_subtrees`. For the root it is the whole tree.

The construction uses `IsPredArchimedean.findAtom`. For a vertex $r \ne \bot$ it follows the parents from $r$ down until it reaches a vertex whose parent is the root. That vertex is an atom of the order, `IsPredArchimedean.isAtom_findAtom`, and it lies below $r$, `IsPredArchimedean.findAtom_le`. So an Archimedean predecessor order with a bottom is atomic, `IsPredArchimedean.instIsAtomic`.

#### Common errors

1. `Succ.rec` proves a statement only for $n \ge m$, and the motive takes the proof of $m \le n$ as an argument. For a statement over all of `ℤ` one needs the downward recursion `Pred.rec` as well, or `Succ.rec_linear` for a property that is the same at $a$ and $\operatorname{succ} a$.
2. `LinearLocallyFiniteOrder.succOrder` is a definition, so the instance search does not find it. A proof must install it with `letI`.
3. The value of `toZ i0 i` depends on the base point $i_0$. Two choices of $i_0$ give maps that differ by a constant, and `toZ i0 i0 = 0`.

### Exercises

1. (A) Show that `Fin n` is Archimedean as a successor order with `WellFoundedGT.toIsSuccArchimedean`.
2. (A) Prove `exists_succ_iterate_or` from `exists_succ_iterate_iff_le` in a linear order.
3. (B) Prove `strictMono_of_lt_succ` with `Succ.rec`.
4. (B) Show that the ordinals are not Archimedean as a successor order: no finite iterate of the successor sends $0$ to $\omega$.
5. (B) Show that the order $\mathbb{Z} \times_{\mathrm{lex}} \mathbb{Z}$ is not locally finite, and that it has a successor order that is not Archimedean.
6. (C) Prove that $\operatorname{toZ}_{i_0}$ is strictly monotone from its definition.

### Reference

<?reference?>
