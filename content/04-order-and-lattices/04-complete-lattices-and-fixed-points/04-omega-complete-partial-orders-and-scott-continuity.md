---
title: Omega-complete partial orders and Scott continuity
kind: api
modules:
  - Mathlib.Order.OmegaCompletePartialOrder
  - Mathlib.Order.ScottContinuity
  - Mathlib.Order.ScottContinuity.Complete
  - Mathlib.Order.ScottContinuity.Prod
  - Mathlib.Order.OrdContinuous
  - Mathlib.Order.Part
explains:
  E2: [OmegaCompletePartialOrder, OmegaCompletePartialOrder.Chain, OmegaCompletePartialOrder.ωSup_le_iff, OmegaCompletePartialOrder.ContinuousHom, OmegaCompletePartialOrder.fixedPoints.ωSup_iterate_mem_fixedPoint, Part.mem_ωSup, ScottContinuous, scottContinuous_iff_map_sSup, LeftOrdContinuous, GaloisConnection.leftOrdContinuous]
  E1: auto
families: []
requires: [V04.C01, V04.C02, V04.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Omega-complete partial orders and Scott continuity

### Overview

A complete lattice has a supremum for each set. Many orders in analysis and in computer science have suprema only for some sets. The partial functions from $\mathbb{N}$ to $\mathbb{N}$, ordered by extension, have no top element, but each increasing sequence of partial functions has a supremum: the union of their graphs. An order in which each increasing sequence has a supremum is an $\omega$-complete partial order. The fixed point theorem of Kleene works in these orders: a map that keeps the suprema of increasing sequences has a least fixed point above each point $x \le f(x)$, and the fixed point is the supremum of the sequence $x, f(x), f(f(x)), \dots$.

Scott continuity is the same condition for directed sets instead of sequences. A map $f$ is Scott continuous if it sends the least upper bound of each nonempty directed set $d$ to the least upper bound of $f(d)$. Order continuity is the condition for all nonempty sets. Each of the three conditions implies that $f$ is monotone, and the conditions get stronger in the order $\omega$, directed, all sets.

The section describes the class `OmegaCompletePartialOrder`, the chains, the continuous maps, the instance for `Part`, and the predicates `ScottContinuous` and `LeftOrdContinuous`. Section 2 of this chapter uses the predicate `OmegaCompletePartialOrder.ωScottContinuous` for Kleene's theorem in a complete lattice. This section gives the general setting.

### The library around it

#### Chains and the class

In the module `Mathlib.Order.OmegaCompletePartialOrder`, a chain is a monotone sequence: `OmegaCompletePartialOrder.Chain α` is the type `ℕ →o α`. The function `OmegaCompletePartialOrder.Chain.map` composes a chain with a monotone map. The class `OmegaCompletePartialOrder α` extends `PartialOrder α` with a function `ωSup` on chains and two axioms. In the namespace `OmegaCompletePartialOrder`, they are these.

| Lean name | Statement |
|---|---|
| `OmegaCompletePartialOrder.le_ωSup` | $c(i) \le \omega\mathrm{Sup}(c)$ for each $i$ |
| `OmegaCompletePartialOrder.ωSup_le` | if $c(i) \le x$ for each $i$, then $\omega\mathrm{Sup}(c) \le x$ |
| `OmegaCompletePartialOrder.ωSup_le_iff` | $\omega\mathrm{Sup}(c) \le x \iff \forall i,\ c(i) \le x$ |
| `OmegaCompletePartialOrder.isLUB_range_ωSup` | $\omega\mathrm{Sup}(c)$ is the least upper bound of the range of $c$ |
| `OmegaCompletePartialOrder.ωSup_eq_of_isLUB` | a least upper bound of the range is equal to $\omega\mathrm{Sup}(c)$ |

The last two lemmas connect the class with the predicate `IsLUB` of Chapter 1. Each complete lattice is an $\omega$-complete partial order, with $\omega\mathrm{Sup}(c) = \sup_i c(i)$. The function types have the pointwise instance, and `Pi.ωSup_apply` evaluates it.

#### Continuous maps

The predicate `OmegaCompletePartialOrder.ωScottContinuous f` says that $f$ keeps the least upper bounds of the ranges of chains. The lemma `OmegaCompletePartialOrder.ωScottContinuous.monotone` says that such a map is monotone, so `OmegaCompletePartialOrder.ωScottContinuous.map_ωSup` can state $f(\omega\mathrm{Sup}(c)) = \omega\mathrm{Sup}(c.\mathrm{map}\, f)$. The lemma `OmegaCompletePartialOrder.ωScottContinuous_iff_monotone_map_ωSup` is the equivalence with "monotone and keeps `ωSup`".

The bundled type `α →𝒄 β` is `OmegaCompletePartialOrder.ContinuousHom`: a monotone map with a proof of continuity. The continuous maps between two $\omega$-complete partial orders form an $\omega$-complete partial order, with the pointwise supremum by `OmegaCompletePartialOrder.ContinuousHom.ωSup_apply`. The proof is a swap of two suprema: for a chain of continuous maps $f_n$ and a chain $c$ in $\alpha$,
$$\sup_n f_n\Big(\sup_m c_m\Big) = \sup_n \sup_m f_n(c_m) = \sup_m \sup_n f_n(c_m).$$
The combinators `OmegaCompletePartialOrder.ContinuousHom.bind` and `OmegaCompletePartialOrder.ContinuousHom.seq` build continuous maps into `Part β` from continuous parts.

#### Fixed points

For a monotone map $f$ and a point $x$ with $x \le f(x)$, the chain `OmegaCompletePartialOrder.fixedPoints.iterateChain f x h` is the sequence $x, f(x), f(f(x)), \dots$. It is monotone by induction: $x \le f(x)$, and $f^n(x) \le f^{n+1}(x)$ gives $f^{n+1}(x) \le f^{n+2}(x)$ because $f$ is monotone. For a continuous $f$, two lemmas give the theorem of Kleene.

1. `OmegaCompletePartialOrder.fixedPoints.ωSup_iterate_mem_fixedPoint` says that the supremum $p$ of the chain is a fixed point of $f$. Proof: $f(p) = \sup_n f^{n+1}(x)$ by continuity, and the shifted chain has the same supremum as the chain, because $x \le f(x)$.
2. `OmegaCompletePartialOrder.fixedPoints.ωSup_iterate_le_prefixedPoint` says that $p \le a$ for each $a$ with $f(a) \le a$ and $x \le a$. Proof: $f^n(x) \le a$ by induction on $n$, because $f^n(x) \le a$ gives $f^{n+1}(x) \le f(a) \le a$.

With $x = \bot$, the point $p$ is the least fixed point of $f$.

#### Partial values

The module `Mathlib.Order.Part` gives the monotonicity rules for `Part α`, the type of the values that can be undefined. The lemma `Monotone.partBind` says that `Part.bind` of two monotone maps is monotone, and `OrderHom.partBind` is the bundled form. In `Mathlib.Order.OmegaCompletePartialOrder`, the instance `Part.omegaCompletePartialOrder` orders `Part α` by "undefined is below each value". A chain in `Part α` is constant from the first defined term on. So `Part.mem_ωSup` says that $x \in \omega\mathrm{Sup}(c)$ if and only if `Part.some x` is a term of the chain, `Part.ωSup_eq_some` gives the value when a term is defined, and `Part.ωSup_eq_none` gives the undefined value when no term is defined. With this instance, the fixed point lemmas apply to maps on the partial functions `α → Part β`.

#### Scott continuity

The module `Mathlib.Order.ScottContinuity` defines `ScottContinuous f` for maps between preorders: for each nonempty set $d$ that is directed for $\le$, and each least upper bound $a$ of $d$, the point $f(a)$ is a least upper bound of $f(d)$. The relative form `ScottContinuousOn D f` restricts $d$ to a family $D$ of sets, and `scottContinuousOn_univ` says that the form with all sets is `ScottContinuous f`. The lemma `ScottContinuous.monotone` gives the monotonicity: for $a \le b$, the set $\{a, b\}$ is directed with least upper bound $b$, so $f(b)$ is an upper bound of $f(a)$. A chain has a directed range, so `ScottContinuous.ωScottContinuous` turns a Scott continuous map into an $\omega$-continuous one.

In complete lattices, `Mathlib.Order.ScottContinuity.Complete` has the form with `sSup`: `scottContinuous_iff_map_sSup` says that $f$ is Scott continuous if and only if $f(\sup d) = \sup f(d)$ for each nonempty directed set $d$, and `ScottContinuous.map_sSup` is the forward direction. The module `Mathlib.Order.ScottContinuity.Prod` treats products. `ScottContinuous.prod` says that `Prod.map f g` is Scott continuous when $f$ and $g$ are, and `ScottContinuous.fromProd` says that a map on $\alpha \times \beta$ that is Scott continuous in each variable is Scott continuous. Examples are `ScottContinuous.sup₂` for the binary supremum and `ScottContinuous.inf₂` for the binary infimum in a complete linear order, with the one-variable form `scottContinuous_inf_left`.

#### Order continuity

The module `Mathlib.Order.OrdContinuous` defines the strongest form. `LeftOrdContinuous f` says that $f$ sends the least upper bound of each nonempty set $s$ to a least upper bound of $f(s)$. `RightOrdContinuous f` is the dual for greatest lower bounds. The main source of examples is `GaloisConnection.leftOrdContinuous`: the lower adjoint of a Galois connection is left order continuous. So `OrderIso.leftOrdContinuous` holds for each order isomorphism.

The consequences follow the order type. `LeftOrdContinuous.mono` gives the monotonicity, and `LeftOrdContinuous.map_sup` gives $f(a \sqcup b) = f(a) \sqcup f(b)$ in a semilattice. In a complete lattice, `LeftOrdContinuous.map_sSup` gives $f(\sup s) = \sup_{x \in s} f(x)$ for a nonempty set $s$. In a conditionally complete lattice, `LeftOrdContinuous.map_csSup` needs the extra hypothesis that $s$ is bounded above. For an injective map, `LeftOrdContinuous.le_iff` gives $f(x) \le f(y) \iff x \le y$, and `LeftOrdContinuous.toOrderEmbedding` makes $f$ an order embedding.

#### Common errors

1. A chain is a bundled monotone map `ℕ →o α`, not a function `ℕ → α`. To apply `OmegaCompletePartialOrder.ωSup` to a sequence, first build the chain with its proof of monotonicity, for example with `OmegaCompletePartialOrder.fixedPoints.iterateChain`.
2. The definitions `ScottContinuous` and `LeftOrdContinuous` quantify only over nonempty sets. They do not say $f(\bot) = \bot$, so `LeftOrdContinuous.map_sSup` has a hypothesis `s.Nonempty`.
3. The predicate `ScottContinuous` needs only a preorder, but `ScottContinuous.ωScottContinuous` needs `OmegaCompletePartialOrder` instances on both sides. In a complete lattice these instances exist, and the predicate of Section 2 then follows.

### Exercises

1. (A) Show that the identity map and each constant map on an $\omega$-complete partial order are continuous, with `OmegaCompletePartialOrder.ωScottContinuous_iff_monotone_map_ωSup`.
2. (A) Use `GaloisConnection.leftOrdContinuous` to show that the image map `Set.image f` keeps arbitrary unions.
3. (B) Prove `OmegaCompletePartialOrder.ωSup_le_iff` from the two axioms of the class.
4. (B) Prove that a Scott continuous map between preorders is monotone, without `ScottContinuous.monotone`.
5. (B) In `Part ℕ`, compute the supremum of the chain whose terms are undefined for $n < 3$ and equal to `Part.some 7` for $n \ge 3$, with `Part.ωSup_eq_some`.
6. (C) Give a monotone map on the complete lattice `Set ℕ` that is $\omega$-continuous but not left order continuous, and prove both facts.

### Reference

<?reference?>
