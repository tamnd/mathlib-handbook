---
title: Successor orders
kind: api
modules:
  - Mathlib.Order.SuccPred.Basic
  - Mathlib.Order.SuccPred.WithBot
  - Mathlib.Order.SuccPred.Nat
  - Mathlib.Order.SuccPred.Int
  - Mathlib.Order.SuccPred.PNat
  - Mathlib.Order.SuccPred.Fin
  - Mathlib.Order.SuccPred.ENat
  - Mathlib.Order.SuccPred.Relation
  - Mathlib.Order.SuccPred.IntervalSucc
explains:
  E2: [SuccOrder, Order.succ, Order.succ_le_iff, Order.lt_succ_iff, Order.covBy_succ_of_not_isMax, SuccOrder.ofCore, Order.succ_eq_sInf, WithBot.succ, Fin.orderSucc_last, Monotone.biUnion_Ico_Ioc_map_succ]
  E1: auto
families: []
requires: [V04.C01, V04.C02, V04.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Successor orders

### Overview

The successor of a natural number $n$ is $n + 1$. Two properties describe it by the order alone: $n < n + 1$, and $n + 1 \le m$ for each $m > n$. So $n + 1$ is the least element above $n$. The same description works in `ℤ`, in `Fin n` and in `ℕ∞`, and it also works for the ordinals, where $\omega + 1$ is the least ordinal above $\omega$. Mathlib collects these orders in the class `SuccOrder`.

The definition must say what happens at a maximal element. In `Fin (n + 1)` the last element has nothing above it, so its successor cannot be larger. Mathlib sets the successor of a maximal element to the element itself, and the main lemmas carry a hypothesis that the element is not maximal, or the class `NoMaxOrder`. This section describes the class, these hypotheses, the dual class `PredOrder`, the instances on the number types, and the unions of intervals that a monotone map gives.

### The library around it

#### The class

The class `SuccOrder α`, for a preorder $\alpha$, has a map `succ : α → α` and three fields:

1. `le_succ`: $a \le \operatorname{succ} a$;
2. `max_of_succ_le`: if $\operatorname{succ} a \le a$, then $a$ is maximal;
3. `succ_le_of_lt`: if $a < b$, then $\operatorname{succ} a \le b$.

The map is `Order.succ`, and the root lemmas are `Order.le_succ`, `Order.max_of_succ_le` and `Order.succ_le_of_lt`. The class `PredOrder α` is the dual, with `Order.pred`, $\operatorname{pred} a \le a$, and $b \le \operatorname{pred} a$ for each $b < a$. The instance `instPredOrderOrderDualOfSuccOrder` makes a successor on $\alpha$ a predecessor on $\alpha^{\mathrm{op}}$, so each lemma on `succ` has a `pred` twin with the same name pattern.

The source explains why the fields are not the equivalence $\operatorname{succ} a \le b \iff a < b$. At a maximal $a$ the right side is false for $b = \operatorname{succ} a$, and the left side is true. So the equivalence needs a hypothesis.

| Lean name | Statement |
|---|---|
| `Order.succ_le_iff` | $\operatorname{succ} a \le b \iff a < b$, with `NoMaxOrder α` |
| `Order.lt_succ_iff` | $a < \operatorname{succ} b \iff a \le b$, linear, with `NoMaxOrder α` |
| `Order.lt_succ_iff_not_isMax` | $a < \operatorname{succ} a \iff \neg\operatorname{IsMax} a$ |
| `Order.covBy_succ_of_not_isMax` | $a \lessdot \operatorname{succ} a$ for $a$ not maximal |
| `Order.succ_eq_iff_covBy` | $\operatorname{succ} a = b \iff a \lessdot b$, with `NoMaxOrder α` |
| `Order.le_succ_iff_eq_or_le` | $a \le \operatorname{succ} b \iff a = \operatorname{succ} b \lor a \le b$, linear |
| `Order.succ_le_succ_iff` | $\operatorname{succ} a \le \operatorname{succ} b \iff a \le b$, linear, `NoMaxOrder α` |
| `Order.succ_strictMono` | `succ` is strictly monotone, with `NoMaxOrder α` |
| `Order.succ_top` | $\operatorname{succ} \top = \top$ |

Many lemmas come in two forms: one with `[NoMaxOrder α]` and one with a hypothesis `¬IsMax a`, whose name ends in `_of_not_isMax`. The covering statement shows the role of the hypothesis. Let $a$ be not maximal. Then $a < \operatorname{succ} a$ by `Order.lt_succ_iff_not_isMax`. If $a < c$, then $\operatorname{succ} a \le c$ by the third field, so no $c$ lies strictly between $a$ and $\operatorname{succ} a$. This is $a \lessdot \operatorname{succ} a$.

When both classes are present, `Order.gc_pred_succ` says that `pred` and `succ` form a Galois connection. Without maximal elements, `Order.pred_succ` gives $\operatorname{pred}(\operatorname{succ} a) = a$, and without minimal elements `Order.succ_pred` gives $\operatorname{succ}(\operatorname{pred} a) = a$.

#### Uniqueness and construction

In a partial order the successor is unique, `Order.instSubsingletonSuccOrder`: two `SuccOrder` structures on the same order are equal. So the class carries no choice, and the instances on `ℕ` and `ℤ` cannot clash. The successor has a formula in a complete lattice: `Order.succ_eq_sInf` gives $\operatorname{succ} a = \inf\,(a, \infty)$. The lemmas `Order.succ_eq_csInf` and `Order.succ_eq_iInf` give the forms for a conditionally complete lattice and for an indexed infimum.

Three constructors build the structure.

1. `SuccOrder.ofSuccLeIff` takes a map with $\operatorname{succ} a \le b \iff a < b$ for all $a, b$. This fits an order without maximal elements.
2. `SuccOrder.ofCore`, in a linear order, takes the equivalence for $a$ not maximal and the equation $\operatorname{succ} a = a$ for $a$ maximal.
3. `SuccOrder.ofLinearWellFoundedLT` builds the successor of a well-founded linear order as the least element above $a$, or $a$ itself if there is none. It is a definition, not an instance, so a proof must install it with `letI`.

A subset that is order connected keeps the successor of the order: `Set.OrdConnected.succOrder`.

#### Intervals

With `NoMaxOrder α` in a linear order, the successor turns closed bounds into open ones. `Order.Iio_succ` gives $(-\infty, \operatorname{succ} a) = (-\infty, a]$, and `Order.Ico_succ_right` gives $[a, \operatorname{succ} b) = [a, b]$. The inclusion `Order.Iic_subset_Iio_succ`, $(-\infty, a] \subseteq (-\infty, \operatorname{succ} a)$, holds without the linearity. At a maximal $a$ all three statements fail, since $(-\infty, \operatorname{succ} a) = (-\infty, a)$.

#### The number types

| Lean name | Statement |
|---|---|
| `Nat.succ_eq_succ` | `Order.succ = Nat.succ` |
| `Nat.succ_iterate` | $\operatorname{succ}^{[n]} a = a + n$ |
| `Nat.covBy_iff_add_one_eq` | $m \lessdot n \iff m + 1 = n$ |
| `Int.succ_eq_succ` | `Order.succ = Int.succ` |
| `PNat.succ_eq_add_one` | $\operatorname{succ} n = n + 1$ in `ℕ+` |
| `Fin.orderSucc_castSucc` | $\operatorname{succ}(\operatorname{castSucc} i) = \operatorname{succ} i$ |
| `Fin.orderSucc_last` | $\operatorname{succ}(\operatorname{last} n) = \operatorname{last} n$ |
| `Order.succ_eq_add_one` | $\operatorname{succ} m = m + 1$ in `ℕ∞` |
| `ENat.add_one_le_iff` | $m \ne \top \to (m + 1 \le n \iff m < n)$ |

The predecessor lemmas `Nat.pred_eq_pred` and `Int.pred_eq_pred` are the duals. The classes `Nat.instSuccAddOrder`, `Int.instSuccAddOrder` and `ENat.instSuccAddOrder` record that the successor is $x \mapsto x + 1$, so that a lemma about `succ` can be stated with `+ 1`. The two examples `Fin.orderSucc_last` and `ENat.succ_top` show the convention at a top element: $\operatorname{succ} \top = \top$, by the general `Order.succ_top`. So in `ℕ∞` the equivalence `ENat.add_one_le_iff` needs $m \ne \top$. The lemmas `Fin.covBy_iff` and `Int.natCast_covBy` move the covering relation through the casts to `ℕ` and to `ℤ`.

#### Adding a bottom element

The type `WithBot α` adds a new bottom $\bot$ below $\alpha$. With a successor on $\alpha$ and a bottom in $\alpha$, the instance `WithBot.instSuccOrder` gives a successor with $\operatorname{succ} \bot = \uparrow\bot$, `WithBot.orderSucc_bot`, and $\operatorname{succ} \uparrow a = \uparrow(\operatorname{succ} a)$, `WithBot.orderSucc_coe`. The module `Mathlib.Order.SuccPred.WithBot` has a second map, `WithBot.succ : WithBot α → α`, that lands in $\alpha$. It sends $\bot$ to $\bot$ and $\uparrow a$ to $\operatorname{succ} a$ (`WithBot.succ_bot`, `WithBot.succ_coe`). With `NoMaxOrder α` it is strictly monotone, `WithBot.succ_strictMono`. For `ℕ`, `withBotSucc_zero` says that it sends $0$ to $1$. The dual `WithTop.pred` sends $\top$ to $\top$.

For `WithTop α`, the instance `WithTop.instSuccOrder` sends $\uparrow a$ to $\top$ exactly when $a$ is maximal, `WithTop.succ_coe_eq_top_iff`.

#### Chains of steps

The module `Mathlib.Order.SuccPred.Relation` proves that a relation that holds at each step holds along a chain. Let $r$ be a relation with $r\,i\,(\operatorname{succ} i)$ for all $i \in [n, m)$. Then `transGen_of_succ_of_lt` gives the transitive closure of $r$ from $n$ to $m$ when $n < m$, and `reflTransGen_of_succ_of_le` gives the reflexive transitive closure when $n \le m$. These lemmas need the class `IsSuccArchimedean` of the next section, which says that $m$ is reached from $n$ by finitely many steps. In a linear order `reflTransGen_of_succ` also accepts a chain that goes down.

#### Unions over steps

A monotone map $f$ from a successor order cuts its target into the intervals $[f(i), f(\operatorname{succ} i))$. The module `Mathlib.Order.SuccPred.IntervalSucc` has three facts about them.

1. `Monotone.pairwise_disjoint_on_Ico_succ`: the intervals $[f(i), f(\operatorname{succ} i))$ are pairwise disjoint.
2. `Monotone.biUnion_Ico_Ioc_map_succ`: in an Archimedean successor order, $\bigcup_{i \in [m, n)} (f(i), f(\operatorname{succ} i)] = (f(m), f(n)]$.
3. `iUnion_Ico_map_succ_eq_Ici`: if $\alpha$ has a bottom, $f(\bot) \le f(a)$ for all $a$, and the range of $f$ is not bounded above, then the intervals $[f(a), f(\operatorname{succ} a))$ cover $[f(\bot), \infty)$.

The proof of the disjointness is short. Let $i < j$. Then $\operatorname{succ} i \le j$, so $f(\operatorname{succ} i) \le f(j)$. Each point of the first interval is below $f(\operatorname{succ} i)$, and each point of the second is at least $f(j)$. The union over all $n \in \mathbb{N}$ splits a set into the layers $\{x \mid f(n) \le g(x) < f(n + 1)\}$, one layer for each step.

#### Common errors

1. `Order.succ_le_iff` needs `[NoMaxOrder α]`. In `Fin n` or `ℕ∞` it does not apply, and a proof must use `Order.succ_le_iff_of_not_isMax` with a proof that the element is not maximal.
2. `WithBot.succ` and `Order.succ` on `WithBot α` are different maps with different targets. The first has type `WithBot α → α`, the second `WithBot α → WithBot α`, and they disagree at $\bot$.
3. `SuccOrder.ofLinearWellFoundedLT` is not an instance, so a well-founded linear order has no `Order.succ` until the definition is installed.

### Exercises

1. (A) Prove $a \lessdot \operatorname{succ} a$ for $a$ not maximal from the three fields of `SuccOrder`.
2. (A) Compute `Order.succ (3 : Fin 4)` and `Order.succ (2 : Fin 4)`, and name the lemmas that give the values.
3. (B) Show that in a partial order two `SuccOrder` structures have the same `succ`, without `Order.instSubsingletonSuccOrder`.
4. (B) Prove `Order.lt_succ_iff` in a linear order without maximal elements from `Order.succ_le_iff`.
5. (B) Use `Monotone.biUnion_Ico_Ioc_map_succ` to show that $\bigcup_{i < n} (i^2, (i+1)^2] = (0, n^2]$ in `ℕ`.
6. (C) Show that `ℚ` has no `SuccOrder` structure.

### Reference

<?reference?>
