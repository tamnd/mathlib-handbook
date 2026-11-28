---
title: Limit elements, normal functions and transfinite iteration
kind: api
modules:
  - Mathlib.Order.SuccPred.Limit
  - Mathlib.Order.SuccPred.CompleteLinearOrder
  - Mathlib.Order.SuccPred.InitialSeg
  - Mathlib.Order.IsNormal
  - Mathlib.Order.TransfiniteIteration
explains:
  E2: [Order.IsSuccPrelimit, Order.IsSuccLimit, Order.isMin_or_mem_range_succ_or_isSuccLimit, SuccOrder.limitRecOn, Order.IsSuccLimit.sSup_Iio, Order.IsNormal, Order.isNormal_iff, Order.IsNormal.iSup_iterate_mem_fixedPoints, supTransfiniteIterate, top_mem_range_supTransfiniteIterate]
  E1: auto
families: []
requires: [V04.C01, V04.C02, V04.C04, V04.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Limit elements, normal functions and transfinite iteration

### Overview

The ordinal $\omega$ is not the successor of any ordinal, and it is not $0$. It is the supremum of the ordinals below it. Such an element is a limit. In a well-founded linear order each element is of one of three kinds: minimal, a successor, or a limit. A proof by transfinite induction treats the three cases, and a definition by transfinite recursion gives a value in each case. The ordinal functions $\alpha \mapsto \beta + \alpha$ and $\alpha \mapsto \omega^\alpha$ are defined in this way, and they are continuous at limits: the value at a limit is the supremum of the earlier values. Such functions are called normal.

Mathlib states these notions for an arbitrary order, not only for the ordinals. The module `Mathlib.Order.SuccPred.Limit` defines limits and the recursion, `Mathlib.Order.SuccPred.CompleteLinearOrder` relates limits to suprema, `Mathlib.Order.SuccPred.InitialSeg` shows that initial segment embeddings keep successors and limits, `Mathlib.Order.IsNormal` defines normal functions, and `Mathlib.Order.TransfiniteIteration` iterates a map on a complete lattice along a well-ordered index type. The ordinal applications are in the set theory volume.

### The library around it

#### Limits and prelimits

Mathlib uses two notions, both phrased with the covering relation $b \lessdot a$, which says that $b < a$ and nothing lies strictly between.

1. `Order.IsSuccPrelimit a` means that no $b$ satisfies $b \lessdot a$: the element covers nothing.
2. `Order.IsSuccLimit a` is a structure with two parts: $a$ is not minimal, and $a$ is a prelimit. `Order.isSuccLimit_iff` states the equivalence with the conjunction, and `Order.IsSuccLimit.isSuccPrelimit` forgets the first part.

A minimal element is a prelimit, since nothing lies below it. So in `ℕ` the only prelimit is $0$, and there is no limit. The definitions do not mention `Order.succ`, so they make sense in each preorder. In a dense order each element is a prelimit, `Order.IsSuccPrelimit.of_dense`. The dual notions `Order.IsPredPrelimit` and `Order.IsPredLimit` use $a \lessdot b$, and `Order.isSuccLimit_toDual_iff` exchanges them through the order dual.

With a successor order the definitions get a second form.

| Lean name | Statement |
|---|---|
| `Order.isSuccPrelimit_iff_succ_ne` | prelimit iff $\operatorname{succ} b \ne a$ for all $b$, with `NoMaxOrder α` |
| `Order.not_isSuccPrelimit_iff_mem_range_succ` | not a prelimit iff $a$ is a successor, with `NoMaxOrder α` |
| `Order.not_isSuccLimit_succ` | a successor is not a limit, with `NoMaxOrder α` |
| `Order.isMin_or_mem_range_succ_or_isSuccLimit` | $a$ is minimal, a successor, or a limit |
| `Order.IsSuccLimit.succ_lt` | $b < a$ gives $\operatorname{succ} b < a$ at a limit $a$ |
| `Order.IsSuccLimit.isLUB_Iio` | a limit is the least upper bound of $(-\infty, a)$ |
| `Order.isLUB_Iio_iff_isSuccPrelimit` | in a linear order, $a = \sup\,(-\infty, a)$ iff $a$ is a prelimit |
| `Order.not_isSuccLimit_of_isSuccArchimedean` | an Archimedean order has no limits |

The trichotomy has a short proof. If $a$ is not minimal and not a limit, then $a$ is not a prelimit, so some $b$ satisfies $b \lessdot a$. Then $b$ is not maximal, and $b \lessdot \operatorname{succ} b$. Two elements that cover $b$ in a partial order with a successor are equal, since $\operatorname{succ} b \le a$ and nothing lies strictly between $b$ and $a$. So $a = \operatorname{succ} b$.

The proof of `Order.IsSuccLimit.succ_lt` is also short. From $b < a$ the successor axiom gives $\operatorname{succ} b \le a$. Equality would make $a$ the successor of $b$, and $b$ is not maximal because $b < a$, so $b \lessdot a$, which a prelimit forbids.

#### Recursion on limits

Two recursors split a goal by the trichotomy.

1. `Order.isSuccLimitRecOn b` needs no well-foundedness. It takes a case for minimal elements, a case for $\operatorname{succ} a$ with $a$ not maximal, and a case for limits, and gives a value at $b$. It is a case split, not a recursion.
2. `SuccOrder.limitRecOn b`, with `WellFoundedLT α`, is a recursion. The successor case gets the value at $a$, and the limit case gets the values at all $c < a$.

The computation rules are `SuccOrder.limitRecOn_isMin`, `SuccOrder.limitRecOn_succ_of_not_isMax` (in a linear order) and `SuccOrder.limitRecOn_of_isSuccLimit`. The variants with prelimits, `Order.isSuccPrelimitRecOn` and `SuccOrder.prelimitRecOn`, merge the minimal case into the limit case. The dual `PredOrder.colimitRecOn` recurses down in an order where $>$ is well founded.

#### Limits and suprema

In a complete linear order the limits are exactly the points that are suprema without being attained.

| Lean name | Statement |
|---|---|
| `Order.IsSuccLimit.sSup_Iio` | at a limit $x$, $\sup\,(-\infty, x) = x$, in a conditionally complete lattice |
| `Order.IsSuccLimit.iSup_Iio` | the same as an indexed supremum over the subtype |
| `sSup_Iio_eq_self_iff_isSuccPrelimit` | with a bottom, $\sup\,(-\infty, x) = x \iff x$ is a prelimit |
| `sSup_mem_of_not_isSuccPrelimit` | if $\sup s$ is not a prelimit, then $\sup s \in s$ |
| `csSup_mem_of_not_isSuccLimit` | the conditional form, for $s$ nonempty and bounded above |
| `exists_eq_iSup_of_not_isSuccPrelimit` | the indexed form: some $f(i)$ equals $\sup_i f(i)$ |
| `Order.IsSuccPrelimit.sSup_lt_iff` | at a prelimit $x$, $\sup s < x$ iff some $a < x$ bounds $s$ strictly |

The proof of `sSup_mem_of_not_isSuccPrelimit` runs as follows. Let $x = \sup s$, and let $b \lessdot x$. If $x \notin s$, then each element of $s$ is below $x$, hence at most $b$ in a linear order, because nothing lies between $b$ and $x$. So $b$ is an upper bound of $s$, and $x \le b$, which contradicts $b < x$.

#### Initial segments

An initial segment embedding `f : α ≤i β` is an order embedding whose image is downward closed. It keeps the structure of this section. `InitialSeg.map_isSuccLimit` and `InitialSeg.isSuccLimit_apply_iff` say that $f(a)$ is a limit if and only if $a$ is a limit. `InitialSeg.apply_covBy_apply_iff` keeps the covering relation, and `InitialSeg.map_succ` gives $f(\operatorname{succ} a) = \operatorname{succ}(f(a))$ when $\alpha$ has no maximum. The principal segments `α <i β` have the same lemmas, `PrincipalSeg.map_succ` and `PrincipalSeg.isSuccLimit_apply_iff`.

#### Normal functions

The structure `Order.IsNormal f`, for a map $f$ between linear orders, has two fields: $f$ is strictly monotone, and at each limit $a$, $f(a)$ is below each upper bound of $f((-\infty, a))$. The form that a proof uses is `Order.isNormal_iff`:
$$\operatorname{IsNormal} f \iff \operatorname{StrictMono} f \land \forall o,\ \operatorname{IsSuccLimit} o \to \forall a,\ (\forall b < o,\ f(b) \le a) \to f(o) \le a.$$
With monotonicity, the second field says that $f(a)$ is the least upper bound of $f((-\infty, a))$ at a limit.

| Lean name | Statement |
|---|---|
| `Order.IsNormal.id` | the identity is normal |
| `Order.IsNormal.comp` | if $g$ and $f$ are normal, then $g \circ f$ is normal |
| `OrderIso.isNormal` | an order isomorphism is normal |
| `InitialSeg.isNormal` | an initial segment embedding is normal |
| `Order.IsNormal.of_succ_lt` | in a well order, $f(a) < f(\operatorname{succ} a)$ and continuity at limits give normality |
| `Order.IsNormal.map_isSuccLimit` | a normal function sends limits to limits |
| `Order.IsNormal.le_iff_forall_le` | at a limit $a$, $f(a) \le b \iff \forall a' < a,\ f(a') \le b$ |
| `LeftOrdContinuous.map_csSup` | $f(\sup s) = \sup f(s)$ for $s$ nonempty and bounded above |
| `Order.IsNormal.apply_of_isSuccLimit` | $f(a) = \sup_{b < a} f(b)$ at a limit $a$ |
| `Order.isNormal_iff_dirSupClosed_range` | in a well order, a strictly monotone $f$ is normal iff its range is closed under directed suprema |

The test `Order.IsNormal.of_succ_lt` is the one used for ordinal functions: it is enough to check the successor step and the limit step. The proof of strict monotonicity is a transfinite induction on the larger argument: the successor step uses $f(a) < f(\operatorname{succ} a)$, and the limit step uses that $f(a)$ is the least upper bound of the earlier values.

The fixed point lemma `Order.IsNormal.iSup_iterate_mem_fixedPoints` says: in a conditionally complete linear well order, if $f$ is normal and the orbit $a, f(a), f(f(a)), \dots$ is bounded, then $x = \sup_n f^{[n]}(a)$ is a fixed point. If the orbit has a largest element, it is fixed. Otherwise $x$ is the supremum of a strictly increasing sequence, and continuity gives $f(x) = \sup_n f^{[n+1]}(a) = x$. For ordinals this produces the fixed points of $\alpha \mapsto \omega^\alpha$, such as $\varepsilon_0$. The lemma `Order.IsNormal.exists_map_le_lt_map_succ` locates each $x \ge f(\bot)$ between two consecutive values: $f(a) \le x < f(\operatorname{succ} a)$.

#### Transfinite iteration

Let $\varphi : I \to I$ be a map on a type with suprema, and let $J$ be a well-ordered index type. The definition `supTransfiniteIterate φ j i₀` builds a value for each $j \in J$ by `SuccOrder.limitRecOn`, with the successor `SuccOrder.ofLinearWellFoundedLT J`:

1. at a minimal $j$, the value is $i_0$, `supTransfiniteIterate_bot`;
2. at $\operatorname{succ} j$, the value is $\varphi$ of the value at $j$, `supTransfiniteIterate_succ`, for $J$ without a maximum;
3. at a limit $j$, the value is the supremum of the values at $k < j$, `supTransfiniteIterate_limit`.

The dual `infTransfiniteIterate` takes infima at limits, and `supTransfiniteIterate_dual` relates the two through the order dual. In a complete lattice, `supTransfiniteIterate_monotone` says that the values increase with $j$ when $\varphi$ is inflationary, $i \le \varphi(i)$, and `infTransfiniteIterate_antitone` is the dual.

The main result is `top_mem_range_supTransfiniteIterate`. Assume $i < \varphi(i)$ for each $i \ne \top$ and $\varphi(\top) = \top$. If the map $j \mapsto$ the value at $j$ is not injective, then the iteration reaches $\top$ at some $j$. The proof: the values increase, so two equal values at $j < k$ give $v_j \le v_{\operatorname{succ} j} \le v_k = v_j$, where $v_j$ is the value at $j$. Then that value is fixed by $\varphi$, and the only fixed point is $\top$. A cardinality argument gives the hypothesis: if $J$ has more elements than $I$, the map cannot be injective. The source plans to use it in Grothendieck abelian categories, to write each monomorphism as a transfinite composition of pushouts of a set of monomorphisms.

The older names without the `sup` prefix are deprecated aliases of these lemmas.

#### Common errors

1. A minimal element is a prelimit but not a limit. A lemma about `IsSuccPrelimit` covers $\bot$, and a lemma about `IsSuccLimit` does not. In `ℕ`, $0$ is a prelimit.
2. `supTransfiniteIterate_succ` needs `NoMaxOrder J`, because the successor of a maximal index is the index itself. For a bounded index type such as an ordinal $\mathrm{Iio}\ \alpha$, the step from a non maximal index uses `supTransfiniteIterate_succ_of_not_isMax`.
3. `Order.IsNormal` asks for strict monotonicity. The map $\alpha \mapsto \alpha \cdot 0$ is continuous at limits but not normal, and a constant map is never normal on a nontrivial order.

### Exercises

1. (A) Show that in `ℤ` no element is a prelimit, and that in `ℕ` the only prelimit is $0$.
2. (A) Show that each element of `ℚ` is a prelimit and none is minimal, so each element of `ℚ` is a limit.
3. (B) Prove `Order.IsNormal.comp` from `Order.isNormal_iff`.
4. (B) Prove `sSup_mem_of_not_isSuccPrelimit` for a complete linear order, following the proof above.
5. (B) Compute `supTransfiniteIterate φ j i₀` for $J = \mathbb{N}$, and show that it is $\varphi^{[j]}(i_0)$.
6. (C) Let $\varphi$ be inflationary on a complete lattice $I$ and let $J$ be a well order with more elements than $I$. Show that some value of the iteration is a fixed point of $\varphi$.

### Reference

<?reference?>
