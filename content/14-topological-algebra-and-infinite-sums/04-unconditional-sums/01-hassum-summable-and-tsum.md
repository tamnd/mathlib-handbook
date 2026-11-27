---
title: "Unconditional sums: HasSum, Summable and tsum"
kind: theory
modules:
  - Mathlib.Topology.Algebra.InfiniteSum.Defs
  - Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
explains:
  E3: [HasSum, Summable, tsum, SummationFilter]
  E2: [HasSum.unique, HasSum.tsum_eq, Summable.hasSum, HasSum.summable, tsum_eq_zero_of_not_summable, hasSum_fintype, Finset.hasSum, hasSum_sum_of_ne_finset_zero, summable_of_ne_finset_zero, Function.Injective.hasSum_iff, SummationFilter.unconditional, SummationFilter.conditional, SummationFilter.conditional_filter, SummationFilter.NeBot, SummationFilter.LeAtTop, SummationFilter.HasSupport, tsum_eq_of_summable_unconditional, hasSum_bot, Summable.mono_filter, tsum_def]
  E1: auto
families: []
requires: [V03, V13.C02, V13.C04, V15.C01, V14.C01]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Unconditional sums: HasSum, Summable and tsum

### Overview

This section defines the infinite sum of Mathlib. Let $(f_i)_{i \in I}$ be a family in a commutative topological monoid $M$, indexed by an arbitrary type $I$. The family has the sum $a$ if the finite sums $\sum_{i \in F} f_i$ come and stay close to $a$ when the finite set $F \subseteq I$ is large enough. The definition needs no order on $I$, and the sum does not depend on an enumeration of the terms. This is why it is called unconditional.

The price of the definition is that the alternating harmonic series has no unconditional sum. Mathlib keeps both notions: a *summation filter* says along which finite sets the partial sums are taken, and `SummationFilter.conditional` gives the conditional sums of a first course.

### Definitions

The finite subsets of $I$ form a directed set under inclusion: two finite sets $F$ and $G$ are both contained in $F \cup G$. Volume 13, Chapter 2, gives the filter $\mathrm{atTop}$ of a directed set. Its members are the sets that contain a tail $\{F : F \supseteq F_0\}$ for some finite $F_0$.

**Definition (Unconditional sum).** Let $M$ be a commutative monoid with a topology, $I$ a type and $f : I \to M$. For a finite set $F \subseteq I$ put $S_F = \sum_{i \in F} f(i)$. The family $f$ *has the sum* $a \in M$ if $S_F \to a$ along $\mathrm{atTop}$ on the finite subsets of $I$. In words: for each neighbourhood $U$ of $a$ there is a finite set $F_0 \subseteq I$ such that $S_F \in U$ for each finite $F \supseteq F_0$. The family is *summable* if it has some sum.

In a metric space, such as $\mathbb{R}$, the condition reads: for each $\varepsilon > 0$ there is a finite $F_0$ with $d(S_F, a) < \varepsilon$ for each finite $F \supseteq F_0$. Here $F$ ranges over all finite supersets of $F_0$, and not only over the initial segments $\{0, \dots, n-1\}$.

**Definition (The function tsum).** Let $f : I \to M$. If $f$ is summable, $\sum'_{i} f(i)$ denotes a chosen sum of $f$. If $f$ is not summable, $\sum'_{i} f(i) = 0$.

When $M$ is Hausdorff the sum is unique (Theorem 1 below), and $\sum' f$ is *the* sum. The value $0$ for a family that is not summable is a junk value. It makes `tsum` a total function, so that the expression $\sum' f$ makes sense before summability is proved.

::: mathlib
`HasSum` · `Mathlib.Topology.Algebra.InfiniteSum.Defs`

`HasSum f a L` says that `fun s : Finset β => ∑ b ∈ s, f b` tends to `𝓝 a` along the filter `L.filter` on `Finset β`. The argument `L : SummationFilter β` is optional. Its default value `SummationFilter.unconditional β` has the filter `atTop`, so `HasSum f a` is the definition of the text. The type class arguments are only `[AddCommMonoid α] [TopologicalSpace α]`: no group, no metric and no Hausdorff hypothesis.

<?decl HasSum?>
:::

::: mathlib
`Summable` · `Mathlib.Topology.Algebra.InfiniteSum.Defs`

`Summable f L` is `∃ a, HasSum f a L`. The lemma `HasSum.summable` gives `Summable f` from `HasSum f a`, and `Summable.hasSum` gives `HasSum f (∑' b, f b)` back.

<?decl Summable?>
:::

::: mathlib
`tsum` · `Mathlib.Topology.Algebra.InfiniteSum.Defs`

The notation `∑' i, f i` stands for `tsum f`, and `∑'[L] i, f i` for `tsum f L`. The definition `tsum_def` makes three cases. If `f` is not summable, the value is `0`; this is `tsum_eq_zero_of_not_summable`. If the support of `f` is finite, the value is the finite sum over the support. Otherwise the value is a sum chosen with the axiom of choice. The lemma `HasSum.tsum_eq` turns a proof of `HasSum f a` into the equation `∑' b, f b = a`, under `[T2Space α]`.

<?decl tsum?>
:::

**Definition (Summation filter).** Let $I$ be a type. A *summation filter* on $I$ is a filter $L$ on the set of finite subsets of $I$. The family $f$ has the $L$-sum $a$ if $S_F \to a$ along $L$.

The unconditional sum is the case $L = \mathrm{atTop}$. Let $I$ be a locally finite order, such as $\mathbb{N}$ or $\mathbb{Z}$, in which each interval $[m, n]$ is finite. The *conditional* summation filter is the image of the filter $\mathrm{atBot} \times \mathrm{atTop}$ under the map $(m, n) \mapsto [m, n]$. On $I = \mathbb{N}$ the lower end is eventually $0$, so the $L$-sum is the limit of the partial sums $f(0) + \cdots + f(n)$: the sum of a first course. On $I = \mathbb{Z}$ both ends move independently.

::: mathlib
`SummationFilter` · `Mathlib.Topology.Algebra.InfiniteSum.SummationFilter`

A structure with one field `filter : Filter (Finset β)`. The instances `SummationFilter.unconditional β` and `SummationFilter.conditional β` are the two filters of the text; `SummationFilter.conditional_filter` states the second one as a map of `atBot ×ˢ atTop`. The classes `L.NeBot` (the filter is proper), `L.LeAtTop` (`L.filter ≤ atTop`) and `L.HasSupport` record good behaviour.

<?decl SummationFilter?>
:::

### Theorems and proofs

**Theorem (Uniqueness).** Let $M$ be Hausdorff. If $f$ has the sums $a$ and $b$, then $a = b$. Hence $\sum' f = a$ whenever $f$ has the sum $a$.

*Proof.* The filter $\mathrm{atTop}$ on the finite subsets of $I$ is proper: each of its members contains a set $\{F : F \supseteq F_0\}$, and this set contains $F_0$, so it is not empty. A function has at most one limit along a proper filter in a Hausdorff space (Volume 13, Chapter 4). So $a = b$. If $f$ has the sum $a$, then $f$ is summable, $\sum' f$ is a sum of $f$ by definition, and the first part gives $\sum' f = a$. $\square$

::: mathlib
`HasSum.unique` · `Mathlib.Topology.Algebra.InfiniteSum.Defs`

The hypotheses are `[T2Space α]` and `[L.NeBot]`. For the unconditional filter the instance `SummationFilter.instNeBotUnconditional` gives `NeBot` at once. The lemma `hasSum_bot` shows why the hypothesis is there: along the trivial filter $\bot$ every family has every sum.

<?decl HasSum.unique?>
:::

**Theorem (Finite support).** Let $F_1 \subseteq I$ be finite and $f(i) = 0$ for $i \notin F_1$. Then $f$ has the sum $\sum_{i \in F_1} f(i)$. In particular, if $I$ is finite, $f$ has the sum $\sum_{i \in I} f(i)$.

*Proof.* Let $F \supseteq F_1$ be finite. The terms of $S_F$ with index in $F \setminus F_1$ are $0$, so $S_F = S_{F_1}$. So the function $F \mapsto S_F$ is constant on the member $\{F : F \supseteq F_1\}$ of $\mathrm{atTop}$, and it tends to its constant value. For finite $I$ take $F_1 = I$. $\square$

::: mathlib
`hasSum_sum_of_ne_finset_zero` · `Mathlib.Topology.Algebra.InfiniteSum.Defs`

The hypothesis `∀ b ∉ s, f b = 0` for a `Finset` `s`. The finite type case is `hasSum_fintype`, and `summable_of_ne_finset_zero` gives the summability alone.

<?decl hasSum_sum_of_ne_finset_zero?>
:::

**Theorem (Reindexing).** Let $e : J \to I$ be a bijection and $f : I \to M$. Then $f \circ e$ has the sum $a$ if and only if $f$ has the sum $a$. More generally, let $g : J \to I$ be injective and $f(i) = 0$ for each $i$ outside the image of $g$. Then $f \circ g$ has the sum $a$ if and only if $f$ has the sum $a$.

*Proof.* Prove the general form. For a finite $G \subseteq J$, $g(G)$ is finite and $\sum_{j \in G} f(g(j)) = \sum_{i \in g(G)} f(i)$, since $g$ is injective.

Assume $f$ has the sum $a$, and let $U$ be a neighbourhood of $a$. Choose a finite $F_0 \subseteq I$ with $S_F \in U$ for each finite $F \supseteq F_0$. Put $G_0 = g^{-1}(F_0)$, a finite set since $g$ is injective. For a finite $G \supseteq G_0$, the set $F = g(G) \cup F_0$ contains $F_0$, so $S_F \in U$. The indices in $F_0 \setminus g(G)$ lie outside the image of $g$ or are images of points outside $G$; a point $g(j) \in F_0$ has $j \in G_0 \subseteq G$, so only the first case occurs, and there $f = 0$. Hence $S_F = S_{g(G)} = \sum_{j \in G} f(g(j))$, and this sum lies in $U$.

Conversely, assume $f \circ g$ has the sum $a$, let $U$ be a neighbourhood of $a$, and choose a finite $G_0$ for $U$. Put $F_0 = g(G_0)$. For a finite $F \supseteq F_0$ let $G = g^{-1}(F)$, a finite set that contains $G_0$. The terms of $S_F$ with index outside $g(J)$ are $0$, so $S_F = S_{g(G)} = \sum_{j \in G} f(g(j)) \in U$. $\square$

::: mathlib
`Function.Injective.hasSum_iff` · `Mathlib.Topology.Algebra.InfiniteSum.Defs`

The general form of the theorem, with the hypothesis `∀ x ∉ Set.range g, f x = 0`. The bijective form is `Equiv.hasSum_iff`, with `Equiv.summable_iff` and `Equiv.tsum_eq`; Section 2 lists them.

<?decl Function.Injective.hasSum_iff?>
:::

**Proposition (Nonnegative real terms).** Let $f : \mathbb{N} \to \mathbb{R}$ with $f(n) \ge 0$ for all $n$, and let $s_n = f(0) + \cdots + f(n-1)$. Then $f$ has the unconditional sum $a$ if and only if $s_n \to a$.

*Proof.* Assume $f$ has the sum $a$. Each finite $F_0 \subseteq \mathbb{N}$ lies in $\{0, \dots, n-1\}$ for $n$ large, so the sets $\{0, \dots, n-1\}$ tend to $\mathrm{atTop}$ as $n \to \infty$. By composition of limits, $s_n \to a$. This direction does not use $f \ge 0$.

Conversely, assume $s_n \to a$. The sequence $s_n$ is increasing since $f \ge 0$, so $s_n \le a$ for all $n$. Let $\varepsilon > 0$ and choose $N$ with $s_N > a - \varepsilon$. Put $F_0 = \{0, \dots, N-1\}$. Let $F \supseteq F_0$ be finite and choose $M \ge N$ with $F \subseteq \{0, \dots, M-1\}$. Since the terms are nonnegative, $s_N = S_{F_0} \le S_F \le s_M \le a$. So $a - \varepsilon < S_F \le a$. $\square$

::: mathlib
`hasSum_iff_tendsto_nat_of_nonneg` · `Mathlib.Topology.Algebra.InfiniteSum.ENNReal`

The proposition for real terms. The direction that holds for all terms is `HasSum.tendsto_sum_nat` of Section 3. In a normed group the converse holds when the norms are summable: `hasSum_iff_tendsto_nat_of_summable_norm`.

<?decl hasSum_iff_tendsto_nat_of_nonneg?>
<?decl hasSum_iff_tendsto_nat_of_summable_norm?>
:::

### Examples

**Example (A telescoping sum).** Let $f(n) = \dfrac{1}{(n+1)(n+2)}$ for $n \in \mathbb{N}$. Since $\dfrac{1}{(n+1)(n+2)} = \dfrac{1}{n+1} - \dfrac{1}{n+2}$, the partial sums telescope: $s_N = 1 - \dfrac{1}{N+1}$. So $s_N \to 1$. The terms are positive, so the proposition gives the unconditional sum $1$, and $\sum'_{n} f(n) = 1$. For instance $F_0 = \{0, \dots, 99\}$ has $S_{F_0} = 100/101$, and every finite $F \supseteq F_0$ has $|S_F - 1| \le 1/101$.

**Example (The alternating harmonic series).** Let $f(n) = (-1)^{n+1}/n$ for $n \ge 1$ and $f(0) = 0$. The partial sums $1 - \tfrac12 + \tfrac13 - \cdots$ converge, by the test of Leibniz in Volume 15, Chapter 1, and their limit is $\log 2$. So $f$ has the conditional sum $\log 2$. It has no unconditional sum.

*Proof.* Assume that $f$ has the sum $a$. Choose a finite $F_0$ with $|S_F - a| < \tfrac14$ for every finite $F \supseteq F_0$. Then $|S_F - S_{F_0}| < \tfrac12$ for every such $F$. Let $N$ be larger than every element of $F_0$. The odd numbers $n > N$ have $f(n) = 1/n > 0$, and $\sum_{n > N, \, n \text{ odd}} 1/n$ diverges, since $\frac{1}{2k+1} \ge \frac{1}{2(k+1)}$ and the harmonic series diverges. Choose $M$ such that the set $T$ of odd $n$ with $N < n \le M$ has $\sum_{n \in T} 1/n \ge 1$. Put $F = F_0 \cup T$. Then $S_F - S_{F_0} = \sum_{n \in T} 1/n \ge 1$, a contradiction. $\square$


::: mathlib
`SummationFilter.conditional` · `Mathlib.Topology.Algebra.InfiniteSum.SummationFilter`

With `L = SummationFilter.conditional ℕ`, the statement `HasSum f (Real.log 2) L` is the classical one, and `Summable f` (unconditional) is false. The lemma `tsum_eq_of_summable_unconditional` says that the two sums agree when the unconditional sum exists, under `[L.NeBot] [L.LeAtTop]`; `Summable.mono_filter` transfers summability to a finer filter.

<?decl SummationFilter.conditional?>
<?decl tsum_eq_of_summable_unconditional?>
:::


**Remark (Common errors).** The first error is to read $\sum' f = a$ as "$f$ is summable with sum $a$". An equation $\sum' f = 0$ holds for every family that is not summable, such as $f(n) = n$ or $f(n) = 1/n$ in $\mathbb{R}$, so a proof of summability is needed before the equation carries meaning. The second error is to forget the summability hypotheses of the rules. The rule $\sum'(f + g) = \sum' f + \sum' g$ needs $f$ and $g$ summable. For $f(n) = n + 2^{-n}$ and $g(n) = -n$ in $\mathbb{R}$, neither $f$ nor $g$ is summable, so the right side is $0 + 0 = 0$, while $f + g = 2^{-n}$ has the sum $2$. The third error is to expect that a convergent series of a first course is `Summable`. It is, for real terms, only when it converges absolutely.

### The library around it

The file `Mathlib.Topology.Algebra.InfiniteSum.Defs` holds the three definitions, their multiplicative versions `HasProd`, `Multipliable` and `tprod` of Chapter 7, and the first lemmas. Each lemma is stated once for products with the attribute `to_additive`, which generates the version for sums; so every name of the form `hasProd_*` has a twin `hasSum_*`. The file `Mathlib.Topology.Algebra.InfiniteSum.SummationFilter` defines the filters and their instances.

### Exercises

1. (A) Show that the constant family $f(i) = 0$ on any type has the sum $0$, and that $\sum'_{i} 0 = 0$.
2. (A) Let $b \in I$ and $f(i) = c$ for $i = b$ and $f(i) = 0$ otherwise. Show that $f$ has the sum $c$. *Hint:* use the finite support theorem with $F_1 = \{b\}$.
3. (A) Compute $\sum_{n \ge 0} \frac{1}{(n+1)(n+3)}$ as an unconditional sum. *Hint:* split into partial fractions; the answer is $\tfrac34$.
4. (A) Let $M = \mathbb{Z}$ with the discrete topology. Show that $f : I \to \mathbb{Z}$ is summable if and only if its support is finite. *Hint:* the neighbourhood $\{a\}$ of the sum forces $S_F = a$ for all large $F$.
5. (B) Let $I$ be uncountable and $f : I \to \mathbb{R}$ summable. Show that the set $\{i : f(i) \ne 0\}$ is countable. *Hint:* for each $k \ge 1$, show that only finitely many $i$ have $|f(i)| > 1/k$, using the set $F_0$ for $\varepsilon = 1/(2k)$.
6. (B) Show that $f(n) = (-1)^n/(n+1)$ is not summable by the method of the alternating harmonic series, and that the $L$-sum for $L$ the conditional filter exists.
7. (C) Let $L$ be the filter on the finite subsets of $\mathbb{Z}$ generated by the symmetric intervals $[-N, N]$. Show that $f(n) = n$ has the $L$-sum $0$, while $f$ has no conditional sum and no unconditional sum.

### Notes and history

The definition of a sum as a limit along the finite subsets of the index set is in Bourbaki, *General Topology*, Chapter III, §5, where these families are called summable families. Moore and Smith introduced limits along directed sets in 1922, and the unconditional sum is one of their first examples. The theorem that a real series converges unconditionally exactly when it converges absolutely goes back to Dirichlet and Riemann; Chapter 5 proves it.

### Reference

<?reference?>
