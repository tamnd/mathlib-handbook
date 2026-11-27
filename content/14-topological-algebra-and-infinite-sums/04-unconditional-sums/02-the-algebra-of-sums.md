---
title: The algebra of infinite sums
kind: theory
modules:
  - Mathlib.Topology.Algebra.InfiniteSum.Basic
  - Mathlib.Topology.Algebra.InfiniteSum.Group
  - Mathlib.Topology.Algebra.InfiniteSum.Module
  - Mathlib.Topology.Algebra.InfiniteSum.Field
  - Mathlib.Topology.Algebra.InfiniteSum.Constructions
explains:
  E3: [HasSum.add, HasSum.map, summable_iff_cauchySeq_finset, summable_iff_vanishing, HasSum.sigma]
  E2: [Summable.add, Summable.tsum_add, HasSum.neg, HasSum.sub, Summable.tsum_sub, HasSum.const_smul, Summable.tsum_const_smul, Summable.map_tsum, ContinuousLinearMap.map_tsum, Equiv.hasSum_iff, Equiv.summable_iff, Equiv.tsum_eq, HasSum.add_compl, Summable.tsum_add_tsum_compl, Summable.vanishing, Summable.tendsto_cofinite_zero, Summable.comp_injective, Summable.subtype, Summable.sigma, Summable.tsum_sigma, Summable.tsum_sigma', Summable.tsum_prod, Summable.prod_factor, Summable.tsum_comm, Summable.tsum_finsetSum, hasSum_single, tsum_ite_eq]
  E1: auto
families: []
requires: [V03, V13.C04, V13.C07, V14.C01, V14.C03]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The algebra of infinite sums

### Overview

The finite sums of Volume 3 obey a list of rules: they are additive in the family, they commute with additive maps, and a sum over a disjoint union or a product splits into an iterated sum. This section proves the same rules for the unconditional sums of Section 1, and it shows which hypothesis each rule needs. Additivity needs continuity of addition. The image under an additive map needs continuity of the map. The splitting of a sum over a sigma type needs a regular space, or a complete group.

The main tool is the Cauchy criterion. In a complete commutative topological group, a family is summable if and only if the sums over finite sets far from a fixed finite set are small. From it follow two facts that have no analogue for conditional sums: each subfamily of a summable family is summable, and the terms of a summable family tend to $0$ along the cofinite filter.

### Definitions

The section needs one definition, the vanishing condition of Cauchy.

**Definition (Cauchy condition for a family).** Let $G$ be a commutative topological group and $f : I \to G$. The family $f$ satisfies the *Cauchy condition* if for each neighbourhood $U$ of $0$ there is a finite set $F_0 \subseteq I$ such that $\sum_{i \in T} f(i) \in U$ for each finite set $T$ disjoint from $F_0$.

In $\mathbb{R}$ the condition reads: for each $\varepsilon > 0$ there is a finite $F_0$ such that $\left|\sum_{i \in T} f(i)\right| < \varepsilon$ for every finite $T$ with $T \cap F_0 = \emptyset$. For $I = \mathbb{N}$ the sets $T$ are all finite subsets of a tail, not only its blocks $\{N, \dots, M\}$.

::: mathlib
`summable_iff_vanishing` · `Mathlib.Topology.Algebra.InfiniteSum.Group`

The statement `Summable f ↔ ∀ e ∈ 𝓝 0, ∃ s, ∀ t, Disjoint t s → ∑ b ∈ t, f b ∈ e`, for `[IsUniformAddGroup α] [CompleteSpace α]`. The direction from left to right, `Summable.vanishing`, holds in every topological group, with no completeness.

<?decl summable_iff_vanishing?>
:::

### Theorems and proofs

**Theorem (Additivity).** Let $M$ be a commutative monoid with continuous addition. If $f$ has the sum $a$ and $g$ has the sum $b$, then $f + g$ has the sum $a + b$. If $M$ is also Hausdorff and $f$, $g$ are summable, then $\sum'(f + g) = \sum' f + \sum' g$.

*Proof.* For each finite $F$, $S_F(f + g) = S_F(f) + S_F(g)$, a finite sum rule. The map $F \mapsto (S_F(f), S_F(g))$ tends to $(a, b)$ in $M \times M$, since each coordinate does. Addition $M \times M \to M$ is continuous at $(a, b)$, so $S_F(f + g) \to a + b$. The second claim follows by uniqueness: $f + g$ has the sum $\sum' f + \sum' g$, so this is $\sum'(f + g)$. $\square$

In a topological group the same proof, with the continuity of $x \mapsto -x$ and of $(x, y) \mapsto x - y$, gives $-f$ the sum $-a$ and $f - g$ the sum $a - b$.

::: mathlib
`HasSum.add` · `Mathlib.Topology.Algebra.InfiniteSum.Basic`

The hypothesis is `[ContinuousAdd α]`. The forms with `Summable` and `tsum` are `Summable.add` and `Summable.tsum_add`; the second needs `[T2Space α]` and the two summability proofs. The group forms are `HasSum.neg`, `HasSum.sub` and `Summable.tsum_sub` in `Mathlib.Topology.Algebra.InfiniteSum.Group`. The unprimed name `tsum_add`, with no namespace, is a different lemma of Chapter 5: it holds without summability in a complete lattice such as $[0, \infty]$.

<?decl HasSum.add?>
:::

**Theorem (Continuous additive maps).** Let $\varphi : M \to N$ be a continuous homomorphism of commutative topological monoids. If $f$ has the sum $a$, then $\varphi \circ f$ has the sum $\varphi(a)$. If $N$ is Hausdorff and $f$ is summable, then $\varphi\left(\sum' f\right) = \sum' (\varphi \circ f)$.

*Proof.* For finite $F$, $\varphi(S_F(f)) = S_F(\varphi \circ f)$, since $\varphi$ preserves finite sums. The left side tends to $\varphi(a)$ by continuity of $\varphi$. The second claim follows from the first with $a = \sum' f$ and uniqueness in $N$. $\square$

The theorem has many special cases. Multiplication by a fixed scalar $c$ in a topological module is a continuous additive map, so $\sum' c f = c \sum' f$. The coordinate maps of a product, the evaluation maps $g \mapsto g(x)$ and the continuous linear maps are other cases.

::: mathlib
`HasSum.map` · `Mathlib.Topology.Algebra.InfiniteSum.Basic`

The map is any `g : G` of a type with `[AddMonoidHomClass G α γ]`, together with a proof of `Continuous g`. So the lemma applies to bundled additive maps, ring homomorphisms and linear maps alike. The `tsum` form is `Summable.map_tsum`. The scalar forms are `HasSum.const_smul` and `Summable.tsum_const_smul`, which need only `[ContinuousConstSMul γ α]`; the linear form is `ContinuousLinearMap.map_tsum` in `Mathlib.Topology.Algebra.InfiniteSum.Module`.

<?decl HasSum.map?>
:::

**Theorem (Cauchy criterion).** Let $G$ be a commutative topological group with its uniform structure from Chapter 3.

1. If $f : I \to G$ is summable, then $f$ satisfies the Cauchy condition.
2. If $G$ is complete and $f$ satisfies the Cauchy condition, then $f$ is summable.

*Proof.* Recall from Chapter 3 that the net $F \mapsto S_F$ is Cauchy if and only if for each neighbourhood $V$ of $0$ there is a finite $F_0$ with $S_F - S_{F'} \in V$ for all finite $F, F' \supseteq F_0$.

(1) Let $f$ have the sum $a$ and let $U$ be a neighbourhood of $0$. By continuity of subtraction choose a neighbourhood $W$ of $0$ with $W - W \subseteq U$. Choose $F_0$ with $S_F \in a + W$ for all finite $F \supseteq F_0$. Let $T$ be finite and disjoint from $F_0$. Then $S_T = S_{F_0 \cup T} - S_{F_0}$, and both terms lie in $a + W$, so $S_T \in W - W \subseteq U$.

(2) Assume the Cauchy condition, and let $V$ be a neighbourhood of $0$. Choose $W$ with $W - W \subseteq V$, and $F_0$ for $W$ as in the Cauchy condition. Let $F, F' \supseteq F_0$ be finite. The common part $F \cap F'$ cancels in the difference: $S_F - S_{F'} = S_{F \setminus F'} - S_{F' \setminus F}$. The two sets $F \setminus F'$ and $F' \setminus F$ are disjoint from $F_0$, since $F_0 \subseteq F \cap F'$. So both sums lie in $W$, and $S_F - S_{F'} \in V$. The net $F \mapsto S_F$ is Cauchy. Since $G$ is complete, it converges, and its limit is a sum of $f$. $\square$

::: mathlib
`summable_iff_cauchySeq_finset` · `Mathlib.Topology.Algebra.InfiniteSum.Group`

The form "summable if and only if the net of finite sums is a `CauchySeq`". Mathlib uses the name `CauchySeq` for any map from a directed set, here `Finset β`.

<?decl summable_iff_cauchySeq_finset?>
:::

**Corollary (Subfamilies and terms).** Let $G$ be a complete commutative topological group and $f : I \to G$ summable.

1. For each subset $J \subseteq I$, the restriction $f|_J$ is summable. More generally $f \circ g$ is summable for each injective $g : K \to I$.
2. The terms tend to $0$ along the cofinite filter: for each neighbourhood $U$ of $0$, $f(i) \in U$ for all but finitely many $i$.

*Proof.* (1) Let $U$ be a neighbourhood of $0$, and let $F_0$ be as in the Cauchy condition for $f$. Put $K_0 = g^{-1}(F_0)$, a finite set. Let $T \subseteq K$ be finite and disjoint from $K_0$. Then $g(T)$ is disjoint from $F_0$, and $\sum_{k \in T} f(g(k)) = S_{g(T)}(f) \in U$ since $g$ is injective. So $f \circ g$ satisfies the Cauchy condition, and it is summable by part 2 of the theorem. A subset $J$ is the case where $g$ is the inclusion.

(2) Take $T = \{i\}$ for $i \notin F_0$. Then $f(i) = S_T \in U$. This part needs no completeness. $\square$

::: mathlib
`Summable.comp_injective` · `Mathlib.Topology.Algebra.InfiniteSum.Group`

Part 1, with the subset form `Summable.subtype`. Both need `[IsUniformAddGroup α] [CompleteSpace α]`. Part 2 is `Summable.tendsto_cofinite_zero` and needs only `[IsTopologicalAddGroup G]`.

<?decl Summable.comp_injective?>
:::

**Theorem (Sums over a sigma type).** Let $M$ be a commutative topological monoid with continuous addition that is a regular space. Let $(I_b)_{b \in B}$ be a family of types and $f$ a function on the disjoint union $\Sigma_b I_b$. Assume that $f$ has the sum $a$, and that for each $b$ the fibre $c \mapsto f(b, c)$ has the sum $g(b)$. Then $g$ has the sum $a$. In words: $\sum_{(b, c)} f(b, c) = \sum_b \sum_c f(b, c)$.

*Proof.* Let $U$ be a neighbourhood of $a$. Since $M$ is regular, $U$ contains a closed neighbourhood $V$ of $a$ (Volume 13, Chapter 4). Choose a finite $F_0 \subseteq \Sigma_b I_b$ with $S_F(f) \in V$ for all finite $F \supseteq F_0$. Let $T_0$ be the finite set of first coordinates of the points of $F_0$. Fix a finite $T \supseteq T_0$. For each $b \in T$ let $C_b$ run through the finite subsets of $I_b$ that contain the fibre $\{c : (b, c) \in F_0\}$. The set $F = \{(b, c) : b \in T, c \in C_b\}$ contains $F_0$, so
$$\sum_{b \in T} \sum_{c \in C_b} f(b, c) = S_F(f) \in V.$$
As each $C_b$ grows, $\sum_{c \in C_b} f(b, c) \to g(b)$. The set $T$ is finite and addition is continuous, so the left side tends to $\sum_{b \in T} g(b)$ along the product of the filters $\mathrm{atTop}$ on the sets $C_b$. Every value lies in the closed set $V$, so the limit lies in $V$ too. So $\sum_{b \in T} g(b) \in V \subseteq U$ for every finite $T \supseteq T_0$, and $g$ has the sum $a$. $\square$

In a complete Hausdorff group the fibres are summable by the corollary, so only the summability of $f$ is needed. The product $B \times C$ is the sigma type with constant fibres, and the theorem gives $\sum_{(b, c)} f(b, c) = \sum_b \sum_c f(b, c) = \sum_c \sum_b f(b, c)$ for a summable $f$ on $B \times C$.

::: mathlib
`HasSum.sigma` · `Mathlib.Topology.Algebra.InfiniteSum.Constructions`

The theorem, with `[ContinuousAdd α] [RegularSpace α]`. The `tsum` form `Summable.tsum_sigma'` takes the summability of the fibres as a hypothesis and needs `[T3Space α]`. In a complete group `Summable.sigma` gives the summability of the outer sum, `Summable.tsum_sigma` and `Summable.tsum_prod` give the equations from the summability of `f` alone, `Summable.prod_factor` gives the fibres, and `Summable.tsum_comm` exchanges the two sums.

<?decl HasSum.sigma?>
:::

### Examples

**Example (A double sum).** Let $f(m, n) = 2^{-m} 3^{-n}$ on $\mathbb{N} \times \mathbb{N}$. The family is positive, and its sums over the squares $\{0, \dots, N\}^2$ are bounded by $2 \cdot \tfrac32 = 3$; by Chapter 5, it is summable in $\mathbb{R}$. The theorem on sigma types gives
$$\sum'_{(m, n)} 2^{-m} 3^{-n} = \sum'_m 2^{-m} \sum'_n 3^{-n} = \sum'_m 2^{-m} \cdot \tfrac32 = \tfrac32 \cdot 2 = 3.$$

**Example (A subfamily in an incomplete group).** Let $0.d_1 d_2 d_3 \ldots$ be the decimal expansion of $\sqrt2 - 1$. Define $f : \mathbb{N} \to \mathbb{Q}$ by $f(2n) = d_n 10^{-n}$ and $f(2n+1) = -d_n 10^{-n}$, with $d_0 = 0$. In $\mathbb{R}$ the family is summable, since $\sum |f| \le 2 \sum 9 \cdot 10^{-n}$ is finite (Chapter 5), and its sum is $0$, since the terms cancel in pairs. The inclusion $\mathbb{Q} \to \mathbb{R}$ is a topological embedding, so $f$ has the sum $0$ in $\mathbb{Q}$ as well. The subfamily over the even indices has the sum $\sqrt2 - 1$ in $\mathbb{R}$, which is not rational, so it has no sum in $\mathbb{Q}$. Completeness cannot be dropped from the corollary.

**Example (Iterated sums that differ).** Let $f(m, n) = 1$ if $n = m$, $f(m, n) = -1$ if $n = m + 1$, and $f(m, n) = 0$ otherwise. Each row $m$ has the two nonzero terms $1$ and $-1$, so $\sum_n f(m, n) = 0$ and $\sum_m \sum_n f(m, n) = 0$. Column $0$ has the single term $f(0, 0) = 1$, and column $n \ge 1$ has the terms $f(n, n) = 1$ and $f(n-1, n) = -1$. So $\sum_n \sum_m f(m, n) = 1$. The two iterated sums differ. The family $f$ itself is not summable, since its terms do not tend to $0$ along the cofinite filter, so the theorem does not apply.

**Remark (Common errors).** The rules of this section are stated for `HasSum` without extra hypotheses, but their `tsum` forms need the summability of each family that occurs. A frequent error is to rewrite with `Summable.tsum_sigma` in a group that is not complete, or to forget that the iterated sum on the right can exist when the double family is not summable, as in the last example.

### The library around it

The module `Mathlib.Topology.Algebra.InfiniteSum.Basic` holds the lemmas that need only a commutative topological monoid, such as `hasSum_single`, `HasSum.add_compl` and `Equiv.hasSum_iff`. The module `Mathlib.Topology.Algebra.InfiniteSum.Group` adds negation, subtraction, the Cauchy criterion and its consequences. The module `Mathlib.Topology.Algebra.InfiniteSum.Constructions` treats products, sigma types and families of functions (`Pi.hasSum`), and `Mathlib.Topology.Algebra.InfiniteSum.Module` treats scalar multiplication and continuous linear maps.

### Exercises

1. (A) Show that $\sum'_{n} \left(2^{-n} + 3^{-n}\right) = \tfrac72$, and say which summability facts the computation uses.
2. (A) Show that in a topological group, if $f$ and $f + g$ are summable, then $g$ is summable.
3. (B) Let $f : I \to \mathbb{R}$ be summable and $J_1, J_2, \dots$ a partition of $I$ into disjoint sets. Show that $\sum' f = \sum_k \sum'_{i \in J_k} f(i)$. *Hint:* use the sigma type over $k$.
4. (B) Let $G$ be a complete group and $f$ summable. Show that $\sum'_{i \in J} f(i) \to 0$ as $J$ runs through the complements of finite sets. *Hint:* write the tail as a limit of finite sums and use a closed neighbourhood from the Cauchy condition.
5. (B) Show that the Cauchy condition does not imply summability in $\mathbb{Q}$. *Hint:* use the even subfamily of the example.
6. (B) Compute $\sum'_{(m, n) \in \mathbb{N}^2,\, m < n} 2^{-n}$. *Hint:* sum over $m$ first; the answer is $2$.
7. (C) Prove the theorem on sigma types for a complete Hausdorff group without the regularity argument, using the Cauchy condition for the outer sum.

### Notes and history

Bourbaki, *General Topology*, Chapter III, §5, proves these rules for summable families in a commutative Hausdorff group, with the Cauchy criterion in the complete case and the associativity theorem for partitions. The counterexample of the iterated sums is classical.

### Reference

<?reference?>
