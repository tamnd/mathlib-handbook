---
title: Absolute convergence, rearrangements and the Cauchy product
kind: theory
modules:
  - Mathlib.Topology.Algebra.InfiniteSum.Ring
  - Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
  - Mathlib.Topology.Algebra.InfiniteSum.DiscreteConvolution
  - Mathlib.Topology.Algebra.InfiniteSum.UniformOn
  - Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
  - Mathlib.Topology.Algebra.InfiniteSum.ContinuousEval
  - Mathlib.Topology.Algebra.UniformConvergence
explains:
  E3: [summable_abs_iff, HasSum.mul, Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal, NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero, HasSumUniformlyOn]
  E2: [Summable.of_abs, Summable.abs, HasSum.mul_left, HasSum.mul_right, Summable.mul_left, Summable.mul_right, tsum_mul_left, tsum_mul_right, HasSum.mul_eq, Summable.tsum_mul_tsum, summable_sum_mul_antidiagonal_of_summable_mul, Summable.tsum_mul_tsum_eq_tsum_sum_range, Summable.tsum_pow_mul_one_sub, NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero, NonarchimedeanAddGroup.cauchySeq_sum_of_tendsto_cofinite_zero, Summable.mul_of_nonarchimedean, tsum_mul_tsum_of_nonarchimedean, DiscreteConvolution.addRingConvolution, SummableUniformlyOn, HasSumLocallyUniformlyOn, hasSumUniformlyOn_iff_tendstoUniformlyOn, HasSumUniformlyOn.tendstoUniformlyOn, HasSumUniformlyOn.hasSum, HasSumUniformlyOn.of_norm_le_summable, derivWithin_tsum, summable_apply, tsum_apply]
  E1: auto
families: []
requires: [V13.C07, V15.C01, V14.C01, V14.C02, V14.C03, V14.C04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Absolute convergence, rearrangements and the Cauchy product

### Overview

A real series $\sum a_n$ converges *absolutely* when $\sum |a_n|$ converges, and *conditionally* when it converges and $\sum |a_n|$ does not. The rearrangement theorem of Riemann says that the sum of a conditionally convergent series can be changed to any real number by a change of order. Since the unconditional sum of Mathlib does not depend on the order, it cannot see conditional convergence. This section proves the exact statement: in $\mathbb{R}$, and in any complete linearly ordered group, a family is summable exactly when the family of its absolute values is summable.

The section then treats the product of two sums and the Cauchy product, the criterion "the terms tend to $0$" in a complete nonarchimedean group, and sums of functions that converge uniformly.

### Definitions

Let $\alpha$ be a commutative group with a linear order and $|x| = \max(x, -x)$. A family $f : I \to \alpha$ is *absolutely summable* when $i \mapsto |f_i|$ is summable. A real sequence is *conditionally convergent* when its partial sums converge and it is not absolutely summable.

Let $R$ be a semiring with a topology and $f, g : \mathbb{N} \to R$. The *Cauchy product* of $f$ and $g$ is the sequence $c_n = \sum_{k + l = n} f_k g_l$. The pairs $(k, l)$ with $k + l = n$ form the *antidiagonal* of $n$. Mathlib defines antidiagonals on every type with the class `Finset.HasAntidiagonal`, such as $\mathbb{N}$ and $\mathbb{N} \times \mathbb{N}$.

A topological group $G$ is *nonarchimedean* when the open subgroups form a basis of neighbourhoods of $0$. Chapter 8 studies these groups. The groups $\mathbb{Q}_p$ and $\mathbb{Z}_p$ are the main examples, and so is every group with the discrete topology.

Let $f : I \to (X \to \alpha)$ be a family of functions, $g : X \to \alpha$, and $s \subseteq X$, with $\alpha$ a uniform space. Then $f$ *has the sum $g$ uniformly on $s$* when the finite sums $\sum_{i \in F} f_i$ tend to $g$ uniformly on $s$ along $\mathrm{atTop}$: for each entourage $V$ there is a finite $F_0$ with $(g(x), \sum_{i \in F} f_i(x)) \in V$ for all $F \supseteq F_0$ and $x \in s$.

::: mathlib
`HasSumUniformlyOn` · `Mathlib.Topology.Algebra.InfiniteSum.UniformOn`

The definition is `HasSumUniformlyOn f g s`, with `f : ι → β → α`. The lemma `hasSumUniformlyOn_iff_tendstoUniformlyOn` unfolds it into `TendstoUniformlyOn (fun s x ↦ ∑ i ∈ s, f i x) g atTop s`. The module also defines `SummableUniformlyOn` and the local forms `HasSumLocallyUniformlyOn` and `SummableLocallyUniformlyOn`.

<?decl HasSumUniformlyOn?>
:::

### Theorems and proofs

**Theorem (Absolute summability).** Let $\alpha$ be a linearly ordered commutative group with a uniform structure compatible with the group, and suppose that $\alpha$ is complete, as $\mathbb{R}$ is. A family $f : I \to \alpha$ is summable exactly when $|f|$ is summable.

*Proof.* The proof uses the Cauchy criterion of Chapter 4. It suffices to use the neighbourhoods $U_\varepsilon = \{x : |x| < \varepsilon\}$ with $\varepsilon > 0$.

Suppose that $|f|$ is summable. Given $\varepsilon$, choose $s$ for $|f|$. For $t$ disjoint from $s$, the triangle inequality gives $|S_t(f)| \le S_t(|f|) < \varepsilon$. So $f$ satisfies the criterion.

Suppose that $f$ is summable. Let $f^+_i = \max(f_i, 0)$ and $f^-_i = \max(-f_i, 0)$, so that $|f| = f^+ + f^-$. Given $\varepsilon$, choose $s$ for $f$. For $t$ disjoint from $s$, let $t^+ = \{i \in t : f_i \ge 0\}$. Then $t^+$ is disjoint from $s$ and $S_t(f^+) = S_{t^+}(f)$, so $|S_t(f^+)| < \varepsilon$. So $f^+$ is summable, and $f^-$ is summable by the same argument with $-f$. The sum $|f| = f^+ + f^-$ is summable. $\square$

::: mathlib
`summable_abs_iff` · `Mathlib.Topology.Algebra.InfiniteSum.Order`

The statement is `(Summable fun x ↦ |f x|) ↔ Summable f`, with `LinearOrder α`, `IsOrderedAddMonoid α`, `UniformSpace α`, `IsUniformAddGroup α` and `CompleteSpace α`. The two directions are `Summable.of_abs` and `Summable.abs`. For a finite dimensional real normed space the same holds with the norm, `summable_norm_iff`. In an infinite dimensional Banach space only one direction holds, `Summable.of_norm`; the theorem of Dvoretzky and Rogers says that the other fails in every such space.

<?decl summable_abs_iff?>
<?decl summable_norm_iff?>
<?decl Summable.of_norm?>
:::

**Theorem (Riemann).** Let $(a_n)$ be a real sequence that converges conditionally, and let $c \in \mathbb{R}$. There is a bijection $\sigma : \mathbb{N} \to \mathbb{N}$ such that the partial sums of $(a_{\sigma(n)})$ converge to $c$.

*Proof.* The terms tend to $0$, since the partial sums converge. Let $P$ be the set of $n$ with $a_n \ge 0$ and $N$ its complement. Both sums $\sum_{n \in P} a_n$ and $\sum_{n \in N} (-a_n)$ diverge to $+\infty$: if both were finite, the series would converge absolutely, and if only one were finite, the partial sums would diverge. Build $\sigma$ in stages. Take the elements of $P$ in increasing order until the partial sum first exceeds $c$, then the elements of $N$ in increasing order until it first falls below $c$, and repeat. Each stage ends, since each of the two sums diverges, and each stage uses at least one new index, so every index is used once. After the first stage the partial sums differ from $c$ by at most the size of the last term used at a change of direction, and these terms tend to $0$. So the partial sums converge to $c$. $\square$

So the unconditional theory can only accept absolutely convergent series. The alternating harmonic sequence is not summable in Mathlib, and its sum $\log 2$ is a sum for the conditional summation filter of Chapter 4. The index of this edition has no declaration for the rearrangement theorem of Riemann.

**Theorem (Product of two sums).** Let $R$ be a topological semiring that is Hausdorff. Let $f : I \to R$ have the sum $s$ and $g : J \to R$ the sum $t$, and suppose that the family $(i, j) \mapsto f_i g_j$ on $I \times J$ is summable with sum $u$. Then $u = st$.

*Proof.* For finite $F \subseteq I$ and $G \subseteq J$, distributivity gives $S_F(f) S_G(g) = S_{F \times G}(f \otimes g)$. The map $(F, G) \mapsto F \times G$ tends to $\mathrm{atTop}$ on the finite subsets of $I \times J$, since every finite subset of $I \times J$ lies in some $F \times G$. So $S_{F \times G}(f \otimes g) \to u$ along the product filter. Also $S_F(f) S_G(g) \to st$, because multiplication is continuous. Limits are unique in a Hausdorff space, so $u = st$. $\square$

The hypothesis on the product family cannot be dropped in general. In $\mathbb{R}$ it follows from the summability of $f$ and $g$: the finite sums of $|f_i g_j|$ over $F \times G$ are at most $\sum' |f| \cdot \sum' |g|$, so $|f \otimes g|$ is summable by Section 1, and $f \otimes g$ by the theorem on absolute summability. In a nonarchimedean ring it holds always (`Summable.mul_of_nonarchimedean`).

::: mathlib
`HasSum.mul` · `Mathlib.Topology.Algebra.InfiniteSum.Ring`

The statement is `HasSum f s → HasSum g t → Summable (fun x : ι × κ ↦ f x.1 * g x.2) → HasSum (fun x ↦ f x.1 * g x.2) (s * t)`, with `T3Space α` and `IsTopologicalSemiring α`. The form with `tsum` is `Summable.tsum_mul_tsum`. For a normed ring, the summability of the product family follows from the summability of the norms, `summable_mul_of_summable_norm` in `Mathlib.Analysis.Normed.Ring.InfiniteSum`.

<?decl HasSum.mul?>
<?decl summable_mul_of_summable_norm?>
:::

**Corollary (Cauchy product).** Under the hypotheses of the theorem, with $I = J = \mathbb{N}$, the Cauchy product $c_n = \sum_{k + l = n} f_k g_l$ has the sum $st$.

*Proof.* The sets $D_n = \{(k, l) : k + l = n\}$ partition $\mathbb{N} \times \mathbb{N}$ into finite sets. The rule for sums over a sigma type of Chapter 4 regroups the summable family $f \otimes g$ along this partition: the family $n \mapsto \sum_{(k,l) \in D_n} f_k g_l = c_n$ has the sum $u = st$. $\square$

::: mathlib
`Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal` · `Mathlib.Topology.Algebra.InfiniteSum.Ring`

The statement holds on any type `A` with `Finset.HasAntidiagonal A`. It takes `Summable f`, `Summable g` and the summability of the product family, and concludes `(∑' n, f n) * (∑' n, g n) = ∑' n, ∑ kl ∈ antidiagonal n, f kl.1 * g kl.2`.

<?decl Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal?>
:::

**Theorem (Nonarchimedean groups).** Let $G$ be a complete commutative nonarchimedean group. A family $f : I \to G$ is summable exactly when $f_i \to 0$ along the cofinite filter, that is, when for each neighbourhood $U$ of $0$ only finitely many $f_i$ lie outside $U$.

*Proof.* In every commutative topological group the terms of a summable family tend to $0$ along the cofinite filter (Chapter 4). Conversely, suppose $f_i \to 0$ along the cofinite filter, and use the Cauchy criterion. Let $U$ be a neighbourhood of $0$. It contains an open subgroup $H$. The set $s = \{i : f_i \notin H\}$ is finite. For $t$ finite and disjoint from $s$, every term $f_i$ with $i \in t$ lies in $H$, and $H$ is closed under addition, so $S_t \in H \subseteq U$. $\square$

::: mathlib
`NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero` · `Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean`

The statement is `Summable f ↔ Tendsto f cofinite (𝓝 0)`, for `G` with `IsUniformAddGroup G`, `NonarchimedeanAddGroup G` and `CompleteSpace G`. The ring versions `Summable.mul_of_nonarchimedean` and `tsum_mul_tsum_of_nonarchimedean` give the product of two sums with no hypothesis on the product family. The $p$-adic numbers `Padic p` satisfy all the hypotheses.

<?decl NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero?>
<?decl Padic?>
:::

**Theorem (Uniform sums of continuous functions).** Let $X$ be a topological space, $\alpha$ a uniform space with a commutative monoid structure and continuous addition, and $f : I \to (X \to \alpha)$ a family of continuous functions with the sum $g$ uniformly on $X$. Then $g$ is continuous.

*Proof.* Each finite sum $\sum_{i \in F} f_i$ is continuous, as a finite sum of continuous functions. The finite sums tend to $g$ uniformly along $\mathrm{atTop}$, which is not trivial. A uniform limit of continuous functions is continuous (Volume 13). $\square$

The Weierstrass M-test gives uniform sums in a complete normed group: if $\|f_i(x)\| \le u_i$ for all $x \in s$ and $u$ is summable, then $f$ has the sum $x \mapsto \sum' f_i(x)$ uniformly on $s$. The proof is the Cauchy criterion with a bound that does not depend on $x$.

::: mathlib
`HasSumUniformlyOn.of_norm_le_summable` · `Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn`

The M-test. The same module proves `derivWithin_tsum`: a sum of differentiable functions whose derivatives sum locally uniformly can be differentiated term by term. Continuity of the limit comes from `TendstoUniformlyOn.continuousOn` of Volume 13, applied after `HasSumUniformlyOn.tendstoUniformlyOn`.

<?decl HasSumUniformlyOn.of_norm_le_summable?>
<?decl TendstoUniformlyOn.continuousOn?>
:::

### Examples

**Example (The square of the geometric series).** Let $x \in \mathbb{R}$ with $|x| < 1$. The geometric series has the sum $1/(1 - x)$ and is absolutely summable. The Cauchy product of the series with itself has the terms $c_n = \sum_{k=0}^{n} x^k x^{n-k} = (n+1) x^n$. So $\sum_{n \ge 0} (n+1) x^n = \frac{1}{(1-x)^2}$.

**Example (A counterexample: the Cauchy product of a conditionally convergent series).** Let $a_n = (-1)^n/\sqrt{n+1}$. The partial sums converge, by the alternating series test of Volume 15. The Cauchy product of $a$ with itself is $c_n = (-1)^n \sum_{k=0}^{n} \frac{1}{\sqrt{(k+1)(n-k+1)}}$. By the inequality of arithmetic and geometric means, $(k+1)(n-k+1) \le \left(\frac{n+2}{2}\right)^2$, so $|c_n| \ge \frac{2(n+1)}{n+2} \ge 1$. The terms $c_n$ do not tend to $0$, and the Cauchy product diverges. This is consistent with the theorem: $a$ is not summable in Mathlib, and the product family on $\mathbb{N} \times \mathbb{N}$ is not summable either.

**Example (Sums in $\mathbb{Q}_p$).** In $\mathbb{Q}_p$ the powers $p^n$ have $|p^n|_p = p^{-n} \to 0$, so $\sum p^n$ is summable, and its sum is $1/(1-p)$ by the geometric identity above. The factorials satisfy $|n!|_p \to 0$, since $n!$ is divisible by $p^{\lfloor n/p \rfloor}$. So $\sum n!$ is summable in $\mathbb{Q}_p$ for every prime $p$, while it diverges in $\mathbb{R}$.

**Remark (Common errors: summability of the product family).** `HasSum.mul` and `Summable.tsum_mul_tsum` take the summability of $(i, j) \mapsto f_i g_j$ as a separate hypothesis, and in a general topological semiring it does not follow from the summability of $f$ and $g$. A proof over $\mathbb{R}$ or $\mathbb{C}$ supplies it from the norms with `summable_mul_of_summable_norm`, and a proof over $\mathbb{Q}_p$ with `Summable.mul_of_nonarchimedean`.

### The library around it

The module `Mathlib.Topology.Algebra.InfiniteSum.Ring` has the rules for multiplication by a constant (`HasSum.mul_left`, `tsum_mul_left` and their twins), the product of two sums and the Cauchy product. In a division semiring `tsum_mul_left` needs no summability. The module `Mathlib.Topology.Algebra.InfiniteSum.DiscreteConvolution` defines the convolution of two functions on a monoid, with the Cauchy product as the convolution on $\mathbb{N}$; `DiscreteConvolution.addRingConvolution` is its form for a ring. The module `Mathlib.Topology.Algebra.InfiniteSum.ContinuousEval` commutes sums with evaluation at a point (`summable_apply`, `tsum_apply`), and `Mathlib.Topology.Algebra.UniformConvergence` makes the spaces of functions with uniform convergence topological groups.

### Exercises

1. (A) Show that $\sum_{n \ge 1} \frac{\cos n}{n^2}$ is summable in $\mathbb{R}$.
2. (A) Show that $\sum_{n \ge 1} \frac{(-1)^n}{\sqrt n}$ is not summable in Mathlib, and that its partial sums converge.
3. (A) Compute $\sum_{n \ge 0} (n+1) 2^{-n}$ with the Cauchy product. *Hint:* the answer is $4$.
4. (B) Let $f : I \to \mathbb{R}$ be summable. Show that $|\sum' f| \le \sum' |f|$. *Hint:* the comparison of sums of Section 1, applied to $-|f| \le f \le |f|$.
5. (B) Show that $\sum_{n \ge 0} n\,n!$ has the sum $-1$ in $\mathbb{Q}_p$. *Hint:* $n\,n! = (n+1)! - n!$, and the partial sums are $N! - 1$.
6. (B) In the proof of Riemann's theorem, construct a bijection $\sigma$ such that the partial sums of $(a_{\sigma(n)})$ tend to $+\infty$.
7. (B) Let $f_n(x) = x^n/n^2$ on $[-1, 1]$. Show that $\sum f_n$ converges uniformly on $[-1, 1]$ and that its sum is continuous.
8. (C) Let $G$ be a commutative nonarchimedean group that is Hausdorff, $H$ an open subgroup, and $f : I \to G$ a summable family with $f_i \in H$ for every $i$. Show that $\sum' f \in H$. *Hint:* an open subgroup is closed (Chapter 1), and every finite sum lies in $H$.

### Notes and history

Riemann stated the rearrangement theorem in his work on trigonometric series, published after his death. Dirichlet had shown earlier that absolutely convergent series can be rearranged freely. The theorem of Mertens says that the Cauchy product of a convergent series and an absolutely convergent series converges to the product of the sums, a stronger result than the corollary above.

### Reference

<?reference?>
