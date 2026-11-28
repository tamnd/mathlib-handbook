---
title: Normed rings and products of series
kind: api
modules:
  - Mathlib.Analysis.Normed.Ring.Basic
  - Mathlib.Analysis.Normed.Ring.Lemmas
  - Mathlib.Analysis.Normed.Ring.Finite
  - Mathlib.Analysis.Normed.Ring.Int
  - Mathlib.Analysis.Normed.Ring.InfiniteSum
  - Mathlib.Analysis.Normed.Ring.InfiniteProd
explains:
  E2: [norm_mul_le, norm_pow_le, NormOneClass, NormMulClass, RingHomIsometric, antilipschitzWith_mul_left, IsOfFinOrder.norm_eq_one, summable_mul_of_summable_norm, tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm, tendsto_tprod_one_add_of_dominated_convergence]
  E1: auto
families: []
requires: [V06, V13, V15, V16.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Normed rings and products of series

### Overview

A normed ring is a ring with a norm that makes it a normed group and that is submultiplicative: $\|a b\| \le \|a\| \|b\|$. The bounded operators on a Banach space, the square matrices with an operator norm, and the continuous functions on a compact space with the sup norm are normed rings. In a normed ring the multiplication is continuous, a power satisfies $\|a^n\| \le \|a\|^n$, and the norm of $1$ is at least $1$ when the ring is not trivial. When the norm is multiplicative, $\|a b\| = \|a\| \|b\|$, the ring behaves like a field of numbers, and each element of finite order has norm $1$.

Products of series need the norm. When $\sum a_i$ and $\sum b_j$ converge absolutely in a complete normed ring, the double series $\sum a_i b_j$ converges absolutely, and its sum is the product of the two sums. The Cauchy product $\sum_n \sum_{k \le n} a_k b_{n-k}$ has the same sum. This section gives these results and the classes behind them. A statement about a general normed ring in Lean starts with a variable such as `[NormedRing R]`, and the more specific classes, such as `[NormOneClass R]` or `[CompleteSpace R]`, are added only when a lemma needs them. The Banach algebras of the next sections add a scalar field to this setting.

### The library around it

The module `Mathlib.Analysis.Normed.Ring.Basic` has a hierarchy of classes. The basic ones are `NonUnitalSeminormedRing`, `SeminormedRing`, `NonUnitalNormedRing` and `NormedRing`, with commutative forms such as `NormedCommRing`. Each one extends the matching normed group and adds the field `norm_mul_le`. The general lemma `norm_mul_le` states $\|a b\| \le \|a\| \|b\|$, and `norm_mul₃_le` and `norm_mul_le_of_le` are forms for three factors and for bounds. The lemma `norm_pow_le'` states $\|a^n\| \le \|a\|^n$ for $n \ge 1$ in a unital ring. The lemma `norm_pow_le` states the same bound for all $n$, and it needs `NormOneClass`, since the case $n = 0$ is $\|1\| \le 1$. The lemma `eventually_norm_pow_le` states the same bound for all large $n$ in a ring without a unit. The bounds on the maps of multiplication are `mulLeft_bound` and `mulRight_bound`.

Finite products follow the same pattern. The lemma `List.norm_prod_le'` bounds the norm of the product of a nonempty list by the product of the norms, and `List.norm_prod_le` removes the condition on the list when the ring has `NormOneClass`. For a commutative ring, `Finset.norm_prod_le'` and `Finset.norm_prod_le` give the same bounds for a product over a finite set. The lemma `norm_sub_mul_le` states that $\|c - a b\| \le \|c - a\| + \|1 - b\|$ when $\|a\| \le 1$. It is the usual tool to show that a product of factors close to $1$ stays close to $1$, and the proofs on infinite products use it one factor at a time.

Two classes add equalities. The class `NormOneClass` states that $\|1\| = 1$. Without it the norm of $1$ can be larger, as for the Frobenius norm on matrices, and `one_le_norm_one` gives only $1 \le \|1\|$. The class `NormMulClass` states that $\|a b\| = \|a\| \|b\|$, with the lemma `norm_mul`. With both classes, `norm_pow` gives $\|a^n\| = \|a\|^n$, `norm_prod` gives the norm of a finite product, and `normHom` bundles the norm as a monoid homomorphism to $\mathbb{R}$. A normed division ring has both classes. A nontrivial ring with `NormMulClass` has `NormMulClass.toNormOneClass`.

The class `RingHomIsometric σ` states that a ring homomorphism preserves the norm. Chapter 2 uses it for semilinear maps, so that a conjugate linear map has the usual operator norm. Products, finite products, opposite rings, subrings and separation quotients of normed rings are normed rings. The instances are `Prod.normedRing`, `Pi.normedRing`, `MulOpposite.instNormedRing`, `SubringClass.toNormedRing` and `SeparationQuotient.instNormedRing`. An absolute value on a ring gives a normed ring, by `AbsoluteValue.toNormedRing`. To pull a norm back along an injective homomorphism, use `NormedRing.induced`.

The module `Mathlib.Analysis.Normed.Ring.Lemmas` gives the topology. The instance `NonUnitalSeminormedRing.toIsTopologicalRing` states that a seminormed ring is a topological ring. In a ring with `NormMulClass`, multiplication by $a \ne 0$ is a dilation, `Dilation.mulLeft`, and `antilipschitzWith_mul_left` states that it is antilipschitz with constant $\|a\|^{-1}$. The lemma `Filter.Tendsto.zero_mul_isBoundedUnder_le` states that the product of a function that tends to $0$ and a bounded function tends to $0$. The lemma `tendsto_pow_cobounded_cobounded` states that $x^m$ tends to infinity when $x$ does, for $m \ne 0$.

The two small modules on the integers and on finite order use the multiplicative norm. The integers are a normed commutative ring with $\|n\| = |n|$, and `Int.norm_coe_units` states that the units $\pm 1$ have norm $1$. The lemma `Int.toNat_add_toNat_neg_eq_norm` writes the norm as a sum of positive and negative parts. In a ring with `NormMulClass` and `NormOneClass`, `IsOfFinOrder.norm_eq_one` states that an element $a$ with $a^n = 1$ for some $n \ge 1$ has norm $1$, since $\|a\|^n = 1$. So the roots of unity in $\mathbb{C}$ lie on the unit circle, and `AddChar.norm_apply` states that the values of an additive character of a finite group have norm $1$.

The module `Mathlib.Analysis.Normed.Ring.InfiniteSum` multiplies series. The lemma `summable_mul_of_summable_norm` states that, when $\sum \|f(i)\|$ and $\sum \|g(j)\|$ converge in a complete normed ring, the family $f(i) g(j)$ on pairs is summable. The lemma `tsum_mul_tsum_of_summable_norm` states that its sum is the product of the two sums. For sequences, `tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm` gives the Cauchy product with the sums over `Finset.range`, and `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm` gives the form with the antidiagonal. The lemmas `summable_norm_sum_mul_range_of_summable_norm` and `summable_norm_sum_mul_antidiagonal_of_summable_norm` state that the Cauchy product converges absolutely. The exponential of section 4 uses these results to prove $\exp(a + b) = \exp(a) \exp(b)$ for commuting $a$ and $b$.

The module `Mathlib.Analysis.Normed.Ring.InfiniteProd` holds one theorem on infinite products. The theorem `tendsto_tprod_one_add_of_dominated_convergence` states that $\prod_k (1 + f_n(k)) \to \prod_k (1 + g(k))$ when $f_n(k) \to g(k)$ for each $k$ and $\|f_n(k)\| \le b(k)$ for a summable $b$. It is a dominated convergence theorem for products, and it is the usual tool to compute the limit of a product of functions such as the product formula for the sine.

#### Common errors

1. Assuming $\|1\| = 1$ in each normed ring. The norm of $1$ is $1$ only with `NormOneClass`. The Frobenius norm on $n \times n$ matrices gives $\|1\| = \sqrt{n}$.
2. Using `norm_pow_le` in a ring without `NormOneClass`. The bound for $n = 0$ states $\|1\| \le 1$, which can fail. Use `norm_pow_le'` with a proof of $0 < n$.
3. Using `tsum_mul_tsum_of_summable_norm` with only the summability of the two series. Mathlib asks for the summability of the norms, since products of conditionally convergent series need not converge.

### Exercises

1. (A) Show that $\|a^3\| \le \|a\|^3$ from `norm_mul_le`, without `norm_pow_le'`.
2. (A) Show with `IsOfFinOrder.norm_eq_one` that each $n$-th root of unity in $\mathbb{C}$ has absolute value $1$.
3. (B) Show that in a normed ring with $\|1\| > 1$ the norm $\|a\|' = \sup_{\|b\| \le 1} \|a b\|$ is a ring norm with $\|1\|' = 1$.
4. (B) Use `tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm` to show that $\left(\sum_n x^n\right)^2 = \sum_n (n + 1) x^n$ for $|x| < 1$.
5. (B) Show that the conditionally convergent series $\sum_n (-1)^n / \sqrt{n + 1}$ has a Cauchy square that does not converge, so the hypothesis on norms is needed.
6. (C) Prove `summable_mul_of_summable_norm` from the bound $\sum_{(i, j) \in F} \|f(i)\| \|g(j)\| \le \sum_i \|f(i)\| \cdot \sum_j \|g(j)\|$ for each finite set $F$ of pairs.

### Reference

<?reference?>
