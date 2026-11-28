---
title: Monovariance and the rearrangement inequality
kind: api
modules:
  - Mathlib.Algebra.Order.Monovary
  - Mathlib.Algebra.Order.Rearrangement
explains:
  E2: [Monovary.mul_add_mul_le_mul_add_mul, monovary_iff_forall_mul_nonneg, monovaryOn_iff_mul_rearrangement, monovary_neg_left, Monovary.add_left, Monovary.inv_left₀, MonovaryOn.sum_smul_comp_perm_le_sum_smul, Monovary.sum_mul_comp_perm_le_sum_mul, Monovary.sum_mul_comp_perm_eq_sum_mul_iff, Antivary.sum_mul_le_sum_mul_comp_perm]
  E1: auto
families: []
requires: [V04.C02, V04.C08, V01.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Monovariance and the rearrangement inequality

### Overview

Let $a_1 \le a_2 \le \dots \le a_n$ and $b_1 \le b_2 \le \dots \le b_n$ be real numbers. The rearrangement inequality states that, among all the ways to pair the $a_i$ with the $b_j$, the sum of the products is largest when the two lists are in the same order and smallest when they are in opposite orders. For a permutation $\sigma$,
$$\sum_i a_i b_{\sigma(i)} \le \sum_i a_i b_i.$$
Chebyshev's sum inequality has a short proof from this inequality, and so do several inequalities of competition problems.

Mathlib does not state the inequality for sorted lists. It states it for two functions $f$ and $g$ on an index type with no order, with the hypothesis that $f$ and $g$ *monovary*: $g(i) < g(j)$ gives $f(i) \le f(j)$. Chapter 2 defines this relation as `Monovary f g`, with the dual `Antivary f g` and the forms on a set. This section describes the two files that join the relation to the algebra: the rules for sums, products and inverses of functions that monovary, and the rearrangement inequality with its cases of equality.

### The library around it

#### The two-term inequality

The case of two indices is the base of the theory. The lemma `Monovary.mul_add_mul_le_mul_add_mul` in `Mathlib.Algebra.Order.Monovary` states that, in a linearly ordered ring, if $f$ and $g$ monovary, then for each $i$ and $j$
$$f(i) g(j) + f(j) g(i) \le f(i) g(i) + f(j) g(j).$$
The difference of the two sides is $(f(j) - f(i))(g(j) - g(i))$, by expansion. So the inequality is equivalent to
$$0 \le (f(j) - f(i))(g(j) - g(i)),$$
which is `Monovary.sub_mul_sub_nonneg`. The proof of the second form is a case split on $g$. If $g(i) < g(j)$, then $f(i) \le f(j)$ by monovariance, and both factors are nonnegative. If $g(j) < g(i)$, then $f(j) \le f(i)$, and both factors are nonpositive. If $g(i) = g(j)$, then the second factor is $0$. In each case the product is nonnegative.

The converse also holds in a linear order. The lemma `monovary_iff_forall_mul_nonneg` states that $f$ and $g$ monovary if and only if each product $(f(j) - f(i))(g(j) - g(i))$ is nonnegative, and `monovaryOn_iff_mul_rearrangement` states the equivalence with the two-term inequality, on a set. For the converse, suppose $g(i) < g(j)$ and $f(j) < f(i)$. Then the product is a product of a negative and a positive element, so it is negative. The forms for scalar multiplication, such as `Monovary.smul_add_smul_le_smul_add_smul`, let $f$ take values in an ordered ring and $g$ in an ordered module.

#### Operations on monovarying functions

The rest of `Mathlib.Algebra.Order.Monovary` lists the operations that keep the relation. In an ordered additive commutative group, the negative of $f$ reverses it: `monovary_neg_left` states that $-f$ monovaries with $g$ if and only if $f$ antivaries with $g$. The forms `monovary_neg_right` and `monovary_inv_left` treat the other cases.

Sums on the left keep the relation. The lemma `Monovary.add_left` states that if $f_1$ and $f_2$ both monovary with $g$, then so does $f_1 + f_2$. The proof is the sum of the two inequalities $f_1(i) \le f_1(j)$ and $f_2(i) \le f_2(j)$. On the right the condition is stronger. The lemma `Monovary.add_right` asks that $f$ monovary with $g_1$ and with $g_2$, and it needs a linear order on the values of $g$. The hypothesis $g_1(i) + g_2(i) < g_1(j) + g_2(j)$ gives $g_1(i) < g_1(j)$ or $g_2(i) < g_2(j)$, and this step uses the linear order.

In an ordered semiring, products need signs. The lemma `Monovary.mul_left₀` asks that $f_1$ and $f_2$ be nonnegative, and `Monovary.pow_left₀` states that $f^n$ monovaries with $g$ for a nonnegative $f$. In a linearly ordered semifield, `Monovary.inv_left₀` states that if $f$ is positive at each point and monovaries with $g$, then $f^{-1}$ antivaries with $g$. The reason is that $x \mapsto x^{-1}$ is antitone on the positive elements. The forms for ordered groups, such as `Monovary.mul_left` and `Monovary.pow_left`, need no sign condition.

#### The rearrangement inequality

The file `Mathlib.Algebra.Order.Rearrangement` proves the inequality for $n$ terms. Its most general form is `MonovaryOn.sum_smul_comp_perm_le_sum_smul`. For a finite set $s$ of indices, a permutation $\sigma$ that moves only elements of $s$, and functions $f$ and $g$ that monovary on $s$, it states
$$\sum_{i \in s} f(i) \cdot g(\sigma(i)) \le \sum_{i \in s} f(i) \cdot g(i).$$
Here $f$ takes values in a linearly ordered semiring $\alpha$, $g$ in a linearly ordered cancellative additive monoid $\beta$ that is an $\alpha$-module, and the product is the scalar product.

The proof is an induction on $s$ by the largest value of $g$, with ties broken by $f$. Let $a$ be an index where the pair $(g(a), f(a))$ is largest in the lexicographic order. If $\sigma(a) = a$, the induction hypothesis applies to the rest of $s$. If not, let $\tau$ be $\sigma$ followed by the transposition of $a$ and $\sigma(a)$. Then $\tau$ fixes $a$, and the sum for $\sigma$ differs from the sum for $\tau$ only in two terms. These two terms are exactly the two sides of the two-term inequality, so the sum for $\sigma$ is at most the sum for $\tau$. The induction hypothesis applies to $\tau$ on the rest of $s$. Each step fixes one more index, so the induction ends.

The form for multiplication in a ring is `Monovary.sum_mul_comp_perm_le_sum_mul`, for a finite index type:
$$\sum_i f(i) g(\sigma(i)) \le \sum_i f(i) g(i).$$
The forms such as `Monovary.sum_comp_perm_mul_le_sum_mul` permute $f$ in place of $g$. The forms for antivarying functions reverse the inequality: `Antivary.sum_mul_le_sum_mul_comp_perm` states that the sum for two antivarying functions is at most the sum for each permutation.

#### Equality and strict inequality

With a strict monotonicity of the scalar product, the file gives the cases of equality. The lemma `Monovary.sum_mul_comp_perm_eq_sum_mul_iff` states that, when $f$ and $g$ monovary, the sum for $\sigma$ equals the sum for the identity if and only if $f$ and $g \circ \sigma$ also monovary. So a permutation changes the sum exactly when it breaks the common order of $f$ and $g$. The lemma `Monovary.sum_mul_comp_perm_lt_sum_mul_iff` is the strict form: the sum for $\sigma$ is strictly smaller if and only if $f$ and $g \circ \sigma$ do not monovary. The proof of the strict form is short. It combines the weak inequality with the case of equality, because $x < y$ is $x \le y$ and $x \ne y$.

The file does not treat two monotone functions on a linear order separately. Two such functions monovary by `Monotone.monovary` of Chapter 2, and then the lemmas of this section apply. Use `monovary_self` for the sum of the squares $\sum_i f(i)^2$.

#### Common errors

1. Monovariance is not symmetric unless the values of both functions lie in linear orders: `Monovary f g` asks that $g(i) < g(j)$ give $f(i) \le f(j)$, with a strict hypothesis on $g$ only. When $g$ is constant on a set, the relation holds for each $f$. Check which function carries the strict hypothesis before applying a lemma.
2. The rearrangement inequality needs the permutation to move only elements of $s$ in the forms with `MonovaryOn`. Without the hypothesis on $\sigma$, the sums over $s$ are not comparable, because $g \circ \sigma$ can take values from outside $s$.
3. The lemma `Monovary.mul_left₀` needs both factors nonnegative. For $f_1 = f_2 = x \mapsto x$ on $\{-2, 1\}$ and $g$ the same function, the product $x^2$ does not monovary with $g$.

### Exercises

1. (A) Expand $(f(j) - f(i))(g(j) - g(i))$ and deduce `Monovary.mul_add_mul_le_mul_add_mul` from `Monovary.sub_mul_sub_nonneg`.
2. (A) Prove `Monovary.add_left` from the definition of monovariance.
3. (B) Prove the converse direction of `monovary_iff_forall_mul_nonneg` in a linearly ordered ring.
4. (B) Use `Monovary.sum_mul_comp_perm_le_sum_mul` with the cyclic permutation to show $a b + b c + c a \le a^2 + b^2 + c^2$ for real numbers $a$, $b$ and $c$.
5. (B) Deduce Chebyshev's sum inequality $n \sum_i a_i b_i \ge (\sum_i a_i)(\sum_i b_i)$ for two monotone sequences, by a sum of the rearrangement inequality over the $n$ cyclic shifts.
6. (C) Prove the rearrangement inequality for $n = 3$ directly, with at most two uses of the two-term inequality, and compare the argument with the induction of this section.

### Reference

<?reference?>
