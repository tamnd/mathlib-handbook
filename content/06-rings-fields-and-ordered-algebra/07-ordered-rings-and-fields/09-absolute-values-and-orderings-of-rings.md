---
title: Absolute values, the ultrametric inequality and orderings of rings
kind: api
modules:
  - Mathlib.Algebra.Order.AbsoluteValue.Basic
  - Mathlib.Algebra.Order.AbsoluteValue.Euclidean
  - Mathlib.Algebra.Order.AbsoluteValue.Int
  - Mathlib.Algebra.Order.Ring.IsNonarchimedean
  - Mathlib.Algebra.Order.Ring.Cone
  - Mathlib.Algebra.Order.Ring.Ordering.Basic
  - Mathlib.Algebra.Order.Ring.Ordering.Defs
explains:
  E2: [AbsoluteValue, AbsoluteValue.map_mul, AbsoluteValue.add_le, AbsoluteValue.abs, IsAbsoluteValue, AbsoluteValue.IsEuclidean, IsNonarchimedean.add_eq_max_of_ne, IsOrderedRing.ofSubsemiring, Subsemiring.IsPreordering, Subsemiring.IsOrdering]
  E1: auto
families: []
requires: [V06.C01, V06.C02, V06.C03, V06.C06, V04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Absolute values, the ultrametric inequality and orderings of rings

### Overview

An absolute value on a ring $R$ with values in an ordered semiring $S$ is a map $v : R \to S$ that is nonnegative, zero only at $0$, multiplicative and subadditive. The usual absolute value of an ordered ring is one, and the $p$-adic absolute values of $\mathbb{Q}$ are others. This section gives the algebraic API of absolute values: the structure `AbsoluteValue R S`, the unbundled class `IsAbsoluteValue`, the Euclidean absolute values that measure the division with remainder, and the nonarchimedean functions, which satisfy $v(a + b) \le \max(v(a), v(b))$. The topology of an absolute value and the equivalence of absolute values are in Volume 14.

The section ends with the converse direction of Section 1. There, an order on a ring gives the set of nonnegative elements, and a positive cone gives an order. Here the library gives this correspondence for subsemirings, and the more general preorderings of real algebra: the subsemirings that contain all squares and do not contain $-1$. The section needs the ordered rings and fields of Sections 1 and 2, the ideals of Chapter 2, the fields of Chapter 3, the Euclidean domains of Chapter 6 and the lattices of Volume 4.

### The library around it

#### The structure of an absolute value

The structure `AbsoluteValue R S` extends the multiplicative map `R →ₙ* S` with three conditions: `AbsoluteValue.nonneg`, $0 \le v(x)$; $v(x) = 0 \iff x = 0$, with the negated form `AbsoluteValue.ne_zero_iff`; and `AbsoluteValue.add_le`, $v(x + y) \le v(x) + v(y)$. The multiplicativity is `AbsoluteValue.map_mul`. An absolute value is a function by coercion, and `AbsoluteValue.ext` says that two absolute values with the same values are equal.

The first consequences are in the list below.

- `AbsoluteValue.map_zero`, `AbsoluteValue.pos`, `AbsoluteValue.pos_iff` and `AbsoluteValue.nonpos_iff` give the behaviour at $0$.
- `AbsoluteValue.map_one` says $v(1) = 1$, when $S$ is a domain and $R$ is nontrivial. Proof: $v(1) = v(1)^2$ and $v(1) \neq 0$.
- `AbsoluteValue.map_pow` says $v(a^n) = v(a)^n$, under the same conditions.
- `AbsoluteValue.map_neg` says $v(-a) = v(a)$. Proof: $v(-1)^2 = v(1) = 1$ and $v(-1) \ge 0$, so $v(-1) = 1$. This needs that $S$ has no zero divisors.
- `AbsoluteValue.map_sub` says $v(a - b) = v(b - a)$, and `AbsoluteValue.sub_le` is the triangle inequality $v(a - c) \le v(a - b) + v(b - c)$.
- `AbsoluteValue.abs_abv_sub_le_abv_sub` is the reverse triangle inequality $|v(a) - v(b)| \le v(a - b)$.
- `AbsoluteValue.apply_nat_le_self` says $v(n) \le n$ for a natural number $n$, by induction with the triangle inequality.

With these conditions, `AbsoluteValue.toMonoidWithZeroHom` makes an absolute value into a map of monoids with zero, and the instance `AbsoluteValue.addGroupSeminormClass` makes it a seminorm on the additive group. The trivial absolute value `AbsoluteValue.trivial` takes the value $1$ at each nonzero element; it is defined on a ring without zero divisors, and `AbsoluteValue.trivial_apply` gives its values. The predicate `AbsoluteValue.IsNontrivial` says that some nonzero element has a value different from $1$, and `AbsoluteValue.IsNontrivial.exists_abv_gt_one` gives an element of value greater than $1$ in a field.

#### The usual absolute value and the unbundled class

In a linearly ordered strict ring $S$, the usual absolute value is `AbsoluteValue.abs : AbsoluteValue S S`, and `AbsoluteValue.abs_apply` says that its value at $a$ is $|a|$. Multiplicativity is the lemma `abs_mul` of Section 1.

The class `IsAbsoluteValue f` is the unbundled form, for a function `f : R → S`. The library uses it for the completions in Volume 15, where the absolute value is a parameter of a construction. The instance `AbsoluteValue.isAbsoluteValue` goes from the bundled to the unbundled form, and `IsAbsoluteValue.toAbsoluteValue` goes back. The lemmas have the same names in the namespace `IsAbsoluteValue`: `IsAbsoluteValue.abv_mul`, `IsAbsoluteValue.abv_add`, `IsAbsoluteValue.abv_pow`, `IsAbsoluteValue.abv_inv` and `IsAbsoluteValue.abv_div`. The last two are for division rings and give $v(a^{-1}) = v(a)^{-1}$ and $v(a/b) = v(a)/v(b)$.

#### Absolute values on the integers and Euclidean absolute values

The module `Mathlib.Algebra.Order.AbsoluteValue.Int` has the results about units of $\mathbb{Z}$. The units are $\pm 1$, so `AbsoluteValue.map_units_int` says $v(u) = 1$ for each unit $u$ of $\mathbb{Z}$. The forms `AbsoluteValue.map_units_intCast` and `AbsoluteValue.map_units_int_smul` are for the image of a unit in another ring.

A Euclidean domain has a well-founded relation $x \prec y$ that the division with remainder decreases. An absolute value is Euclidean, `AbsoluteValue.IsEuclidean abv`, when it measures this relation: `AbsoluteValue.IsEuclidean.map_lt_map_iff` says $v(x) < v(y) \iff x \prec y$. Then `AbsoluteValue.IsEuclidean.sub_mod_lt` gives $v(a \bmod b) < v(b)$ for $b \neq 0$, and the remainder is smaller than the divisor in the sense of $v$. The usual absolute value on $\mathbb{Z}$ is Euclidean, by `AbsoluteValue.abs_isEuclidean`. Volume 12 uses Euclidean absolute values in the proof that the class group of a number field is finite.

#### The ultrametric inequality

A function $f : \alpha \to R$ into a linear order is nonarchimedean, `IsNonarchimedean f`, when $f(a + b) \le \max(f(a), f(b))$ for all $a, b$. The $p$-adic absolute value is the main example. The module `Mathlib.Algebra.Order.Ring.IsNonarchimedean` gives the consequences.

- `IsNonarchimedean.add_le` says that a nonarchimedean nonnegative function satisfies the triangle inequality, since $\max(x, y) \le x + y$ for nonnegative $x, y$.
- `IsNonarchimedean.nsmul_le` says $f(n \cdot a) \le f(a)$, and `IsNonarchimedean.apply_natCast_le_one` says $f(n) \le 1$ when $f(1) = 1$. So integers are small for a nonarchimedean absolute value, which is the reverse of the archimedean property of Section 3.
- `IsNonarchimedean.add_eq_max_of_ne` says that $f(a + b) = \max(f(a), f(b))$ when $f(a) \neq f(b)$ and $f(-a) = f(a)$. In words, in an ultrametric space every triangle is isosceles. Proof: if $f(a) < f(b)$, then $f(b) = f((a + b) - a) \le \max(f(a + b), f(a))$, so $f(b) \le f(a + b)$.
- `IsNonarchimedean.apply_sum_le_sup` gives the inequality for a finite sum: $f(\sum_{i \in s} g_i) \le \max_{i \in s} f(g_i)$. The lemma `IsNonarchimedean.finset_image_add` gives an index that attains the bound, and `IsNonarchimedean.apply_sum_eq_of_lt` gives equality when one term is strictly larger than all others.
- `IsNonarchimedean.add_pow_le` bounds $f((a + b)^n)$ by $f(a^m) f(b^{n - m})$ for one $m \le n$, the binomial theorem in the ultrametric form.

#### Orderings from subsemirings

Section 1 gives the positive cone of an order. The library states it with the API of supports of submonoids. For a subsemiring $S$ of a ring $R$, the support is $S \cap -S$; $S$ is pointed when the support is $\{0\}$, and spanning when $S \cup -S = R$. The theorem `IsOrderedRing.ofSubsemiring` says that a pointed subsemiring gives a partial order, $a \le b \iff b - a \in S$, with which $R$ is an ordered ring. The order is `PartialOrder.ofAddSubmonoid`, and a subsemiring that is pointed and spanning gives a linear order, `LinearOrder.ofAddSubmonoid`. Conversely, the nonnegative elements `Subsemiring.nonneg R` of an ordered ring are pointed, by `Subsemiring.IsPointed.nonneg`, and spanning when the order is linear, by `Subsemiring.IsSpanning.nonneg`.

#### Preorderings and orderings

Real algebra uses a weaker notion. A subsemiring $S$ of a commutative ring is a preordering, `Subsemiring.IsPreordering S`, when it contains all squares and does not contain $-1$. Then it contains all sums of squares, by `Subsemiring.IsPreordering.mem_of_isSumSq`, and `Subsemiring.IsPreordering.of_sumSq_le` is the converse construction. A preordering is not pointed in general. But in a field it is, by `Subsemiring.IsPreordering.isPointed`, and it is closed under inverses, by `Subsemiring.IsPreordering.inv_mem`, since $a^{-1} = a \cdot (a^{-1})^2$.

An ordering, `Subsemiring.IsOrdering S`, is a spanning subsemiring whose support is a prime ideal: the support is not all of $R$, and `Subsemiring.IsOrdering.mem_support_or_mem_support` is the prime condition. By `Subsemiring.IsOrdering.isPrime_supportIdeal` the support is the prime ideal `Subsemiring.supportIdeal`, and `Subsemiring.IsOrdering.of_isPrime_supportIdeal` is the converse. An ordering of $R$ with support $\mathfrak{p}$ is the same as a linear order on the domain $R/\mathfrak{p}$ that makes it an ordered ring. This is the starting point of the real spectrum. The test `Subsemiring.IsPreordering.isOrdering_iff` says that a preordering is an ordering exactly when $-(ab) \in S$ implies $a \in S$ or $b \in S$.

The older structures `RingCone` and `RingPreordering` are deprecated. Use the predicates on `Subsemiring` in new code.

#### Common errors

1. `AbsoluteValue.map_one`, `AbsoluteValue.map_pow` and `AbsoluteValue.map_neg` need conditions on the target: a domain, or no zero divisors. With a target such as $\mathbb{Z}/6$ these lemmas do not apply.
2. `IsNonarchimedean.add_eq_max_of_ne` needs $f(a) \neq f(b)$ and the symmetry $f(-a) = f(a)$. For $f(a) = f(b)$ the value $f(a + b)$ can be smaller: for the $2$-adic absolute value, $|1|_2 = |1|_2 = 1$ but $|1 + 1|_2 = 1/2$.
3. A preordering is not a positive cone. The set of sums of squares in $\mathbb{R}[X, Y]$ is a preordering, but it is not spanning, since neither $X$ nor $-X$ is a sum of squares.

### Exercises

1. (A) Check that the trivial absolute value on $\mathbb{Z}$ satisfies the triangle inequality, and show that it is nonarchimedean.
2. (A) Prove `AbsoluteValue.map_neg` from `AbsoluteValue.map_mul`, `AbsoluteValue.map_one` and `AbsoluteValue.nonneg`, for a target without zero divisors.
3. (B) Prove `AbsoluteValue.apply_nat_le_self` by induction on $n$.
4. (B) Let $f$ be nonarchimedean, nonnegative and symmetric, with $f(1) = 1$. Prove that $f(n) \le 1$ for each integer $n$.
5. (B) Show that a preordering of a field contains $a^{-1}$ when it contains $a \neq 0$.
6. (C) Let $S$ be an ordering of a commutative ring $R$ with support $\mathfrak{p}$. Show that $a + \mathfrak{p} \le b + \mathfrak{p} \iff b - a \in S$ is a well defined linear order on $R/\mathfrak{p}$, and that it makes $R/\mathfrak{p}$ an ordered ring.

### Reference

<?reference?>
