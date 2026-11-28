---
title: Products of lists and multisets
kind: api
modules:
  - Mathlib.Algebra.BigOperators.Group.List.Defs
  - Mathlib.Algebra.BigOperators.Group.List.Basic
  - Mathlib.Algebra.BigOperators.Group.List.Lemmas
  - Mathlib.Algebra.BigOperators.Group.Multiset.Basic
  - Mathlib.Algebra.BigOperators.Ring.List
  - Mathlib.Algebra.BigOperators.Ring.Multiset
  - Mathlib.Algebra.BigOperators.Ring.Nat
  - Mathlib.Algebra.Order.BigOperators.Group.List
  - Mathlib.Algebra.Order.BigOperators.Group.Multiset
  - Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
  - Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
  - Mathlib.Algebra.Order.BigOperators.Ring.List
  - Mathlib.Algebra.Order.BigOperators.Ring.Multiset
explains:
  E2: [List.prod_take_mul_prod_drop, List.prod_inv_reverse, List.Perm.prod_eq, List.alternatingSum_append, Multiset.prod_add, Multiset.prod_eq_zero_iff, List.le_prod_of_submultiplicative, Finset.even_sum_iff_even_card_odd]
  E1: auto
families: []
requires: [V03.C02, V03.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Products of lists and multisets

### Overview

A finset sum is a multiset sum, and a multiset sum is a list sum up to order. Section 1 used this chain to define `Finset.sum`. This section gives the library one level down: the product of a list in any monoid, and the product of a multiset in a commutative monoid. A list keeps the order of its factors, so its product needs no commutativity. This is the right object for a product of matrices or of permutations. A multiset forgets the order, so its product needs a commutative monoid, and it is the right object for the prime factors of a number or the roots of a polynomial.

The files come in three layers. The group layer has the rules of a monoid: append, reverse, homomorphisms and powers. The ring layer adds the rules with zero, negation and distributivity. The order layer gives the inequalities. Each rule for products has a twin for sums, made by `to_additive`, and the names follow the same pattern as for finsets: replace `prod` by `sum`, `mul` by `add` and `one` by `zero`.

### The library around it

#### Products of lists

For a list $l = [a_1, \ldots, a_n]$ of a monoid, `l.prod` is $a_1 a_2 \cdots a_n$, with `[].prod = 1`. The definition is a right fold, so the computation rules are the cons rule $(a :: l).\mathrm{prod} = a \cdot l.\mathrm{prod}$ and the append rule $(l_1 \mathbin{++} l_2).\mathrm{prod} = l_1.\mathrm{prod} \cdot l_2.\mathrm{prod}$. The file `Mathlib.Algebra.BigOperators.Group.List.Defs` gives the first consequences: `List.prod_replicate` says that the product of $n$ copies of $a$ is $a^n$, `List.prod_eq_pow_card` gives the same when each factor equals one $m$, and `List.prod_induction` proves that a property closed under products and true at $1$ holds for the product.

The main rules of `Mathlib.Algebra.BigOperators.Group.List.Basic` are these.

| Lean name | Statement |
|---|---|
| `List.prod_take_mul_prod_drop` | $(\mathrm{take}\ i\ l).\mathrm{prod} \cdot (\mathrm{drop}\ i\ l).\mathrm{prod} = l.\mathrm{prod}$ |
| `List.headI_mul_tail_prod_of_ne_nil` | $l \ne [] \Rightarrow \mathrm{head}(l) \cdot \mathrm{tail}(l).\mathrm{prod} = l.\mathrm{prod}$ |
| `List.prod_eq_one` | $(\forall x \in l, x = 1) \Rightarrow l.\mathrm{prod} = 1$ |
| `List.exists_mem_ne_one_of_prod_ne_one` | $l.\mathrm{prod} \ne 1 \Rightarrow \exists x \in l, x \ne 1$ |
| `map_list_prod` | $f(l.\mathrm{prod}) = (l.\mathrm{map}\ f).\mathrm{prod}$ for a monoid homomorphism $f$ |
| `List.prod_inv_reverse` | $(l.\mathrm{prod})^{-1} = (l.\mathrm{map}\ (\cdot)^{-1}).\mathrm{reverse}.\mathrm{prod}$ in a group |
| `List.prod_inv` | $(l.\mathrm{prod})^{-1} = (l.\mathrm{map}\ (\cdot)^{-1}).\mathrm{prod}$ in a commutative group |
| `List.Perm.prod_eq` | $l_1 \sim l_2 \Rightarrow l_1.\mathrm{prod} = l_2.\mathrm{prod}$ in a commutative monoid |
| `List.prod_map_mul` | $\prod (f\ g) = \prod f \cdot \prod g$ over a list, in a commutative monoid |

The rule `List.prod_take_mul_prod_drop` has a one-line proof: $l = \mathrm{take}\ i\ l \mathbin{++} \mathrm{drop}\ i\ l$, and the append rule splits the product. The rule `List.prod_inv_reverse` is the law $(a b)^{-1} = b^{-1} a^{-1}$ for many factors. Its proof is induction on $l$: for $l = a :: l'$, $(a \cdot l'.\mathrm{prod})^{-1} = (l'.\mathrm{prod})^{-1} a^{-1}$, and the induction hypothesis rewrites the first factor as the reversed product of the inverses of $l'$, to which $a^{-1}$ is appended at the end. In a commutative group the reverse can be dropped, and this gives `List.prod_inv`.

The rule `List.Perm.prod_eq` is the bridge to multisets. A permutation of a list is a product of swaps of adjacent elements. A swap changes $\cdots a b \cdots$ into $\cdots b a \cdots$, and in a commutative monoid $a b = b a$. So the product is constant on each class of the permutation relation, and it passes to the quotient `Multiset M`. Mathlib defines `Multiset.prod` as a fold over the multiset, and `Multiset.prod_coe` says that on the class of a list it is the list product. The lemma `List.prod_rotate` is a special case: a rotation is a permutation.

The lemmas on commutation are for a monoid that is not commutative. `Commute.list_prod_right` says that an element $y$ that commutes with each factor commutes with the product. The additive twin is `AddCommute.list_sum_right`.

The file `Mathlib.Algebra.BigOperators.Group.List.Lemmas` adds the units and divisibility: `List.prod_isUnit_iff` says that in a commutative monoid a product is a unit exactly when each factor is a unit, and `List.Sublist.prod_dvd_prod` says that the product of a sublist divides the product of the list. It also has the opposite monoid: `MulOpposite.op_list_prod` says that the product in $M^{\mathrm{op}}$ is the reversed product. Two counting rules sit there too. `List.sum_map_count_dedup_eq_length` says that the sum of the counts of the distinct elements of $l$ is the length of $l$, and `List.length_sigma` says that the length of a dependent product of lists is a sum of lengths.

#### Alternating sums

The file `Mathlib.Algebra.BigOperators.Group.List.Defs` also defines `List.alternatingSum` and `List.alternatingProd`. For $l = [a_1, a_2, a_3, \ldots]$, the alternating sum is $a_1 - a_2 + a_3 - \cdots$, and `List.alternatingSum_cons_cons` is its two-step rule $(a :: b :: l) \mapsto a - b + \mathrm{alt}(l)$. In a commutative group, $$\mathrm{alt}(l_1 \mathbin{++} l_2) = \mathrm{alt}(l_1) + (-1)^{|l_1|} \mathrm{alt}(l_2),$$ which is `List.alternatingSum_append`. The sign appears because the first element of $l_2$ sits at position $|l_1| + 1$ of the joined list, and its sign is $+$ exactly when $|l_1|$ is even. The proof is induction on $l_1$: one more element in front changes the sign of each later term. The rule `List.alternatingSum_reverse` follows, with the sign $(-1)^{|l| + 1}$. The test of divisibility by $11$ is an alternating sum of the digits.

#### Products of multisets

The file `Mathlib.Algebra.BigOperators.Group.Multiset.Basic` gives the API of `Multiset.prod`, for a commutative monoid. The main rule is `Multiset.prod_add`: $(s + t).\mathrm{prod} = s.\mathrm{prod} \cdot t.\mathrm{prod}$. Here $s + t$ adds the multiplicities. The proof lifts both multisets to lists $l_1, l_2$. Then $s + t$ is the class of $l_1 \mathbin{++} l_2$, and the append rule for lists gives the claim. So `Multiset.prod` is a monoid homomorphism from the additive monoid of multisets, and for sums the library bundles it as `Multiset.sumAddMonoidHom`.

The other rules follow the finset rules of Section 1 and have the same names.

1. Homomorphisms: `map_multiset_prod` and `map_multiset_sum` push a homomorphism inside.
2. Pointwise operations: `Multiset.prod_map_mul`, `Multiset.prod_map_pow` and `Multiset.prod_map_inv`.
3. Filters and erase: `Multiset.prod_filter_mul_prod_filter_not` splits by a predicate, and `Multiset.prod_map_erase` takes one factor out.
4. Divisibility: `Multiset.dvd_prod` says that each element divides the product, and `Multiset.prod_dvd_prod_of_le` says that $s \le t$ implies $s.\mathrm{prod} \mid t.\mathrm{prod}$.
5. Remainders: `Multiset.prod_nat_mod` and `Multiset.sum_nat_mod` reduce each factor modulo $n$ first. The list forms include `List.sum_int_mod`.

#### Products in rings

The files `Mathlib.Algebra.BigOperators.Ring.List` and `Mathlib.Algebra.BigOperators.Ring.Multiset` give the rules that use zero, negation and distributivity.

| Lean name | Statement |
|---|---|
| `List.prod_eq_zero_iff` | $l.\mathrm{prod} = 0 \iff 0 \in l$, with no zero divisors |
| `Multiset.prod_eq_zero_iff` | $s.\mathrm{prod} = 0 \iff 0 \in s$, with no zero divisors |
| `Multiset.prod_eq_zero` | $0 \in s \Rightarrow s.\mathrm{prod} = 0$, in any monoid with zero |
| `List.prod_map_neg` | $\prod (-a_i) = (-1)^{|l|} \prod a_i$ |
| `List.sum_map_mul_left` | $\sum r a_i = r \sum a_i$ |
| `Commute.list_sum_left` | a list sum commutes with $b$ when each term does |
| `Multiset.prod_map_add` | $\prod_i (f_i + g_i)$ as a sum over the splittings of $s$ |
| `Multiset.prod_map_sum` | a product of sums is a sum over the sections |

For `Multiset.prod_eq_zero_iff`, one direction holds in each commutative monoid with zero: a factor $0$ makes the product $0$. For the other direction, use induction on $s$. If $a \cdot t.\mathrm{prod} = 0$ with no zero divisors, then $a = 0$ or $t.\mathrm{prod} = 0$, and in the second case the hypothesis gives $0 \in t$. The hypothesis `Nontrivial` excludes the zero ring, where $1 = 0$ is the product of the empty multiset.

The rule `Multiset.prod_map_add` is the expansion of $\prod_{i \in s} (f(i) + g(i))$. Each term chooses $f$ or $g$ at each element, so the sum runs over the pairs $(p, q)$ of `Multiset.antidiagonal`, with $p + q = s$, of $\prod_p f \cdot \prod_q g$. The rule `Multiset.prod_map_sum` expands a product of sums over `Multiset.Sections`, the multisets that take one element from each factor.

The file `Mathlib.Algebra.BigOperators.Ring.Nat` has a parity rule: `Finset.even_sum_iff_even_card_odd` says that a sum of natural numbers is even exactly when the number of odd terms is even. The proof reduces each term modulo $2$: an even term gives $0$ and an odd term gives $1$, so the sum is congruent to the number of odd terms. The twin `Finset.odd_sum_iff_odd_card_odd` follows. The handshake lemma is a use: the degrees of a finite graph sum to an even number, so the number of odd degrees is even.

#### Inequalities

The order layer is in `Mathlib.Algebra.Order.BigOperators.Group.List` and `Mathlib.Algebra.Order.BigOperators.Group.Multiset`. The pattern is the pattern of Section 2 for finsets.

1. Term by term: `List.prod_le_prod'` and `List.sum_le_sum` compare $\prod f$ and $\prod g$ over a list when $f \le g$ at each element. The strict forms are `List.prod_lt_prod'` and `Multiset.prod_lt_prod_of_nonempty`, and the forms for two lists in relation are `List.Forall₂.prod_le_prod` and `Multiset.prod_le_prod_of_rel_le`.
2. Bounds by a constant: `List.pow_card_le_prod` gives $n^{|l|} \le l.\mathrm{prod}$ when $n \le x$ for each $x \in l$, and `List.card_nsmul_le_sum` is its twin.
3. One term and the whole: `List.single_le_sum` gives $x \le l.\mathrm{sum}$ for $x \in l$ when all terms are nonnegative, and `List.le_sum_of_mem` gives the same in a canonically ordered monoid with no hypothesis.
4. Zero sums: `List.sum_eq_zero_iff` says that in a canonically ordered monoid, such as $\mathbb{N}$, a sum is $0$ exactly when each term is $0$.
5. Submultiplicative maps: `List.le_prod_of_submultiplicative` and `Multiset.le_prod_of_submultiplicative`.

The rule for a submultiplicative map states: if $f(1) \le 1$ and $f(a b) \le f(a) f(b)$, then $f(l.\mathrm{prod}) \le (l.\mathrm{map}\ f).\mathrm{prod}$. The proof is induction on $l$. For $l = []$, the claim is $f(1) \le 1$. For $l = a :: l'$, $f(a \cdot l'.\mathrm{prod}) \le f(a) f(l'.\mathrm{prod}) \le f(a) \cdot (l'.\mathrm{map}\ f).\mathrm{prod}$, with the induction hypothesis in the second step. The triangle inequality for a norm, $\lVert \sum x_i \rVert \le \sum \lVert x_i \rVert$, is the additive form for a subadditive map.

The files on monoids with zero give the products of nonnegative elements of an ordered semiring. The lemmas `List.prod_nonneg`, `List.prod_pos`, `Multiset.prod_nonneg` and `Multiset.prod_pos` say that a product of nonnegative (or positive) factors is nonnegative (or positive). The lemma `Multiset.prod_map_le_prod_map₀` compares two products when $0 \le f \le g$, and the subscript $0$ marks the form for a monoid with zero, where the hypothesis $0 \le f$ is needed. In a canonically ordered semiring, `CanonicallyOrderedAdd.list_prod_pos` is an `iff`: the product is positive exactly when each factor is positive. The file `Mathlib.Algebra.Order.BigOperators.Ring.Multiset` gives `Multiset.le_prod_of_submultiplicative_of_nonneg`, the submultiplicative rule for a map with nonnegative values.

#### Common errors

1. A list product in a monoid that is not commutative depends on the order. `List.Perm.prod_eq` needs `CommMonoid`, and in a group the inverse of a product reverses the order, by `List.prod_inv_reverse`, not `List.prod_inv`.
2. `Multiset.prod_eq_zero_iff` needs `NoZeroDivisors` and `Nontrivial`. In `ZMod 6`, the product of the multiset $\{2, 3\}$ is $0$ with no factor $0$.
3. The order lemmas for products in a semiring carry the subscript $0$ and need the nonnegativity of the factors. The lemma `List.prod_le_prod'` without the subscript is for an ordered monoid, where multiplication is monotone, and it does not apply to $\mathbb{R}$ with its multiplication.

### Exercises

1. (A) Compute the alternating sum of $[3, 1, 4, 1, 5]$, and check `List.alternatingSum_append` with $l_1 = [3, 1]$ and $l_2 = [4, 1, 5]$.
2. (A) Use `Multiset.prod_eq_zero_iff` to show that a product of nonzero integers is nonzero, and give the step of the induction.
3. (B) In the group of permutations of $\{1, 2, 3\}$, give a list $l$ of two transpositions with $(l.\mathrm{prod})^{-1} \ne (l.\mathrm{map}\ (\cdot)^{-1}).\mathrm{prod}$.
4. (B) Prove that a sum of $k$ odd natural numbers is even exactly when $k$ is even, with `Finset.even_sum_iff_even_card_odd`.
5. (B) Use `List.le_sum_of_subadditive` with $f(x) = |x|$ on $\mathbb{Z}$ to prove $|a_1 + \cdots + a_n| \le |a_1| + \cdots + |a_n|$, and say which two hypotheses on $f$ it needs.
6. (C) Prove `Multiset.prod_map_add` for $s$ with two elements by hand, and list the four pairs of `Multiset.antidiagonal` that appear.

### Reference

<?reference?>
