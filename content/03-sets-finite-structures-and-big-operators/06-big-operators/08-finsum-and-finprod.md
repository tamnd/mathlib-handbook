---
title: Sums and products with finite support
kind: api
modules:
  - Mathlib.Algebra.BigOperators.Finprod
  - Mathlib.Algebra.FiniteSupport.Defs
  - Mathlib.Algebra.FiniteSupport.Basic
explains:
  E2: [finprod, Function.HasFiniteMulSupport, finprod_eq_prod_of_mulSupport_subset, finprod_of_infinite_mulSupport, finprod_mul_distrib, finprod_mem_def, finprod_mem_insert, finsum_mul, Function.HasFiniteMulSupport.mul]
  E1: auto
families: []
requires: [V03.C03, V03.C04, V03.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Sums and products with finite support

### Overview

The sums of the earlier sections run over a finset. A finset is data, and a sum over a whole type needs a `Fintype` instance, which is also data. Sometimes this is not what a proof wants. The index set can be a `Set` that is only known to be finite, or the function can be $0$ outside a finite set that changes with the point, as for a partition of unity. For these cases, Mathlib has the sum `finsum` and the product `finprod`.

The product `finprod f`, with the notation `∏ᶠ i, f i`, takes $f : \alpha \to M$ into a commutative monoid $M$. If the multiplicative support of $f$, the set of the points with $f(i) \ne 1$, is finite, the value is the product of $f$ over this set. If the support is infinite, the value is $1$. This second value is a junk value: it makes the function total, and the lemmas that need the true product have a hypothesis of finite support. The sum `finsum f`, with the notation `∑ᶠ i, f i`, is the additive twin, with the support and the value $0$.

The predicate for the hypothesis is `Function.HasFiniteMulSupport f`, and its additive twin is `Function.HasFiniteSupport f`. The two files on finite support define them and give the rules that prove them for sums, products and compositions of functions.

### The library around it

#### The definition

The definition of `finprod` is a case split. If `Function.HasFiniteMulSupport f` holds, then the support is a finite set, and `Set.Finite.toFinset` makes a finset from it. The value is the finset product of $f$ over that finset. If not, the value is $1$. The definition uses classical logic for the case split, so `finprod` is noncomputable. The domain can be any sort, so $f$ can also take a proof of a proposition as its argument. This is what makes the notation for a product over a set work.

The predicate `Function.HasFiniteMulSupport f` is by definition the statement that `Function.mulSupport f` is a finite set. The additive predicate `Function.HasFiniteSupport f` uses `Function.support f`. The file `Mathlib.Algebra.FiniteSupport.Defs` defines the two predicates and proves `Function.hasFiniteMulSupport_one` and `Function.hasFiniteSupport_zero` for the constant functions. Both predicates have the attribute of the fun_prop tactic, so this tactic can prove a goal of finite support from the rules of the next part.

| Lean name | Statement |
|---|---|
| `finprod_eq_prod` | for $h$ a proof of finite support, `∏ᶠ i, f i` is the finset product over the finset of $h$ |
| `finprod_eq_prod_of_mulSupport_subset` | if the support is in a finset $s$, then `∏ᶠ i, f i = ∏ i ∈ s, f i` |
| `finprod_of_infinite_mulSupport` | if the support is infinite, then `∏ᶠ i, f i = 1` |
| `finprod_eq_prod_of_fintype` | on a `Fintype`, `∏ᶠ i, f i = ∏ i, f i` |
| `finprod_one` | `∏ᶠ i, 1 = 1` |
| `finprod_eq_single` | if $f(x) = 1$ for $x \ne a$, then `∏ᶠ x, f x = f a` |
| `finprod_unique` | on a type with one element, the product is the value at that element |

The lemma `finprod_eq_prod_of_mulSupport_subset` is the main bridge to the finset library. Its proof is short. The support is a subset of $s$, so it is finite, and the definition gives the product over the support. The finset $s$ is the support plus some points where $f$ equals $1$, so the product over $s$ is the same by `Finset.prod_subset`, the rule of Section 2 for the points with value $1$. The additive form is `finsum_eq_sum_of_support_subset`.

#### Products over a set

The notation `∏ᶠ i ∈ s, f i` for a set $s$ is a nested product: the outer product runs over $i$, and the inner product runs over the proofs of $i \in s$. A product over the proofs of a proposition $p$ equals the value if $p$ is true and $1$ if not, by `finprod_eq_if`. So the inner product is the multiplicative indicator. The lemma `finprod_mem_def` states this: `∏ᶠ i ∈ s, f i` equals `∏ᶠ i, s.mulIndicator f i`, with `Set.mulIndicator` from Section 5 of this chapter. The same notation works for any proposition, so `∑ᶠ n < 5, f n` is the sum $f(0) + \cdots + f(4)$ over the natural numbers.

The rules for a product over a set match the finset rules of Section 1, with a hypothesis of finiteness where the finset rule needs none.

1. `finprod_mem_empty` gives the value $1$ over the empty set, and `finprod_mem_singleton` gives $f(a)$ over $\{a\}$.
2. `finprod_mem_insert` gives $f(a)$ times the product over $s$, for $a \notin s$ and $s$ finite.
3. `finprod_mem_insert_one` removes a point $a$ with $f(a) = 1$ and needs no finiteness.
4. `finprod_mem_union` splits the product over the union of two disjoint finite sets.
5. `finprod_mem_pair` gives $f(a) f(b)$ over $\{a, b\}$ for $a \ne b$.
6. `finprod_mem_coe_finset` says that the product over the set of a finset $s$ is the finset product over $s$.
7. `finprod_mem_eq_prod` writes the product over a set $s$ with $s \cap \mathrm{supp} f$ finite as a finset product.
8. `finprod_mem_univ` says that the product over `Set.univ` is the product over the type.

Why does `finprod_mem_insert` need $s$ finite? If $s$ is infinite and $f$ is not $1$ on an infinite part of $s$, both sides are junk. The left side is $1$. The right side is $f(a) \cdot 1 = f(a)$, which is not $1$ in general. So the hypothesis is necessary.

For a union of many sets, `finprod_mem_biUnion`, `finprod_mem_iUnion` and `finprod_mem_sUnion` give the product over a pairwise disjoint finite family of finite sets. A change of index is `finprod_mem_image` for a map that is injective on $s$, `finsum_mem_range` for an injective map, and `finprod_comp_equiv` for an equivalence. The equivalence form needs no finiteness: an equivalence takes the support to the support, so both sides are junk together or are true products together.

#### Algebra of finsum and finprod

The rules of Section 2 hold with hypotheses of finite support.

1. `finprod_mul_distrib` says $\prod^f (f_i g_i) = \prod^f f_i \cdot \prod^f g_i$ if $f$ and $g$ have finite support.
2. `finprod_mem_mul_distrib` is the same over a finite set $s$, with no hypothesis on the supports.
3. `MonoidHom.map_finprod` says that a monoid homomorphism commutes with `finprod` for $f$ with finite support.
4. `finprod_induction` proves $p(\prod^f f_i)$ from $p(1)$, from the closure of $p$ under products and from $p(f_i)$ for all $i$. It needs no finiteness, because the junk value $1$ satisfies $p$.
5. `finprod_mem_dvd` says $f(a)$ divides `finprod f` for $f$ with finite support.
6. `finprod_mem_comm` swaps two products over finite sets.

The hypotheses in item 1 are necessary. In $\mathbb{Q}$, let $g(n) = 1/2$ for all $n \in \mathbb{N}$, and let $f(n) = 2$ for $n \ne 0$ and $f(0) = 3$. Both supports are infinite, so the right side is $1 \cdot 1 = 1$. But $f g$ equals $1$ except at $0$, where it equals $3/2$, so the left side is $3/2$. The safe way is to prove finite support first.

The lemma `finsum_mul` says $(\sum^f f_i) r = \sum^f f_i r$ and needs `NoZeroDivisors`. The reason is again the junk value. For $r \ne 0$ in a ring with no zero divisors, $f_i r \ne 0$ exactly when $f_i \ne 0$, so the supports of $f$ and of $i \mapsto f_i r$ are the same set. If this set is infinite, both sides are $0$. If it is finite, the finset rule applies. For $r = 0$, both sides are $0$. In a ring with zero divisors, the support of $i \mapsto f_i r$ can be finite while the support of $f$ is infinite, and the rule fails. The form `finsum_mul'` takes a hypothesis of finite support in place of `NoZeroDivisors`. The same holds for `mul_finsum`, `finsum_smul` and `smul_finsum`.

For an ordered monoid, `finsum_nonneg` and `one_le_finprod` need no finiteness, since the junk value satisfies the bound. In contrast, `single_le_finsum` and `finsum_le_finsum` need finite support. The lemma `hasFiniteSupport_of_finsum_ne_zero` goes the other way: a nonzero `finsum` has finite support, since the junk value is $0$.

#### Proofs of finite support

The file `Mathlib.Algebra.FiniteSupport.Basic` gives the closure rules for the predicate. Each rule has the attribute of the fun_prop tactic, so this tactic can usually close a goal of finite support.

| Lean name | Statement |
|---|---|
| `Function.HasFiniteMulSupport.mul` | finite support for $f$ and $g$ gives it for $f g$ |
| `Function.HasFiniteMulSupport.fun_mul` | the same for the lambda form `fun i ↦ f i * g i` |
| `Function.HasFiniteMulSupport.inv` | finite support for $f$ gives it for $f^{-1}$ |
| `Function.HasFiniteSupport.fun_sub` | the same for a difference of two functions |
| `Function.HasFiniteMulSupport.comp` | finite support for $f$ and $g(1) = 1$ give it for $g \circ f$ |
| `Function.HasFiniteMulSupport.fun_comp_of_injective` | finite support for $f$ and $g$ injective give it for $f \circ g$ |
| `Function.HasFiniteMulSupport.prod` | a finset product of functions with finite support has finite support |
| `Function.HasFiniteMulSupport.pi` | on a finite type of values, finite support holds if it holds at each value |
| `Function.HasFiniteSupport.smul_right` | finite support of $g$ gives it for $f \bullet g$ |

The proof of `Function.HasFiniteMulSupport.mul` is a set inclusion: if $f(i) g(i) \ne 1$, then $f(i) \ne 1$ or $g(i) \ne 1$. So the support of $f g$ is a subset of the union of the two supports, and a subset of a finite set is finite by Chapter 5. Most rules in the file have this form. The rule `Function.HasFiniteMulSupport.of_eq_one_iff` moves the predicate from $f$ to $g$ when $f(a) = 1$ exactly when $g(a) = 1$.

#### Common errors

1. A rule of `finprod` used with no proof of finite support. Many rules, such as `finprod_mul_distrib` and `MonoidHom.map_finprod`, have such a hypothesis, and the goal that is left is easy to lose. Try the fun_prop tactic on the goal, or prove the finiteness of the support with the rules of Chapter 5.
2. A wrong form of the product over a set. The expression `∏ᶠ i ∈ s, f i` is a nested `finprod`, not a product over a subtype. Rewrite with `finprod_mem_def` or with `finprod_mem_coe_finset` before you use finset rules.
3. A computation that expects a value. The definition uses classical logic and is noncomputable, so the evaluation of a `finsum` does not reduce. Change it to a finset sum with `finsum_eq_sum_of_support_subset` and compute there.

### Exercises

1. (A) Let $f : \mathbb{N} \to \mathbb{N}$ be $f(n) = 1$ for all $n$. Compute `∑ᶠ n, f n` and `∏ᶠ n, f n` and give the lemma for each value.
2. (A) Prove `∏ᶠ i ∈ {a, b, c}, f i = f a * f b * f c` for distinct $a, b, c$ with `finprod_mem_insert` and `finprod_mem_pair`.
3. (B) Give an example in $\mathbb{Z} \times \mathbb{Z}$, which has zero divisors, of $f$ and $r$ with $(\sum^f f_i) r \ne \sum^f f_i r$. Use it to show that `finsum_mul` needs `NoZeroDivisors`.
4. (B) Prove that the support of $f + g$ is finite if the supports of $f$ and $g$ are finite, by the inclusion argument of `Function.HasFiniteMulSupport.mul`.
5. (B) Prove `finprod_induction` from `finprod_def`, the induction rule for finsets and a case split on finite support.
6. (C) Let $(t_i)_{i \in I}$ be a finite pairwise disjoint family of finite sets. Use `finprod_mem_biUnion` and `finprod_mem_comm` to prove that a double product over the pairs $(i, a)$ with $a \in t_i$ equals the product over the union.

### Reference

<?reference?>
