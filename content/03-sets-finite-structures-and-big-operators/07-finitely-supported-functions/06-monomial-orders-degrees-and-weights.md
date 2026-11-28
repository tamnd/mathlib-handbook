---
title: Monomial orders, degrees and weights
kind: api
modules:
  - Mathlib.Data.Finsupp.MonomialOrder
  - Mathlib.Data.Finsupp.MonomialOrder.DegLex
  - Mathlib.Data.Finsupp.Weight
explains:
  E2: [MonomialOrder, MonomialOrder.lex, MonomialOrder.degLex, Finsupp.DegLex.lt_iff, Finsupp.degree_apply, Finsupp.weight_apply, Finsupp.le_degree, Finsupp.finite_of_degree_le]
  E1: auto
families: []
requires: [V03.C03, V03.C06, V04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Monomial orders, degrees and weights

### Overview

A monomial $x_1^{a_1} \cdots x_n^{a_n}$ in the variables of a type $\sigma$ is coded by its exponent vector $a : \sigma \to_0 \mathbb{N}$. The product of two monomials is the sum of their exponent vectors. The division algorithm and the Gröbner bases of multivariate polynomials need a way to say which monomial of a polynomial is the leading one. A *monomial order* is a linear order on $\sigma \to_0 \mathbb{N}$ that is compatible with addition, in which $0$ is the least element, and which is well founded.

The modules of this section give the structure `MonomialOrder σ` for such an order, its two standard examples (the lexicographic order and the graded lexicographic order), and the degree and the weighted degree of an exponent vector. They build on the lexicographic order and the well-foundedness results of the section before. The polynomial rings of the volume on commutative algebra use them for the leading term and the division algorithm.

### The library around it

#### The structure of a monomial order

There can be several monomial orders on the same type $\sigma \to_0 \mathbb{N}$, and a proof often needs two at the same time. So a monomial order is not an instance on $\sigma \to_0 \mathbb{N}$. It is a structure `MonomialOrder σ` that carries a separate type with the order. The fields are:

1. `MonomialOrder.syn`, a type, the *synonym*, which carries a linear order (`MonomialOrder.linearOrderSyn`) and a structure of ordered cancellative commutative monoid (`MonomialOrder.isOrderedCancelAddMonoid_syn`);
2. `MonomialOrder.toSyn`, an additive equivalence `(σ →₀ ℕ) ≃+ m.syn`;
3. the proof that `MonomialOrder.toSyn` is monotone for the pointwise order (`MonomialOrder.toSyn_monotone`);
4. the proof that the order on the synonym is well founded (`MonomialOrder.wellFoundedLT_syn`).

To compare $c, d : \sigma \to_0 \mathbb{N}$ for an order $m$, the library compares `m.toSyn c` and `m.toSyn d`. After `open scoped MonomialOrder` the notations `c ≼[m] d` and `c ≺[m] d` stand for these two comparisons.

The first consequences follow from the fields. The monotonicity gives $0 \le a$ for each $a$, because $0 \le a$ in the pointwise order: this is `MonomialOrder.zero_le`, and `MonomialOrder.bot_eq_zero` says that $0$ is the bottom. Then addition gives `MonomialOrder.le_add_right`: $\operatorname{toSyn}(a) \le \operatorname{toSyn}(a) + \operatorname{toSyn}(b)$. The equivalence is injective and monotone, so it is strictly monotone (`MonomialOrder.toSyn_strictMono`). For the degree of the zero polynomial the library uses $\bot$, and `MonomialOrder.toWithBotSyn` extends `MonomialOrder.toSyn` to `WithBot (σ →₀ ℕ)`, with the rules `MonomialOrder.toWithBotSyn_apply_bot` and `MonomialOrder.toWithBotSyn_apply_coe`.

#### The lexicographic monomial order

Let $\sigma$ be a linear order with `WellFoundedGT σ`, for example `Fin n`. Then `MonomialOrder.lex` is the monomial order whose synonym is `Lex (σ →₀ ℕ)`. The rules `MonomialOrder.lex_le_iff` and `MonomialOrder.lex_lt_iff` say that its comparison is the comparison of `toLex c` and `toLex d`. So $c < d$ when $c$ and $d$ agree at each variable before some variable $i$ and $c(i) < d(i)$.

Each field has a short proof from the section before. The order is linear and compatible with addition by `Finsupp.Lex.linearOrder` and `Finsupp.Lex.isOrderedCancelAddMonoid`. It refines the pointwise order by `Finsupp.toLex_monotone`. It is well founded by `Finsupp.Lex.wellFoundedLT`, and this is the place where the condition `WellFoundedGT σ` is needed. In this order $x_0 > x_1 > x_2 > \cdots$, the usual convention of algebraic geometry.

#### The graded lexicographic order

The graded order compares first the total degrees, and then breaks ties with the lexicographic order. The type synonym `DegLex α` has the maps `toDegLex` and `ofDegLex`, with the usual rules `toDegLex_ofDegLex`, `ofDegLex_toDegLex` and `toDegLex_add`. The relation `Finsupp.DegLex r s` is defined by `Finsupp.degLex_def` as the lexicographic order on the pair $(\deg a, a)$. With the order relations, `Finsupp.DegLex.lt_iff` states

$$a < b \iff \deg a < \deg b \ \text{ or } \ (\deg a = \deg b \text{ and } \operatorname{toLex} a < \operatorname{toLex} b).$$

The instances `Finsupp.DegLex.instLinearOrderDegLexNat`, `Finsupp.DegLex.instIsOrderedCancelAddMonoidDegLexNat` and `Finsupp.DegLex.orderBot` give the algebra of the order. The degree is monotone along it (`Finsupp.DegLex.monotone_degree`). On the variables the order is reversed as for `Lex`: `Finsupp.DegLex.single_strictAnti` says that $a \mapsto \operatorname{toDegLex}(\operatorname{single}(a, 1))$ is strictly antitone.

The graded order has an advantage over the lexicographic order. It is well founded under the same condition `WellFoundedGT α` (`Finsupp.DegLex.wellFoundedLT`), but each monomial has only finitely many monomials below it when $\sigma$ is finite, because there are finitely many exponent vectors of each degree. The monomial order `MonomialOrder.degLex` packs it, with `MonomialOrder.degLex_le_iff` and `MonomialOrder.degLex_lt_iff` as the bridge to `DegLex (σ →₀ ℕ)`. The general theorem behind the well-foundedness is `Finsupp.DegLex.wellFounded`.

#### Degree and weight

The module `Mathlib.Data.Finsupp.Weight` gives two additive maps on exponent vectors. The degree `Finsupp.degree : (σ →₀ R) →+ R` is the sum of all values: `Finsupp.degree_apply` states $\deg d = \sum_{i \in \operatorname{supp} d} d(i)$, and `Finsupp.degree_eq_sum` states $\deg d = \sum_i d(i)$ over a finite type. The weighted degree `Finsupp.weight w` gives a weight $w(i)$ in a module $M$ to each variable, and `Finsupp.weight_apply` states

$$\operatorname{weight}_w(f) = \sum_{i \in \operatorname{supp} f} f(i) \cdot w(i).$$

The degree is the weight with all weights $1$ (`Finsupp.degree_eq_weight_one`). Both maps are additive, so they are determined by their values on singles: `Finsupp.degree_single` and `Finsupp.weight_single` give $\deg \operatorname{single}(a, r) = r$ and $\operatorname{weight}_w(\operatorname{single}(s, r)) = r \cdot w(s)$.

The order properties hold for a canonically ordered monoid of values, for example $\mathbb{N}$.

| Lean name | Statement |
|---|---|
| `Finsupp.le_degree` | $f(s) \le \deg f$ |
| `Finsupp.degree_mono` | the degree is monotone for the pointwise order |
| `Finsupp.degree_eq_zero_iff` | $\deg d = 0 \iff d = 0$ |
| `Finsupp.le_weight_of_ne_zero` | $w(s) \le \operatorname{weight}_w(f)$ when $f(s) \ne 0$ and all weights are nonnegative |
| `Finsupp.weight_sub_single_add` | $\operatorname{weight}_w(f - \operatorname{single}(i, 1)) + w(i) = \operatorname{weight}_w(f)$ when $f(i) \ne 0$ |
| `Finsupp.exists_le_degree_eq` | for each $n \le \deg f$ there is $g \le f$ with $\deg g = n$ |

The proof of `Finsupp.le_degree` is one line: $f(s)$ is one term of the sum $\sum_i f(i)$, and the other terms are nonnegative. If $s$ is not in the support, then $f(s) = 0$.

A weight is *nontorsion* when no multiple $n \cdot w(i)$ with $n \ne 0$ is zero. The class `Finsupp.NonTorsionWeight R w` records this, and `Finsupp.nonTorsionWeight_of` gives it for nonzero weights in a torsion free module over a domain. With it, `Finsupp.weight_eq_zero_iff_eq_zero` says that the weighted degree of $f$ is $0$ only for $f = 0$.

For finitely many variables there are only finitely many exponent vectors of a given degree: `Finsupp.finite_of_degree_eq`, `Finsupp.finite_of_degree_le` and `Finsupp.finite_of_degree_lt`. The proof of the second one: if $\deg f \le n$, then $f(i) \le n$ for each $i$ by `Finsupp.le_degree`, so $f$ lies in the finite interval $[0, (n, \dots, n)]$ of `σ →₀ ℕ`. The rules `Finsupp.finite_of_nat_weight_le` and its two relatives do the same for a weighted degree with nonzero weights in $\mathbb{N}$. The last results of the module connect the degree to sets of monomials. `Finsupp.range_single_one` says that the exponent vectors of degree $1$ are the singles $\operatorname{single}(a, 1)$, and `Finsupp.image_pow_eq_finsuppProd_image` writes the $n$-th power of an image set in a commutative monoid as the set of products $\prod_i f(x_i)^{e_i}$ with $\deg e = n$.

#### Common errors

1. A learner writes `c ≤ d` and expects the comparison of a monomial order. On `σ →₀ ℕ` the relation `≤` is the pointwise order. Use `m.toSyn c ≤ m.toSyn d`, or the notation `c ≼[m] d` after `open scoped MonomialOrder`.
2. A learner tries `MonomialOrder.lex` on the variables `ℕ` and the instance `WellFoundedGT ℕ` is not found. It is false: the lexicographic order on `ℕ →₀ ℕ` with $x_0 > x_1 > \cdots$ is not well founded. Use a finite type of variables, such as `Fin n`.
3. A learner uses `Finsupp.degree` for a weighted degree with all weights $2$. The degree is the weight with all weights $1$. Use `Finsupp.weight (fun _ => 2)`.

### Exercises

1. (A) Order the exponent vectors of $x_0^2$, $x_0 x_1$, $x_1^2$, $x_0$ and $x_1^3$ in `Fin 2 →₀ ℕ` for `MonomialOrder.lex` and for `MonomialOrder.degLex`.
2. (A) Compute $\operatorname{weight}_w(f)$ for $f = \operatorname{single}(0, 2) + \operatorname{single}(1, 3)$ and the weights $w(0) = 5$, $w(1) = 7$ in $\mathbb{N}$.
3. (A) Show that in any monomial order, $a \le b$ in the pointwise order implies $\operatorname{toSyn}(a) \le \operatorname{toSyn}(b)$, and that the converse fails for `MonomialOrder.lex` on two variables.
4. (B) Count the exponent vectors of degree $n$ in `Fin k →₀ ℕ`, and conclude `Finsupp.finite_of_degree_eq` for $\sigma = $ `Fin k`.
5. (C) Show that in `DegLex (Fin 2 →₀ ℕ)` each element has only finitely many elements below it, and that this fails in `Lex (Fin 2 →₀ ℕ)`.

### Reference

<?reference?>
