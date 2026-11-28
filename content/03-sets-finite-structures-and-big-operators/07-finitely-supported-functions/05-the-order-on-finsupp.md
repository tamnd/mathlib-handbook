---
title: The order on finitely supported functions
kind: api
modules:
  - Mathlib.Data.Finsupp.Order
  - Mathlib.Data.Finsupp.Interval
  - Mathlib.Data.Finsupp.NeLocus
  - Mathlib.Data.Finsupp.Lex
  - Mathlib.Data.Finsupp.WellFounded
  - Mathlib.Data.Finsupp.PWO
  - Mathlib.Data.Finsupp.Antidiagonal
explains:
  E2: [Finsupp.le_iff, Finsupp.single_le_iff, Finsupp.support_inf, Finsupp.card_Icc, Finsupp.neLocus_eq_support_sub, Finsupp.Lex.lt_iff, Finsupp.Lex.single_strictAnti, Finsupp.Colex.wellFoundedLT, Finsupp.wellQuasiOrderedLE]
  E1: auto
families: []
requires: [V03.C02, V03.C03, V03.C06, V04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The order on finitely supported functions

### Overview

A function $f : \iota \to_0 \alpha$ with values in an ordered type can be compared with another one point by point: $f \le g$ when $f(i) \le g(i)$ for each $i$. For $\alpha = \mathbb{N}$ this is the order of divisibility on the exponent vectors of monomials, and also the order of inclusion on multisets. The modules of this section give this pointwise order, its truncated subtraction, its finite intervals and its well-foundedness. They also give two other orders that matter for polynomials: the lexicographic order `Lex (ι →₀ α)` and the colexicographic order `Colex (ι →₀ α)`, which are linear orders.

The section continues Sections 1 and 2 of this chapter, which give the type `ι →₀ M`, the function `Finsupp.single` and the sums over the support. It uses the orders, the lattices and the intervals of Volume 4 as a language, and the finsets of Chapter 3. The next section uses the lexicographic orders to build the monomial orders of the polynomial rings.

### The library around it

#### The pointwise order

The relations `≤` and `<` on `ι →₀ α` come from the pointwise order on functions: `Finsupp.le_def` says $f \le g \iff \forall i,\ f(i) \le g(i)$. The module `Mathlib.Data.Finsupp.Order` adds the algebra. The instances `Finsupp.isOrderedAddMonoid` and `Finsupp.isOrderedCancelAddMonoid` say that addition is monotone when it is monotone in $\alpha$. When the zero of $\alpha$ is its bottom (the class `IsBotZeroClass`, true for $\mathbb{N}$), the zero function is the bottom, by the instance `Finsupp.orderBot`.

For a canonically ordered monoid such as $\mathbb{N}$ or $\mathbb{R}_{\ge 0}$, a point outside the support of $f$ gives $f(i) = 0 \le g(i)$ at once. So the comparison needs only the points of the support:

$$f \le g \iff \forall i \in \operatorname{supp} f,\ f(i) \le g(i).$$

This is `Finsupp.le_iff`, and `Finsupp.le_iff'` allows any finset that contains the support. It makes `≤` decidable, by `Finsupp.decidableLE`. The special case of one point is `Finsupp.single_le_iff`: $\operatorname{single}(i, x) \le f \iff x \le f(i)$. Its proof is `Finsupp.le_iff` with the support $\{i\}$, or nothing when $x = 0$. Other rules of the same kind are `Finsupp.single_le_single`, `Finsupp.single_mono`, `Finsupp.single_nonneg` and `Finsupp.add_eq_zero_iff` ($f + g = 0$ if and only if $f = 0$ and $g = 0$).

The support is monotone for this order (`Finsupp.support_monotone`). Over a linear order with zero at the bottom, the lattice operations act on supports as the set operations:

| Lean name | Statement |
|---|---|
| `Finsupp.support_inf` | $\operatorname{supp}(f \sqcap g) = \operatorname{supp} f \cap \operatorname{supp} g$ |
| `Finsupp.support_sup` | $\operatorname{supp}(f \sqcup g) = \operatorname{supp} f \cup \operatorname{supp} g$ |
| `Finsupp.disjoint_iff` | $f$ and $g$ are disjoint if and only if their supports are disjoint |
| `Finsupp.support_add_eq_union` | the support of $f + g$ is the union of the supports, in a canonically ordered monoid |

The proof of `Finsupp.support_inf` is one line at each point $i$: $\min(f(i), g(i)) \ne 0$ if and only if both values are not $0$, because $0$ is the least element and the order is linear.

#### Truncated subtraction

On $\mathbb{N}$ the subtraction is truncated: $3 - 5 = 0$. The instance `Finsupp.tsub` gives the same subtraction on `ι →₀ α`, point by point, with `Finsupp.tsub_apply` as its rule $(f - g)(i) = f(i) - g(i)$. The instance `Finsupp.orderedSub` says that it is the subtraction of an ordered monoid: $f - g \le h \iff f \le h + g$. With it, `ι →₀ ℕ` is a canonically ordered monoid (`Finsupp.instCanonicallyOrderedAddOfAddLeftMono`). The support can only shrink: `Finsupp.support_tsub` gives $\operatorname{supp}(f - g) \subseteq \operatorname{supp} f$, and `Finsupp.subset_support_tsub` gives $\operatorname{supp} f \setminus \operatorname{supp} g \subseteq \operatorname{supp}(f - g)$.

For exponent vectors in `ι →₀ ℕ`, the subtraction of one unit at a point is common in the proofs about derivatives of polynomials. The rules `Finsupp.sub_add_single_one_cancel`, `Finsupp.sub_single_one_add` and `Finsupp.add_sub_single_one` state the expected identities when $u(i) \ne 0$, for example $(u - \operatorname{single}(i, 1)) + \operatorname{single}(i, 1) = u$.

The module also compares sums and maps. `Finsupp.sum_le_sum_index` gives $f_1.\mathrm{sum}(h) \le f_2.\mathrm{sum}(h)$ when $f_1 \le f_2$ and each $h(i, \cdot)$ is monotone and sends $0$ to $0$. `Finsupp.single_le_sum` says that one term is at most the whole sum when the terms are nonnegative. `Finsupp.mapDomain_mono` and `Finsupp.embDomain_mono` say that the maps of the domain are monotone.

#### Finite intervals

If $\alpha$ is a locally finite order, for example $\mathbb{N}$, then each interval $[f, g]$ of `ι →₀ α` is finite, and `Finsupp.instLocallyFiniteOrder` gives the finsets `Finset.Icc f g`, `Finset.Ico f g` and so on. The construction is direct. Outside $\operatorname{supp} f \cup \operatorname{supp} g$ an element $h$ of the interval is $0$, and at a point $i$ of the union its value lies in the finite interval $[f(i), g(i)]$ of $\alpha$. The function `Finsupp.rangeIcc f g : ι →₀ Finset α` records these intervals, with `Finsupp.mem_rangeIcc_apply_iff`. Then `Finsupp.Icc_eq` writes the interval as `Finset.finsupp` of the union of the supports and this family. The card of a `Finset.finsupp` is a product (`Finset.card_finsupp`), so

$$\#[f, g] = \prod_{i \in \operatorname{supp} f \cup \operatorname{supp} g} \#[f(i), g(i)].$$

This is `Finsupp.card_Icc`. The rules `Finsupp.card_Ico`, `Finsupp.card_Ioc` and `Finsupp.card_Ioo` subtract $1$ or $2$ from it. For a lower interval, `Finsupp.card_Iic` gives $\#\{h \le f\} = \prod_{i \in \operatorname{supp} f} \#\{a \le f(i)\}$. With $\alpha = \mathbb{N}$ and `Nat.card_Iic`, this is $\prod_i (f(i) + 1)$: the number of divisors of $\prod_i p_i^{f(i)}$.

#### The locus where two functions differ

For $f, g : \alpha \to_0 N$, the finset `Finsupp.neLocus f g` holds the points where $f$ and $g$ differ (`Finsupp.mem_neLocus`, `Finsupp.coe_neLocus`). Its card is a Hamming distance between $f$ and $g$. The rules are those of a distance.

| Lean name | Statement |
|---|---|
| `Finsupp.neLocus_comm` | $\operatorname{neLocus}(f, g) = \operatorname{neLocus}(g, f)$ |
| `Finsupp.neLocus_eq_empty` | the locus is empty if and only if $f = g$ |
| `Finsupp.nonempty_neLocus_iff` | the locus is nonempty if and only if $f \ne g$ |
| `Finsupp.neLocus_zero_right` | $\operatorname{neLocus}(f, 0) = \operatorname{supp} f$ |
| `Finsupp.neLocus_add_left` | $\operatorname{neLocus}(f + g, f + h) = \operatorname{neLocus}(g, h)$ in a cancellative monoid |
| `Finsupp.neLocus_eq_support_sub` | $\operatorname{neLocus}(f, g) = \operatorname{supp}(f - g)$ in a group |

The last rule has a one line proof: $f(a) \ne g(a) \iff (f - g)(a) \ne 0$ in a group. The rules `Finsupp.subset_mapRange_neLocus` and `Finsupp.zipWith_neLocus_eq_left` control the locus under `Finsupp.mapRange` and `Finsupp.zipWith`.

#### Lexicographic and colexicographic orders

The pointwise order is not linear: $\operatorname{single}(1, 1)$ and $\operatorname{single}(2, 1)$ are not comparable. The relation `Finsupp.Lex r s` compares two functions at the first point where they differ, for a relation $r$ on the points and $s$ on the values. By `Finsupp.lex_def`, $\operatorname{Lex}\ r\ s\ a\ b$ holds when there is a point $j$ such that $a$ and $b$ agree at each $d$ with $r\ d\ j$, and $s\ (a\ j)\ (b\ j)$ holds. With the order relations this gives the type synonym `Lex (ι →₀ N)`, reached with `toLex`, and `Finsupp.Lex.lt_iff` states

$$a < b \iff \exists i,\ (\forall j < i,\ a(j) = b(j)) \wedge a(i) < b(i).$$

The synonym `Colex (ι →₀ N)` compares at the last point where they differ, by `Finsupp.Colex.lt_iff`. When both orders on $\iota$ and $N$ are linear, the two synonyms are linear orders (`Finsupp.Lex.linearOrder`, `Finsupp.Colex.linearOrder`) and ordered cancellative monoids (`Finsupp.Lex.isOrderedCancelAddMonoid`). Both refine the pointwise order: `Finsupp.toLex_monotone` and `Finsupp.toColex_monotone`.

The two orders treat the monomials $x_a$ in opposite ways. In the lexicographic order a smaller index gives a larger element: $\operatorname{toLex}(\operatorname{single}(b, 1)) < \operatorname{toLex}(\operatorname{single}(a, 1))$ when $a < b$, so the map $a \mapsto \operatorname{toLex}(\operatorname{single}(a, 1))$ is strictly antitone (`Finsupp.Lex.single_strictAnti`). The reason is that the two functions first differ at $a$, where the values are $1$ and $0$. In the colexicographic order the same map is strictly monotone (`Finsupp.Colex.single_strictMono`). The order $x_1 > x_2 > x_3 > \dots$ of the lexicographic order is the usual convention for polynomials. The bridge `Finsupp.lex_eq_invImage_dfinsupp_lex` reduces the order to the dependent functions of `DFinsupp`.

#### Well-foundedness

A well-founded order allows induction and the division algorithm of polynomials, so the library proves well-foundedness for each of the orders above.

1. The pointwise order: `Finsupp.wellFoundedLT'` says that `<` on `α →₀ N` is well founded when it is well founded on $N$ and $0$ is the bottom of $N$. The general form `Finsupp.wellFoundedLT` asks only that no value is below $0$, and `Finsupp.wellFoundedLT_of_finite` covers a finite type of points.
2. The colexicographic order: `Finsupp.Colex.wellFoundedLT` says that `Colex (α →₀ N)` is well founded when $\alpha$ is a well-founded linear order and $N$ is well founded with $0$ at the bottom. So `Colex (ℕ →₀ ℕ)` is well founded.
3. The lexicographic order: `Finsupp.Lex.wellFoundedLT` needs the reverse order `WellFoundedGT α` on the points. This condition is necessary. In `Lex (ℕ →₀ ℕ)` the sequence $\operatorname{single}(0, 1) > \operatorname{single}(1, 1) > \operatorname{single}(2, 1) > \cdots$ descends forever, by `Finsupp.Lex.single_strictAnti`. For a finite type of points no condition is needed: `Finsupp.Lex.wellFoundedLT_of_finite`.

The general theorems behind these instances are `Finsupp.Lex.acc`, `Finsupp.Lex.wellFounded` and `Finsupp.Lex.wellFounded'`. They work with any relations $r$ and $s$, with the condition that no value is $s$-below $0$.

The module `Mathlib.Data.Finsupp.PWO` has one result, the lemma of Dickson. The instance `Finsupp.wellQuasiOrderedLE` says that `σ →₀ α` is well quasi ordered when $\sigma$ is finite and $\alpha$ is well quasi ordered. For `σ →₀ ℕ` it says: each infinite sequence of monomials in finitely many variables has two terms $m_i, m_j$ with $i < j$ and $m_i \mid m_j$. This is the key fact behind the finiteness of Gröbner bases.

#### The antidiagonal

The module `Mathlib.Data.Finsupp.Antidiagonal` gives the instance `Finsupp.instHasAntidiagonal`: for $f : \alpha \to_0 \mathbb{N}$, the finset `Finset.HasAntidiagonal.antidiagonal f` holds the pairs $(g, h)$ with $g + h = f$. These are the pairs of monomials whose product is the monomial of $f$, so this finset appears in the product rule for the coefficients of multivariate polynomials. The rules are `Finsupp.antidiagonal_zero` (the antidiagonal of $0$ is $\{(0, 0)\}$), `Finsupp.antidiagonal_single` (the antidiagonal of $\operatorname{single}(a, n)$ is the image of the antidiagonal of $n$ in $\mathbb{N}$) and `Finsupp.sum_antidiagonal_swap` (a sum over the antidiagonal does not change when the two parts swap). The function `Finsupp.antidiagonal'` is the same object as a function to $\mathbb{N}$, used to build the finset.

#### Common errors

1. A learner writes `f ≤ g` for `f g : Lex (ι →₀ ℕ)` and expects the pointwise order. On the synonym `Lex` the relation is the lexicographic order. Use `toLex` and `ofLex` to move between the two, and `Finsupp.toLex_monotone` to pass from the pointwise order to the lexicographic one.
2. A learner applies `Finsupp.Lex.wellFoundedLT` to `Lex (ℕ →₀ ℕ)` and the instance search fails. The instance needs `WellFoundedGT` on the points, and it is false for $\mathbb{N}$. Use `Colex`, or the dual order on the points, or a finite type of points.
3. A learner uses `Finsupp.le_iff` with values in $\mathbb{Z}$. The rule needs a canonically ordered monoid. For $\mathbb{Z}$ the points outside the support matter, because $g(i)$ can be negative there, and only `Finsupp.le_def` holds.

### Exercises

1. (A) In `ℕ →₀ ℕ`, compute $f - g$ and $f \sqcap g$ for $f = \operatorname{single}(0, 3) + \operatorname{single}(2, 1)$ and $g = \operatorname{single}(0, 1) + \operatorname{single}(1, 4)$, and check `Finsupp.support_inf` on them.
2. (A) Use `Finsupp.card_Iic` to count the functions $h \le f$ for $f = \operatorname{single}(0, 2) + \operatorname{single}(1, 3)$ in `ℕ →₀ ℕ`, and relate the answer to the divisors of $2^2 3^3$.
3. (A) Show that $\#\operatorname{neLocus}(f, h) \le \#\operatorname{neLocus}(f, g) + \#\operatorname{neLocus}(g, h)$.
4. (B) Order the monomials $x_0^2$, $x_0 x_1$, $x_1^3$ and $x_2$ of `Fin 3 →₀ ℕ` in `Lex` and in `Colex`.
5. (B) Prove `Finsupp.single_le_iff` from `Finsupp.le_iff`, with the two cases $x = 0$ and $x \ne 0$.
6. (C) Prove the lemma of Dickson for `Fin 2 →₀ ℕ` from the fact that each sequence in $\mathbb{N}$ has a monotone subsequence.

### Reference

<?reference?>
