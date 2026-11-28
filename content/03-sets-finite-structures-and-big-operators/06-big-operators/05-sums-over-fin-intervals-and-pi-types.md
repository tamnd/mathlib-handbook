---
title: Sums over Fin, intervals and function types
kind: api
modules:
  - Mathlib.Algebra.BigOperators.Fin
  - Mathlib.Algebra.BigOperators.Finsupp.Fin
  - Mathlib.Algebra.BigOperators.Option
  - Mathlib.Algebra.BigOperators.Sym
  - Mathlib.Algebra.BigOperators.Group.Finset.Interval
  - Mathlib.Algebra.BigOperators.Group.Finset.Gaps
  - Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
  - Mathlib.Algebra.BigOperators.Group.Finset.Pi
  - Mathlib.Algebra.BigOperators.Group.Finset.Preimage
  - Mathlib.Algebra.BigOperators.Group.Finset.Indicator
  - Mathlib.Algebra.BigOperators.Pi
  - Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
explains:
  E2: [Fin.prod_univ_succ, Fin.prod_univ_castSucc, Fin.prod_const, Fin.prod_univ_add, finFunctionFinEquiv_apply, Finset.prod_Ico_mul_eq_prod_Icc, Finset.prod_insertNone, Finset.prod_mulIndicator_subset, Finset.prod_apply]
  E1: auto
families: []
requires: [V03.C03, V03.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Sums over Fin, intervals and function types

### Overview

Sections 1 and 2 summed over a finset and over `Finset.range n`. Many sums in practice have another index set: the type $\mathrm{Fin}\ n$ of the numbers $0, \ldots, n - 1$, an interval $[a, b]$ of a general order, the type $\mathrm{Option}\ \alpha$ with one more element, or a whole type with `Finset.univ`. The summands can also have values in a product of monoids, or in a type of functions. This section gives the library for these cases.

The modules have one theme each. The file on Fin gives the induction rules for sums over $\mathrm{Fin}(n + 1)$ and the coding of tuples by numbers. The interval files give the splitting rules at the endpoints of $[a, b]$. The files on Option, on preimages and on indicators change the index set. The file on Pi types computes a sum of functions point by point. Each product rule has a sum twin, with the same name after "prod" becomes "sum".

### The library around it

#### Sums over Fin

For a function $f : \mathrm{Fin}\ n \to M$, the sum `∑ i, f i` runs over `Finset.univ` of $\mathrm{Fin}\ n$. There is no finset `range n` here, so the induction on $n$ needs two rules that split off one element. They differ in which element.

| Lean name | Statement |
|---|---|
| `Fin.prod_univ_zero` | $\prod_{i : \mathrm{Fin}\ 0} f(i) = 1$ |
| `Fin.prod_univ_succ` | $\prod_{i : \mathrm{Fin}(n+1)} f(i) = f(0) \cdot \prod_{i : \mathrm{Fin}\ n} f(i + 1)$ |
| `Fin.prod_univ_castSucc` | $\prod_{i : \mathrm{Fin}(n+1)} f(i) = \bigl(\prod_{i : \mathrm{Fin}\ n} f(i)\bigr) \cdot f(n)$ |
| `Fin.prod_univ_add` | $\prod_{i : \mathrm{Fin}(a+b)} f(i) = \prod_{i < a} f(i) \cdot \prod_{j < b} f(a + j)$ |
| `Fin.prod_const` | $\prod_{i : \mathrm{Fin}\ n} x = x^n$ |
| `Fin.sum_const` | $\sum_{i : \mathrm{Fin}\ n} x = n \cdot x$ |
| `Fin.prod_cons` | the product of the tuple $(x, f_0, \ldots, f_{n-1})$ is $x \cdot \prod f$ |
| `Fin.sum_snoc` | the sum of the tuple $(f_0, \ldots, f_{n-1}, x)$ is $\sum f + x$ |
| `Fin.prod_ofFn` | the list product of the list of values of $f$ is $\prod_i f(i)$ |

In `Fin.prod_univ_succ`, the map $i \mapsto i + 1$ is the successor map, from $\mathrm{Fin}\ n$ to $\mathrm{Fin}(n + 1)$. In `Fin.prod_univ_castSucc`, the map is the cast map, which keeps the value and enlarges the type, and the last element is $n$. The proof of `Fin.prod_univ_succ` is a reindexing. The type $\mathrm{Fin}(n + 1)$ is the disjoint union of $\{0\}$ and the image of the successor map, which is injective. The splitting rule of Section 2 and the sum over an image give the claim. The proof of `Fin.prod_univ_castSucc` is the same with the image of the cast map and the point $n$. The rule `Fin.prod_univ_add` is the general form: $\mathrm{Fin}(a + b)$ is the disjoint union of the images of the two embeddings of $\mathrm{Fin}\ a$ and $\mathrm{Fin}\ b$.

The file also gives the closed forms for small $n$: `Fin.prod_univ_one`, `Fin.prod_univ_two` and so on to `Fin.prod_univ_eight`, for example `Fin.sum_univ_two` states $\sum_{i : \mathrm{Fin}\ 2} f(i) = f(0) + f(1)$. A call of the simp tactic with these lemmas expands a sum over a small $\mathrm{Fin}\ n$ into its terms.

The partial products `Fin.partialProd` and `Fin.partialSum` take $f : \mathrm{Fin}\ n \to M$ to the tuple of length $n + 1$ of the products of the first $j$ values. So `Fin.partialProd_zero` gives the value $1$ at $j = 0$, and `Fin.partialProd_succ` gives the step $P(j + 1) = P(j) \cdot f(j)$. In a group, the partial products have an inverse: `Fin.partialProd_left_inv` recovers $f$ from the quotients $f(i)^{-1} f(i + 1)$ of consecutive values. This is the discrete form of the fundamental theorem of calculus.

#### Tuples as numbers

The file `Mathlib.Algebra.BigOperators.Fin` also counts. Three equivalences make the card rules of Chapter 4 concrete.

1. `finFunctionFinEquiv` is an equivalence between $\mathrm{Fin}\ n \to \mathrm{Fin}\ m$ and $\mathrm{Fin}(m^n)$.
2. `finPiFinEquiv` is an equivalence between the dependent functions $\prod_i \mathrm{Fin}(n_i)$ and $\mathrm{Fin}(\prod_i n_i)$.
3. `finSigmaFinEquiv` is an equivalence between the dependent pairs $\Sigma_i \mathrm{Fin}(n_i)$ and $\mathrm{Fin}(\sum_i n_i)$.

The first one is the expansion in base $m$: by `finFunctionFinEquiv_apply`, the tuple $(d_0, \ldots, d_{n-1})$ goes to $\sum_{i < n} d_i m^i$. So each number below $m^n$ has exactly one expansion with $n$ digits in base $m$. The map is injective because two expansions with a first difference at the digit $i$ differ by a nonzero multiple of $m^i$ plus a smaller term. It is surjective because the two sides have the same card $m^n$. The tuple $(1, 0, 1)$ in base $2$ goes to $1 + 0 \cdot 2 + 1 \cdot 4 = 5$.

The file `Mathlib.Algebra.BigOperators.Finsupp.Fin` gives the rule `Finsupp.sum_cons` for the finitely supported functions on $\mathrm{Fin}(n + 1)$, and the equivalence `finTwoArrowEquiv'` of the finitely supported functions on $\mathrm{Fin}\ 2$ with $M \times M$.

#### Intervals of a locally finite order

A locally finite order has finite intervals `Finset.Icc a b`, `Finset.Ico a b`, `Finset.Ioc a b` and `Finset.Ioo a b`. Section 2 gave the rules for the intervals of $\mathbb{N}$, such as `Finset.prod_Ico_consecutive`. The file `Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite` gives the rules for a general locally finite order. They add or remove one endpoint, and the name says which.

| Lean name | Statement, for $a \le b$ |
|---|---|
| `Finset.prod_Ico_mul_eq_prod_Icc` | $\prod_{[a, b)} f \cdot f(b) = \prod_{[a, b]} f$ |
| `Finset.sum_Ioc_add_eq_sum_Icc` | $\sum_{(a, b]} f + f(a) = \sum_{[a, b]} f$ |
| `Finset.mul_prod_Ioi_eq_prod_Ici` | $f(a) \cdot \prod_{x > a} f(x) = \prod_{x \ge a} f(x)$ |
| `Finset.prod_Ioi_mul_eq_prod_Ici` | $\prod_{x > a} f(x) \cdot f(a) = \prod_{x \ge a} f(x)$ |

The proof of `Finset.prod_Ico_mul_eq_prod_Icc` is one line: for $a \le b$, $[a, b]$ is the insert of $b$ into $[a, b)$, and $b \notin [a, b)$, so the insert rule of Section 1 applies. The lemma `Finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag` turns a sum over the pairs $j > i$ into a sum over all pairs $i \ne j$, for a finite linear order. The lemma `Finset.prod_eq_prod_range_sdiff` writes the product over the last finset of an increasing chain $s_0 \subseteq s_1 \subseteq \cdots$ as the product over $s_0$ times the products over the differences $s_{i + 1} \setminus s_i$.

The file `Mathlib.Algebra.BigOperators.Group.Finset.Interval` has the rules for the symmetric intervals of $\mathbb{Z}$. For instance `Finset.prod_Icc_eq_prod_Ico_mul` is the endpoint rule on $\mathbb{Z}$, `Finset.sum_Ico_int_sub` is a telescope over $[-b, b)$, and `Finset.sum_Icc_of_even_eq_range` folds the sum of an even function over $[-N, N]$ to $2 \sum_{m = 0}^{N} f(m) - f(0)$. The file `Mathlib.Algebra.BigOperators.Group.Finset.Gaps` uses the finset `Finset.intervalGapsWithin` of the gaps between a finite family of disjoint closed intervals of $[a, b]$. Its rule `Finset.sum_intervalGapsWithin_add_sum_eq_sub` says that $g(b) - g(a)$ is the sum of the increments of $g$ over the intervals plus the sum of the increments over the gaps. This is a telescope over a cut of $[a, b]$.

#### Changing the index set

1. Option: `Finset.prod_insertNone` says that the product over `Finset.insertNone s`, a finset of $\mathrm{Option}\ \alpha$, is $f(\mathrm{none}) \cdot \prod_{x \in s} f(\mathrm{some}\ x)$. The proof is the insert rule: none is not the image of an element of $s$. The lemma `Finset.prod_eraseNone` goes the other way.
2. Preimages: `Finset.prod_preimage` sums over `Finset.preimage s f`, the finset of the points that $f$ sends into $s$, for an $f$ that is injective on this set. The values of $g$ outside the range of $f$ must be $1$.
3. Symmetric powers: `Finset.sum_count_of_mem_sym` says that the multiplicities of an element of `Finset.sym s m` add up to $m$, and `Finset.sum_sym2_filter_not_isDiag` turns a sum over the unordered pairs with distinct entries into a sum over the ordered pairs $(i, j)$ with $i < j$.
4. Pi finsets: `Finset.prod_univ_pi` reindexes a product over `Finset.univ.pi t`, the finset of the dependent functions with values in the finsets $t_i$.

#### Indicators

The indicator `Set.indicator s f` equals $f$ on $s$ and $0$ off $s$, and `Set.mulIndicator` is its twin with $1$. The file `Mathlib.Algebra.BigOperators.Group.Finset.Indicator` gives the rules for a sum of an indicator. The lemma `Finset.prod_mulIndicator_subset` says that $\prod_{i \in t} (\mathbf{1}_s f)(i) = \prod_{i \in s} f(i)$ for $s \subseteq t$. The proof splits $t$ into $s$ and $t \setminus s$. On $s$, the indicator is $f$. On $t \setminus s$, it is $1$, so that part contributes $1$. The form with no inclusion is `Finset.prod_mulIndicator_eq_prod_inter`, over $s \cap t$. The lemma `Finset.indicator_sum` says that the indicator of a sum is the sum of the indicators, and `Finset.mulIndicator_biUnion` says that the indicator of a disjoint union is the product of the indicators.

#### Sums of functions and of pairs

The file `Mathlib.Algebra.BigOperators.Pi` computes a sum of functions point by point. The lemma `Finset.prod_apply` says $(\prod_{c \in s} g_c)(a) = \prod_{c \in s} g_c(a)$. The proof is induction on $s$: the product of functions is defined point by point, so the insert rule commutes with the evaluation at $a$. The same holds for pairs, with `Prod.fst_prod` and `Prod.snd_sum`, and for multisets of functions, with `Pi.multiset_prod_apply`.

For a finite index type, each function is a sum of its single values. The lemma `Finset.univ_sum_single` says $\sum_i \mathrm{single}_i(f(i)) = f$, where `Pi.single i x` is the function with value $x$ at $i$ and $0$ elsewhere. So `Pi.single_induction` proves a property of all functions from the property for the singles, for $0$ and for sums. A homomorphism out of the functions is determined by its values on the singles: `MonoidHom.functions_ext`, `AddMonoidHom.functions_ext` and `RingHom.functions_ext` are the rules of extensionality. The equivalence `Pi.monoidHomMulEquiv` is the universal property of the finite product of commutative monoids: a homomorphism out of $\prod_i M_i$ is a family of homomorphisms out of the $M_i$.

The file `Mathlib.Algebra.BigOperators.Group.Finset.Lemmas` has rules of the same kind. The lemma `MonoidHom.finsetProd_apply` evaluates a product of homomorphisms, `Finset.isSquare_prod` and `Finset.even_sum` say that a product of squares is a square and a sum of even elements is even, and `Finset.support_sum` bounds the support of a sum by the union of the supports.

#### Common errors

1. The two induction rules for $\mathrm{Fin}(n + 1)$ split off different elements. If a goal has $f(0)$ outside the sum, use `Fin.prod_univ_succ`. If it has the last value outside, use `Fin.prod_univ_castSucc`. A wrong choice gives a goal with the successor map where the hypothesis has the cast map.
2. The endpoint rules need $a \le b$. For $a > b$, the interval $[a, b]$ is empty, but $[a, b)$ plus the point $b$ is not.
3. A sum over a type of functions, `∑ c ∈ s, g c` with `g c : α → M`, is a function. Before the simp tactic can work on the value at $a$, rewrite with `Finset.sum_apply`, because the evaluation does not reduce by itself under the sum.

### Exercises

1. (A) Compute $\sum_{i : \mathrm{Fin}\ 4} (i + 1)^2$ with `Fin.sum_univ_succ` and with `Fin.sum_univ_castSucc`, and compare the steps.
2. (A) Find the tuple of $\mathrm{Fin}\ 3 \to \mathrm{Fin}\ 10$ that `finFunctionFinEquiv` sends to $472$.
3. (B) Prove $\sum_{x \in [a, b]} f(x) = \sum_{x \in (a, b)} f(x) + f(a) + f(b)$ for $a < b$ in a locally finite order, with two endpoint rules.
4. (B) Let $s \subseteq t$ be finsets. Prove $\sum_{i \in t} \mathbf{1}_s(i) = |s|$ with `Finset.sum_indicator_subset`.
5. (B) Use `Finset.sum_Icc_of_even_eq_range` to compute $\sum_{m = -3}^{3} m^2$.
6. (C) Prove `Fin.prod_univ_add` by induction on $b$ with `Fin.prod_univ_castSucc`.

### Reference

<?reference?>
