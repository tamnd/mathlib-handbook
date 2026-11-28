---
title: Summable families of Hahn series
kind: api
modules:
  - Mathlib.RingTheory.HahnSeries.Summable
  - Mathlib.RingTheory.HahnSeries.HEval
  - Mathlib.RingTheory.HahnSeries.Binomial
explains:
  E2: [HahnSeries.SummableFamily, HahnSeries.SummableFamily.coeff_hsum, HahnSeries.SummableFamily.hsum_mul, HahnSeries.SummableFamily.one_sub_self_mul_hsum_powers, HahnSeries.isUnit_of_orderTop_pos, HahnSeries.inv_def, PowerSeries.heval_X, HahnSeries.SummableFamily.binomialFamily_apply, HahnSeries.pow_add]
  E1: auto
families: []
requires: [V04, V06.C01, V06.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Summable families of Hahn series

### Overview

A ring of Hahn series has no topology in the library, but it has a good notion of an infinite sum. A family $(x_i)_{i \in \alpha}$ of Hahn series can be summed coefficientwise if two conditions hold: each coefficient $g$ is nonzero in only finitely many $x_i$, and the union of the supports is partially well-ordered. The first condition makes each coefficient of the sum a finite sum. The second condition makes the sum a Hahn series again. The geometric series $\sum_n x^n$ is such a family when the order of $x$ is positive.

This section covers the type of summable families and its sum, the algebra of these sums, and three uses of them. The first use is the inverse of a Hahn series, which gives the units of the ring and the field instance. The second use is the substitution of a series of positive order into a formal power series. The third use is the binomial power $x^r$ of a series $x = 1 + (\text{higher terms})$, for an exponent $r$ in a binomial ring. The previous section gives the ring of Hahn series, its order and its leading coefficient.

### The library around it

#### The type of summable families

The structure `HahnSeries.SummableFamily Γ R α` needs `[PartialOrder Γ] [AddCommMonoid R]`. It is a function $s : \alpha \to$ `HahnSeries Γ R` with two proofs, the two conditions of the overview. The constructor `HahnSeries.SummableFamily.mk` takes the function, a proof that $\bigcup_i \operatorname{supp}(s_i)$ is partially well-ordered, and for each $g$ a proof that $\{i \mid (s_i)_g \ne 0\}$ is finite. The structure has a coercion to functions (`HahnSeries.SummableFamily.instFunLike`), and the API reads the two proofs with `HahnSeries.SummableFamily.isPWO_iUnion_support` and `HahnSeries.SummableFamily.finite_co_support`. Two families are equal if they agree at each index (`HahnSeries.SummableFamily.ext`).

The sum is `HahnSeries.SummableFamily.hsum`.

> `HahnSeries.SummableFamily.coeff_hsum`: $(\sum_i s_i)_g = \sum^{f}_i (s_i)_g$, a sum with finite support.

This is the definition, and it is a Hahn series because its support is in $\bigcup_i \operatorname{supp}(s_i)$ (`HahnSeries.SummableFamily.support_hsum_subset`). `HahnSeries.SummableFamily.coeff_hsum_eq_sum` writes the same sum as a `Finset` sum over the indices with a nonzero coefficient at $g$, and `HahnSeries.SummableFamily.coeff_hsum_eq_sum_of_subset` allows each larger finite set of indices.

Each finite family is summable. The constructors are `HahnSeries.SummableFamily.ofFinsupp` for a finitely supported function, `HahnSeries.SummableFamily.single i x` for one series at the index $i$, and `HahnSeries.SummableFamily.const` for a constant family over a finite type. The sum of `single i x` is $x$ (`HahnSeries.SummableFamily.hsum_single`). Reindexing does not change the sum: `HahnSeries.SummableFamily.Equiv` moves a family along an equivalence $\alpha \simeq \beta$, with `HahnSeries.SummableFamily.hsum_equiv`, and `HahnSeries.SummableFamily.embDomain` extends a family by zero along an embedding $\alpha \hookrightarrow \beta$, with `HahnSeries.SummableFamily.hsum_embDomain`.

#### The algebra of sums

The families form an additive group with the pointwise operations (`HahnSeries.SummableFamily.instAddCommGroup`), and the sum is additive (`HahnSeries.SummableFamily.hsum_add`, `HahnSeries.SummableFamily.hsum_sub`). Over a semiring $R$ and an ordered cancellative monoid $\Gamma$, a Hahn series $x$ acts on a family by multiplication at each index, and `HahnSeries.SummableFamily.hsum_smul` says that $\sum_i x s_i = x \sum_i s_i$. These facts together give the linear map `HahnSeries.SummableFamily.lsum` over the ring of Hahn series.

The product of two summable families $s$ over $\alpha$ and $t$ over $\beta$ is the family $(s_i t_j)$ over $\alpha \times \beta$, which is `HahnSeries.SummableFamily.mul`.

> `HahnSeries.SummableFamily.hsum_mul`: $\sum_{(i, j)} s_i t_j = (\sum_i s_i)(\sum_j t_j)$.

Proof sketch: the support of $s_i t_j$ is in $\bigcup_i \operatorname{supp}(s_i) + \bigcup_j \operatorname{supp}(t_j)$, a sum of two partially well-ordered sets. So the product family is summable. For a fixed $g$, only finitely many pairs of exponents $(a, b)$ in the two unions have $a + b = g$, and for each of them only finitely many $i$ and $j$ give nonzero coefficients. Both sides have the coefficient $\sum_{a + b = g} \sum_{i, j} (s_i)_a (t_j)_b$ at $g$. The scalar action of `HahnModule` has the same pair of results, `HahnSeries.SummableFamily.smul` and `HahnSeries.SummableFamily.smul_hsum`, and `HahnSeries.SummableFamily.smulFamily` multiplies each member by a scalar of $R$.

#### Geometric series and units

Let $\Gamma$ be linearly ordered and $R$ a commutative ring. `HahnSeries.SummableFamily.powers x` is the family $(x^n)_{n \in \mathbb{N}}$ when $\operatorname{ord}(x) > 0$ (`HahnSeries.SummableFamily.powers_of_orderTop_pos`). When $\operatorname{ord}(x) \le 0$, the definition replaces $x$ by $0$, so that the family is always summable. The summability for positive order uses `HahnSeries.SummableFamily.isPWO_iUnion_support_powers`: the union of the supports of the $x^n$ is in the additive monoid generated by $\operatorname{supp}(x)$, and that monoid is partially well-ordered when $\operatorname{supp}(x)$ is a partially well-ordered set of nonnegative elements. Each $g$ is in the support of only finitely many $x^n$ (`HahnSeries.SummableFamily.pow_finite_co_support`). For $\Gamma = \mathbb{Z}$ this is clear, since $x^n$ has the order at least $n$, but in general the proof uses the partially well-ordered property again.

> `HahnSeries.SummableFamily.one_sub_self_mul_hsum_powers`: if $\operatorname{ord}(x) > 0$, then $(1 - x) \sum_n x^n = 1$.

Proof: the left side is $\sum_n x^n - x \sum_n x^n$, and `HahnSeries.SummableFamily.hsum_smul` makes the second term the sum of the family $(x^{n + 1})_n$. Moved along $n \mapsto n + 1$ by `HahnSeries.SummableFamily.embDomain`, this family is the family of powers without its term at $0$ (`HahnSeries.SummableFamily.embDomain_succ_smul_powers`). Its sum is thus $\sum_n x^n - 1$, by `HahnSeries.SummableFamily.hsum_embDomain`, and the difference is $1$.

The geometric series gives units. If $\operatorname{ord}(x - 1) > 0$, then $x = 1 - (1 - x)$ has the inverse $\sum_n (1 - x)^n$.

> `HahnSeries.isUnit_of_orderTop_pos`: if $\operatorname{ord}(x - 1) > 0$, then $x$ is a unit.

`HahnSeries.toOrderTopSubOnePos` puts such a series in the subgroup `HahnSeries.orderTopSubOnePos` of the previous section. A general series $x \ne 0$ is $c t^a (1 + y)$, with $c$ the leading coefficient, $a$ the order and $\operatorname{ord}(y) > 0$. So $x$ is a unit when $c$ is a unit in $R$ and $a$ has an additive inverse in $\Gamma$ (`HahnSeries.isUnit_of_isUnit_leadingCoeff_AddUnitOrder`). Over an ordered group $\Gamma$ and a domain $R$, `HahnSeries.isUnit_iff` gives the converse: $x$ is a unit if and only if its leading coefficient is a unit.

Over a field $R$ and an ordered group $\Gamma$, the inverse has an explicit formula.

> `HahnSeries.inv_def`: $x^{-1} = c^{-1} t^{-a} \sum_n (1 - c^{-1} t^{-a} x)^n$, with $a$ the order and $c$ the leading coefficient of $x$.

For $x \ne 0$, the series $1 - c^{-1} t^{-a} x$ has positive order, because $c^{-1} t^{-a} x$ has the order $0$ and the leading coefficient $1$. The identity $x x^{-1} = 1$ then follows from the geometric series. This gives `HahnSeries.instField`, the field instance that the previous sections use for Laurent series over a field. The monomials behave as expected: `HahnSeries.inv_single` gives $(r t^a)^{-1} = r^{-1} t^{-a}$, and `HahnSeries.single_div_single` gives $r t^a / s t^b = (r / s) t^{a - b}$.

#### Substitution into power series

The file HEval.lean substitutes a Hahn series $x$ for the variable of a formal power series $f = \sum_n f_n X^n$. The family is `HahnSeries.SummableFamily.powerSeriesFamily x f`, which is $(f_n x^n)_n$ when $\operatorname{ord}(x) > 0$ (`HahnSeries.SummableFamily.powerSeriesFamily_of_orderTop_pos`). Otherwise the definition puts $0$ in place of $x$, and the sum is the constant coefficient $f_0$. Its sum is `PowerSeries.heval x`, an $R$-algebra homomorphism from `PowerSeries R` to `HahnSeries Γ R` (`PowerSeries.heval_apply`). The multiplicativity `PowerSeries.heval_mul` is `HahnSeries.SummableFamily.hsum_mul` together with the Cauchy product of the coefficients.

> `PowerSeries.heval_X`: if $\operatorname{ord}(x) > 0$, then the substitution sends $X$ to $x$.

Proof: the family is $f_n x^n$ with $f_1 = 1$ and $f_n = 0$ for $n \ne 1$, so the sum is $x$ by `HahnSeries.SummableFamily.hsum_single`. The other values are `PowerSeries.heval_C` for the constants, `PowerSeries.coeff_heval_zero` for the coefficient at $0$, which is the constant coefficient of $f$, and `PowerSeries.coeff_heval` for a general coefficient. `PowerSeries.heval_unit` says that a unit power series goes to a unit.

#### Binomial powers

Let $R$ be a binomial ring (`BinomialRing`), such as $\mathbb{Z}$ or a $\mathbb{Q}$-algebra, with the binomial coefficients `Ring.choose`. For a series $x$ with $\operatorname{ord}(x - 1) > 0$ and $r \in R$, `HahnSeries.SummableFamily.binomialFamily x r` is the family of the binomial expansion of $(1 + (x - 1))^r$.

> `HahnSeries.SummableFamily.binomialFamily_apply`: its $n$-th term is $\binom{r}{n} (x - 1)^n$.

The sum is again of the form $1 + (\text{higher terms})$ (`HahnSeries.SummableFamily.orderTop_hsum_binomialFamily_pos`), so it lies in the subgroup `HahnSeries.orderTopSubOnePos`. This gives the power instance `HahnSeries.instPowSubtypeUnitsMemSubgroupOrderTopSubOnePos`, and `HahnSeries.binomial_power` says that $x^r$ is this sum. The power is a homomorphism in the exponent.

> `HahnSeries.pow_add`: $x^{r + s} = x^r x^s$.

Proof sketch: the product of the two sums is a sum over pairs by `HahnSeries.SummableFamily.hsum_mul`. The coefficient of $(x - 1)^n$ in it is $\sum_{i + j = n} \binom{r}{i} \binom{s}{j}$, and the Vandermonde identity of a binomial ring makes it $\binom{r + s}{n}$. For a monomial, `HahnSeries.coeff_toOrderTopSubOnePos_pow` gives the coefficients of $(1 + c t^g)^s$ with $g > 0$: the coefficient at $k g$ is $\binom{s}{k} c^k$.

#### Common errors

1. `HahnSeries.SummableFamily.powers x` is not the family $(x^n)$ for each $x$. When $\operatorname{ord}(x) \le 0$, its terms are the powers of $0$. Each lemma that computes its terms needs the hypothesis `0 < x.orderTop`.
2. The hypothesis of `HahnSeries.isUnit_of_orderTop_pos` is on $x - 1$, not on $x$. A series of positive order such as $t$ does not satisfy it. Over an ordered group, $t$ is still a unit, with the inverse $t^{-1}$, but the proof goes through `HahnSeries.isUnit_iff` or `HahnSeries.single_mul_single`.
3. The binomial power $x^r$ is defined on the subtype `HahnSeries.orderTopSubOnePos Γ R` of the units, not on `HahnSeries Γ R`. Coerce the result twice, to the units and then to the series, to read its coefficients.

### Exercises

1. (A) Show that the family $(t^n)_{n \in \mathbb{N}}$ in `HahnSeries ℤ R` is summable, and give the coefficients of its sum.
2. (A) Use `HahnSeries.SummableFamily.one_sub_self_mul_hsum_powers` to compute the inverse of $1 - t^{1/2}$ in `HahnSeries ℚ R`.
3. (B) Show that the family $(t^{-n})_{n \in \mathbb{N}}$ in `HahnSeries ℤ R` is not summable, for a nontrivial ring $R$.
4. (B) Show that `PowerSeries.heval x` sends the power series of $1/(1 - X)$ to the sum of `HahnSeries.SummableFamily.powers x`, for $\operatorname{ord}(x) > 0$.
5. (B) For $R = \mathbb{Q}$ and $x = 1 + t$ in `HahnSeries ℤ ℚ`, compute the first four coefficients of $x^{1/2}$ and check that its square is $x$.
6. (C) Prove that a Hahn series over a domain $R$ and an ordered group $\Gamma$ is a unit if and only if its leading coefficient is a unit in $R$.

### Reference

<?reference?>
