---
title: Hahn series
kind: api
modules:
  - Mathlib.RingTheory.HahnSeries.Basic
  - Mathlib.RingTheory.HahnSeries.Addition
  - Mathlib.RingTheory.HahnSeries.Multiplication
  - Mathlib.RingTheory.HahnSeries.Lex
  - Mathlib.RingTheory.HahnSeries.Cardinal
  - Mathlib.RingTheory.HahnSeries.PowerSeries
  - Mathlib.RingTheory.HahnSeries.Valuation
  - Mathlib.RingTheory.HahnSeries.HahnEmbedding
explains:
  E2: [HahnSeries.coeff_mul, HahnSeries.single_mul_single, HahnSeries.min_orderTop_le_orderTop_add, HahnSeries.order_mul, HahnSeries.lt_iff, HahnSeries.toPowerSeries, HahnSeries.addVal, HahnSeries.cardSupp_mul_le]
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

## Hahn series

### Overview

A Hahn series over a partially ordered set $\Gamma$ with coefficients in $R$ is a function $x : \Gamma \to R$ whose support is partially well-ordered. In a linear order, this means that each nonempty subset of the support has a least element. Formal power series are the case $\Gamma = \mathbb{N}$, and Laurent series are the case $\Gamma = \mathbb{Z}$. For $\Gamma = \mathbb{Q}$ or $\Gamma = \mathbb{R}$, the series can have exponents such as $1/2, 2/3, 3/4, \dots$ that accumulate from below, but never an infinite descending sequence of exponents. The well-ordered support is exactly the condition that makes the product of two series a finite sum in each coefficient.

The previous section uses `LaurentSeries R`, which is an abbreviation for `HahnSeries ℤ R`. This section covers the general type: its constructors, the order and the leading coefficient, the additive and the ring structure, the lexicographic order on the series, the bounds on the size of the support, the comparison with power series, the order valuation, and the Hahn embedding of an ordered abelian group. The next section treats infinite sums of Hahn series, and with them the inverses and the field structure.

### The library around it

#### The type and its constructors

The structure `HahnSeries Γ R` needs `[PartialOrder Γ] [Zero R]`. It has the field `HahnSeries.coeff : Γ → R` and a proof that the support is partially well-ordered. The library writes the type as `R⟦Γ⟧` in the source with a scoped notation. `HahnSeries.ext` reduces an equality of series to an equality of the coefficients, and `HahnSeries.support` is the set of $g$ with $x_g \ne 0$. The lemma `HahnSeries.isPWO_support` gives the partially well-ordered property, and `HahnSeries.isWF_support` gives the weaker well-founded property.

The basic series are the monomials. `HahnSeries.single a` is a `ZeroHom` from $R$ to the series, and `HahnSeries.single a r` is the series $r t^a$, with the coefficient $r$ at $a$ and $0$ elsewhere (`HahnSeries.coeff_single_same`, `HahnSeries.coeff_single_of_ne`). Other constructors give series from data with a smaller support. `HahnSeries.ofFinsupp` turns a finitely supported function into a series. `HahnSeries.ofSuppBddBelow` accepts each function whose support is bounded below, when $\Gamma$ is a locally finite order such as $\mathbb{Z}$. `HahnSeries.truncLT c x` keeps the terms of $x$ below $c$.

Two maps change the index or the coefficients. `HahnSeries.embDomain f` moves a series along an order embedding $f : \Gamma \hookrightarrow \Gamma'$, with `HahnSeries.embDomain_coeff` for the coefficients. `HahnSeries.map` applies a zero-preserving map to each coefficient. Iterated series have a normal form: `HahnSeries.iterateEquiv` is the equivalence of `HahnSeries Γ (HahnSeries Γ' R)` with the series over the lexicographic product `Lex (Γ × Γ')`, with the two directions `HahnSeries.toIterate` and `HahnSeries.ofIterate`.

#### Order and leading coefficient

There are two order functions. `HahnSeries.orderTop x` is in `WithTop Γ`. It is the least element of the support of $x$, and it is $\top$ for $x = 0$ (`HahnSeries.orderTop_zero`, `HahnSeries.orderTop_eq_top`). `HahnSeries.order x` is in $\Gamma$ and needs `[Zero Γ]`. It agrees with `HahnSeries.orderTop` for $x \ne 0$ (`HahnSeries.order_eq_orderTop_of_ne_zero`) and takes the value $0$ for $x = 0$. Use `HahnSeries.orderTop` in statements that must hold for all $x$, and use `HahnSeries.order` when $x \ne 0$ is a hypothesis anyway. `HahnSeries.leadingCoeff x` is the coefficient of $x$ at its order, and it is $0$ for $x = 0$ (`HahnSeries.leadingCoeff_eq_zero`).

#### The additive structure

The file Addition.lean gives the instances `AddCommMonoid`, `AddCommGroup` and `Module`, all coefficientwise. The order of a sum satisfies the ultrametric inequality.

> `HahnSeries.min_orderTop_le_orderTop_add`: $\min(\operatorname{ord}(x), \operatorname{ord}(y)) \le \operatorname{ord}(x + y)$ in `WithTop Γ`.

Proof sketch: $\Gamma$ is linearly ordered here. If $g < \min(\operatorname{ord}(x), \operatorname{ord}(y))$, then $x_g = 0$ and $y_g = 0$, so $(x + y)_g = 0$. The support of $x + y$ thus has no element below the minimum. The strict case is `HahnSeries.orderTop_add_eq_left`: if $\operatorname{ord}(x) < \operatorname{ord}(y)$, then $\operatorname{ord}(x + y) = \operatorname{ord}(x)$, because the coefficient at $\operatorname{ord}(x)$ does not cancel.

The linear maps of this module have the suffix linearMap or LinearMap: `HahnSeries.coeff.linearMap` takes one coefficient, `HahnSeries.single.linearMap` makes a monomial, `HahnSeries.embDomainLinearMap` moves the index, and `HahnSeries.truncLTLinearMap` truncates.

#### Multiplication

Let $\Gamma$ be an ordered cancellative additive monoid. For $g \in \Gamma$, the set of pairs $(a, b)$ in $\operatorname{supp}(x) \times \operatorname{supp}(y)$ with $a + b = g$ is finite. The reason is that the two supports are partially well-ordered, and the library packs this set as a `Finset`. The product is then the Cauchy product.

> `HahnSeries.coeff_mul`: $(xy)_g = \sum_{a + b = g} x_a y_b$, where the sum runs over the finite set of such pairs in the supports.

The support of $xy$ is in $\operatorname{supp}(x) + \operatorname{supp}(y)$, and this sum of two partially well-ordered sets is again partially well-ordered. That is the reason why the product is a Hahn series. For monomials, the formula has one term.

> `HahnSeries.single_mul_single`: $(r t^a)(s t^b) = (rs) t^{a + b}$.

Proof: the only pair in the supports is $(a, b)$, so the product has the coefficient $rs$ at $a + b$ and $0$ elsewhere. The constant series form the ring homomorphism `HahnSeries.C : R →+* HahnSeries Γ R`, with `HahnSeries.C_apply` saying that $C(r)$ is `single 0 r`. The instances are `HahnSeries.instCommRing` and `HahnSeries.instAlgebra`. `HahnSeries.embDomainRingHom` and `HahnSeries.embDomainAlgHom` make `HahnSeries.embDomain` a ring map for an injective additive map $\Gamma \to \Gamma'$ that reflects the order.

Over a linear order, the leading terms multiply. The coefficient of $xy$ at $\operatorname{ord}(x) + \operatorname{ord}(y)$ is $x_{\operatorname{ord}(x)} y_{\operatorname{ord}(y)}$ (`HahnSeries.coeff_mul_order_add_order`), because the only pair of the supports that sums to this exponent is the pair of the two orders. If $R$ has no zero divisors, this coefficient is not zero, and the order is additive.

> `HahnSeries.order_mul`: if $x \ne 0$ and $y \ne 0$, then $\operatorname{ord}(xy) = \operatorname{ord}(x) + \operatorname{ord}(y)$.

The forms for the top order and for the leading coefficient are `HahnSeries.orderTop_mul` and `HahnSeries.leadingCoeff_mul`. The form for powers is `HahnSeries.order_pow`, with $\operatorname{ord}(x^n) = n \cdot \operatorname{ord}(x)$. The instances `HahnSeries.instNoZeroDivisors` and `HahnSeries.instIsDomainOfIsCancelAdd` follow: Hahn series over a domain form a domain. The subgroup `HahnSeries.orderTopSubOnePos` of the units holds the series $x$ with $\operatorname{ord}(x - 1) > 0$, that is, the series of the form $1 + (\text{higher terms})$. The next section raises these units to powers.

The type `HahnModule Γ R V` is a copy of `HahnSeries Γ V` with a scalar action of Hahn series over $R$. The map `HahnModule.of` identifies the two types, and `HahnModule.coeff_smul` gives the same Cauchy formula, with `Finset.VAddAntidiagonal` in place of the antidiagonal.

#### The lexicographic order

Over a linear order $\Gamma$ and a linearly ordered coefficient type $R$ with a zero, the type `Lex (HahnSeries Γ R)` has the linear order `HahnSeries.instLinearOrderLex`.

> `HahnSeries.lt_iff`: $x < y$ if and only if there is $g$ with $x_h = y_h$ for each $h < g$ and $x_g < y_g$.

The well-ordered support is what makes this a total order: the support of $x - y$ has a least element, and that element decides. In other words, $x < y$ when the leading coefficient of $y - x$ is positive, and `HahnSeries.leadingCoeff_pos_iff` states the case $x = 0$. The instance `HahnSeries.instIsStrictOrderedRingLex` makes the series a strictly ordered ring. In this order, $t^a$ is infinitely small compared to $t^b$ for $a > b$. `HahnSeries.archimedeanClassOrderIsoWithTop` identifies the Archimedean classes of the series with `WithTop Γ` when $R$ is Archimedean, and `HahnSeries.finiteArchimedeanClassOrderIso` does the same for the nonzero classes. `HahnSeries.embDomainOrderEmbedding` is the order embedding that `HahnSeries.embDomain` gives.

#### The Hahn embedding

The file HahnEmbedding.lean gives the Hahn embedding theorem for groups. `hahnEmbedding_isOrderedAddMonoid` states that each linearly ordered abelian group $M$ has an injective ordered group map $f$ into `Lex (HahnSeries (FiniteArchimedeanClass M) ℝ)` such that the Archimedean class of $a$ corresponds to the `HahnSeries.orderTop` of $f(a)$. The variant `hahnEmbedding_isOrderedModule_rat` gives the form for ordered $\mathbb{Q}$-modules. The general module form and its proof are in the section on Archimedean modules in V07.

#### Size of the support

The file Cardinal.lean measures the support with `HahnSeries.cardSupp`, the cardinal of `HahnSeries.support`.

> `HahnSeries.cardSupp_mul_le`: $|\operatorname{supp}(xy)| \le |\operatorname{supp}(x)| \cdot |\operatorname{supp}(y)|$.

Proof: by `HahnSeries.coeff_mul`, the support of $xy$ is in the image of $\operatorname{supp}(x) \times \operatorname{supp}(y)$ under addition. For the inverse, `HahnSeries.cardSupp_inv_le` gives the bound $\max(\aleph_0, |\operatorname{supp}(x)|)$, since the inverse is a sum of countably many powers. For an infinite cardinal $\kappa$, the series with fewer than $\kappa$ terms thus form the subring `HahnSeries.cardSuppLTSubring`, and for $\kappa > \aleph_0$ the subfield `HahnSeries.cardSuppLTSubfield`.

#### Power series and the valuation

For $\Gamma = \mathbb{N}$, the well-ordered condition is empty, and `HahnSeries.toPowerSeries` is a ring isomorphism of `HahnSeries ℕ R` with `PowerSeries R`. Its proof is a match of the two Cauchy products: in $\mathbb{N}$, the pairs with $a + b = n$ are the antidiagonal. `HahnSeries.toPowerSeriesAlg` is the algebra form. For a finite type $\sigma$, `HahnSeries.toMvPowerSeries` identifies the series over `σ →₀ ℕ` with `MvPowerSeries σ R`. For an ordered semiring $\Gamma$, the composite of the inverse with `HahnSeries.embDomain` along $\mathbb{N} \to \Gamma$ is the ring homomorphism `HahnSeries.ofPowerSeries Γ R`, which sends $X$ to $t^1$ (`HahnSeries.ofPowerSeries_X`). `Polynomial.algebraMap_hahnSeries_injective` says that polynomials embed.

Over a domain $R$, `HahnSeries.addVal Γ R` is an additive valuation with values in `WithTop Γ`, and `HahnSeries.addVal_apply` says that it is `HahnSeries.orderTop`. The three axioms of an additive valuation are the facts of the earlier parts: $\operatorname{ord}(0) = \top$, the additivity `HahnSeries.orderTop_mul`, and the ultrametric inequality `HahnSeries.min_orderTop_le_orderTop_add`.

#### Common errors

1. The lemmas for `HahnSeries.order` need $x \ne 0$, because `HahnSeries.order 0` is $0$ and not $\top$. When a statement must hold for each $x$, use `HahnSeries.orderTop`: for example, `HahnSeries.orderTop_mul` needs no nonzero hypothesis.
2. The order on `HahnSeries Γ R` itself is not the lexicographic order. The lexicographic order and the ordered ring instances are on `Lex (HahnSeries Γ R)`, so move with `toLex` and `ofLex`.
3. Multiplication needs an ordered cancellative monoid $\Gamma$, and the lemmas on `HahnSeries.order` and `HahnSeries.leadingCoeff` need a linear order. Over a partial order such as `σ →₀ ℕ`, the product exists, but a series has no single leading term.

### Exercises

1. (A) Use `HahnSeries.single_mul_single` to show that `single a 1` is a unit in `HahnSeries ℤ R` for each $a \in \mathbb{Z}$.
2. (A) Show that $\operatorname{ord}(x^n) = n \operatorname{ord}(x)$ for a nonzero Hahn series $x$ over a domain, by induction with `HahnSeries.order_mul`.
3. (B) Over $\Gamma = \mathbb{Q}$, show that the function with the coefficient $1$ at each $1 - 1/n$ for $n \ge 1$ is a Hahn series, and that the function with the coefficient $1$ at each $-n$ is not.
4. (B) Show that if $\operatorname{ord}(x) < \operatorname{ord}(y)$, then the leading coefficient of $x + y$ is the leading coefficient of $x$.
5. (B) In `Lex (HahnSeries ℤ ℝ)`, show that $0 < t^1 < 1/n$ for each $n \ge 1$, so the ordered field is not Archimedean.
6. (C) Prove that the support of $xy$ is partially well-ordered, from the fact that the sum of two partially well-ordered subsets of an ordered cancellative monoid is partially well-ordered.

### Reference

<?reference?>
