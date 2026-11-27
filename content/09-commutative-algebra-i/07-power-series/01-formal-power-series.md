---
title: Formal power series
kind: theory
modules:
  - Mathlib.RingTheory.PowerSeries.Basic
  - Mathlib.RingTheory.PowerSeries.Inverse
  - Mathlib.RingTheory.PowerSeries.Order
  - Mathlib.RingTheory.PowerSeries.NoZeroDivisors
explains:
  E3: [PowerSeries, PowerSeries.isUnit_iff_constantCoeff, PowerSeries.order, PowerSeries.maximalIdeal_eq_span_X]
  E2: [PowerSeries.coeff, PowerSeries.mk, PowerSeries.X, PowerSeries.C, PowerSeries.constantCoeff, PowerSeries.coeff_mul, PowerSeries.ext, PowerSeries.X_pow_dvd_iff, PowerSeries.sub_const_eq_X_mul_shift, PowerSeries.invOfUnit, PowerSeries.mul_invOfUnit, PowerSeries.inv, PowerSeries.order_eq_nat, PowerSeries.min_order_le_order_add, PowerSeries.order_mul, PowerSeries.X_pow_order_mul_divXPowOrder, PowerSeries.instIsDomain, PowerSeries.prime_X, PowerSeries.instIsDiscreteValuationRing, Polynomial.coeToPowerSeries, PowerSeries.mk_one_mul_one_sub_eq_one]
  E1: auto
families: []
requires: [V06.C05, V06.C06, V09.C01]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Formal power series

### Overview

A polynomial over a commutative ring $R$ is a sequence of coefficients with only finitely many nonzero terms (Volume 6, Chapter 5). A formal power series drops the finiteness condition. It is an arbitrary sequence $(a_0, a_1, a_2, \dots)$ of elements of $R$, written $\sum_{n \ge 0} a_n X^n$. The sum and the product have the same formulas as for polynomials. No limit and no topology enter: the word *formal* says that the series is a sequence and not a function.

The ring $R[[X]]$ has many units: a series is invertible exactly when its constant coefficient is invertible in $R$. Over a field $k$ every nonzero series is $X^n$ times a unit, and the ideals of $k[[X]]$ are $0$ and the powers $(X^n)$. So $k[[X]]$ is a local principal ideal domain.

### Definitions

**Definition (Formal power series).** Let $R$ be a commutative ring. A formal power series over $R$ in the variable $X$ is a sequence $f = (a_0, a_1, a_2, \dots)$ of elements of $R$, written $f = \sum_{n \ge 0} a_n X^n$. The element $a_n$ is the coefficient of $X^n$ in $f$, written $[X^n] f$. The set of all formal power series is $R[[X]]$. For $f = \sum a_n X^n$ and $g = \sum b_n X^n$ put
$$f + g = \sum_{n \ge 0} (a_n + b_n) X^n, \qquad f g = \sum_{n \ge 0} \Big( \sum_{i + j = n} a_i b_j \Big) X^n.$$
The constant coefficient of $f$ is $f(0) = a_0$. The element $c \in R$ is identified with the series $(c, 0, 0, \dots)$, and $X$ is the series $(0, 1, 0, 0, \dots)$.

The inner sum in the product is finite. An evaluation such as $f(1) = a_0 + a_1 + \cdots$ has no meaning in $R$.

::: mathlib
`PowerSeries` · `Mathlib.RingTheory.PowerSeries.Basic`

`PowerSeries R` is an abbreviation for `MvPowerSeries Unit R`, the power series in a family of variables indexed by the type `Unit` with one element. The notation `R⟦X⟧` is available after `open PowerSeries`, and the ring structure needs only `[Semiring R]`.

<?decl PowerSeries?>
:::

::: mathlib
`PowerSeries.coeff` · `Mathlib.RingTheory.PowerSeries.Basic`

`coeff n : R⟦X⟧ →ₗ[R] R` is the coefficient of $X^n$, bundled as an $R$-linear map. The constructor `PowerSeries.mk : (ℕ → R) → R⟦X⟧` makes a series from its sequence of coefficients, and `coeff_mk` computes `coeff n (mk a) = a n`. Two series are equal when all coefficients agree: `PowerSeries.ext`. The constant coefficient is a ring homomorphism `constantCoeff : R⟦X⟧ →+* R`, and `C : R →+* R⟦X⟧` embeds the constants.

<?decl PowerSeries.coeff?>
:::

**Definition (Order).** The order of a nonzero series $f$ is the least $n$ with $[X^n] f \ne 0$. The order of $0$ is $\infty$. It is written $\operatorname{ord} f$.

::: mathlib
`PowerSeries.order` · `Mathlib.RingTheory.PowerSeries.Order`

`order f : ℕ∞` takes values in the natural numbers with a top element `⊤`, and `order 0 = ⊤`. The lemma `order_eq_nat` characterizes `order f = n`.

<?decl PowerSeries.order?>
:::

### Theorems and proofs

**Theorem (The ring of power series).** With the sum and the product above, $R[[X]]$ is a commutative ring. The map $R[X] \to R[[X]]$ that sends a polynomial to the series with the same coefficients is an injective ring homomorphism.

*Proof.* Commutativity, the neutral element $1$ and distributivity hold coefficient by coefficient. For associativity let $f = \sum a_n X^n$, $g = \sum b_n X^n$, $h = \sum c_n X^n$. The coefficient of $X^n$ in $(fg)h$ is
$$\sum_{m + k = n} \Big( \sum_{i + j = m} a_i b_j \Big) c_k = \sum_{i + j + k = n} a_i b_j c_k,$$
a sum over all triples of natural numbers with sum $n$. The coefficient of $X^n$ in $f(gh)$ is $\sum_{i + m = n} a_i \sum_{j + k = m} b_j c_k$, the same sum over the same triples. So $(fg)h = f(gh)$.

The formulas for polynomials are the same, so the inclusion is a ring homomorphism, and it is injective. $\square$

**Lemma (Divisibility by powers of $X$).** Let $f \in R[[X]]$ and $n \ge 0$. Then $X^n \mid f$ if and only if $[X^i] f = 0$ for all $i < n$. In particular $f = f(0) + X g$ with $g = \sum_{n \ge 0} a_{n+1} X^n$.

*Proof.* The coefficient of $X^m$ in $X^n g$ is $[X^{m - n}] g$ for $m \ge n$ and $0$ for $m < n$. So the first $n$ coefficients of a multiple of $X^n$ vanish. Conversely, if $a_i = 0$ for $i < n$, then $f = X^n \sum_{m \ge 0} a_{m + n} X^m$ by the same computation. The second statement is the case $n = 1$ applied to $f - f(0)$. $\square$

::: mathlib
`PowerSeries.X_pow_dvd_iff` · `Mathlib.RingTheory.PowerSeries.Basic`

The lemma, for a semiring. The decomposition $f = f(0) + Xg$ is `sub_const_eq_X_mul_shift`, stated as `φ - C (constantCoeff φ) = X * mk fun p ↦ coeff (p + 1) φ`.

<?decl PowerSeries.X_pow_dvd_iff?>
:::

**Theorem (Units of $R[[X]]$).** A series $f = \sum a_n X^n \in R[[X]]$ is a unit if and only if $a_0$ is a unit of $R$. The inverse $g = \sum b_n X^n$ is given by
$$b_0 = a_0^{-1}, \qquad b_n = -a_0^{-1} \sum_{i = 1}^{n} a_i b_{n - i} \quad (n \ge 1).$$

*Proof.* If $f g = 1$, then the constant coefficients give $a_0 b_0 = 1$, so $a_0$ is a unit.

Conversely let $a_0$ be a unit. Define $b_n$ by the recursion. Each $b_n$ uses only $b_0, \dots, b_{n-1}$, so the recursion defines a sequence. Put $g = \sum b_n X^n$. The constant coefficient of $fg$ is $a_0 b_0 = 1$. For $n \ge 1$ the coefficient of $X^n$ in $fg$ is
$$\sum_{i = 0}^{n} a_i b_{n - i} = a_0 b_n + \sum_{i=1}^n a_i b_{n-i} = -\sum_{i=1}^n a_i b_{n-i} + \sum_{i=1}^n a_i b_{n-i} = 0.$$
So $fg = 1$, and $g$ is the inverse of $f$ since $R[[X]]$ is commutative. $\square$

::: mathlib
`PowerSeries.isUnit_iff_constantCoeff` · `Mathlib.RingTheory.PowerSeries.Inverse`

The theorem, for any ring `R`. The explicit inverse is `invOfUnit φ u`, for a unit `u : Rˣ` with `constantCoeff φ = u`, and `mul_invOfUnit` proves `φ * invOfUnit φ u = 1`. Over a field, `PowerSeries.inv` gives `φ⁻¹`, with the junk value `0` when `constantCoeff φ = 0`.

<?decl PowerSeries.isUnit_iff_constantCoeff?>
:::

**Theorem (Rules for the order).** Let $f, g \in R[[X]]$.

1. $\operatorname{ord}(f + g) \ge \min(\operatorname{ord} f, \operatorname{ord} g)$, with equality when $\operatorname{ord} f \ne \operatorname{ord} g$.
2. $\operatorname{ord}(fg) \ge \operatorname{ord} f + \operatorname{ord} g$.
3. If $R$ is an integral domain, then $\operatorname{ord}(fg) = \operatorname{ord} f + \operatorname{ord} g$, and $R[[X]]$ is an integral domain.

*Proof.* For (1), every coefficient below $\min(\operatorname{ord} f, \operatorname{ord} g)$ is zero in $f$ and in $g$, so it is zero in $f + g$. If $m = \operatorname{ord} f < \operatorname{ord} g$, then $[X^m](f + g) = [X^m] f + 0 \ne 0$, so the order of $f + g$ is $m$.

If $f = 0$ or $g = 0$, both sides of (2) and (3) are $\infty$. Let $f, g \ne 0$, with $m = \operatorname{ord} f$ and $k = \operatorname{ord} g$. A term $a_i b_j$ with $i + j < m + k$ has $i < m$ or $j < k$, so it is zero. So the coefficients of $fg$ below $X^{m+k}$ vanish, which is (2). The coefficient of $X^{m+k}$ is $\sum_{i + j = m + k} a_i b_j$. In this sum only the term with $i = m$ and $j = k$ can be nonzero, by the same argument. So $[X^{m+k}](fg) = a_m b_k$. In a domain this is nonzero, since $a_m \ne 0$ and $b_k \ne 0$. So $\operatorname{ord}(fg) = m + k$, and in particular $fg \ne 0$. So $R[[X]]$ is a domain. $\square$

::: mathlib
`PowerSeries.order_mul` · `Mathlib.RingTheory.PowerSeries.Order`

Part 3, under `[NoZeroDivisors R]`, with the sum computed in `ℕ∞`. Part 1 is `min_order_le_order_add` and `order_add_of_order_ne`. The instance `PowerSeries.instIsDomain` gives `IsDomain R⟦X⟧` from `IsDomain R`.

<?decl PowerSeries.order_mul?>
:::

**Theorem (The ideals of $k[[X]]$).** Let $k$ be a field.

1. Every nonzero $f \in k[[X]]$ is $f = X^n u$ with $n = \operatorname{ord} f$ and $u$ a unit.
2. The ideals of $k[[X]]$ are $0$ and $(X^n)$ for $n \ge 0$. They form the chain $k[[X]] = (1) \supsetneq (X) \supsetneq (X^2) \supsetneq \cdots \supsetneq 0$.
3. $k[[X]]$ is a principal ideal domain with exactly one maximal ideal, $(X)$, and its nonzero prime ideals are the one ideal $(X)$.

*Proof.* (1) Let $n = \operatorname{ord} f$. By the lemma on divisibility $f = X^n u$, where $u = \sum_{m \ge 0} a_{m + n} X^m$. The constant coefficient of $u$ is $a_n \ne 0$, a unit of $k$. So $u$ is a unit by the unit criterion.

(2) Let $I \ne 0$ be an ideal. The set of orders of the nonzero elements of $I$ is a nonempty set of natural numbers. Let $n$ be its least element and $f \in I$ with $\operatorname{ord} f = n$. By (1), $f = X^n u$ with $u$ a unit, so $X^n = u^{-1} f \in I$ and $(X^n) \subseteq I$. Each nonzero $g \in I$ has $\operatorname{ord} g \ge n$, so $X^n \mid g$ by the lemma on divisibility, and $g \in (X^n)$. So $I = (X^n)$. The inclusions are strict: $X^n \notin (X^{n+1})$ since its coefficient of $X^n$ is $1$.

(3) Every ideal is principal by (2), and $k[[X]]$ is a domain by the rules for the order, so it is a PID. A proper ideal is $0$ or $(X^n)$ with $n \ge 1$, and all of these lie in $(X)$. So $(X)$ is the only maximal ideal. The ideal $(X^n)$ with $n \ge 2$ is not prime: $X \cdot X^{n-1} \in (X^n)$ but $X \notin (X^n)$. The ideal $(X)$ is maximal, hence prime. $\square$

So $k[[X]]$ is a local ring (Chapter 2, Section 2). It is a discrete valuation ring (Volume 10), with valuation $\operatorname{ord}$.

::: mathlib
`PowerSeries.maximalIdeal_eq_span_X` · `Mathlib.RingTheory.PowerSeries.Inverse`

The statement `IsLocalRing.maximalIdeal k⟦X⟧ = Ideal.span {X}`. The same file proves the instance `PowerSeries.instIsDiscreteValuationRing`, and with it `IsPrincipalIdealRing k⟦X⟧` by instance search, and `PowerSeries.prime_X` says that $X$ is prime over a domain. Part 1 of the theorem is `X_pow_order_mul_divXPowOrder`: `X ^ f.order.toNat * f.divXPowOrder = f`, where `divXPowOrder f` is the unit $u$.

<?decl PowerSeries.maximalIdeal_eq_span_X?>
:::

### Examples

**Example (The geometric series).** In $R[[X]]$ for any commutative ring $R$,
$$(1 - X) \sum_{n \ge 0} X^n = 1.$$
The coefficient of $X^0$ in the product is $1$. For $n \ge 1$ the coefficient of $X^n$ is $1 \cdot 1 + (-1) \cdot 1 = 0$, from the terms $1 \cdot X^n$ and $(-X) \cdot X^{n-1}$. So $1 - X$ is a unit of $R[[X]]$, but not of $R[X]$ when $R$ is a domain, since the units of $R[X]$ are then the units of $R$ (Volume 6, Chapter 5). In Mathlib the identity is `PowerSeries.mk_one_mul_one_sub_eq_one`: `mk 1 * (1 - X) = 1`.

**Example (Fibonacci numbers).** Let $f = 1 - X - X^2 \in \mathbb{Z}[[X]]$. Its constant coefficient is $1$, so $f$ is a unit. The recursion of the unit criterion, with $a_0 = 1$, $a_1 = a_2 = -1$ and $a_i = 0$ for $i \ge 3$, reads $b_0 = 1$ and
$$b_n = b_{n-1} + b_{n-2} \quad (n \ge 1),$$
with $b_{-1} = 0$. So $b_0, b_1, b_2, \dots = 1, 1, 2, 3, 5, 8, 13, \dots$ and
$$\frac{1}{1 - X - X^2} = \sum_{n \ge 0} F_{n+1} X^n,$$
where $F_0 = 0$, $F_1 = 1$ and $F_{n+1} = F_n + F_{n-1}$ are the Fibonacci numbers. Over $\mathbb{Q}(\sqrt 5)$ the factorization $1 - X - X^2 = (1 - \varphi X)(1 - \psi X)$, with $\varphi, \psi = (1 \pm \sqrt 5)/2$, partial fractions and two geometric series give the formula of Binet, $F_{n+1} = (\varphi^{n+1} - \psi^{n+1})/\sqrt 5$ (Exercise 2).

**Example (The ideals of $\mathbb{Z}[[X]]$ are not a chain).** The theorem on ideals needs a field. In $\mathbb{Z}[[X]]$ the series $2 + X$ is not a unit, since $2$ is not a unit of $\mathbb{Z}$, and $1 + 2X$ is a unit. The ideals $(2)$ and $(X)$ are both prime: $\mathbb{Z}[[X]]/(X) \cong \mathbb{Z}$ is a domain, and $\mathbb{Z}[[X]]/(2) \cong (\mathbb{Z}/2)[[X]]$ is a domain. Their sum $(2, X)$ is the maximal ideal of the series with even constant coefficient, and it is not principal. Suppose $(2, X) = (d)$. Then $2 = de$ for some $e$, and the constant coefficients give $d(0) e(0) = 2$. If $d(0) = \pm 1$, then $d$ is a unit and $(d) = (1)$, but $(2, X)$ is proper. If $d(0) = \pm 2$, then $e(0) = \pm 1$, so $e$ is a unit and $(d) = (2)$, but $X \notin (2)$. Both cases are impossible.

### The library around it

The files are in `Mathlib/RingTheory/PowerSeries/`. `Basic` defines the ring, `coeff`, `mk`, `C`, `X`, `constantCoeff`, the coercion `Polynomial.coeToPowerSeries` from `R[X]` and the map `PowerSeries.map` along a ring homomorphism. `Inverse` holds the unit criterion and the local ring `k⟦X⟧`, `Order` the order, `NoZeroDivisors` the domain property, `WellKnown` the geometric series, and `Trunc` the truncation to a polynomial. The lemma `coeff_mul` expands the coefficient of a product as a sum over `antidiagonal n`. A proof that two series are equal usually starts with `ext n`.

`PowerSeries.X` and `Polynomial.X` are different terms, related by the lemma `Polynomial.coe_X`.

### Exercises

1. (A) Compute the first five coefficients of $(1 + X + X^2)^{-1}$ in $\mathbb{Z}[[X]]$, and show that they are periodic. Hint: $(1 - X)(1 + X + X^2) = 1 - X^3$.
2. (A) Carry out the partial fraction computation that proves the formula of Binet in $\mathbb{Q}(\sqrt 5)[[X]]$.
3. (A) Show that the map $R[[X]] \to R$, $f \mapsto f(0)$ is a surjective ring homomorphism with kernel $(X)$. Deduce that $(X)$ is a prime ideal if and only if $R$ is a domain, and a maximal ideal if and only if $R$ is a field.
4. (B) Show that the maximal ideals of $R[[X]]$ are the ideals $(\mathfrak m, X) = \{ f : f(0) \in \mathfrak m \}$ for the maximal ideals $\mathfrak m$ of $R$. Deduce that $R[[X]]$ is local if and only if $R$ is local. Hint: an element outside every ideal $(\mathfrak m, X)$ is a unit by the unit criterion.
5. (B) Show that the Jacobson radical of $R[[X]]$ (Chapter 1, Section 2) contains $X$, while the Jacobson radical of $R[X]$ is equal to its nilradical for each commutative ring $R$. Hint: quote the description of the units of $R[X]$: $a_0 + a_1 X + \dots + a_n X^n$ is a unit if and only if $a_0$ is a unit and $a_1, \dots, a_n$ are nilpotent; then test $1 - fX$.
6. (B) Let $p_n$ be the number of partitions of $n$. Show that $\prod_{k = 1}^{m} (1 - X^k)^{-1}$ and $\sum_n p_n X^n$ have the same coefficients up to $X^m$. Explain why the infinite product $\prod_{k \ge 1} (1 - X^k)^{-1}$ is well defined in $\mathbb{Z}[[X]]$.

### Notes and history

Power series were the main tool of the analysis of Newton, Leibniz and Euler, and Euler used them as generating functions for partitions in the *Introductio in analysin infinitorum* (1748). A classical survey is Niven, "Formal power series", *American Mathematical Monthly* 76 (1969). The ring $k[[X]]$ is treated in Bourbaki, *Algèbre*, Chapter IV, §4.

### Reference

<?reference?>
