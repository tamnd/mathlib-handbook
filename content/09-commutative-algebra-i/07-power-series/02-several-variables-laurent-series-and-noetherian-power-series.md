---
title: Several variables, Laurent series and Noetherian power series
kind: theory
modules:
  - Mathlib.RingTheory.MvPowerSeries.Basic
  - Mathlib.RingTheory.MvPowerSeries.Inverse
  - Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
  - Mathlib.RingTheory.PowerSeries.Ideal
  - Mathlib.RingTheory.LaurentSeries
explains:
  E3: [MvPowerSeries, MvPowerSeries.isUnit_iff_constantCoeff, LaurentSeries, LaurentSeries.instIsFractionRingPowerSeries, PowerSeries.instIsNoetherianRing]
  E2: [MvPowerSeries.coeff, MvPowerSeries.coeff_mul, MvPowerSeries.constantCoeff, MvPowerSeries.X, MvPowerSeries.invOfUnit, MvPowerSeries.mul_invOfUnit, MvPowerSeries.instNoZeroDivisors, MvPowerSeries.instIsLocalRing, MvPowerSeries.isNoetherianRing, PowerSeries.toMvPowerSeries, MvPolynomial.coeToMvPowerSeries, LaurentSeries.of_powerSeries_localization, LaurentSeries.powerSeriesPart, LaurentSeries.single_order_mul_powerSeriesPart, HahnSeries, HahnSeries.instField, PowerSeries.instUniqueFactorizationMonoidOfIsPrincipalIdealRingOfIsDomain]
  E1: auto
families: []
requires: [V09.C02, V09.C03, V09.C06]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Several variables, Laurent series and Noetherian power series

### Overview

Section 1 studied $R[[X]]$. This section takes three further steps. First it allows several variables: a power series in $X_1, \dots, X_n$ is an infinite sum of monomials $X_1^{e_1} \cdots X_n^{e_n}$ with coefficients in $R$. The unit criterion holds again, and $R[[X_1, \dots, X_n]]$ is a domain when $R$ is one. Second it allows finitely many negative powers of $X$: a Laurent series is $X^{-m} f$ with $f \in R[[X]]$. Over a field the Laurent series form a field $k((X))$, and this field is the field of fractions of $k[[X]]$. Third it proves the analogue of the Hilbert basis theorem of Chapter 3, Section 2: if $R$ is Noetherian, then so is $R[[X]]$. The proof uses the lowest coefficient in place of the leading one.

### Definitions

**Definition (Power series in several variables).** Let $\sigma$ be a set of variables. A monomial is a product $X^e = \prod_{s \in \sigma} X_s^{e_s}$ for an exponent vector $e : \sigma \to \mathbb{N}$ with finitely many nonzero entries. A power series in the variables $\sigma$ over $R$ is a function $f$ that sends each exponent vector $e$ to a coefficient $f_e \in R$, written $f = \sum_e f_e X^e$. The sum is taken coefficientwise, and the product is
$$(fg)_e = \sum_{p + q = e} f_p\, g_q.$$
The ring is $R[[\sigma]]$, or $R[[X_1, \dots, X_n]]$ when $\sigma = \{1, \dots, n\}$. The constant coefficient is $f_0$.

For a fixed $e$ there are finitely many pairs with $p + q = e$, since $p_s \le e_s$ for all $s$. So the product is a finite sum, and the ring axioms follow as in Section 1. A polynomial is a power series through `MvPolynomial.coeToMvPowerSeries`, and `PowerSeries.toMvPowerSeries s` sends $X$ to $X_s$.

::: mathlib
`MvPowerSeries` · `Mathlib.RingTheory.MvPowerSeries.Basic`

`MvPowerSeries σ R` is defined as the function type `(σ →₀ ℕ) → R`, where `σ →₀ ℕ` is the type of finitely supported functions, the exponent vectors. The coefficient `coeff n : MvPowerSeries σ R →ₗ[R] R` and the constant coefficient `constantCoeff : MvPowerSeries σ R →+* R` are bundled maps, and `X s` is the variable indexed by `s`. The product formula is `MvPowerSeries.coeff_mul`, with the sum over `antidiagonal n`.

<?decl MvPowerSeries?>
:::

**Definition (Laurent series).** Let $R$ be a commutative ring. A Laurent series over $R$ is a family $(a_n)_{n \in \mathbb{Z}}$ of elements of $R$ for which there is $N \in \mathbb{Z}$ with $a_n = 0$ for all $n < N$. It is written $\sum_{n \ge N} a_n X^n$. The sum is coefficientwise, and the product is
$$\Big( \sum_n a_n X^n \Big) \Big( \sum_n b_n X^n \Big) = \sum_n \Big( \sum_{i + j = n} a_i b_j \Big) X^n.$$
The ring of Laurent series is $R((X))$. The order of a nonzero Laurent series is the least $n$ with $a_n \ne 0$.

If $a_i = 0$ for $i < N$ and $b_j = 0$ for $j < M$, the inner sum runs over $N \le i \le n - M$, a finite range. Each Laurent series is $X^{N} f$ for a power series $f$, so $R((X)) = \bigcup_{N \ge 0} X^{-N} R[[X]]$.

::: mathlib
`LaurentSeries` · `Mathlib.RingTheory.LaurentSeries`

`LaurentSeries R` is an abbreviation for `HahnSeries ℤ R`. A Hahn series over an ordered group $\Gamma$ is a function $\Gamma \to R$ with well-ordered support, and for $\Gamma = \mathbb{Z}$ this means a support bounded below. The inclusion of $R[[X]]$ is the ring homomorphism `HahnSeries.ofPowerSeries ℤ R`, which Mathlib uses as a coercion. Over a field, `HahnSeries.instField` makes every ring of Hahn series a field.

<?decl LaurentSeries?>
:::

### Theorems and proofs

**Theorem (Units in several variables).** A series $f \in R[[\sigma]]$ is a unit if and only if its constant coefficient $f_0$ is a unit of $R$.

*Proof.* If $fg = 1$, then $f_0 g_0 = 1$. Conversely let $f_0$ be a unit. Order the exponent vectors by $q \le e$ when $q_s \le e_s$ for all $s$. Each $e$ has only finitely many $q \le e$, so this order is well founded: there is no infinite strictly decreasing sequence, since the sum $\sum_s e_s$ drops at each strict step. Define $g$ by well-founded recursion:
$$g_0 = f_0^{-1}, \qquad g_e = -f_0^{-1} \sum_{p + q = e,\ q \ne e} f_p\, g_q \quad (e \ne 0).$$
Each $q$ in the sum satisfies $q \le e$ and $q \ne e$, so $g_e$ uses only values already defined. Then $(fg)_0 = f_0 g_0 = 1$, and for $e \ne 0$
$$(fg)_e = f_0 g_e + \sum_{p + q = e,\ q \ne e} f_p\, g_q = 0,$$
since the term with $q = e$ is the term with $p = 0$. So $fg = 1$. $\square$

::: mathlib
`MvPowerSeries.isUnit_iff_constantCoeff` · `Mathlib.RingTheory.MvPowerSeries.Inverse`

The theorem, for any ring and any type of variables. The inverse is `invOfUnit φ u` with `mul_invOfUnit`, built by the recursion of the proof. A consequence is the instance `MvPowerSeries.instIsLocalRing`: if `R` is local, so is `MvPowerSeries σ R`, since a series is a nonunit exactly when its constant coefficient lies in the maximal ideal of `R`.

<?decl MvPowerSeries.isUnit_iff_constantCoeff?>
:::

**Theorem (Power series over a domain).** Let $R$ be an integral domain and $n \ge 1$. Then $R[[X_1, \dots, X_n]]$ is an integral domain.

*Proof.* For a nonzero series $f$ let $d(f)$ be the least total degree $e_1 + \dots + e_n$ of a monomial with $f_e \ne 0$, and let $\operatorname{in}(f) = \sum_{|e| = d(f)} f_e X^e$ be its lowest homogeneous part. It is a nonzero polynomial. Let $f, g \ne 0$. A coefficient $(fg)_e$ with $|e| < d(f) + d(g)$ is a sum of terms $f_p g_q$ with $|p| + |q| = |e|$, so $|p| < d(f)$ or $|q| < d(g)$, and each term vanishes. For $|e| = d(f) + d(g)$ the only terms that can be nonzero have $|p| = d(f)$ and $|q| = d(g)$. So the homogeneous part of $fg$ of degree $d(f) + d(g)$ is the product $\operatorname{in}(f) \operatorname{in}(g)$ of two nonzero polynomials. The polynomial ring $R[X_1, \dots, X_n]$ is a domain (Chapter 6, Section 1), so this product is nonzero, and $fg \ne 0$. $\square$

::: mathlib
`MvPowerSeries.instNoZeroDivisors` · `Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors`

Mathlib proves `NoZeroDivisors (MvPowerSeries σ R)` for every type `σ` of variables, finite or not, by a lowest term for a monomial order in place of the total degree.

<?decl MvPowerSeries.instNoZeroDivisors?>
:::

**Theorem (Laurent series over a field).** Let $k$ be a field. Then $k((X))$ is a field, and it is the field of fractions of $k[[X]]$: each Laurent series is $g / X^N$ with $g \in k[[X]]$ and $N \ge 0$.

*Proof.* Let $f \in k((X))$ be nonzero, of order $m \in \mathbb{Z}$. Then $f = X^m u$ where $u = \sum_{n \ge 0} a_{n + m} X^n$ is a power series with constant coefficient $a_m \ne 0$. By the unit criterion of Section 1, $u$ has an inverse $u^{-1}$ in $k[[X]]$. Then $f \cdot X^{-m} u^{-1} = 1$, so $k((X))$ is a field.

The inclusion $k[[X]] \to k((X))$ is injective, and each $f$ is $g / X^N$ with $g \in k[[X]]$ and $N \ge 0$. So $k((X))$ is generated as a field by $k[[X]]$, and by the universal property of the field of fractions (Volume 6, Chapter 3) the induced map from the field of fractions of $k[[X]]$ to $k((X))$ is an isomorphism. $\square$

The proof shows more: for every commutative ring $R$, the ring $R((X))$ is the localization of $R[[X]]$ at the powers of $X$ (Chapter 2, Section 1), since $X$ is a unit of $R((X))$, each element is $g / X^N$, and $g / X^N = 0$ forces $g = 0$.

::: mathlib
`LaurentSeries.instIsFractionRingPowerSeries` · `Mathlib.RingTheory.LaurentSeries`

The instance `IsFractionRing K⟦X⟧ (LaurentSeries K)` for a field `K`, in the characteristic-predicate form of Volume 6, Chapter 3. The localization at the powers of $X$ for any commutative ring is the instance `LaurentSeries.of_powerSeries_localization : IsLocalization (Submonoid.powers X) (LaurentSeries R)`. The decomposition $f = X^m u$ is `single_order_mul_powerSeriesPart`, with `powerSeriesPart f` the series $u$.

<?decl LaurentSeries.instIsFractionRingPowerSeries?>
:::

**Theorem (Power series over a Noetherian ring).** Let $R$ be a Noetherian ring. Then $R[[X]]$ is Noetherian. By induction, $R[[X_1, \dots, X_n]]$ is Noetherian.

*Proof.* For $k \ge 0$ let $L_k$ be the set of $a \in R$ such that some $f \in I$ has $[X^i] f = 0$ for $i < k$ and $[X^k] f = a$. Then $L_k$ is an ideal of $R$: it contains $0$ (take $f = 0$), and if $f, f'$ witness $a, a'$, then $f - f'$ and $r f$ witness $a - a'$ and $ra$. If $f$ witnesses $a \in L_k$, then $Xf \in I$ witnesses $a \in L_{k+1}$. So $L_0 \subseteq L_1 \subseteq \cdots$. Since $R$ is Noetherian, the chain is constant from some $N$ on, and each $L_k$ is finitely generated.

For each $k \le N$ choose generators $a_{k,1}, \dots, a_{k,r_k}$ of $L_k$ and witnesses $f_{k,j} \in I$: each $f_{k,j}$ has order at least $k$ and coefficient $a_{k,j}$ at $X^k$. Let $J$ be the ideal generated by all $f_{k,j}$. Then $J \subseteq I$. Let $g \in I$. The claim is $g \in J$.

Step 1: reduction to order at least $N$. Put $g_0 = g$. Suppose $g_k \in I$ has order at least $k$, for some $k < N$. Its coefficient at $X^k$ lies in $L_k$, so it equals $\sum_j c_j a_{k,j}$ with $c_j \in R$. Put $g_{k+1} = g_k - \sum_j c_j f_{k,j}$. Then $g_{k+1} \in I$, $g_k - g_{k+1} \in J$, and $g_{k+1}$ has order at least $k + 1$. After $N$ steps, $g - g_N \in J$ and $g_N \in I$ has order at least $N$.

Step 2: the tail. Write $f_j = f_{N,j}$ and $a_j = a_{N,j}$ for $j = 1, \dots, r = r_N$. Suppose $h_m \in I$ has order at least $m$, for some $m \ge N$. Its coefficient at $X^m$ lies in $L_m = L_N$, so it equals $\sum_j c_{m,j} a_j$ with $c_{m,j} \in R$. Put $h_{m+1} = h_m - \sum_j c_{m,j} X^{m - N} f_j$. The series $X^{m - N} f_j$ has order at least $m$ and coefficient $a_j$ at $X^m$, so $h_{m+1} \in I$ has order at least $m + 1$. Start with $h_N = g_N$, and let $u_j = \sum_{m \ge N} c_{m,j} X^{m - N} \in R[[X]]$.

Fix a degree $t$. The series $X^{m-N} f_j$ has no terms below $X^m$, so for $m > t$ it does not contribute to the coefficient of $X^t$. So the coefficient of $X^t$ in $g_N - \sum_j u_j f_j$ equals the coefficient of $X^t$ in $g_N - \sum_{m = N}^{M} \sum_j c_{m,j} X^{m - N} f_j = h_{M + 1}$ for every $M \ge t$. Take $M = t$: the series $h_{t+1}$ has order at least $t + 1$, so this coefficient is $0$. This holds for every $t$, so $g_N = \sum_j u_j f_j \in J$. With Step 1, $g \in J$. So $I = J$ is finitely generated, and $R[[X]]$ is Noetherian.

For several variables, $R[[X_1, \dots, X_n]] \cong R[[X_1, \dots, X_{n-1}]][[X_n]]$, by grouping the terms by the power of $X_n$. Induction on $n$ ends the proof. $\square$

::: mathlib
`PowerSeries.instIsNoetherianRing` · `Mathlib.RingTheory.PowerSeries.Ideal`

The instance `[IsNoetherianRing R] → IsNoetherianRing R⟦X⟧`, so instance search finds it for `ℤ⟦X⟧` and `k⟦X⟧`. The several-variable form is `MvPowerSeries.isNoetherianRing`, under `[Finite σ]`. The same file has the instance `PowerSeries.instUniqueFactorizationMonoidOfIsPrincipalIdealRingOfIsDomain`: over a principal ideal domain, $R[[X]]$ is a unique factorization domain. The index of this edition has no declaration for the statement that $R[[X]]$ is a unique factorization domain for every unique factorization domain $R$, which is false in general.

<?decl PowerSeries.instIsNoetherianRing?>
:::

### Examples

**Example (An inverse in $k((X))$).** Let $f = X^2 + X^3 = X^2 (1 + X)$. The order of $f$ is $2$, and $u = 1 + X$ has the inverse $\sum_{n \ge 0} (-1)^n X^n$. So
$$f^{-1} = X^{-2} (1 - X + X^2 - X^3 + \cdots) = X^{-2} - X^{-1} + 1 - X + X^2 - \cdots.$$
The product $f \cdot f^{-1}$ telescopes to $1$: the coefficient of $X^n$ for $n \ge 1$ is $(-1)^n + (-1)^{n-1} = 0$.

**Example (Units and the maximal ideal of $k[[x, y]]$).** In $k[[x, y]]$ the series $1 + x + y^2$ is a unit, and $x + y$ is not. By the unit criterion the nonunits are the series with constant coefficient $0$. They form the ideal $\mathfrak m = (x, y)$: a series with zero constant term is $x g + y h$, with $g$ the sum of the terms that contain $x$, divided by $x$, and $h$ the sum of the remaining terms, divided by $y$. So $k[[x, y]]$ is local with maximal ideal $(x, y)$. It is Noetherian by the theorem, but it is not a principal ideal domain: a generator $d$ of $(x, y)$ would divide $x$ and $y$, and $x$ and $y$ are irreducible and not associated, since their quotient would be a unit with constant coefficient $0$.

**Example (Infinitely many variables).** Let $\sigma = \{1, 2, 3, \dots\}$ and let $\mathfrak m \subseteq k[[\sigma]]$ be the ideal of the series with constant coefficient $0$. Then $\mathfrak m$ is not finitely generated, so $k[[\sigma]]$ is not Noetherian. Proof: suppose that $\mathfrak m = (f_1, \dots, f_r)$. Each $f_i$ has a linear part $\ell_i = \sum_s (f_i)_{e_s} X_s$, where $e_s$ is the exponent vector of $X_s$. Each $X_s \in \mathfrak m$ is $\sum_i g_i f_i$, and the comparison of the terms of degree $1$ gives $X_s = \sum_i g_i(0)\, \ell_i$. So the $r$ linear parts $\ell_i$ span a $k$-vector space that contains the infinitely many independent elements $X_1, X_2, \dots$. This is impossible, so the hypothesis `[Finite σ]` of `MvPowerSeries.isNoetherianRing` is needed.

### The library around it

The multivariate files are in `Mathlib/RingTheory/MvPowerSeries/`: `Basic` for the ring, `coeff`, `X`, `C` and `constantCoeff`, `Inverse` for units and the local ring instance, `NoZeroDivisors` for the domain property, and `Equiv` for the isomorphisms between series rings and the Noetherian instance. The one-variable ring is `MvPowerSeries Unit R`, so a lemma about `MvPowerSeries` applies to `PowerSeries` after unfolding, but `PowerSeries.X` and `MvPowerSeries.X ()` are different terms, equal by a lemma, and `simp` lemmas are stated for one form. The Weierstrass preparation theorem, which writes a series over a complete local ring as a distinguished polynomial times a unit, is `PowerSeries.exists_isWeierstrassFactorization`. The Laurent series are in `Mathlib.RingTheory.LaurentSeries`, built on the Hahn series of `Mathlib/RingTheory/HahnSeries/`. The order of a Laurent series is `HahnSeries.order`.

### Exercises

1. (A) Compute the first four terms of the inverse of $1 - x - y$ in $\mathbb{Z}[[x, y]]$, and show that the coefficient of $x^i y^j$ is $\binom{i + j}{i}$.
2. (A) Find the Laurent series of $1 / (X - X^2)$ and of $1 / (2X + X^3)$ in $\mathbb{Q}((X))$, up to the term in $X^2$.
3. (A) Show that $R \cong R[[X]]/(X)$. Deduce that if $R[[X]]$ is Noetherian, then so is $R$.
4. (B) Show that the order $v(f)$ of a nonzero Laurent series over a field satisfies $v(fg) = v(f) + v(g)$ and $v(f + g) \ge \min(v(f), v(g))$, and that $k[[X]] = \{ f : f = 0 \text{ or } v(f) \ge 0 \}$.
5. (B) Show that the ideal $(x, y)$ of $k[[x, y]]$ needs two generators, and that the ideal $(x, y)^2$ needs three. Hint: compute $\mathfrak m / \mathfrak m^2$ and $\mathfrak m^2 / \mathfrak m^3$ as $k$-vector spaces and use Nakayama's lemma (Chapter 4, Section 1).
6. (B) Let $R$ be a domain and $f \in R[[X]]$ with $f(0)$ a prime element of $R$. Show that $f$ is irreducible in $R[[X]]$. Apply this to $2 + X$ in $\mathbb{Z}[[X]]$.

### Notes and history

Laurent introduced the series with negative powers in 1843 for functions with an isolated singularity. The theorem that $R[[X]]$ is Noetherian when $R$ is Noetherian is in Matsumura, *Commutative Ring Theory*, Theorem 3.3, and in Atiyah-Macdonald, *Introduction to Commutative Algebra*, Chapter 7, Exercise 4. Hahn introduced the series with well-ordered supports in 1907 in his work on non-archimedean ordered fields.

### Reference

<?reference?>
