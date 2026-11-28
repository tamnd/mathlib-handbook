---
title: Trailing degree, reverse and mirror
kind: api
modules:
  - Mathlib.Algebra.Polynomial.Degree.TrailingDegree
  - Mathlib.Algebra.Polynomial.EraseLead
  - Mathlib.Algebra.Polynomial.Reverse
  - Mathlib.Algebra.Polynomial.Mirror
  - Mathlib.Algebra.Polynomial.CancelLeads
  - Mathlib.Algebra.Polynomial.UnitTrinomial
explains:
  E2: [Polynomial.trailingDegree_eq_natTrailingDegree, Polynomial.coeff_mul_natTrailingDegree_add_natTrailingDegree, Polynomial.eraseLead_add_monomial_natDegree_leadingCoeff, Polynomial.card_support_eraseLead, Polynomial.induction_with_natDegree_le, Polynomial.coeff_reverse, Polynomial.reverse_mul_of_domain, Polynomial.eval₂_reverse_mul_pow, Polynomial.mirror_mirror, Polynomial.IsUnitTrinomial.irreducible_of_coprime]
  E1: auto
families: []
requires: [V06.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Trailing degree, reverse and mirror

### Overview

Section 2 looked at the top of a polynomial: the degree and the leading coefficient. This section looks at the bottom and at operations that move terms. The trailing degree is the smallest exponent with a nonzero coefficient. The erasure of the leading term gives an induction on the number of terms. The reverse of a polynomial reads its coefficients backward, so that the top and the bottom change places. The mirror is a reverse that keeps the trailing degree. Two small files use these tools: one cancels the leading terms of two polynomials, and one studies trinomials over $\mathbb{Z}$ whose coefficients are units.

### The library around it

#### Trailing degree and trailing coefficient

The file `Mathlib.Algebra.Polynomial.Degree.TrailingDegree` is the mirror image of the degree file. The trailing degree `Polynomial.trailingDegree` $p$ is the minimum of the support, a value in `ℕ∞`. The zero polynomial has trailing degree $\top$ (`Polynomial.trailingDegree_zero`, `Polynomial.trailingDegree_eq_top`), because the minimum of the empty set is the top element. The natural trailing degree `Polynomial.natTrailingDegree` $p$ is the same number in $\mathbb{N}$, and $0$ for $p = 0$. The lemma `Polynomial.trailingDegree_eq_natTrailingDegree` says that the two agree for $p \ne 0$. Proof: the support of a nonzero $p$ is nonempty, so its minimum is a natural number $k$, and `natTrailingDegree` reads this $k$ out of `ℕ∞`.

The trailing coefficient `Polynomial.trailingCoeff` $p$ is the coefficient at the natural trailing degree, and it is zero only for $p = 0$ (`Polynomial.trailingCoeff_eq_zero`). The predicate `Polynomial.TrailingMonic` says that it is $1$, and `Polynomial.nextCoeffUp` is the coefficient one step above. All coefficients below the trailing degree vanish (`Polynomial.coeff_eq_zero_of_lt_natTrailingDegree`), and the trailing degree is at most the degree (`Polynomial.natTrailingDegree_le_natDegree`).

The rules for products are the rules of Section 2 with the inequalities turned around. `Polynomial.le_trailingDegree_mul` says $\operatorname{tdeg} p + \operatorname{tdeg} q \le \operatorname{tdeg}(pq)$. The coefficient at the sum of the trailing degrees is the product of the trailing coefficients: this is `Polynomial.coeff_mul_natTrailingDegree_add_natTrailingDegree`. Proof: in the sum $\sum_{i + j = k + l} p_i q_j$ with $k = \operatorname{tdeg} p$ and $l = \operatorname{tdeg} q$, a pair with $i < k$ has $p_i = 0$, and a pair with $i > k$ has $j < l$ and $q_j = 0$. So only $(k, l)$ contributes. When the product $\operatorname{tc}(p) \operatorname{tc}(q)$ is not zero, `Polynomial.trailingDegree_mul'` gives equality, and over a ring without zero divisors `Polynomial.natTrailingDegree_mul` adds the natural trailing degrees of nonzero factors. Multiplying by $X^n$ adds $n$ (`Polynomial.natTrailingDegree_mul_X_pow`).

#### Erasing the leading term

The file `Mathlib.Algebra.Polynomial.EraseLead` defines `Polynomial.eraseLead` $f$, the polynomial $f$ without its top term. Its support is the support of $f$ without the natural degree (`Polynomial.eraseLead_support`), and the other coefficients do not change (`Polynomial.eraseLead_coeff_of_ne`). The basic identity is `Polynomial.eraseLead_add_monomial_natDegree_leadingCoeff`: $\operatorname{eraseLead} f + \operatorname{lc}(f) X^{\operatorname{natDeg} f} = f$. Proof: compare the coefficients at $i$. At $i = \operatorname{natDeg} f$ the left side gives $0 + \operatorname{lc}(f) = f_i$. At other $i$ it gives $f_i + 0$. Over a ring the same identity reads `Polynomial.self_sub_monomial_natDegree_leadingCoeff`.

The erasure lowers the number of terms by one, `Polynomial.card_support_eraseLead`. Proof: the support of the erasure is the support of $f$ with one element removed, and for $f \ne 0$ this element lies in the support. For $f = 0$ both sides are $0$, since the subtraction in $\mathbb{N}$ is truncated. The degree also drops: `Polynomial.degree_eraseLead_lt` for $f \ne 0$, and `Polynomial.eraseLead_natDegree_lt` when $f$ has at least two terms. The new leading coefficient is the old next coefficient when that is not zero (`Polynomial.leadingCoeff_eraseLead_eq_nextCoeff`).

These facts give an induction on the number of terms. The principle `Polynomial.induction_with_natDegree_le` proves a property of all polynomials of natural degree at most $N$ from three facts: it holds for $0$, it holds for each monomial $r X^n$ with $r \ne 0$ and $n \le N$, and it passes to $f + g$ when $\operatorname{natDeg} f < \operatorname{natDeg} g$. Proof: by induction on the number of terms, write $f = \operatorname{eraseLead} f + \operatorname{lc}(f) X^{\operatorname{natDeg} f}$ and use the third fact. The same file classifies the polynomials with few terms: `Polynomial.card_support_eq_two` and `Polynomial.card_support_eq_three` write a polynomial with two or three terms as $x X^k + y X^m$ or $x X^k + y X^m + z X^n$ with $k < m < n$ and nonzero coefficients, and `Polynomial.card_support_eq` does the same for $n$ terms.

#### Reflection and reverse

The file `Mathlib.Algebra.Polynomial.Reverse` reads coefficients backward. The map `Polynomial.revAt` $N$ is the bijection of $\mathbb{N}$ that sends $i \le N$ to $N - i$ (`Polynomial.revAt_le`) and fixes all $i > N$. It is an involution (`Polynomial.revAt_invol`). The reflection `Polynomial.reflect` $N$ $f$ moves the coefficient at $i$ to $\operatorname{revAt} N \, i$, so `Polynomial.coeff_reflect` says $(\operatorname{reflect} N f)_i = f_{\operatorname{revAt} N \, i}$. For $\operatorname{natDeg} f \le N$ this is $X^N f(1/X)$. The reflection is an involution (`Polynomial.reflect_reflect`), and `Polynomial.reflect_mul` says $\operatorname{reflect}(F + G)(fg) = \operatorname{reflect} F f \cdot \operatorname{reflect} G g$ when $\operatorname{natDeg} f \le F$ and $\operatorname{natDeg} g \le G$.

The reverse `Polynomial.reverse` $f$ is the reflection at the natural degree of $f$. So `Polynomial.coeff_reverse` says $(\operatorname{rev} f)_n = f_{\operatorname{revAt}(\operatorname{natDeg} f) \, n}$. For $f = a_0 + a_1 X + \dots + a_d X^d$ with $a_d \ne 0$ the reverse is $a_d + a_{d-1} X + \dots + a_0 X^d$. The top and the bottom change places.

| Lean name | Statement |
| --- | --- |
| `Polynomial.coeff_zero_reverse` | $(\operatorname{rev} f)_0 = \operatorname{lc}(f)$ |
| `Polynomial.reverse_leadingCoeff` | $\operatorname{lc}(\operatorname{rev} f) = \operatorname{tc}(f)$ |
| `Polynomial.reverse_trailingCoeff` | $\operatorname{tc}(\operatorname{rev} f) = \operatorname{lc}(f)$ |
| `Polynomial.reverse_natDegree` | $\operatorname{natDeg}(\operatorname{rev} f) = \operatorname{natDeg} f - \operatorname{tdeg} f$ |
| `Polynomial.natTrailingDegree_reverse` | $\operatorname{tdeg}(\operatorname{rev} f) = 0$ |
| `Polynomial.reverse_X_pow_mul` | $\operatorname{rev}(X^n f) = \operatorname{rev} f$ |

The last two rows show that the reverse forgets the trailing powers of $X$: the reverse of $X^2 + X^3$ is $1 + X$, and reversing again gives $X + 1$, not $X^2 + X^3$. The reverse is multiplicative when the product of the leading coefficients is not zero (`Polynomial.reverse_mul`), and over a ring without zero divisors always (`Polynomial.reverse_mul_of_domain`). Proof of the second: for nonzero $f$ and $g$ the degree of $fg$ is $\operatorname{natDeg} f + \operatorname{natDeg} g$, so $\operatorname{rev}(fg) = \operatorname{reflect}(\operatorname{natDeg} f + \operatorname{natDeg} g)(fg)$, which `Polynomial.reflect_mul` splits into $\operatorname{rev} f \cdot \operatorname{rev} g$. If $f$ or $g$ is zero both sides are zero. As a consequence the trailing coefficient is multiplicative over such a ring (`Polynomial.trailingCoeff_mul`).

Evaluation links the reverse to the substitution $x \mapsto 1/x$. For an invertible $x$, `Polynomial.eval₂_reverse_mul_pow` says $\operatorname{rev} f(1/x) \cdot x^{\operatorname{natDeg} f} = f(x)$, and so `Polynomial.eval₂_reverse_eq_zero_iff` says that $1/x$ is a root of the reverse exactly when $x$ is a root of $f$. Proof of the first: $\operatorname{rev} f(1/x) = \sum_i f_i x^{-(d - i)}$ with $d = \operatorname{natDeg} f$, and multiplying by $x^d$ gives $\sum_i f_i x^i$. Evaluation is the subject of Section 4.

#### Mirror

The file `Mathlib.Algebra.Polynomial.Mirror` defines `Polynomial.mirror` $p$ as $\operatorname{rev} p \cdot X^{\operatorname{tdeg} p}$. So the mirror reverses the coefficients between the trailing degree and the degree and keeps both: `Polynomial.mirror_natDegree` and `Polynomial.mirror_natTrailingDegree`. For $p = X^2 + 2X^3 + 5X^4$ the mirror is $5X^2 + 2X^3 + X^4$. Unlike the reverse, the mirror is an involution: `Polynomial.mirror_mirror` says $\operatorname{mirror}(\operatorname{mirror} p) = p$. Proof: compare coefficients. By `Polynomial.coeff_mirror`, the coefficient of the mirror at $n$ is $p_{\operatorname{revAt}(d + k) \, n}$ with $d = \operatorname{natDeg} p$ and $k = \operatorname{tdeg} p$. The mirror has the same $d$ and $k$, so applying it twice gives $p_{\operatorname{revAt}(d + k)(\operatorname{revAt}(d + k) \, n)} = p_n$ by `Polynomial.revAt_invol`.

The mirror exchanges the leading and the trailing coefficients (`Polynomial.mirror_leadingCoeff`), it does not change the value at $1$ (`Polynomial.mirror_eval_one`), and it is multiplicative over a ring without zero divisors (`Polynomial.mirror_mul_of_domain`). The coefficient of $p \cdot \operatorname{mirror} p$ at $d + k$ is the sum of the squares of the coefficients of $p$ (`Polynomial.coeff_mul_mirror`). The criterion `Polynomial.irreducible_of_mirror` proves irreducibility of $f$ from three facts: $f$ is not a unit, the only $k$ with $k \cdot \operatorname{mirror} k = f \cdot \operatorname{mirror} f$ are $\pm f$ and $\pm \operatorname{mirror} f$, and $f$ and $\operatorname{mirror} f$ have no common nonunit factor.

#### Cancelling leading terms and unit trinomials

The file `Mathlib.Algebra.Polynomial.CancelLeads` defines, over a ring, `Polynomial.cancelLeads` $p$ $q$ as $\operatorname{lc}(p) X^{\operatorname{natDeg} p - \operatorname{natDeg} q} q - \operatorname{lc}(q) X^{\operatorname{natDeg} q - \operatorname{natDeg} p} p$. The two top terms cancel, so `Polynomial.natDegree_cancelLeads_lt_of_natDegree_le_natDegree` says that the degree drops below $\operatorname{natDeg} q$ when $\operatorname{natDeg} p \le \operatorname{natDeg} q$ and $q$ is not constant. A common divisor of $p$ and $q$ divides the result (`Polynomial.dvd_cancelLeads_of_dvd_of_dvd`). This is the step of a pseudo division, which works without dividing by the leading coefficient.

The file `Mathlib.Algebra.Polynomial.UnitTrinomial` defines `Polynomial.trinomial` $k$ $m$ $n$ $u$ $v$ $w$ as $u X^k + v X^m + w X^n$ (`Polynomial.trinomial_def`). For $k < m < n$ and nonzero outer coefficients, its degree is $n$, its trailing degree is $k$ and its leading coefficient is $w$ (`Polynomial.trinomial_natDegree`, `Polynomial.trinomial_natTrailingDegree`, `Polynomial.trinomial_leadingCoeff`), and its mirror is $w X^k + v X^{n + k - m} + u X^n$ (`Polynomial.trinomial_mirror`). A polynomial over $\mathbb{Z}$ is a unit trinomial, `Polynomial.IsUnitTrinomial`, when it has three terms with coefficients $\pm 1$ (`Polynomial.isUnitTrinomial_iff`). The main result `Polynomial.IsUnitTrinomial.irreducible_of_coprime` says that a unit trinomial $p$ is irreducible when $p$ and its mirror have no common nonunit factor. Proof outline: it applies `Polynomial.irreducible_of_mirror`. A factorization $p = gh$ gives $k = g \cdot \operatorname{mirror} h$ with $k \cdot \operatorname{mirror} k = p \cdot \operatorname{mirror} p$. The coefficient of this product at $d + k$ is $3$ by `Polynomial.coeff_mul_mirror`, so $k$ has three terms with coefficients $\pm 1$, and a comparison of the remaining coefficients shows that $k$ is $\pm p$ or $\pm \operatorname{mirror} p$. The criterion is used for the irreducibility of the trinomials $X^n - X - 1$ over $\mathbb{Z}$.

#### Common errors

1. Expecting the reverse to be an involution. The reverse drops the factor $X^{\operatorname{tdeg} f}$, so $\operatorname{rev}(\operatorname{rev} f) = f$ holds only when $f_0 \ne 0$. Use `Polynomial.mirror` when an involution is needed.
2. Confusing the values at $0$. The trailing degree of $0$ is $\top$ in `ℕ∞`, while its degree is $\bot$ in `WithBot ℕ`; the natural versions are both $0$.
3. Using `Polynomial.reflect` $N$ with $N$ below the degree. For $\operatorname{natDeg} f > N$ the map `Polynomial.revAt` fixes the high exponents, so the result is not $X^N f(1/X)$.

### Exercises

1. (A) Compute the reverse and the mirror of $3X + X^4$ over $\mathbb{Z}$ with `Polynomial.coeff_reverse` and `Polynomial.coeff_mirror`.
2. (A) Show with `Polynomial.coeff_eq_zero_of_lt_natTrailingDegree` that $X^k$ divides $f$ for $k = \operatorname{tdeg} f$.
3. (B) Prove with `Polynomial.card_support_eraseLead` and `Polynomial.eraseLead_add_monomial_natDegree_leadingCoeff` that a polynomial with $n$ terms is a sum of $n$ monomials.
4. (B) Use `Polynomial.eval₂_reverse_eq_zero_iff` to show that the roots of $2X^2 - 3X + 1$ in $\mathbb{Q}$ are the inverses of the roots of $X^2 - 3X + 2$.
5. (B) Show with `Polynomial.mirror_mul_of_domain` that the mirror of a product $f \cdot \operatorname{mirror} f$ is the product itself.
6. (C) Prove that $X^2 - X - 1$ is irreducible over $\mathbb{Z}$ with `Polynomial.IsUnitTrinomial.irreducible_of_coprime`.

### Reference

<?reference?>
