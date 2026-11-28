---
title: Division with remainder
kind: api
modules:
  - Mathlib.Algebra.Polynomial.Div
  - Mathlib.Algebra.Polynomial.RingDivision
  - Mathlib.Algebra.Polynomial.FieldDivision
  - Mathlib.Algebra.Polynomial.PartialFractions
explains:
  E2: [Polynomial.modByMonic_add_div, Polynomial.div_modByMonic_unique, Polynomial.modByMonic_X_sub_C_eq_C_eval, Polynomial.dvd_iff_isRoot, Polynomial.modByMonic_eq_zero_iff_dvd, Polynomial.map_modByMonic, Polynomial.rootMultiplicity_mul, Polynomial.mod_def, Polynomial.irreducible_iff_degree_lt, Polynomial.div_eq_quo_add_rem_div_add_rem_div]
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

## Division with remainder

### Overview

Over any ring $R$, a polynomial $p$ can be divided by a monic polynomial $q$: there are unique $s$ and $r$ with $p = qs + r$ and $\deg r < \deg q$. Over a field the divisor only needs to be nonzero, because it can first be made monic. This makes $K[X]$ a Euclidean domain, and Chapter 5 uses this to prove that $K[X]$ is a principal ideal domain and a unique factorization domain.

The library splits the topic into four files. `Mathlib.Algebra.Polynomial.Div` divides by a monic polynomial over a ring and defines the multiplicity of a root. `Mathlib.Algebra.Polynomial.RingDivision` adds the results that need a domain. `Mathlib.Algebra.Polynomial.FieldDivision` defines `/` and `%` over a field, the Euclidean domain instance and the normalization. `Mathlib.Algebra.Polynomial.PartialFractions` writes a quotient $f/g$ as a sum of simple fractions. Section 2 gives the facts about degrees and monic polynomials that this section uses.

### The library around it

#### Division by a monic polynomial

The quotient `Polynomial.divByMonic` $p$ $q$ and the remainder `Polynomial.modByMonic` $p$ $q$ have the notations `p /ₘ q` and `p %ₘ q`. They are defined by a recursion on the degree of $p$, `Polynomial.divModByMonicAux`: while $\deg p \ge \deg q$, subtract $\operatorname{lc}(p) X^{\deg p - \deg q} q$ from $p$. The degree drops in each step because $q$ is monic, so no division in $R$ is needed. If $q$ is not monic, the definitions return junk values: the quotient is $0$ (`Polynomial.divByMonic_eq_of_not_monic`) and the remainder is $p$ (`Polynomial.modByMonic_eq_of_not_monic`).

The main identity `Polynomial.modByMonic_add_div` holds with no hypothesis: `p %ₘ q + q * (p /ₘ q) = p`. The degree bound `Polynomial.degree_modByMonic_lt` needs $q$ monic. For the natural degree, `Polynomial.natDegree_modByMonic_lt` also needs $q \ne 1$, because the natural degree of the zero remainder is $0$, not $\bot$.

The pair is unique. `Polynomial.div_modByMonic_unique` says: if $g$ is monic, $r + g s = f$ and $\deg r < \deg g$, then `f /ₘ g = s` and `f %ₘ g = r`. Proof: subtract the two identities to get $g\,(s - s') = r' - r$. If $s \ne s'$, the left side has degree at least $\deg g$, because $g$ is monic and the leading coefficient of $g\,(s - s')$ is the leading coefficient of $s - s'$. The right side has degree less than $\deg g$. So $s = s'$, and then $r = r'$.

Uniqueness gives the rest of the API. `Polynomial.modByMonic_eq_zero_iff_dvd` says that for monic $q$, the remainder is zero exactly when $q \mid p$. Proof: if $p = qt$, then $(t, 0)$ is a pair with the properties of the theorem, so the remainder is $0$. The converse is the main identity. In the same way `Polynomial.map_modByMonic` and `Polynomial.map_divByMonic` say that division commutes with a ring map $f$: the image of $q$ is monic, and the image of the pair has the properties of the theorem for the image of $p$. Other useful lemmas are `Polynomial.natDegree_divByMonic`, `Polynomial.mul_divByMonic_cancel_left` and `Polynomial.modByMonic_eq_sub_mul_div`.

#### Division by $X - a$

For $q = X - a$ the remainder is a constant, and the constant is the value at $a$. This is `Polynomial.modByMonic_X_sub_C_eq_C_eval`: `p %ₘ (X - C a) = C (eval a p)`. Proof: the remainder has degree less than $1$, so it is a constant $c$. Evaluate $p = (X - a)s + c$ at $a$ to get $p(a) = c$.

The factor theorem follows. `Polynomial.dvd_iff_isRoot` says that $X - a$ divides $p$ exactly when $p(a) = 0$. Proof: by `Polynomial.modByMonic_eq_zero_iff_dvd`, $X - a \mid p$ exactly when the remainder $C(p(a))$ is zero, and $C$ is injective. The form `Polynomial.mul_divByMonic_eq_iff_isRoot` gives the factorization $p = (X - a)(p /ₘ (X - a))$. Two related lemmas are `Polynomial.X_sub_C_dvd_sub_C_eval`, for $X - a \mid p - p(a)$, and `Polynomial.sub_dvd_eval_sub`, for $a - b \mid p(a) - p(b)$ in $R$. The case $a = 0$ is `Polynomial.X_dvd_iff`: $X \mid f$ exactly when the constant term of $f$ is zero.

#### The multiplicity of a root

The number `Polynomial.rootMultiplicity` $a$ $p$ is the largest $n$ with $(X - a)^n \mid p$, and it is $0$ for $p = 0$. The lemma `Polynomial.rootMultiplicity_eq_multiplicity` relates it to the general `multiplicity`. The two halves of the definition are `Polynomial.pow_rootMultiplicity_dvd` and `Polynomial.pow_rootMultiplicity_not_dvd`, and `Polynomial.rootMultiplicity_le_iff` combines them. The multiplicity is $0$ when $a$ is not a root (`Polynomial.rootMultiplicity_eq_zero`). For $p \ne 0$, `Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd` writes $p = (X - a)^m q$ with $X - a \nmid q$, and `Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero` says that the cofactor does not vanish at $a$.

#### Results over a domain

The file `Mathlib.Algebra.Polynomial.RingDivision` assumes that $R$ is a commutative domain. The main result is `Polynomial.rootMultiplicity_mul`: for $pq \ne 0$, the multiplicity of $a$ in $pq$ is the sum of the multiplicities in $p$ and in $q$. Proof: write $p = (X - a)^m p'$ and $q = (X - a)^n q'$ with $p'(a) \ne 0$ and $q'(a) \ne 0$. Then $pq = (X - a)^{m+n} p'q'$, and $(p'q')(a) = p'(a) q'(a) \ne 0$ because $R$ is a domain. So $X - a \nmid p'q'$ by the factor theorem. If $(X - a)^{m+n+1}$ divided $pq$, cancellation of $(X - a)^{m+n}$ in the domain $R[X]$ would give $X - a \mid p'q'$. So the multiplicity is exactly $m + n$.

Other results of the file:

| Lean name | Statement |
| --- | --- |
| `Polynomial.rootMultiplicity_X_sub_C_self` | $a$ has multiplicity $1$ in $X - a$ |
| `Polynomial.rootMultiplicity_X_sub_C_pow` | $a$ has multiplicity $n$ in $(X - a)^n$ |
| `Polynomial.prime_X_sub_C` | $X - a$ is prime |
| `Polynomial.irreducible_X_sub_C` | $X - a$ is irreducible |
| `Polynomial.Monic.prime_of_degree_eq_one` | a monic polynomial of degree $1$ is prime |
| `Polynomial.exists_multiset_roots` | a multiset of size at most $\deg p$ counts each root with its multiplicity |
| `Polynomial.degree_eq_degree_of_associated` | associated polynomials have the same degree |
| `Polynomial.mem_ker_modByMonic` | the kernel of $p \mapsto p \bmod q$ is the ideal $(q)$ |

The multiset of `Polynomial.exists_multiset_roots` is the starting point of `Polynomial.roots` in Section 6. The linear maps `Polynomial.modByMonicHom` and `Polynomial.divByMonicHom` bundle the remainder and the quotient. The lemma `Polynomial.aeval_modByMonic_eq_self_of_root` says that if $q(x) = 0$, then $p$ and its remainder modulo $q$ have the same value at $x$. This is how a computation in $R[X]/(q)$ reduces to polynomials of degree less than $\deg q$.

#### Division over a field

Over a field $K$ the library defines `Polynomial.div` and `Polynomial.mod`, with the usual notations `p / q` and `p % q`. The definitions make the divisor monic first. `Polynomial.mod_def` says `p % q = p %ₘ (q * C (q.leadingCoeff)⁻¹)`, and `Polynomial.div_def` gives the quotient with the extra factor $C(\operatorname{lc} q)^{-1}$. For a monic $q$ the two kinds of division agree: `Polynomial.modByMonic_eq_mod` and `Polynomial.divByMonic_eq_div`. The degree bound `Polynomial.degree_mod_lt` needs only $q \ne 0$, and together with the identity $q\,(p / q) + p \% q = p$ it gives the instance `Polynomial.instEuclideanDomain`. Chapter 5 uses this instance.

The degree rules are `Polynomial.degree_add_div`, `Polynomial.degree_div_lt` and `Polynomial.leadingCoeff_div`. The forms for $X - a$ are `Polynomial.mod_X_sub_C_eq_C_eval` and `Polynomial.mul_div_eq_iff_isRoot`. Division and the greatest common divisor commute with a map of fields: `Polynomial.map_div`, `Polynomial.map_mod` and `Polynomial.gcd_map`. Proof of the last: the Euclidean algorithm uses only divisions with remainder, and each step commutes with the map. So `Polynomial.isCoprime_map` says that coprimality does not depend on the field. The lemma `Polynomial.isRoot_gcd_iff_isRoot_left_right` says that the roots of $\gcd(f, g)$ are the common roots.

The units of $K[X]$ are the nonzero constants (`Polynomial.isUnit_iff_degree_eq_zero`). Each polynomial of degree $1$ is irreducible (`Polynomial.irreducible_of_degree_eq_one`), each irreducible polynomial has positive degree (`Polynomial.degree_pos_of_irreducible`), and each nonunit has a monic irreducible factor (`Polynomial.exists_monic_irreducible_factor`). The test `Polynomial.irreducible_iff_degree_lt` says that a nonzero nonunit $p$ is irreducible exactly when each divisor of degree at most $\deg p / 2$ is a unit. Proof: if $p = ab$ with nonunits $a$ and $b$, then $\deg a + \deg b = \deg p$, so one of them has degree at most $\deg p / 2$. The monic form is `Polynomial.irreducible_iff_lt_natDegree_lt`.

The instance `Polynomial.instNormalizationMonoid` normalizes a polynomial by the unit of its leading coefficient, by `Polynomial.coe_normUnit`. So `Polynomial.leadingCoeff_normalize` holds, and over a field `Polynomial.normalize_eq_self_iff_monic` says that the normalized polynomials are the monic ones. The `gcd` of Chapter 5 is monic for this reason.

The file also relates multiplicities to the derivative. `Polynomial.one_lt_rootMultiplicity_iff_isRoot` says that $a$ is a multiple root of $p \ne 0$ exactly when $p(a) = 0$ and $p'(a) = 0$. In characteristic zero, `Polynomial.rootMultiplicity_sub_one_le_derivative_rootMultiplicity` says that the derivative loses at most one from the multiplicity. Section 7 covers the derivative.

#### Partial fractions

The file `Mathlib.Algebra.Polynomial.PartialFractions` works in a field $K$ that contains $R[X]$, such as the field of fractions of a domain. For monic coprime $g_1$ and $g_2$, `Polynomial.div_eq_quo_add_rem_div_add_rem_div` gives $q$, $r_1$ and $r_2$ with $\deg r_i < \deg g_i$ and
$$\frac{f}{g_1 g_2} = q + \frac{r_1}{g_1} + \frac{r_2}{g_2}.$$
Proof: coprimality gives $c_1 g_1 + c_2 g_2 = 1$. So $f / (g_1 g_2) = f c_2 / g_1 + f c_1 / g_2$. Divide $f c_2$ by the monic $g_1$ and $f c_1$ by the monic $g_2$, and collect the two quotients in $q$. The form for a finite family of pairwise coprime monic polynomials is `Polynomial.div_prod_eq_quo_add_sum_rem_div`. The decomposition is unique: `Polynomial.quo_add_rem_div_add_rem_div_unique`. For powers of one monic polynomial the uniqueness is `Polynomial.quo_mul_pow_add_sum_rem_mul_pow_unique`, and `Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse` is the general form with powers.

#### Common errors

1. Using `p /ₘ q` with a $q$ that is not monic. The result is $0$, not an error, and the lemmas about it need the hypothesis that $q$ is monic. Over a field, use `p / q` instead.
2. Forgetting $q \ne 1$ in `Polynomial.natDegree_modByMonic_lt`. For $q = 1$ the remainder is $0$, and both natural degrees are $0$. The version with `degree` has no such hypothesis.
3. Expecting `Polynomial.rootMultiplicity_mul` without $pq \ne 0$ or over a ring with zero divisors. The multiplicity of the zero polynomial is $0$, and over $\mathbb{Z}/4$ the multiplicities do not add.

### Exercises

1. (A) Compute `(X^3 + 2 * X + 1) %ₘ (X - C 1)` over $\mathbb{Z}$ with `Polynomial.modByMonic_X_sub_C_eq_C_eval`.
2. (A) Show with `Polynomial.dvd_iff_isRoot` that $X - 1$ divides $X^n - 1$ for every $n$.
3. (B) Show that the multiplicity of $1$ as a root of $(X - 1)^2 (X + 1)$ over $\mathbb{Q}$ is $2$, with `Polynomial.rootMultiplicity_mul`.
4. (B) Use `Polynomial.irreducible_iff_degree_lt` to prove that $X^3 - 2$ is irreducible over $\mathbb{Q}$.
5. (B) Show with `Polynomial.map_modByMonic` that the remainder of $f \in \mathbb{Z}[X]$ modulo a monic $g$ reduces modulo $p$ to the remainder of the reductions.
6. (C) Find the decomposition of $1/(X^2 - 1)$ given by `Polynomial.div_eq_quo_add_rem_div_add_rem_div` with $g_1 = X - 1$ and $g_2 = X + 1$, and check that it is unique.

### Reference

<?reference?>
