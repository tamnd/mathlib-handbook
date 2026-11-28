---
title: The multivariate polynomial library
kind: api
modules:
  - Mathlib.Algebra.MvPolynomial.Basic
  - Mathlib.Algebra.MvPolynomial.Coeff
  - Mathlib.Algebra.MvPolynomial.CommRing
  - Mathlib.Algebra.MvPolynomial.Eval
  - Mathlib.Algebra.MvPolynomial.Rename
  - Mathlib.Algebra.MvPolynomial.Comap
  - Mathlib.Algebra.MvPolynomial.Counit
  - Mathlib.Algebra.MvPolynomial.Monad
  - Mathlib.Algebra.MvPolynomial.Polynomial
  - Mathlib.Algebra.MvPolynomial.Funext
  - Mathlib.Algebra.MvPolynomial.Invertible
  - Mathlib.Algebra.MvPolynomial.Cardinal
explains:
  E2: [MvPolynomial.C_dvd_iff_dvd_coeff, MvPolynomial.eval_eq, MvPolynomial.map_injective, MvPolynomial.homEquiv, MvPolynomial.killCompl_comp_rename, MvPolynomial.aeval_id_rename, MvPolynomial.vars_aeval, MvPolynomial.counit_surjective, MvPolynomial.cardinalMk_eq_max, MvPolynomial.funext_set]
  E1: auto
families: []
requires: [V06.C05, V09.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The multivariate polynomial library

### Overview

Section 1 defined the ring `MvPolynomial σ R`, proved its universal property and gave the main constructors. This section is a guide to the rest of the core files of the library: the coefficient lemmas, the evaluation maps, the change of variables, the substitution of polynomials into polynomials, and a few results on functions and cardinals.

The files follow one pattern. Each operation exists as a plain function and as a bundled homomorphism, and a lemma about the operation exists for each constructor `C`, `X`, `monomial`, `+` and `*`. The reader who knows this pattern can guess most names. Section 6 then treats degrees, variables, derivatives and division.

### The library around it

#### Coefficients and the basic lemmas

The module `Mathlib.Algebra.MvPolynomial.Basic` describes a polynomial through its coefficients. The coefficient of the monomial $m$ in $p$ is `coeff m p`, and its bundled forms are `MvPolynomial.coeffAddMonoidHom` and the linear map `MvPolynomial.lcoeff`. The lemmas on coefficients follow the constructors.

| Lean name | Statement |
|---|---|
| `MvPolynomial.coeff_C` | the coefficient of $m$ in $C(a)$ is $a$ for $m = 0$ and $0$ otherwise |
| `MvPolynomial.coeff_X_pow` | the coefficient of $m$ in $x_i^k$ is $1$ for $m = k e_i$ and $0$ otherwise |
| `MvPolynomial.coeff_C_mul` | the coefficient of $m$ in $C(a) p$ is $a$ times the coefficient in $p$ |
| `MvPolynomial.coeff_mul_X'` | the coefficient of $m$ in $p x_s$ is the coefficient of $m - e_s$ in $p$ when $m_s > 0$, else $0$ |
| `AddMonoidAlgebra.coeff_add` | coefficients are additive |
| `MvPolynomial.coeff_sum` | coefficients commute with finite sums |

Here $e_i$ is the monomial $x_i$. The support `MvPolynomial.support` has the lemmas `MvPolynomial.mem_support_iff`, `MvPolynomial.support_add`, `MvPolynomial.support_mul` and `MvPolynomial.support_X_pow`. The finite set of nonzero coefficients is `MvPolynomial.coeffs`. The monomial $C(a) \prod_i x_i^{s_i}$ is written in normal form as `monomial s a`, and `MvPolynomial.monomial_eq` and `MvPolynomial.C_mul_X_pow_eq_monomial` translate between the two forms.

Besides `MvPolynomial.induction_on`, there are three induction principles. `MvPolynomial.induction_on'` builds $p$ from monomials by sums. `MvPolynomial.monomial_add_induction_on` adds one monomial at a time, with a monomial that is not yet in the support. `MvPolynomial.induction_on_monomial` builds a monomial from constants by products with variables. The injectivity lemmas `MvPolynomial.C_injective` and `MvPolynomial.X_injective` hold over a nontrivial ring, and `MvPolynomial.isRegular_X` says that multiplication by a variable is injective over any semiring.

A constant divides a polynomial exactly when it divides each coefficient. This is `MvPolynomial.C_dvd_iff_dvd_coeff`. *Proof.* If $p = C(r) q$, then each coefficient of $p$ is $r$ times a coefficient of $q$ by `MvPolynomial.coeff_C_mul`. Conversely, if $r$ divides each coefficient $c_m$ of $p$, choose $d_m$ with $c_m = r d_m$ for $m$ in the support. Then $q = \sum_m d_m x^m$ satisfies $C(r) q = p$. $\square$

The submodule `MvPolynomial.coeffsIn σ M` is the set of polynomials with all coefficients in a submodule $M$. The lemma `MvPolynomial.mem_coeffsIn` states this, and `MvPolynomial.coeffsIn_mul` says that the product of two such submodules lies in the submodule of the product. The instances `MvPolynomial.instNoZeroDivisors` and `MvPolynomial.instIsCancelMulZeroOfIsCancelAdd` pass the absence of zero divisors and the cancellation from $R$ to the polynomial ring.

The module `Mathlib.Algebra.MvPolynomial.Coeff` computes the coefficients of a power of a sum of variables. `MvPolynomial.coeff_add_pow` is the binomial theorem in two variables: the coefficient of $x_0^a x_1^b$ in $(x_0 + x_1)^n$ is $\binom{n}{a}$ for $a + b = n$. `MvPolynomial.coeff_sum_X_pow_of_fintype` is the multinomial theorem: the coefficient of $x^d$ in $(\sum_i x_i)^n$ is the multinomial coefficient of $d$ when $|d| = n$.

The module `Mathlib.Algebra.MvPolynomial.CommRing` adds the lemmas that need negation, such as `AddMonoidAlgebra.coeff_neg`, `AddMonoidAlgebra.coeff_sub` and `MvPolynomial.eval_sub`. It also holds `MvPolynomial.homEquiv`: the ring homomorphisms $\mathbb{Z}[\sigma] \to S$ correspond to the functions $\sigma \to S$, for each commutative ring $S$. *Proof.* A ring homomorphism out of $\mathbb{Z}$ is unique, so a ring homomorphism out of $\mathbb{Z}[\sigma]$ is the same as a $\mathbb{Z}$-algebra homomorphism, and the universal property of Section 1 applies. $\square$ So $\mathbb{Z}[\sigma]$ is the free commutative ring on $\sigma$.

#### Evaluation and change of coefficients

The module `Mathlib.Algebra.MvPolynomial.Eval` holds the evaluation maps. They form a family with one base function.

| Lean name | Kind | Meaning |
|---|---|---|
| `MvPolynomial.eval₂ f g` | function | $\sum c_m x^m \mapsto \sum f(c_m) g^m$ for $f : R \to S$ and $g : \sigma \to S$ |
| `MvPolynomial.eval₂Hom f g` | ring homomorphism | the bundled form of `eval₂ f g` |
| `MvPolynomial.eval g` | ring homomorphism | evaluation at a point $g : \sigma \to R$ |
| `MvPolynomial.aeval g` | algebra homomorphism | evaluation in an $R$-algebra |
| `MvPolynomial.aevalTower` | algebra homomorphism | evaluation along an algebra map $R \to A$ over a base ring |
| `MvPolynomial.map f` | ring homomorphism | apply $f : R \to S$ to each coefficient |
| `MvPolynomial.mapAlgHom` | algebra homomorphism | `map` for an algebra homomorphism |

The simp normal form uses `aeval` and `eval`, and `MvPolynomial.aeval_def` unfolds `aeval` to `eval₂` with the algebra map. The bridge between evaluation and the change of coefficients is `MvPolynomial.eval_map`: evaluating `map f p` at $g$ is `eval₂ f g p`. The lemma `MvPolynomial.coeff_map` says that the coefficients of `map f p` are the images of the coefficients of $p$. The formula `MvPolynomial.eval_eq` writes the value as a finite sum:
$$\operatorname{eval}_x(f) = \sum_{d \in \operatorname{supp} f} c_d \prod_{i \in \operatorname{supp} d} x_i^{d_i}.$$
The image of `aeval g` is the subalgebra that the values $g(i)$ generate, by `MvPolynomial.aeval_range`.

The map of coefficients keeps injectivity and surjectivity: `MvPolynomial.map_injective` and `MvPolynomial.map_surjective`. *Proof of injectivity.* By `MvPolynomial.coeff_map`, if `map f p = map f q`, then $f(c_m(p)) = f(c_m(q))$ for each $m$. The map $f$ is injective, so $p$ and $q$ have the same coefficients. $\square$ The image of `map f` consists of the polynomials whose coefficients lie in the image of $f$ (`MvPolynomial.mem_range_map_iff_coeffs_subset`). The instance `MvPolynomial.algebraMvPolynomial` makes $S[\sigma]$ an algebra over $R[\sigma]$ for an $R$-algebra $S$.

#### Change of variables

The module `Mathlib.Algebra.MvPolynomial.Rename` treats `rename f` for $f : \sigma \to \tau$, the algebra homomorphism with $x_i \mapsto x_{f(i)}$. It is functorial: `MvPolynomial.rename_rename` says that renaming by $f$ then by $g$ is renaming by $g \circ f$. For an equivalence of types it is `MvPolynomial.renameEquiv`. Evaluation after renaming is evaluation at the composite point: `MvPolynomial.eval_rename`. For injective $f$ the coefficient of the image monomial is the old coefficient, by `MvPolynomial.coeff_rename_mapDomain`.

A polynomial involves only finitely many variables. The lemma `MvPolynomial.exists_fin_rename` says that each $p$ is `rename f q` for an injective map $f : \operatorname{Fin} n \to \sigma$ and some $q$. This reduces many questions to finitely many variables.

For injective $f$ there is a map in the other direction. `MvPolynomial.killCompl hf` sends the variables in the image of $f$ back to $\sigma$ and the other variables to $0$. Its coefficients are given by `MvPolynomial.coeff_killCompl`. The result `MvPolynomial.killCompl_comp_rename` says that it is a left inverse of `rename f`. *Proof.* Both sides are $R$-algebra homomorphisms out of $R[\sigma]$, so it suffices to compare them on the variables. The composite sends $x_i$ to `killCompl hf` of $x_{f(i)}$, which is $x_i$ since $f(i)$ is in the image. $\square$ This gives a second proof that `rename f` is injective.

The module `Mathlib.Algebra.MvPolynomial.Comap` turns an algebra homomorphism $\varphi : R[\sigma] \to R[\tau]$ into a map of points $R^\tau \to R^\sigma$. The map `MvPolynomial.comap` sends a point $x$ to the point whose $i$th coordinate is the value of $\varphi(x_i)$ at $x$ (`MvPolynomial.comap_apply`). It reverses composition (`MvPolynomial.comap_comp`), so it is a contravariant functor, the first case of the duality between polynomial maps and maps of affine spaces. An algebra isomorphism gives an equivalence of points, `MvPolynomial.comapEquiv`.

#### Substitution

The module `Mathlib.Algebra.MvPolynomial.Monad` treats the substitution of polynomials into polynomials. A substitution is a case of `aeval`: for $f : \sigma \to R[\tau]$, the map `aeval f` with values in the algebra $R[\tau]$ substitutes $f(i)$ for $x_i$. The composition law is `MvPolynomial.comp_aeval_apply`, from the module `Mathlib.Algebra.MvPolynomial.Eval`: an algebra homomorphism $\varphi$ after `aeval f` is `aeval` of the family $i \mapsto \varphi(f(i))$. So substituting $f$ and then $g$ is substituting the family $i \mapsto \operatorname{aeval}_g(f(i))$. These are the laws of a monad in the variables.

The lemma `MvPolynomial.aeval_id_rename` relates substitution and renaming. The map $f$ is also a renaming of $R[\sigma]$ into the ring of polynomials whose variables are the elements of $R[\tau]$, and `aeval id` evaluates each such variable at itself. The lemma says that `rename f` followed by `aeval id` is `aeval f`. *Proof.* Both sides are $R$-algebra homomorphisms out of $R[\sigma]$, so it suffices to check them on $x_i$. The left side sends $x_i$ to the variable $f(i)$ and then to $f(i)$. The right side sends $x_i$ to $f(i)$ by `MvPolynomial.aeval_X`. $\square$ The lemmas `MvPolynomial.rename_aeval` and `MvPolynomial.map_aeval_eq_aeval_map_map` move a renaming or a change of coefficients inside a substitution. The variables of a substitution are controlled by `MvPolynomial.vars_aeval`: the variables of `aeval f φ` lie in the union of the variables of $f(i)$ over the variables $i$ of $\varphi$. *Proof.* Write $\varphi$ as a sum of monomials. The variables of a sum lie in the union of the variables of the terms, and the variables of a product of powers of the $f(i)$ lie in the union of the variables of the $f(i)$, by `MvPolynomial.vars_add_subset` and `MvPolynomial.vars_mul`. $\square$ The Witt vectors use this calculus to compose their structure polynomials.

#### Counits, polynomials of polynomials and small facts

The module `Mathlib.Algebra.MvPolynomial.Counit` defines `MvPolynomial.counit R`, the ring homomorphism $\mathbb{Z}[R] \to R$ that sends the variable $x_r$ to $r$. Here the variables are the elements of $R$. It is surjective (`MvPolynomial.counit_surjective`). *Proof.* The element $r$ is the image of $x_r$ by `MvPolynomial.counit_X`. $\square$ So each commutative ring is a quotient of a polynomial ring over $\mathbb{Z}$. The variants `MvPolynomial.counitNat` and `MvPolynomial.ACounit` do the same over $\mathbb{N}$ and over a base ring $A$.

The module `Mathlib.Algebra.MvPolynomial.Polynomial` relates `eval₂` with values in a polynomial ring to evaluation of one variable after: `MvPolynomial.polynomial_eval_eval₂` and `MvPolynomial.eval_polynomial_eval_finSuccEquiv`. The module `Mathlib.Algebra.MvPolynomial.Invertible` holds the instance `MvPolynomial.invertibleC`: if $r$ is invertible in $R$, then $C(r)$ is invertible.

The module `Mathlib.Algebra.MvPolynomial.Funext` refines the theorem of Section 1 on polynomials and functions. `MvPolynomial.funext_set` says that over a domain two polynomials that agree on a product $\prod_i S_i$ of infinite sets are equal. *Proof sketch.* Reduce to finitely many variables by `MvPolynomial.exists_fin_rename`, and use induction on the number of variables as in Section 1. In the last variable the difference is a polynomial in one variable with infinitely many roots in $S_n$, so it is $0$. $\square$ The case $S_i = R$ is `MvPolynomial.funext`, and `MvPolynomial.funext_iff` is the form as an equivalence.

The module `Mathlib.Algebra.MvPolynomial.Cardinal` counts polynomials. `MvPolynomial.cardinalMk_le_max` says $|R[\sigma]| \le \max(|R|, |\sigma|, \aleph_0)$, and `MvPolynomial.cardinalMk_eq_max` is the equality for nonempty $\sigma$ and nontrivial $R$. *Proof sketch.* The monomials $\sigma \to_0 \mathbb{N}$ have cardinality at most $\max(|\sigma|, \aleph_0)$, and a polynomial is a finite subset of monomials with a coefficient each. For the equality, the constants give $|R| \le |R[\sigma]|$, the variables give $|\sigma| \le |R[\sigma]|$, and the powers of one variable give $\aleph_0$. $\square$

#### Common errors

1. `eval`, `aeval` and `eval₂` are three different maps, and a rewrite with a lemma about one fails on the others. Use `MvPolynomial.aeval_def` or `MvPolynomial.eval_map` to pass between them.
2. `rename f` needs no injectivity, but `killCompl` and the coefficient lemma `MvPolynomial.coeff_rename_mapDomain` do. For a noninjective $f$ several monomials have the same image, and their coefficients add.
3. In `MvPolynomial.counit R` the variables of the polynomial ring are the elements of $R$, so `MvPolynomial R ℤ` has $R$ in the first argument. Writing `MvPolynomial ℤ R` gives a different ring.

### Exercises

1. (A) Compute the coefficient of $x_0^2 x_1^3$ in $(x_0 + x_1)^5$ with `MvPolynomial.coeff_add_pow`, and the coefficient of $x_0 x_1 x_2$ in $(x_0 + x_1 + x_2)^3$.
2. (A) Show that `MvPolynomial.map f` is the identity when $f$ is the identity homomorphism, and that `map g` after `map f` is `map (g ∘ f)`.
3. (A) Let $f : \operatorname{Fin} 2 \to \operatorname{Fin} 1$ be the unique map. Compute `rename f` on $x_0^2 x_1 + x_0 x_1^2$.
4. (B) Show that $\mathbb{Z}[\sigma]$ has no zero divisors, and deduce from `MvPolynomial.homEquiv` that a ring homomorphism $\mathbb{Z}[\sigma] \to \mathbb{Z}[\tau]$ is determined by the images of the variables.
5. (B) Prove that `MvPolynomial.comap` of the identity is the identity and that `MvPolynomial.comap` sends algebra isomorphisms to bijections.
6. (C) Use `MvPolynomial.counit_surjective` to show that each commutative ring is isomorphic to a quotient of a polynomial ring over $\mathbb{Z}$, and show that a countable ring is a quotient of $\mathbb{Z}[x_1, x_2, \dots]$ with countably many variables.

### Reference

<?reference?>
