---
title: Derivatives, Hasse derivatives and Taylor expansion
kind: api
modules:
  - Mathlib.Algebra.Polynomial.Derivative
  - Mathlib.Algebra.Polynomial.Derivation
  - Mathlib.Algebra.Polynomial.HasseDeriv
  - Mathlib.Algebra.Polynomial.SumIteratedDerivative
  - Mathlib.Algebra.Polynomial.Taylor
  - Mathlib.Algebra.Polynomial.Expand
explains:
  E2: [Polynomial.coeff_iterate_derivative, Polynomial.iterate_derivative_mul, Polynomial.derivation_ext, Polynomial.hasseDeriv_mul, Polynomial.factorial_smul_hasseDeriv, Polynomial.sumIDeriv_eq_self_add, Polynomial.taylor_coeff, Polynomial.sum_taylor_eq, Polynomial.expand_contract, Polynomial.map_frobenius_expand]
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

## Derivatives, Hasse derivatives and Taylor expansion

### Overview

The formal derivative of a polynomial needs no limits. It is the $R$-linear map with $X^n \mapsto n X^{n-1}$. Chapter 5, Section 3 uses it to detect multiple roots. This section is a guide to the six files that hold the derivative and the operations that come with it.

The file `Mathlib.Algebra.Polynomial.Derivative` defines the derivative and proves the rules of calculus for it. The file `Mathlib.Algebra.Polynomial.Derivation` shows that the derivative is the derivation of $R[X]$ with $X \mapsto 1$. The file `Mathlib.Algebra.Polynomial.HasseDeriv` defines the Hasse derivatives $D^{(k)}$, which act like $\frac{1}{k!} \frac{d^k}{dX^k}$ without a division by $k!$. The file `Mathlib.Algebra.Polynomial.Taylor` defines the shift $f(X) \mapsto f(X + r)$, whose coefficients are the values of the Hasse derivatives at $r$. The file `Mathlib.Algebra.Polynomial.SumIteratedDerivative` sums all the iterated derivatives. The file `Mathlib.Algebra.Polynomial.Expand` defines the substitution $f(X) \mapsto f(X^p)$ and its partial inverse, which are the tools for polynomials with zero derivative in characteristic $p$.

### The library around it

#### The derivative

The derivative `Polynomial.derivative` is a linear map `R[X] →ₗ[R] R[X]` over any semiring. So `map_add`, `map_smul` and `map_sum` apply to it, and the library has the short forms `Polynomial.derivative_add`, `Polynomial.derivative_smul` and `Polynomial.derivative_sum`. The definition is the coefficient formula `Polynomial.coeff_derivative`: the coefficient of $X^n$ in $f'$ is $(n + 1) a_{n+1}$. On the basis it gives `Polynomial.derivative_X_pow`, $(X^n)' = n X^{n-1}$, with `Polynomial.derivative_C` and `Polynomial.derivative_X` for the constants and the variable.

The rules of calculus hold in the expected form.

| Lean name | Statement |
| --- | --- |
| `Polynomial.derivative_mul` | $(fg)' = f'g + fg'$ |
| `Polynomial.derivative_pow` | $(f^n)' = n f^{n-1} f'$, over a commutative semiring |
| `Polynomial.derivative_comp` | $(f \circ g)' = g' \cdot (f' \circ g)$ |
| `Polynomial.derivative_prod` | the derivative of a product over a multiset |
| `Polynomial.derivative_map` | the derivative commutes with a map of coefficients |
| `Polynomial.derivative_eval` | $f'(x) = \sum_n a_n n x^{n-1}$ |

The proof of `Polynomial.derivative_mul` is a reduction to monomials. Both sides are additive in $f$ and in $g$, so it is enough to take $f = a X^m$ and $g = b X^n$. Then the left side is $(m + n) ab X^{m+n-1}$ and the right side is $m ab X^{m+n-1} + n ab X^{m+n-1}$, with care for the cases $m = 0$ and $n = 0$.

For the degree, `Polynomial.degree_derivative_lt` says that $\deg f' < \deg f$ for $f \ne 0$, and `Polynomial.natDegree_derivative_lt` is the version for the natural degree. The exact statements need that multiplication by a nonzero natural number is injective on $R$. The class for this is `HasUniqueDiv`, which holds for $\mathbb{Z}$, $\mathbb{Q}$ and every ring whose additive group is torsion free. Under it, `Polynomial.natDegree_derivative` gives $\deg f' = \deg f - 1$, `Polynomial.leadingCoeff_derivative` gives the leading coefficient $n a_n$, and `Polynomial.derivative_eq_zero` says that $f' = 0$ exactly when $f$ is constant. In characteristic $p$ the last statement fails: $(X^p)' = p X^{p-1} = 0$.

Two facts connect the derivative with divisibility. `Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd` says that $q^n \mid f$ implies $q^{n-1} \mid f'$. Proof: write $f = q^n g$; then $f' = n q^{n-1} q' g + q^n g'$, and both terms are multiples of $q^{n-1}$. Over a ring without zero divisors, `Polynomial.dvd_derivative_iff` says that $f \mid f'$ only when $f' = 0$, because a nonzero $f'$ has a smaller degree than $f$.

#### Iterated derivatives

The $k$th derivative is the $k$th iterate of the coerced function, in the sense of `Nat.iterate`. Its coefficients are `Polynomial.coeff_iterate_derivative`: the coefficient of $X^m$ in $f^{(k)}$ is $(m + k)^{\underline{k}} a_{m+k}$, where $n^{\underline{k}} = n (n - 1) \cdots (n - k + 1)$ is the falling factorial `Nat.descFactorial`. Proof: induction on $k$ with `Polynomial.coeff_derivative` at each step, and the identity $(m + k + 1)^{\underline{k+1}} = (m + k + 1) \cdot (m + k)^{\underline{k}}$ of falling factorials. On a power, `Polynomial.iterate_derivative_X_pow_eq_smul` gives $(X^n)^{(k)} = n^{\underline{k}} X^{n-k}$. By `Polynomial.iterate_derivative_eq_zero`, the $k$th derivative is zero for $k > \deg f$.

The Leibniz rule is `Polynomial.iterate_derivative_mul`: $(fg)^{(n)} = \sum_{k=0}^{n} \binom{n}{k} f^{(n-k)} g^{(k)}$. Proof: induction on $n$. The step differentiates each term with `Polynomial.derivative_mul`, and Pascal's rule $\binom{n}{k-1} + \binom{n}{k} = \binom{n+1}{k}$ collects the terms. The library also has `Polynomial.iterate_derivative_map` and `Polynomial.iterate_derivative_C_mul`.

#### The derivative as a derivation

The file `Mathlib.Algebra.Polynomial.Derivation` puts the derivative in the language of `Derivation`. The bundled derivative is `Polynomial.derivative'`. A derivation $D$ from $R[X]$ to an $R[X]$-module $A$ is fixed by its value at $X$: this is `Polynomial.derivation_ext`. Proof: two derivations that agree on $X$ agree on $X^n$ by the Leibniz rule and induction, they agree on constants because a derivation kills the image of $R$, and both are linear.

Conversely each $a \in A$ is the value at $X$ of a derivation: `Polynomial.mkDerivation` $R$ $a$ satisfies `Polynomial.mkDerivation_X`. So `Polynomial.mkDerivationEquiv` is a linear equivalence between $A$ and the derivations to $A$. With $A = R[X]$ and $a = 1$ it gives the ordinary derivative, by `Polynomial.mkDerivation_one_eq_derivative`. For an $R$-algebra $B$, a derivation $d$ of $B$ and $b \in B$, the composite `Derivation.compAEval` is the derivation $f \mapsto d(f(b))$ of $R[X]$, and `Derivation.compAEval_eq` computes it as $f'(b) \cdot d(b)$. This is the chain rule for derivations.

#### Hasse derivatives

The $k$th Hasse derivative `Polynomial.hasseDeriv` $k$ is the linear map with $X^n \mapsto \binom{n}{k} X^{n-k}$. The coefficient form is `Polynomial.hasseDeriv_coeff`: the coefficient of $X^n$ in $D^{(k)} f$ is $\binom{n+k}{k} a_{n+k}$. The relation with the ordinary derivative is `Polynomial.factorial_smul_hasseDeriv`: $k! \cdot D^{(k)} = \frac{d^k}{dX^k}$. Proof: compare the coefficients with `Polynomial.coeff_iterate_derivative`, and use $(n + k)^{\underline{k}} = k! \binom{n+k}{k}$.

Over $\mathbb{Q}$ the Hasse derivatives give nothing new, since $D^{(k)} = \frac{1}{k!} \frac{d^k}{dX^k}$. In characteristic $p$ they carry more information, because $\frac{d^p}{dX^p} = 0$ while $D^{(p)}(X^p) = 1$. The product rule is `Polynomial.hasseDeriv_mul`: $D^{(k)}(fg) = \sum_{i + j = k} D^{(i)} f \cdot D^{(j)} g$, with no binomial coefficients. Proof: by bilinearity it is enough to take monomials, and then the statement is the Vandermonde identity $\binom{m + n}{k} = \sum_{i + j = k} \binom{m}{i} \binom{n}{j}$. The composition rule is `Polynomial.hasseDeriv_comp`: $D^{(k)} \circ D^{(l)} = \binom{k+l}{k} D^{(k+l)}$. At the top degree, `Polynomial.hasseDeriv_natDegree_eq_C` says that $D^{(n)} f$ is the leading coefficient for $n = \deg f$, and `Polynomial.hasseDeriv_eq_zero_of_lt_natDegree` says that $D^{(k)} f = 0$ for $k > \deg f$.

#### Taylor expansion

For $r \in R$, `Polynomial.taylor` $r$ is the linear map $f \mapsto f(X + r)$, by `Polynomial.taylor_apply`. It is a ring map over a commutative semiring (`Polynomial.taylor_mul`, bundled as `Polynomial.taylorAlgHom`), it keeps the degree (`Polynomial.natDegree_taylor`) and the leading coefficient (`Polynomial.leadingCoeff_taylor`), and `Polynomial.taylor_taylor` says that shifts add. Over a commutative ring it is an algebra automorphism, `Polynomial.taylorEquiv`, with inverse the shift by $-r$ (`Polynomial.taylorEquiv_symm`).

The coefficients of the shift are the values of the Hasse derivatives: `Polynomial.taylor_coeff` says that the coefficient of $X^n$ in $f(X + r)$ is $(D^{(n)} f)(r)$. Proof: both sides are linear in $f$, so take $f = X^m$. The binomial theorem gives the coefficient $\binom{m}{n} r^{m-n}$ on the left, and the definition of $D^{(n)}$ gives the same value on the right. The first two cases are `Polynomial.taylor_coeff_zero`, the value $f(r)$, and `Polynomial.taylor_coeff_one`, the value $f'(r)$.

The Taylor formula itself is `Polynomial.sum_taylor_eq`: $f = \sum_n (D^{(n)} f)(r) \, (X - r)^n$. Proof: substitute $X - r$ for $X$ in $f(X + r) = \sum_n c_n X^n$. The left side becomes $f$, because the two shifts cancel. So the expansion of $f$ in powers of $X - r$ has the Hasse derivatives at $r$ as coefficients, in every characteristic. A first order form is `Polynomial.eval_add_of_sq_eq_zero`: if $y^2 = 0$ then $f(x + y) = f(x) + f'(x) y$. The general form with a remainder is `Polynomial.exists_mul_sq_add_linear_part_eq_eval_add`. These are the computations behind Hensel's lemma.

#### Sums of iterated derivatives

The map `Polynomial.sumIDeriv` sends $f$ to $f + f' + f'' + \cdots$, a finite sum by `Polynomial.sumIDeriv_apply`. Its key property is `Polynomial.sumIDeriv_eq_self_add`: $S(f) = f + S(f)'$. Proof: the sum $S(f')$ is $f' + f'' + \cdots$, which is $S(f) - f$, and the derivative commutes with $S$ (`Polynomial.sumIDeriv_derivative`). This identity makes $e^{-x} S(f)(x)$ an antiderivative of $-e^{-x} f(x)$, a standard step in transcendence proofs. The lemmas `Polynomial.aeval_iterate_derivative_of_lt` and `Polynomial.aeval_iterate_derivative_self` evaluate the iterated derivatives at a root of multiplicity $q$: the derivatives of order less than $q$ vanish there, and the derivative of order $q$ is $q!$ times a value. The lemma `Polynomial.exists_iterate_derivative_eq_factorial_smul` says that the $k$th derivative is $k!$ times a polynomial with integral coefficients.

#### Expansion and contraction

For $p \in \mathbb{N}$, `Polynomial.expand` $R$ $p$ is the algebra map $f(X) \mapsto f(X^p)$, by `Polynomial.expand_eq_comp_X_pow`. Its coefficients are `Polynomial.coeff_expand`: the coefficient of $X^n$ is $a_{n/p}$ when $p \mid n$, and zero otherwise. It multiplies the degree by $p$ (`Polynomial.natDegree_expand`), keeps monic polynomials monic (`Polynomial.Monic.expand`), is injective for $p > 0$ (`Polynomial.expand_injective`), and `Polynomial.expand_expand` says that expansions compose by multiplication of exponents. The derivative of an expansion is `Polynomial.derivative_expand`: $(f(X^p))' = f'(X^p) \cdot p X^{p-1}$.

The partial inverse `Polynomial.contract` $p$ keeps the coefficients at multiples of $p$ and divides the exponents by $p$ (`Polynomial.coeff_contract`). It undoes expansion: `Polynomial.contract_expand`. In the other order, `Polynomial.expand_contract` says that $f = \operatorname{expand}_p(\operatorname{contract}_p f)$ when $R$ has characteristic $p \ne 0$, $R$ has no zero divisors, and $f' = 0$. Proof: the coefficient of $X^n$ in $f'$ is $(n + 1) a_{n+1}$, and it is zero. If $p \nmid n + 1$, then $n + 1$ is not zero in $R$, because $R$ has characteristic $p$, and since $R$ has no zero divisors, $a_{n+1} = 0$. So all nonzero coefficients of $f$ sit at multiples of $p$, and contraction followed by expansion keeps them.

In characteristic $p$, expansion is related to the Frobenius map by `Polynomial.map_frobenius_expand`: applying $a \mapsto a^p$ to the coefficients of $f(X^p)$ gives $f^p$. Proof: $f^p = \sum a_n^p X^{np}$ by the binomial theorem in characteristic $p$, which is the right side. So over a perfect field each polynomial with $f' = 0$ is a $p$th power, the fact behind the theory of separable polynomials. For irreducibility, `Polynomial.of_irreducible_expand` says that $f$ is irreducible when $f(X^p)$ is. For roots, `Polynomial.rootMultiplicity_expand` says that the multiplicity of $r$ as a root of $f(X^p)$ is $p$ times the multiplicity of $r^p$ as a root of $f$, in exponential characteristic $p$.

#### Common errors

1. Expecting `Polynomial.natDegree_derivative` over every ring. It needs `HasUniqueDiv`, and over $\mathbb{Z}/p$ the derivative of $X^p$ is zero. In characteristic $p$, use the inequality `Polynomial.natDegree_derivative_le` or the Hasse derivatives.
2. Iterating the linear map `Polynomial.derivative` without the coercion to a function. The iteration `Nat.iterate` needs a function, so the lemmas state the $k$th derivative as the iterate of the coerced map, and a goal written with powers of the linear map in `Module.End` must be rewritten first.
3. Mixing the two conventions for the shift. The value of `Polynomial.taylor` $r$ at $f$ is $f(X + r)$, so the expansion around $r$ in `Polynomial.sum_taylor_eq` uses powers of $X - C\,r$.

### Exercises

1. (A) Compute $(X^3 + 2X)^{(2)}$ with `Polynomial.coeff_iterate_derivative` and check the result by hand.
2. (A) Show with `Polynomial.taylor_coeff_zero` and `Polynomial.taylor_coeff_one` that $f(X + r) \equiv f(r) + f'(r) X \pmod{X^2}$.
3. (B) Prove with `Polynomial.hasseDeriv_mul` that $D^{(1)}$ is the ordinary derivative and satisfies the Leibniz rule.
4. (B) Over $\mathbb{F}_p$, show that $D^{(p)}(X^p) = 1$ while the $p$th derivative of $X^p$ is zero.
5. (B) Use `Polynomial.expand_contract` to show that a polynomial over $\mathbb{F}_p$ with zero derivative is a polynomial in $X^p$.
6. (C) Prove `Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd` and deduce that a root of multiplicity $m$ of $f$ is a root of $f'$ for $m \ge 2$.

### Reference

<?reference?>
