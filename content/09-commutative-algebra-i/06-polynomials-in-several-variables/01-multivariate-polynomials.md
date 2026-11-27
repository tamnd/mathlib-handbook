---
title: Multivariate polynomials
kind: theory
modules: []
explains:
  E3: [MvPolynomial, MvPolynomial.aeval, MvPolynomial.finSuccEquiv, MvPolynomial.funext]
  E2: [MvPolynomial.X, MvPolynomial.C, MvPolynomial.monomial, MvPolynomial.support, MvPolynomial.coeff_mul, MvPolynomial.monomial_mul_monomial, MvPolynomial.as_sum, MvPolynomial.ext, MvPolynomial.induction_on, MvPolynomial.totalDegree, MvPolynomial.totalDegree_mul, MvPolynomial.totalDegree_mul_of_isDomain, MvPolynomial.degreeOf, MvPolynomial.eval₂Hom, MvPolynomial.eval, MvPolynomial.aeval_X, MvPolynomial.aeval_unique, MvPolynomial.algHom_ext, MvPolynomial.rename, MvPolynomial.rename_injective, MvPolynomial.exists_finset_rename, MvPolynomial.optionEquivLeft, MvPolynomial.IsHomogeneous, MvPolynomial.homogeneousComponent, MvPolynomial.sum_homogeneousComponent, MvPolynomial.instIsDomainOfIsCancelAdd]
  E1: [MvPolynomial.eval₂, MvPolynomial.vars, MvPolynomial.degrees, MvPolynomial.totalDegree_add, MvPolynomial.totalDegree_X, MvPolynomial.IsHomogeneous.mul, MvPolynomial.homogeneousComponent_isHomogeneous, MvPolynomial.instNoZeroDivisors, MvPolynomial.sumAlgEquiv, MvPolynomial.constantCoeff, MvPolynomial.IsSymmetric, MvPolynomial.esymm, MvPolynomial.esymmAlgEquiv, MvPolynomial.IsWeightedHomogeneous, AddMonoidAlgebra, Finsupp]
families: []
requires: [V06.C05, V09.C03, V09.C05]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Multivariate polynomials

### Overview

Many texts define $R[x, y]$ as $R[x][y]$. Mathlib takes a direct route: a monomial gives each variable an exponent, and a polynomial is a finite linear combination of monomials, for any set $\sigma$ of variables. For finitely many variables the two constructions agree, and the isomorphism moves the results of Chapter 5 to several variables.

This section sets up the ring, its universal property and its degrees, and proves that it is a domain when $R$ is one and that over an infinite domain a polynomial is determined by its values.

### Definitions

Let $R$ be a commutative ring and $\sigma$ a set, the set of variables.

**Definition (Monomial).** A monomial in the variables $\sigma$ is a function $a \colon \sigma \to \mathbb{N}$ with $a(i) = 0$ for all but finitely many $i$. It is written $x^a = \prod_i x_i^{a(i)}$. Monomials are added pointwise, and $x^a x^b = x^{a+b}$. The degree of $x^a$ is $|a| = \sum_i a(i)$.

**Definition (Polynomial ring).** A polynomial over $R$ in the variables $\sigma$ is a function $f$ from monomials to $R$ with finite support. It is written $f = \sum_a c_a x^a$, with $c_a = f(a)$ the coefficient of $x^a$. The sum is pointwise and the product is
$$\Bigl( \sum_a c_a x^a \Bigr) \Bigl( \sum_b d_b x^b \Bigr) = \sum_e \Bigl( \sum_{a + b = e} c_a d_b \Bigr) x^e.$$
The ring of these polynomials is $R[\sigma]$, or $R[x_1, \dots, x_n]$ for $\sigma = \{1, \dots, n\}$. The variable $x_i$ is the monomial with $a(i) = 1$ and $a(j) = 0$ for $j \ne i$.

The inner sum is finite, since $e$ has finitely many decompositions $e = a + b$, and the ring axioms follow as for the group algebra of a commutative monoid.

**Definition (Degrees).** Let $f = \sum c_a x^a \ne 0$. The total degree of $f$ is the largest $|a|$ with $c_a \ne 0$. The degree of $f$ in $x_i$ is the largest $a(i)$ with $c_a \ne 0$. A polynomial is homogeneous of degree $d$ if all its monomials with nonzero coefficient have degree $d$. The homogeneous component $f_d$ is the sum of the terms of $f$ of degree $d$, so $f = \sum_d f_d$.

::: mathlib
`MvPolynomial` · `Mathlib.Algebra.MvPolynomial.Basic`

`MvPolynomial σ R` is `AddMonoidAlgebra R (σ →₀ ℕ)`: finitely supported functions from monomials `σ →₀ ℕ` to `R`, with the product of the definition. The monomials use `Finsupp` from Volume 3. The constructors are `X i`, `C r` and `monomial s r`. The coefficient is `coeff s f`, and `coeff_mul` and `monomial_mul_monomial` give the product. `support f` is the set of monomials with nonzero coefficient, `as_sum` writes `f` as the sum of its terms, `ext` compares coefficients, and `induction_on` builds a polynomial from constants by sums and products with variables.

<?decl MvPolynomial?>
:::

::: mathlib
`MvPolynomial.totalDegree` · `Mathlib.Algebra.MvPolynomial.Degrees`

`f.totalDegree : ℕ` has the junk value `0` at `f = 0`, and `degreeOf i f` is the degree in `X i`. `totalDegree_mul` is only the inequality `≤`, valid over any semiring, and `totalDegree_mul_of_isDomain` is the equality for nonzero factors. `IsHomogeneous f d` and `homogeneousComponent d f` are in `Mathlib.RingTheory.MvPolynomial.Homogeneous`, and `sum_homogeneousComponent` is $f = \sum_d f_d$.

<?decl MvPolynomial.totalDegree?>
:::

### Theorems and proofs

**Theorem (Universal property).** Let $S$ be a commutative $R$-algebra and $s \colon \sigma \to S$ a function. There is exactly one $R$-algebra homomorphism $\varphi \colon R[\sigma] \to S$ with $\varphi(x_i) = s_i$ for all $i$. It is $\varphi(\sum c_a x^a) = \sum c_a s^a$ with $s^a = \prod_i s_i^{a(i)}$.

*Proof.* The product $s^a$ is finite, since $a$ has finite support, and $s^{a + b} = s^a s^b$, since $S$ is commutative. The formula defines an $R$-linear map. For monomials, $\varphi(x^a x^b) = \varphi(x^{a+b}) = s^{a+b} = s^a s^b = \varphi(x^a) \varphi(x^b)$, and both sides of $\varphi(fg) = \varphi(f) \varphi(g)$ are $R$-bilinear in $(f, g)$, so $\varphi$ is multiplicative. Also $\varphi(1) = s^0 = 1$. For the uniqueness, an $R$-algebra homomorphism $\psi$ with $\psi(x_i) = s_i$ satisfies $\psi(x^a) = \prod_i \psi(x_i)^{a(i)} = s^a$, and it is $R$-linear, so $\psi = \varphi$. $\square$

The value $\varphi(f)$ is written $f(s)$. For $S = R$ this is the evaluation of $f$ at a point $s \in R^\sigma$.

**Theorem (One variable at a time).** For each $n \ge 0$ there is an $R$-algebra isomorphism
$$R[x_1, \dots, x_{n+1}] \cong R[x_1, \dots, x_n][T]$$
that sends $x_i$ to $x_i$ for $i \le n$ and $x_{n+1}$ to $T$.

*Proof.* Put $A = R[x_1, \dots, x_n]$. The universal property gives an $R$-algebra homomorphism $\Phi \colon R[x_1, \dots, x_{n+1}] \to A[T]$ with $x_i \mapsto x_i$ for $i \le n$ and $x_{n+1} \mapsto T$. In the other direction, the universal property of $A$ gives the inclusion $j \colon A \to R[x_1, \dots, x_{n+1}]$ with $x_i \mapsto x_i$, and the universal property of $A[T]$ (Volume 6, Chapter 5) extends $j$ to $\Psi \colon A[T] \to R[x_1, \dots, x_{n+1}]$ with $T \mapsto x_{n+1}$. The composite $\Psi \circ \Phi$ fixes each $x_i$, so it is the identity by the uniqueness part of the universal property. The composite $\Phi \circ \Psi$ fixes $A$ and $T$, so it is the identity on $A[T]$. $\square$

**Corollary (Domain).** If $R$ is a domain, then $R[\sigma]$ is a domain for every set $\sigma$. If $R$ is a unique factorization domain, then so is $R[x_1, \dots, x_n]$.

*Proof.* For $\sigma = \{1, \dots, n\}$ use induction on $n$ and the theorem: $A[T]$ is a domain when $A$ is one, by the formula for the degree of a product. For the second claim use Chapter 5, Section 1 in the same induction. For an arbitrary $\sigma$, let $fg = 0$. The polynomials $f$ and $g$ involve only finitely many variables, so they lie in the image of $R[\tau] \to R[\sigma]$ for a finite subset $\tau$, and this map is injective, since it sends distinct monomials to distinct monomials. The finite case gives $f = 0$ or $g = 0$. $\square$

**Theorem (Degree of a product).** Let $R$ be a domain and $f, g \in R[\sigma]$ nonzero. Then $\deg(fg) = \deg f + \deg g$ for the total degree.

*Proof.* Let $d = \deg f$ and $e = \deg g$, and let $f_d$, $g_e$ be the top homogeneous components. They are nonzero. Since $|a + b| = |a| + |b|$,
$$fg = f_d g_e + (\text{terms of degree} < d + e).$$
Here $f_d g_e$ is nonzero by the corollary and homogeneous of degree $d + e$. $\square$

**Theorem (Polynomials and functions).** Let $R$ be an infinite domain and $f \in R[x_1, \dots, x_n]$. If $f(a) = 0$ for all $a \in R^n$, then $f = 0$.

*Proof.* Induction on $n$. For $n = 0$, $f$ is a constant, equal to its value. Let $f \in R[x_1, \dots, x_{n+1}]$ vanish on $R^{n+1}$. Write $f = \sum_{j = 0}^m f_j(x_1, \dots, x_n) \, x_{n+1}^j$ by the theorem on one variable at a time. Fix $b \in R^n$. The polynomial $h(T) = \sum_j f_j(b) T^j \in R[T]$ has the value $f(b, t) = 0$ at every $t \in R$. A nonzero polynomial over a domain has at most its degree many roots (Volume 6, Chapter 5), and $R$ is infinite, so $h = 0$, that is, $f_j(b) = 0$ for all $j$. This holds for every $b \in R^n$, so $f_j = 0$ for all $j$ by the induction hypothesis, and $f = 0$. $\square$

::: mathlib
`MvPolynomial.aeval` · `Mathlib.Algebra.MvPolynomial.Eval`

`aeval s : MvPolynomial σ R →ₐ[R] S` is the homomorphism of the universal property for `s : σ → S`, and `aeval_X` says `aeval s (X i) = s i`. The uniqueness is `aeval_unique` or `algHom_ext`. For a ring homomorphism `g : R →+* S` there is `eval₂Hom g s`, and `eval s` evaluates at a point `s : σ → R`. `rename f` changes variables along `f : σ → τ`, `rename_injective` holds for injective `f`, and `exists_finset_rename` says that each polynomial comes from finitely many variables.

<?decl MvPolynomial.aeval?>
:::

::: mathlib
`MvPolynomial.finSuccEquiv` · `Mathlib.Algebra.MvPolynomial.Equiv`

`finSuccEquiv R n : MvPolynomial (Fin (n + 1)) R ≃ₐ[R] Polynomial (MvPolynomial (Fin n) R)`. It singles out the variable `0`, not the last one. The general form is `optionEquivLeft`, for the variables `Option σ`, and `sumAlgEquiv` splits the variables `σ ⊕ τ`. The domain property is the instance `instIsDomainOfIsCancelAdd`.

<?decl MvPolynomial.finSuccEquiv?>
:::

::: mathlib
`MvPolynomial.funext` · `Mathlib.Algebra.MvPolynomial.Funext`

`funext : (∀ x, eval x p = eval x q) → p = q` under `[IsDomain R] [Infinite R]`, for any type `σ` of variables.

<?decl MvPolynomial.funext?>
:::

### Examples

**Example (Degrees of $x^2 y + 3 x y^3$).** Let $f = x^2 y + 3 x y^3 \in \mathbb{Z}[x, y]$. The monomials are $x^{(2,1)}$ and $x^{(1,3)}$, of degrees $3$ and $4$. So $\deg f = 4$, $\deg_x f = 2$ and $\deg_y f = 3$. The homogeneous components are $f_3 = x^2 y$ and $f_4 = 3 x y^3$. Its square is $f^2 = x^4 y^2 + 6 x^3 y^4 + 9 x^2 y^6$, of total degree $8 = 4 + 4$, with top component $f_4^2 = 9 x^2 y^6$.

**Example (Symmetric polynomials).** The elementary symmetric polynomials in $x_1, x_2, x_3$ are $e_1 = x_1 + x_2 + x_3$, $e_2 = x_1 x_2 + x_1 x_3 + x_2 x_3$ and $e_3 = x_1 x_2 x_3$. They are homogeneous of degrees $1$, $2$, $3$. The power sum $p_2 = x_1^2 + x_2^2 + x_3^2$ is symmetric, and $p_2 = e_1^2 - 2 e_2$. By the fundamental theorem every symmetric polynomial is a unique polynomial in $e_1, \dots, e_n$, stated in Mathlib as `MvPolynomial.esymmAlgEquiv`.

**Counterexample (A finite field).** Over $\mathbb{F}_2$ the polynomial $x^2 - x$ is nonzero, but its value at $0$ and at $1$ is $0$. So the function $\mathbb{F}_2 \to \mathbb{F}_2$ is zero, and the theorem on polynomials and functions fails without the hypothesis that $R$ is infinite.

**Counterexample (Degree over a ring with zero divisors).** Over $\mathbb{Z}/4$, $f = 2x + 1$ and $g = 2y + 1$ have total degree $1$, but $fg = 4xy + 2x + 2y + 1 = 2x + 2y + 1$ has total degree $1 < 2$. So the domain hypothesis is needed, and `totalDegree_mul` is only an inequality.

### The library around it

Besides `degrees` and `vars` (the variables that occur), the library has weighted homogeneous polynomials, `IsWeightedHomogeneous`, and symmetric polynomials, `IsSymmetric` and `esymm`, in `Mathlib/RingTheory/MvPolynomial/`.

A common error of a learner: `MvPolynomial (Fin 2) R` and `Polynomial (Polynomial R)` are different types, and results move between them only through `finSuccEquiv` or `optionEquivLeft`.

### Exercises

1. (A) Compute the total degree, the degree in each variable and the homogeneous components of $(x + y)^2 - x^2 + z^3$ in $\mathbb{Q}[x, y, z]$.
2. (A) Show that the units of $R[\sigma]$ are the units of $R$ when $R$ is a domain. Hint: use the theorem on the degree of a product.
3. (A) Write $x_1^3 + x_2^3$ as a polynomial in $e_1 = x_1 + x_2$ and $e_2 = x_1 x_2$.
4. (B) Let $k$ be a field. Show that the ring homomorphism $k[x, y] \to k[t]$ with $x \mapsto t^2$ and $y \mapsto t^3$ has the kernel $(y^2 - x^3)$. Hint: divide by $y^2 - x^3$ as a monic polynomial in $y$, and write the remainder as $a(x) + b(x) y$.
5. (B) Let $k$ be a field with $q$ elements. Show that every function $k^n \to k$ is the function of a polynomial with all degrees $\deg_{x_i} < q$, and that this polynomial is unique. Hint: $\prod_i \bigl( 1 - (x_i - a_i)^{q-1} \bigr)$ is the indicator function of the point $a$; then count both sides.
6. (C) Show that a divisor of a homogeneous polynomial over a domain is homogeneous. Deduce that $x^2 + y^2 + z^2$ factors over $\mathbb{C}$ only into homogeneous factors, and show that it is irreducible over $\mathbb{C}$. Hint: a product of two linear forms is a quadratic form of rank at most $2$.

### Notes and history

The construction through finitely supported functions on monomials is the one of Bourbaki, *Algèbre*, Chapter IV.

### Reference

<?reference?>
