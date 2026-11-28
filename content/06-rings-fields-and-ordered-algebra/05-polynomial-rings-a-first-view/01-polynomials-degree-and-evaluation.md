---
title: Polynomials, degree and evaluation
kind: theory
modules: []
explains:
  E1: [Polynomial, Polynomial.C, Polynomial.X, Polynomial.degree, Polynomial.natDegree, Polynomial.leadingCoeff, Polynomial.Monic, Polynomial.degree_mul, Polynomial.natDegree_mul, Polynomial.noZeroDivisors_iff, Polynomial.isUnit_iff, Polynomial.eval₂, Polynomial.eval₂RingHom, Polynomial.eval, Polynomial.ringHom_ext]
families: []
requires: [V06.C03, V06.C04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Polynomials, degree and evaluation

### Overview

A polynomial is a formal expression $a_0 + a_1 X + \dots + a_n X^n$. In algebra a polynomial is its list of coefficients, not a function. The two views agree over $\mathbb{R}$, but not over a finite ring: over $\mathbb{F}_2$ the polynomials $X^2$ and $X$ are different and they take the same values. So the definition must be the formal one.

This section builds the ring $R[X]$ of polynomials over a commutative ring $R$. It defines the degree and the leading coefficient and proves the degree formula $\deg(fg) = \deg f + \deg g$ over an integral domain. Two consequences follow: $R[X]$ is an integral domain when $R$ is, and the units of $R[X]$ are then the constant units. The section ends with the universal property of $R[X]$: for each ring homomorphism $\varphi : R \to S$ to a commutative ring and each $s \in S$ there is exactly one ring homomorphism $R[X] \to S$ that extends $\varphi$ and sends $X$ to $s$. Evaluation of a polynomial at a point is the case $\varphi = \mathrm{id}$.

### Definitions

In this section $R$ is a commutative ring. Most definitions work for a semiring, and Mathlib states them so.

**Definition (Polynomial).** A polynomial over $R$ is a sequence $(a_0, a_1, a_2, \dots)$ of elements of $R$ such that $a_k = 0$ for all but finitely many $k$. The element $a_k$ is the coefficient of degree $k$. The set of polynomials is $R[X]$. The sum and the product are
$$(a + b)_k = a_k + b_k, \qquad (a b)_k = \sum_{i + j = k} a_i b_j.$$
The sum in the product is finite, with the $k + 1$ terms $i = 0, \dots, k$. The constant polynomial $c$ is the sequence $(c, 0, 0, \dots)$, and $X$ is the sequence $(0, 1, 0, 0, \dots)$.

The product rule gives $X^n = (0, \dots, 0, 1, 0, \dots)$ with the $1$ at place $n$, by induction on $n$. So the polynomial with coefficients $a_0, \dots, a_n$ and zeros after them is the sum $\sum_{k=0}^n a_k X^k$. This justifies the usual notation, and from now on the text uses it. The rule for the product is the rule that the distributive law and $X^i X^j = X^{i+j}$ force.

::: mathlib
`Polynomial` · `Mathlib.Algebra.Polynomial.Basic`

`Polynomial R` has the notation `R[X]` after `open Polynomial`. At this commit it is an abbreviation for `AddMonoidAlgebra R ℕ`, the finitely supported functions `ℕ → R` with the convolution product of Volume 3. This is the definition of the text: a polynomial is its sequence of coefficients. The coefficient of degree `n` is `p.coeff n`, and two polynomials with the same coefficients are equal by `AddMonoidAlgebra.ext`. Mathlib defines `Polynomial R` for a semiring `R`, so `ℕ[X]` is a valid type.

<?decl Polynomial?>
:::

::: mathlib
`Polynomial.C` · `Mathlib.Algebra.Polynomial.Basic`

The constant polynomials as a ring homomorphism `C : R →+* R[X]`. The variable is `Polynomial.X`. A polynomial written in a proof looks like `C 3 * X ^ 2 + X + C 1`.

<?decl Polynomial.C?>
:::

::: mathlib
`Polynomial.X` · `Mathlib.Algebra.Polynomial.Basic`

The variable. It commutes with everything: `Polynomial.X_mul : X * p = p * X`.

<?decl Polynomial.X?>
:::

**Definition (Degree, leading coefficient, monic).** Let $f = \sum_k a_k X^k$ be a nonzero polynomial. Its degree $\deg f$ is the largest $n$ with $a_n \ne 0$, and $a_n$ is its leading coefficient. The degree of the zero polynomial is $-\infty$, with the rules $-\infty < n$ and $-\infty + n = -\infty + (-\infty) = -\infty$. A polynomial is monic if its leading coefficient is $1$. A polynomial of degree $\le 0$ is a constant.

The value $-\infty$ makes the degree formula true also when one factor is zero.

::: mathlib
`Polynomial.degree` · `Mathlib.Algebra.Polynomial.Degree.Defs`

The degree has values in `WithBot ℕ`, the natural numbers with a new least element `⊥`, and `degree 0 = ⊥`. This is the $-\infty$ of the text. The addition of `WithBot ℕ` has `⊥ + n = ⊥`.

<?decl Polynomial.degree?>
:::

::: mathlib
`Polynomial.natDegree` · `Mathlib.Algebra.Polynomial.Degree.Defs`

The degree as a natural number, with the junk value `natDegree 0 = 0`. A lemma about `natDegree` often needs the hypothesis `p ≠ 0`. The two are related by `Polynomial.degree_eq_natDegree : p ≠ 0 → p.degree = p.natDegree`.

<?decl Polynomial.natDegree?>
:::

::: mathlib
`Polynomial.leadingCoeff` · `Mathlib.Algebra.Polynomial.Degree.Defs`

The coefficient of degree `natDegree p`. So `leadingCoeff 0 = 0`, and `Polynomial.leadingCoeff_ne_zero : p.leadingCoeff ≠ 0 ↔ p ≠ 0`.

<?decl Polynomial.leadingCoeff?>
:::

::: mathlib
`Polynomial.Monic` · `Mathlib.Algebra.Polynomial.Degree.Defs`

The proposition `p.leadingCoeff = 1`. Over the zero ring every polynomial is monic, so a lemma that needs `p ≠ 0` from `p.Monic` also needs `[Nontrivial R]`: this is `Polynomial.Monic.ne_zero`.

<?decl Polynomial.Monic?>
:::

**Definition (Evaluation).** Let $\varphi : R \to S$ be a ring homomorphism to a commutative ring $S$, and let $s \in S$. For $f = \sum_{k=0}^n a_k X^k$ put
$$\mathrm{ev}_{\varphi, s}(f) = \sum_{k=0}^n \varphi(a_k)\, s^k.$$
When $S = R$ and $\varphi = \mathrm{id}$ this is the value $f(s)$ of $f$ at $s$. The value does not depend on the choice of $n$, since a coefficient $a_k = 0$ adds $\varphi(0) s^k = 0$.

::: mathlib
`Polynomial.eval₂` · `Mathlib.Algebra.Polynomial.Eval.Defs`

`eval₂ f x p` is $\mathrm{ev}_{f, x}(p)$. It is defined for any semiring `S`, but it is a ring homomorphism in `p` only when the values of `f` commute with `x`; for a commutative `S` the bundled form is `Polynomial.eval₂RingHom`.

<?decl Polynomial.eval₂?>
:::

::: mathlib
`Polynomial.eval` · `Mathlib.Algebra.Polynomial.Eval.Defs`

`eval x p` is $p(x)$, the case `f = RingHom.id R` of `eval₂`. The point comes first. The simp lemmas `Polynomial.eval_add`, `Polynomial.eval_mul`, `Polynomial.eval_X` and `Polynomial.eval_C` compute values.

<?decl Polynomial.eval?>
:::

### Theorems and proofs

**Theorem (The polynomial ring).** With the sum and the product above, $R[X]$ is a commutative ring with zero the zero sequence and one the constant $1$. The map $c \mapsto c$ is an injective ring homomorphism $R \to R[X]$.

*Proof.* The sum of two sequences with finitely many nonzero terms has finitely many nonzero terms. For the product, if $a_i = 0$ for $i > m$ and $b_j = 0$ for $j > n$, then each term of $(ab)_k$ for $k > m + n$ has $i > m$ or $j > n$, so $(ab)_k = 0$. The addition is the addition of sequences, so it is associative and commutative, with zero $0$ and negative $(-a_k)$. The product is commutative because $\sum_{i+j=k} a_i b_j = \sum_{j+i=k} b_j a_i$. The constant $1$ is a unit element: $(1 \cdot b)_k = \sum_{i+j=k} 1_i b_j = b_k$, since $1_i = 0$ for $i > 0$. The distributive law holds term by term: $\sum_{i+j=k} a_i (b_j + c_j) = \sum_{i+j=k} a_i b_j + \sum_{i+j=k} a_i c_j$. For associativity, compute the coefficient of degree $k$ of both sides:
$$((ab)c)_k = \sum_{l + j = k} \Big(\sum_{i + h = l} a_i b_h\Big) c_j = \sum_{i + h + j = k} a_i b_h c_j,$$
$$(a(bc))_k = \sum_{i + l = k} a_i \Big(\sum_{h + j = l} b_h c_j\Big) = \sum_{i + h + j = k} a_i b_h c_j.$$
Both are the sum over all triples with $i + h + j = k$, so they are equal. The map $c \mapsto (c, 0, 0, \dots)$ preserves sums, it sends $1$ to $1$, and $(c, 0, \dots)(d, 0, \dots) = (cd, 0, \dots)$ because the only nonzero term of the product formula is $i = j = 0$. It is injective, since $c$ is the coefficient of degree $0$. $\square$

**Theorem (Degree of a sum and of a product).** Let $f, g \in R[X]$. Then
1. $\deg(f + g) \le \max(\deg f, \deg g)$;
2. $\deg(fg) \le \deg f + \deg g$, and if $f$ and $g$ are nonzero with degrees $m$ and $n$ and leading coefficients $a$ and $b$, then the coefficient of $X^{m+n}$ in $fg$ is $ab$.

*Proof.* (1) If $k > \max(\deg f, \deg g)$, then $f_k = g_k = 0$, so $(f+g)_k = 0$. (2) If $f = 0$ or $g = 0$, then $fg = 0$ and both sides are $-\infty$. Otherwise the proof of the previous theorem shows $(fg)_k = 0$ for $k > m + n$. For $k = m + n$, a term $f_i g_j$ with $i + j = m + n$ and $(i, j) \ne (m, n)$ has $i > m$ or $j > n$, so it is zero. The only term left is $f_m g_n = ab$. $\square$

**Theorem (Degree formula over a domain).** Let $R$ be an integral domain and let $f, g \in R[X]$. Then $\deg(fg) = \deg f + \deg g$, and the leading coefficient of $fg$ is the product of the leading coefficients.

*Proof.* If $f = 0$ or $g = 0$, both sides are $-\infty$. Otherwise let $a, b$ be the leading coefficients. They are nonzero, and $R$ has no zero divisors, so $ab \ne 0$. By the previous theorem, $ab$ is the coefficient of $X^{\deg f + \deg g}$ in $fg$ and all higher coefficients vanish. So $\deg(fg) = \deg f + \deg g$ with leading coefficient $ab$. $\square$

The proof needs only that the product of the two leading coefficients is nonzero. So the formula holds over any commutative ring when one of the two polynomials is monic: $1 \cdot b = b \ne 0$. This remark is used in Section 2 for the division by a monic polynomial.

**Corollary (Polynomials over a domain).** Let $R$ be a commutative ring. Then $R[X]$ is an integral domain if and only if $R$ is an integral domain. If $R$ is an integral domain, the units of $R[X]$ are the constant polynomials $c$ with $c \in R^\times$.

*Proof.* If $R[X]$ is a domain, then so is its subring $R$ of constants, since a subring of a domain is a domain. Conversely let $R$ be a domain. Then $R[X]$ is commutative, and $1 \ne 0$ in $R[X]$ because $1 \ne 0$ in $R$. If $f \ne 0$ and $g \ne 0$, then $\deg(fg) = \deg f + \deg g \ge 0$, so $fg \ne 0$. For the units, let $fg = 1$. Then $\deg f + \deg g = \deg 1 = 0$, and both degrees are $\ge 0$, so both are $0$. Thus $f = c$ and $g = d$ are constants with $cd = 1$ in $R$, and $c \in R^\times$. Conversely a constant unit $c$ has the inverse $c^{-1}$ in $R[X]$. $\square$

::: mathlib
`Polynomial.degree_mul` · `Mathlib.Algebra.Polynomial.Degree.Operations`

The degree formula, stated with `[NoZeroDivisors R]` for a semiring. The inequality for any semiring is `Polynomial.degree_mul_le`, and the sum is `Polynomial.degree_add_le`.

<?decl Polynomial.degree_mul?>
:::

::: mathlib
`Polynomial.natDegree_mul` · `Mathlib.Algebra.Polynomial.Degree.Domain`

The same formula for `natDegree`. Here the hypotheses `p ≠ 0` and `q ≠ 0` are needed: with `p = 0` and `q = X` the left side is `0` and the right side is `1`.

<?decl Polynomial.natDegree_mul?>
:::

::: mathlib
`Polynomial.noZeroDivisors_iff` · `Mathlib.Algebra.Polynomial.Basic`

The first half of the corollary, in the form `NoZeroDivisors R[X] ↔ NoZeroDivisors R`. Instance search gives `IsDomain R[X]` from `IsDomain R`.

<?decl Polynomial.noZeroDivisors_iff?>
:::

::: mathlib
`Polynomial.isUnit_iff` · `Mathlib.Algebra.Polynomial.Degree.Units`

The units of `R[X]` over a semiring with no zero divisors: `IsUnit p ↔ ∃ r, IsUnit r ∧ C r = p`.

<?decl Polynomial.isUnit_iff?>
:::

**Theorem (Universal property of $R[X]$).** Let $\varphi : R \to S$ be a ring homomorphism to a commutative ring $S$ and let $s \in S$. Then $\mathrm{ev}_{\varphi, s} : R[X] \to S$ is a ring homomorphism with $\mathrm{ev}_{\varphi,s}(c) = \varphi(c)$ for $c \in R$ and $\mathrm{ev}_{\varphi,s}(X) = s$. It is the only ring homomorphism $\psi : R[X] \to S$ with $\psi(c) = \varphi(c)$ for all $c \in R$ and $\psi(X) = s$.

*Proof.* Write $\mathrm{ev}$ for $\mathrm{ev}_{\varphi, s}$. By definition, $\mathrm{ev}(c) = \varphi(c) s^0 = \varphi(c)$ and $\mathrm{ev}(X) = \varphi(1) s = s$. In particular $\mathrm{ev}(1) = 1$. Additivity: for $f = \sum a_k X^k$ and $g = \sum b_k X^k$, with a common bound $n$ for the degrees,
$$\mathrm{ev}(f + g) = \sum_{k=0}^n \varphi(a_k + b_k) s^k = \sum_{k=0}^n \varphi(a_k) s^k + \sum_{k=0}^n \varphi(b_k) s^k = \mathrm{ev}(f) + \mathrm{ev}(g).$$
Multiplicativity: expand the product of the two finite sums in $S$ and group the terms by $i + j$:
$$\mathrm{ev}(f)\,\mathrm{ev}(g) = \sum_{i, j} \varphi(a_i) s^i \varphi(b_j) s^j = \sum_{k} \Big(\sum_{i + j = k} \varphi(a_i)\varphi(b_j)\Big) s^k = \sum_k \varphi\Big(\sum_{i+j=k} a_i b_j\Big) s^k = \mathrm{ev}(fg).$$
The second equality moves $s^i$ past $\varphi(b_j)$. This step uses that $S$ is commutative. The third uses that $\varphi$ is a ring homomorphism.

Uniqueness: let $\psi$ be a ring homomorphism with $\psi(c) = \varphi(c)$ and $\psi(X) = s$. For $f = \sum_{k=0}^n a_k X^k$,
$$\psi(f) = \sum_{k=0}^n \psi(a_k)\psi(X)^k = \sum_{k=0}^n \varphi(a_k) s^k = \mathrm{ev}(f),$$
since $\psi$ preserves sums, products and powers. $\square$

So a ring homomorphism out of $R[X]$ is the same as a ring homomorphism out of $R$ together with one element of the target. In particular $f \mapsto f(s)$ is a ring homomorphism $R[X] \to R$ for each $s \in R$. Its kernel contains $X - s$, and Section 2 shows that the kernel is the ideal $(X - s)$.

::: mathlib
`Polynomial.eval₂RingHom` · `Mathlib.Algebra.Polynomial.Eval.Defs`

The map of the theorem, bundled as `R[X] →+* S` for a commutative semiring `S`. The variant `Polynomial.aeval` for an algebra over `R` is in Chapter 8.

<?decl Polynomial.eval₂RingHom?>
:::

::: mathlib
`Polynomial.ringHom_ext` · `Mathlib.Algebra.Polynomial.Monomial`

The uniqueness half of the universal property: two ring homomorphisms out of `R[X]` that agree on the constants and on `X` are equal.

<?decl Polynomial.ringHom_ext?>
:::

### Examples

**Example (A product and a value).** In $\mathbb{Z}[X]$ let $f = 2X^2 - X + 3$ and $g = X^3 + 4X - 1$. The coefficient of $X^k$ in $fg$ collects the products of terms whose degrees add to $k$:
$$fg = 2X^5 + (-1)X^4 + (3 + 8)X^3 + (-2 - 4)X^2 + (12 + 1)X - 3 = 2X^5 - X^4 + 11X^3 - 6X^2 + 13X - 3.$$
For example, the coefficient of $X^2$ comes from $2X^2 \cdot (-1)$ and $(-X) \cdot 4X$. The degree is $5 = 2 + 3$ and the leading coefficient is $2 = 2 \cdot 1$. Evaluation at $2$ is a ring homomorphism, so it can be checked: $f(2) = 8 - 2 + 3 = 9$ and $g(2) = 8 + 8 - 1 = 15$, and $(fg)(2) = 64 - 16 + 88 - 24 + 26 - 3 = 135 = 9 \cdot 15$.

**Counterexample (A unit of positive degree).** Over $\mathbb{Z}/4$, which is not a domain,
$$(1 + 2X)(1 + 2X) = 1 + 4X + 4X^2 = 1.$$
So $1 + 2X$ is a unit of $(\mathbb{Z}/4)[X]$ of degree $1$, and its own inverse. Both the degree formula and the description of the units fail: $\deg((1+2X)^2) = 0 \ne 2$. The leading coefficient $2$ has $2 \cdot 2 = 0$, which is exactly the case that the proof excludes.

**Counterexample (Polynomials are not functions).** Over $\mathbb{F}_2 = \mathbb{Z}/2$ the polynomial $f = X^2 + X$ is not zero: its coefficients are $(0, 1, 1, 0, \dots)$. But $f(0) = 0$ and $f(1) = 1 + 1 = 0$. So $f$ defines the zero function on $\mathbb{F}_2$. The map from $\mathbb{F}_2[X]$ to the functions $\mathbb{F}_2 \to \mathbb{F}_2$ is not injective. Section 2 shows that this cannot happen over an infinite domain.

**Counterexample (The universal property needs commutativity).** Let $\mathbb{H}$ be the quaternions of Chapter 3, with $ij = k = -ji$, and let $\varphi : \mathbb{C} \to \mathbb{H}$ be the inclusion $a + bi \mapsto a + bi$. Take $s = j$. Then the formula $\mathrm{ev}(f) = \sum \varphi(a_k) j^k$ is not multiplicative. With $f = X$ and $g = i$ (a constant), $fg = iX$ in $\mathbb{C}[X]$, so $\mathrm{ev}(fg) = i j = k$. But $\mathrm{ev}(f)\,\mathrm{ev}(g) = j i = -k$. The step of the proof that moves $s^i$ past $\varphi(b_j)$ fails, because $j$ does not commute with $\varphi(i)$. This is why Mathlib asks for a commutative target in `eval₂RingHom`.

### The library around it

Volume 9 covers the rest of the polynomial library. The coefficients are `Polynomial.coeff p n`, with the simp lemmas `coeff_add`, `coeff_C_mul`, `coeff_X_pow` and the convolution formula `Polynomial.coeff_mul`. The monomial $c X^n$ is `Polynomial.monomial n c`, equal to `C c * X ^ n`. The induction principle is `Polynomial.induction_on`.

The degree lemmas come in pairs, one for `degree` and one for `natDegree`. The `degree` form has no side condition for zero, and the `natDegree` form usually asks `p ≠ 0`. The tactic `compute_degree` proves goals such as `natDegree (X ^ 3 + C 2 * X) = 3`, and `monicity` proves that an explicit polynomial is monic.

Common errors of a learner:

- `natDegree 0 = 0`, so `natDegree p = 0` does not mean `p` is a nonzero constant. Use `degree` or add `p ≠ 0`.
- Over a ring with zero divisors, `degree_mul` does not apply. Instance search fails with a missing `NoZeroDivisors`, which is the right error: the formula is false there.

### Exercises

1. (A) Compute $(X^2 + X + 1)(X^2 - X + 1)$ in $\mathbb{Z}[X]$ and check the degree formula. Hint: the answer has only three nonzero terms.
2. (A) Compute $(3X + 2)(2X + 3)$ in $(\mathbb{Z}/6)[X]$ and give its degree. Hint: reduce each coefficient modulo $6$.
3. (B) Show that $a + bX$ with $a \in R^\times$ and $b$ nilpotent is a unit of $R[X]$. Hint: Chapter 3 shows that a unit plus a nilpotent is a unit.
4. (B) Let $R$ be a domain. Show that $X$ is irreducible in $R[X]$, that is, $X = fg$ implies that $f$ or $g$ is a unit. Hint: compare degrees, then compare the coefficients of $X$.
5. (B) Use the universal property to show that $X \mapsto X + 1$ extends to a ring automorphism of $R[X]$ that fixes the constants. Hint: find its inverse, and use the uniqueness half for both composites.
6. (B) Show that the evaluation map $\mathbb{R}[X] \to \mathbb{C}$, $f \mapsto f(i)$, is surjective, and that $X^2 + 1$ is in its kernel.
7. (C) Show that each ring homomorphism $\mathbb{Z}[X] \to \mathbb{Z}$ is evaluation at some integer. Hint: a ring homomorphism $\mathbb{Z} \to \mathbb{Z}$ is the identity.
8. (C) Show that the map $\mathbb{F}_p[X] \to \{\text{functions } \mathbb{F}_p \to \mathbb{F}_p\}$ is surjective, and find a nonzero polynomial in its kernel. Hint: for each $a$, the polynomial $1 - (X - a)^{p-1}$ is $1$ at $a$ and $0$ elsewhere, by Fermat's little theorem of Chapter 4.

### Notes and history

Polynomials as formal objects are much younger than polynomial equations. The view of a polynomial as the sequence of its coefficients, independent of any values, became standard with the abstract algebra of Steinitz (1910) and of the school of Noether in the 1920s, when fields of positive characteristic made the difference between a polynomial and a function visible. The universal property is the form of the definition in Bourbaki, *Algèbre*, Chapter IV, and in Lang, *Algebra*, Chapter IV §1.

In Mathlib, the file `Mathlib/Algebra/Polynomial/Basic.lean` has the authors Chris Hughes, Johannes Hölzl, Kim Morrison and Jens Wagemaker, and it goes back to the polynomial library of Lean 3 of 2018. The type has changed form more than once, but a reader who uses only the API of this section does not see the difference.

### Reference

<?reference?>
