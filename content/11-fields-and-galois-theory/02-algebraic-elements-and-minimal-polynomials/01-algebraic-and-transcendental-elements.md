---
title: Algebraic and transcendental elements
kind: theory
modules:
  - Mathlib.RingTheory.Algebraic.Defs
  - Mathlib.RingTheory.Algebraic.Basic
  - Mathlib.RingTheory.Algebraic.Integral
  - Mathlib.RingTheory.Algebraic.Cardinality
  - Mathlib.FieldTheory.Cardinality
  - Mathlib.RingTheory.AlgebraicIndependent.Defs
  - Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
explains:
  E3: [IsAlgebraic, Transcendental, Algebra.IsAlgebraic, Algebra.IsAlgebraic.trans, IsAlgebraic.of_finite]
  E2: [Algebra.IsAlgebraic.of_finite, IsAlgebraic.add, IsAlgebraic.inv, isAlgebraic_iff_isIntegral, transcendental_iff_injective, isAlgebraic_iff_not_injective, Polynomial.transcendental_X, IsAlgebraic.tower_top, Transcendental.of_tower_top, Subalgebra.algebraicClosure, Algebra.isAlgebraic_adjoin_iff, Subalgebra.isField_of_algebraic, Algebra.IsAlgebraic.cardinalMk_le_max, AlgebraicIndependent, IsTranscendenceBasis, exists_isTranscendenceBasis, IsTranscendenceBasis.isAlgebraic, Fintype.isPrimePow_card_of_field]
  E1: auto
families: []
requires: [V11.C01, V06.C05]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Algebraic and transcendental elements

### Overview

The number $\sqrt 2$ is a root of $X^2 - 2$. The number $\pi$ is a root of no nonzero polynomial with rational coefficients. The field $\mathbb{Q}(\sqrt 2)$ has degree $2$ and equals $\mathbb{Q}[\sqrt 2]$, but $\mathbb{Q}[\pi] \neq \mathbb{Q}(\pi)$ (Chapter 1, Section 1).

This section makes the difference precise. It proves that $\alpha$ is algebraic over $K$ if and only if $K(\alpha)/K$ is finite. From this and the tower law it derives that sums, products and inverses of algebraic elements are algebraic, and that algebraic over algebraic is algebraic. A count shows that the algebraic numbers are countable, so transcendental numbers exist. The section ends with transcendence bases, which measure how far an extension is from algebraic.

The section needs Chapter 1 and polynomials, evaluation and the root bound from Volume 6, Chapter 5.

### Definitions

**Definition (Algebraic element).** Let $L/K$ be an extension. An element $\alpha \in L$ is algebraic over $K$ if there is a nonzero $p \in K[X]$ with $p(\alpha) = 0$. Otherwise $\alpha$ is transcendental over $K$. An element of $\mathbb{C}$ that is algebraic over $\mathbb{Q}$ is an algebraic number.

Equivalently, $\alpha$ is transcendental if the evaluation map $K[X] \to L$, $p \mapsto p(\alpha)$, is injective. Then $K[X] \cong K[\alpha]$.

**Definition (Algebraic extension).** An extension $L/K$ is algebraic if each element of $L$ is algebraic over $K$.

::: mathlib
`IsAlgebraic` · `Mathlib.RingTheory.Algebraic.Defs`

`IsAlgebraic R x` is `∃ p : R[X], p ≠ 0 ∧ aeval x p = 0`. It makes sense for any commutative ring `R` and any `R`-algebra `A`. The map `Polynomial.aeval x : R[X] →ₐ[R] A` is evaluation at `x`. The lemma `isAlgebraic_iff_not_injective` restates the definition as the failure of injectivity of `aeval x`. Over a ring, a related notion is `IsIntegral R x`, with a monic polynomial. Over a field the two agree, since one can divide by the leading coefficient: this is `isAlgebraic_iff_isIntegral`.

<?decl IsAlgebraic?>
:::

::: mathlib
`Transcendental` · `Mathlib.RingTheory.Algebraic.Defs`

`Transcendental R x` is defined as `¬ IsAlgebraic R x`. The lemma `transcendental_iff_injective` gives the form `Function.Injective (aeval x)`. The first example is `Polynomial.transcendental_X`: the variable `X` is transcendental over `R` in `R[X]`.

<?decl Transcendental?>
:::

::: mathlib
`Algebra.IsAlgebraic` · `Mathlib.RingTheory.Algebraic.Defs`

`Algebra.IsAlgebraic R A` is a class with one field, `isAlgebraic : ∀ x : A, IsAlgebraic R x`. Lemmas take it in square brackets.

<?decl Algebra.IsAlgebraic?>
:::

### Theorems and proofs

**Theorem (Algebraic and finite).** Let $L/K$ be an extension and $\alpha \in L$. The following are equivalent.
1. $\alpha$ is algebraic over $K$.
2. The ring $K[\alpha]$ has finite dimension over $K$.
3. The field $K(\alpha)$ has finite dimension over $K$.

If they hold, then $K[\alpha] = K(\alpha)$.

*Proof.* (1 implies 2.) Let $p \neq 0$ with $p(\alpha) = 0$, of degree $n$. Each element of $K[\alpha]$ is $f(\alpha)$ for some $f \in K[X]$. Division with remainder (Volume 6, Chapter 5) gives $f = qp + r$ with $\deg r < n$, so $f(\alpha) = r(\alpha)$. Thus $1, \alpha, \dots, \alpha^{n-1}$ span $K[\alpha]$.

(2 implies $K[\alpha] = K(\alpha)$.) The ring $D = K[\alpha]$ is a subring of a field, so it has no zero divisors. Let $d \in D$ be nonzero. Multiplication by $d$ is a $K$-linear map $D \to D$, and it is injective, since $dx = 0$ gives $x = 0$. An injective linear map of a space of finite dimension to itself is surjective (Volume 7, Chapter 2). So $de = 1$ for some $e \in D$, and $D$ is a field. It contains $K$ and $\alpha$, so $K(\alpha) \subseteq D \subseteq K(\alpha)$.

(2 implies 3) follows, and (3 implies 2) holds because $K[\alpha] \subseteq K(\alpha)$ is a subspace.

(3 implies 1.) Let $[K(\alpha):K] = n$. The $n + 1$ elements $1, \alpha, \dots, \alpha^n$ are linearly dependent. So there are $c_0, \dots, c_n \in K$, not all zero, with $\sum c_i\alpha^i = 0$. Then $p = \sum c_iX^i$ is nonzero and $p(\alpha) = 0$. $\square$

**Corollary (Finite implies algebraic).** A finite extension $L/K$ is algebraic. More precisely, each $\alpha \in L$ is a root of a nonzero polynomial of degree at most $[L:K]$.

*Proof.* The last step of the proof works with $L$ in place of $K(\alpha)$. $\square$

::: mathlib
`IsAlgebraic.of_finite` · `Mathlib.RingTheory.Algebraic.Integral`

The statement is `IsAlgebraic.of_finite R e : IsAlgebraic R e`, under `[Module.Finite R A]` and `[Nontrivial R]`. The instance `Algebra.IsAlgebraic.of_finite` gives the class `Algebra.IsAlgebraic R A`. So in a finite extension, Lean finds the algebraicity by itself.

<?decl IsAlgebraic.of_finite?>
:::

**Theorem (The algebraic elements form a field).** Let $L/K$ be an extension. The set $A$ of elements of $L$ that are algebraic over $K$ is an intermediate field.

*Proof.* Let $\alpha, \beta \in A$. The element $\beta$ is algebraic over $K$, so also over $K(\alpha)$, with the same polynomial. By the theorem, $K(\alpha)/K$ and $K(\alpha)(\beta)/K(\alpha)$ are finite. By the tower law, $K(\alpha, \beta)/K$ is finite. By the corollary, each element of $K(\alpha, \beta)$ is algebraic over $K$. This includes $\alpha \pm \beta$, $\alpha\beta$ and, for $\alpha \neq 0$, $\alpha^{-1}$. Each $a \in K$ is a root of $X - a$. $\square$

The field $A$ is the algebraic closure of $K$ in $L$; for $\mathbb{C}/\mathbb{Q}$ it is the field $\overline{\mathbb{Q}}$ of algebraic numbers. Over a ring, Mathlib has the subalgebra `Subalgebra.algebraicClosure R S`, from `IsAlgebraic.add` and similar lemmas; inverses are `IsAlgebraic.inv`.

**Theorem (Transitivity).** Let $K \subseteq L \subseteq M$ be fields. If $L/K$ and $M/L$ are algebraic, then $M/K$ is algebraic.

*Proof.* Let $\gamma \in M$. It is a root of a nonzero $p = c_0 + c_1X + \dots + c_nX^n$ with $c_i \in L$. Let $E = K(c_0, \dots, c_n)$. Each $c_i$ is algebraic over $K$, so also over $K(c_0, \dots, c_{i-1})$. By the theorem, each step of the chain
$$K \subseteq K(c_0) \subseteq K(c_0, c_1) \subseteq \dots \subseteq E$$
is finite, and the tower law shows that $E/K$ is finite. The coefficients of $p$ lie in $E$, so $\gamma$ is algebraic over $E$, and $E(\gamma)/E$ is finite. By the tower law $E(\gamma)/K$ is finite. By the corollary, $\gamma$ is algebraic over $K$. $\square$

::: mathlib
`Algebra.IsAlgebraic.trans` · `Mathlib.RingTheory.Algebraic.Integral`

The statement is `Algebra.IsAlgebraic.trans R S A : Algebra.IsAlgebraic R A` for a tower `R → S → A` with `[IsScalarTower R S A]`, `[Algebra.IsAlgebraic R S]` and `[Algebra.IsAlgebraic S A]`. It also needs `[NoZeroDivisors S]`. The one step version for elements goes the other way: `IsAlgebraic.tower_top L` turns `IsAlgebraic K x` into `IsAlgebraic L x`, and `Transcendental.of_tower_top` turns `Transcendental L x` into `Transcendental K x`.

<?decl Algebra.IsAlgebraic.trans?>
:::

**Theorem (Countability).** The set of algebraic numbers is countable. So there are transcendental real numbers, and they form an uncountable set.

*Proof.* The polynomials of degree at most $n$ correspond to $\mathbb{Q}^{n+1}$, so $\mathbb{Q}[X]$ is countable. A nonzero polynomial has finitely many roots in $\mathbb{C}$ (Volume 6, Chapter 5), so the algebraic numbers form a countable union of finite sets. Since $\mathbb{R}$ is uncountable, the rest is uncountable. $\square$

In Mathlib, the theorem is `Algebraic.countable`, and `Algebra.IsAlgebraic.cardinalMk_le_max` gives the general bound $|L| \leq \max(|K|, \aleph_0)$ for an algebraic extension.

**Definition (Algebraic independence, transcendence basis).** Let $L/K$ be an extension. A family $(x_i)_{i \in I}$ of elements of $L$ is algebraically independent over $K$ if the evaluation map $K[X_i : i \in I] \to L$ is injective. A transcendence basis is an algebraically independent family $(x_i)$ such that $L$ is algebraic over $K(x_i : i \in I)$.

**Theorem (Transcendence bases).** Each extension $L/K$ has a transcendence basis, and any two have the same cardinality.

The existence follows from the lemma of Zorn: a maximal algebraically independent family is a transcendence basis. The equality of the cardinalities uses an exchange argument, as for bases of vector spaces. This volume uses the theorem only in Chapter 3, to classify algebraically closed fields, and does not prove it. The common cardinality is the transcendence degree.

::: mathlib
`IsTranscendenceBasis` · `Mathlib.RingTheory.AlgebraicIndependent.Defs`

`AlgebraicIndependent R x` says that `MvPolynomial.aeval x` is injective. `IsTranscendenceBasis R x` says that `x` is algebraically independent and maximal with this property. The theorem `exists_isTranscendenceBasis R A` gives existence. The theorem `IsTranscendenceBasis.isAlgebraic` gives the property of the definition above: `A` is algebraic over `Algebra.adjoin R (Set.range x)`. The degree is `Algebra.trdeg R A`, and `IsTranscendenceBasis.lift_cardinalMk_eq_trdeg` says that each transcendence basis has this cardinality.

<?decl IsTranscendenceBasis?>
:::

### Examples

**Example (An inverse as a polynomial).** Let $c = \sqrt[3]{2}$ and $\alpha = 1 + c$. The theorem says that $\alpha^{-1}$ lies in $\mathbb{Q}[c]$, so it is a polynomial in $c$. To find it, use $c^3 = 2$ and the identity $(1 + c)(1 - c + c^2) = 1 + c^3 = 3$. So
$$\frac{1}{1 + c} = \frac{1 - c + c^2}{3}.$$
The general method is the proof: write $\alpha^{-1}$ as $x_0 + x_1c + x_2c^2$ and solve the linear system $\alpha \cdot (x_0 + x_1c + x_2c^2) = 1$. With $c^3 = 2$, the product is $(x_0 + 2x_2) + (x_0 + x_1)c + (x_1 + x_2)c^2$, and the system $x_0 + 2x_2 = 1$, $x_0 + x_1 = 0$, $x_1 + x_2 = 0$ has the solution $x_0 = 1/3$, $x_1 = -1/3$, $x_2 = 1/3$.

**Example (Algebraic does not imply finite).** The converse of the corollary fails. Let $\overline{\mathbb{Q}} \subseteq \mathbb{C}$ be the field of algebraic numbers. It is algebraic over $\mathbb{Q}$ by definition. For each $n \geq 1$, it contains $2^{1/n}$, and Section 2 proves with the criterion of Eisenstein that $[\mathbb{Q}(2^{1/n}):\mathbb{Q}] = n$. If $[\overline{\mathbb{Q}}:\mathbb{Q}]$ were finite, then each $n$ would divide it. So $\overline{\mathbb{Q}}/\mathbb{Q}$ is algebraic and infinite.

**Example (Rational functions).** The field $K(t)$ has the transcendence basis $\{t\}$ over $K$, so its transcendence degree is $1$. The element $t$ is transcendental by `Polynomial.transcendental_X`. Let $f = g/h \in K(t) \setminus K$. Then $t$ is a root of $g(X) - f\,h(X) \in K(f)[X]$. This polynomial is nonzero: if all its coefficients $g_i - f h_i$ were $0$, then $f = g_i/h_i \in K$ for an $i$ with $h_i \neq 0$. So $K(t)/K(f)$ is algebraic. If $f$ were algebraic over $K$, then $t$ would be algebraic over $K$ by transitivity. So $f$ is transcendental.

### The library around it

Three lemmas connect algebraicity to the structure of subalgebras. `Algebra.isAlgebraic_adjoin_iff` says that `Algebra.adjoin R s` is algebraic if and only if each element of `s` is. `Subalgebra.isField_of_algebraic` says that a subalgebra of an algebraic extension of fields is a field: this is the step $K[\alpha] = K(\alpha)$ of the theorem.

For finite fields, `Fintype.isPrimePow_card_of_field` says that the size of a finite field is a prime power.

**Common errors.** Over a ring, `IsAlgebraic` is weaker than `IsIntegral`: over $\mathbb{Z}$, $1/2$ is a root of $2X - 1$ but is not integral. A proof of `IsAlgebraic K x` needs the proof that the polynomial is nonzero.

### Exercises

1. (A) Show that $\sqrt 2 + \sqrt 3$ and $\sqrt 2\sqrt[3]{5}$ are algebraic over $\mathbb{Q}$ without finding a polynomial. Hint: the field of algebraic elements.

2. (A) Express $(1 + \sqrt 2 + \sqrt 3)^{-1}$ in the basis $1, \sqrt 2, \sqrt 3, \sqrt 6$. Hint: multiply first by $1 + \sqrt 2 - \sqrt 3$, then remove $\sqrt 2$ from the denominator.

3. (A) Show that if $\alpha$ is transcendental over $K$, then so are $\alpha^2$, $\alpha + 1$ and $1/\alpha$. Hint: if $\alpha^2$ were algebraic, then $\alpha$ would be a root of $p(X^2)$.

4. (B) Let $\alpha$ be algebraic and $\beta$ transcendental over $K$. Show that $\alpha + \beta$ and, for $\alpha \neq 0$, $\alpha\beta$ are transcendental. Hint: the algebraic elements form a field.

5. (B) Show that $\mathbb{C}/\overline{\mathbb{Q}}$ is not algebraic, and that the transcendental numbers in $\mathbb{C}$ form an uncountable set. Hint: transitivity and countability.

6. (B) Let $L/K$ be algebraic and $R$ a ring with $K \subseteq R \subseteq L$. Show that $R$ is a field. Hint: for $r \neq 0$, use $K[r] \subseteq R$ and the theorem on algebraic elements.

7. (B) Show that an extension $L/K$ is finite if and only if it is algebraic and finitely generated. Hint: the tower law along $K(\alpha_1) \subseteq K(\alpha_1, \alpha_2) \subseteq \dots$.

8. (C) Let $K$ be a countable field and $L/K$ algebraic. Show that $L$ is countable. Deduce that $\mathbb{C}$ has an uncountable transcendence basis over $\mathbb{Q}$. Hint: count roots as in the countability theorem; for the second part, $\mathbb{Q}(S)$ is countable for a countable $S$.

### Notes and history

Liouville constructed the first explicit transcendental numbers in 1844. Cantor proved in 1874 that the algebraic numbers are countable, which gives the existence of transcendental numbers without a construction. Hermite proved that $e$ is transcendental in 1873, and Lindemann proved that $\pi$ is transcendental in 1882. Steinitz introduced transcendence bases in his article of 1910.

### Reference

<?reference?>
