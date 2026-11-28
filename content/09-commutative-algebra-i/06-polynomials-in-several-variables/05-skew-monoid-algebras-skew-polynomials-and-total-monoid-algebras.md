---
title: Skew monoid algebras, skew polynomials and total monoid algebras
kind: api
modules:
  - Mathlib.Algebra.SkewMonoidAlgebra.Basic
  - Mathlib.Algebra.SkewMonoidAlgebra.Lift
  - Mathlib.Algebra.SkewMonoidAlgebra.Single
  - Mathlib.Algebra.SkewMonoidAlgebra.Support
  - Mathlib.Algebra.SkewPolynomial.Basic
  - Mathlib.Algebra.TotalMonoidAlgebra.Defs
explains:
  E2: [SkewMonoidAlgebra.single_mul_single, SkewMonoidAlgebra.coeff_mul_single_one, SkewMonoidAlgebra.liftNCRingHom, SkewMonoidAlgebra.support_mul, SkewPolynomial.monomial_mul_monomial, SkewPolynomial.X_mul_monomial, TotalMonoidAlgebra.coeff_mul, TotalMonoidAlgebra.single_mul_single]
  E1: auto
families: []
requires: [V05.C06, V06.C01, V06.C05, V06.C08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Skew monoid algebras, skew polynomials and total monoid algebras

### Overview

The monoid algebra $k[G]$ of a monoid $G$ over a semiring $k$ has the finitely supported functions $G \to k$ as elements and the convolution product. This section treats two variants of this construction. The first variant twists the product by an action of $G$ on $k$. The result is the skew monoid algebra $k[G; \sigma]$, and its most used special case is the ring of skew polynomials $R[X; \varphi]$, in which the variable does not commute with the scalars. The second variant keeps the product but drops the finiteness of the support. The result is the total monoid algebra, a large algebra of all functions $G \to R$.

Both variants are noncommutative or infinite in a way that the ordinary polynomial rings of this chapter are not. Skew polynomial rings are the standard source of examples in noncommutative ring theory: Ore extensions, rings of difference operators, and the rings of Frobenius twisted polynomials over a field of characteristic $p$. Total monoid algebras give a uniform model for power series: for $M = \sigma \to_0 \mathbb{N}$ the total algebra is the ring of formal power series in the variables $\sigma$, in the large sense where each formal infinite sum of monomials is an element.

The library keeps all three types as separate structures. They are not type synonyms for the monoid algebra, for `Polynomial` or for `MvPowerSeries`, and the lemmas of those types do not apply to them without a transfer.

### The library around it

#### The skew monoid algebra

`SkewMonoidAlgebra k G` is a structure with one field: a finitely supported function `SkewMonoidAlgebra.coeff`, of type $G \to_0 k$. The constructor is `SkewMonoidAlgebra.ofCoeff`. The element `SkewMonoidAlgebra.single a b` is the function with value $b$ at $a$ and $0$ elsewhere, and `SkewMonoidAlgebra.coeff_single` says that its coefficient function is `Finsupp.single a b`. The map `SkewMonoidAlgebra.of` sends $a$ to `SkewMonoidAlgebra.single a 1`, see `SkewMonoidAlgebra.of_apply`.

The additive structure needs only `AddCommMonoid k`. The product needs an action `MulSemiringAction G k`: each $g \in G$ acts on $k$ by a ring endomorphism, and the action is a monoid action. On single elements the product is

$$ (a_1 \cdot b_1)(a_2 \cdot b_2) = (a_1 a_2) \cdot \big(b_1 \,(a_1 \bullet b_2)\big). $$

This is `SkewMonoidAlgebra.single_mul_single`. In words: to move a scalar $b$ to the left past a group element $a$, replace $b$ with $a \bullet b$. For a general product, `SkewMonoidAlgebra.mul_def` and `SkewMonoidAlgebra.coeff_mul` give the double sum

$$ (f g)(x) = \sum_{a_1 a_2 = x} f(a_1)\,\big(a_1 \bullet g(a_2)\big). $$

The trivial action gives the convolution of the monoid algebra. The action on the right factor is the only change.

Associativity uses both axioms of the action. In $\big((a_1 \cdot b_1)(a_2 \cdot b_2)\big)(a_3 \cdot b_3)$ the last scalar becomes $(a_1 a_2) \bullet b_3$. In the other bracketing it becomes $a_1 \bullet (a_2 \bullet b_3)$, and the two agree because the action is a monoid action. The middle scalar becomes $a_1 \bullet (b_2 \,(a_2 \bullet b_3))$ in one bracketing and $(a_1 \bullet b_2)(a_1 \bullet a_2 \bullet b_3)$ in the other, and these agree because each $a_1$ acts multiplicatively. With these two facts, the instances `SkewMonoidAlgebra.instSemiring` and `SkewMonoidAlgebra.instRing` follow. `SkewMonoidAlgebra.instCommSemiring` needs a commutative monoid, a commutative semiring and `SMulCommClass G k k`. Exercise 3 shows that this last condition makes the action trivial.

The unit is `SkewMonoidAlgebra.single 1 1`. Multiplication on the right by a scalar at the unit is simple:

$$ (f \cdot (1 \cdot r))(x) = f(x)\,(x \bullet r). $$

This is `SkewMonoidAlgebra.coeff_mul_single_one`. Proof: in the double sum only $a_2 = 1$ contributes, so $a_1 = x$, and the term is $f(x)\,(x \bullet r)$. For a group, `SkewMonoidAlgebra.coeff_mul_single` gives the general right multiplication by `SkewMonoidAlgebra.single x r`: the coefficient at $y$ is $f(y x^{-1})\,\big((y x^{-1}) \bullet r\big)$. For a group, `SkewMonoidAlgebra.coeff_mul_left` and `SkewMonoidAlgebra.coeff_mul_right` also write a general product as a single sum: the coefficient at $x$ is $\sum_a f(a)\,(a \bullet g(a^{-1}x))$, or the same sum over the support of $g$.

The algebra structure is `SkewMonoidAlgebra.instAlgebraOfSMulCommClass`. For a $k$-algebra $A$ with an action of $G$, it makes `SkewMonoidAlgebra A G` a $k$-algebra. It needs `SMulCommClass G k A`, so the scalars of $k$ commute with the action. For $A = k$ with this condition, `SkewMonoidAlgebra.single_eq_algebraMap_mul_of` writes `SkewMonoidAlgebra.single a b` as `algebraMap k _ b * of k G a`.

#### Linear structure, induction and change of monoid

The coefficient map is a linear equivalence. `SkewMonoidAlgebra.coeffLinearEquiv` identifies the module with $G \to_0 k$, and `SkewMonoidAlgebra.coeffAddEquiv` does the same for the additive structure. Through them, `SkewMonoidAlgebra.basisSingleOne` gives the basis of single elements and `SkewMonoidAlgebra.instFree` says that the module is free.

The induction principles have the usual shape. `SkewMonoidAlgebra.induction_on` proves a property for each element from the cases $0$, `SkewMonoidAlgebra.single g a`, and sums. To sum a function over the support, apply `Finsupp.sum` to the coefficient function. The operations `SkewMonoidAlgebra.erase` and `SkewMonoidAlgebra.update` remove or change one coefficient.

A monoid homomorphism $G \to G'$ that is compatible with the actions induces a map of skew monoid algebras. `SkewMonoidAlgebra.mapDomain` is the additive map, `SkewMonoidAlgebra.mapDomainRingHom` is the ring map, and `SkewMonoidAlgebra.mapDomainAlgHom` is the algebra map. For an equivalence of monoids, `SkewMonoidAlgebra.domCongr` and `SkewMonoidAlgebra.domCongrAlg` give the equivalences.

#### The universal property

A ring map out of $k[G; \sigma]$ is given by a ring map $f : k \to R$ and a monoid map $g : G \to R$ that respect the twisted commutation rule. In $k[G; \sigma]$ the rule is $(y \cdot 1)(1 \cdot x) = (1 \cdot (y \bullet x))(y \cdot 1)$, by two uses of `SkewMonoidAlgebra.single_mul_single`. So the condition is

$$ f(y \bullet x)\, g(y) = g(y)\, f(x) \quad \text{for all } x \in k,\ y \in G. $$

Under this condition `SkewMonoidAlgebra.liftNCRingHom f g h` is the ring map that sends `SkewMonoidAlgebra.single a b` to $f(b)\,g(a)$. Proof sketch: the map is additive by definition. On single elements, the image of the product is $f(b_1)\, f(a_1 \bullet b_2)\, g(a_1)\, g(a_2)$, and the condition moves $g(a_1)$ to the left of $f(b_2)$, so the image is $f(b_1)\, g(a_1)\, f(b_2)\, g(a_2)$. The general case follows by additivity in each factor. The underlying additive map is `SkewMonoidAlgebra.liftNC`.

The module `Mathlib.Algebra.SkewMonoidAlgebra.Lift` gives the algebra versions. `SkewMonoidAlgebra.liftNCAlgHom` lifts an algebra map and a monoid map with the same kind of condition. `SkewMonoidAlgebra.lift` is the equivalence between monoid maps $G \to A$ and $k$-algebra maps $k[G; \sigma] \to A$, for a commutative semiring $k$, with `SMulCommClass G k k`. Its simp lemmas are `SkewMonoidAlgebra.lift_single`, which says that the lift sends `SkewMonoidAlgebra.single a b` to $b \bullet F(a)$, and `SkewMonoidAlgebra.lift_of`. `SkewMonoidAlgebra.lift_unique` expresses an algebra map by its values on single elements.

#### Support

The module `Mathlib.Algebra.SkewMonoidAlgebra.Support` relates the support of a product to the supports of the factors. `SkewMonoidAlgebra.support_mul` states

$$ \operatorname{supp}(f g) \subseteq \operatorname{supp}(f) \cdot \operatorname{supp}(g). $$

Proof: by `SkewMonoidAlgebra.coeff_mul`, a nonzero coefficient at $x$ needs a nonzero term $f(a_1)\,(a_1 \bullet g(a_2))$ with $a_1 a_2 = x$. Then $f(a_1) \neq 0$ and $g(a_2) \neq 0$, since the action fixes $0$. `SkewMonoidAlgebra.support_single_mul_eq_image` gives equality for left multiplication by a single element, under a hypothesis that prevents cancellation of the scalars. The module `Mathlib.Algebra.SkewMonoidAlgebra.Single` collects the lemmas about one coefficient: `SkewMonoidAlgebra.erase_single`, `SkewMonoidAlgebra.single_add_erase`, `SkewMonoidAlgebra.update_eq_erase_add_single`, `SkewMonoidAlgebra.support_update` and `SkewMonoidAlgebra.support_erase`. The principle `SkewMonoidAlgebra.induction` adds one new single element at a time to an element with smaller support.

#### Skew polynomials

The ring of skew polynomials is the abbreviation `SkewPolynomial R`, equal to `SkewMonoidAlgebra R (Multiplicative ℕ)`. The endomorphism $\varphi$ is not a parameter of the type. It comes from an instance `MulSemiringAction (Multiplicative ℕ) R`, and `SkewPolynomial.φ` is the action of `Multiplicative.ofAdd 1`, see `SkewPolynomial.φ_def`. An action of the free monoid on one generator is the same as one ring endomorphism, so this choice loses nothing. `SkewPolynomial.φ_iterate_apply` says that $\varphi^{n}(a)$ is the action of `ofAdd n` on $a$.

The API copies the names of `Polynomial`. The basic objects are `SkewPolynomial.X`, `SkewPolynomial.C`, `SkewPolynomial.monomial`, `SkewPolynomial.coeff` and `SkewPolynomial.support`, indexed by natural numbers instead of `Multiplicative ℕ`. `SkewPolynomial.monomial_def` unfolds `monomial n a` to a single element of the skew monoid algebra. `SkewPolynomial.C` is an additive map. The ring map is `SkewPolynomial.CRingHom`, and `SkewPolynomial.CRingHom_eq_C` relates the two.

The multiplication rules are the core of the module.

| Lean name | Statement |
| --- | --- |
| `SkewPolynomial.monomial_mul_monomial` | $(r X^n)(s X^m) = r\,\varphi^n(s)\, X^{n+m}$ |
| `SkewPolynomial.X_mul_monomial` | $X \cdot r X^n = \varphi(r)\, X^{n+1}$ |
| `SkewPolynomial.X_pow_mul_monomial` | $X^k \cdot r X^n = \varphi^k(r)\, X^{n+k}$ |
| `SkewPolynomial.monomial_mul_C` | $r X^n \cdot s = r\,\varphi^n(s)\, X^n$ |
| `SkewPolynomial.C_mul_monomial` | $a \cdot b X^n = (ab) X^n$ |
| `SkewPolynomial.monomial_mul_X` | $r X^n \cdot X = r X^{n+1}$ |
| `SkewPolynomial.X_mul` | $X p = \big(\sum_n \varphi(p_n) X^n\big) X$ |
| `SkewPolynomial.mul_def` | $f g = \sum_{n,m} f_n\, \varphi^n(g_m)\, X^{n+m}$ |

All of them follow from `SkewMonoidAlgebra.single_mul_single`. For example, for `SkewPolynomial.X_mul_monomial`: $X$ is `SkewMonoidAlgebra.single (ofAdd 1) 1` and $r X^n$ is `SkewMonoidAlgebra.single (ofAdd n) r`, so the product is `SkewMonoidAlgebra.single (ofAdd 1 * ofAdd n) (1 * φ r)`, and `ofAdd 1 * ofAdd n` is `ofAdd (n + 1)`. In particular $X a = \varphi(a) X$: the scalars move to the left of $X$ through $\varphi$, and to the right of $X$ they stay.

The remaining lemmas are bookkeeping in the style of `Polynomial`: `SkewPolynomial.coeff_monomial`, `SkewPolynomial.coeff_C`, `SkewPolynomial.coeff_X`, `SkewPolynomial.ext`, `SkewPolynomial.support_monomial`, `SkewPolynomial.support_X_pow`, `SkewPolynomial.sum_def`, `SkewPolynomial.induction`, and the extensionality lemmas `SkewPolynomial.addHom_ext` and `SkewPolynomial.linearMap_ext'`. The module has no degree function, no evaluation and no division algorithm.

#### Total monoid algebras

`TotalMonoidAlgebra R M` is a structure with one field `TotalMonoidAlgebra.coeff`, an arbitrary function $M \to R$. The constructor is `TotalMonoidAlgebra.ofCoeff`, and `TotalMonoidAlgebra.coeffEquiv` and `TotalMonoidAlgebra.coeffAddEquiv` identify the type with $M \to R$. The additive version `TotalAddMonoidAlgebra R M` is generated from the multiplicative one by the additive translation tool of the library, so each lemma below exists in both forms.

The product of two arbitrary functions has a coefficient at $z$ that sums over all pairs with product $z$. This sum must be finite. The class `Finset.HasMulAntidiagonal` provides, for each $z \in M$, the finset of pairs $(x, y)$ with $x y = z$. With it,

$$ (x y)(z) = \sum_{(p, q) \in \operatorname{antidiag}(z)} x(p)\, y(q). $$

This is `TotalMonoidAlgebra.coeff_mul`, and `TotalMonoidAlgebra.mul_def` is the same statement as an equation of elements. The additive version uses `Finset.HasAntidiagonal`, which exists for $\mathbb{N}$, for finite products of $\mathbb{N}$, and for $\sigma \to_0 \mathbb{N}$. A group such as $\mathbb{Z}$ has infinite antidiagonals and no such instance. The single elements `TotalMonoidAlgebra.single` multiply as in the monoid algebra: `TotalMonoidAlgebra.single_mul_single` says that the product of the single elements $r_1 m_1$ and $r_2 m_2$ is the single element $(r_1 r_2)(m_1 m_2)$. Proof: by `TotalMonoidAlgebra.coeff_mul`, the coefficient at $z$ is a sum over the antidiagonal of $z$. Only the pair $(m_1, m_2)$ gives a nonzero term, and it lies in the antidiagonal exactly when $z = m_1 m_2$.

The instance `TotalMonoidAlgebra.semiring` needs a monoid $M$ with `Finset.HasMulAntidiagonal M` and decidable equality. The map `TotalMonoidAlgebra.of` is the monoid map $m \mapsto$ `TotalMonoidAlgebra.single m 1`, and `TotalMonoidAlgebra.singleOneRingHom` is the ring map $r \mapsto$ `TotalMonoidAlgebra.single 1 r`; in the additive form it is `TotalAddMonoidAlgebra.singleZeroRingHom`. The lemmas `TotalMonoidAlgebra.coeff_mul_single_one` and `TotalMonoidAlgebra.coeff_single_one_mul` describe multiplication by scalars, and `TotalMonoidAlgebra.single_pow` computes powers of single elements. The module `Mathlib.Algebra.TotalMonoidAlgebra.Defs` gives the definitions and the semiring structure only. It has no commutative instance and no comparison with `PowerSeries` or `MvPowerSeries`.

#### Common errors

1. Finsupp lemmas do not apply to a skew monoid algebra. The type is a structure around $G \to_0 k$, so rewrite with `SkewMonoidAlgebra.coeff` first, or transfer through `SkewMonoidAlgebra.coeffLinearEquiv`.
2. The action is read from an instance. Two different `MulSemiringAction (Multiplicative ℕ) R` instances give two different rings `SkewPolynomial R` with the same name. To work with a chosen endomorphism, introduce the action as a local instance and check that `SkewPolynomial.φ` is the intended map.
3. A product in `TotalMonoidAlgebra R M` needs `Finset.HasMulAntidiagonal M`. If Lean does not find a multiplication on the type, the cause is usually this instance and not the semiring $R$.

### Exercises

1. (A) Show that `SkewPolynomial.X * SkewPolynomial.C a = SkewPolynomial.C (SkewPolynomial.φ a) * SkewPolynomial.X` from `SkewPolynomial.X_mul_monomial` and `SkewPolynomial.C_mul_X_eq_monomial`.
2. (A) Use `SkewMonoidAlgebra.single_mul_single` to show that, for the trivial action of $G$ on $k$, the product of two single elements is `SkewMonoidAlgebra.single (a₁ * a₂) (b₁ * b₂)`.
3. (B) Show that `MulSemiringAction G k` and `SMulCommClass G k k` together force $g \bullet a = a$ for all $g$ and $a$. Explain what this says about the hypotheses of `SkewMonoidAlgebra.lift`.
4. (B) Let $\varphi$ be injective and let $R$ have no zero divisors. Show that $\deg(pq) = \deg p + \deg q$ for nonzero skew polynomials, with the degree as the maximum of `SkewPolynomial.support`.
5. (B) Show that $X$ is central in $R[X; \varphi]$ if and only if $\varphi$ is the identity map.
6. (C) Give the map from `TotalAddMonoidAlgebra R ℕ` to `PowerSeries R` that keeps the coefficients, and prove that it is a ring isomorphism.

### Reference

<?reference?>
