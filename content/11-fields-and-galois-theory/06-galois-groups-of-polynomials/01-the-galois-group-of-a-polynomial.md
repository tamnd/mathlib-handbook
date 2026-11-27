---
title: The Galois group of a polynomial
kind: theory
modules:
  - Mathlib.FieldTheory.PolynomialGaloisGroup
  - Mathlib.Algebra.CubicDiscriminant
explains:
  E3: [Polynomial.Gal, Polynomial.Gal.galActionHom, Polynomial.Gal.galAction_isPretransitive, Cubic, Cubic.discr]
  E2: [Polynomial.Gal.galAction, Polynomial.Gal.galActionHom_injective, Polynomial.Gal.card_of_separable, Polynomial.Gal.prime_degree_dvd_card, Polynomial.Gal.restrict, Polynomial.Gal.restrict_surjective, Polynomial.Gal.restrictProd, Polynomial.Gal.restrictProd_injective, Polynomial.Gal.uniqueGalXPow, Polynomial.Gal.mapRoots_bijective, Cubic.toPoly, Cubic.discr_eq_prod_three_roots, Cubic.discr_ne_zero_iff_roots_nodup, Cubic.splits_iff_roots_eq_three]
  E1: auto
families: []
requires: [V11.C05, V05.C07, V05.C06]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The Galois group of a polynomial

### Overview

The Galois group of a polynomial $f \in K[X]$ is the group of the automorphisms of its splitting field over $K$. Each automorphism permutes the roots of $f$ and is fixed by this permutation, since the roots generate the splitting field. For $f$ of degree $n$ with distinct roots, it is a subgroup of $S_n$, defined up to the choice of a numbering of the roots.

This section proves two basic facts. For a separable $f$ the group is transitive if and only if $f$ is irreducible. Outside characteristic $2$ it lies in $A_n$ if and only if the discriminant of $f$ is a square in $K$; for an irreducible cubic this decides between $A_3$ and $S_3$.

The section uses the fundamental theorem and the theorem on conjugates (Chapter 5), the sign of a permutation and the alternating group (Volume 5, Chapter 7), and orbits (Volume 5, Chapter 6).

### Definitions

**Definition (Galois group of a polynomial).** Let $f \in K[X]$ and let $L$ be a splitting field of $f$ over $K$. The Galois group of $f$ is $\operatorname{Gal}(f) = \operatorname{Aut}(L/K)$. By the uniqueness of splitting fields (Chapter 3), it is defined up to isomorphism.

If $f$ is separable, $L/K$ is Galois (Chapter 5, Section 2) and $|\operatorname{Gal}(f)| = [L:K]$. If $f$ is not separable, the group is still defined, but it can be smaller than the degree.

::: mathlib
`Polynomial.Gal` · `Mathlib.FieldTheory.PolynomialGaloisGroup`

`p.Gal` is the type `p.SplittingField ≃ₐ[F] p.SplittingField`, with a group structure and a `Fintype` instance. The theorem `Polynomial.Gal.card_of_separable` gives `Nat.card p.Gal = finrank F p.SplittingField` for a separable `p`. For the polynomial `X ^ n`, the instance `Polynomial.Gal.uniqueGalXPow` says that the group is trivial.

<?decl Polynomial.Gal?>
:::

**Definition (Action on the roots).** Let $R \subseteq L$ be the set of the distinct roots of $f$ in $L$. Each $\sigma \in \operatorname{Gal}(f)$ maps $R$ into $R$, since $f(\sigma(\alpha)) = \sigma(f(\alpha)) = 0$. So $\sigma|_R$ is a permutation of the finite set $R$, and this gives a homomorphism $\rho : \operatorname{Gal}(f) \to \operatorname{Sym}(R)$.

**Theorem (The action is faithful).** The homomorphism $\rho$ is injective.

*Proof.* If $\sigma$ fixes each root, it fixes $K(R) = L$, so $\sigma = 1$. $\square$

So $|\operatorname{Gal}(f)|$ divides $|R|!$, and $[L : K] \leq n!$ for a separable $f$ of degree $n$.

::: mathlib
`Polynomial.Gal.galActionHom` · `Mathlib.FieldTheory.PolynomialGaloisGroup`

`galActionHom p E : p.Gal →* Equiv.Perm (p.rootSet E)` is the action on the roots in any field `E` over which `p` splits, given as an instance `[Fact ((p.map (algebraMap F E)).Splits)]`. For $F = \mathbb{Q}$ the field `E` can be $\mathbb{C}$. The underlying action is `Polynomial.Gal.galAction`, and faithfulness is `Polynomial.Gal.galActionHom_injective`. The bijection `Polynomial.Gal.mapRoots_bijective` identifies the roots in `E` with those in the splitting field.

<?decl Polynomial.Gal.galActionHom?>
:::

### Theorems and proofs

**Theorem (Transitivity).** Let $f \in K[X]$ be separable of degree $n \geq 1$. Then $\operatorname{Gal}(f)$ acts transitively on the roots of $f$ if and only if $f$ is irreducible.

*Proof.* Suppose $f$ is irreducible, and let $\alpha, \beta \in R$. Up to a constant, $f$ is the minimal polynomial of both. The splitting field $L$ is normal over $K$, so by the theorem on conjugates (Chapter 5, Section 1) there is $\sigma \in \operatorname{Gal}(f)$ with $\sigma(\alpha) = \beta$.

Suppose $f = gh$ with $g, h$ of positive degree. Since $f$ is separable, $g$ and $h$ have no common root. Let $\alpha$ be a root of $g$ and $\beta$ a root of $h$. Each $\sigma \in \operatorname{Gal}(f)$ maps $\alpha$ to a root of $g$, which is not $\beta$. So the action is not transitive. $\square$

::: mathlib
`Polynomial.Gal.galAction_isPretransitive` · `Mathlib.FieldTheory.PolynomialGaloisGroup`

The statement `Irreducible p → MulAction.IsPretransitive p.Gal (p.rootSet E)`. Mathlib needs only irreducibility for this direction. In the class name, "pretransitive" means transitive without the condition that the set is nonempty.

<?decl Polynomial.Gal.galAction_isPretransitive?>
:::

**Corollary (Degree divides the order).** If $f$ is irreducible and separable of degree $n$, then $n$ divides $|\operatorname{Gal}(f)|$.

*Proof.* The orbit of a root has $n$ elements, and the size of an orbit divides the order of the group (Volume 5, Chapter 6). Equivalently, $[K(\alpha):K] = n$ divides $[L:K]$. $\square$

Mathlib has the case of a prime degree in characteristic $0$ as `Polynomial.Gal.prime_degree_dvd_card`. It is the first step of the criterion of Section 2.

**Theorem (Factors).** Let $g$ divide $f$. Then the splitting field $L_g$ of $g$ lies in the splitting field $L_f$ of $f$, and restriction gives a surjective homomorphism $\operatorname{Gal}(f) \to \operatorname{Gal}(g)$. For two polynomials $g, h$, restriction gives an injective homomorphism $\operatorname{Gal}(gh) \to \operatorname{Gal}(g) \times \operatorname{Gal}(h)$.

*Proof.* The roots of $g$ generate a subfield $L_g$ of $L_f$, normal over $K$, so restriction is defined and surjective by Chapter 5, Section 1. For the product, an automorphism of $L_{gh}$ that is the identity on the roots of $g$ and on the roots of $h$ fixes all the roots of $gh$, so it is the identity. $\square$

The image in the product is in general a proper subgroup. For $g = X^2 - 2$ and $h = X^2 - 8$, both groups have order $2$, but $\sqrt 8 = 2\sqrt 2$, so $\operatorname{Gal}(gh)$ has order $2$, the diagonal.

::: mathlib
`Polynomial.Gal.restrict` · `Mathlib.FieldTheory.PolynomialGaloisGroup`

`Polynomial.Gal.restrict p E` restricts the automorphisms of a normal extension `E` in which `p` splits to `p.Gal`, and `Polynomial.Gal.restrict_surjective` is its surjectivity. The product map is `Polynomial.Gal.restrictProd`, injective by `Polynomial.Gal.restrictProd_injective`.

<?decl Polynomial.Gal.restrict?>
:::

**Definition (Discriminant).** Let $f \in K[X]$ have degree $n$, leading coefficient $a$, and roots $\alpha_1, \dots, \alpha_n$ in a splitting field, listed with multiplicity. Put
$$\delta = \prod_{i < j} (\alpha_i - \alpha_j), \qquad \Delta(f) = a^{2n-2} \delta^2 = a^{2n-2} \prod_{i<j} (\alpha_i - \alpha_j)^2.$$
The number $\Delta(f)$ is the discriminant of $f$. It is zero if and only if $f$ has a repeated root.

The factor $a^{2n-2}$ makes $\Delta(f)$ a polynomial in the coefficients of $f$ with integer coefficients. For $n = 2$ and $f = aX^2 + bX + c$, the formula gives $\Delta = a^2 (\alpha_1 - \alpha_2)^2 = b^2 - 4ac$.

**Theorem (Sign of the discriminant root).** Let $f$ be separable of degree $n$, and number its roots $\alpha_1, \dots, \alpha_n$. For $\sigma \in \operatorname{Gal}(f)$, viewed as a permutation of $\{1, \dots, n\}$, $\sigma(\delta) = \operatorname{sgn}(\sigma)\, \delta$. So $\Delta(f) \in K$.

*Proof.* The automorphism $\sigma$ maps $\prod_{i<j} (\alpha_i - \alpha_j)$ to $\prod_{i<j} (\alpha_{\sigma(i)} - \alpha_{\sigma(j)})$. Each pair occurs once, with the sign $-1$ exactly when $\sigma$ reverses its order, so the new product is $\operatorname{sgn}(\sigma)\, \delta$ (Volume 5, Chapter 7). Then $\sigma(\delta^2) = \delta^2$ for all $\sigma$, and $\Delta(f) = a^{2n-2}\delta^2$ is in the fixed field of $\operatorname{Gal}(f)$, which is $K$ (Chapter 5, Section 2). $\square$

**Corollary (The alternating group).** Let $K$ have characteristic other than $2$ and let $f \in K[X]$ be separable. Then $\operatorname{Gal}(f) \subseteq A_n$ if and only if $\Delta(f)$ is a square in $K$.

*Proof.* Since $f$ is separable, $\delta \neq 0$, and since the characteristic is not $2$, $-\delta \neq \delta$. So $\sigma(\delta) = \delta$ if and only if $\operatorname{sgn}(\sigma) = 1$. Hence $\operatorname{Gal}(f) \subseteq A_n$ if and only if each $\sigma$ fixes $\delta$, if and only if $\delta \in K$. If $\delta \in K$, then $\Delta(f) = (a^{n-1}\delta)^2$ is a square in $K$. Conversely, if $\Delta(f) = c^2$ with $c \in K$, then $a^{n-1}\delta = \pm c$, so $\delta \in K$. $\square$

By the fundamental theorem, the fixed field of $\operatorname{Gal}(f) \cap A_n$ is $K(\delta) = K(\sqrt{\Delta(f)})$.

**Theorem (Cubics).** Let $f = X^3 + pX + q$ with $p, q \in K$. Then $\Delta(f) = -4p^3 - 27q^2$. If $f$ is irreducible and separable, then $\operatorname{Gal}(f) \cong A_3$, cyclic of order $3$, if $\Delta(f)$ is a square in $K$, and $\operatorname{Gal}(f) \cong S_3$ otherwise, when the characteristic is not $2$.

*Proof.* For a monic $f$ of degree $n$ with roots $\alpha_i$, the derivative satisfies $f'(\alpha_i) = \prod_{j \neq i} (\alpha_i - \alpha_j)$, by the product rule applied to $f = \prod_j (X - \alpha_j)$. Each pair $i < j$ appears twice in $\prod_i f'(\alpha_i)$, once as $\alpha_i - \alpha_j$ and once as $\alpha_j - \alpha_i$. So $\prod_i f'(\alpha_i) = (-1)^{n(n-1)/2} \Delta(f)$. For $n = 3$ the sign is $-1$.

Now $f' = 3X^2 + p$. Both sides of the claimed formula are polynomials in $p$ and $q$ with integer coefficients (Exercise 4), so it suffices to prove it when $p \neq 0$ and $q \neq 0$, over the field $\mathbb{Q}(p, q)$ of rational functions. From $\alpha^3 = -p\alpha - q$ for a root $\alpha$:
$$f'(\alpha) = \frac{3\alpha^3 + p\alpha}{\alpha} = \frac{-2p\alpha - 3q}{\alpha}.$$
The product of the roots is $\alpha_1\alpha_2\alpha_3 = -q$. Put $y = 3q/(2p)$. Since $\prod_i (X - \alpha_i) = f$, the product $\prod_i (\alpha_i + y) = -f(-y) = y^3 + py - q$. So
$$\prod_i (-2p\alpha_i - 3q) = (-2p)^3 \prod_i (\alpha_i + y) = -8p^3 \Big(\frac{27q^3}{8p^3} + \frac{3q}{2} - q\Big) = -27q^3 - 4p^3 q.$$
Divide by $\prod_i \alpha_i = -q$: $\prod_i f'(\alpha_i) = 27q^2 + 4p^3$. So $\Delta(f) = -4p^3 - 27q^2$.

If $f$ is irreducible and separable, $\operatorname{Gal}(f)$ is a subgroup of $S_3$ whose order is divisible by $3$, by the corollary on the degree. So it is $A_3$ or $S_3$, and the previous corollary decides between them. $\square$

A general cubic $aX^3 + bX^2 + cX + d$ becomes $X^3 + pX + q$ after division by $a$ and the substitution $X \mapsto X - b/(3a)$, in characteristic other than $3$. The roots shift by the same amount, so their differences, and $\delta$, do not change. The result is the general formula
$$\Delta = b^2c^2 - 4ac^3 - 4b^3d - 27a^2d^2 + 18abcd.$$

::: mathlib
`Cubic` · `Mathlib.Algebra.CubicDiscriminant`

A structure with four fields `a b c d : R`, standing for $aX^3 + bX^2 + cX + d$. The polynomial itself is `Cubic.toPoly P`. The leading coefficient may be zero.

<?decl Cubic?>
:::

::: mathlib
`Cubic.discr` · `Mathlib.Algebra.CubicDiscriminant`

`P.discr` is the polynomial expression in `a b c d` above. The theorem `Cubic.discr_eq_prod_three_roots` proves that it equals $(a^2 (x - y)(x - z)(y - z))^2$ when the roots after a map `φ` are `{x, y, z}`; this is the definition of $\Delta$ with $a^{2n-2} = a^4$. The theorem `Cubic.discr_ne_zero_iff_roots_nodup` says that the discriminant is not zero if and only if the roots are distinct.

<?decl Cubic.discr?>
:::

### Examples

**Example (Two cubics).** The polynomial $f = X^3 - 3X + 1$ has no rational root, since $f(1) = -1$ and $f(-1) = 3$, so it is irreducible over $\mathbb{Q}$. Its discriminant is $-4(-3)^3 - 27 \cdot 1^2 = 108 - 27 = 81 = 9^2$. So $\operatorname{Gal}(f) \cong A_3$, the splitting field has degree $3$, and it is generated by any one root. The roots are $2\cos(2\pi k/9)$ for $k = 1, 2, 4$. The polynomial $g = X^3 - 2$ has $\Delta(g) = -27 \cdot 4 = -108$, which is not a square in $\mathbb{Q}$. So $\operatorname{Gal}(g) \cong S_3$, as computed by hand in Chapter 5, Section 3, and $\mathbb{Q}(\sqrt{-108}) = \mathbb{Q}(\sqrt{-3}) = \mathbb{Q}(\omega)$ is the fixed field of $A_3$.

**Example (Transitivity needs a separable polynomial).** The polynomial $f = (X^2 - 2)^2$ is reducible. Its roots are $\pm\sqrt 2$, and $\operatorname{Gal}(f) = \operatorname{Gal}(\mathbb{Q}(\sqrt 2)/\mathbb{Q})$ swaps them. So the group acts transitively on the roots of a reducible polynomial. So the direction "transitive implies irreducible" needs $f$ separable.

**Example (The discriminant in characteristic $2$).** Over $K = \mathbb{F}_2$, let $f = X^2 + X + 1$, irreducible with group $S_2$ of order $2$. Its discriminant is $b^2 - 4ac = 1$, a square. But $S_2 \not\subseteq A_2 = 1$. The proof fails because $-\delta = \delta$ in characteristic $2$. So the hypothesis on the characteristic in the corollary is needed.

### The library around it

The file `Mathlib.FieldTheory.PolynomialGaloisGroup` defines `Polynomial.Gal`, its action on the roots in any splitting extension, and the restriction maps for divisors, products and compositions. The file `Mathlib.Algebra.CubicDiscriminant` defines the structure `Cubic`, its roots `Cubic.roots`, the splitting criteria such as `Cubic.splits_iff_roots_eq_three`, and the discriminant. The general discriminant `Polynomial.discr`, defined through the resultant, is in `Mathlib.RingTheory.Polynomial.Resultant.Basic`. The reference table lists the declarations of the section.

### Exercises

1. (A) Find the Galois group of $X^3 - 7X + 7$ over $\mathbb{Q}$. Hint: it is irreducible by Eisenstein, and $\Delta = -4(-7)^3 - 27 \cdot 49 = 49$.
2. (A) Find the Galois group of $X^3 + X + 1$ over $\mathbb{Q}$ and over $\mathbb{F}_5$.
3. (A) Show that the discriminant of $X^2 + bX + c$ is $b^2 - 4c$ from the definition.
4. (B) Show that $\Delta(f)$ is a polynomial in the coefficients of $f$ with integer coefficients. Hint: it is symmetric in the roots; use the theorem on symmetric polynomials.
5. (B) Let $f \in \mathbb{R}[X]$ be a separable cubic. Show that $\Delta(f) > 0$ if and only if $f$ has three real roots.
6. (B) Let $f = X^n - 1$ over $\mathbb{Q}$. Show that $\Delta(f) = (-1)^{(n-1)(n-2)/2} n^n$. Hint: use $\prod_i f'(\zeta_i) = \prod_i n\zeta_i^{n-1}$.
7. (C) Let $K$ have characteristic $3$ and $f = X^3 - X - t$ over $K = \mathbb{F}_3(t)$. Show that $\Delta(f) = 4 = 1$, a square, and that $\operatorname{Gal}(f)$ is cyclic of order $3$. Hint: if $\alpha$ is a root, so is $\alpha + 1$.

### Notes and history

Lagrange in 1770 studied the effect of permutations of the roots on rational functions of the roots, and this is the origin of the group of a polynomial. Galois defined the group of an equation as a group of permutations of the roots, the approach of this section. Sylvester and Cayley studied the discriminant and the resultant in the nineteenth century.

### Reference

<?reference?>
