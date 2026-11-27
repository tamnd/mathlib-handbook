---
title: Roots of unity, cyclotomic and Kummer extensions
kind: theory
modules:
  - Mathlib.RingTheory.RootsOfUnity.Basic
  - Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
  - Mathlib.RingTheory.RootsOfUnity.Minpoly
  - Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
  - Mathlib.FieldTheory.KummerPolynomial
  - Mathlib.FieldTheory.KummerExtension
explains:
  E3: [rootsOfUnity, IsPrimitiveRoot, IsPrimitiveRoot.autToPow, IsPrimitiveRoot.totient_le_degree_minpoly, irreducible_X_pow_sub_C_of_prime, autEquivRootsOfUnity, exists_root_adjoin_eq_top_of_isCyclic]
  E2: [rootsOfUnity.isCyclic, card_rootsOfUnity, IsPrimitiveRoot.card_rootsOfUnity, primitiveRoots, IsPrimitiveRoot.card_primitiveRoots, IsPrimitiveRoot.pow_of_coprime, IsPrimitiveRoot.isPrimitiveRoot_iff, IsPrimitiveRoot.zmodEquivZPowers, HasEnoughRootsOfUnity, isCyclic_of_isSplittingField_X_pow_sub_C, finrank_of_isSplittingField_X_pow_sub_C, isGalois_of_isSplittingField_X_pow_sub_C, irreducible_X_pow_sub_C_iff_of_prime_pow_of_ne_two]
  E1: auto
families: []
requires: [V11.C05, V11.C06, V11.C07, V06.C05]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Roots of unity, cyclotomic and Kummer extensions

### Overview

The $n$th roots of unity in a field form a finite cyclic group. Adjoining a primitive $n$th root of unity to $K$ gives a Galois extension whose group embeds into $(\mathbb{Z}/n\mathbb{Z})^\times$, so it is abelian. Over $\mathbb{Q}$ the embedding is an isomorphism, because the cyclotomic polynomial $\Phi_n$ is irreducible. When $K$ already contains the $n$th roots of unity, the extensions $K(\sqrt[n]{a})$ are exactly the cyclic extensions of degree dividing $n$. This is Kummer theory. The two kinds of extensions are the steps of a solution by radicals (Section 2).

The section uses the theorem that a finite subgroup of the units of a domain is cyclic (Volume 6, Chapter 5), the fundamental theorem (Chapter 5), the theorem of Dedekind on the independence of characters (Chapter 5, Section 2) and finite fields (Chapter 7).

### Definitions

**Definition (Roots of unity).** Let $K$ be a field and $n \geq 1$. The group of $n$th roots of unity is $\mu_n(K) = \{\zeta \in K^\times : \zeta^n = 1\}$. An element $\zeta$ is a primitive $n$th root of unity if $\zeta^n = 1$ and $\zeta^m \neq 1$ for $0 < m < n$, that is, if $\zeta$ has order exactly $n$ in $K^\times$.

::: mathlib
`rootsOfUnity` · `Mathlib.RingTheory.RootsOfUnity.Basic`

`rootsOfUnity n M` is the subgroup of the units `Mˣ` of a commutative monoid with `m ^ n = 1`. Its elements are units, so a coercion is needed. For a domain `R`, `card_rootsOfUnity` gives at most `n` elements, and the instance `rootsOfUnity.isCyclic` says that the group is cyclic. For `n = 0`, the junk value is the trivial group.

<?decl rootsOfUnity?>
:::

::: mathlib
`IsPrimitiveRoot` · `Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots`

`IsPrimitiveRoot ζ k` is a structure on an element of a commutative monoid: `ζ ^ k = 1`, and `ζ ^ l = 1` implies `k ∣ l`. The finset of them in a domain is `primitiveRoots k R`. `IsPrimitiveRoot.card_rootsOfUnity` says that one primitive root makes the group of order exactly `n`, `IsPrimitiveRoot.card_primitiveRoots` counts `φ(k)` primitive roots, and `IsPrimitiveRoot.isPrimitiveRoot_iff` and `IsPrimitiveRoot.pow_of_coprime` describe them as the powers `ζ ^ i` with `i` coprime to `k`. The class `HasEnoughRootsOfUnity M n` packs the hypothesis that `M` has a primitive `n`th root of unity.

<?decl IsPrimitiveRoot?>
:::

**Definition (Cyclotomic polynomial and extension).** The $n$th cyclotomic polynomial is $\Phi_n = \prod (X - \zeta)$, the product over the primitive $n$th roots of unity $\zeta \in \mathbb{C}$. A cyclotomic extension of $K$ of level $n$ is a splitting field of $X^n - 1$ over $K$.

From $X^n - 1 = \prod_{d \mid n} \Phi_d$ and induction on $n$, the division algorithm for monic polynomials shows that $\Phi_n$ has integer coefficients. Its degree is $\varphi(n)$, the Euler function.

::: mathlib
`Polynomial.cyclotomic` · `Mathlib.RingTheory.Polynomial.Cyclotomic.Basic`

`Polynomial.cyclotomic n R` is defined over each ring by mapping the integer polynomial. The product formula is `Polynomial.prod_cyclotomic_eq_X_pow_sub_one`. The class `IsCyclotomicExtension S A B` in `Mathlib.NumberTheory.Cyclotomic.Basic` says that `B` is generated over `A` by primitive `n`th roots of unity for `n ∈ S`.

<?decl Polynomial.cyclotomic?>
<?decl IsCyclotomicExtension?>
:::

### Theorems and proofs

**Theorem (Roots of unity).** Let $K$ be a field and $n \geq 1$. Then $\mu_n(K)$ is cyclic of order dividing $n$. If $\operatorname{char} K \nmid n$, then $X^n - 1$ is separable, and in a splitting field of $X^n - 1$ the group $\mu_n$ has order $n$, with $\varphi(n)$ generators, the primitive $n$th roots of unity.

*Proof.* $\mu_n(K)$ is a finite subgroup of $K^\times$, so it is cyclic (Volume 6, Chapter 5), and its generator has order dividing $n$. If $\operatorname{char} K \nmid n$, then the derivative $nX^{n-1}$ is coprime to $X^n - 1$, so $X^n - 1$ has $n$ distinct roots in a splitting field. A cyclic group of order $n$ has $\varphi(n)$ generators. $\square$

**Theorem (The Galois group of a cyclotomic extension).** Let $\zeta$ be a primitive $n$th root of unity in an extension of $K$. Then $K(\zeta)/K$ is Galois, and the map $\chi : \operatorname{Gal}(K(\zeta)/K) \to (\mathbb{Z}/n\mathbb{Z})^\times$, with $\sigma(\zeta) = \zeta^{\chi(\sigma)}$, is an injective group homomorphism. In particular $\operatorname{Gal}(K(\zeta)/K)$ is abelian and $[K(\zeta):K]$ divides $\varphi(n)$.

*Proof.* The powers $\zeta^i$, $0 \leq i < n$, are $n$ distinct roots of $X^n - 1$, so they are all its roots, it splits in $K(\zeta)$ and it is separable. So $K(\zeta)$ is the splitting field of a separable polynomial, and it is Galois (Chapter 5, Section 2). An automorphism $\sigma$ maps $\zeta$ to an element of the same order $n$, so $\sigma(\zeta) = \zeta^a$ with $a$ coprime to $n$, and $a$ is unique modulo $n$. Then $\sigma\tau(\zeta) = \sigma(\zeta^b) = \zeta^{ab}$, so $\chi$ is a homomorphism. It is injective since $\sigma$ is determined by $\sigma(\zeta)$. $\square$

::: mathlib
`IsPrimitiveRoot.autToPow` · `Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots`

For `hμ : IsPrimitiveRoot μ n` in a domain `S` over `R`, the monoid homomorphism `hμ.autToPow R : (S ≃ₐ[R] S) →* (ZMod n)ˣ`. It does not depend on the choice of `μ`. The isomorphism `IsPrimitiveRoot.zmodEquivZPowers` identifies the powers of `μ` with `ZMod n`. The injectivity over a cyclotomic extension, and the isomorphism `IsCyclotomicExtension.autEquivPow` over $\mathbb{Q}$, are in `Mathlib.NumberTheory.Cyclotomic.Gal`.

<?decl IsPrimitiveRoot.autToPow?>
<?decl IsCyclotomicExtension.autEquivPow?>
:::

**Theorem (Irreducibility of $\Phi_n$ over $\mathbb{Q}$).** For each $n \geq 1$, $\Phi_n$ is irreducible in $\mathbb{Q}[X]$. So $[\mathbb{Q}(\zeta_n) : \mathbb{Q}] = \varphi(n)$ and $\operatorname{Gal}(\mathbb{Q}(\zeta_n)/\mathbb{Q}) \cong (\mathbb{Z}/n\mathbb{Z})^\times$.

*Proof.* Let $\zeta$ be a primitive $n$th root of unity in $\mathbb{C}$ and $f$ its minimal polynomial over $\mathbb{Q}$. Then $f$ divides $\Phi_n$, and by the lemma of Gauss $f \in \mathbb{Z}[X]$ and $\Phi_n = fg$ with $g \in \mathbb{Z}[X]$ monic. The main step: for each prime $p \nmid n$ and each root $\xi$ of $f$, $\xi^p$ is a root of $f$.

Suppose not. Then $\xi^p$ is a primitive $n$th root of unity, so a root of $g$, and $\xi$ is a root of $g(X^p)$. Since $f$ is the minimal polynomial of $\xi$, $f \mid g(X^p)$ in $\mathbb{Q}[X]$, and by Gauss in $\mathbb{Z}[X]$. Reduce modulo $p$, with bars. In $\mathbb{F}_p[X]$, $\bar g(X^p) = \bar g(X)^p$, because the Frobenius fixes the coefficients (Chapter 7). So $\bar f \mid \bar g^p$, and an irreducible factor $h$ of $\bar f$ divides $\bar g$. Then $h^2$ divides $\bar f \bar g = \bar\Phi_n$, which divides $X^n - 1$. But $X^n - 1$ is separable over $\mathbb{F}_p$ since $p \nmid n$, a contradiction.

Each primitive $n$th root of unity is $\zeta^a$ with $a$ coprime to $n$, and $a$ is a product of primes not dividing $n$. Applying the main step once for each prime factor shows that $\zeta^a$ is a root of $f$. So $f$ has all the $\varphi(n)$ roots of $\Phi_n$, and $f = \Phi_n$. The degree is $\varphi(n)$, and the injective map $\chi$ of the previous theorem is between groups of order $\varphi(n)$. $\square$

::: mathlib
`IsPrimitiveRoot.totient_le_degree_minpoly` · `Mathlib.RingTheory.RootsOfUnity.Minpoly`

For `h : IsPrimitiveRoot μ n` in a domain of characteristic zero, `n.totient ≤ (minpoly ℤ μ).natDegree`. This is the main step of the proof above, done over `ℤ`. The file `Mathlib.RingTheory.Polynomial.Cyclotomic.Roots` deduces `Polynomial.cyclotomic.irreducible_rat` and `Polynomial.cyclotomic_eq_minpoly_rat`.

<?decl IsPrimitiveRoot.totient_le_degree_minpoly?>
<?decl Polynomial.cyclotomic.irreducible_rat?>
:::

**Theorem (Irreducibility of $X^p - a$).** Let $p$ be a prime, $K$ a field and $a \in K$ not a $p$th power in $K$. Then $X^p - a$ is irreducible over $K$.

*Proof.* Let $\alpha$ be a root in a splitting field. Then $\alpha^p = a$ and $X^p - a = \prod_{i} (X - \omega_i \alpha)$ with $\omega_i^p = 1$. Suppose $X^p - a = gh$ with $g$ monic of degree $d$, $0 < d < p$. Here $a \neq 0$, since $0$ is a $p$th power. The constant term of $g$ is $c = (-1)^d \omega \alpha^d$ for a product $\omega$ of some $\omega_i$, so $c \neq 0$ and $c^p = (-1)^{dp} a^d$. Since $\gcd(d, p) = 1$, $ud + vp = 1$ for some integers $u, v$. Then $a = a^{ud} a^{vp} = ((-1)^{du} c^u a^v)^p$, and $a$ is a $p$th power in $K$, a contradiction. $\square$

::: mathlib
`irreducible_X_pow_sub_C_of_prime` · `Mathlib.FieldTheory.KummerPolynomial`

For `Nat.Prime p` and `∀ b, b ^ p ≠ a`, the statement `Irreducible (X ^ p - C a)`. For prime powers the test is `irreducible_X_pow_sub_C_iff_of_prime_pow_of_ne_two`, which needs `p ≠ 2`; the example below shows why.

<?decl irreducible_X_pow_sub_C_of_prime?>
:::

**Theorem (Kummer).** Let $K$ contain a primitive $n$th root of unity $\zeta$.

1. If $X^n - a$ is irreducible over $K$ and $L = K(\alpha)$ with $\alpha^n = a$, then $L/K$ is Galois and $\sigma \mapsto \sigma(\alpha)/\alpha$ is an isomorphism $\operatorname{Gal}(L/K) \cong \mu_n(K)$. In particular $\operatorname{Gal}(L/K)$ is cyclic of order $n$.
2. Conversely, if $L/K$ is Galois with cyclic group of order $n$, then $L = K(\beta)$ for some $\beta$ with $\beta^n \in K$.

*Proof.* (1) The $n$ distinct roots $\zeta^i \alpha$ of $X^n - a$ lie in $L$, so $L/K$ is Galois of degree $n$, and $\sigma(\alpha)/\alpha \in \mu_n(K)$. Since $\tau(\alpha)/\alpha \in K$ is fixed by $\sigma$, $\sigma\tau(\alpha)/\alpha = (\tau(\alpha)/\alpha)(\sigma(\alpha)/\alpha)$, so the map is a homomorphism. It is injective, and both groups have order $n$.

(2) Let $\sigma$ generate $\operatorname{Gal}(L/K)$. For $x \in L$, form the Lagrange resolvent $b(x) = \sum_{i=0}^{n-1} \zeta^{-i} \sigma^i(x)$. By Dedekind, $1, \sigma, \dots, \sigma^{n-1}$ are linearly independent over $L$, so $\beta = b(x) \neq 0$ for some $x$. Since $\sigma(\zeta) = \zeta$, $\sigma(\beta) = \sum \zeta^{-i} \sigma^{i+1}(x) = \zeta \beta$. So $\sigma(\beta^n) = \beta^n$ and $\beta^n \in K$ by the fundamental theorem. The elements $\sigma^i(\beta) = \zeta^i \beta$ are $n$ distinct conjugates of $\beta$, so $[K(\beta):K] \geq n = [L:K]$, and $L = K(\beta)$. $\square$

::: mathlib
`autEquivRootsOfUnity` · `Mathlib.FieldTheory.KummerExtension`

For `(primitiveRoots n K).Nonempty`, `Irreducible (X ^ n - C a)` and a splitting field `L`, the isomorphism `Gal(L/K) ≃* rootsOfUnity n K`. It does not depend on a choice of the root. The related results are `isGalois_of_isSplittingField_X_pow_sub_C`, `finrank_of_isSplittingField_X_pow_sub_C` and `isCyclic_of_isSplittingField_X_pow_sub_C`.

<?decl autEquivRootsOfUnity?>
:::

::: mathlib
`exists_root_adjoin_eq_top_of_isCyclic` · `Mathlib.FieldTheory.KummerExtension`

For a finite Galois `L/K` with cyclic group and `(primitiveRoots (finrank K L) K).Nonempty`, there is `α : L` with `α ^ finrank K L ∈ range (algebraMap K L)` and `K⟮α⟯ = ⊤`. The proof uses the linear independence of characters `linearIndependent_monoidHom`.

<?decl exists_root_adjoin_eq_top_of_isCyclic?>
<?decl linearIndependent_monoidHom?>
:::

### Examples

**Example (The eighth roots of unity).** Let $\zeta = e^{2\pi i/8} = (1+i)/\sqrt{2}$. Then $\Phi_8 = X^4 + 1$, and $\mathbb{Q}(\zeta) = \mathbb{Q}(i, \sqrt{2})$, since $\zeta^2 = i$ and $\zeta + \zeta^{-1} = \sqrt{2}$. The group $(\mathbb{Z}/8\mathbb{Z})^\times = \{1, 3, 5, 7\}$ has each element of order $2$, so it is the Klein four group, not cyclic. The automorphism $\zeta \mapsto \zeta^7 = \bar\zeta$ is complex conjugation, which fixes $\sqrt{2}$; $\zeta \mapsto \zeta^5 = -\zeta$ fixes $i$; $\zeta \mapsto \zeta^3$ fixes $i\sqrt{2} = \zeta + \zeta^3$.

**Example (Irreducibility needs the right base field).** Modulo each prime $p$, $X^4 + 1$ is reducible. For $p = 2$, $X^4 + 1 = (X + 1)^4$. For $p$ odd, the group of units of $\mathbb{F}_{p^2}$ has $p^2 - 1 \equiv 0 \pmod 8$ elements, so it contains a primitive eighth root of unity, whose minimal polynomial over $\mathbb{F}_p$ has degree at most $2$. So the irreducibility of $\Phi_n$ is a fact about $\mathbb{Q}$.

**Example (The hypotheses of the prime power test).** The number $-4$ is not a square in $\mathbb{Q}$, but $X^4 + 4 = (X^2 + 2X + 2)(X^2 - 2X + 2)$. So for $p = 2$ the condition that $a$ is not a $p$th power does not give the irreducibility of $X^{p^n} - a$; the full test also excludes $a = -4b^4$. And without the roots of unity in $K$, Kummer's theorem fails: the splitting field of $X^3 - 2$ over $\mathbb{Q}$ has the group $S_3$, which is not cyclic, and $\mathbb{Q}(\sqrt[3]{2})/\mathbb{Q}$ is not even normal.

### The library around it

The folder `Mathlib.RingTheory.RootsOfUnity` holds the general theory, with the explicit complex roots in `Complex`. The cyclotomic polynomials are in `Mathlib.RingTheory.Polynomial.Cyclotomic`, and the cyclotomic fields and their rings of integers in `Mathlib.NumberTheory.Cyclotomic`. The reference table lists the declarations of the section.

### Exercises

1. (A) Compute $\Phi_n$ for $n \leq 12$ from $X^n - 1 = \prod_{d \mid n} \Phi_d$, and check that $\Phi_p = X^{p-1} + \dots + X + 1$ for $p$ prime.
2. (A) Show that the group of roots of unity of $\mathbb{Q}(i)$ has order $4$, and that $\mathbb{Q}(\zeta_3)$ has six roots of unity.
3. (A) List the subfields of $\mathbb{Q}(\zeta_5)$, and show that $\mathbb{Q}(\sqrt 5)$ is one of them. *Hint:* $(\mathbb{Z}/5\mathbb{Z})^\times$ is cyclic of order $4$; compute $(\zeta + \zeta^4)^2$.
4. (B) Let $p$ be an odd prime. Show that $\mathbb{Q}(\zeta_p)$ contains exactly one quadratic field, and that it is $\mathbb{Q}(\sqrt{\pm p})$ with the sign $(-1)^{(p-1)/2}$. *Hint:* the discriminant of $\Phi_p$.
5. (B) Show that $\operatorname{Gal}(\mathbb{F}_q(\zeta_n)/\mathbb{F}_q)$, for $\gcd(q, n) = 1$, is the cyclic subgroup of $(\mathbb{Z}/n\mathbb{Z})^\times$ generated by $q$. Deduce that $\Phi_n$ is irreducible over $\mathbb{F}_p$ if and only if $p$ generates $(\mathbb{Z}/n\mathbb{Z})^\times$.
6. (C) Show that each finite abelian group is the Galois group of some extension of $\mathbb{Q}$. *Hint:* use primes $p \equiv 1 \pmod m$, the existence of which is a special case of the theorem of Dirichlet that has an elementary proof with $\Phi_m$.

### Notes and history

Gauss proved the irreducibility of $\Phi_p$ in the Disquisitiones Arithmeticae (1801) and deduced the construction of the regular $17$-gon. The irreducibility of $\Phi_n$ for all $n$ was proved by Kronecker in 1854; the proof by reduction modulo $p$ is due to Dedekind (1857). Kummer used the extensions $\mathbb{Q}(\zeta_p, \sqrt[p]{a})$ in his work on Fermat's last theorem, and Hilbert set out Kummer theory in his Zahlbericht of 1897.

### Reference

<?reference?>
