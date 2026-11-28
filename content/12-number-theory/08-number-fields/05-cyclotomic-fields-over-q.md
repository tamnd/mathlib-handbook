---
title: Cyclotomic fields over Q
kind: api
modules:
  - Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
  - Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
  - Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
  - Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
  - Mathlib.NumberTheory.NumberField.Cyclotomic.Three
explains:
  E2: [IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton, IsCyclotomicExtension.Rat.discr, IsCyclotomicExtension.Rat.torsionOrder_eq, IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero, IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq, IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime, IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_prime, IsCyclotomicExtension.Rat.Three.Units.mem, IsCyclotomicExtension.Rat.Three.lambda_pow_four_dvd_cube_sub_one_of_dvd_sub_one]
  E1: auto
families: []
requires: [V11.C08, V12.C06, V07.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Cyclotomic fields over Q

### Overview

The $n$-th cyclotomic field $\mathbb{Q}(\zeta_n)$ is the field that $\mathbb{Q}$ generates with a primitive $n$-th root of unity $\zeta_n$. It is the first family of number fields where every invariant of Sections 1 and 2 has a closed form: the degree is $\varphi(n)$, the ring of integers is $\mathbb{Z}[\zeta_n]$, the discriminant is an explicit product of primes that divide $n$, the Galois group is $(\mathbb{Z}/n\mathbb{Z})^\times$, and the factorization of a prime $p$ depends only on $p$ modulo $n$. The case $n = 3$ is an input of the proof of Fermat's last theorem for the exponent $3$ (Chapter 4, Section 1).

The general theory of cyclotomic extensions $L/K$, with the predicate `IsCyclotomicExtension S K L` and the polynomials `Polynomial.cyclotomic n R`, is in Volume 11, Chapter 8. The modules of this section specialize it to the base field $\mathbb{Q}$, and their names are in the namespace `IsCyclotomicExtension.Rat` or in `IsPrimitiveRoot`. Section 2 has already used one of their results: the rings of integers of $\mathbb{Q}(\zeta_3)$, $\mathbb{Q}(\zeta_5)$ and $\mathbb{Q}(\zeta_7)$ are principal ideal domains.

### The library around it

#### The setting

A statement of this section has a number field `K` and the instance `[IsCyclotomicExtension {n} ℚ K]`: $K$ is generated over $\mathbb{Q}$ by the $n$-th roots of unity, and it has a primitive one. The concrete model is `CyclotomicField n ℚ`. Most results take a primitive root `ζ : K` with a proof `hζ : IsPrimitiveRoot ζ n` and then work with `hζ.toInteger`, the same element seen in the ring of integers `𝓞 K`. The lemma `IsPrimitiveRoot.coe_toInteger` gives back `ζ`, and `IsPrimitiveRoot.toInteger_isPrimitiveRoot` says that `hζ.toInteger` is still primitive. The degree is `IsCyclotomicExtension.Rat.finrank : finrank ℚ K = n.totient`, and the instance `IsCyclotomicExtension.ringOfIntegers` says that `𝓞 K` is a cyclotomic extension of `ℤ`.

#### The ring of integers

**Theorem.** $\mathcal{O}_K = \mathbb{Z}[\zeta_n]$. In Lean, `IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton` says that the subring `ℤ[ζ]` is the integral closure of `ℤ` in `K`, and `IsCyclotomicExtension.Rat.adjoin_singleton_eq_top` says `ℤ[hζ.toInteger] = ⊤`. For the concrete field, `IsCyclotomicExtension.Rat.cyclotomicRing_isIntegralClosure` says the same of `CyclotomicRing n ℤ ℚ`.

*About the proof.* The library first treats $n = p^k$. There $\pi = \zeta - 1$ satisfies an Eisenstein polynomial at $p$, so an element $x$ of $\mathcal{O}_K$ with $p x \in \mathbb{Z}[\zeta]$ is already in $\mathbb{Z}[\zeta]$. The discriminant of the basis $1, \zeta, \dots, \zeta^{\varphi(n) - 1}$ is $\pm$ a power of $p$, so $p^m\mathcal{O}_K \subseteq \mathbb{Z}[\zeta]$ for some $m$, and the first step gives equality. For general $n$ the field is a compositum of prime power cyclotomic fields with coprime discriminants, and the rings of integers combine.

The equality comes in three bundled forms. `IsPrimitiveRoot.adjoinEquivRingOfIntegers` is the $\mathbb{Z}$-algebra isomorphism `ℤ[ζ] ≃ₐ[ℤ] 𝓞 K`. `IsPrimitiveRoot.integralPowerBasis` is a power basis of `𝓞 K` over `ℤ` with generator `hζ.toInteger` (`IsPrimitiveRoot.integralPowerBasis_gen`) and dimension `n.totient` (`IsPrimitiveRoot.integralPowerBasis_dim`). `IsPrimitiveRoot.subOneIntegralPowerBasis` has the generator $\zeta - 1$ instead. Each of them has a form for prime powers with the suffix `OfPrimePow`, such as `IsPrimitiveRoot.integralPowerBasisOfPrimePow`, which needs fewer instances.

#### The discriminant

The discriminant of $K = \mathbb{Q}(\zeta_n)$ is
$$d_K = (-1)^{\varphi(n)/2}\,\frac{n^{\varphi(n)}}{\prod_{p \mid n} p^{\varphi(n)/(p - 1)}},$$
which is `IsCyclotomicExtension.Rat.discr`. Its absolute value is `IsCyclotomicExtension.Rat.natAbs_discr`. For $n = 4$: $\varphi(4) = 2$, so $d_K = -16/2^2 = -4$, the discriminant of $\mathbb{Q}(i)$. For $n = 3$: $d_K = -9/3 = -3$. The prime power cases are `IsCyclotomicExtension.Rat.discr_prime_pow`, `IsCyclotomicExtension.Rat.discr_prime_pow_succ` and `IsCyclotomicExtension.Rat.discr_prime`, with $d_K = (-1)^{(p-1)/2}p^{p-2}$ for $n = p$. The primed forms, such as `IsCyclotomicExtension.Rat.discr_odd_prime'`, compute `Algebra.discr` of the power basis of $\zeta - 1$ over $\mathbb{Q}$. Since only the primes that divide $n$ divide $d_K$, only these primes ramify in $K$.

#### The element zeta minus one

For $n = p^{k+1}$ the element $\zeta - 1$ is prime in $\mathcal{O}_K$: this is `IsPrimitiveRoot.zeta_sub_one_prime`, with `IsPrimitiveRoot.zeta_sub_one_prime'` for $n = p$ and `IsPrimitiveRoot.zeta_sub_one_prime_of_two_pow` for $n = 2^{k+1}$. Its norm is computed by a family of lemmas.

| Lean name | Statement |
|---|---|
| `IsPrimitiveRoot.norm_toInteger_sub_one_of_prime_ne_two` | $N(\zeta - 1) = p$ for $n = p^{k+1}$, $p \ne 2$ |
| `IsPrimitiveRoot.norm_toInteger_sub_one_of_eq_two` | $N(\zeta - 1) = -2$ for $n = 2$ |
| `IsPrimitiveRoot.norm_toInteger_sub_one_of_eq_two_pow` | $N(\zeta - 1) = 2$ for $n = 2^{k+2}$ |
| `IsPrimitiveRoot.norm_toInteger_sub_one_eq_one` | $N(\zeta - 1) = 1$ when $n > 2$ is not a prime power |
| `IsPrimitiveRoot.prime_dvd_of_dvd_norm_sub_one` | if $p \mid N(\zeta - 1)$, then $p \mid n$ |
| `IsPrimitiveRoot.card_quotient_toInteger_sub_one` | $|\mathcal{O}_K/(\zeta - 1)| = |N(\zeta - 1)|$ |

In the last case of the norm table, $\zeta - 1$ is a unit. Two more facts are used in the proofs on Fermat's equation. `IsPrimitiveRoot.toInteger_sub_one_dvd_prime` says that $\zeta - 1$ divides $p$, and `IsPrimitiveRoot.not_exists_int_prime_dvd_sub_of_prime_ne_two` says that for $p \ne 2$ no integer $m$ has $p \mid \zeta - m$ in $\mathcal{O}_K$.

#### Roots of unity and infinite places

**Proposition.** The group of roots of unity of $K = \mathbb{Q}(\zeta_n)$ has order $n$ if $n$ is even and $2n$ if $n$ is odd. This is `IsCyclotomicExtension.Rat.torsionOrder_eq`.

*Proof sketch.* If $n$ is odd, $-\zeta_n$ is a primitive $2n$-th root of unity, so it suffices to treat even $n$. Let $K$ contain a primitive $m$-th root of unity. Then $K$ contains a primitive root of order $l = \mathrm{lcm}(m, n)$, so $\mathbb{Q}(\zeta_n) \subseteq \mathbb{Q}(\zeta_l) \subseteq K$ and $\varphi(l) = \varphi(n)$. If $l \ne n$, some prime $q$ divides $l/n$. If $q \mid n$, then $\varphi(l) \ge q\varphi(n)$. If $q \nmid n$, then $q$ is odd because $n$ is even, and $\varphi(l) \ge (q - 1)\varphi(n) \ge 2\varphi(n)$. Both contradict $\varphi(l) = \varphi(n)$, so $l = n$ and $m \mid n$. The divisibility $n \mid$ `torsionOrder K` for any primitive $n$-th root is `NumberField.Units.dvd_torsionOrder_of_isPrimitiveRoot`. $\square$

**Proposition.** For $n > 2$, $K$ is totally complex: $r_1 = 0$ and $r_2 = \varphi(n)/2$. These are `IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero`, `IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two` and `IsCyclotomicExtension.Rat.isTotallyComplex`.

*Proof.* An embedding $\sigma : K \to \mathbb{C}$ sends $\zeta$ to a primitive $n$-th root of unity. The only real roots of unity are $\pm 1$, of order $1$ or $2$, so for $n > 2$ no embedding is real. Then $2r_2 = [K : \mathbb{Q}] = \varphi(n)$. $\square$

With Dirichlet's unit theorem of Section 2, the unit rank of $\mathbb{Q}(\zeta_n)$ is $\varphi(n)/2 - 1$ for $n > 2$.

#### The Galois group and the characters

The map $\sigma \mapsto a_\sigma$ with $\sigma(\zeta) = \zeta^{a_\sigma}$ is an isomorphism $\mathrm{Gal}(K/\mathbb{Q}) \cong (\mathbb{Z}/n\mathbb{Z})^\times$. In Lean it is `IsCyclotomicExtension.Rat.galEquivZMod n K : Gal(K/ℚ) ≃* (ZMod n)ˣ`. The defining property is `IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq`: if $x^n = 1$, then $\sigma(x) = x^{a_\sigma}$, where the exponent is the natural number `(galEquivZMod n K σ).val`. The form for elements of `𝓞 K` with the action `σ • x` is `IsCyclotomicExtension.Rat.galEquivZMod_smul_of_pow_eq`, and `IsCyclotomicExtension.Rat.galEquivZMod_restrictNormal_apply` says that the restriction to a cyclotomic subfield $\mathbb{Q}(\zeta_m)$ is reduction modulo $m$.

*Proof sketch of the property.* $\sigma(\zeta)$ is again a primitive $n$-th root of unity, so $\sigma(\zeta) = \zeta^a$ with $a$ prime to $n$. Each $x$ with $x^n = 1$ is a power $\zeta^j$, and $\sigma(\zeta^j) = \zeta^{aj} = (\zeta^j)^a$. The map is injective because $\zeta$ generates $K$, and it is surjective because the degree is $\varphi(n)$. $\square$

The decomposition group of a prime $P$ above $p \nmid n$ is the stabilizer of $P$ in the Galois group. By `IsCyclotomicExtension.Rat.galEquivZMod_stabilizer`, its image in $(\mathbb{Z}/n\mathbb{Z})^\times$ is the cyclic subgroup generated by $p$. This is the group theoretic form of the fact that Frobenius at $p$ is $\zeta \mapsto \zeta^p$.

Since the Galois group is abelian, its subgroups correspond to the subgroups of its dual, the group of Dirichlet characters modulo $n$ (Chapter 6). A subgroup $H$ goes to the characters that are trivial on $H$. In Lean, `IsCyclotomicExtension.Rat.subgroupGalEquivSubgroupChar n K R` is an order reversing isomorphism from subgroups of `Gal(K/ℚ)` to subgroups of `DirichletCharacter R n`, for a ring `R` with enough roots of unity. Composed with the Galois correspondence it gives the order isomorphism `IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar` from the subfields of $K$ to the groups of characters. The group $Y$ that belongs to a subfield $F$ has $|Y| = [F : \mathbb{Q}]$ (`IsCyclotomicExtension.Rat.card_intermediateFieldEquivSubgroupChar`). When $F = \mathbb{Q}(\zeta_m)$ with $m \mid n$, a character $\chi$ is in $Y$ if and only if its conductor divides $m$ (`IsCyclotomicExtension.Rat.mem_intermediateFieldEquivSubgroupChar_iff_conductor_dvd`). The abstract duality behind this is `MulChar.subgroupOrderIsoSubgroupMulChar` of Chapter 6.

#### The factorization of primes

The module `Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal` computes the ramification index $e$ and the inertia degree $f$ of each rational prime in $\mathbb{Q}(\zeta_n)$. It uses `Ideal.ramificationIdxIn` and `Ideal.inertiaDegIn` of the ideal `Ideal.span {(p : ℤ)}`, which are the common values of $e$ and $f$ over the primes above $p$ in a Galois extension, and `Ideal.primesOver` for the set of these primes.

**Proposition.** Let $p$ be prime and $\zeta$ a primitive $p$-th root of unity. Then $(\zeta - 1)^{p-1}$ and $p$ are associated in $\mathcal{O}_K$, so $p\mathcal{O}_K = (\zeta - 1)^{p-1}$ is totally ramified: $e = p - 1$, $f = 1$, and there is one prime above $p$. These are `IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime`, `IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_prime`, `IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_prime` and `IsCyclotomicExtension.Rat.ncard_primesOver_of_prime`.

*Proof.* Put $X = 1$ in $\Phi_p(X) = \prod_{i=1}^{p-1}(X - \zeta^i)$: then $p = \prod_{i=1}^{p-1}(1 - \zeta^i)$. For $1 \le i \le p - 1$, the quotient $u_i = (1 - \zeta^i)/(1 - \zeta) = 1 + \zeta + \dots + \zeta^{i-1}$ is in $\mathcal{O}_K$. With $j$ such that $ij \equiv 1 \pmod p$, the inverse $(1 - \zeta)/(1 - \zeta^i) = (1 - (\zeta^i)^j)/(1 - \zeta^i)$ is in $\mathcal{O}_K$ too, so $u_i$ is a unit. So $p = u(1 - \zeta)^{p-1}$ with $u$ a unit. The ideal $P = (\zeta - 1)$ is prime, so $p\mathcal{O}_K = P^{p-1}$ is the factorization of $p$: there is one prime above $p$ and $e = p - 1$. The relation $efg = [K : \mathbb{Q}] = p - 1$ gives $f = 1$. $\square$

The table gives the general results. Here $n = p^{k+1}m$ with $p \nmid m$. The order of $p$ modulo $m$ is `orderOf` of the class of $p$ in `ZMod m`.

| Lean name | Statement |
|---|---|
| `IsCyclotomicExtension.Rat.map_eq_span_zeta_sub_one_pow` | $p\mathcal{O}_K = (\zeta - 1)^{\varphi(p^{k+1})}$ for $n = p^{k+1}$ |
| `IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_prime_pow` | $e = p^k(p - 1)$ for $n = p^{k+1}$ |
| `IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_prime_pow` | $f = 1$ for $n = p^{k+1}$ |
| `IsCyclotomicExtension.Rat.ncard_primesOver_of_prime_pow` | one prime above $p$ for $n = p^{k+1}$ |
| `IsCyclotomicExtension.Rat.absNorm_span_zeta_sub_one` | the ideal $(\zeta - 1)$ has norm $p$ |
| `IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd` | $e = 1$ when $p \nmid n$ |
| `IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd` | $f$ is the order of $p$ modulo $n$ when $p \nmid n$ |
| `IsCyclotomicExtension.Rat.ramificationIdxIn_eq` | $e = p^k(p - 1)$ in general |
| `IsCyclotomicExtension.Rat.inertiaDegIn_eq` | $f$ is the order of $p$ modulo $m$ in general |

The forms without `In`, such as `IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime` and `IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd`, state the same for a given prime `P` with the instances `[P.IsPrime]` and `[P.LiesOver (Ideal.span {(p : ℤ)})]`. The instances `IsCyclotomicExtension.Rat.isPrime_span_zeta_sub_one` and `IsCyclotomicExtension.Rat.liesOver_span_zeta_sub_one` supply them for $P = (\zeta - 1)$. Divisibility of integers by $\zeta - 1$ reduces to divisibility by $p$: `IsCyclotomicExtension.Rat.zeta_sub_one_dvd_intCast_iff` says $\zeta - 1 \mid m \iff p \mid m$ for $m \in \mathbb{Z}$.

#### The third cyclotomic field

The module `Mathlib.NumberTheory.NumberField.Cyclotomic.Three` collects the facts on $K = \mathbb{Q}(\zeta_3)$ that the proof of Fermat's last theorem for the exponent $3$ uses. The element $\eta$ is $\zeta$ as a unit of $\mathcal{O}_K$, and $\lambda = \eta - 1$, which is `hζ.toInteger - 1` in the statements. The identities are `IsCyclotomicExtension.Rat.Three.eta_sq` ($\eta^2 = -\eta - 1$), `IsCyclotomicExtension.Rat.Three.eta_sq_add_eta_add_one` and `IsCyclotomicExtension.Rat.Three.cube_sub_one_eq_mul` ($x^3 - 1 = (x - 1)(x - \eta)(x - \eta^2)$).

**Proposition.** The units of $\mathbb{Z}[\zeta_3]$ are $\pm1, \pm\eta, \pm\eta^2$ (`IsCyclotomicExtension.Rat.Three.Units.mem`).

*Proof.* Here $n = 3$ is odd, so the torsion has order $6$ by `IsCyclotomicExtension.Rat.torsionOrder_eq`, and the six elements $\pm\eta^i$ are distinct roots of unity. The field is imaginary quadratic, so the unit rank is $r_1 + r_2 - 1 = 0$, and every unit is a root of unity. $\square$

**Proposition.** If $\lambda \mid x - 1$, then $\lambda^4 \mid x^3 - 1$ (`IsCyclotomicExtension.Rat.Three.lambda_pow_four_dvd_cube_sub_one_of_dvd_sub_one`).

*Proof.* Write $x = 1 + \lambda y$. Then $x - \eta = \lambda(y - 1)$ and, since $1 - \eta^2 = -\lambda(1 + \eta)$, $x - \eta^2 = \lambda(y - (1 + \eta))$. So $x^3 - 1 = \lambda^3\,y(y - 1)(y - (1 + \eta))$. The quotient $\mathcal{O}_K/(\lambda)$ has $|N(\lambda)| = 3$ elements, and $\eta \equiv 1$ modulo $\lambda$, so $y, y - 1, y - (1 + \eta)$ are congruent to $y, y - 1, y - 2$ and cover the three classes. One of them is divisible by $\lambda$. $\square$

The divisibility by $\lambda$ of the product $y(y - 1)(y - (\eta + 1))$ is `IsCyclotomicExtension.Rat.Three.lambda_dvd_mul_sub_one_mul_sub_eta_add_one`. The companions are `IsCyclotomicExtension.Rat.Three.lambda_dvd_or_dvd_sub_one_or_dvd_add_one` (each $x$ is $0$, $1$ or $-1$ modulo $\lambda$), `IsCyclotomicExtension.Rat.Three.lambda_pow_four_dvd_cube_add_one_of_dvd_add_one`, and `IsCyclotomicExtension.Rat.Three.lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd`, which says that $\lambda^4$ divides $x^3 - 1$ or $x^3 + 1$ when $\lambda \nmid x$.

#### Common errors

1. Most results need both `[NumberField K]` (or `[CharZero K]`) and `[IsCyclotomicExtension {n} ℚ K]` with a set `{n}` of one element. A field with `IsCyclotomicExtension {n, m} ℚ K` is the cyclotomic field of `lcm n m`, and the library must be told so by a separate lemma.
2. The lemmas on $\zeta - 1$ are about `hζ.toInteger - 1 : 𝓞 K`, not about `ζ - 1 : K`. Divisibility in `K` is trivial, since `K` is a field.
3. The prime power lemmas are stated for `p ^ (k + 1)` and not for `p ^ k`, to exclude $n = 1$. A statement for $n = p$ often has its own primed name, such as `IsPrimitiveRoot.zeta_sub_one_prime'`.

### Exercises

1. (A) Use `IsCyclotomicExtension.Rat.discr` to compute the discriminants of $\mathbb{Q}(\zeta_5)$, $\mathbb{Q}(\zeta_8)$ and $\mathbb{Q}(\zeta_{12})$.
2. (A) Show that $\mathbb{Q}(\zeta_n) = \mathbb{Q}(\zeta_{2n})$ for odd $n$, and check that the formula for $d_K$ gives the same value for $n$ and $2n$.
3. (B) Let $p \nmid n$. Show that $p$ splits completely in $\mathbb{Q}(\zeta_n)$ if and only if $p \equiv 1 \pmod n$, and find the factorization type of $2$, $3$ and $5$ in $\mathbb{Q}(\zeta_7)$.
4. (B) Show that $1 + \zeta_5$ is a unit of $\mathbb{Z}[\zeta_5]$ of infinite order, and compute the unit rank of $\mathbb{Q}(\zeta_5)$.
5. (B) Find the subgroup of Dirichlet characters modulo $8$ that belongs to each of the three quadratic subfields $\mathbb{Q}(i)$, $\mathbb{Q}(\sqrt2)$ and $\mathbb{Q}(\sqrt{-2})$ of $\mathbb{Q}(\zeta_8)$.
6. (C) Show that $x^3 + y^3 = z^3$ has no solution with $3 \nmid xyz$ in integers, with the lemmas of the module on $\mathbb{Q}(\zeta_3)$ and the factorization of $x^3 + y^3$.

### Reference

<?reference?>
