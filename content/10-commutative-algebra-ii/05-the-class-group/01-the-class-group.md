---
title: The class group
kind: theory
modules:
  - Mathlib.RingTheory.ClassGroup.Basic
  - Mathlib.RingTheory.ClassGroup.ExtendedHom
  - Mathlib.RingTheory.DedekindDomain.PID
explains:
  E3: [ClassGroup, ClassGroup.mk0, card_classGroup_eq_one_iff, ClassGroup.extendedHom, IsPrincipalIdealRing.of_isDedekindDomain_of_uniqueFactorizationMonoid]
  E2: [toPrincipalIdeal, ClassGroup.mk, ClassGroup.equiv, ClassGroup.mk_eq_one_iff, ClassGroup.mk0_eq_one_iff, card_classGroup_eq_one, instFintypeClassGroupOfIsPrincipalIdealRing, ClassGroup.isPrincipal_pow_card, ClassGroup.exists_pow_isPrincipal, ClassGroup.mulEquiv, IsPrincipalIdealRing.of_finite_primes, Ideal.IsPrincipal.of_isPrincipal_pow_of_coprime]
  E1: auto
families: []
requires: [V05, V10.C04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The class group

### Overview

Let $A$ be a domain with fraction field $K$. The invertible fractional ideals of $A$ form a group under multiplication, and the principal fractional ideals $xA$, $x \in K^\times$, form a subgroup. The quotient is the class group $\operatorname{Cl}(A)$. Two invertible ideals lie in the same class when one is the other times a principal fractional ideal.

For a Dedekind domain every nonzero fractional ideal is invertible (Chapter 4, Section 2), so the class group is the group of all nonzero fractional ideals modulo the principal ones. The section proves that $\operatorname{Cl}(A)$ is trivial if and only if $A$ is a PID, and that a Dedekind domain is a UFD if and only if it is a PID. Ring maps induce maps of class groups.

### Definitions

**Definition (Class group).** Let $A$ be a domain with fraction field $K$, $\mathcal I(A)$ the group of invertible fractional ideals, and $\mathcal P(A) = \{xA : x \in K^\times\}$ its subgroup of principal fractional ideals. The class group is $\operatorname{Cl}(A) = \mathcal I(A)/\mathcal P(A)$. The class of $I$ is written $[I]$. When $\operatorname{Cl}(A)$ is finite, its order is the class number $h(A)$.

The map $K^\times \to \mathcal I(A)$, $x \mapsto xA$, is a group map with kernel $A^\times$, since $xA = A$ exactly when $x$ is a unit of $A$. So there is an exact sequence
$$1 \to A^\times \to K^\times \to \mathcal I(A) \to \operatorname{Cl}(A) \to 1.$$

::: mathlib
`ClassGroup` · `Mathlib.RingTheory.ClassGroup.Basic`

`ClassGroup R` is the quotient of the units of `FractionalIdeal R⁰ (FractionRing R)` by the range of `toPrincipalIdeal R (FractionRing R) : Kˣ →* (FractionalIdeal R⁰ K)ˣ`. It is defined for any domain, with the canonical fraction field. The class of a unit fractional ideal for any fraction field `K` is `ClassGroup.mk K`, and `ClassGroup.equiv K` identifies `ClassGroup R` with the quotient built from `K`. An instance gives the commutative group structure.

<?decl ClassGroup?>
:::

For a Dedekind domain, every class contains an integral ideal: if $I = d^{-1}J$ with $J$ an ideal, then $[I] = [J]$, since $d^{-1}A$ is principal. So it is enough to work with nonzero ideals of $A$, and $[I] = [J]$ if and only if $xI = yJ$ for some nonzero $x, y \in A$.

::: mathlib
`ClassGroup.mk0` · `Mathlib.RingTheory.ClassGroup.Basic`

For a Dedekind domain, `ClassGroup.mk0 : (Ideal R)⁰ →* ClassGroup R` sends a nonzero ideal to its class. The criteria are `ClassGroup.mk0_eq_one_iff : mk0 ⟨I, hI⟩ = 1 ↔ I.IsPrincipal` and `ClassGroup.mk0_eq_mk0_iff`, which says that two ideals have the same class if and only if `span {x} * I = span {y} * J` for nonzero `x`, `y`. The map is surjective, `ClassGroup.mk0_surjective`. For a fractional ideal, `ClassGroup.mk_eq_one_iff` says that the class is trivial if and only if the submodule is principal.

<?decl ClassGroup.mk0?>
:::

### Theorems and proofs

**Theorem (Trivial class group).** Let $A$ be a Dedekind domain. Then $\operatorname{Cl}(A)$ is trivial if and only if $A$ is a PID.

*Proof.* If $A$ is a PID, every ideal is principal, so every fractional ideal $d^{-1}J$ is principal, and $\operatorname{Cl}(A) = 1$. Conversely, if $\operatorname{Cl}(A) = 1$, every nonzero ideal $I$ has trivial class, so $I = xA$ for some $x \in K^\times$. Since $x = x \cdot 1 \in I \subseteq A$, $x \in A$ and $I$ is a principal ideal. The zero ideal is principal. $\square$

::: mathlib
`card_classGroup_eq_one_iff` · `Mathlib.RingTheory.ClassGroup.Basic`

For a Dedekind domain with `[Fintype (ClassGroup R)]`: `Fintype.card (ClassGroup R) = 1 ↔ IsPrincipalIdealRing R`. The instance `instFintypeClassGroupOfIsPrincipalIdealRing` gives the finiteness for a PID, and `card_classGroup_eq_one` the class number $1$.

<?decl card_classGroup_eq_one_iff?>
:::

**Theorem (UFD and PID).** A Dedekind domain is a UFD if and only if it is a PID.

*Proof.* A PID is a UFD (Volume 9). Conversely, let $A$ be a Dedekind domain that is a UFD. Every nonzero ideal is a product of nonzero primes, so it is enough to show that every nonzero prime $\mathfrak p$ is principal. Take $a \in \mathfrak p$ nonzero, and factor $a$ into prime elements. Since $\mathfrak p$ is prime, it contains one of them, $\pi$. Then $(\pi)$ is a nonzero prime ideal inside $\mathfrak p$, so $(\pi) = \mathfrak p$, because nonzero primes are maximal in a Dedekind domain. $\square$

::: mathlib
`IsPrincipalIdealRing.of_isDedekindDomain_of_uniqueFactorizationMonoid` · `Mathlib.RingTheory.DedekindDomain.PID`

For a Dedekind domain `R` with `[UniqueFactorizationMonoid R]`, the instance `IsPrincipalIdealRing R`. The same file proves `IsPrincipalIdealRing.of_finite_primes`: a Dedekind domain with finitely many primes is a PID.

<?decl IsPrincipalIdealRing.of_isDedekindDomain_of_uniqueFactorizationMonoid?>
:::

**Theorem (Torsion).** Let $A$ be a Dedekind domain with finite class group of order $h$. For every nonzero ideal $I$, the ideal $I^h$ is principal. If $I^n$ is principal for some $n$ prime to $h$, then $I$ is principal.

*Proof.* In a finite group of order $h$, $g^h = 1$ for every $g$ (Lagrange, Volume 5), and $[I]^h = [I^h]$. For the second claim, $[I]^n = 1$ and $[I]^h = 1$ with $\gcd(n, h) = 1$. Write $1 = un + vh$; then $[I] = ([I]^n)^u ([I]^h)^v = 1$. $\square$

::: mathlib
`ClassGroup.isPrincipal_pow_card` · `Mathlib.RingTheory.ClassGroup.Basic`

`(I ^ Nat.card (ClassGroup R)).IsPrincipal` for every ideal `I` of a Dedekind domain. With `Nat.card`, the statement holds also when the class group is infinite, since then `Nat.card` is `0` and `I ^ 0 = ⊤`. The second claim is `Ideal.IsPrincipal.of_isPrincipal_pow_of_coprime`, and `ClassGroup.exists_pow_isPrincipal` gives a power for a torsion class group.

<?decl ClassGroup.isPrincipal_pow_card?>
:::

**Theorem (Functoriality).** Let $A \to B$ be an injective map of domains. Extension of ideals, $I \mapsto IB$, induces a group map $\operatorname{Cl}(A) \to \operatorname{Cl}(B)$.

*Proof.* For fractional ideals, $(IJ)B = (IB)(JB)$, and $(xA)B = xB$ for $x$ in the fraction field of $A$, viewed in that of $B$. Invertible fractional ideals go to invertible ones, since $IJ = A$ gives $(IB)(JB) = B$. So extension is a group map $\mathcal I(A) \to \mathcal I(B)$ that sends $\mathcal P(A)$ into $\mathcal P(B)$, and it passes to the quotients. $\square$

::: mathlib
`ClassGroup.extendedHom` · `Mathlib.RingTheory.ClassGroup.ExtendedHom`

`ClassGroup.extendedHom A B : ClassGroup A →* ClassGroup B` for an algebra `B` over `A` of domains with `[Module.IsTorsionFree A B]`. The isomorphism induced by a ring isomorphism is `ClassGroup.mulEquiv`.

<?decl ClassGroup.extendedHom?>
:::

### Examples

**Example (PIDs).** The class groups of $\mathbb{Z}$, $k[X]$, $\mathbb{Z}[i]$, $\mathbb{Z}[\omega]$ with $\omega^2 + \omega + 1 = 0$, and every DVR are trivial. So is the class group of every semilocal Dedekind domain, such as $\mathbb{Z}_{(p)} \cap \mathbb{Z}_{(q)}$.

**Example ($\mathbb{Z}[\sqrt{-5}]$).** The ideal $\mathfrak p = (2, 1 + \sqrt{-5})$ is not principal (Chapter 4, Section 3), so $[\mathfrak p] \ne 1$, and $\mathfrak p^2 = (2)$ gives $[\mathfrak p]^2 = 1$. So $\operatorname{Cl}(\mathbb{Z}[\sqrt{-5}])$ contains an element of order $2$. Section 2 shows that it has no other nontrivial element. The ideals $\mathfrak q = (3, 1 + \sqrt{-5})$ and $\mathfrak q'$ lie in the same class as $\mathfrak p$, since $\mathfrak p\mathfrak q = (1 + \sqrt{-5})$ gives $[\mathfrak q] = [\mathfrak p]^{-1} = [\mathfrak p]$.

**Example (An elliptic curve).** Let $k$ be a field of characteristic not $2$ and $A = k[X, Y]/(Y^2 - X^3 + X)$. The curve is smooth, so $A$ is a Dedekind domain. The maximal ideal $\mathfrak m = (x, y)$ at the origin satisfies $\mathfrak m^2 = (x)$: the generators $x^2$, $xy$, $y^2 = x^3 - x = x(x^2 - 1)$ are multiples of $x$, and $x$ is a combination of them, as $x = x^3 - y^2$ with $x^3 = x \cdot x^2$. So $[\mathfrak m]^2 = 1$. In fact $\mathfrak m$ is not principal, and the class group of $A$ is the group of points of the elliptic curve, which can be infinite. This example shows that class groups of Dedekind domains need not be finite.

**Example (Function fields).** For the coordinate ring of the affine line, $k[X]$, the class group is trivial. For the ring $\mathbb{R}[X, Y]/(X^2 + Y^2 - 1)$ of the real circle, the maximal ideal $(x - 1, y)$ is not principal, and the class group has order $2$. The class group of the complex circle $\mathbb{C}[X, Y]/(X^2 + Y^2 - 1) \cong \mathbb{C}[t, t^{-1}]$, with $t = x + iy$, is trivial, since $\mathbb{C}[t, t^{-1}]$ is a localization of a PID.

### The library around it

The file `Mathlib/RingTheory/ClassGroup/Basic.lean` has the definition, the map from ideals, the criteria and the class number 1 theorem. `ClassGroup/ExtendedHom.lean` has the functoriality. The Picard group `CommRing.Pic R`, the group of invertible modules up to isomorphism, is in `Mathlib/RingTheory/PicardGroup.lean`; for a Dedekind domain it is isomorphic to the class group, since every invertible module is isomorphic to an invertible ideal. The finiteness of the class group of a ring of integers and the class number of a number field are in Volume 12.

Common errors of a learner:

- `ClassGroup R` needs `[IsDomain R]`, and the definition uses `FractionRing R`. Lemmas stated with another fraction field `K` pass through `ClassGroup.mk K`.
- `ClassGroup.mk0` takes an element of `(Ideal R)⁰`, a subtype, so its argument is a pair `⟨I, hI⟩` with `hI : I ∈ (Ideal R)⁰`. The membership follows from `I ≠ 0`, since `Ideal R` has no zero divisors when `R` is a domain.
- The class number theorem uses `Fintype.card`, so it needs a `Fintype` instance, while `ClassGroup.isPrincipal_pow_card` uses `Nat.card`.

### Exercises

1. (A) Show that $[I][J] = [IJ]$ and $[I]^{-1} = [I^{-1}]$ in $\operatorname{Cl}(A)$.
2. (A) Let $A$ be a Dedekind domain with class number $3$, and $I$ an ideal with $I^2$ principal. Show that $I$ is principal.
3. (A) Show that every class of a Dedekind domain contains an integral ideal.
4. (B) Let $A$ be a Dedekind domain and $S$ a multiplicative subset. Show that $\operatorname{Cl}(A) \to \operatorname{Cl}(S^{-1}A)$ is surjective, with kernel generated by the classes of the primes that meet $S$.
5. (B) In $\mathbb{Z}[\sqrt{-5}]$, show that the primes over $3$ and over $7$ are not principal, and that the primes over $29$ are principal.
6. (B) Verify the identity $\mathfrak m^2 = (x)$ in the elliptic curve example, and show that $\mathfrak m$ is not principal by computing $\dim_k \mathfrak m/\mathfrak m^2$ at the origin and the degree of a putative generator. Use the grading by $\deg x = 2$, $\deg y = 3$.
7. (C) Show that $(x - 1, y)$ is not principal in $\mathbb{R}[X, Y]/(X^2 + Y^2 - 1)$.

### Notes and history

The class group goes back to Gauss's composition of binary quadratic forms in the *Disquisitiones Arithmeticae* (1801), which is the class group of a quadratic order in another language. Dedekind proved that the class group of a ring of integers of a number field is finite. Claborn proved in 1966 that every abelian group is the class group of some Dedekind domain.

### Reference

<?reference?>
