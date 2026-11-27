---
title: Étale, smooth and unramified algebras, and Witt vectors
kind: theory
modules:
  - Mathlib.RingTheory.Unramified.Basic
  - Mathlib.RingTheory.Smooth.Basic
  - Mathlib.RingTheory.Etale.Basic
  - Mathlib.RingTheory.Etale.Field
  - Mathlib.RingTheory.Smooth.Flat
  - Mathlib.RingTheory.WittVector.Defs
  - Mathlib.RingTheory.WittVector.Basic
  - Mathlib.RingTheory.WittVector.WittPolynomial
  - Mathlib.RingTheory.WittVector.Compare
  - Mathlib.RingTheory.WittVector.DiscreteValuationRing
explains:
  E3: [Algebra.FormallyUnramified, Algebra.FormallySmooth, Algebra.Etale, Algebra.Etale.iff_formallyUnramified_and_smooth, WittVector, WittVector.isDiscreteValuationRing]
  E2: [Algebra.Unramified, Algebra.Smooth, Algebra.FormallyEtale, Algebra.H1Cotangent, Algebra.FormallyUnramified.lift_unique, Algebra.FormallySmooth.exists_lift, Algebra.FormallySmooth.iff_comp_surjective, Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth, Algebra.FormallyEtale.of_isLocalization, Algebra.Etale.of_isLocalizationAway, Algebra.FormallyEtale.of_isSeparable, Algebra.FormallyEtale.iff_exists_algEquiv_prod, Algebra.Smooth.flat, Algebra.Etale.comp, Algebra.Etale.baseChange, WittVector.coeff, wittPolynomial, WittVector.ghostMap, WittVector.equiv, WittVector.toPadicInt, WittVector.exists_eq_pow_p_mul]
  E1: auto
families: []
requires: [V07, V10.C03, V10.C06]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Étale, smooth and unramified algebras, and Witt vectors

### Overview

Let $A$ be an $R$-algebra. Grothendieck's infinitesimal criteria describe three properties through lifting along square-zero thickenings $B \to B/I$, $I^2 = 0$: $A$ is formally unramified if algebra maps $A \to B/I$ have at most one lift to $B$, formally smooth if they have at least one, and formally étale if they have exactly one. With a finiteness condition these give unramified, smooth and étale algebras. A finite separable field extension is étale; a polynomial ring is smooth; a localization is formally étale.

The last part of the section treats a ring that exists because of these ideas: the ring of Witt vectors $W(k)$ of a perfect field $k$ of characteristic $p$, a complete DVR of characteristic $0$ with residue field $k$ and maximal ideal $(p)$. For $k = \mathbb{F}_p$ it is the ring $\mathbb{Z}_p$.

### Definitions

**Definition (Unramified, smooth, étale).** Let $A$ be an $R$-algebra. $A$ is formally unramified if for every $R$-algebra $B$ and ideal $I \subseteq B$ with $I^2 = 0$, the map $\operatorname{Hom}_R(A, B) \to \operatorname{Hom}_R(A, B/I)$ is injective; formally smooth if it is surjective; formally étale if it is bijective. $A$ is unramified if it is formally unramified and of finite type, smooth if it is formally smooth and of finite presentation, and étale if it is formally étale and of finite presentation.

::: mathlib
`Algebra.FormallyUnramified` · `Mathlib.RingTheory.Unramified.Basic`

`Algebra.FormallyUnramified R A` is the class with the single field `Subsingleton Ω[A⁄R]`: the vanishing of the Kähler differentials. This is equivalent to the lifting definition, and the lifting form is `Algebra.FormallyUnramified.lift_unique`, for a nilpotent ideal. `Algebra.Unramified R A` adds `Algebra.FiniteType R A`.

<?decl Algebra.FormallyUnramified?>
:::

::: mathlib
`Algebra.FormallySmooth` · `Mathlib.RingTheory.Smooth.Basic`

`Algebra.FormallySmooth R A` has two fields: `Ω[A⁄R]` is a projective `A`-module, and the first homology `Algebra.H1Cotangent R A` of the naive cotangent complex vanishes. The equivalence with lifting is `Algebra.FormallySmooth.iff_comp_surjective`, and `Algebra.FormallySmooth.exists_lift` lifts along a nilpotent ideal. `Algebra.Smooth R A` adds `Algebra.FinitePresentation R A`.

<?decl Algebra.FormallySmooth?>
:::

::: mathlib
`Algebra.Etale` · `Mathlib.RingTheory.Etale.Basic`

`Algebra.FormallyEtale R A` asks for `Subsingleton Ω[A⁄R]` and `Subsingleton (H1Cotangent R A)`, and `Algebra.Etale R A` extends it with finite presentation. `Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth` splits formally étale into the two other properties. Étale algebras are stable under composition, `Algebra.Etale.comp`, and base change, `Algebra.Etale.baseChange`.

<?decl Algebra.Etale?>
:::

**Definition (Witt vectors).** Let $p$ be a prime. The Witt polynomials are $w_n = \sum_{i=0}^n p^iX_i^{p^{n-i}} = X_0^{p^n} + pX_1^{p^{n-1}} + \cdots + p^nX_n$. For a ring $R$, the Witt vectors $W(R)$ are the sequences $(a_0, a_1, \dots)$ of elements of $R$, with the unique ring structure, given by universal integer polynomials in the coordinates, for which the ghost map $(a_n) \mapsto (w_n(a))_n \in R^{\mathbb{N}}$ is a ring map for every $R$.

::: mathlib
`WittVector` · `Mathlib.RingTheory.WittVector.Defs`

`WittVector p R`, with notation `𝕎 R`, is a structure that wraps a sequence; `WittVector.coeff` gives the coordinates. The Witt polynomials are `wittPolynomial p R n`, and the ghost map is `WittVector.ghostMap`, a ring map. The ring axioms are proved by the ghost component argument: over a ring in which $p$ is invertible, the ghost map is a bijection, and the identities transfer from $R^{\mathbb{N}}$.

<?decl WittVector?>
:::

### Theorems and proofs

**Theorem (Unramified means no differentials).** $A$ is formally unramified over $R$ if and only if $\Omega_{A/R} = 0$.

*Proof.* Two lifts $f, g : A \to B$ of the same map to $B/I$, $I^2 = 0$, differ by $D = f - g : A \to I$. The ideal $I$ is an $A$-module through $f \bmod I = g \bmod I$, and $D(ab) = f(a)f(b) - g(a)g(b) = f(a)D(b) + g(b)D(a)$, so $D$ is an $R$-derivation. If $\Omega_{A/R} = 0$, every derivation is zero, so $f = g$. Conversely, $B = A \oplus \Omega_{A/R}$ with $\Omega^2 = 0$ and $I = \Omega_{A/R}$ has the two lifts $a \mapsto (a, 0)$ and $a \mapsto (a, da)$ of the identity, so formal unramifiedness gives $d = 0$, and $\Omega_{A/R} = 0$. $\square$

**Theorem (Étale = unramified + smooth).** $A$ is étale over $R$ if and only if it is unramified and smooth.

*Proof.* Lifts exist and are unique if and only if they exist and are at most one. For the finiteness conditions: an étale algebra is of finite presentation, hence of finite type and smooth; conversely, a smooth algebra is of finite presentation. $\square$

::: mathlib
`Algebra.Etale.iff_formallyUnramified_and_smooth` · `Mathlib.RingTheory.Etale.Basic`

`Algebra.Etale R A ↔ Algebra.FormallyUnramified R A ∧ Algebra.Smooth R A`. Smooth algebras are flat, `Algebra.Smooth.flat`, so étale algebras are flat as well.

<?decl Algebra.Etale.iff_formallyUnramified_and_smooth?>
:::

**Theorem (Examples of étale algebras).**

1. A localization $T^{-1}R$ is formally étale over $R$; $R[1/f]$ is étale.
2. A finite separable field extension $L/K$ is étale.
3. An algebra $A$ of finite type over a field $K$ is étale if and only if $A \cong L_1 \times \cdots \times L_n$ with each $L_i$ a finite separable extension of $K$.

*Proof of 1 and 2.* (1) A map $T^{-1}R \to B/I$ is a map $R \to B/I$ that sends $T$ to units. Its lift $R \to B$ is the structure map, and it sends $T$ to units of $B$, since an element of $B$ whose image in $B/I$ is a unit is a unit when $I$ is nilpotent. So the lift to $T^{-1}R$ exists and is unique by the universal property of localization. (2) $L = K[X]/(f)$ with $f$ separable. A map $L \to B/I$ is a root $\bar b$ of $f$ in $B/I$. Lift $\bar b$ to any $b \in B$; since $f'(b)$ is a unit (its image is $f'(\bar b)$, a unit because $f$ is separable), the root $b - f(b)/f'(b)$ is the unique lift, as in Hensel's lemma (Chapter 6, Section 2): with $I^2 = 0$ one Newton step gives an exact root, and two roots $b, b + \epsilon$ with $\epsilon \in I$ satisfy $f'(b)\epsilon = 0$, so $\epsilon = 0$. $\square$

::: mathlib
`Algebra.FormallyEtale.of_isSeparable` · `Mathlib.RingTheory.Etale.Field`

A separable algebraic field extension is formally étale. The structure theorem for étale algebras over a field is `Algebra.FormallyEtale.iff_exists_algEquiv_prod`: for an essentially finite type algebra `A` over a field `K`, formally étale if and only if `A ≃ₐ[K] Π i, Ai i` for finitely many separable field extensions. For localizations, `Algebra.FormallyEtale.of_isLocalization` and `Algebra.Etale.of_isLocalizationAway`.

<?decl Algebra.FormallyEtale.of_isSeparable?>
:::

**Theorem (Witt vectors of a perfect field).** Let $k$ be a perfect field of characteristic $p$. Then $W(k)$ is a DVR with maximal ideal $pW(k)$ and residue field $k$. For $k = \mathbb{F}_p$, $W(\mathbb{F}_p) \cong \mathbb{Z}_p$.

*Proof sketch.* The Verschiebung $V(a_0, a_1, \dots) = (0, a_0, a_1, \dots)$ and the Frobenius $F(a_0, a_1, \dots) = (a_0^p, a_1^p, \dots)$ satisfy $p = VF$ on $W(k)$ since $k$ has characteristic $p$. A nonzero $a$ has a first nonzero coordinate $a_m$, so $a = V^m(c)$ with $c_0 \ne 0$. Since $k$ is perfect, $F$ is bijective and $c = F^m(b)$, so $a = V^mF^m(b) = p^mb$, with $b_0 \ne 0$. An element $b$ with $b_0 \ne 0$ is a unit: its image in $W(k)/V W(k) \cong k$ is $b_0$, a unit, and $W(k)$ is complete for $V W(k) = pW(k)$. So every nonzero element is $p^m$ times a unit, and $p$ is not nilpotent because the $p^m$ have nonzero coordinate $m$. A domain with this property is a DVR (Chapter 3, Section 3). For $k = \mathbb{F}_p$, the maps $W(\mathbb{F}_p) \to W(\mathbb{F}_p)/p^n = W_n(\mathbb{F}_p) \cong \mathbb{Z}/p^n$ give, in the limit, the isomorphism with $\mathbb{Z}_p$. $\square$

::: mathlib
`WittVector.isDiscreteValuationRing` · `Mathlib.RingTheory.WittVector.DiscreteValuationRing`

The instance `IsDiscreteValuationRing (𝕎 k)` for a perfect field `k` of characteristic `p`. The key step of the proof is `WittVector.exists_eq_pow_p_mul : a ≠ 0 → ∃ m b, b.coeff 0 ≠ 0 ∧ a = p ^ m * b`.

<?decl WittVector.isDiscreteValuationRing?>
:::

::: mathlib
`WittVector.equiv` · `Mathlib.RingTheory.WittVector.Compare`

`WittVector.equiv p : 𝕎 (ZMod p) ≃+* ℤ_[p]`, the isomorphism with the `p`-adic integers of Volume 12, given by `WittVector.toPadicInt` and its inverse.

<?decl WittVector.equiv?>
:::

### Examples

**Example (A ramified extension).** $\mathbb{Z}[i]$ over $\mathbb{Z}$ has $\Omega = \mathbb{Z}[i]/(2)$ (the derivative of $X^2+1$ is $2X$), which is nonzero, so it is not unramified. After inverting $2$, $\Omega_{\mathbb{Z}[1/2, i]/\mathbb{Z}[1/2]} = 0$, and $\mathbb{Z}[1/2, i]$ is étale over $\mathbb{Z}[1/2]$. In the language of Chapter 4, $2$ is the only prime that ramifies in $\mathbb{Z}[i]$.

**Example (Smooth and not smooth).** $R[X_1, \dots, X_n]$ is smooth over $R$: a map to $B/I$ is a choice of $n$ elements of $B/I$, which lift to $B$. The cusp $k[X, Y]/(Y^2 - X^3)$ is not smooth over $k$, since $\Omega$ is not projective: its rank at the origin is $2$ and at other points $1$.

**Example (Inseparable extensions).** $\mathbb{F}_p(t^{1/p})$ over $\mathbb{F}_p(t)$ has $\Omega \cong L \ne 0$, generated by $d(t^{1/p})$, so it is a finite field extension that is not étale.

**Example (Witt vectors).** $W(\mathbb{F}_{p^n})$ is the ring of integers of the unramified extension of $\mathbb{Q}_p$ of degree $n$. For a ring $R$ in which $p$ is invertible, the ghost map is an isomorphism $W(R) \cong R^{\mathbb{N}}$, so Witt vectors are interesting only in the presence of $p$-torsion. For $p = 2$ and $R = \mathbb{F}_2$, $(1, 0, 0, \dots) + (1, 0, 0, \dots) = (0, 1, 0, \dots)$, which corresponds to $1 + 1 = 2$ in $\mathbb{Z}_2$.

### The library around it

Unramified, smooth and étale algebras are in `Mathlib/RingTheory/Unramified/`, `Mathlib/RingTheory/Smooth/` and `Mathlib/RingTheory/Etale/`, with the field cases in the files `Field.lean` and the relation to standard smooth algebras in `Smooth/StandardSmooth*.lean`. The naive cotangent complex that defines `Algebra.H1Cotangent` is in `Mathlib/RingTheory/Extension/`. Witt vectors are in `Mathlib/RingTheory/WittVector/`, with the Frobenius, the Verschiebung, the Teichmüller lifts, the truncated Witt vectors, and the isomorphism with $\mathbb{Z}_p$. The $p$-adic integers and the separability of field extensions are in Volumes 12 and 11.

Common errors of a learner:

- `Algebra.FormallySmooth` in Mathlib is defined through the cotangent complex, not through lifting. To use lifting, apply `Algebra.FormallySmooth.exists_lift`.
- `Algebra.Unramified` needs only finite type, while `Algebra.Smooth` and `Algebra.Etale` need finite presentation.
- The ring structure on `𝕎 R` depends on `p`, which must be a prime given as `[Fact p.Prime]`.

### Exercises

1. (A) Show that $R \times R$ is étale over $R$.
2. (A) Show that $\mathbb{C}$ is étale over $\mathbb{R}$, and that $\mathbb{R}[X]/(X^2)$ is not.
3. (A) Compute the first two ghost components of a Witt vector, and show that the zeroth coordinate of a sum is $a_0 + b_0$.
4. (B) Show that $\mathbb{Z}[\sqrt{-5}]$ is étale over $\mathbb{Z}$ after inverting $10$, and find the primes of $\mathbb{Z}$ at which it is not unramified.
5. (B) Show that a formally unramified algebra $A$ over a field $K$ that is finite as a vector space is a product of finite separable field extensions, assuming it is reduced.
6. (B) Compute the first coordinate of $(a_0, 0, \dots) + (b_0, 0, \dots)$ in $W(R)$ for $p = 2$ and $p = 3$.
7. (C) Show that $W(k)/pW(k) \cong k$ for a perfect field $k$ of characteristic $p$, and that the Teichmüller map $k \to W(k)$, $a \mapsto (a, 0, 0, \dots)$, is multiplicative.

### Notes and history

The definitions of unramified, smooth and étale morphisms through infinitesimal lifting are due to Grothendieck, in the *Éléments de géométrie algébrique* (EGA IV, 1964 to 1967). Witt vectors were introduced by Ernst Witt in 1936, to describe the complete DVRs of characteristic $0$ with perfect residue field of characteristic $p$.

### Reference

<?reference?>
