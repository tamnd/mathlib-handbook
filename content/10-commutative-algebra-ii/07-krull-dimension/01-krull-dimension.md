---
title: Krull dimension
kind: theory
modules:
  - Mathlib.RingTheory.KrullDimension.Basic
  - Mathlib.RingTheory.KrullDimension.Field
  - Mathlib.RingTheory.KrullDimension.PID
  - Mathlib.RingTheory.KrullDimension.Polynomial
  - Mathlib.RingTheory.KrullDimension.Zero
explains:
  E3: [ringKrullDim, Ring.KrullDimLE, ringKrullDim_le_of_surjective, Polynomial.ringKrullDim_of_isNoetherianRing, IsPrincipalIdealRing.ringKrullDim_eq_one]
  E2: [ringKrullDim_quotient_le, ringKrullDim_eq_zero_of_isField, ringKrullDim_eq_zero_of_field, Ring.krullDimLE_iff, ringKrullDim_eq_of_ringEquiv, ringKrullDim_eq_bot_iff_subsingleton, ringKrullDim_nonneg_of_nontrivial, Polynomial.ringKrullDim_le, ringKrullDim_succ_le_ringKrullDim_polynomial, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, MvPolynomial.ringKrullDim_of_isNoetherianRing, IsPrincipalIdealRing.krullDimLE_one, Ring.krullDimLE_zero_iff, IsArtinianRing.instKrullDimLEOfNatNat, PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  E1: auto
families: []
requires: [V04, V10.C01, V10.C04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Krull dimension

### Overview

The Krull dimension of a ring is the length of the longest chain of prime ideals. A field has dimension $0$, $\mathbb{Z}$ and $k[X]$ have dimension $1$, and $k[X_1, \dots, X_n]$ has dimension $n$, which matches the geometric dimension of affine $n$-space. Dedekind domains are the Noetherian normal domains of dimension at most $1$ (Chapter 4).

The definition is order theory on the prime spectrum. This section proves the basic properties: quotients do not raise the dimension, an integral extension does not change it, a PID that is not a field has dimension $1$, and the polynomial ring over a Noetherian ring has dimension one more than the ring.

### Definitions

**Definition (Krull dimension).** A chain of primes of length $n$ in a ring $R$ is a strict chain $\mathfrak p_0 \subsetneq \mathfrak p_1 \subsetneq \cdots \subsetneq \mathfrak p_n$. The Krull dimension $\dim R$ is the supremum of the lengths of chains of primes. It is a value in $\{-\infty\} \cup \mathbb{N} \cup \{\infty\}$, with $\dim R = -\infty$ exactly when $R$ is the zero ring.

**Definition (Height).** The height of a prime $\mathfrak p$ is the supremum of the lengths of chains of primes that end at $\mathfrak p$. It is the dimension of the localization $R_{\mathfrak p}$, and $\dim R$ is the supremum of the heights of the maximal ideals.

::: mathlib
`ringKrullDim` · `Mathlib.RingTheory.KrullDimension.Basic`

`ringKrullDim R : WithBot ℕ∞` is `Order.krullDim (PrimeSpectrum R)`, the order-theoretic Krull dimension of the poset of primes (Volume 4). The values `⊥` and `⊤` are $-\infty$ and $\infty$. Basic facts: `ringKrullDim_eq_bot_iff_subsingleton`, `ringKrullDim_nonneg_of_nontrivial`, and invariance under ring isomorphisms, `ringKrullDim_eq_of_ringEquiv`. The dimension of the topological space `PrimeSpectrum R` agrees with it, `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`.

<?decl ringKrullDim?>
:::

::: mathlib
`Ring.KrullDimLE` · `Mathlib.RingTheory.KrullDimension.Basic`

`Ring.KrullDimLE n R` is the class "dimension at most `n`", with `Ring.krullDimLE_iff : Ring.KrullDimLE n R ↔ ringKrullDim R ≤ n`. Classes are convenient for automatic use: `IsArtinianRing.instKrullDimLEOfNatNat` gives dimension at most `0` for Artinian rings, and `IsPrincipalIdealRing.krullDimLE_one` gives dimension at most `1` for PIDs. `Ring.krullDimLE_zero_iff` says that dimension at most `0` means every prime is maximal.

<?decl Ring.KrullDimLE?>
:::

::: mathlib
`Ideal.height` · `Mathlib.RingTheory.Ideal.Height`

The height of an ideal, in Volume 9, together with `IsLocalization.AtPrime.ringKrullDim_eq_height`, the dimension of the localization at a prime.

<?decl Ideal.height?>
:::

### Theorems and proofs

**Theorem (Quotients).** For an ideal $I$ of $R$, $\dim R/I \le \dim R$. More generally, if $R \to S$ is surjective, then $\dim S \le \dim R$.

*Proof.* The primes of $S$ correspond to the primes of $R$ that contain the kernel, by $\mathfrak q \mapsto f^{-1}(\mathfrak q)$, and this correspondence preserves strict inclusions. So a chain of length $n$ in $S$ gives a chain of length $n$ in $R$. $\square$

::: mathlib
`ringKrullDim_le_of_surjective` · `Mathlib.RingTheory.KrullDimension.Basic`

`ringKrullDim_le_of_surjective (f : R →+* S) (hf : Function.Surjective f) : ringKrullDim S ≤ ringKrullDim R`, with the special case `ringKrullDim_quotient_le`. The proof is `Order.krullDim_le_of_strictMono` applied to `comap`.

<?decl ringKrullDim_le_of_surjective?>
:::

**Theorem (Integral extensions).** Let $A \subseteq B$ be an integral extension. Then $\dim A = \dim B$.

*Proof.* Let $\mathfrak q_0 \subsetneq \cdots \subsetneq \mathfrak q_n$ be a chain in $B$. The contractions $\mathfrak q_i \cap A$ form a chain in $A$, and the inclusions stay strict by incomparability (Chapter 1, Section 3): two distinct primes of $B$ with the same contraction are not comparable. So $\dim B \le \dim A$. Conversely, let $\mathfrak p_0 \subsetneq \cdots \subsetneq \mathfrak p_n$ be a chain in $A$. By lying over there is $\mathfrak q_0$ over $\mathfrak p_0$, and by going up there are $\mathfrak q_0 \subseteq \mathfrak q_1 \subseteq \cdots \subseteq \mathfrak q_n$ with $\mathfrak q_i \cap A = \mathfrak p_i$. These inclusions are strict since the contractions are distinct. So $\dim A \le \dim B$. $\square$

The index of this edition has no declaration for the equality of dimensions in an integral extension; the ingredients are the lying over, going up and incomparability theorems of Chapter 1.

**Theorem (PIDs).** A PID that is not a field has dimension $1$.

*Proof.* In a PID every nonzero prime $(p)$ is maximal: if $(p) \subseteq (q)$, then $q \mid p$, so $q$ is a unit or an associate of $p$, since $p$ is irreducible. So a chain of primes has at most two terms, $0 \subsetneq (p)$, and since $R$ is not a field it has a nonzero prime, so a chain of length $1$ exists. $\square$

::: mathlib
`IsPrincipalIdealRing.ringKrullDim_eq_one` · `Mathlib.RingTheory.KrullDimension.PID`

`IsPrincipalIdealRing.ringKrullDim_eq_one R (h : ¬ IsField R) : ringKrullDim R = 1` for a PID `R` that is a domain. For fields, `ringKrullDim_eq_zero_of_isField` and `ringKrullDim_eq_zero_of_field` give `0`.

<?decl IsPrincipalIdealRing.ringKrullDim_eq_one?>
:::

**Theorem (Polynomial rings).** For every ring $R$, $\dim R + 1 \le \dim R[X] \le 2\dim R + 1$. If $R$ is Noetherian, $\dim R[X] = \dim R + 1$, and $\dim R[X_1, \dots, X_n] = \dim R + n$.

*Proof of the lower bound.* Let $\mathfrak p_0 \subsetneq \cdots \subsetneq \mathfrak p_n$ be a chain in $R$. Then $\mathfrak p_iR[X]$ is prime, with quotient $(R/\mathfrak p_i)[X]$, a domain, and $\mathfrak p_iR[X] \cap R = \mathfrak p_i$, so the inclusions are strict. The ideal $\mathfrak p_nR[X] + (X)$ is prime, with quotient $R/\mathfrak p_n$, and it contains $\mathfrak p_nR[X]$ strictly. This gives a chain of length $n + 1$ in $R[X]$.

*Sketch of the rest.* For the upper bound, the primes of $R[X]$ over a fixed prime $\mathfrak p$ of $R$ correspond to the primes of $\kappa(\mathfrak p)[X]$, a PID, so a chain in $R[X]$ contracts to a chain in $R$ in which each prime is repeated at most twice. The equality for Noetherian $R$ uses Krull's height theorem (Section 2): a prime $\mathfrak P$ of $R[X]$ over $\mathfrak p$ has height at most $\operatorname{ht}\mathfrak p + 1$. $\square$

::: mathlib
`Polynomial.ringKrullDim_of_isNoetherianRing` · `Mathlib.RingTheory.KrullDimension.Polynomial`

`ringKrullDim R[X] = ringKrullDim R + 1` for `[IsNoetherianRing R]`, a simp lemma. The bounds for every ring are `ringKrullDim_succ_le_ringKrullDim_polynomial` and `Polynomial.ringKrullDim_le : ringKrullDim R[X] ≤ 2 * ringKrullDim R + 1`. For several variables: `MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite` gives `ringKrullDim R + Nat.card ι`, and `MvPolynomial.ringKrullDim_of_isNoetherianRing` the version with `ENat.card ι` for any index type.

<?decl Polynomial.ringKrullDim_of_isNoetherianRing?>
:::

### Examples

**Example (Small dimensions).** A field and every Artinian ring have dimension $0$; so does a product of finitely many fields, and $\mathbb{Z}/n$ for $n \ge 1$. The rings $\mathbb{Z}$, $k[X]$, $\mathbb{Z}_p$, every DVR and every Dedekind domain that is not a field have dimension $1$. The ring $\mathbb{Z}[X]$ has dimension $2$, with the maximal chain $0 \subsetneq (p) \subsetneq (p, X)$.

**Example (Affine space).** For a field $k$, $\dim k[X_1, \dots, X_n] = n$. The chain $0 \subsetneq (X_1) \subsetneq (X_1, X_2) \subsetneq \cdots \subsetneq (X_1, \dots, X_n)$ has length $n$. The upper bound is the Noetherian case of the theorem, by induction on $n$.

**Example (Rings of integers).** The ring of integers $\mathcal O_K$ of a number field is integral over $\mathbb{Z}$, so it has dimension $1$ by the theorem on integral extensions. This is the dimension part of the proof that $\mathcal O_K$ is a Dedekind domain (Chapter 4, Section 1).

**Example (Infinite dimension).** The polynomial ring $k[X_1, X_2, \dots]$ in countably many variables has infinite dimension, since it contains the chains $(X_1) \subsetneq (X_1, X_2) \subsetneq \cdots$ of every length. Nagata gave a Noetherian ring of infinite dimension: every localization at a maximal ideal has finite dimension, but these dimensions are unbounded.

**Example (A valuation ring of dimension $2$).** Let $v$ be the valuation on $k(X, Y)$ with values in $\mathbb{Z}^2$ ordered lexicographically, with $v(X) = (1, 0)$ and $v(Y) = (0, 1)$. Its valuation ring has the chain of primes $0 \subsetneq \mathfrak p \subsetneq \mathfrak m$, where $\mathfrak p$ consists of the elements with first coordinate of the valuation positive. So it has dimension $2$, and it is not Noetherian (Chapter 3, Section 2).

### The library around it

The folder `Mathlib/RingTheory/KrullDimension/` has the definition and the basic facts (`Basic.lean`), fields, PIDs, zero-dimensional rings (`Zero.lean`), local rings, polynomial rings, and the relation with nonzerodivisors and regular sequences used in Section 2. The heights of ideals and Krull's height theorem are in `Mathlib/RingTheory/Ideal/Height.lean` and `Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean`, in Volume 9. The order-theoretic dimension of a poset is in Volume 4.

Common errors of a learner:

- `ringKrullDim R` takes values in `WithBot ℕ∞`, not `ℕ`. Coercions from `ℕ` appear in statements such as `ringKrullDim R = 1`, and arithmetic like `ringKrullDim R + 1` is in `WithBot ℕ∞`.
- The equality for polynomial rings needs `IsNoetherianRing R`; for general rings only the bounds hold.
- `Ring.KrullDimLE n R` is a class. To use a value of `ringKrullDim`, convert with `Ring.krullDimLE_iff`.

### Exercises

1. (A) Show that $\dim(R \times S) = \max(\dim R, \dim S)$.
2. (A) Show that $\dim \mathbb{Z}[X] = 2$, using the theorem on polynomial rings.
3. (A) Show that a domain of dimension $0$ is a field.
4. (B) Show that $\dim R = \dim R_{\mathrm{red}}$, where $R_{\mathrm{red}}$ is the quotient by the nilradical.
5. (B) Show that $\dim R = \sup_{\mathfrak m} \dim R_{\mathfrak m}$, over the maximal ideals.
6. (B) Show that $\dim k[X, Y]/(XY) = 1$, and find its minimal primes.
7. (B) Let $A \subseteq B$ be integral, with $B$ a domain. Show that $A$ is a field if and only if $B$ is a field, and deduce the case $n = 0$ of the theorem on integral extensions.
8. (C) Prove the upper bound $\dim R[X] \le 2\dim R + 1$ in detail.

### Notes and history

The notion of dimension through chains of primes is due to Krull, who also proved the principal ideal theorem in 1928. Seidenberg proved the bounds $\dim R + 1 \le \dim R[X] \le 2\dim R + 1$ in 1953. Nagata's Noetherian ring of infinite dimension is in his book *Local Rings* (1962).

### Reference

<?reference?>
