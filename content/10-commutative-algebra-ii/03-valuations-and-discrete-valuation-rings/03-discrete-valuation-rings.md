---
title: Discrete valuation rings
kind: theory
modules:
  - Mathlib.RingTheory.DiscreteValuationRing.Basic
  - Mathlib.RingTheory.DiscreteValuationRing.TFAE
explains:
  E3: [IsDiscreteValuationRing, IsDiscreteValuationRing.TFAE, IsDiscreteValuationRing.addVal, IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime, exists_maximalIdeal_pow_eq_of_principal]
  E2: [IsDiscreteValuationRing.irreducible_iff_uniformizer, IsDiscreteValuationRing.exists_irreducible, IsDiscreteValuationRing.associated_pow_irreducible, IsDiscreteValuationRing.ideal_eq_span_pow_irreducible, IsDiscreteValuationRing.of_ufd_of_unique_irreducible, IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_add, IsLocalRing.finrank_CotangentSpace_eq_one_iff]
  E1: auto
families: []
requires: [V10.C01, V10.C02]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Discrete valuation rings

### Overview

A discrete valuation ring is a valuation ring whose value group is $\mathbb{Z}$. The examples are $\mathbb{Z}_{(p)}$, the $p$-adic integers, the power series $k[[X]]$, and the local rings of a smooth curve at its points. In such a ring there is an element $\pi$, a uniformizer, such that every nonzero element is $u \pi^n$ with $u$ a unit and $n \ge 0$ unique. The ideals are the powers of $(\pi)$, and arithmetic reduces to counting powers of $\pi$.

The section gives the definition used in Mathlib (a local PID that is not a field), the structure of the elements and ideals, the additive valuation, and the main characterization: a Noetherian local domain of dimension $1$ is a discrete valuation ring if and only if it is integrally closed, if and only if its maximal ideal is principal, if and only if its cotangent space has dimension $1$. This theorem is the local form of the definition of a Dedekind domain in Chapter 4.

### Definitions

**Definition (Discrete valuation ring).** A discrete valuation ring (DVR) is a domain $R$ that is a local principal ideal domain and not a field.

**Definition (Uniformizer).** A uniformizer of a DVR $R$ is a generator $\pi$ of the maximal ideal: $\mathfrak m = (\pi)$.

Since $R$ is a PID and not a field, $\mathfrak m = (\pi)$ for some $\pi \ne 0$. A uniformizer is unique up to a unit.

::: mathlib
`IsDiscreteValuationRing` · `Mathlib.RingTheory.DiscreteValuationRing.Basic`

`IsDiscreteValuationRing R` is a class on a domain `R` that extends `IsPrincipalIdealRing R` and `IsLocalRing R` with the field `not_a_field' : maximalIdeal R ≠ ⊥`. The name records the theorem below: the ring has a valuation with values in $\mathbb{Z}$. Mathlib has no separate predicate for a uniformizer of a DVR: the uniformizers are the irreducible elements, by `IsDiscreteValuationRing.irreducible_iff_uniformizer`, and `IsDiscreteValuationRing.exists_irreducible` gives one.

<?decl IsDiscreteValuationRing?>
:::

**Definition (Valuation of a DVR).** Let $R$ be a DVR with uniformizer $\pi$. For $x \ne 0$, $v(x)$ is the integer $n \ge 0$ with $x = u\pi^n$, $u$ a unit, and $v(0) = \infty$. On the field of fractions $K$, $v(x/y) = v(x) - v(y)$.

::: mathlib
`IsDiscreteValuationRing.addVal` · `Mathlib.RingTheory.DiscreteValuationRing.Basic`

`addVal R : AddValuation R ℕ∞`, the additive valuation of a DVR on the ring itself, with values in the natural numbers with infinity. The rules are `IsDiscreteValuationRing.addVal_mul`, `IsDiscreteValuationRing.addVal_add`, and `IsDiscreteValuationRing.addVal_le_iff_dvd`, which says `addVal R a ≤ addVal R b ↔ a ∣ b`. The value of a uniformizer is `1`.

<?decl IsDiscreteValuationRing.addVal?>
:::

### Theorems and proofs

**Theorem (Structure of a DVR).** Let $R$ be a DVR with uniformizer $\pi$.

1. Every nonzero $x \in R$ is $x = u \pi^n$ with $u$ a unit, and $n$ is unique.
2. The nonzero ideals of $R$ are the ideals $(\pi^n) = \mathfrak m^n$ for $n \ge 0$, and they are distinct.
3. The irreducible elements of $R$ are the uniformizers, up to units there is one prime element, and $R$ is a UFD.
4. The map $v$ is an additive valuation on $K$ with values in $\mathbb{Z}$, and $R = \{x \in K : v(x) \ge 0\}$. So $R$ is a valuation ring with value group $\mathbb{Z}$.

*Proof.* (1) A PID is a UFD (Volume 9, Commutative algebra I), so $x$ is a unit times a product of primes. Every prime $q$ generates a nonzero prime ideal, so $(q) \subseteq \mathfrak m = (\pi)$, and $(q)$ is maximal since $R$ is a PID, so $(q) = (\pi)$ and $q$ is associate to $\pi$. So $x = u\pi^n$. If $u\pi^n = u'\pi^m$ with $n > m$, cancel $\pi^m$ in the domain to get $u' = u\pi^{n-m} \in \mathfrak m$, a contradiction.

(2) A nonzero ideal is $(x)$ with $x = u\pi^n$, so it is $(\pi^n)$. The ideals are distinct by the uniqueness in (1).

(3) An irreducible element of a PID is prime, and the proof of (1) shows that every prime is associate to $\pi$.

(4) For $x = u\pi^n$ and $y = u'\pi^m$, $xy = uu'\pi^{n+m}$, so $v(xy) = v(x) + v(y)$. For the sum, say $n \le m$: $x + y = \pi^n(u + u'\pi^{m-n})$, so $v(x + y) \ge n$. Each element of $K^\times$ is $u\pi^n$ with $n \in \mathbb{Z}$, and it lies in $R$ exactly when $n \ge 0$. $\square$

::: mathlib
`IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime` · `Mathlib.RingTheory.DiscreteValuationRing.Basic`

A domain is a DVR if and only if it is a PID with exactly one nonzero prime ideal. Part 1 of the theorem is `IsDiscreteValuationRing.associated_pow_irreducible`, part 2 is `IsDiscreteValuationRing.ideal_eq_span_pow_irreducible`, and a converse of part 3 is `IsDiscreteValuationRing.of_ufd_of_unique_irreducible`: a UFD with an irreducible element, all of whose irreducible elements are associate, is a DVR.

<?decl IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime?>
:::

**Lemma (Principal maximal ideal).** Let $(R, \mathfrak m)$ be a Noetherian local domain with $\mathfrak m = (\pi)$ principal. Then every nonzero ideal of $R$ is a power of $\mathfrak m$.

*Proof.* First, $\bigcap_n \mathfrak m^n = 0$. Let $x \in \bigcap_n (\pi^n)$ and write $x = \pi^n y_n$. Then $\pi^{n} y_n = \pi^{n+1} y_{n+1}$, and cancellation gives $y_n = \pi y_{n+1}$. So $(y_1) \subseteq (y_2) \subseteq \cdots$, and this chain stabilizes since $R$ is Noetherian: $y_{n+1} = c y_n = c\pi y_{n+1}$ for some $n$ and $c$. Then $(1 - c\pi) y_{n+1} = 0$, and $1 - c\pi$ is a unit, so $y_{n+1} = 0$ and $x = 0$.

Now let $I \ne 0$ be an ideal. If $I = R$, then $I = \mathfrak m^0$. Otherwise $I \subseteq \mathfrak m$, and since $\bigcap \mathfrak m^n = 0$ there is a largest $n$ with $I \subseteq \mathfrak m^n = (\pi^n)$. Then $J = \{y : \pi^n y \in I\}$ is an ideal with $I = \pi^n J$, and $J \not\subseteq \mathfrak m$ by the choice of $n$. So $J = R$ and $I = (\pi^n)$. $\square$

::: mathlib
`exists_maximalIdeal_pow_eq_of_principal` · `Mathlib.RingTheory.DiscreteValuationRing.TFAE`

For a Noetherian local domain with `(maximalIdeal R).IsPrincipal`, every nonzero ideal `I` satisfies `∃ n, I = maximalIdeal R ^ n`. The name is in the root namespace.

<?decl exists_maximalIdeal_pow_eq_of_principal?>
:::

**Theorem (Characterization of DVRs).** Let $(R, \mathfrak m, k)$ be a Noetherian local domain that is not a field. The following are equivalent:

1. $R$ is a DVR;
2. $R$ is a valuation ring;
3. $R$ is a Dedekind domain (Chapter 4);
4. $R$ is integrally closed and has exactly one nonzero prime ideal;
5. $\mathfrak m$ is principal;
6. $\dim_k \mathfrak m/\mathfrak m^2 = 1$;
7. every nonzero ideal of $R$ is a power of $\mathfrak m$.

*Proof of the main steps.* $1 \Rightarrow 2$ is part 4 of the structure theorem. $2 \Rightarrow 5$: in a valuation ring every finitely generated ideal is principal (Section 2), and $\mathfrak m$ is finitely generated. $5 \Rightarrow 7$ is the lemma. $7 \Rightarrow 5$: if $\mathfrak m = \mathfrak m^2$, then $\mathfrak m = 0$ by Nakayama's lemma, and $R$ would be a field. Take $\pi \in \mathfrak m \setminus \mathfrak m^2$. By 7, $(\pi) = \mathfrak m^n$ for some $n$, and $n = 1$ since $\pi \notin \mathfrak m^2$. $5 \Rightarrow 1$: by the lemma every nonzero ideal is $\mathfrak m^n = (\pi^n)$, so $R$ is a local PID, and it is not a field by hypothesis. $5 \Leftrightarrow 6$ is Nakayama's lemma: $\mathfrak m$ needs $\dim_k \mathfrak m/\mathfrak m^2$ generators (Chapter 2, Section 2), and the dimension is not $0$ since $\mathfrak m \ne 0$.

$1 \Rightarrow 4$: a UFD is integrally closed (Volume 9), and the nonzero primes of a DVR reduce to $\mathfrak m$.

$4 \Rightarrow 5$. Take $a \in \mathfrak m$, $a \ne 0$. The radical of $(a)$ is the intersection of the primes that contain $a$, which is $\mathfrak m$, since $\mathfrak m$ is the only nonzero prime. In a Noetherian ring an ideal contains a power of its radical, so $\mathfrak m^n \subseteq (a)$ for some $n$. Take $n$ least, so $n \ge 1$ and there is $b \in \mathfrak m^{n-1}$ with $b \notin (a)$. Let $x = a/b \in K$. Then $x^{-1} = b/a \notin R$. But $b\mathfrak m \subseteq \mathfrak m^n \subseteq (a)$, so $x^{-1}\mathfrak m \subseteq R$. If $x^{-1}\mathfrak m \subseteq \mathfrak m$, then $\mathfrak m$ is a faithful $R[x^{-1}]$-module that is finitely generated over $R$, and the determinant trick (Chapter 1, Section 1) shows that $x^{-1}$ is integral over $R$. As $R$ is integrally closed, $x^{-1} \in R$, which is false. So $x^{-1}\mathfrak m$ is an ideal of $R$ not inside $\mathfrak m$, that is $x^{-1}\mathfrak m = R$. Then $\mathfrak m = xR$, and $x = x \cdot 1 \in xR = \mathfrak m$. So $\mathfrak m = (x)$ is principal.

The equivalence with 3 uses the definition of Chapter 4: a Noetherian, integrally closed domain in which every nonzero prime is maximal. For a local domain that is not a field, this is condition 4. $\square$

::: mathlib
`IsDiscreteValuationRing.TFAE` · `Mathlib.RingTheory.DiscreteValuationRing.TFAE`

The seven conditions, in the order above, as a `List.TFAE` for `R` with `[IsNoetherianRing R] [IsLocalRing R] [IsDomain R]` and a hypothesis `¬IsField R`. Condition 6 is stated with `Module.finrank (ResidueField R) (CotangentSpace R) = 1`, and the equivalence with a DVR alone is `IsLocalRing.finrank_CotangentSpace_eq_one_iff`. Use `(IsDiscreteValuationRing.TFAE R h).out 0 4` for one implication.

<?decl IsDiscreteValuationRing.TFAE?>
:::

### Examples

**Example ($\mathbb{Z}_{(p)}$ and $k[[X]]$).** The ring $\mathbb{Z}_{(p)}$ is a local PID (Exercise 2 of Chapter 2, Section 1) and not a field, so it is a DVR with uniformizer $p$. The elements $-p$ and $p(1 + p)$ are also uniformizers, and $p^2$ is not. In $k[[X]]$, every nonzero series is $X^n g$ with $g(0) \ne 0$, so $g$ is a unit and $X$ is a uniformizer. The valuation is the order of the series. The ring $\mathbb{Z}_p$ of $p$-adic integers is a DVR with uniformizer $p$; it is constructed in Volume 12.

**Example (A local ring of a curve).** Let $R = k[X, Y]/(Y - X^2)$, the parabola, and $P$ the origin, with local ring $R_P$ and maximal ideal $(x, y)$. Since $y = x^2$, the maximal ideal is $(x)$, principal. The ring is a Noetherian local domain, not a field, so it is a DVR by condition 5, and the uniformizer $x$ measures the order of vanishing along the curve. The function $y$ has valuation $2$: the parabola is tangent to the line $y = 0$ at the origin.

**Example (The cusp is not a DVR).** Let $R = k[[t^2, t^3]] \subseteq k[[t]]$, the power series with no $t$ term. Its maximal ideal is $\mathfrak m = (t^2, t^3)$, and $\mathfrak m^2 = (t^4, t^5, t^6)$ contains all $t^n$ with $n \ge 4$. So $\mathfrak m/\mathfrak m^2$ has basis $t^2, t^3$ and dimension $2$, and $R$ is not a DVR by condition 6. In agreement with condition 4, $R$ is not integrally closed: $t = t^3/t^2$ lies in the fraction field and satisfies $X^2 - t^2 = 0$, but $t \notin R$.

**Example (Dimension 2).** The local ring $k[X, Y]_{(X, Y)}$ is Noetherian, integrally closed (a UFD), and local, but has the nonzero primes $(X)$, $(Y)$ and $(X, Y)$. So condition 4 fails, and indeed $\dim_k \mathfrak m/\mathfrak m^2 = 2$. This ring has Krull dimension $2$ (Chapter 7).

### The library around it

The file `DiscreteValuationRing/Basic.lean` has the class, the factorization of elements and ideals, the valuation `addVal`, and the criteria by unique factorization. The file `DiscreteValuationRing/TFAE.lean` has the characterization and the facts `IsDiscreteValuationRing.ringKrullDim_eq_one` and `maximalIdeal_isPrincipal_of_isDedekindDomain`. The folder `Valuation/Discrete/` treats valuations with value group $\mathbb{Z}$ on a field: `Valuation.valuationSubring_isDiscreteValuationRing` says that the ring of integers of a valuation with cyclic nontrivial value group is a DVR. The Witt vectors of a perfect field of characteristic $p$ form a DVR, `WittVector.isDiscreteValuationRing`, used in Chapter 8.

Common errors of a learner:

- The class needs `[IsDomain R]` as a separate argument.
- `addVal R` is a valuation on `R` with values in `ℕ∞`, not on the fraction field. The valuation on the fraction field with values in `ℤᵐ⁰` comes from the Dedekind domain machinery of Chapter 4, Section 3.
- The characterization needs the hypothesis `¬IsField R`, since a field is Noetherian, local and integrally closed.

### Exercises

1. (A) Find a uniformizer of $k[X]_{(X - 1)}$ and the valuation of $X^2 - 1$ and of $X^3$.
2. (A) Show that $\mathbb{Z}_{(p)}/(p^n) \cong \mathbb{Z}/p^n$.
3. (A) Show that the field of fractions of a DVR is $R[\pi^{-1}]$.
4. (B) Let $R$ be a DVR with valuation $v$. Show that $v(x + y) = \min(v(x), v(y))$ when $v(x) \ne v(y)$, and give an example with $v(x) = v(y) < v(x + y)$ in $\mathbb{Z}_{(3)}$.
5. (B) Show that the local ring of the circle $X^2 + Y^2 = 1$ at $(1, 0)$, over a field of characteristic not $2$, is a DVR, and find a uniformizer.
6. (B) Show that the localization of the nodal cubic $Y^2 = X^2(X + 1)$ at the origin is not a DVR.
7. (B) Let $R$ be a DVR and $M$ a finitely generated $R$-module. Show that $M \cong R^r \oplus \bigoplus_i R/(\pi^{n_i})$.
8. (C) Let $R$ be a Noetherian local domain of dimension $1$ that is not integrally closed, and $\bar R$ its integral closure. Assume that $\bar R$ is a finite $R$-module. Show that $\bar R$ is a semilocal PID: its localizations at maximal ideals are DVRs, and it has finitely many maximal ideals.

### Notes and history

The term "discrete valuation ring" refers to the value group $\mathbb{Z}$, a discrete subgroup of $\mathbb{R}$. The characterization by integral closure and dimension 1 is the local form of the theory of Dedekind and of Noether's axioms for Dedekind domains (1927). The proof of $4 \Rightarrow 5$ follows Atiyah and Macdonald, Proposition 9.2. In the Mathlib history, the class was renamed from `DiscreteValuationRing` to `IsDiscreteValuationRing`, following the same convention as `IsLocalRing`.

### Reference

<?reference?>
