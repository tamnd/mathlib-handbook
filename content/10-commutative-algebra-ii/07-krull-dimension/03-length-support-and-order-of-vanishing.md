---
title: Length, support and the order of vanishing
kind: api
modules:
  - Mathlib.RingTheory.Length
  - Mathlib.RingTheory.LocalRing.Length
  - Mathlib.RingTheory.Support
  - Mathlib.RingTheory.OrderOfVanishing.Basic
  - Mathlib.RingTheory.OrderOfVanishing.Noetherian
  - Mathlib.RingTheory.KrullDimension.Module
explains:
  E2: [Module.length, Module.length_eq_add_of_exact, Module.length_eq_one_iff, IsLocalRing.length_restrictScalars, Module.support, Module.mem_support_iff, Module.support_eq_zeroLocus, Module.supportDim, Ring.ord, Ring.ordFrac]
  E1: auto
families: []
requires: [V06, V10.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Length, support and the order of vanishing

### Overview

Three invariants of a module measure its size in different ways. The length counts the steps of a composition series. The support is the set of primes at which the module does not vanish. The dimension of the support is the Krull dimension of the module. For a ring of dimension one, the length of $R/(x)$ is the order of vanishing of $x$, and this order is the starting point of intersection theory and of divisors on curves.

This section describes the length as an element of $\mathbb{N}_\infty$, its additivity on exact sequences, the support and its description by the annihilator, the dimension of a module, and the order of vanishing on a one dimensional Noetherian ring and its fraction field.

### The library around it

#### Length

The module `Mathlib.RingTheory.Length` defines `Module.length R M` in $\mathbb{N}_\infty$ as the Krull dimension of the lattice of submodules, `Module.coe_length`. So it is the supremum of the lengths of chains of submodules, and it is $\infty$ for a module that is not of finite length, `Module.length_ne_top_iff`. A composition series from $0$ to $M$ has exactly this length, `Module.length_compositionSeries`.

| Lean name | Statement |
|---|---|
| `Module.length_eq_zero_iff` | $\ell(M) = 0$ if and only if $M = 0$ |
| `Module.length_pos_iff` | $\ell(M) > 0$ if and only if $M \ne 0$ |
| `Module.length_eq_one_iff` | $\ell(M) = 1$ if and only if $M$ is simple |
| `Module.length_eq_add_of_exact` | $\ell(N) = \ell(M) + \ell(P)$ for a short exact sequence $0 \to M \to N \to P \to 0$ |
| `Module.length_le_of_injective` | a submodule is not longer |
| `Module.length_le_of_surjective` | a quotient is not longer |
| `Submodule.length_lt` | a proper submodule of a module of finite length is shorter |
| `Module.length_prod` | $\ell(M \times N) = \ell(M) + \ell(N)$ |
| `Module.length_pi_of_fintype` | the length of a finite product is the sum |
| `Module.length_eq_finrank` | over a field the length is the dimension |
| `Module.length_of_free_of_finite` | $\ell(R^n) = n \cdot \ell(R)$ |
| `LinearEquiv.length_eq` | isomorphic modules have the same length |

**Theorem.** Length is additive on short exact sequences. This is `Module.length_eq_add_of_exact`.

*Proof sketch.* Identify $M$ with a submodule of $N$ and $P$ with $N/M$. A chain of submodules of $M$ is a chain in $N$ that ends at $M$. A chain of submodules of $N/M$ lifts to a chain in $N$ that starts at $M$. Joining the two chains gives a chain in $N$ of length $\ell(M) + \ell(P)$. Conversely, for a chain $N_0 \subset \dots \subset N_k$ in $N$, the chains $N_i \cap M$ and $(N_i + M)/M$ cannot both stop at a step, so $k \le \ell(M) + \ell(P)$. $\square$

The heights in the lattice of submodules give the lengths of submodules and quotients: `Module.length_submodule` says that $\ell(N)$ is the height of $N$, and `Module.length_quotient` says that $\ell(M/N)$ is its coheight. A change of rings along a surjection does not change length, `Module.length_eq_of_surjective`.

The module `Mathlib.RingTheory.LocalRing.Length` treats a local map $A \to B$ of local rings. If $M$ is a $B$-module, then $\ell_A(M) = \ell_B(M) \cdot [k_B : k_A]$, by `IsLocalRing.length_restrictScalars`, since a simple $B$-module is $k_B$ and has $A$-length $[k_B : k_A]$. If $B$ is flat over $A$ and $M$ is an $A$-module, then $\ell_B(B \otimes_A M) = \ell_A(M) \cdot \ell_B(B/\mathfrak m_A B)$, by `IsLocalRing.length_baseChange`.

#### Support

The module `Mathlib.RingTheory.Support` defines `Module.support R M`, the set of primes $\mathfrak p$ with $M_{\mathfrak p} \ne 0$, `Module.mem_support_iff`.

1. `Module.notMem_support_iff'`: $\mathfrak p$ is not in the support if and only if each $m$ is killed by some $r \notin \mathfrak p$.
2. `Module.mem_support_mono`: the support is closed under specialization.
3. `Module.support_eq_zeroLocus`: for a finitely generated module the support is $V(\operatorname{Ann} M)$, and `Module.mem_support_iff_of_finite` is the form for one prime.
4. `Module.support_of_exact`: for a short exact sequence, the support of the middle term is the union.
5. `Module.support_quotient`: the support of $M/IM$ is $\operatorname{Supp} M \cap V(I)$, and `Module.support_quotSMulTop` is the case $I = (x)$.
6. `Module.support_eq_empty_iff`: the support is empty if and only if $M = 0$.
7. `Module.support_of_algebra`: the support of an algebra $A$ is the zero locus of the kernel of $R \to A$.

A torsion free module over a domain has full support, `Module.support_of_isTorsionFree`. The lemma `LocalizedModule.subsingleton_iff_support_subset` says that $M_f = 0$ if and only if the support lies in $V(f)$.

#### The dimension of a module

The module `Mathlib.RingTheory.KrullDimension.Module` defines `Module.supportDim R M` as the Krull dimension of the support, in `WithBot ℕ∞`. It is $\bot$ exactly for $M = 0$, `Module.supportDim_eq_bot_iff_subsingleton`. For a finitely generated module it is the dimension of $R/\operatorname{Ann} M$, `Module.supportDim_eq_ringKrullDim_quotient_annihilator`. The dimension of $R$ as a module is the Krull dimension of $R$, `Module.supportDim_self_eq_ringKrullDim`, and the dimension of a submodule or quotient is at most that of the module, `Module.supportDim_le_of_injective` and `Module.supportDim_le_of_surjective`. Over a local ring, a module of dimension zero has support $\{\mathfrak m\}$, `support_of_supportDim_eq_zero`.

#### The order of vanishing

Let $R$ be a ring. The module `Mathlib.RingTheory.OrderOfVanishing.Basic` defines `Ring.ord R x` as the length of $R/(x)$. Then $\operatorname{ord}(1) = 0$, `Ring.ord_one`, and $\operatorname{ord}(0) = \ell(R)$, `Ring.ord_zero`. For a nonzerodivisor $b$,

$$\operatorname{ord}(ab) = \operatorname{ord}(a) + \operatorname{ord}(b),$$

by `Ring.ord_mul`. The proof uses the exact sequence $0 \to R/(a) \to R/(ab) \to R/(b) \to 0$, built from `Ideal.mulQuot` and `Ideal.quotOfMul`, and the additivity of length. For a Noetherian ring of dimension at most one, `isFiniteLength_quotient_span_singleton` says that $R/(x)$ has finite length for a nonzerodivisor $x$, so `Ring.ord_ne_top` holds.

The multiplicative form `Ring.ordMonoidWithZeroHom R` takes values in $\mathbb{Z}^{m0}$. It sends $x$ to $\exp(\operatorname{ord}(x))$ for a nonzerodivisor and to $0$ otherwise. On the fraction field $K$ of a Noetherian ring of dimension at most one, `Ring.ordFrac R` extends it by $\operatorname{ord}(a/b) = \operatorname{ord}(a) - \operatorname{ord}(b)$, `Ring.ordFrac_eq_div`.

The module `Mathlib.RingTheory.OrderOfVanishing.Noetherian` treats a discrete valuation ring. Then `Ring.ord_eq_addVal` says that $\operatorname{ord}$ is the normalized additive valuation, `Ring.ord_add` is the ultrametric inequality, and `Ring.ord_eq_iff_associated` says that two elements have the same order if and only if they are associated. On the fraction field, `Ring.ordFrac_eq_valuation_inv` says that `Ring.ordFrac R` is the inverse of the adic valuation of Chapter 4, and `Ring.ordFrac_irreducible` says that a uniformizer has order $\exp(1)$.

#### Common errors

1. `Module.length R M` is in $\mathbb{N}_\infty$. A module of infinite length has length $\top$, and `Module.length_eq_add_of_exact` still holds there.
2. `Module.support_eq_zeroLocus` needs `Module.Finite R M`. The module $\mathbb{Q}/\mathbb{Z}$ over $\mathbb{Z}$ has annihilator $0$, but its support is the set of maximal ideals, not the whole spectrum.
3. `Ring.ord R x` is the length of $R/(x)$ over $R$, not a valuation. It satisfies the ultrametric inequality only under the discrete valuation ring hypotheses of `Ring.ord_add`.

### Exercises

1. (A) Compute `Module.length ℤ (ZMod 12)` from a composition series.
2. (A) Show that $\ell_R(R/\mathfrak m^n) = n$ for a discrete valuation ring $R$ with maximal ideal $\mathfrak m$.
3. (B) Let $R = k[x, y]_{(x, y)}$ and $M = R/(x^2, xy)$. Find the support of $M$ and its dimension.
4. (B) Prove that the support of a finitely generated module is $V(\operatorname{Ann} M)$.
5. (B) Let $R = k[t^2, t^3]$ localized at $(t^2, t^3)$. Compute $\operatorname{ord}(t^2)$ and $\operatorname{ord}(t^3)$.
6. (C) Use `IsLocalRing.length_restrictScalars` to prove that for a finite extension of discrete valuation rings with ramification index $e$ and residue degree $f$, the length of $B/\mathfrak m_A B$ over $A$ is $ef$.

### Reference

<?reference?>
