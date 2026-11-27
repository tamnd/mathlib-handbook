---
title: Primary decomposition
kind: theory
modules:
  - Mathlib.RingTheory.Ideal.IsPrimary
  - Mathlib.RingTheory.IsPrimary
  - Mathlib.RingTheory.Lasker
explains:
  E3: [Ideal.IsPrimary, IsLasker, Submodule.isLasker, InfIrred.isPrimary, Submodule.IsMinimalPrimaryDecomposition]
  E2: [Ideal.isPrimary_iff, Ideal.isPrime_radical, Ideal.isPrimary_of_isMaximal_radical, Ideal.IsPrime.isPrimary, Ideal.IsPrimary.inf, Ideal.isPrimary_finsetInf, Submodule.IsPrimary, Submodule.IsLasker.exists_isMinimalPrimaryDecomposition, Submodule.IsMinimalPrimaryDecomposition.image_radical_eq_associated_primes, Ideal.IsMinimalPrimaryDecomposition.minimalPrimes_subset_image_radical, Submodule.associatedPrimes]
  E1: auto
families: []
requires: [V06.C02, V06.C06, V09.C01]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Primary decomposition

### Overview

In $\mathbb{Z}$, the factorization $n = \pm p_1^{e_1} \cdots p_k^{e_k}$ gives $(n) = (p_1^{e_1}) \cap \cdots \cap (p_k^{e_k})$. In a general Noetherian ring ideals do not factor into primes, but they are still finite intersections of primary ideals: this is the Lasker-Noether theorem. The radicals of the pieces of a minimal decomposition depend only on the ideal, so an ideal has only finitely many minimal primes over it. The radical $r(I)$ and the ideal quotient $(I : x) = \{ y \in R : xy \in I \}$ are from Chapter 1.

### Definitions

In this section $R$ is a commutative ring.

**Definition (Primary ideal).** An ideal $q \ne R$ is primary if for all $x, y \in R$ with $xy \in q$ and $x \notin q$, some power $y^n$ lies in $q$, that is, $y \in r(q)$.

Equivalently, every zero divisor of $R/q$ is nilpotent. Every prime ideal is primary.

**Definition (Irreducible ideal).** An ideal $I \ne R$ is irreducible if $I = J \cap K$ for ideals $J, K$ implies $I = J$ or $I = K$.

**Definition (Primary decomposition).** A primary decomposition of an ideal $I$ is an expression $I = q_1 \cap \cdots \cap q_k$ with every $q_i$ primary. It is minimal if the radicals $r(q_i)$ are pairwise distinct and no $q_i$ contains $\bigcap_{j \ne i} q_j$.

::: mathlib
`Ideal.IsPrimary` · `Mathlib.RingTheory.Ideal.IsPrimary`

An abbreviation for `Submodule.IsPrimary` with `M = R`: Mathlib defines primary submodules of a module, where `r • x ∈ S` implies `x ∈ S` or `r ^ n • ⊤ ≤ S`. The lemma `Ideal.isPrimary_iff` gives the definition above.

<?decl Ideal.IsPrimary?>
:::

### Theorems and proofs

**Theorem (Radical of a primary ideal).** If $q$ is primary, then $r(q)$ is prime.

*Proof.* Since $1 \notin q$, $1 \notin r(q)$. Let $xy \in r(q)$, so $x^m y^m = (xy)^m \in q$ for some $m$. If $x^m \in q$, then $x \in r(q)$. Otherwise $q$ primary gives $(y^m)^n \in q$ for some $n$, so $y \in r(q)$. $\square$

If $p = r(q)$, then $q$ is called $p$-primary.

**Theorem (Ideals with maximal radical).** If $r(I) = m$ is a maximal ideal, then $I$ is $m$-primary. In particular $m^n$ is $m$-primary for $n \ge 1$.

*Proof.* Here $I \ne R$, since $r(I) \ne R$. Let $xy \in I$ with $y \notin m$. Since $m$ is maximal, $m + Ry = R$, so $1 = a + ry$ with $a \in m$ and $r \in R$. Then $a^n \in I$ for some $n$. Expand $a^n = (1 - ry)^n = 1 - ys$ with $s \in R$. So $1 = ys + a^n$ and $x = (xy)s + x a^n \in I$. This is the definition with $x$ and $y$ exchanged. For $m^n$: $m \subseteq r(m^n) \subseteq r(m) = m$. $\square$

**Theorem (Intersections).** If $q_1, \dots, q_k$ are $p$-primary, then $q = q_1 \cap \cdots \cap q_k$ is $p$-primary.

*Proof.* By Chapter 1, $r(q) = \bigcap_i r(q_i) = p$, and $q \ne R$. Let $xy \in q$ and $y \notin p$. For each $i$, $xy \in q_i$ and $y \notin r(q_i)$, so $x \in q_i$. Hence $x \in q$. $\square$

::: mathlib
`Ideal.isPrimary_of_isMaximal_radical` · `Mathlib.RingTheory.Ideal.IsPrimary`

The theorem on maximal radicals. The first theorem is `Ideal.isPrime_radical`, primes are primary by `Ideal.IsPrime.isPrimary`, and intersections are `Ideal.IsPrimary.inf` and `Ideal.isPrimary_finsetInf`.

<?decl Ideal.isPrimary_of_isMaximal_radical?>
:::

**Lemma (Ideal quotients of a primary ideal).** Let $q$ be $p$-primary and $x \in R$.

1. If $x \in q$, then $(q : x) = R$.
2. If $x \notin q$, then $(q : x)$ is $p$-primary.
3. If $x \notin p$, then $(q : x) = q$.

*Proof.* (1) If $x \in q$, then $xy \in q$ for every $y$. (2) If $y \in (q : x)$, then $xy \in q$ and $x \notin q$, so $y \in p$. So $q \subseteq (q : x) \subseteq p$, and taking radicals gives $r(q : x) = p$. If $yz \in (q : x)$ and $z \notin p$, then $(xy) z \in q$ and $z \notin r(q)$, so $xy \in q$ and $y \in (q : x)$. (3) If $xy \in q$ and $x \notin r(q)$, then $y \in q$. $\square$

**Theorem (Irreducible ideals are primary).** If $R$ is Noetherian, then every irreducible ideal is primary.

*Proof.* Let $I$ be irreducible and $A = R/I$. Ideals of $A$ correspond to ideals of $R$ that contain $I$, and the correspondence preserves intersections, so the zero ideal of $A$ is irreducible. It suffices to show: if $xy = 0$ in $A$ and $y \ne 0$, then $x$ is nilpotent. The ring $A$ is Noetherian (Section 1), so the chain $\operatorname{Ann}(x) \subseteq \operatorname{Ann}(x^2) \subseteq \cdots$ stops: $\operatorname{Ann}(x^n) = \operatorname{Ann}(x^{n+1})$ for some $n$. Let $a \in (x^n) \cap (y)$. From $a = by$ follows $ax = bxy = 0$. From $a = cx^n$ follows $cx^{n+1} = 0$, so $c \in \operatorname{Ann}(x^{n+1}) = \operatorname{Ann}(x^n)$ and $a = cx^n = 0$. So $(x^n) \cap (y) = 0$. Since $0$ is irreducible and $(y) \ne 0$, $(x^n) = 0$. $\square$

**Theorem (Lasker-Noether).** In a Noetherian ring every ideal $I \ne R$ has a primary decomposition.

*Proof.* First, every ideal is the intersection of a finite set of irreducible ideals, where $R$ is the intersection of the empty set. Let $\mathcal{S}$ be the set of ideals for which this fails, and assume $\mathcal{S} \ne \varnothing$. By the maximal condition, $\mathcal{S}$ has a maximal element $I$. Then $I \ne R$, and $I$ is not irreducible. So $I = J \cap K$ with $J \ne I$ and $K \ne I$. Then $J$ and $K$ strictly contain $I$, so they are not in $\mathcal{S}$. They are finite intersections of irreducible ideals, and so is $I$, a contradiction. For $I \ne R$ the set is nonempty, and its members are primary by the previous theorem. $\square$

**Theorem (Minimal decompositions).** If $I$ has a primary decomposition, then it has a minimal one.

*Proof.* Group the $q_i$ by their radicals, and replace each group by its intersection. By the theorem on intersections this gives a decomposition with distinct radicals. Then, while some $q_i$ contains the intersection of the others, delete it. The intersection does not change, the radicals stay distinct, and the process stops because the set is finite. $\square$

::: mathlib
`Submodule.isLasker` · `Mathlib.RingTheory.Lasker`

The theorem for a Noetherian module: `IsLasker R M` says that every submodule is `s.inf id` for a finite set `s` of primary submodules. The irreducible step is `InfIrred.isPrimary`, and `Submodule.IsLasker.exists_isMinimalPrimaryDecomposition` gives a minimal decomposition.

<?decl Submodule.isLasker?>
:::

**Theorem (First uniqueness theorem).** Let $I = q_1 \cap \cdots \cap q_k$ be a minimal primary decomposition and $p_i = r(q_i)$. Then $\{p_1, \dots, p_k\}$ is the set of prime ideals of the form $r(I : x)$ with $x \in R$. In particular this set depends only on $I$.

*Proof.* For $x \in R$, $(I : x) = \bigcap_i (q_i : x)$, since $xy \in I$ exactly when $xy \in q_i$ for all $i$. Radicals commute with finite intersections (Chapter 1), so by the lemma
$$r(I : x) = \bigcap_{i \,:\, x \notin q_i} p_i.$$
Assume $r(I : x)$ is prime. Then $x \notin q_i$ for some $i$, and the prime $r(I : x)$ contains the product of the $p_i$ with $x \notin q_i$. So it contains one of them, $p_j$, and it is contained in $p_j$. Thus $r(I : x) = p_j$. Conversely, fix $i$. By minimality there is $x_i \in \bigcap_{j \ne i} q_j$ with $x_i \notin q_i$. Then $r(I : x_i) = p_i$. $\square$

The primes $p_i$ are the associated primes of $I$. Some are minimal among them, the others are embedded.

**Corollary (Minimal primes).** Let $R$ be Noetherian and $I \ne R$. Every prime $P \supseteq I$ contains a minimal associated prime of $I$. So the minimal primes over $I$ are the minimal associated primes, and there are finitely many.

*Proof.* Take a primary decomposition. Then $P \supseteq q_1 \cap \cdots \cap q_k \supseteq q_1 \cdots q_k$, so $P \supseteq q_i$ for some $i$, and $P = r(P) \supseteq r(q_i) = p_i$. If $P$ is minimal over $I$, then $P = p_i$ since $p_i \supseteq I$. $\square$

::: mathlib
`Submodule.IsMinimalPrimaryDecomposition` · `Mathlib.RingTheory.Lasker`

A structure with three fields: `t.inf id = N`, the members are primary, and the decomposition is minimal. The first uniqueness theorem is `Submodule.IsMinimalPrimaryDecomposition.image_radical_eq_associated_primes`, where `Submodule.associatedPrimes` is the set of primes `(N.colon {x}).radical`. The corollary is `Ideal.IsMinimalPrimaryDecomposition.minimalPrimes_subset_image_radical`.

<?decl Submodule.IsMinimalPrimaryDecomposition?>
:::

### Examples

**Example (A decomposition with an embedded prime).** Let $R = k[x, y]$ and $I = (x^2, xy)$. Then
$$I = (x) \cap (x^2, y) = (x) \cap (x, y)^2.$$
An element $xg$ of $(x)$ lies in $(x^2, y)$, or in $(x, y)^2$, exactly when $g \in (x, y)$, that is, when $xg \in (x^2, xy)$. The ideal $(x)$ is prime, and $(x^2, y)$ and $(x, y)^2$ have the maximal radical $(x, y)$, so they are primary. Both decompositions are minimal and differ, but the radicals agree: $(I : x) = (x, y)$ and $(I : y) = (x)$. The minimal prime is $(x)$, and $(x, y)$ is embedded.

**Counterexample (A ring without primary decompositions).** Let $R = \prod_{n \in \mathbb{N}} \mathbb{F}_2$. Every element satisfies $x^2 = x$, so $r(q) = q$ for every ideal $q$, and a primary ideal is prime. A prime $p$ gives a domain $R/p$ in which every element satisfies $x^2 = x$, so $R/p \cong \mathbb{F}_2$ and $p$ is maximal. If $0 = m_1 \cap \cdots \cap m_k$ with distinct maximal $m_i$, then the Chinese remainder theorem of Chapter 1 gives $R \cong \mathbb{F}_2^k$, which is finite. But $R$ is infinite. So the zero ideal has no primary decomposition, and the Lasker-Noether theorem needs the Noetherian hypothesis.

### The library around it

Mathlib states the theory for submodules, and ideals are the case `M = R`. The radical of a primary submodule `J` is `(J.colon Set.univ).radical`.

Common errors of a learner:

- A primary decomposition is a `Finset`, so repeated members merge.
- `Ideal.IsPrimary.inf` needs equal radicals. With different radicals the intersection is usually not primary.

### Exercises

1. (A) Find a minimal primary decomposition of $(360)$ in $\mathbb{Z}$ and of $(x^2(x - 1))$ in $k[x]$.
2. (A) Show that $(4, x)$ is primary in $\mathbb{Z}[x]$, and that $(4, 2x)$ is not. Hint: $2 \cdot x$.
3. (A) Show that a primary ideal of $\mathbb{Z}$ is $0$ or $(p^e)$ with $p$ prime.
4. (B) Show that $(x^2, xy) = (x) \cap (x^2, y + cx)$ for every $c \in k$. So $(x^2, xy)$ has infinitely many minimal primary decompositions. Hint: $k[x, y]/(x^2, y + cx) \cong k[x]/(x^2)$.
5. (B) Let $R$ be Noetherian. Show that the set of zero divisors of $R$ is the union of the associated primes of $0$. Hint: $x$ is a zero divisor exactly when $(0 : x) \ne 0$.
6. (B) Find a minimal primary decomposition of $(xy, xz, yz)$ in $k[x, y, z]$.
7. (C) Let $q$ be $p$-primary in a Noetherian ring. Show that $p^n \subseteq q$ for some $n$, and that the symbolic power $p^{(n)} = p^n R_p \cap R$ is $p$-primary. Hint: Chapter 2 for the localization.

### Notes and history

Emanuel Lasker proved the existence of primary decompositions for polynomial rings in 1905. Emmy Noether proved it for all rings with the ascending chain condition in 1921, by the method of irreducible ideals. Atiyah and Macdonald, Chapter 4, also prove the second uniqueness theorem, with localization.

### Reference

<?reference?>
