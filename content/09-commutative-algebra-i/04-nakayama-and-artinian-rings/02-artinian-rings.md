---
title: Artinian rings
kind: theory
modules:
  - Mathlib.RingTheory.Artinian.Defs
  - Mathlib.RingTheory.Artinian.Module
  - Mathlib.RingTheory.Artinian.Ring
explains:
  E3: [IsArtinian, IsArtinianRing, IsArtinianRing.isField_of_isDomain, IsArtinianRing.setOfPred_isMaximal_finite, IsArtinianRing.isNilpotent_jacobson]
  E2: [isArtinianRing_iff, set_has_minimal_iff_artinian, monotone_stabilizes_iff_artinian, IsArtinian.set_has_minimal, IsArtinian.induction, isArtinian_of_range_eq_ker, isArtinian_of_quotient_of_artinian, isArtinian_of_fg_of_artinian, IsArtinianRing.isPrime_iff_isMaximal, IsArtinianRing.isMaximal_of_isPrime, IsArtinianRing.instFiniteMaximalSpectrum, IsArtinianRing.isNilpotent_nilradical, IsArtinianRing.jacobson_eq_radical, IsArtinianRing.of_finite, Function.Surjective.isArtinianRing, IsArtinianRing.localization_artinian, IsArtinian.surjective_of_injective_endomorphism, IsArtinianRing.isUnit_iff_mem_nonZeroDivisors]
  E1: auto
families: []
requires: [V07.C01, V07.C02, V09.C01, V09.C02, V09.C03]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Artinian rings

### Overview

Chapter 3 studied the ascending chain condition. This section turns the chains around. A module is Artinian if every descending chain of submodules stops. Finite rings, the rings $\mathbb{Z}/n$, and finite-dimensional algebras over a field are Artinian. The ring $\mathbb{Z}$ is not, because $(2) \supsetneq (4) \supsetneq (8) \supsetneq \cdots$ does not stop.

For rings the descending chain condition is much stronger. In an Artinian ring every prime ideal is maximal, there are only finitely many maximal ideals, and the Jacobson radical is nilpotent. Section 3 uses these three facts.

### Definitions

In this section $R$ is a commutative ring and $M$ is an $R$-module.

**Definition (Descending chain condition).** The module $M$ satisfies the descending chain condition (DCC) if every chain $N_1 \supseteq N_2 \supseteq \cdots$ of submodules is eventually constant.

**Definition (Minimal condition).** The module $M$ satisfies the minimal condition if every nonempty set of submodules has a minimal element.

**Definition (Artinian module, Artinian ring).** The module $M$ is Artinian if it satisfies the DCC. The ring $R$ is Artinian if it is Artinian as a module over itself, that is, if every descending chain of ideals stops.

::: mathlib
`IsArtinian` · `Mathlib.RingTheory.Artinian.Defs`

An abbreviation for `WellFoundedLT (Submodule R M)`, so there is no infinite strictly descending chain of submodules. `IsArtinian.induction` is the induction on submodules from below.

<?decl IsArtinian?>
:::

::: mathlib
`IsArtinianRing` · `Mathlib.RingTheory.Artinian.Defs`

An abbreviation for `IsArtinian R R`, and `isArtinianRing_iff` states it.

<?decl IsArtinianRing?>
:::

### Theorems and proofs

**Theorem (Two forms of the Artinian condition).** The module $M$ satisfies the DCC if and only if it satisfies the minimal condition.

*Proof.* Assume the DCC, and let $\mathcal{S}$ be a nonempty set of submodules without a minimal element. By dependent choice there is a chain $N_1 \supsetneq N_2 \supsetneq \cdots$ in $\mathcal{S}$, which contradicts the DCC. Conversely, assume the minimal condition and let $N_1 \supseteq N_2 \supseteq \cdots$ be a chain. The set $\{N_k\}$ has a minimal element $N_n$. For $k \ge n$, $N_k \subseteq N_n$, and minimality gives $N_k = N_n$. $\square$

::: mathlib
`set_has_minimal_iff_artinian` · `Mathlib.RingTheory.Artinian.Module`

The minimal condition, with `∃ M' ∈ a, ∀ I ∈ a, ¬I < M'`. The DCC for a sequence is `monotone_stabilizes_iff_artinian`, with a monotone map into the order dual `(Submodule R M)ᵒᵈ`.

<?decl set_has_minimal_iff_artinian?>
:::

**Theorem (Exact sequences).** Let $0 \to M' \xrightarrow{f} M \xrightarrow{g} M'' \to 0$ be exact. Then $M$ is Artinian if and only if $M'$ and $M''$ are Artinian.

*Proof.* If $M$ is Artinian, a descending chain $L_k$ in $M'$ gives the chain $f(L_k)$ in $M$, and a descending chain $L_k$ in $M''$ gives the chain $g^{-1}(L_k)$. These stop, and $L_k = f^{-1}(f(L_k))$, $L_k = g(g^{-1}(L_k))$ recover the first chains. Conversely, let $N_1 \supseteq N_2 \supseteq \cdots$ be a chain in $M$. The chains $f^{-1}(N_k)$ and $g(N_k)$ stop, so for some $n$ and all $k \ge n$, $N_k \subseteq N_n$ with $f^{-1}(N_k) = f^{-1}(N_n)$ and $g(N_k) = g(N_n)$. Chapter 3, Section 1 proves that two submodules $N \subseteq N'$ with $f^{-1}(N) = f^{-1}(N')$ and $g(N) = g(N')$ are equal. So $N_k = N_n$. $\square$

::: mathlib
`isArtinian_of_range_eq_ker` · `Mathlib.RingTheory.Artinian.Module`

The extension half, with the same hypotheses as `isNoetherian_of_range_eq_ker` of Chapter 3. The quotient half is the instance `isArtinian_of_quotient_of_artinian`.

<?decl isArtinian_of_range_eq_ker?>
:::

**Corollary (Constructions).** Let $R$ be Artinian. Then every finitely generated $R$-module is Artinian, and $R/I$ and every image of $R$ under a surjective ring homomorphism are Artinian rings. Every finite-dimensional algebra $A$ over a field $k$ is an Artinian ring.

*Proof.* As in Chapter 3, Section 1, $R^n$ is Artinian by induction with the exact sequence $0 \to R \to R^n \to R^{n-1} \to 0$, and a finitely generated module is a quotient of some $R^n$. The ideals of $R/I$ correspond to the ideals of $R$ that contain $I$, by an inclusion-preserving bijection. For $A$: every ideal of $A$ is a $k$-subspace. In a strictly descending chain of subspaces the dimension decreases strictly, so the chain has at most $\dim_k A + 1$ terms. $\square$

**Theorem (Artinian domains).** An Artinian domain is a field.

*Proof.* Let $x \ne 0$. The chain $(x) \supseteq (x^2) \supseteq \cdots$ stops, so $(x^n) = (x^{n+1})$ for some $n$. Then $x^n = x^{n+1} y$ for some $y$, so $x^n(1 - xy) = 0$. Since $x^n \ne 0$ in a domain, $xy = 1$. $\square$

**Corollary (Primes are maximal).** In an Artinian ring every prime ideal is maximal. So the nilradical equals the Jacobson radical.

*Proof.* If $p$ is prime, then $R/p$ is an Artinian domain, hence a field, and $p$ is maximal. By Chapter 1, Section 2, the nilradical is the intersection of the prime ideals and the Jacobson radical is the intersection of the maximal ideals. These are the same sets of ideals. $\square$

::: mathlib
`IsArtinianRing.isField_of_isDomain` · `Mathlib.RingTheory.Artinian.Module`

The theorem, with conclusion `IsField R`. The corollary is `IsArtinianRing.isPrime_iff_isMaximal` and the instance `IsArtinianRing.isMaximal_of_isPrime`. The equality of the radicals is `IsArtinianRing.jacobson_eq_radical`, in the form `I.jacobson = I.radical` for every ideal `I`.

<?decl IsArtinianRing.isField_of_isDomain?>
:::

**Theorem (Finitely many maximal ideals).** An Artinian ring has only finitely many maximal ideals.

*Proof.* Consider the set of all finite intersections $m_1 \cap \cdots \cap m_k$ of maximal ideals. It is nonempty, so it has a minimal element $m_1 \cap \cdots \cap m_n$. Let $m$ be any maximal ideal. Then $m \cap m_1 \cap \cdots \cap m_n$ is in the set and is contained in $m_1 \cap \cdots \cap m_n$, so they are equal by minimality. Hence $m \supseteq m_1 \cap \cdots \cap m_n \supseteq m_1 m_2 \cdots m_n$. A prime ideal that contains a product contains a factor, so $m \supseteq m_i$ for some $i$, and $m = m_i$ since $m_i$ is maximal. $\square$

::: mathlib
`IsArtinianRing.setOfPred_isMaximal_finite` · `Mathlib.RingTheory.Artinian.Module`

The statement `{I : Ideal R | I.IsMaximal}.Finite`. The instance `IsArtinianRing.instFiniteMaximalSpectrum` gives `Finite (MaximalSpectrum R)`.

<?decl IsArtinianRing.setOfPred_isMaximal_finite?>
:::

**Theorem (The Jacobson radical is nilpotent).** In an Artinian ring, $J(R)^k = 0$ for some $k$.

*Proof.* Write $J = J(R)$. The chain $J \supseteq J^2 \supseteq \cdots$ stops: $J^k = J^{k+1} = \cdots$ for some $k$. Let $a = J^k$, so $a^2 = J^{2k} = a$. Assume $a \ne 0$. Let $\mathcal{S}$ be the set of ideals $c$ with $ca \ne 0$. It contains $a$, since $a \cdot a = a \ne 0$. Let $c$ be a minimal element of $\mathcal{S}$. Some $x \in c$ has $xa \ne 0$. Then $(x) \in \mathcal{S}$ and $(x) \subseteq c$, so $c = (x)$. Next, $(xa)a = xa^2 = xa \ne 0$, so $xa \in \mathcal{S}$, and $xa \subseteq (x) = c$. So $xa = (x)$, and $x = xy$ for some $y \in a \subseteq J$. Then $x(1 - y) = 0$, and $1 - y$ is a unit by Chapter 1, so $x = 0$. This contradicts $xa \ne 0$. So $a = 0$. $\square$

Since the nilradical is $J$, the nilradical is nilpotent too: a single power $k$ kills all nilpotent elements at once.

::: mathlib
`IsArtinianRing.isNilpotent_jacobson` · `Mathlib.RingTheory.Artinian.Ring`

The statement `IsNilpotent (Ring.jacobson R)`, which holds for noncommutative Artinian rings too. The commutative form for the nilradical is `IsArtinianRing.isNilpotent_nilradical`.

<?decl IsArtinianRing.isNilpotent_jacobson?>
:::

### Examples

**Example (The ring $\mathbb{Z}/360$).** The ring $R = \mathbb{Z}/360$ is finite, so it is Artinian. Since $360 = 2^3 \cdot 3^2 \cdot 5$, the maximal ideals are $(2)$, $(3)$ and $(5)$, the images of the prime ideals of $\mathbb{Z}$ that contain $360$. The Jacobson radical is $(2) \cap (3) \cap (5) = (30)$, and it equals the nilradical. Since $30^3 = 75 \cdot 360$ and $30^2 = 900 \not\equiv 0$, $J^3 = 0$ and $J^2 \ne 0$. The least $k$ with $J^k = 0$ is $3$, the largest exponent in $360$.

**Example (Truncated polynomials).** Let $k$ be a field and $R = k[x]/(x^n)$, a $k$-algebra of dimension $n$. It is Artinian. Every element outside $(\bar x)$ is $c + \bar x g$ with $c \ne 0$, a unit since $\bar x g$ is nilpotent, so $(\bar x)$ is the only maximal ideal. Its powers $(\bar x) \supsetneq (\bar x^2) \supsetneq \cdots \supsetneq (\bar x^n) = 0$ form a chain of length $n$.

**Counterexample (Domains that are not fields).** By the theorem on Artinian domains, $\mathbb{Z}$, $k[x]$ and $\mathbb{Z}_{(p)}$ are not Artinian. For $\mathbb{Z}_{(p)}$ the chain $(p) \supsetneq (p^2) \supsetneq \cdots$ does not stop, although this ring has only one maximal ideal. So finitely many maximal ideals do not suffice for the Artinian condition.

**Counterexample (An Artinian module that is not Noetherian).** Let $p$ be prime and $M = \mathbb{Z}[1/p]/\mathbb{Z}$, the Prüfer group, as a $\mathbb{Z}$-module. Let $C_n$ be the subgroup generated by $1/p^n$, cyclic of order $p^n$. An element $a/p^n$ with $p \nmid a$ generates $C_n$, since $a$ is invertible modulo $p^n$. So a subgroup $H$ is the union of the $C_n$ that it contains. If these $C_n$ have bounded $n$, then $H = C_N$ for the largest one, and otherwise $H = M$. So the proper subgroups are the finite groups $C_n$, and a descending chain stops. The chain $C_1 \subsetneq C_2 \subsetneq \cdots$ does not stop. So $M$ is Artinian and not Noetherian. Section 3 proves that this cannot happen for a ring.

### The library around it

Instance search finds that finite rings, fields, quotients `R ⧸ I` of an Artinian ring and finite algebras over an Artinian ring are Artinian. The lemma `IsArtinianRing.of_finite` gives the last, and `Function.Surjective.isArtinianRing` gives images. Localizations of an Artinian ring are Artinian by `IsArtinianRing.localization_artinian`.

Common errors of a learner:

- Artinian rings in Mathlib may be noncommutative. Lemmas such as `IsArtinianRing.isPrime_iff_isMaximal` need `CommRing`.
- `isArtinian_iff` is deprecated. Use the definition `WellFoundedLT` or `set_has_minimal_iff_artinian`.

### Exercises

1. (A) List the maximal ideals of $\mathbb{Z}/72$, and find the least $k$ with $J^k = 0$.
2. (A) Let $M$ be Artinian and $\varphi : M \to M$ injective. Show that $\varphi$ is surjective. Hint: the chain $\operatorname{im} \varphi^n$.
3. (A) Deduce from Exercise 2 that in an Artinian ring every non-zero-divisor is a unit.
4. (B) Show that a product $R_1 \times R_2$ is Artinian if and only if $R_1$ and $R_2$ are.
5. (B) Let $R$ be Artinian and reduced. Show that $R$ is a finite product of fields. Hint: $J = 0$, so $m_1 \cap \cdots \cap m_n = 0$, and the Chinese remainder theorem of Chapter 1.
6. (B) Let $R$ be Artinian and $S$ a multiplicative set. Show that $S^{-1}R$ is Artinian. Hint: as in Chapter 3, every ideal of $S^{-1}R$ is the extension of its contraction.
7. (C) Show that the Prüfer group is an Artinian $\mathbb{Z}$-module whose endomorphism ring is the ring $\mathbb{Z}_p$ of $p$-adic integers, and that multiplication by $p$ is surjective and not injective.

### Notes and history

The descending chain condition is named after Emil Artin, who studied rings with the minimum condition on left ideals in 1927. This section follows Atiyah and Macdonald, *Introduction to Commutative Algebra*, Chapter 8.

### Reference

<?reference?>
