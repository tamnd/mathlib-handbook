---
title: The prime spectrum
kind: theory
modules: []
explains:
  E3: []
  E2: [Ideal.radical_le_radical_iff, Ideal.radical_eq_top, Ideal.IsPrime.radical]
  E1: [PrimeSpectrum, PrimeSpectrum.asIdeal, PrimeSpectrum.zeroLocus, PrimeSpectrum.mem_zeroLocus, PrimeSpectrum.vanishingIdeal, PrimeSpectrum.zariskiTopology, PrimeSpectrum.basicOpen, PrimeSpectrum.mem_basicOpen, PrimeSpectrum.isClosed_iff_zeroLocus, PrimeSpectrum.isClosed_zeroLocus, PrimeSpectrum.zeroLocus_span, PrimeSpectrum.zeroLocus_radical, PrimeSpectrum.zeroLocus_sup, PrimeSpectrum.zeroLocus_iSup, PrimeSpectrum.zeroLocus_mul, PrimeSpectrum.zeroLocus_inf, PrimeSpectrum.zeroLocus_bot, PrimeSpectrum.zeroLocus_empty_iff_eq_top, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff, PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, PrimeSpectrum.basicOpen_eq_zeroLocus_compl, PrimeSpectrum.basicOpen_mul, PrimeSpectrum.basicOpen_eq_bot_iff, PrimeSpectrum.isTopologicalBasis_basic_opens, PrimeSpectrum.compactSpace, PrimeSpectrum.iSup_basicOpen_eq_top_iff, PrimeSpectrum.isCompact_basicOpen, PrimeSpectrum.comap, PrimeSpectrum.localization_away_comap_range, PrimeSpectrum.localization_comap_range, PrimeSpectrum.isClosedEmbedding_comap_of_surjective, PrimeSpectrum.closure_singleton, PrimeSpectrum.isClosed_singleton_iff_isMaximal, PrimeSpectrum.isIrreducible_zeroLocus_iff, PrimeSpectrum.le_iff_mem_closure]
families: []
requires: [V09.C01, V13]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The prime spectrum

### Overview

A polynomial $f \in \mathbb{C}[x]$ vanishes at $a$ when $f \in (x - a)$. The prime spectrum extends this picture to any commutative ring: its points are the prime ideals, $f$ vanishes at $\mathfrak{p}$ when $f \in \mathfrak{p}$, and the closed sets are the zero sets $V(E)$. The radicals of Chapter 1 describe the closed sets, and the localizations of this chapter describe the basic open sets $D(f)$. The section uses the definition of a topological space and of a basis from Volume 13.

### Definitions

**Definition (Prime spectrum).** $\operatorname{Spec} R$ is the set of prime ideals of $R$.

**Definition (Zero locus and basic open set).** For a subset $E \subseteq R$,
$$V(E) = \{ \mathfrak{p} \in \operatorname{Spec} R : E \subseteq \mathfrak{p} \}.$$
For $f \in R$, $D(f) = \operatorname{Spec} R \setminus V(\{f\}) = \{ \mathfrak{p} : f \notin \mathfrak{p} \}$.

**Definition (Irreducible).** A topological space $X$ is irreducible if it is nonempty and it is not the union of two closed subsets different from $X$. A subset is irreducible if it is irreducible in the subspace topology.

::: mathlib
`PrimeSpectrum` · `Mathlib.RingTheory.Spectrum.Prime.Defs`

`PrimeSpectrum R` is a structure with the field `asIdeal : Ideal R` and a proof that it is prime. The zero locus is `PrimeSpectrum.zeroLocus s` for `s : Set R`, with `PrimeSpectrum.mem_zeroLocus : x ∈ zeroLocus s ↔ s ⊆ x.asIdeal`. The other direction is `PrimeSpectrum.vanishingIdeal`, the intersection of the primes in a set of points.

<?decl PrimeSpectrum?>
:::

### Theorems and proofs

**Theorem (Rules for $V$).** Let $E \subseteq R$, and let $I$, $J$, $I_\lambda$ be ideals.

1. $V(E) = V((E)) = V(\sqrt{(E)})$.
2. $V(0) = \operatorname{Spec} R$ and $V(R) = \emptyset$.
3. $V(\sum_\lambda I_\lambda) = \bigcap_\lambda V(I_\lambda)$.
4. $V(I \cap J) = V(I J) = V(I) \cup V(J)$.

Consequently the sets $V(E)$ are the closed sets of a topology on $\operatorname{Spec} R$, the Zariski topology.

*Proof.* (1) A prime contains $E$ if and only if it contains the ideal $(E)$, and it contains $I$ if and only if it contains $\sqrt{I}$, since primes are radical (Chapter 1, Section 2).

(2) Each prime contains $0$, and no prime contains $1$.

(3) A prime contains each $I_\lambda$ if and only if it contains their sum.

(4) From $I J \subseteq I \cap J \subseteq I$ and $\subseteq J$ follows $V(I) \cup V(J) \subseteq V(I \cap J) \subseteq V(I J)$. Let $I J \subseteq \mathfrak{p}$ and $I \not\subseteq \mathfrak{p}$, with $a \in I \setminus \mathfrak{p}$. For $b \in J$, $a b \in \mathfrak{p}$ gives $b \in \mathfrak{p}$. So $J \subseteq \mathfrak{p}$.

By (1) each $V(E)$ is a $V(I)$ for an ideal $I$. By (2), (3), (4) these sets contain $\emptyset$ and $\operatorname{Spec} R$ and are closed under arbitrary intersections and finite unions. These are the axioms for closed sets (Volume 13). $\square$

::: mathlib
`PrimeSpectrum.zariskiTopology` · `Mathlib.RingTheory.Spectrum.Prime.Topology`

The instance `TopologicalSpace (PrimeSpectrum R)`, defined by its closed sets, so that `PrimeSpectrum.isClosed_iff_zeroLocus : IsClosed Z ↔ ∃ s, Z = zeroLocus s`. The rules of the theorem are `PrimeSpectrum.zeroLocus_span`, `PrimeSpectrum.zeroLocus_radical`, `PrimeSpectrum.zeroLocus_bot`, `PrimeSpectrum.zeroLocus_iSup`, `PrimeSpectrum.zeroLocus_sup`, `PrimeSpectrum.zeroLocus_inf` and `PrimeSpectrum.zeroLocus_mul`.

<?decl PrimeSpectrum.zariskiTopology?>
:::

**Theorem (Closed sets and radicals).** For ideals $I, J$ of $R$, $V(I) \subseteq V(J)$ if and only if $\sqrt{J} \subseteq \sqrt{I}$. Consequently $V(I) = \emptyset$ if and only if $I = R$, and $I \mapsto V(I)$ is an inclusion-reversing bijection from the radical ideals of $R$ onto the closed subsets of $\operatorname{Spec} R$.

*Proof.* Let $\sqrt{J} \subseteq \sqrt{I}$ and $\mathfrak{p} \in V(I)$. Then $J \subseteq \sqrt{J} \subseteq \sqrt{I} \subseteq \mathfrak{p}$. Conversely let $V(I) \subseteq V(J)$. By Chapter 1, Section 2, $\sqrt{I}$ is the intersection of the primes in $V(I)$. Each of them contains $J$, so $J \subseteq \sqrt{I}$ and $\sqrt{J} \subseteq \sqrt{\sqrt{I}} = \sqrt{I}$.

$V(I) = \emptyset = V(R)$ means $\sqrt{I} = \sqrt{R} = R$, that is, $I = R$. For radical ideals, $V(I) = V(J)$ gives $I = \sqrt{I} = \sqrt{J} = J$, so the map is injective. It is surjective by part (1) of the previous theorem. $\square$

::: mathlib
`Ideal.radical_le_radical_iff` · `Mathlib.RingTheory.Ideal.Operations`

The algebra behind the theorem: `I.radical ≤ J.radical ↔ I ≤ J.radical`, `Ideal.radical_eq_top : I.radical = ⊤ ↔ I = ⊤` and `Ideal.IsPrime.radical`. The topological forms are `PrimeSpectrum.zeroLocus_subset_zeroLocus_iff : zeroLocus I ⊆ zeroLocus J ↔ J ≤ I.radical`, `PrimeSpectrum.zeroLocus_empty_iff_eq_top` and `PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical`.

<?decl Ideal.radical_le_radical_iff?>
:::

**Theorem (Basic open sets).** Let $f, g \in R$.

1. $D(f) \cap D(g) = D(f g)$.
2. $D(f) = \emptyset$ if and only if $f$ is nilpotent.
3. The sets $D(f)$ form a basis of the Zariski topology.

*Proof.* (1) A prime misses $f g$ if and only if it misses $f$ and $g$.

(2) $D(f) = \emptyset$ means that $f$ lies in every prime, that is, in $\mathfrak{N}(R)$ (Chapter 1, Section 2).

(3) Each $D(f)$ is open. Let $U$ be open and $\mathfrak{p} \in U$. Then $U = \operatorname{Spec} R \setminus V(E)$ for some $E$, and $\mathfrak{p} \notin V(E)$, so some $f \in E$ misses $\mathfrak{p}$. Then $\mathfrak{p} \in D(f)$, and $D(f) \subseteq U$, since a prime that misses $f$ does not contain $E$. $\square$

**Theorem (Quasi-compactness).** Let $(f_i)_{i \in \Lambda}$ be elements of $R$. Then $\operatorname{Spec} R = \bigcup_i D(f_i)$ if and only if the $f_i$ generate the unit ideal. In that case finitely many $D(f_i)$ cover $\operatorname{Spec} R$. So $\operatorname{Spec} R$ is quasi-compact.

*Proof.* $\bigcup_i D(f_i)$ is the complement of $V(\{f_i\})$. So it is all of $\operatorname{Spec} R$ if and only if $V(\{f_i\}) = \emptyset$, that is, $(f_i : i \in \Lambda) = R$ by the previous theorems. Then $1 = a_1 f_{i_1} + \dots + a_n f_{i_n}$ for finitely many indices, so $f_{i_1}, \dots, f_{i_n}$ generate $R$ and $D(f_{i_1}), \dots, D(f_{i_n})$ cover. For an arbitrary open cover, cover each member by basic open sets, choose finitely many of them, and choose for each one a member of the cover that contains it. $\square$

::: mathlib
`PrimeSpectrum.compactSpace` · `Mathlib.RingTheory.Spectrum.Prime.Topology`

The instance `CompactSpace (PrimeSpectrum R)`. In Mathlib "compact" means quasi-compact, with no Hausdorff condition. The basic open set is `PrimeSpectrum.basicOpen f : Opens (PrimeSpectrum R)`, with `PrimeSpectrum.mem_basicOpen`, `PrimeSpectrum.basicOpen_eq_zeroLocus_compl`, `PrimeSpectrum.basicOpen_mul`, `PrimeSpectrum.basicOpen_eq_bot_iff` and `PrimeSpectrum.isTopologicalBasis_basic_opens`. The covering criterion is `PrimeSpectrum.iSup_basicOpen_eq_top_iff`, and `PrimeSpectrum.isCompact_basicOpen` says that each $D(f)$ is quasi-compact too.

<?decl PrimeSpectrum.compactSpace?>
:::

**Theorem (Points and closures).** For $\mathfrak{p} \in \operatorname{Spec} R$, the closure of $\{\mathfrak{p}\}$ is $V(\mathfrak{p})$. So $\mathfrak{q}$ lies in the closure of $\{\mathfrak{p}\}$ if and only if $\mathfrak{p} \subseteq \mathfrak{q}$, and $\{\mathfrak{p}\}$ is closed if and only if $\mathfrak{p}$ is maximal.

*Proof.* $V(\mathfrak{p})$ is closed and contains $\mathfrak{p}$. If $V(E)$ contains $\mathfrak{p}$, then $E \subseteq \mathfrak{p}$, so each prime that contains $\mathfrak{p}$ contains $E$, and $V(\mathfrak{p}) \subseteq V(E)$. So $V(\mathfrak{p})$ is the least closed set that contains $\mathfrak{p}$. The point is closed if and only if $V(\mathfrak{p}) = \{\mathfrak{p}\}$, that is, no prime strictly contains $\mathfrak{p}$. Since each proper ideal lies in a maximal ideal, this means $\mathfrak{p}$ is maximal. $\square$

**Theorem (Irreducible closed sets).** $V(I)$ is irreducible if and only if $\sqrt{I}$ is prime. So the irreducible closed sets are the closures of points, and each one is the closure of exactly one point.

*Proof.* Let $\mathfrak{p} = \sqrt{I}$ be prime. Then $V(I) = V(\mathfrak{p})$ is the closure of $\{\mathfrak{p}\}$. It is nonempty. If $V(\mathfrak{p}) = Z_1 \cup Z_2$ with $Z_1, Z_2$ closed, then $\mathfrak{p}$ lies in $Z_1$, say, and then the closure $V(\mathfrak{p})$ lies in $Z_1$. So $V(\mathfrak{p})$ is irreducible.

Conversely let $V(I)$ be irreducible. It is nonempty, so $I \ne R$ and $\sqrt{I} \ne R$. Let $a b \in \sqrt{I}$. By the rules for $V$,
$$V(I) = V(\sqrt{I}) \subseteq V(a b) = V(a) \cup V(b), \qquad V(I) = V(I + (a)) \cup V(I + (b)).$$
By irreducibility $V(I) = V(I + (a))$, say. By the theorem on radicals, $a \in \sqrt{I + (a)} \subseteq \sqrt{I}$. So $\sqrt{I}$ is prime. If $V(\mathfrak{p}) = V(\mathfrak{q})$ for primes, then $\mathfrak{p} = \mathfrak{q}$ by the bijection with radical ideals. $\square$

::: mathlib
`PrimeSpectrum.isIrreducible_zeroLocus_iff` · `Mathlib.RingTheory.Spectrum.Prime.Topology`

The theorem as `IsIrreducible (zeroLocus I) ↔ I.radical.IsPrime`. The previous theorem is `PrimeSpectrum.closure_singleton : closure {x} = zeroLocus x.asIdeal`, `PrimeSpectrum.le_iff_mem_closure` and `PrimeSpectrum.isClosed_singleton_iff_isMaximal`.

<?decl PrimeSpectrum.isIrreducible_zeroLocus_iff?>
:::

**Theorem (Functoriality).** A ring homomorphism $\varphi : R \to S$ gives a continuous map $\varphi^* : \operatorname{Spec} S \to \operatorname{Spec} R$, $\mathfrak{q} \mapsto \varphi^{-1}(\mathfrak{q})$.

1. If $\varphi$ is surjective with kernel $I$, then $\varphi^*$ is a homeomorphism onto the closed set $V(I)$.
2. If $\varphi = \iota : R \to S^{-1} R$, then $\varphi^*$ is injective with image the set of primes that miss $S$. For $R_f$ the image is $D(f)$.

*Proof.* The preimage of a prime is prime, and $(\varphi^*)^{-1}(V(E)) = V(\varphi(E))$, so $\varphi^*$ is continuous.

(1) By the correspondence theorem (Volume 6, Chapter 2), $\mathfrak{q} \mapsto \varphi^{-1}(\mathfrak{q})$ is a bijection from the primes of $S$ onto the primes of $R$ that contain $I$. It sends $V(J)$ to $V(\varphi^{-1}(J))$, a closed set, so $\varphi^*$ is closed. A continuous closed injection is a homeomorphism onto its image.

(2) This is the theorem on primes of Section 2. A prime misses $\{1, f, f^2, \dots\}$ if and only if it misses $f$. $\square$

::: mathlib
`PrimeSpectrum.comap` · `Mathlib.RingTheory.Spectrum.Prime.RingHom`

`PrimeSpectrum.comap φ` is the map $\varphi^*$. Part (1) is `PrimeSpectrum.isClosedEmbedding_comap_of_surjective`. Part (2) is `PrimeSpectrum.localization_comap_range`, with image `{p | Disjoint ↑M ↑p.asIdeal}`, and `PrimeSpectrum.localization_away_comap_range`, with image `basicOpen r`.

<?decl PrimeSpectrum.comap?>
:::

### Examples

**Example ($\operatorname{Spec} \mathbb{Z}$).** The points are $(0)$ and $(p)$ for primes $p$. For $n \ne 0$, $V(n)$ is the finite set of primes dividing $n$, and $V(0)$ is everything. So the closed sets are the finite sets of nonzero primes and the whole space. The closure of $(0)$ is $V(0) = \operatorname{Spec} \mathbb{Z}$.

**Counterexample (A point that is not closed).** In $\operatorname{Spec} \mathbb{Z}$ the point $(0)$ is not closed, since $(0)$ is not maximal. Any open set that contains $(2)$ also contains $(0)$, so the two points cannot be separated, and $\operatorname{Spec} \mathbb{Z}$ is not Hausdorff.

**Counterexample ($V$ does not see the radical).** In $\mathbb{Z}$, $V(4) = V(2) = \{(2)\}$, but $(4) \ne (2)$. The bijection between ideals and closed sets needs radical ideals: $\sqrt{(4)} = (2)$.

### The library around it

The files `Mathlib.RingTheory.Spectrum.Prime.*` have their home in Volume 10, which proves further facts. Common errors:

- A point `x : PrimeSpectrum R` is not an ideal. Use `x.asIdeal`, and build a point from a prime `p` as `⟨p, hp⟩`.
- `basicOpen f` is an element of `Opens`, not a `Set`. Coerce it with `↑` before a set lemma.

### Exercises

1. (A) Describe $\operatorname{Spec} \mathbb{Z}/360$ and its topology.
2. (A) Show that $D(f) = \operatorname{Spec} R$ if and only if $f$ is a unit.
3. (B) Show that $D(f) \subseteq D(g)$ if and only if $f \in \sqrt{(g)}$.
4. (B) Show that $D(f)$ is quasi-compact. Hint: if $D(f) \subseteq \bigcup_i D(g_i)$, then $f$ lies in the radical of $(g_i : i)$.
5. (C) Show that the irreducible components of $\operatorname{Spec} R$ are the sets $V(\mathfrak{p})$ for minimal primes $\mathfrak{p}$. Hint: use Chapter 1, Section 2.
6. (C) Show that $\operatorname{Spec} R$ is disconnected if and only if $R$ has an idempotent $e \ne 0, 1$. Hint: for the converse, write $\operatorname{Spec} R = V(I) \cup V(J)$ disjointly with both parts nonempty. Then $I + J = R$ and $I J \subseteq \mathfrak{N}(R)$, so $a + b = 1$ with $a \in I$, $b \in J$, $(a b)^n = 0$. Write $1 = r a^n + s b^n$ by Chapter 1, Section 1, and take $e = r a^n$.

### Notes and history

Grothendieck made the prime spectrum the base of the theory of schemes. The topology carries the name of Oscar Zariski, who used it earlier on algebraic varieties.

### Reference

<?reference?>
