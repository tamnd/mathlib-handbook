---
title: Noetherian rings and modules
kind: theory
modules:
  - Mathlib.RingTheory.Noetherian.Defs
  - Mathlib.RingTheory.Noetherian.Basic
  - Mathlib.RingTheory.Ideal.Quotient.Noetherian
  - Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
explains:
  E3: [IsNoetherian, IsNoetherianRing, set_has_maximal_iff_noetherian, isNoetherian_of_range_eq_ker]
  E2: [isNoetherian_iff, isNoetherian_def, isNoetherianRing_iff_ideal_fg, monotone_stabilizes_iff_noetherian, IsNoetherian.induction, isNoetherian_of_isNoetherianRing_of_finite, isNoetherian_quotient, isNoetherian_pi, isNoetherian_of_le, Ideal.Quotient.isNoetherianRing, isNoetherianRing_of_surjective, IsLocalization.isNoetherianRing, IsNoetherianRing.wfDvdMonoid]
  E1: auto
families: []
requires: [V06.C02, V06.C06, V07.C01, V09.C01, V09.C02]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Noetherian rings and modules

### Overview

Volume 6, Chapter 6 used one finiteness property of a principal ideal domain to prove the existence of factorizations: every ascending chain of ideals is eventually constant. This section takes that property as a definition, proves three equivalent forms of it, and shows that it passes to submodules, quotients, extensions, quotient rings and localizations.

### Definitions

In this section $R$ is a commutative ring and $M$ is an $R$-module. A submodule $N$ of $M$ is finitely generated if $N = Rx_1 + \cdots + Rx_n$ for some $x_1, \dots, x_n \in N$.

**Definition (Ascending chain condition).** The module $M$ satisfies the ascending chain condition (ACC) if every chain $N_1 \subseteq N_2 \subseteq N_3 \subseteq \cdots$ of submodules of $M$ is eventually constant: there is an $n$ with $N_k = N_n$ for all $k \ge n$.

**Definition (Maximal condition).** The module $M$ satisfies the maximal condition if every nonempty set $\mathcal{S}$ of submodules of $M$ has a maximal element: an $N_0 \in \mathcal{S}$ such that no $N \in \mathcal{S}$ satisfies $N_0 \subsetneq N$.

**Definition (Noetherian module, Noetherian ring).** The module $M$ is Noetherian if every submodule of $M$ is finitely generated. The ring $R$ is Noetherian if it is Noetherian as a module over itself, that is, if every ideal of $R$ is finitely generated.

::: mathlib
`IsNoetherian` · `Mathlib.RingTheory.Noetherian.Defs`

A class with one field `noetherian : ∀ s : Submodule R M, s.FG`, so Mathlib takes the definition by finite generation. The ACC is `isNoetherian_iff`: `IsNoetherian R M ↔ WellFoundedGT (Submodule R M)`.

<?decl IsNoetherian?>
:::

::: mathlib
`IsNoetherianRing` · `Mathlib.RingTheory.Noetherian.Defs`

An abbreviation for `IsNoetherian R R`, so every lemma about Noetherian modules applies to the ring. The lemma `isNoetherianRing_iff_ideal_fg` states it with ideals.

<?decl IsNoetherianRing?>
:::

### Theorems and proofs

**Theorem (Three forms of the Noetherian condition).** For an $R$-module $M$ the following are equivalent:

1. every submodule of $M$ is finitely generated;
2. $M$ satisfies the ACC;
3. $M$ satisfies the maximal condition.

*Proof.* (1) implies (2). Let $N_1 \subseteq N_2 \subseteq \cdots$ be a chain and $N = \bigcup_k N_k$. Then $N$ is a submodule, because two elements of $N$ lie in one $N_k$. By (1), $N = Rx_1 + \cdots + Rx_m$. Each $x_i$ lies in some $N_{k_i}$. Let $n = \max_i k_i$. Then all $x_i$ lie in $N_n$, so $N \subseteq N_n \subseteq N_k \subseteq N$ for $k \ge n$. Thus $N_k = N_n$ for $k \ge n$.

(2) implies (3). Let $\mathcal{S}$ be a nonempty set of submodules with no maximal element. Then every $N \in \mathcal{S}$ has a strictly larger $N' \in \mathcal{S}$. By dependent choice there is a chain $N_1 \subsetneq N_2 \subsetneq \cdots$ in $\mathcal{S}$, which contradicts (2).

(3) implies (1). Let $N$ be a submodule, and let $\mathcal{S}$ be the set of finitely generated submodules contained in $N$. It contains $0$, so it is nonempty. Let $N_0$ be a maximal element. If $N_0 \ne N$, pick $x \in N \setminus N_0$. Then $N_0 + Rx$ is finitely generated, it is contained in $N$, and it is strictly larger than $N_0$. This contradicts the maximality of $N_0$. So $N = N_0$ is finitely generated. $\square$

::: mathlib
`set_has_maximal_iff_noetherian` · `Mathlib.RingTheory.Noetherian.Defs`

The maximal condition: every nonempty `a : Set (Submodule R M)` has an `M' ∈ a` with `¬M' < I` for all `I ∈ a`. The ACC for a monotone map `ℕ →o Submodule R M` is `monotone_stabilizes_iff_noetherian`.

<?decl set_has_maximal_iff_noetherian?>
:::

The maximal condition gives Noetherian induction: to prove $P$ for all submodules, take a maximal counterexample $N$, and derive $P(N)$ from $P$ for the larger submodules. Mathlib has it as `IsNoetherian.induction`.

**Theorem (Exact sequences).** Let $0 \to M' \xrightarrow{f} M \xrightarrow{g} M'' \to 0$ be an exact sequence of $R$-modules: $f$ is injective, $g$ is surjective, and $\operatorname{im} f = \ker g$. Then $M$ is Noetherian if and only if $M'$ and $M''$ are Noetherian.

*Proof.* Assume $M$ is Noetherian. A chain $L_k$ in $M'$ gives the chain $f(L_k)$ in $M$, which stops, and $L_k = f^{-1}(f(L_k))$ since $f$ is injective. A chain $L_k$ in $M''$ gives the chain $g^{-1}(L_k)$, which stops, and $L_k = g(g^{-1}(L_k))$ since $g$ is surjective.

Conversely, assume $M'$ and $M''$ are Noetherian, and let $N_1 \subseteq N_2 \subseteq \cdots$ be a chain in $M$. The chains $f^{-1}(N_k)$ in $M'$ and $g(N_k)$ in $M''$ stop, so there is an $n$ with $f^{-1}(N_k) = f^{-1}(N_n)$ and $g(N_k) = g(N_n)$ for all $k \ge n$. It remains to prove: if $N \subseteq N'$ are submodules with $f^{-1}(N) = f^{-1}(N')$ and $g(N) = g(N')$, then $N = N'$. Let $x \in N'$. Since $g(x) \in g(N)$, there is $y \in N$ with $g(x) = g(y)$. Then $x - y \in \ker g = \operatorname{im} f$, so $x - y = f(z)$ for some $z \in M'$. Now $f(z) = x - y \in N'$, so $z \in f^{-1}(N') = f^{-1}(N)$, and $f(z) \in N$. Thus $x = y + f(z) \in N$. $\square$

::: mathlib
`isNoetherian_of_range_eq_ker` · `Mathlib.RingTheory.Noetherian.Basic`

The extension half, with hypotheses `f.range = g.ker`, `Injective f` and `Surjective g`. The other half is `isNoetherian_quotient` and `isNoetherian_of_le`.

<?decl isNoetherian_of_range_eq_ker?>
:::

**Corollary (Finite sums and finitely generated modules).** If $M_1, \dots, M_n$ are Noetherian, then so is $M_1 \oplus \cdots \oplus M_n$. If $R$ is a Noetherian ring, then every finitely generated $R$-module is Noetherian.

*Proof.* The first claim is by induction on $n$, with the exact sequence $0 \to M_n \to M_1 \oplus \cdots \oplus M_n \to M_1 \oplus \cdots \oplus M_{n-1} \to 0$. For the second claim, let $M$ be generated by $x_1, \dots, x_n$. The map $R^n \to M$, $(r_1, \dots, r_n) \mapsto \sum r_i x_i$, is surjective. The module $R^n$ is Noetherian by the first claim, and $M$ is a quotient of $R^n$, so $M$ is Noetherian by the theorem. $\square$

::: mathlib
`isNoetherian_of_isNoetherianRing_of_finite` · `Mathlib.RingTheory.Noetherian.Basic`

An instance from `[IsNoetherianRing R] [Module.Finite R M]`. Finite products are `isNoetherian_pi`.

<?decl isNoetherian_of_isNoetherianRing_of_finite?>
:::

**Theorem (Quotients and localizations).** Let $R$ be a Noetherian ring. Then:

1. for every ideal $I$, the ring $R/I$ is Noetherian, and so is every ring $S$ with a surjective homomorphism $R \to S$;
2. for every multiplicative set $S \subseteq R$, the ring $S^{-1}R$ is Noetherian.

*Proof.* (1) By the correspondence theorem (Volume 6, Chapter 2), chains of ideals of $R/I$ correspond to chains of ideals of $R$ that contain $I$. A surjection $R \to S$ with kernel $I$ gives $S \cong R/I$.

(2) Let $\phi : R \to S^{-1}R$ be the canonical map, and let $J$ be an ideal of $S^{-1}R$. By Chapter 2, Section 2, $J$ is generated by $\phi(\phi^{-1}(J))$: each $x \in J$ has the form $\phi(a)/s$ with $a \in R$ and $s \in S$, and then $\phi(a) = s \cdot x \in J$, so $a \in \phi^{-1}(J)$ and $x = \phi(a) \cdot (1/s)$. The ideal $\phi^{-1}(J)$ of $R$ is generated by finitely many $a_1, \dots, a_n$. Every element of $\phi^{-1}(J)$ is $\sum r_i a_i$, so $J$ is generated by $\phi(a_1), \dots, \phi(a_n)$. $\square$

::: mathlib
`Ideal.Quotient.isNoetherianRing` · `Mathlib.RingTheory.Ideal.Quotient.Noetherian`

The instance for `R ⧸ I`. The general form is `isNoetherianRing_of_surjective`, and localizations are `IsLocalization.isNoetherianRing`, stated with the predicate `IsLocalization` of Chapter 2.

<?decl Ideal.Quotient.isNoetherianRing?>
:::

**Theorem (Factorization in a Noetherian domain).** In a Noetherian domain every nonzero nonunit is a product of irreducible elements.

*Proof.* A Noetherian ring satisfies the ACC on principal ideals. Volume 6, Chapter 6, Section 3 proves that a domain with the ACC on principal ideals has factorizations into irreducibles. $\square$

::: mathlib
`IsNoetherianRing.wfDvdMonoid` · `Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain`

An instance: a Noetherian domain is a `WfDvdMonoid` (Volume 6).

<?decl IsNoetherianRing.wfDvdMonoid?>
:::

### Examples

**Example ($\mathbb{Z}[\sqrt{-5}]$ is Noetherian and not a UFD).** Let $A = \mathbb{Z}[\sqrt{-5}]$. As a $\mathbb{Z}$-module, $A = \mathbb{Z} + \mathbb{Z}\sqrt{-5}$ is finitely generated, so it is a Noetherian $\mathbb{Z}$-module by the corollary. An ideal $I$ of $A$ is a $\mathbb{Z}$-submodule, so it is generated over $\mathbb{Z}$ by finitely many $y_1, \dots, y_m$, and the same elements generate $I$ as an ideal of $A$. So $A$ is Noetherian. Volume 6, Chapter 6, Section 3 shows that $6 = 2 \cdot 3 = (1 + \sqrt{-5})(1 - \sqrt{-5})$ gives two different factorizations into irreducibles. So the Noetherian condition gives the existence of factorizations and not their uniqueness.

**Counterexample (Infinitely many variables).** Let $k$ be a field and $R = k[x_1, x_2, x_3, \dots]$ the ring of polynomials in countably many variables. The chain
$$(x_1) \subseteq (x_1, x_2) \subseteq (x_1, x_2, x_3) \subseteq \cdots$$
is strictly increasing. To see that $x_{n+1} \notin (x_1, \dots, x_n)$, let $\varepsilon : R \to k[x_{n+1}]$ be the homomorphism that fixes $x_{n+1}$ and sends every other variable to $0$. It kills $(x_1, \dots, x_n)$ and not $x_{n+1}$. So $R$ is not Noetherian. The ring $R$ is a domain, and its field of fractions is Noetherian. So a subring of a Noetherian ring need not be Noetherian, unlike a submodule of a Noetherian module.

**Counterexample (A module that is not finitely generated).** The ring $\mathbb{Z}$ is Noetherian, but the $\mathbb{Z}$-module $\mathbb{Q}$ is not: elements with a common denominator $d$ generate a submodule of $\frac{1}{d}\mathbb{Z}$, so $\mathbb{Q}$ is not finitely generated, and the chain $\mathbb{Z} \subsetneq \frac12 \mathbb{Z} \subsetneq \frac14 \mathbb{Z} \subsetneq \cdots$ does not stop. So the hypothesis "finitely generated" in the corollary is needed.

### The library around it

Most results are instances: instance search finds that `ℤ`, fields, principal ideal rings, `R ⧸ I` and `R[X]` are Noetherian. The module lemmas have the pattern `isNoetherian_of_*`, for example `isNoetherian_of_surjective`. For one ideal, `Ideal.fg_of_isNoetherianRing I` gives its finite generation.

Common errors of a learner:

- A hypothesis `h : IsNoetherian R M` must be in square brackets or installed with `haveI`.
- The ACC in Mathlib is `WellFoundedGT`. The Artinian condition of Chapter 4 is `WellFoundedLT`.

### Exercises

1. (A) Show that $\mathbb{Z} \times \mathbb{Z}$ is a Noetherian ring, and describe its ideals.
2. (A) Let $M$ be a Noetherian module and $\phi : M \to M$ a linear map. Show that the chain $\ker \phi \subseteq \ker \phi^2 \subseteq \cdots$ stops, and deduce that a surjective $\phi$ is injective. Hint: if $\ker \phi^n = \ker \phi^{n+1}$ and $\phi(y) = 0$, write $y = \phi^n(x)$.
3. (B) Let $R$ be Noetherian and $I \subseteq R$ an ideal with $I \subseteq \sqrt{0}$. Show that $I^n = 0$ for some $n$. Hint: if $I = (a_1, \dots, a_m)$ and $a_i^{e} = 0$, consider the monomials of degree $m(e - 1) + 1$ in the $a_i$.
4. (B) Let $R$ be Noetherian. Show that every ideal $I \ne R$ contains a product of prime ideals that contain $I$. Hint: Noetherian induction on the set of ideals without this property; a maximal one is prime.
5. (B) Show that a surjective ring homomorphism $\phi : R \to R$ of a Noetherian ring is an isomorphism. Hint: Exercise 2 with the chain of kernels of $\phi^n$, which are ideals.
6. (C) (Cohen) Let $R$ be a ring in which every prime ideal is finitely generated. Show that $R$ is Noetherian. Hint: by Zorn's lemma there is an ideal $I$ maximal among the ideals that are not finitely generated; if $ab \in I$ with $a, b \notin I$, consider $I + Ra$ and $(I : a)$. Mathlib has the theorem as `IsNoetherianRing.of_prime`.

### Notes and history

Emmy Noether's paper "Idealtheorie in Ringbereichen" of 1921 made the ascending chain condition the axiom of an abstract theory of ideals. The standard reference is Atiyah and Macdonald, *Introduction to Commutative Algebra*, Chapters 6 and 7.

### Reference

<?reference?>
