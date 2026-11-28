---
title: Prime ideals, ramification and inertia
kind: api
modules:
  - Mathlib.NumberTheory.RamificationInertia.Basic
  - Mathlib.NumberTheory.RamificationInertia.Ramification
  - Mathlib.NumberTheory.RamificationInertia.Inertia
  - Mathlib.NumberTheory.RamificationInertia.Valuation
  - Mathlib.NumberTheory.RamificationInertia.Galois
  - Mathlib.NumberTheory.RamificationInertia.HilbertTheory
  - Mathlib.NumberTheory.RamificationInertia.Unramified
  - Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
  - Mathlib.NumberTheory.NumberField.Discriminant.Different
  - Mathlib.NumberTheory.NumberField.ExistsRamified
  - Mathlib.NumberTheory.NumberField.Ideal.Basic
  - Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
  - Mathlib.NumberTheory.NumberField.FractionalIdeal
explains:
  E2: [Ideal.exists_smul_eq_of_isGaloisGroup, Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn, Ideal.card_inertia_eq_ramificationIdxIn, IsInertiaField.rank_left, NumberField.Ideal.primesOverSpanEquivMonicFactorsMod, NumberField.absNorm_differentIdeal, NumberField.not_dvd_discr_iff_isUnramifiedIn, NumberField.exists_not_isUnramifiedIn, NumberField.torsionOrder_dvd_absNorm_sub_one]
  E1: auto
families: []
requires: [V10.C04, V11.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Prime ideals, ramification and inertia

### Overview

Let $L/K$ be an extension of number fields of degree $n$, and let $\mathfrak p$ be a nonzero prime of $\mathcal{O}_K$. The ideal $\mathfrak p \mathcal{O}_L$ factors as $\mathfrak P_1^{e_1} \cdots \mathfrak P_g^{e_g}$. The exponent $e_i$ is the ramification index of $\mathfrak P_i$, and the degree $f_i = [\mathcal{O}_L/\mathfrak P_i : \mathcal{O}_K/\mathfrak p]$ is its inertia degree. The fundamental identity is $\sum_i e_i f_i = n$. Volume 10, Chapter 4 defines $e$ and $f$ for general ring extensions and proves this identity.

This section is about the number theory that uses these invariants. In a Galois extension, the Galois group permutes the primes over $\mathfrak p$ transitively, so all $e_i$ are equal and all $f_i$ are equal, and $g e f = n$. The decomposition and inertia groups give a tower of fields with degrees $g$, $f$ and $e$. The Kummer-Dedekind theorem reads $e$ and $f$ off the factorization of a polynomial modulo $p$. A rational prime ramifies in $K$ exactly when it divides the discriminant, and each number field other than $\mathbb{Q}$ has a ramified prime. The section ends with some smaller results on ideals of $\mathcal{O}_K$: roots of unity modulo a prime, the number of ideals of bounded norm, and bases of fractional ideals.

### The library around it

#### Two forms of the invariants

The current definitions are `Ideal.ramificationIdx` and `Ideal.inertiaDeg` from `Mathlib.RingTheory.RamificationInertia`, treated in Volume 10, Chapter 4. For a prime `P : Ideal S` and a ring `R` below it, `P.ramificationIdx R` and `P.inertiaDeg R` are the invariants of `P` over the prime `P.under R`. The fundamental identity in this form is `Ideal.sum_ramification_inertia_eq_finrank`.

The modules `Mathlib.NumberTheory.RamificationInertia.Basic`, `.Ramification` and `.Inertia` hold an older form with the base ideal as an explicit argument: `Ideal.ramificationIdx' p P` is $\sup \{ n \mid p S \le P^n \}$ (`Ideal.ramificationIdx'_spec`), and `Ideal.inertiaDeg' p P` is the residue degree. In the index of this edition, all of `.Basic`, `Ideal.inertiaDeg'` and many unprimed lemma names of `.Ramification` are deprecated. Among them is the deprecated `Ideal.sum_ramification_inertia`, the old form of the fundamental identity. The lemmas about `Ideal.ramificationIdx'` still stand. Some examples are the tower formula `Ideal.ramificationIdx'_algebra_tower`, the localization criterion `Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff` and the count in the factorization `Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count`. New code uses the unprimed forms. The module `Mathlib.NumberTheory.RamificationInertia.Valuation` has no declarations in this edition.

#### Galois extensions

`Mathlib.NumberTheory.RamificationInertia.Galois` works with a ring extension $A \subseteq B$ and a finite group $G$ that acts on $B$ with the predicate `IsGaloisGroup G A B`: the invariants of $G$ are $A$, and the action is faithful. The main example is $\mathcal{O}_K \subseteq \mathcal{O}_L$ with $G = \operatorname{Gal}(L/K)$. The set `p.primesOver B` is the set of primes of $B$ over $p$. The group $G$ acts on it (`Ideal.instMulActionElemPrimesOver`).

**Theorem (Transitivity).** Let $P$ and $Q$ be primes of $B$ over $p$. Then $\sigma P = Q$ for some $\sigma \in G$ (`Ideal.exists_smul_eq_of_isGaloisGroup`).

*Proof.* Assume that $Q \ne \sigma P$ for each $\sigma$. Primes over the same $p$ are incomparable, so $Q \not\subseteq \sigma P$ for each $\sigma$. By prime avoidance, there is $x \in Q$ outside all the primes $\sigma P$. The norm $N(x) = \prod_{\sigma \in G} \sigma(x)$ is in $A$ and in $Q$, so it is in $Q \cap A = p \subseteq P$. Since $P$ is prime, some factor $\sigma(x)$ is in $P$, so $x \in \sigma^{-1} P$. This is a contradiction. $\square$

The same statement for `galRestrict` is `Ideal.exists_comap_galRestrict_eq`, and the instance form is `Ideal.isPretransitive_of_isGaloisGroup`. An element $\sigma$ maps $P$ to $\sigma P$ and induces isomorphisms $B/P \cong B/\sigma P$ and $B_P \cong B_{\sigma P}$. So all primes over $p$ have the same ramification index (`Ideal.ramificationIdx_eq_of_isGaloisGroup`) and the same inertia degree (`Ideal.inertiaDeg_eq_of_isGaloisGroup`). These common values are `Ideal.ramificationIdxIn p B` and `Ideal.inertiaDegIn p B`. For each prime $P$ over $p$ they equal `P.ramificationIdx A` and `P.inertiaDeg A` (`Ideal.ramificationIdxIn_eq_ramificationIdx`, `Ideal.inertiaDegIn_eq_inertiaDeg`).

**Corollary.** If $A$ and $B$ are domains, $B$ is finite and flat over $A$, and $p$ is prime, then $g \cdot (e \cdot f) = |G|$, with $g$ the number of primes over $p$ (`Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`).

*Proof.* In the fundamental identity $\sum_{P} e_P f_P = [B : A] = |G|$, each of the $g$ terms is $e f$. $\square$

For $\mathbb{Z}[i]$ over $\mathbb{Z}$, with $|G| = 2$: the prime $2 = -i(1+i)^2$ has $g = 1$, $e = 2$, $f = 1$. The prime $5 = (2+i)(2-i)$ has $g = 2$, $e = f = 1$. The prime $3$ stays prime, so $g = e = 1$ and $f = 2$.

The decomposition group of $P$ is its stabilizer `MulAction.stabilizer G P`, and its inertia group `Ideal.inertia G P` is the subgroup of elements that act trivially on $B/P$. When the residue field extension is separable (the class `Algebra.HasSeparableResidueFieldsAt A B p`), the counts are as follows.

| Lean name | Statement |
|---|---|
| `Ideal.card_inertia_eq_ramificationIdxIn` | $|I_P| = e$ |
| `Ideal.card_stabilizer_eq_card_inertia_mul_finrank` | $|D_P| = |I_P| \cdot f$ |
| `Ideal.ncard_primesOver_mul_card_inertia_mul_finrank` | $g \cdot |I_P| \cdot f = |G|$ |
| `Ideal.ramificationIdxIn_mul_ramificationIdxIn` | $e$ is multiplicative in a tower |
| `Ideal.inertiaDegIn_mul_inertiaDegIn` | $f$ is multiplicative in a tower |

The proof of $|I_P| = e$ uses the surjection $D_P \to \operatorname{Gal}(\kappa(P)/\kappa(p))$ with kernel $I_P$, which is where the separability is needed. Then $|D_P| = |G|/g = e f$ and $|D_P/I_P| = f$ give $|I_P| = e$.

#### Decomposition and inertia fields

`Mathlib.NumberTheory.RamificationInertia.HilbertTheory` names the fixed fields of $D_P$ and $I_P$. For a Galois extension $L/K$ and a prime $P$ of $B$, the predicate `IsDecompositionField K L P D` says that an intermediate field $D$ is the fixed field of $D_P$, and `IsInertiaField K L P E` says the same for $E$ and $I_P$. Instances give the actual fixed fields. A field with the predicate is unique up to isomorphism (`IsDecompositionField.ringEquiv`, `IsInertiaField.ringEquiv`). The ring forms `Ideal.IsDecompositionRing` and `Ideal.IsInertiaRing` say the same thing for an intermediate ring.

**Theorem.** In the tower $K \subseteq D \subseteq E \subseteq L$, the degrees are $[D : K] = g$, $[E : D] = f$ and $[L : E] = e$.

In Lean these are `IsDecompositionField.rank_right`, `IsInertiaField.rank_decompositionField` and `IsInertiaField.rank_left`. The companions `IsDecompositionField.rank_left` ($[L : D] = e f$) and `IsInertiaField.rank_right` ($[E : K] = g f$) follow. The degrees follow from Galois theory and the counts of the previous table: $[L : E] = |I_P| = e$ and $[L : D] = |D_P| = e f$. Over $D$ the prime $P$ is the only prime above $P \cap D$ (`IsDecompositionField.primesOver_eq_singleton`), with the same $e$ and $f$ (`IsDecompositionField.ramificationIdx_eq`, `IsDecompositionField.inertiaDeg_eq`).

#### Unramified primes

An extension is unramified at a prime $P$ of $S$ (`Algebra.IsUnramifiedAt R P`) when the localization of $S$ at $P$ is unramified over $R$ in the sense of étale algebra. It is unramified over a prime $p$ of $R$ (`Algebra.IsUnramifiedIn S p`) when it is unramified at each prime over $p$. `Mathlib.NumberTheory.RamificationInertia.Unramified` connects these predicates with the ramification index.

| Lean name | Statement |
|---|---|
| `Ideal.ramificationIdx_eq_one_of_isUnramifiedAt` | unramified at $P$ gives $e_P = 1$ |
| `Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one` | over $\mathbb{Z}$-finite $R$ of characteristic $0$: unramified over $p$ iff $e_P = 1$ for all $P$ over $p$ |
| `Algebra.IsUnramifiedIn.ramificationIdx_eq_one` | the forward direction |
| `Algebra.isUnramifiedIn_iff_forall_of_isDedekindDomain` | unramified over $p$ iff unramified at each maximal $P$ over $p$ |

The residue fields of a number field are finite and so perfect. Thus the condition $e_P = 1$ is the full condition: the residue extension is separable without an extra hypothesis.

#### The Kummer-Dedekind theorem

Let $\theta \in \mathcal{O}_K$ generate $K$, and let $f$ be its minimal polynomial. The ring $\mathbb{Z}[\theta]$ can be smaller than $\mathcal{O}_K$. `Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind` measures the difference by `NumberField.RingOfIntegers.exponent θ`, the positive generator of the conductor $\{ x \in \mathbb{Z} \mid x \mathcal{O}_K \subseteq \mathbb{Z}[\theta] \}$. It is $1$ exactly when $\mathbb{Z}[\theta] = \mathcal{O}_K$ (`NumberField.RingOfIntegers.exponent_eq_one_iff`). A prime $p$ does not divide it exactly when the conductor and $p$ are coprime (`NumberField.RingOfIntegers.not_dvd_exponent_iff`). The finset `NumberField.RingOfIntegers.monicFactorsMod θ p` holds the monic irreducible factors of $\bar f \in \mathbb{F}_p[X]$ (`NumberField.RingOfIntegers.mem_monicFactorsMod_iff`).

**Theorem (Kummer-Dedekind).** Let $p$ be a prime that does not divide the exponent of $\theta$. Then the primes of $\mathcal{O}_K$ over $p$ correspond to the monic irreducible factors $\bar Q$ of $\bar f$. The prime of $\bar Q$ is $(p, Q(\theta))$, its ramification index is the multiplicity of $\bar Q$ in $\bar f$, and its inertia degree is $\deg \bar Q$.

In Lean the bijection is `NumberField.Ideal.primesOverSpanEquivMonicFactorsMod`. Its three properties are `NumberField.Ideal.primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span`, `NumberField.Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply'` and `NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'`. The proof goes through the isomorphism `NumberField.RingOfIntegers.ZModXQuotSpanEquivQuotSpan` between $\mathbb{F}_p[X]/(\bar f)$ and $\mathcal{O}_K/p\mathcal{O}_K$. That isomorphism needs $p$ coprime to the conductor. Then the primes of $\mathcal{O}_K/p$ are the primes of $\mathbb{F}_p[X]/(\bar f)$, which are the ideals $(\bar Q)$. The general theorem for an order is `Mathlib.NumberTheory.KummerDedekind`, which is treated elsewhere.

For $K = \mathbb{Q}(i)$ and $\theta = i$: $\mathbb{Z}[i] = \mathcal{O}_K$, so each $p$ qualifies. Modulo $2$, $X^2 + 1 = (X+1)^2$, so $2$ has one prime $(2, 1+i)$ with $e = 2$. Modulo $5$, $X^2 + 1 = (X-2)(X+2)$, so $5$ splits into $(5, i-2)$ and $(5, i+2)$. Modulo $3$, $X^2 + 1$ is irreducible, so $3$ stays prime with $f = 2$.

#### The different and the discriminant

The different ideal `differentIdeal` and the general criterion `not_dvd_differentIdeal_iff` (a prime $P$ is unramified iff $P$ does not divide the different) are in Volume 10, Chapter 4. `Mathlib.NumberTheory.NumberField.Discriminant.Different` applies them to number fields.

**Theorem.** $N(\mathfrak D_{K/\mathbb{Q}}) = |d_K|$ (`NumberField.absNorm_differentIdeal`). For a prime $p$, $p \nmid d_K$ if and only if $p$ is unramified in $K$ (`NumberField.not_dvd_discr_iff_isUnramifiedIn`).

*Proof of the second statement from the first.* The norm of $\mathfrak D$ is the product of $N(P)^{v_P(\mathfrak D)}$, and $N(P)$ is a power of the prime under $P$. So $p \mid N(\mathfrak D)$ if and only if some prime $P$ over $p$ divides $\mathfrak D$. By `not_dvd_differentIdeal_iff`, this is the case if and only if $K$ is ramified at some $P$ over $p$. $\square$

Other forms of the criterion are `NumberField.not_dvd_discr_iff_forall_liesOver` and `NumberField.not_dvd_discr_iff_forall_mem`. The module also proves $d_K \in \mathfrak D_{K/\mathbb{Q}}$ (`NumberField.discr_mem_differentIdeal`) and the tower formula $|d_L| = N(\mathfrak D_{L/K}) \cdot |d_K|^{[L:K]}$ (`NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow`). A consequence is $d_K \mid d_L$ (`NumberField.discr_dvd_discr`). For two Galois fields with coprime discriminants, `NumberField.linearDisjoint_of_isGalois_isCoprime_discr` gives linear disjointness, and `NumberField.natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow` computes the discriminant of the compositum.

**Theorem (Existence of a ramified prime).** If $K \ne \mathbb{Q}$, then some prime $p$ ramifies in $K$ (`NumberField.exists_not_isUnramifiedIn`).

*Proof.* If $[K : \mathbb{Q}] > 1$, then $|d_K| > 2$ by the Minkowski bound (`NumberField.abs_discr_gt_two`). So $d_K$ has a prime factor $p$, and $p$ ramifies by the previous theorem. $\square$

The forms of `Mathlib.NumberTheory.NumberField.ExistsRamified` for a prime $P$ of $\mathcal{O}_K$ are `NumberField.exists_not_isUnramifiedAt_int` and, for Galois $K$, `NumberField.exists_not_isUnramifiedAt_int_of_isGalois`. In the language of étale algebras, `NumberField.finrank_eq_one_of_unramified` says that $\mathcal{O}_K$ unramified over $\mathbb{Z}$ forces $K = \mathbb{Q}$, and `bijective_algebraMap_int_of_finite_of_unramified` says that $\mathbb{Z}$ is the only such ring that is a domain and finite over $\mathbb{Z}$.

#### Roots of unity modulo an ideal

`Mathlib.NumberTheory.NumberField.Ideal.Basic` reduces the roots of unity of $K$ modulo an ideal $I$. The map is `Ideal.torsionMapQuot I` from the torsion subgroup to $(\mathcal{O}_K/I)^\times$, and `Ideal.rootsOfUnityMapQuot` is the same map for the $n$-th roots of unity. If $N(I) \ne 1$ and $N(I)$ is coprime to the number $w$ of roots of unity, the map is injective (`Ideal.torsionMapQuot_injective`).

**Corollary.** For a nonzero prime $P$ with $N(P)$ coprime to $w$, $w \mid N(P) - 1$ (`NumberField.torsionOrder_dvd_absNorm_sub_one`).

*Proof.* The map embeds the cyclic group of order $w$ into $(\mathcal{O}_K/P)^\times$, which has order $N(P) - 1$. By Lagrange, $w \mid N(P) - 1$. $\square$

For $K = \mathbb{Q}(\zeta_n)$ this gives the classical fact that the primes $p \nmid n$ satisfy $N(P) \equiv 1 \pmod n$.

#### Counting ideals

`Mathlib.NumberTheory.NumberField.Ideal.Asymptotics` proves an asymptotic formula for the number of ideals of bounded norm:
$$\lim_{s \to \infty} \frac{\#\{ I \subseteq \mathcal{O}_K \mid N(I) \le s \}}{s} = \frac{2^{r_1} (2\pi)^{r_2} R_K h_K}{w_K \sqrt{|d_K|}}.$$
This is `NumberField.Ideal.tendsto_norm_le_div_atTop`, with the regulator `NumberField.Units.regulator` and the class number `NumberField.classNumber` of Section 2. The limit counts lattice points of a cone in the mixed space, and that count is not reproduced here. `NumberField.Ideal.tendsto_norm_le_and_mk_eq_div_atTop` gives the same limit for the ideals of one class, without the factor $h_K$.

#### Bases of fractional ideals

`Mathlib.NumberTheory.NumberField.FractionalIdeal` gives a fractional ideal $I$ of $K$ a $\mathbb{Z}$-basis `NumberField.fractionalIdealBasis K I`. For an invertible $I$, the rank is $[K : \mathbb{Q}]$ (`NumberField.fractionalIdeal_rank`), and `NumberField.basisOfFractionalIdeal K I` is the same basis seen as a $\mathbb{Q}$-basis of $K$. Its determinant in the integral basis has absolute value $N(I)$ (`NumberField.det_basisOfFractionalIdeal_eq_absNorm`). This is the covolume identity that the asymptotic count and the class group section use.

#### Common errors

1. The two forms of the ramification index take their arguments in a different order. `Ideal.ramificationIdx'` takes the lower ideal first (`p.ramificationIdx' P`), and `Ideal.ramificationIdx` takes the prime and then the ring (`P.ramificationIdx R`). A rewrite with a lemma of one form fails on a goal of the other form.
2. The results on inertia groups need the instance `Algebra.HasSeparableResidueFieldsAt A B p`. If instance search does not find it in a general setting, give it by hand: it holds when the residue fields are perfect, for example finite.
3. The primes above $p$ are a `Set` in `Ideal.primesOver`, so the count is `Set.ncard`. The Galois statements use `(p.primesOver B).ncard`. The finset `IsDedekindDomain.primesOverFinset` belongs to the deprecated older form.

### Exercises

1. (A) Use the Kummer-Dedekind theorem with $\theta = \sqrt{-5}$ to factor $2$, $3$ and $7$ in $\mathbb{Z}[\sqrt{-5}]$. For each prime, give $g$, $e$ and $f$, and check $g e f = 2$.
2. (A) In a Galois extension of degree $6$, list the possible triples $(g, e, f)$.
3. (B) Show that $2$ is ramified in $\mathbb{Q}(\sqrt d)$ for $d \equiv 2, 3 \pmod 4$ and unramified for $d \equiv 1 \pmod 4$, with the discriminant criterion.
4. (B) Let $K = \mathbb{Q}(\zeta_3)$, with $w = 6$. Use the corollary on roots of unity to show that $N(P) \equiv 1 \pmod 6$ for each prime $P$ over a prime $p \ge 5$. Conclude that a prime $p \equiv 2 \pmod 3$ with $p \ge 5$ stays prime in $\mathcal{O}_K$.
5. (B) Show that in an abelian extension, the decomposition group and the inertia group of $P$ depend only on $p$, and not on $P$.
6. (C) Show that if $L/K$ is Galois and $p$ is unramified in $L$, then $D_P$ is cyclic of order $f$.

### Reference

<?reference?>
