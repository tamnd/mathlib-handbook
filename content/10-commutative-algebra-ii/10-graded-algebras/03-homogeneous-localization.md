---
title: Homogeneous localization
kind: api
modules:
  - Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
explains:
  E2: [HomogeneousLocalization, HomogeneousLocalization.NumDenSameDeg, HomogeneousLocalization.val_injective, HomogeneousLocalization.Away, HomogeneousLocalization.AtPrime, HomogeneousLocalization.isLocalRing, HomogeneousLocalization.map, HomogeneousLocalization.awayMap, HomogeneousLocalization.Away.isLocalization_mul, HomogeneousLocalization.Away.finiteType]
  E1: auto
families: []
requires: [V09, V10.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Homogeneous localization

### Overview

Let $A$ be a commutative graded ring and $S$ a submonoid of $A$. The homogeneous localization $A_{(S)}$ is the subring of $S^{-1}A$ of the fractions $a/s$ with $s \in S$ and $a$, $s$ homogeneous of the same degree. These fractions have degree $0$. Two cases are important. For a homogeneous $f$, the ring $A_{(f)}$ uses the powers of $f$. For a homogeneous prime $\mathfrak p$, the ring $A_{(\mathfrak p)}$ uses the homogeneous elements outside $\mathfrak p$. For $A = k[X_0, \dots, X_n]$ the ring $A_{(X_0)}$ is the polynomial ring $k[X_1/X_0, \dots, X_n/X_0]$, the coordinate ring of an affine chart of projective space. In general the rings $A_{(f)}$ are the rings of the affine open sets of $\operatorname{Proj} A$, and the rings $A_{(\mathfrak p)}$ are its local rings.

In Mathlib the ring is `HomogeneousLocalization 𝒜 S`, with the abbreviations `HomogeneousLocalization.Away 𝒜 f` and `HomogeneousLocalization.AtPrime 𝒜 𝔭`. This section describes the construction, the embedding into the localization, the local ring at a prime, the functorial maps, and two results for gradings by $\mathbb{N}$: the localization $A_{(fg)}$ is a localization of $A_{(f)}$, and $A_{(f)}$ is of finite type when $A$ is.

### The library around it

#### The construction

The file assumes that $\iota$ is a commutative monoid, that $A$ is a commutative ring, and that `𝒜 : ι → σ` is a grading by additive subgroups. A pair of a numerator and a denominator is the structure `HomogeneousLocalization.NumDenSameDeg 𝒜 S`, with fields `deg : ι`, `num : 𝒜 deg` and `den : 𝒜 deg` and the proof `den_mem : den ∈ S`. The map `HomogeneousLocalization.NumDenSameDeg.embedding` sends a pair to the fraction $\mathrm{num}/\mathrm{den}$ in `Localization S`.

The pairs do not form a ring. The sum of $a/s$ and $b/t$ is $(ta + sb)/(st)$, of degree $i + j$, by `HomogeneousLocalization.NumDenSameDeg.deg_add`, but the zero pair has degree $0$. So for a pair $c$ of degree $i \neq 0$ the sum $c + (-c)$ has degree $2i$ and is not the zero pair. The pairs form only a commutative monoid under multiplication, `HomogeneousLocalization.NumDenSameDeg.instCommMonoid`. The type `HomogeneousLocalization 𝒜 S` is the quotient of the pairs by the relation of equal image in `Localization S`. On the quotient the ring axioms hold, since they hold in the localization. The instance is `HomogeneousLocalization.homogeneousLocalizationCommRing`.

| Lean name | Statement |
|---|---|
| `HomogeneousLocalization.mk` | the class of a pair |
| `HomogeneousLocalization.mk_surjective` | every element is the class of a pair |
| `HomogeneousLocalization.val` | the map to `Localization S` |
| `HomogeneousLocalization.val_mk` | `(mk c).val` is `Localization.mk c.num ⟨c.den, c.den_mem⟩` |
| `HomogeneousLocalization.val_injective` | `val` is injective, the `@[ext]` lemma |
| `HomogeneousLocalization.ext_iff_val` | $a = b \iff a.\mathrm{val} = b.\mathrm{val}$ |
| `HomogeneousLocalization.num`, `.den`, `.deg` | a chosen numerator, denominator and degree |
| `HomogeneousLocalization.num_mem_deg` | the numerator has the chosen degree, also `den_mem_deg` |
| `HomogeneousLocalization.den_smul_val` | $\mathrm{den} \cdot a.\mathrm{val} = \mathrm{num}/1$ |
| `HomogeneousLocalization.subsingleton` | if $0 \in S$, the ring is trivial |
| `HomogeneousLocalization.isUnit_iff_isUnit_val` | $a$ is a unit iff $a.\mathrm{val}$ is a unit |

The map `val` is a ring map, by the simp lemmas `val_add`, `val_mul`, `val_one`, `val_pow` and the others. The instance `HomogeneousLocalization.homogeneousLocalizationAlgebra` makes `Localization S` an algebra over `HomogeneousLocalization 𝒜 S`, with `algebraMap` equal to `val`. So the ring is a subring of the localization in all but the definition. The map `HomogeneousLocalization.fromZeroRingHom 𝒜 S : 𝒜 0 →+* HomogeneousLocalization 𝒜 S` sends $a$ to $a/1$. It is the algebra map for the instance over `𝒜 0`, by `HomogeneousLocalization.algebraMap_eq`.

The ring is a quotient and not a subring. So `num` and `den` are chosen with `Quotient.out`. For a pair $c$, the numerator of `mk c` is in general not `c.num`. Compute through `val` instead.

#### The local ring at a prime

Let $\mathfrak p$ be a prime ideal of $A$. Then `HomogeneousLocalization.AtPrime 𝒜 𝔭` is the homogeneous localization at `𝔭.primeCompl`. The prime need not be homogeneous for the definition. The denominators are the homogeneous elements outside $\mathfrak p$, since a denominator must be homogeneous to form a pair.

**Proposition.** The ring $A_{(\mathfrak p)}$ is a local ring.

*Proof.* The localization $A_{\mathfrak p}$ is local. Let $a \in A_{(\mathfrak p)}$. By `HomogeneousLocalization.isUnit_iff_isUnit_val`, the element $a$ is a unit if its image in $A_{\mathfrak p}$ is a unit. This holds because the inverse $s/r$ of a fraction $r/s$ is again a fraction of two homogeneous elements of the same degree, with $r \notin \mathfrak p$. In the local ring $A_{\mathfrak p}$, either the image of $a$ or the image of $1 - a$ is a unit. So $a$ or $1 - a$ is a unit in $A_{(\mathfrak p)}$. $\square$

The instance is `HomogeneousLocalization.isLocalRing`, and `HomogeneousLocalization.instNontrivialAtPrime` says that the ring is not trivial.

#### Localization at an element

For $f \in A$, `HomogeneousLocalization.Away 𝒜 f` is the homogeneous localization at `Submonoid.powers f`. When $f \in A_d$, the constructor `HomogeneousLocalization.Away.mk 𝒜 hf n a ha` is the fraction $a/f^n$ for $a \in A_{n \cdot d}$. By `HomogeneousLocalization.Away.mk_surjective` every element has this form. `HomogeneousLocalization.Away.val_mk` computes its image in `Localization.Away f`. The lemma `HomogeneousLocalization.Away.eventually_smul_mem` says that for an element $z$ of $A_{(f)}$, the product $f^nz$ in $A_f$ is the image of an element of $A_{n \cdot d}$ for all large $n$.

#### Maps

Let `g : 𝒜 →+*ᵍ ℬ` be a graded ring map and $P$, $Q$ submonoids with $P \subseteq g^{-1}(Q)$. Then $a/s \mapsto g(a)/g(s)$ is a ring map $A_{(P)} \to B_{(Q)}$.

| Lean name | Statement |
|---|---|
| `HomogeneousLocalization.map g h` | the map $A_{(P)} \to B_{(Q)}$ for `h : P ≤ Q.comap g` |
| `HomogeneousLocalization.mapId` | the same for the identity of $A$ and $P \le Q$ |
| `HomogeneousLocalization.Away.map g f` | the map $A_{(f)} \to B_{(g(f))}$ |
| `HomogeneousLocalization.localRingHom` | the map $A_{(I)} \to B_{(J)}$ for primes with $I = g^{-1}(J)$ |
| `HomogeneousLocalization.val_localRingHom` | its value in the localizations is `Localization.localRingHom` |
| `HomogeneousLocalization.awayMap 𝒜 hg hx` | the map $A_{(f)} \to A_{(x)}$ for $x = fg$ and $g$ homogeneous |
| `HomogeneousLocalization.awayMapₐ` | the same map as an algebra map over `𝒜 0` |
| `HomogeneousLocalization.awayMap_mk` | it sends $a/f^n$ to $ag^n/(fg)^n$ |

The map `localRingHom` is a local homomorphism, by the instance `HomogeneousLocalization.instIsLocalHomAtPrimeRingHomLocalRingHom`. The lemmas `HomogeneousLocalization.map_comp`, `HomogeneousLocalization.map_id` and `HomogeneousLocalization.Away.map_comp` give the functoriality.

#### Gluing the charts

The map `awayMap` corresponds to the inclusion of the open set $D_+(fg)$ in $D_+(f)$. The next result says that this inclusion is that of a basic open set of the affine scheme $\operatorname{Spec} A_{(f)}$.

**Proposition.** Let $A$ be graded by $\mathbb{N}$, $f \in A_d$ with $d \ne 0$, and $g \in A_e$. Put $t = g^d/f^e \in A_{(f)}$. Then `awayMap` makes $A_{(fg)}$ the localization of $A_{(f)}$ at $t$.

*Proof.* The image of $t$ in $A_{(fg)}$ is $g^{d+e}/(fg)^e$. It is a unit with inverse $f^{d+e}/(fg)^d$, because both fractions equal $g^d/f^e$ and $f^e/g^d$ in $A_{fg}$. Let $a/(fg)^n$ be an element of $A_{(fg)}$, with $a$ of degree $n(d+e)$. Then
$$\frac{a}{(fg)^n} = \frac{ag^{n(d-1)}}{f^{n(e+1)}} \cdot \Big(\frac{f^e}{g^d}\Big)^{n},$$
and the first factor is the image of an element of $A_{(f)}$: its numerator has degree $nd(e+1)$, the degree of the denominator. Here $d \ge 1$ is used. So every element of $A_{(fg)}$ is the image of an element of $A_{(f)}$ times a power of $t^{-1}$. The condition on the kernel follows from the same computation in $A_{fg}$. $\square$

In Lean, $t$ is `HomogeneousLocalization.Away.isLocalizationElem hf hg`. The result `HomogeneousLocalization.Away.isLocalization_mul` is stated with `letI := (awayMap 𝒜 hg hx).toAlgebra` and the conclusion `IsLocalization.Away (isLocalizationElem hf hg) (Away 𝒜 x)`.

#### Finite type

**Proposition.** Let $A$ be graded by $\mathbb{N}$ and of finite type over $A_0$, and let $f \in A_d$. Then $A_{(f)}$ is of finite type over $A_0$.

*Proof sketch.* By Section 1, $A$ is generated over $A_0$ by finitely many homogeneous $v_1, \dots, v_m$ of positive degrees $d_1, \dots, d_m$. An element of $A_{(f)}$ is $a/f^n$ with $a \in A_{nd}$, so $a$ is an $A_0$-linear combination of monomials $\prod_i v_i^{a_i}$ with $\sum_i a_id_i = nd$. This is `HomogeneousLocalization.Away.span_mk_prod_pow_eq_top`. Write $a_i = dq_i + r_i$ with $0 \le r_i < d$. Then the fraction of a monomial is the product of the powers $(v_i^d/f^{d_i})^{q_i}$ and of a fraction of $\prod_i v_i^{r_i}$ by a power of $f$. There are finitely many exponents $r_i < d$. So the elements $v_i^d/f^{d_i}$ and the fractions of the monomials with all exponents at most $d$ generate $A_{(f)}$. $\square$

The generating set is `HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top`, and the result is `HomogeneousLocalization.Away.finiteType 𝒜 f d hf`, with the hypothesis `[Algebra.FiniteType (𝒜 0) A]`. Together with the previous result, this shows that the open sets $D_+(f)$ give an affine cover of $\operatorname{Proj} A$ by schemes of finite type over $A_0$.

#### Common errors

1. Equality in `HomogeneousLocalization 𝒜 S` is not equality of pairs. Prove it with `HomogeneousLocalization.val_injective` or the `ext` tactic, and then compute in `Localization S` with `val_mk`.
2. `HomogeneousLocalization.Away 𝒜 f` is defined for every $f$, but `Away.mk` needs a proof `hf : f ∈ 𝒜 d`. For a nonhomogeneous $f$ the powers $f^n$ with $n > 0$ are in general not homogeneous. Then the only denominator is $1$, and the ring is the image of $A_0$.
3. The gluing and finiteness results assume a grading by $\mathbb{N}$, `𝒜 : ℕ → σ`, while the construction accepts any commutative monoid. For a grading by $\mathbb{Z}$ the lemmas `Away.isLocalization_mul` and `Away.finiteType` do not apply.

### Exercises

1. (A) Show that $A_{(S)}$ is the zero ring if $0 \in S$, with `HomogeneousLocalization.subsingleton`.
2. (A) Let $A = k[X, Y]$ with the grading by degree. Show that $A_{(X)}$ is isomorphic to $k[T]$ by $Y/X \mapsto T$.
3. (B) Let $f \in A_d$ with $d > 0$. Show that $A_{(f)} \cong A_{(f^2)}$, with `HomogeneousLocalization.awayMap` for $g = f$.
4. (B) Let $\mathfrak p$ be a homogeneous prime that does not contain the homogeneous element $f$ of positive degree. Show that $A_{(\mathfrak p)}$ is a localization of $A_{(f)}$ at a prime ideal.
5. (B) Let $A = k[X, Y]$ and $\mathfrak p = (X)$. Show that $A_{(\mathfrak p)}$ is a discrete valuation ring with uniformizer $X/Y$.
6. (C) Let $A$ be $\mathbb{N}$-graded, $f \in A_1$, and suppose that $A$ is generated over $A_0$ by $A_1$. Show that $A_f \cong A_{(f)}[T, T^{-1}]$, with $T$ the image of $f$.

### Reference

<?reference?>
