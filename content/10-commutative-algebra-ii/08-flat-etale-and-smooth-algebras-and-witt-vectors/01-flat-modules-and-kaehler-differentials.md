---
title: Flat modules and Kähler differentials
kind: theory
modules:
  - Mathlib.RingTheory.Flat.Basic
  - Mathlib.RingTheory.Flat.Tensor
  - Mathlib.RingTheory.Flat.Stability
  - Mathlib.RingTheory.Flat.TorsionFree
  - Mathlib.RingTheory.LocalRing.Module
  - Mathlib.RingTheory.Kaehler.Basic
  - Mathlib.RingTheory.Kaehler.Polynomial
  - Mathlib.RingTheory.Kaehler.TensorProduct
  - Mathlib.RingTheory.Kaehler.JacobiZariski
explains:
  E3: [Module.Flat, Module.Flat.iff_rTensor_injective', Module.free_of_flat_of_isLocalRing, KaehlerDifferential, KaehlerDifferential.D]
  E2: [Module.Flat.of_free, Module.Flat.self, Module.Flat.of_projective, Module.Flat.trans, Module.Flat.baseChange, IsLocalization.flat, Module.Flat.localizedModule, Module.Flat.instOfIsDedekindDomainOfIsTorsionFree, Module.Flat.torsion_eq_bot, Module.FaithfullyFlat, Derivation, Derivation.liftKaehlerDifferential, KaehlerDifferential.linearMapEquivDerivation, KaehlerDifferential.ideal, KaehlerDifferential.span_range_derivation, KaehlerDifferential.mvPolynomialBasis, KaehlerDifferential.exact_mapBaseChange_map, KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange]
  E1: auto
families: []
requires: [V07, V08, V10.C02]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Flat modules and Kähler differentials

### Overview

A module $M$ is flat if tensoring with $M$ preserves injective maps. Flatness is the algebraic form of "a family that varies continuously": localizations, free modules and completions of Noetherian rings are flat, and over a Noetherian local ring a finite flat module is free. Flatness is the first of the conditions that define étale and smooth algebras in Section 2.

The second ingredient is the module of Kähler differentials $\Omega_{S/R}$, the universal target of an $R$-linear derivation of $S$. For a polynomial ring it is free on $dX_1, \dots, dX_n$; for a quotient it is computed from the partial derivatives of the relations. The vanishing of $\Omega_{S/R}$ is the condition "unramified".

### Definitions

**Definition (Flat module).** An $R$-module $M$ is flat if for every injective $R$-linear map $N' \to N$, the map $N' \otimes_R M \to N \otimes_R M$ is injective. It is faithfully flat if it is flat and $N \otimes_R M = 0$ implies $N = 0$.

::: mathlib
`Module.Flat` · `Mathlib.RingTheory.Flat.Basic`

`Module.Flat R M` is a class. Its field `out` says that `N ⊗ M → P ⊗ M` is injective for every finitely generated submodule `N` of a finite module `P`, which is equivalent to the definition in the text by `Module.Flat.rTensor_preserves_injective_linearMap`. The basic instances: `Module.Flat.self`, `Module.Flat.of_free`, `Module.Flat.of_projective`, and stability under base change, `Module.Flat.baseChange`, and composition, `Module.Flat.trans`. Faithful flatness is the class `Module.FaithfullyFlat`.

<?decl Module.Flat?>
:::

**Definition (Derivation).** Let $S$ be an $R$-algebra and $M$ an $S$-module. An $R$-derivation $D : S \to M$ is an $R$-linear map with $D(ab) = aD(b) + bD(a)$. Then $D(r) = 0$ for $r$ in the image of $R$, since $D(1) = D(1 \cdot 1) = 2D(1)$.

**Definition (Kähler differentials).** Let $I$ be the kernel of the multiplication $S \otimes_R S \to S$. The module of Kähler differentials is $\Omega_{S/R} = I/I^2$, an $S$-module, with $d : S \to \Omega_{S/R}$, $ds = 1 \otimes s - s \otimes 1 \bmod I^2$.

::: mathlib
`KaehlerDifferential` · `Mathlib.RingTheory.Kaehler.Basic`

`KaehlerDifferential R S`, with notation `Ω[S⁄R]`, is defined as `(KaehlerDifferential.ideal R S).Cotangent`, where `KaehlerDifferential.ideal R S` is the kernel of `S ⊗[R] S → S`. Derivations are `Derivation R S M`, in `Mathlib/RingTheory/Derivation/Basic.lean`.

<?decl KaehlerDifferential?>
:::

::: mathlib
`KaehlerDifferential.D` · `Mathlib.RingTheory.Kaehler.Basic`

`KaehlerDifferential.D R S : Derivation R S Ω[S⁄R]` is the universal derivation $d$. The universal property is `Derivation.liftKaehlerDifferential`, and as an equivalence `KaehlerDifferential.linearMapEquivDerivation : (Ω[S⁄R] →ₗ[S] M) ≃ₗ[S] Derivation R S M`. The image of `D` spans, `KaehlerDifferential.span_range_derivation`.

<?decl KaehlerDifferential.D?>
:::

### Theorems and proofs

**Theorem (Ideal criterion).** $M$ is flat if and only if $I \otimes_R M \to M$ is injective for every ideal $I$, and it is enough to take finitely generated ideals.

*Proof sketch.* One direction is the definition. For the other, first show by induction that $N' \otimes M \to N \otimes M$ is injective when $N = N' + Rx$ is obtained by adding one generator: the quotient $N/N' \cong R/I$ for an ideal $I$, and the injectivity of $I \otimes M \to M$ gives the step, through a diagram chase with the exact sequences $0 \to I \to R \to R/I \to 0$. Then pass to finitely generated $N$, and finally to all $N$, since every element of a tensor product involves finitely many elements. The finitely generated ideals suffice because every ideal is a directed union of them and tensor products commute with directed unions. $\square$

::: mathlib
`Module.Flat.iff_rTensor_injective'` · `Mathlib.RingTheory.Flat.Tensor`

`Module.Flat R M ↔ ∀ I : Ideal R, Function.Injective (rTensor M I.subtype)`. The proof in Mathlib goes through the character module of $M$ and Baer's criterion for injective modules, a different route from the sketch.

<?decl Module.Flat.iff_rTensor_injective'?>
:::

**Theorem (Localization is flat).** For a multiplicative subset $T \subseteq R$, $T^{-1}R$ is a flat $R$-module, and $T^{-1}M \cong T^{-1}R \otimes_R M$.

*Proof.* The isomorphism $T^{-1}R \otimes_R M \to T^{-1}M$, $(r/t) \otimes m \mapsto rm/t$, is in Volume 9. If $N' \to N$ is injective and $n'/t \mapsto 0$ in $T^{-1}N$, then $un' = 0$ in $N$ for some $u \in T$, so $un' = 0$ in $N'$ and $n'/t = 0$. $\square$

::: mathlib
`IsLocalization.flat` · `Mathlib.RingTheory.Flat.Stability`

`IsLocalization.flat : Module.Flat R S` for a localization `S` of `R`. For modules, `Module.Flat.localizedModule` says that localization preserves flatness.

<?decl IsLocalization.flat?>
:::

**Theorem (Flat over a local ring).** Let $(R, \mathfrak m, k)$ be a local ring and $M$ a finitely presented flat $R$-module. Then $M$ is free.

*Proof.* Choose $x_1, \dots, x_n \in M$ whose images form a basis of $M/\mathfrak mM$. By Nakayama (Chapter 2, Section 2) they generate $M$, so there is an exact sequence $0 \to K \to R^n \to M \to 0$, and $K$ is finitely generated because $M$ is finitely presented. Since $M$ is flat, the sequence stays exact after tensoring with $k$: $0 \to K/\mathfrak mK \to k^n \to M/\mathfrak mM \to 0$. (This is the standard fact that $\operatorname{Tor}_1(k, M) = 0$ for flat $M$.) The map $k^n \to M/\mathfrak mM$ is an isomorphism by the choice of the $x_i$, so $K/\mathfrak mK = 0$, and $K = 0$ by Nakayama. So $M \cong R^n$. $\square$

::: mathlib
`Module.free_of_flat_of_isLocalRing` · `Mathlib.RingTheory.LocalRing.Module`

`[Module.Finite R P] [Module.Flat R P] : Module.Free R P` for a local ring `R`. The Mathlib statement needs only a finite module, not a finitely presented one: the proof shows directly that lifts of a basis of `k ⊗[R] P` are linearly independent, using flatness.

<?decl Module.free_of_flat_of_isLocalRing?>
:::

**Theorem (Differentials of a polynomial ring).** $\Omega_{R[X_1, \dots, X_n]/R}$ is free with basis $dX_1, \dots, dX_n$, and $df = \sum_i \frac{\partial f}{\partial X_i} dX_i$.

*Proof.* The map $f \mapsto \sum_i \frac{\partial f}{\partial X_i} e_i$ into the free module on $e_1, \dots, e_n$ is an $R$-derivation, so the universal property gives an $S$-linear map $\Omega \to S^n$ with $dX_i \mapsto e_i$. A derivation is determined by its values on the generators $X_i$, by the Leibniz rule, so $\Omega$ is generated by the $dX_i$, and the map $e_i \mapsto dX_i$ is an inverse. $\square$

::: mathlib
`KaehlerDifferential.mvPolynomialBasis` · `Mathlib.RingTheory.Kaehler.Polynomial`

`KaehlerDifferential.mvPolynomialBasis R σ : Basis σ (MvPolynomial σ R) Ω[MvPolynomial σ R⁄R]`, with `D (X i)` as the basis element at `i`.

<?decl KaehlerDifferential.mvPolynomialBasis?>
:::

**Theorem (Exact sequences).** Let $R \to A \to B$ be ring maps.

1. (First fundamental sequence.) $B \otimes_A \Omega_{A/R} \to \Omega_{B/R} \to \Omega_{B/A} \to 0$ is exact.
2. (Conormal sequence.) If $B = A/J$, then $J/J^2 \to B \otimes_A \Omega_{A/R} \to \Omega_{B/R} \to 0$ is exact, with the first map $\bar f \mapsto 1 \otimes df$.

*Proof sketch.* (1) $\Omega_{B/R} \to \Omega_{B/A}$ is surjective since both are spanned by the $db$, and its kernel is spanned by the $da$ with $a$ from $A$, which is the image of $B \otimes \Omega_{A/R}$. (2) $\Omega_{B/R}$ is spanned by the $d\bar a$, so the second map is surjective. A $B$-linear map from $\Omega_{B/R}$ to $N$ is a derivation $B \to N$, which is a derivation $A \to N$ that kills $J$; this identifies $\Omega_{B/R}$ with the quotient of $B \otimes \Omega_{A/R}$ by the image of $J$. $\square$

::: mathlib
`KaehlerDifferential.exact_mapBaseChange_map` · `Mathlib.RingTheory.Kaehler.Basic`

The exactness of $B \otimes_A \Omega_{A/R} \to \Omega_{B/R} \to \Omega_{B/A}$ in the middle. The conormal sequence is `KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange`, for a surjective `A → B`.

<?decl KaehlerDifferential.exact_mapBaseChange_map?>
:::

### Examples

**Example (Flat and not flat).** Over a PID, or more generally a Dedekind domain, a module is flat if and only if it is torsion free. So $\mathbb{Q}$ is a flat $\mathbb{Z}$-module, and $\mathbb{Z}/n$ is not: tensoring the injection $n : \mathbb{Z} \to \mathbb{Z}$ with $\mathbb{Z}/n$ gives the zero map on $\mathbb{Z}/n$. The ring $k[X, Y]/(XY)$ is not flat over $k[X]$: $X$ is a zero divisor on it, while tensoring $X : k[X] \to k[X]$ with a flat module gives an injection.

**Example (A plane curve).** Let $A = k[X, Y]/(f)$. By the conormal sequence,
$$\Omega_{A/k} = (A\,dx \oplus A\,dy)/A(f_X\,dx + f_Y\,dy).$$
For $f = Y^2 - X^3$ at the origin, both partial derivatives vanish, so $\Omega_{A/k} \otimes k$ has dimension $2$ there, while at a smooth point it has dimension $1$. The rank of $\Omega$ detects the singular point.

**Example (Separable and inseparable).** Let $L = K(\alpha)$ with minimal polynomial $f$. Then $\Omega_{L/K} = L\,d\alpha/(f'(\alpha)\,d\alpha)$. If $f$ is separable, $f'(\alpha) \ne 0$ and $\Omega_{L/K} = 0$. For $K = \mathbb{F}_p(t)$ and $L = K(t^{1/p})$, $f = X^p - t$ has $f' = 0$, and $\Omega_{L/K} \cong L$.

**Example (Flatness of completions).** For a Noetherian ring $R$ and an ideal $I$, the completion $\hat R$ is flat over $R$ (Chapter 6, Section 2). For a Noetherian local ring, $\hat R$ is faithfully flat.

### The library around it

The folder `Mathlib/RingTheory/Flat/` has the definition and the criteria (`Basic.lean`, `Tensor.lean`, the equational criterion in `EquationalCriterion.lean`), stability (`Stability.lean`), the torsion free criterion over Dedekind domains and Bézout domains (`TorsionFree.lean`, with `Module.Flat.instOfIsDedekindDomainOfIsTorsionFree` and `Module.Flat.torsion_eq_bot`), and faithful flatness (`FaithfullyFlat/`). The Kähler differentials are in `Mathlib/RingTheory/Kaehler/`, with the polynomial case and the behaviour under base change. Tensor products are in Volume 8.

The module `Mathlib.RingTheory.Kaehler.TensorProduct` treats base change. For a pushout square of $R \to A$ and $R \to S$ with $B = S \otimes_R A$, the map $S \otimes_R \Omega_{A/R} \to \Omega_{B/S}$ is an isomorphism, `KaehlerDifferential.tensorKaehlerEquivBase`, and `KaehlerDifferential.tensorKaehlerEquiv` is the form $B \otimes_A \Omega_{A/R} \cong \Omega_{B/S}$. The lemma `KaehlerDifferential.isBaseChange` states the same in the language of base change, and the instance `KaehlerDifferential.isLocalizedModule` says that $\Omega_{S^{-1}A/S^{-1}R}$ is the localization of $\Omega_{A/R}$.

The module `Mathlib.RingTheory.Kaehler.JacobiZariski` extends the first exact sequence to the left. For a tower $R \to S \to T$ the connecting map `Algebra.H1Cotangent.δ R S T` goes from $H_1(L_{T/S})$ to $T \otimes_S \Omega_{S/R}$, and the sequence $H_1(L_{T/R}) \to H_1(L_{T/S}) \to T \otimes_S \Omega_{S/R} \to \Omega_{T/R} \to \Omega_{T/S} \to 0$ is exact, by `Algebra.H1Cotangent.exact_map_δ` and `Algebra.H1Cotangent.exact_δ_mapBaseChange`. For a flat $T$ over $S$, `Algebra.H1Cotangent.exact_liftBaseChange_map_of_flat` adds the term $T \otimes_S H_1(L_{S/R})$ on the left. This is the Jacobi Zariski sequence of the naive cotangent complex of Section 6, and the forms for chosen generators are in the namespace of `Algebra.Generators.H1Cotangent.δ`.

Common errors of a learner:

- `Module.Flat R M` is a class whose field is about finitely generated submodules of finite modules; to use the general definition, apply `Module.Flat.lTensor_preserves_injective_linearMap` or `Module.Flat.rTensor_preserves_injective_linearMap`.
- `Ω[S⁄R]` uses the character `⁄` (U+2044), not `/`.
- Elements of `Ω[S⁄R]` are not all of the form `D s`; they are $S$-linear combinations of them.

### Exercises

1. (A) Show that a direct sum of flat modules is flat, and that a direct summand of a flat module is flat.
2. (A) Show that $\mathbb{Z}/n$ is not flat over $\mathbb{Z}$ for $n \ge 2$.
3. (A) Compute $\Omega_{A/k}$ for $A = k[X]/(X^2)$.
4. (B) Show that $\Omega_{T^{-1}S/R} \cong T^{-1}\Omega_{S/R}$ for a multiplicative subset $T \subseteq S$.
5. (B) Show that $\Omega_{\mathbb{Z}[i]/\mathbb{Z}} \cong \mathbb{Z}[i]/(2i) = \mathbb{Z}[i]/(2)$, and interpret the result with the ramified prime $2$.
6. (B) Let $f \in k[X, Y]$ and $A = k[X, Y]/(f)$. Show that $\Omega_{A/k} \otimes_A k(\mathfrak m)$ has dimension $1$ at a maximal ideal $\mathfrak m$ where $(f_X, f_Y) \not\equiv 0$, and $2$ where both vanish.
7. (C) Show that a faithfully flat ring map $R \to S$ is injective, and that $IS \cap R = I$ for every ideal $I$ of $R$.

### Notes and history

Flatness was introduced by Serre in 1956, in *Géométrie algébrique et géométrie analytique*. The module of differentials is named after Erich Kähler, and Grothendieck made it the basis of the definitions of smooth and étale morphisms in the *Éléments de géométrie algébrique*.

### Reference

<?reference?>
