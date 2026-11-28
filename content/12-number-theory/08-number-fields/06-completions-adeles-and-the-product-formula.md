---
title: Completions, adeles and the product formula
kind: api
modules:
  - Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
  - Mathlib.NumberTheory.NumberField.Completion.FinitePlace
  - Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
  - Mathlib.NumberTheory.NumberField.Completion.Ramification
  - Mathlib.NumberTheory.Padics.HeightOneSpectrum
  - Mathlib.NumberTheory.NumberField.ProductFormula
  - Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
  - Mathlib.NumberTheory.NumberField.FiniteAdeleRing
  - Mathlib.NumberTheory.NumberField.AdeleRing
explains:
  E2: [NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal, NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex, NumberField.FinitePlace.norm_lt_one_iff_mem, NumberField.FinitePlace.prod_eq_inv_abs_norm, NumberField.prod_abs_eq_one, NumberField.InfinitePlace.sum_inertiaDeg_eq_finrank, NumberField.AdeleRing.isUnit_iff, NumberField.AdeleRing.norm_algebraMap_eq_one_of_ne_zero]
  E1: auto
families: []
requires: [V10.C04, V12.C05, V14.C03, V14.C08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Completions, adeles and the product formula

### Overview

A number field $K$ has two kinds of places. An infinite place is an absolute value $|\sigma(\cdot)|$ that comes from an embedding $\sigma : K \to \mathbb{C}$ (Section 2). A finite place comes from a nonzero prime ideal $\mathfrak p$ of $\mathcal{O}_K$: it is the absolute value $|x|_{\mathfrak p} = N(\mathfrak p)^{-v_{\mathfrak p}(x)}$. The completion of $K$ at an infinite place is $\mathbb{R}$ or $\mathbb{C}$. The completion at a finite place is a local field, the analogue of $\mathbb{Q}_p$ of Chapter 5.

These modules build the two kinds of completions, prove the product formula $\prod_v |x|_v = 1$ for $x \in K^\times$, and put all completions together into the adele ring $\mathbb{A}_K$, its group of units (the ideles) and the idele class group. The finite adele ring of a Dedekind domain is in Volume 10, Chapter 4, and the absolute values and the type synonym `WithAbs` are in Volume 14, Chapter 8. The mixed space $\mathbb{R}^{r_1} \times \mathbb{C}^{r_2}$ of the canonical embedding section reappears here as the infinite adele ring.

### The library around it

#### The completion at an infinite place

An infinite place `v : InfinitePlace K` is an absolute value on $K$, but $K$ already has other uniform structures, one for each place. To complete $K$ at $v$, Mathlib puts the uniform structure of $v$ on the type synonym `WithAbs v` and takes `UniformSpace.Completion` of it. The result is `NumberField.InfinitePlace.Completion v`, written $v$`.Completion` in the text below. It is the completion `AbsoluteValue.Completion` of the absolute value of $v$, so the general lemmas about `AbsoluteValue.Completion` of Volume 14, Chapter 8 apply to it. The coercion from `WithAbs v` is a ring map with dense range (`AbsoluteValue.Completion.denseRange_coe`), and `AbsoluteValue.Completion.norm_coe` says that the norm of the image of $x$ is $v(x)$.

The embedding $\sigma$ of $v$ is an isometry from $(K, v)$ to $\mathbb{C}$ (`NumberField.InfinitePlace.isometry_embedding`). By the universal property of the completion, it extends to a ring map `NumberField.InfinitePlace.Completion.extensionEmbedding v : v.Completion →+* ℂ`, which is again an isometry (`NumberField.InfinitePlace.Completion.isometry_extensionEmbedding`). Its image is closed, because the completion is complete, and it contains $\sigma(K)$.

**Proposition.** If $v$ is real, then $v$`.Completion` $\cong \mathbb{R}$ (`NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal`). If $v$ is complex, then $v$`.Completion` $\cong \mathbb{C}$ (`NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex`).

*Proof.* The image $E$ of `extensionEmbedding` is a closed subfield of $\mathbb{C}$ that contains $\mathbb{Q}$, so it contains the closure $\mathbb{R}$ of $\mathbb{Q}$. A subfield between $\mathbb{R}$ and $\mathbb{C}$ is $\mathbb{R}$ or $\mathbb{C}$. If $v$ is real, then $\sigma(K) \subseteq \mathbb{R}$, so $E = \overline{\sigma(K)} \subseteq \mathbb{R}$ and $E = \mathbb{R}$. If $v$ is complex, then $\sigma(K) \not\subseteq \mathbb{R}$, so $E = \mathbb{C}$. The map is injective because it is an isometry. $\square$

For a real place, the map to $\mathbb{R}$ is `NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal`. The isometric forms are `NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal` and `NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex`. So each completion is locally compact (`NumberField.InfinitePlace.Completion.locallyCompactSpace`). For $K = \mathbb{Q}$ the only infinite place gives the usual absolute value (`NumberField.InfinitePlace.Completion.Rat.norm_infinitePlace_completion`).

#### Finite places

Let $R$ be a Dedekind domain with fraction field $K$, and let `v : HeightOneSpectrum R` be a nonzero prime $\mathfrak p$. The hypothesis `Ring.HasFiniteQuotients R` says that each quotient $R/I$ by a nonzero ideal is finite; it holds for $\mathcal{O}_K$ and for $\mathbb{Z}$, so many statements of the module are stated for this general $R$. The absolute value `NumberField.HeightOneSpectrum.adicAbv K v` is $|x|_{\mathfrak p} = N(\mathfrak p)^{-v_{\mathfrak p}(x)}$, built from the valuation `IsDedekindDomain.HeightOneSpectrum.valuation K v` (`NumberField.HeightOneSpectrum.adicAbv_def`). It is nonarchimedean (`NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv`). The completion `IsDedekindDomain.HeightOneSpectrum.adicCompletion K v` receives the map `NumberField.FinitePlace.embedding v`, and `NumberField.FinitePlace.norm_embedding` says that the norm of the image is $|x|_{\mathfrak p}$.

For $x \in R$ the rules are the expected ones.

| Lean name | Statement |
|---|---|
| `NumberField.FinitePlace.norm_le_one` | $|x|_{\mathfrak p} \le 1$ |
| `NumberField.FinitePlace.norm_lt_one_iff_mem` | $|x|_{\mathfrak p} < 1 \iff x \in \mathfrak p$ |
| `NumberField.FinitePlace.norm_eq_one_iff_notMem` | $|x|_{\mathfrak p} = 1 \iff x \notin \mathfrak p$ |
| `NumberField.HeightOneSpectrum.embedding_mul_absNorm` | $|x|_{\mathfrak p} \cdot N(\mathfrak p^{v_{\mathfrak p}(x)}) = 1$ for $x \ne 0$ |
| `NumberField.FinitePlace.two_le_norm_of_one_lt_norm` | in the completion, $|y| > 1$ implies $|y| \ge 2$ |

The proof of `NumberField.FinitePlace.norm_lt_one_iff_mem` is one line: $|x|_{\mathfrak p} = N(\mathfrak p)^{-v_{\mathfrak p}(x)}$ with $N(\mathfrak p) \ge 2$ (`NumberField.HeightOneSpectrum.two_le_absNorm_nnreal`), so $|x|_{\mathfrak p} < 1$ exactly when $v_{\mathfrak p}(x) \ge 1$, that is, when $x \in \mathfrak p$.

For a number field, `NumberField.FinitePlace K` is the type of absolute values of $K$ of this form. Its terms act as functions $K \to \mathbb{R}$ through a `FunLike` instance, and they are nonarchimedean (`NumberField.FinitePlace.add_le`). The map `NumberField.FinitePlace.mk` makes a place from a prime, `NumberField.FinitePlace.maximalIdeal` recovers the prime, and `NumberField.FinitePlace.equivHeightOneSpectrum` says that the two are inverse bijections. The predicate `NumberField.IsFinitePlace` on `AbsoluteValue K ℝ` is characterized by `NumberField.isFinitePlace_iff`.

#### The rational case

`Mathlib.NumberTheory.Padics.HeightOneSpectrum` compares the completions of $\mathbb{Q}$ at the primes of a ring $R$ of integers of $\mathbb{Q}$ with the fields $\mathbb{Q}_p$ of Chapter 5. The equivalence `Rat.HeightOneSpectrum.primesEquiv` matches the height one primes of $R$ with `Nat.Primes`, and `Rat.HeightOneSpectrum.natGenerator v` is the positive prime number that generates $v$ (`Rat.HeightOneSpectrum.span_natGenerator`). The valuation of $v$ and the $p$-adic valuation `Rat.padicValuation p` are equivalent (`Rat.HeightOneSpectrum.valuation_equiv_padicValuation`). So the two completions agree: `Rat.HeightOneSpectrum.adicCompletion.padicEquiv v` is a continuous $\mathbb{Q}$-algebra isomorphism from the adic completion to `ℚ_[p]`, and `Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v` does the same for the rings of integers and `ℤ_[p]`. The maps in the other direction are `Padic.adicCompletionEquiv` and `PadicInt.adicCompletionIntegersEquiv`.

#### The product formula

Each place of $K$ has a multiplicity $m_w$: $1$ for a real place and $2$ for a complex place (`NumberField.InfinitePlace.mult`).

**Theorem (Product formula).** For $x \in K^\times$,
$$\prod_{w \text{ infinite}} w(x)^{m_w} \cdot \prod_{w \text{ finite}} w(x) = 1.$$

In Lean this is `NumberField.prod_abs_eq_one`; the finite product uses `finprod`, and `NumberField.FinitePlace.hasFiniteMulSupport` says that $w(x) = 1$ for all but finitely many $w$.

*Proof.* The infinite part is $\prod_\sigma |\sigma(x)| = |N_{K/\mathbb{Q}}(x)|$, since a complex place counts its two conjugate embeddings. For the finite part, `NumberField.FinitePlace.prod_eq_inv_abs_norm` states $\prod_{w} w(x) = |N_{K/\mathbb{Q}}(x)|^{-1}$. For $x \in \mathcal{O}_K$, the ideal $(x)$ is $\prod_{\mathfrak p} \mathfrak p^{v_{\mathfrak p}(x)}$, so $|N(x)| = N((x)) = \prod_{\mathfrak p} N(\mathfrak p)^{v_{\mathfrak p}(x)}$, and this is the inverse of $\prod_{\mathfrak p} |x|_{\mathfrak p}$. The form for integers is `NumberField.FinitePlace.prod_eq_inv_abs_norm_int`. A general $x$ is a quotient $a/b$ of integers, and both sides are multiplicative. The two parts multiply to $1$. $\square$

For $K = \mathbb{Q}$ and $x = -12$: the infinite place gives $12$, the place at $2$ gives $2^{-2}$, the place at $3$ gives $3^{-1}$, and the other places give $1$. The product is $12 \cdot \frac14 \cdot \frac13 = 1$.

#### Extensions of places and local degrees

Let $L/K$ be an extension of number fields, $v$ an infinite place of $K$, and $w$ a place of $L$ over $v$ (the predicate `w.LiesOver v`). `Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances` gives the instances `NumberField.LiesOver.instAlgebraCompletion`, `NumberField.LiesOver.instIsScalarTowerCompletion` and `NumberField.LiesOver.instContinuousSMulCompletion`. So $w$`.Completion` is a $v$`.Completion`-algebra, and the ring map between the completions is `AbsoluteValue.Completion.map`. By `AbsoluteValue.Completion.algebra_eq_of_liesOver`, this is the only algebra structure that is compatible with $K \to L$ and has a continuous action.

`Mathlib.NumberTheory.NumberField.Completion.Ramification` defines the local degree `NumberField.InfinitePlace.inertiaDeg v w` as $[L_w : K_v]$ when $w$ lies over $v$, and $0$ otherwise (`NumberField.InfinitePlace.inertiaDeg_eq_finrank`). The local degree is $1$ or $2$: it is $2$ exactly when $v$ is real and $w$ is complex, that is, when $w$ is ramified over $v$ in the sense of Section 4 (`NumberField.InfinitePlace.IsRamified.finrank_eq_two`, `NumberField.InfinitePlace.IsUnramified.finrank_eq_one`). The multiplicities satisfy $m_v \cdot [L_w : K_v] = m_w$ (`NumberField.InfinitePlace.mult_mul_finrank`).

**Theorem (Sum of local degrees).** $\sum_{w \mid v} [L_w : K_v] = [L : K]$ (`NumberField.InfinitePlace.sum_inertiaDeg_eq_finrank`).

*About the proof.* The embeddings of $L$ into $\mathbb{C}$ that extend a fixed embedding $\sigma$ of $v$ are $[L : K]$ in number. If $v$ is complex, then each place $w$ over $v$ is complex and takes exactly one of these embeddings, and $[L_w : K_v] = 1$. If $v$ is real, then a real $w$ takes one extension of $\sigma$ and a complex $w$ takes two, and $[L_w : K_v]$ is $1$ or $2$ accordingly. In both cases the sum counts each extension of $\sigma$ once.

#### The adele ring

The infinite adele ring `NumberField.InfiniteAdeleRing K`, with the notation `K∞`, is the product $\prod_v K_v$ over the infinite places, a finite product. The ring equivalence `NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace` identifies it with the mixed space $\mathbb{R}^{r_1} \times \mathbb{C}^{r_2}$, and `NumberField.InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp` says that the mixed embedding is the diagonal map $K \to K_\infty$ followed by this equivalence. The ring is locally compact (`NumberField.InfiniteAdeleRing.locallyCompactSpace`), and $K$ is dense in it (`NumberField.InfiniteAdeleRing.denseRange_algebraMap`). Its norm is $\|x\| = \prod_v \|x_v\|^{m_v}$ (`NumberField.InfiniteAdeleRing.norm_def`), and on the diagonal it is $|N_{K/\mathbb{Q}}(x)|$ (`NumberField.InfiniteAdeleRing.coe_norm_eq_abs_norm`).

The finite adele ring `IsDedekindDomain.FiniteAdeleRing R K` of Volume 10, with the notation `𝔸ᶠ[K]` for $R = \mathcal{O}_K$, gets a norm in `Mathlib.NumberTheory.NumberField.FiniteAdeleRing`: $\|x\| = \prod'_v \|x_v\|$ (`NumberField.FiniteAdeleRing.norm_def`). For a unit only finitely many factors differ from $1$, and the product is a `finprod` (`NumberField.FiniteAdeleRing.norm_eq_finprod_of_isUnit`). For a non unit the norm is $0$ (`NumberField.FiniteAdeleRing.norm_eq_zero_of_not_isUnit`). On the diagonal, $\|x\| = |N_{K/\mathbb{Q}}(x)|^{-1}$ for $x \ne 0$ (`NumberField.FiniteAdeleRing.coe_norm_eq_inv_abs_norm`), which is the finite half of the product formula.

The adele ring is `NumberField.AdeleRing R K := InfiniteAdeleRing K × FiniteAdeleRing R K`, with the notations `𝔸[R, K]` and `𝔸[K]`. It is a topological commutative $K$-algebra, and $K$ embeds diagonally (`NumberField.AdeleRing.algebraMap_injective`). The image of $K$ is the additive subgroup `NumberField.AdeleRing.principalSubgroup`. The maps `NumberField.AdeleRing.ofCompletion` and `NumberField.AdeleRing.ofAdicCompletion` put an element of one completion at its place and $1$ at the other places.

**Proposition.** An adele $x$ is a unit if and only if each component $x_v$ is nonzero and $|x_v|_v = 1$ for all but finitely many finite places $v$ (`NumberField.AdeleRing.isUnit_iff`).

*Proof.* A unit of a product is a pair of units. The infinite part is a finite product of fields, so its units are the families with nonzero components. In the finite adele ring, $x$ and $x^{-1}$ are integral at almost all $v$, so $|x_v|_v \le 1$ and $|x_v|_v^{-1} \le 1$ there, and $|x_v|_v = 1$. Conversely, if $|x_v|_v = 1$ at almost all $v$, then the family $(x_v^{-1})$ is again integral at almost all $v$, so it is a finite adele and it is the inverse of $x$. $\square$

The norm of an adele is $\|x\| = \|x_\infty\| \cdot \|x_f\|$ (`NumberField.AdeleRing.norm_def`).

**Theorem (Product formula for adeles).** For $x \in K^\times$, the diagonal adele of $x$ has norm $1$ (`NumberField.AdeleRing.norm_algebraMap_eq_one_of_ne_zero`).

*Proof.* By the two diagonal formulas above, $\|x\| = |N(x)| \cdot |N(x)|^{-1} = 1$. $\square$

The idele group `NumberField.IdeleGroup R K` is the unit group $\mathbb{A}_K^\times$. The map `NumberField.IdeleGroup.unitEmbedding` sends $K^\times$ into it, its image is `NumberField.IdeleGroup.principalSubgroup`, and the quotient is the idele class group `NumberField.IdeleClassGroup R K`. Each local unit group maps into both groups by `NumberField.IdeleGroup.ofCompletion`, `NumberField.IdeleGroup.ofAdicCompletion`, `NumberField.IdeleClassGroup.ofCompletion` and `NumberField.IdeleClassGroup.ofAdicCompletion`. The index of this edition has no declaration for the compactness of the norm one idele classes or for the link with the class group.

#### Common errors

1. Each place of $K$ gives a different uniform structure on $K$. Do not complete `K` itself: complete `WithAbs v`, and move elements in and out of the synonym with `WithAbs.equiv`. The coercion `WithAbs v → v.Completion` is the map to use.
2. The product formula needs the multiplicities: a complex place enters with the square $w(x)^2$. The plain product $\prod_w w(x)$ over the infinite places is not $|N(x)|$ when $r_2 > 0$.
3. The name `NumberField.InfinitePlace.inertiaDeg` is a local degree of completions at infinite places. The residue degree of a prime ideal is `Ideal.inertiaDeg`, treated in the section on prime ideals and ramification.

### Exercises

1. (A) Check the product formula for $x = \frac{3}{10} \in \mathbb{Q}$ and for $x = 1 + i \in \mathbb{Q}(i)$, with all places that give a factor different from $1$.
2. (A) Show that the diagonal image of $\mathbb{Q}$ in the adeles of $\mathbb{Q}$ meets $\mathbb{R} \times \prod_p \mathbb{Z}_p$ in $\mathbb{Z}$.
3. (A) Let $L = \mathbb{Q}(\sqrt[3]2)$ and let $v$ be the infinite place of $\mathbb{Q}$. List the places $w$ of $L$ over $v$ and their local degrees, and check that the sum is $3$.
4. (B) Show that a finite place $w$ of $K$ satisfies $w(n) \le 1$ for every integer $n$, and that $w(p) < 1$ for exactly one prime number $p$.
5. (B) Use the product formula to show that $x \in K^\times$ with $w(x) \le 1$ at every place $w$ is a root of unity.
6. (C) Show that $\mathbb{Q}$ is a discrete subgroup of the adele ring of $\mathbb{Q}$ and that the quotient is compact.

### Reference

<?reference?>
