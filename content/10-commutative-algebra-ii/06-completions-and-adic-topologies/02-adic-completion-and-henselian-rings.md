---
title: Adic completion and Henselian rings
kind: theory
modules:
  - Mathlib.RingTheory.AdicCompletion.Basic
  - Mathlib.RingTheory.AdicCompletion.Completeness
  - Mathlib.RingTheory.AdicCompletion.AsTensorProduct
  - Mathlib.RingTheory.AdicCompletion.Exactness
  - Mathlib.RingTheory.AdicCompletion.LocalRing
  - Mathlib.RingTheory.AdicCompletion.Noetherian
  - Mathlib.RingTheory.Henselian
explains:
  E3: [AdicCompletion, IsAdicComplete, AdicCompletion.isAdicComplete, HenselianLocalRing, IsAdicComplete.henselianRing]
  E2: [IsHausdorff, IsPrecomplete, AdicCompletion.of, AdicCompletion.of_injective_iff, AdicCompletion.ofLinearEquiv, AdicCompletion.AdicCauchySequence, IsAdicComplete.le_jacobson, IsHausdorff.of_le_jacobson, HenselianRing, HenselianLocalRing.TFAE, Field.henselian, PowerSeries.instIsAdicCompleteSpanSingletonSetX, AdicCompletion.ofTensorProductEquivOfFiniteNoetherian, AdicCompletion.flat_of_isNoetherian, AdicCompletion.map_exact, AdicCompletion.isLocalRing_of_fg]
  E1: auto
families: []
requires: [V10.C02]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Adic completion and Henselian rings

### Overview

The $I$-adic completion of a module $M$ is the module of compatible systems of elements of the quotients $M/I^nM$. It plays the role of the real numbers for the $I$-adic topology: Cauchy sequences converge in it. The completion of $\mathbb{Z}$ at $(p)$ is the ring $\mathbb{Z}_p$ of $p$-adic integers, and the completion of $k[X]$ at $(X)$ is the power series ring $k[[X]]$.

Over a Noetherian ring, completion is exact on finite modules, and the completion of a finite module $M$ is $\hat R \otimes_R M$. So $\hat R$ is flat over $R$. A complete ring has Hensel's lemma: a simple root of a polynomial modulo $I$ lifts to a root. The local rings with this property are the Henselian local rings.

### Definitions

**Definition (Hausdorff, precomplete, complete).** Let $I$ be an ideal of $R$ and $M$ an $R$-module. A sequence $(x_n)$ in $M$ is $I$-adically Cauchy if $x_m \equiv x_n \pmod{I^mM}$ for all $m \le n$. The module $M$ is Hausdorff if $\bigcap_n I^nM = 0$, precomplete if every Cauchy sequence has a limit $x$ with $x_n \equiv x \pmod{I^nM}$ for all $n$, and complete if it is both.

::: mathlib
`IsAdicComplete` · `Mathlib.RingTheory.AdicCompletion.Basic`

`IsAdicComplete I M` extends `IsHausdorff I M` and `IsPrecomplete I M`. The two conditions are stated with `SModEq` modulo `I ^ n • ⊤`, the same convention as in the text. For a ring, `IsAdicComplete.le_jacobson` gives `I` in the Jacobson radical. Conversely, `IsHausdorff.of_le_jacobson` is the Krull intersection theorem of Section 1 in this language, for a finite module over a Noetherian ring.

<?decl IsAdicComplete?>
:::

**Definition (Adic completion).** The $I$-adic completion of $M$ is
$$\hat M = \varprojlim_n M/I^nM = \Big\{ (x_n) \in \prod_n M/I^nM : x_n \equiv x_m \pmod{I^mM} \text{ for } m \le n \Big\}.$$
The map $M \to \hat M$ sends $x$ to $(x \bmod I^nM)_n$. Its kernel is $\bigcap_n I^nM$, so it is injective if and only if $M$ is Hausdorff. It is an isomorphism if and only if $M$ is complete. For $M = R$, $\hat R$ is a ring and $\hat M$ is an $\hat R$-module.

::: mathlib
`AdicCompletion` · `Mathlib.RingTheory.AdicCompletion.Basic`

`AdicCompletion I M` is the subtype of `∀ n, M ⧸ (I ^ n • ⊤)` of compatible families. The map from `M` is `AdicCompletion.of I M`, with `AdicCompletion.of_injective_iff : Function.Injective (of I M) ↔ IsHausdorff I M`, and `AdicCompletion.ofLinearEquiv` is the isomorphism for a complete module. Elements can also be built from `AdicCompletion.AdicCauchySequence`. For `M = R`, an algebra structure makes `AdicCompletion I R` a ring.

<?decl AdicCompletion?>
:::

**Definition (Henselian local ring).** A local ring $(R, \mathfrak m)$ is Henselian if for every monic $f \in R[X]$ and $a_0 \in R$ with $f(a_0) \in \mathfrak m$ and $f'(a_0)$ a unit, there is $a \in R$ with $f(a) = 0$ and $a \equiv a_0 \pmod{\mathfrak m}$. More generally, $R$ is Henselian at an ideal $I$ if $I$ is in the Jacobson radical and the same holds with $I$ in place of $\mathfrak m$, the condition on $f'(a_0)$ being that it is a unit modulo $I$.

::: mathlib
`HenselianLocalRing` · `Mathlib.RingTheory.Henselian`

`HenselianLocalRing R` extends `IsLocalRing R` with the field `is_henselian`, exactly the condition in the text. `HenselianRing R I` is the version for an ideal, with fields `jac` and `is_henselian`. `HenselianLocalRing.TFAE` gives the equivalent forms with roots in the residue field: a simple root $\bar a$ of $\bar f$ in $R/\mathfrak m$ lifts to a root of $f$. Every field is Henselian, `Field.henselian`. The index of this edition has no declaration for the equivalent condition that every finite $R$-algebra is a product of local rings.

<?decl HenselianLocalRing?>
:::

### Theorems and proofs

**Theorem (The completion is complete).** If $I$ is finitely generated, then $\hat M$ is $I$-adically complete, and $I^n\hat M$ is the kernel of $\hat M \to M/I^nM$.

*Proof.* The second claim is the main point. Let $K_n$ be the kernel of $\hat M \to M/I^nM$, so $\hat M/K_n \cong M/I^nM$. Clearly $I^n\hat M \subseteq K_n$. For the other inclusion, let $I = (a_1, \dots, a_r)$. Then $I^n$ is generated by the finitely many monomials $m_1, \dots, m_s$ of degree $n$ in the $a_i$. An element $(x_k) \in K_n$ has $x_k \in I^nM/I^kM$ for $k \ge n$, so $x_k = \sum_j m_jy_{k,j}$. The $y_{k,j}$ can be chosen compatibly in $k$ (this is the technical step of the proof): each step lifts a solution modulo $I^{k}M$ to one modulo $I^{k+1}M$, with a correction in $I^{k-n}M$, because $I^{k}M = I^n \cdot I^{k-n}M$. The compatible systems $y_j = (y_{k,j} \bmod I^{k-n}M)_k$ are elements of $\hat M$, and $(x_k) = \sum_j m_jy_j \in I^n\hat M$.

Given $K_n = I^n\hat M$, the completeness is formal. If $\xi \in \bigcap I^n\hat M = \bigcap K_n$, all components of $\xi$ are $0$. A Cauchy sequence $(\xi^{(m)})$ in $\hat M$ has, for each $n$, eventually constant images in $\hat M/K_n = M/I^nM$, and these images form a compatible system, which is the limit. $\square$

::: mathlib
`AdicCompletion.isAdicComplete` · `Mathlib.RingTheory.AdicCompletion.Completeness`

`AdicCompletion.isAdicComplete (h : I.FG) : IsAdicComplete I (AdicCompletion I M)`. The docstring of `AdicCompletion` notes that the completion is Hausdorff for every ideal but need not be complete without the finiteness. The instance `PowerSeries.instIsAdicCompleteSpanSingletonSetX` says that `PowerSeries R` is complete for the ideal `(X)`, by comparison with the completion of the polynomial ring.

<?decl AdicCompletion.isAdicComplete?>
:::

**Theorem (Hensel's lemma).** Let $R$ be $I$-adically complete. Let $f \in R[X]$, and $a_0 \in R$ with $f(a_0) \in I$ and $f'(a_0)$ a unit modulo $I$. Then there is $a \in R$ with $f(a) = 0$ and $a \equiv a_0 \pmod I$. In particular, a complete local ring is Henselian.

*Proof.* Since $R$ is complete, $I$ is in the Jacobson radical: for $x \in I$, the series $1 + x + x^2 + \cdots$ converges and is an inverse of $1 - x$. So an element that is a unit modulo $I$ is a unit.

Taylor expansion in $R[X, Y]$ gives $f(X + Y) = f(X) + f'(X)Y + Y^2g(X, Y)$ for a polynomial $g$. Define $a_{n+1} = a_n - f(a_n)/f'(a_n)$. By induction: $a_n \equiv a_0 \pmod I$, so $f'(a_n) \equiv f'(a_0) \pmod I$ is a unit; and $f(a_n) \in I^{2^n}$. Indeed, with $h = -f(a_n)/f'(a_n) \in I^{2^n}$,
$$f(a_{n+1}) = f(a_n) + f'(a_n)h + h^2g(a_n, h) = h^2g(a_n, h) \in I^{2^{n+1}}.$$
Since $a_{n+1} - a_n = h \in I^{2^n}$, the sequence is Cauchy, with limit $a$, and $a \equiv a_0 \pmod I$. For each $n$, $a \equiv a_n \pmod{I^{2^n}}$, so $f(a) \equiv f(a_n) \equiv 0 \pmod{I^{2^n}}$. As $R$ is Hausdorff, $f(a) = 0$. $\square$

::: mathlib
`IsAdicComplete.henselianRing` · `Mathlib.RingTheory.Henselian`

The instance `[IsAdicComplete I R] : HenselianRing R I`. The proof defines the Newton sequence as in the text. Together with the instance that a Henselian local ring is Henselian at its maximal ideal, this places the complete local rings among the Henselian ones.

<?decl IsAdicComplete.henselianRing?>
:::

**Theorem (Completion over a Noetherian ring).** Let $R$ be Noetherian and $I$ an ideal. Then:

1. For a finite $R$-module $M$, the natural map $\hat R \otimes_R M \to \hat M$ is an isomorphism.
2. On finite modules, $M \mapsto \hat M$ is exact.
3. $\hat R$ is a flat $R$-module.

*Proof.* (2) Let $0 \to N \to M \to P \to 0$ be exact with $M$ finite. For each $n$ there is an exact sequence $0 \to N/(I^nM \cap N) \to M/I^nM \to P/I^nP \to 0$. An inverse limit of short exact sequences is again short exact when the transition maps of the left terms are surjective (the Mittag-Leffler condition), and they are surjective here. So $0 \to \varprojlim N/(I^nM \cap N) \to \hat M \to \hat P \to 0$ is exact. By Artin-Rees (Section 1), the filtrations $I^nM \cap N$ and $I^nN$ define the same topology, so the first limit is $\hat N$.

(1) The map is an isomorphism for $M = R^n$, since both sides commute with finite direct sums. For general $M$, take a presentation $R^m \to R^n \to M \to 0$. Tensor product is right exact, and completion is right exact by (2). The five lemma gives (1).

(3) By (1) and (2), $N \mapsto \hat R \otimes_R N$ preserves injections of finite modules. A module with this property for finitely generated ideals $N \subseteq R$ is flat (Chapter 8, Section 1). $\square$

::: mathlib
`AdicCompletion.ofTensorProductEquivOfFiniteNoetherian` · `Mathlib.RingTheory.AdicCompletion.AsTensorProduct`

The isomorphism `AdicCompletion I R ⊗[R] M ≃ₗ[AdicCompletion I R] AdicCompletion I M` for `[IsNoetherianRing R] [Module.Finite R M]`. The same file has the instance `AdicCompletion.flat_of_isNoetherian : Module.Flat R (AdicCompletion I R)`, and `AdicCompletion.map_exact` in `AdicCompletion/Exactness.lean` is the exactness.

<?decl AdicCompletion.ofTensorProductEquivOfFiniteNoetherian?>
:::

### Examples

**Example ($p$-adic integers).** The completion of $\mathbb{Z}$ at $(p)$ is $\mathbb{Z}_p = \varprojlim \mathbb{Z}/p^n$. Hensel's lemma for $f = X^2 + 1$ and $p = 5$: $a_0 = 2$ has $f(2) = 5 \in (5)$ and $f'(2) = 4$, a unit modulo $5$. So $-1$ has a square root in $\mathbb{Z}_5$, congruent to $2$ modulo $5$. The first Newton step gives $a_1 = 2 - 5/4$, which is $2 - 5 \cdot 4^{-1} \equiv 2 - 5 \cdot 19 \equiv 7 \pmod{25}$, and $7^2 + 1 = 50 \equiv 0 \pmod{25}$. The ring $\mathbb{Z}_p$ and its fraction field are studied in Volume 12.

**Example (Power series).** The completion of $k[X_1, \dots, X_n]$ at $(X_1, \dots, X_n)$ is $k[[X_1, \dots, X_n]]$. The ring $k[[X]]$ is Henselian. With $k$ of characteristic not $2$, $f = Y^2 - (1 + X)$ and $a_0 = 1$: $f(1) = -X \in (X)$, $f'(1) = 2$. The root is the binomial series $\sqrt{1 + X} = 1 + \frac12X - \frac18X^2 + \cdots$.

**Example (A Henselian ring that is not complete).** The ring of power series in $k[[X]]$ that are algebraic over $k(X)$ is a Henselian local ring, but it is countable when $k$ is countable, so it is not complete. The local ring $\mathbb{Z}_{(p)}$ is not Henselian: $X^2 + 1$ has the simple root $2$ modulo $5$ but no root in $\mathbb{Q}$.

**Example (A non-Noetherian failure).** Let $R = k[X_1, X_2, \dots]$ and $I = (X_1, X_2, \dots)$. The ideal $I$ is not finitely generated, and the completion $\hat R$ is not $I$-adically complete in general. This is why `AdicCompletion.isAdicComplete` needs `I.FG`.

### The library around it

The folder `Mathlib/RingTheory/AdicCompletion/` has the definition, the functoriality (`Functoriality.lean`), the ring and algebra structures (`Algebra.lean`), the exactness over Noetherian rings, the comparison with the tensor product and the flatness, and the local ring results: `AdicCompletion.isLocalRing_of_fg` says that the completion of a local ring at a finitely generated maximal ideal is local. The topology of Section 1 and the completion of a uniform space are in Volume 14; for a Noetherian ring and the adic topology, the two completions agree. The Henselian property is in `Mathlib/RingTheory/Henselian.lean`.

Common errors of a learner:

- `IsAdicComplete I M` is a class with two parents. To use precompleteness, take `IsPrecomplete.prec`; the Hausdorff property is `IsHausdorff.haus`.
- The completion of `R` at `I` is `AdicCompletion I R`, a type with an algebra structure; it is not a subring of `R`. The map `AdicCompletion.of I R` is injective only when `R` is Hausdorff.
- `HenselianLocalRing` asks for `f.Monic`. For non-monic polynomials, divide by the unit leading coefficient or use the equivalent forms of `HenselianLocalRing.TFAE`.

### Exercises

1. (A) Show that the kernel of $M \to \hat M$ is $\bigcap_n I^nM$.
2. (A) Compute a square root of $-1$ in $\mathbb{Z}_5$ modulo $125$.
3. (A) Show that $\mathbb{Z}/p^k$ is $p$-adically complete, and that its completion is itself.
4. (B) Show that $k[[X]]$ is $(X)$-adically complete, directly from the definition.
5. (B) Let $R$ be complete for $I$. Show that $x \in R$ is a unit if and only if its image in $R/I$ is a unit.
6. (B) Use Hensel's lemma to show that a unit $u \in \mathbb{Z}_p$, $p$ odd, is a square if and only if its image in $\mathbb{F}_p$ is a square.
7. (B) Show that the completion of $\mathbb{Z}$ at $(6)$ is $\mathbb{Z}_2 \times \mathbb{Z}_3$.
8. (C) Show that $\mathbb{Z}_{(p)}$ is not Henselian for every prime $p$, by choosing a polynomial with a simple root modulo $p$ and no rational root.

### Notes and history

Kurt Hensel introduced the $p$-adic numbers around 1897, with the lemma that bears his name as a tool to lift roots. Henselian local rings were introduced by Azumaya in 1951, and Nagata developed their theory.

### Reference

<?reference?>
