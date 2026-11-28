---
title: Hilbert spaces and l2
kind: theory
modules:
  - Mathlib.Analysis.InnerProductSpace.l2Space
  - Mathlib.Analysis.InnerProductSpace.Orthonormal
explains:
  E3: [lp.instInnerProductSpace, HilbertBasis, HilbertBasis.hasSum_repr, exists_hilbertBasis]
  E2: [lp.inner_eq_tsum, lp.hasSum_inner, lp.summable_inner, Orthonormal.inner_products_summable, exists_maximal_orthonormal, HilbertBasis.repr, HilbertBasis.repr_apply_apply, HilbertBasis.repr_self, HilbertBasis.orthonormal, HilbertBasis.dense_span, HilbertBasis.hasSum_repr_symm, HilbertBasis.tsum_inner_mul_inner, HilbertBasis.mk, HilbertBasis.mkOfOrthogonalEqBot, HilbertBasis.coe_mkOfOrthogonalEqBot, Orthonormal.exists_hilbertBasis_extension, OrthogonalFamily.linearIsometry]
  E1: auto
families: []
requires: [V04, V07, V13, V16.C01, V16.C02]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Hilbert spaces and l2

### Overview

A Hilbert space is a complete inner product space. Completeness turns the finite expansions of Section 2 into infinite ones. For an orthonormal family $(e_i)$ in a Hilbert space and a vector $x$, the series $\sum_i \langle e_i, x \rangle e_i$ converges, and it converges to $x$ for each $x$ exactly when the span of the family is dense. Such a family is a Hilbert basis. Zorn's lemma gives a Hilbert basis in each Hilbert space, and the coefficients define an isometric isomorphism onto the space $\ell^2(\iota)$. So up to isometry the Hilbert spaces are the spaces $\ell^2(\iota)$, one for each cardinal. Mathlib takes this isometry as the definition of a Hilbert basis.

### Definitions

**Definition (Hilbert space).** A *Hilbert space* is an inner product space that is complete for the norm of its inner product.

In Mathlib a Hilbert space is `[NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]`, as for Banach spaces in Chapter 4. There is no separate class.

**Definition (the space $\ell^2(\iota)$).** For a set $\iota$, $\ell^2(\iota)$ is the space of functions $c : \iota \to \mathbb{K}$ with $\sum_{i \in \iota} |c_i|^2 < \infty$, with
$$\langle c, d \rangle = \sum_{i \in \iota} \overline{c_i}\, d_i.$$
The sums over $\iota$ are unconditional sums: the limit of the net of finite partial sums, as in Chapter 1, Section 3.

::: mathlib
`lp.instInnerProductSpace` · `Mathlib.Analysis.InnerProductSpace.l2Space`

The space is `lp G 2` from Chapter 1, Section 3, a subgroup of `∀ i, G i`, written `ℓ²(ι, 𝕜)` with `G i = 𝕜` in the notation of the file. The instance gives `InnerProductSpace 𝕜 (lp G 2)` when each `G i` is an inner product space. The inner product is `lp.inner_eq_tsum : ⟪f, g⟫_𝕜 = ∑' i, ⟪f i, g i⟫_𝕜`, and `lp.summable_inner` and `lp.hasSum_inner` give the convergence. Completeness is `lp.completeSpace` of Chapter 1.

<?decl lp.instInnerProductSpace?>
:::

**Definition (Hilbert basis).** A *Hilbert basis* of a Hilbert space $E$ is an orthonormal family $(e_i)_{i \in \iota}$ whose span is dense in $E$.

::: mathlib
`HilbertBasis` · `Mathlib.Analysis.InnerProductSpace.l2Space`

`HilbertBasis ι 𝕜 E` is a structure with one field `repr : E ≃ₗᵢ[𝕜] ℓ²(ι, 𝕜)`. As for `OrthonormalBasis` in Section 2, a basis is the isometry to coordinates. The vector `b i` is `b.repr.symm (lp.single 2 i 1)`, and `HilbertBasis.repr_self` states `b.repr (b i) = lp.single 2 i 1`. The definition of the text is recovered by `HilbertBasis.orthonormal` and `HilbertBasis.dense_span`. In the other direction, `HilbertBasis.mk` builds a basis from an orthonormal family with dense span, and `HilbertBasis.mkOfOrthogonalEqBot` from an orthonormal family whose span has orthogonal complement `⊥`.

<?decl HilbertBasis?>
:::

### Theorems and proofs

**Theorem ($\ell^2(\iota)$ is a Hilbert space).** The formula for $\langle c, d \rangle$ converges absolutely and defines an inner product on $\ell^2(\iota)$ whose norm is the $\ell^2$ norm. With it, $\ell^2(\iota)$ is a Hilbert space.

*Proof.* For each $i$, $|\overline{c_i}d_i| \le \tfrac12(|c_i|^2 + |d_i|^2)$, so the sum converges absolutely. The axioms of an inner product hold for each finite partial sum and pass to the limit. Also $\langle c, c \rangle = \sum_i |c_i|^2 = \|c\|_2^2$. Completeness for this norm is the completeness of $\ell^p$ with $p = 2$, proved in Chapter 1, Section 3. $\square$

**Lemma (convergence of orthogonal series).** Let $(e_i)_{i \in \iota}$ be orthonormal in a Hilbert space $E$ and $c \in \ell^2(\iota)$. Then $\sum_i c_i e_i$ converges unconditionally, and $\|\sum_i c_i e_i\|^2 = \sum_i |c_i|^2$. For $x \in E$, $(\langle e_i, x \rangle)_i \in \ell^2(\iota)$.

*Proof.* For a finite set $F$, Pythagoras gives $\|\sum_{i \in F} c_i e_i\|^2 = \sum_{i \in F} |c_i|^2$. Let $\varepsilon > 0$. Since $\sum_i |c_i|^2$ converges, there is a finite $F_0$ with $\sum_{i \in G} |c_i|^2 < \varepsilon^2$ for each finite $G$ disjoint from $F_0$. For finite $F, F' \supseteq F_0$, the difference of the partial sums is a sum over $G = F \triangle F'$, with signs, and $G \cap F_0 = \emptyset$, so its norm is less than $\varepsilon$. The net of partial sums is Cauchy, and it converges since $E$ is complete. The norm formula passes to the limit by continuity of the norm. The last statement is Bessel's inequality of Section 2. $\square$

**Theorem (characterization of a Hilbert basis).** Let $(e_i)_{i \in \iota}$ be orthonormal in a Hilbert space $E$. The following are equivalent:

1. the span of $(e_i)$ is dense in $E$;
2. the only $z \in E$ with $\langle e_i, z \rangle = 0$ for each $i$ is $z = 0$;
3. $x = \sum_i \langle e_i, x \rangle e_i$ for each $x \in E$;
4. $\|x\|^2 = \sum_i |\langle e_i, x \rangle|^2$ for each $x \in E$, the identity of Parseval.

*Proof.* (1) implies (2): if $z$ is orthogonal to each $e_i$, it is orthogonal to their span, and by continuity of $y \mapsto \langle y, z \rangle$ to its closure $E$. So $\langle z, z \rangle = 0$. (2) implies (3): by the lemma, $y = \sum_i \langle e_i, x \rangle e_i$ converges. For each $j$, continuity of $\langle e_j, \cdot \rangle$ gives $\langle e_j, y \rangle = \sum_i \langle e_i, x \rangle\langle e_j, e_i \rangle = \langle e_j, x \rangle$. So $x - y$ is orthogonal to each $e_j$, and $x = y$ by (2). (3) implies (4) by the norm formula of the lemma. (4) implies (1): for finite $F$, the vector $x - \sum_{i \in F}\langle e_i, x \rangle e_i$ is orthogonal to each $e_i$ with $i \in F$, as in the proof of Bessel's inequality, so
$$\Big\|x - \sum_{i \in F}\langle e_i, x \rangle e_i\Big\|^2 = \|x\|^2 - \sum_{i \in F}|\langle e_i, x \rangle|^2,$$
which tends to $0$ along the finite sets $F$ by (4). So $x$ is a limit of vectors of the span. $\square$

::: mathlib
`HilbertBasis.hasSum_repr` · `Mathlib.Analysis.InnerProductSpace.l2Space`

`b.hasSum_repr x : HasSum (fun i ↦ b.repr x i • b i) x`, where `b.repr x i = ⟪b i, x⟫_𝕜` by `HilbertBasis.repr_apply_apply`. This is condition (3). Parseval is the statement that `b.repr` is an isometry, part of the type `E ≃ₗᵢ[𝕜] ℓ²(ι, 𝕜)`, and its polarized form is `HilbertBasis.tsum_inner_mul_inner : ∑' i, ⟪x, b i⟫_𝕜 * ⟪b i, y⟫_𝕜 = ⟪x, y⟫_𝕜`. The converse series is `HilbertBasis.hasSum_repr_symm`: for `f : ℓ²(ι, 𝕜)` the series `∑ f i • b i` converges to `b.repr.symm f`.

<?decl HilbertBasis.hasSum_repr?>
:::

**Theorem (existence of Hilbert bases).** Each orthonormal family in a Hilbert space $E$ extends to a Hilbert basis. In particular $E$ has a Hilbert basis.

*Proof.* Let $s$ be an orthonormal subset of $E$. Order the orthonormal subsets of $E$ that contain $s$ by inclusion. The union of a chain is orthonormal, because two of its vectors lie in one member of the chain. By Zorn's lemma, from Volume 4, there is a maximal orthonormal set $w \supseteq s$. Condition (2) of the characterization holds for $w$: if $z \ne 0$ is orthogonal to each vector of $w$, then $w \cup \{z/\|z\|\}$ is orthonormal and larger than $w$. So $w$ is a Hilbert basis. For the last statement apply this to $s = \emptyset$. $\square$

::: mathlib
`exists_hilbertBasis` · `Mathlib.Analysis.InnerProductSpace.l2Space`

`exists_hilbertBasis 𝕜 E : ∃ (w : Set E) (b : HilbertBasis w 𝕜 E), ⇑b = ((↑) : w → E)` for a Hilbert space `E`. The basis is indexed by a subset of `E`, and the vectors of the basis are the elements of the subset. The extension form is `Orthonormal.exists_hilbertBasis_extension`. The proof uses `exists_maximal_orthonormal` from `Mathlib.Analysis.InnerProductSpace.Orthonormal`, which is the Zorn step, and `maximal_orthonormal_iff_orthogonalComplement_eq_bot`, which goes through the orthogonal projection of Chapter 7 in place of the direct argument of the text.

<?decl exists_hilbertBasis?>
:::

**Corollary (classification).** Let $(e_i)_{i \in \iota}$ be a Hilbert basis of a Hilbert space $E$. The map $U(x) = (\langle e_i, x \rangle)_{i \in \iota}$ is a linear isometry of $E$ onto $\ell^2(\iota)$, and it preserves inner products.

*Proof.* $U$ is linear and takes values in $\ell^2(\iota)$ by the lemma, and it is an isometry by Parseval. For $c \in \ell^2(\iota)$, the lemma gives $x = \sum_i c_i e_i$, and continuity of each $\langle e_j, \cdot \rangle$ gives $\langle e_j, x \rangle = c_j$, so $U(x) = c$. An isometry between inner product spaces preserves inner products by the polarization identity of Section 1. $\square$

The space $\ell^2(\iota)$ determines the cardinal of $\iota$ when $\iota$ is infinite, since it is the smallest cardinal of a dense subset of the space. So two Hilbert spaces are isometric if and only if their Hilbert bases have the same cardinal. A Hilbert space is separable if and only if it has a countable Hilbert basis, and then it is isometric to $\mathbb{K}^n$ or to $\ell^2 = \ell^2(\mathbb{N})$.

### Examples

**Example (the standard basis of $\ell^2$).** In $\ell^2(\iota)$ the functions $\delta_i$, with $\delta_i(j) = 1$ for $j = i$ and $0$ otherwise, are orthonormal. Their span is the set of finitely supported functions, which is dense: for $c \in \ell^2(\iota)$ and finite $F$, $\|c - c\,\mathbf{1}_F\|_2^2 = \sum_{i \notin F}|c_i|^2$, which tends to $0$. The expansion is $c = \sum_i c_i\delta_i$. In Mathlib $\delta_i$ is `lp.single 2 i 1`.

**Example (the trigonometric basis).** The functions $e_n(t) = e^{int}$, $n \in \mathbb{Z}$, form a Hilbert basis of $L^2[0, 2\pi]$ with the inner product $\frac{1}{2\pi}\int_0^{2\pi}\bar{f}g$. The density of their span is a theorem of Fourier analysis, which this volume does not prove. Parseval then reads $\frac{1}{2\pi}\int_0^{2\pi}|f|^2 = \sum_{n \in \mathbb{Z}}|\hat{f}(n)|^2$. For $f(t) = t$ on $[0, 2\pi)$ it gives $\sum_{n \ge 1} 1/n^2 = \pi^2/6$. Mathlib has this basis as `AddCircle.fourierBasis` in `Mathlib.Analysis.Fourier.AddCircle`, on the additive circle.

**Counterexample (a maximal orthonormal family without dense span).** Let $E = c_{00}$, the finitely supported sequences with the inner product of $\ell^2$, an inner product space that is not complete. Let $a = (1/n)_{n \ge 1} \in \ell^2$ and $M = \{x \in c_{00} : \langle a, x \rangle = 0\}$. Then $M$ is a closed subspace of $c_{00}$ different from $c_{00}$. A vector $z \in c_{00}$ orthogonal to $M$ is a multiple of $a$, because $M$ is the kernel of $\langle a, \cdot \rangle$ in $c_{00}$, and no nonzero multiple of $a$ is in $c_{00}$. So $M^\perp = \{0\}$ in $c_{00}$. Gram-Schmidt applied to a countable spanning set of $M$ gives an orthonormal family $(u_k)$ with span $M$. It is maximal, since a unit vector orthogonal to each $u_k$ is in $M^\perp$. Its span is not dense, since $M$ is closed and different from $c_{00}$. So the characterization needs completeness: (2) does not imply (1) in $c_{00}$.

### The library around it

The classification has a more general form in Mathlib. An orthogonal family of subspaces, `OrthogonalFamily 𝕜 G V`, gives `OrthogonalFamily.linearIsometry : lp G 2 →ₗᵢ[𝕜] E`, the map $(c_i) \mapsto \sum_i V_i(c_i)$ on the Hilbert sum. A Hilbert basis is the case where each $G_i$ is $\mathbb{K}$. The predicate `IsHilbertSum` records when the map is onto.

Common errors:

- `ℓ²(ι, 𝕜)` is notation of the namespace `lp` for `lp (fun _ : ι ↦ 𝕜) 2`. An element is a function with a proof of membership, and the coercion `⇑f` gives the function.
- A `HilbertBasis` is not a `Module.Basis`. In an infinite dimensional Hilbert space a Hilbert basis is never an algebraic basis, since its span is a proper dense subspace.
- `∑'` of a family that is not summable is `0`. State convergence with `HasSum` or `Summable`, as `hasSum_repr` does.

### Exercises

1. (A) Show that $(\delta_{2n})_{n \in \mathbb{N}}$ is orthonormal in $\ell^2$ and not a Hilbert basis. Find a vector orthogonal to it.
2. (A) Let $(e_i)$ be a Hilbert basis and $x, y \in E$. Show $\langle x, y \rangle = \sum_i \overline{\langle e_i, x \rangle}\langle e_i, y \rangle$.
3. (A) Show that $c_{00}$ with the $\ell^2$ inner product is not complete.
4. (B) Show that in an infinite dimensional Hilbert space each Hilbert basis is infinite and its span is not all of $E$.
5. (B) Let $(e_n)$ be an orthonormal sequence in a Hilbert space. Show that $e_n$ does not converge and that $\langle e_n, x \rangle \to 0$ for each $x$.
6. (B) Show that a Hilbert space is separable if and only if it has a countable Hilbert basis.
7. (C) Show that an infinite dimensional Hilbert space has no countable algebraic basis. Hint: Volume 13, Chapter 3, the theorem of Baire.

### Notes and history

David Hilbert worked with the space of square summable sequences in his work on integral equations in the first decade of the twentieth century, and Erhard Schmidt studied its geometry in 1908. Frigyes Riesz and Ernst Fischer proved in 1907 that the space $L^2$ is complete, which gives the isometry of $L^2[0, 2\pi]$ with $\ell^2(\mathbb{Z})$. The abstract definition of a Hilbert space is due to John von Neumann. The file `Mathlib.Analysis.InnerProductSpace.l2Space` has the author Heather Macbeth.

### Reference

<?reference?>
