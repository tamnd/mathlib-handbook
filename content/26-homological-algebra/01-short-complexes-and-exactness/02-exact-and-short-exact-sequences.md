---
title: Exact and short exact sequences
kind: theory
modules:
  - Mathlib.Algebra.Homology.ShortComplex.Exact
  - Mathlib.Algebra.Homology.ShortComplex.ShortExact
  - Mathlib.Algebra.Homology.ShortComplex.Abelian
  - Mathlib.Algebra.Homology.ShortComplex.ModuleCat
  - Mathlib.Algebra.Homology.ShortComplex.Ab
  - Mathlib.Algebra.Exact.Basic
  - Mathlib.Algebra.Exact
  - Mathlib.Algebra.Exact.Sequence
explains:
  E3: [CategoryTheory.ShortComplex.Exact, CategoryTheory.ShortComplex.ShortExact, CategoryTheory.ShortComplex.Splitting, CategoryTheory.ShortComplex.HomologyData.ofAbelian, CategoryTheory.ShortComplex.moduleCat_exact_iff, Function.Exact, LinearMap.exact_iff, Function.Exact.split_tfae]
  E2: [CategoryTheory.ShortComplex.exact_iff_isZero_homology, CategoryTheory.ShortComplex.exact_of_iso, CategoryTheory.ShortComplex.Exact.op, CategoryTheory.ShortComplex.Exact.map, CategoryTheory.ShortComplex.exact_iff_epi_toCycles, CategoryTheory.ShortComplex.exact_iff_mono_fromOpcycles, CategoryTheory.ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero, CategoryTheory.ShortComplex.exact_iff_mono, CategoryTheory.ShortComplex.exact_iff_epi, CategoryTheory.ShortComplex.Exact.lift, CategoryTheory.ShortComplex.Exact.fIsKernel, CategoryTheory.ShortComplex.Exact.gIsCokernel, CategoryTheory.ShortComplex.Splitting.exact, CategoryTheory.ShortComplex.Splitting.isoBinaryBiproduct, CategoryTheory.ShortComplex.Splitting.ofExactOfRetraction, CategoryTheory.ShortComplex.Splitting.ofExactOfSection, CategoryTheory.ShortComplex.ShortExact.mk', CategoryTheory.ShortComplex.Splitting.shortExact, CategoryTheory.ShortComplex.isIso₂_of_shortExact_of_isIso₁₃, CategoryTheory.ShortComplex.ShortExact.splittingOfInjective, CategoryTheory.ShortComplex.ShortExact.splittingOfProjective, CategoryTheory.ShortComplex.LeftHomologyData.ofAbelian, CategoryTheory.ShortComplex.RightHomologyData.ofAbelian, CategoryTheory.categoryWithHomology_of_abelian, CategoryTheory.ShortComplex.homologyIsoImageICyclesCompPOpcycles, CategoryTheory.ShortComplex.moduleCat_exact_iff_range_eq_ker, CategoryTheory.ShortComplex.ShortExact.moduleCat_injective_f, CategoryTheory.ShortComplex.ShortExact.moduleCat_surjective_g, CategoryTheory.ShortComplex.moduleCatHomologyIso, CategoryTheory.ShortComplex.ab_exact_iff, CategoryTheory.ShortComplex.ab_exact_iff_function_exact, CategoryTheory.ShortComplex.abHomologyIso, LinearMap.exact_subtype_mkQ, LinearMap.exact_zero_iff_injective, AddMonoidHom.exact_iff]
  E1: auto
families: []
requires: [V07, V24.C08, V25.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Exact and short exact sequences

### Overview

A short complex is *exact* when its homology is zero. This is the categorical form of the condition $\ker g = \operatorname{im} f$ of a first course in algebra. This section proves that the abstract definition agrees with the concrete one in each abelian category and in the categories of modules and abelian groups, and it relates it to the predicate `Function.Exact` on maps of sets that the algebra part of Mathlib uses. It then treats *short exact* sequences $0 \to X_1 \to X_2 \to X_3 \to 0$ and their splittings.

The section uses Section 1 for short complexes and homology data. From Volume 25, Chapter 2, it uses the coimage-image isomorphism of an abelian category, the fact that each monomorphism is the kernel of its cokernel, and the five lemma. Section 1 left open that every short complex in an abelian category has homology. The first theorem below proves it.

### Definitions

**Definition (Exact short complex).** A short complex $S$ is *exact* if it has a homology data whose left homology object is a zero object. When $S$ has homology, this holds if and only if $H(S)$ is a zero object, because two left homology objects are isomorphic by Section 1.

**Definition (Exact pair of maps).** Let $f : M \to N$ and $g : N \to P$ be maps of sets, where $P$ has a point $0$. The pair is *exact* if for every $y \in N$,
$$g(y) = 0 \iff y \in f(M).$$
This is a predicate on functions. It asks nothing of the structure of $M$ and $N$, and it includes the claim $g \circ f = 0$.

**Definition (Short exact sequence).** A short complex $S$ is *short exact* if it is exact, $f$ is a monomorphism and $g$ is an epimorphism. It is often written $0 \to X_1 \to X_2 \to X_3 \to 0$.

**Definition (Splitting).** Let $C$ be preadditive. A *splitting* of a short complex $S$ is a pair of morphisms $r : X_2 \to X_1$ and $s : X_3 \to X_2$ with
$$r \circ f = 1_{X_1}, \qquad g \circ s = 1_{X_3}, \qquad f \circ r + s \circ g = 1_{X_2}.$$
A short complex with a splitting is *split*.

### Theorems and proofs

**Theorem (Homology in an abelian category).** Let $C$ be abelian and $S$ a short complex in $C$. Let $i : K \to X_2$ be a kernel of $g$, $p : X_2 \to Q$ a cokernel of $f$, and $p \circ i = m \circ e$ an epi-mono factorization through the image $I$. Then $(K, I, i, e)$ is a left homology data, $(Q, I, p, m)$ is a right homology data, and with the identity of $I$ they form a homology data. In particular every short complex in $C$ has homology, and
$$H(S) \cong \operatorname{im}(p \circ i : K \to Q).$$

*Proof.* Let $f' : X_1 \to K$ be the map with $i \circ f' = f$. First, $e \circ f' = 0$: indeed $m \circ e \circ f' = p \circ i \circ f' = p \circ f = 0$, and $m$ is a monomorphism.

Next, compute the kernel of $e$. Since $m$ is a monomorphism, $\ker e = \ker(p \circ i)$ as subobjects of $K$. A morphism $t : T \to K$ satisfies $p \circ i \circ t = 0$ if and only if $i \circ t$ factors through the kernel of $p$. In an abelian category the kernel of the cokernel of $f$ is the image $\operatorname{im} f \subseteq X_2$, because the monomorphism $\operatorname{im} f \to X_2$ is the kernel of its cokernel and $p$ is that cokernel. So $\ker(p \circ i)$ is the pullback $i^{-1}(\operatorname{im} f)$. Since $f = i \circ f'$ and $i$ is a monomorphism, $\operatorname{im} f$ is the image of the subobject $\operatorname{im} f' \subseteq K$ under $i$, and $i^{-1}(i(\operatorname{im} f')) = \operatorname{im} f'$. Thus $\ker e = \operatorname{im} f'$.

In an abelian category each epimorphism is the cokernel of its kernel. So $e$ is a cokernel of the monomorphism $\operatorname{im} f' \to K$. The map $f'$ is the composite of the epimorphism $X_1 \to \operatorname{im} f'$ with this monomorphism, and a morphism $a$ from $K$ kills $f'$ if and only if it kills $\operatorname{im} f' \to K$. So $e$ is also a cokernel of $f'$, and $(K, I, i, e)$ is a left homology data.

The dual argument in $C^{\mathrm{op}}$, which is again abelian, shows that $m$ is a kernel of the map $g' : Q \to X_3$ induced by $g$. So $(Q, I, p, m)$ is a right homology data. The condition of a homology data with the identity of $I$ reads $m \circ 1 \circ e = p \circ i$, which holds by the choice of the factorization. $\square$

**Corollary (Exactness in an abelian category).** Let $C$ be abelian. For a short complex $S$ the following are equivalent:

1. $S$ is exact;
2. $p \circ i = 0$, where $i$ is a kernel of $g$ and $p$ a cokernel of $f$;
3. the map $f' : X_1 \to \ker g$ is an epimorphism;
4. the map $g' : \operatorname{coker} f \to X_3$ is a monomorphism;
5. $\operatorname{im} f = \ker g$ as subobjects of $X_2$.

*Proof.* By the theorem, $H(S) \cong \operatorname{im}(p \circ i)$, and an image is zero if and only if the morphism is zero. This gives $1 \iff 2$. The left homology $\operatorname{coker} f'$ is zero if and only if $f'$ is an epimorphism: if $f'$ is an epimorphism, each $a$ with $a \circ f' = 0$ is zero, so $0$ is a cokernel; conversely, if the cokernel is zero and $a \circ f' = b \circ f'$, then $(a - b) \circ f' = 0$, so $a - b$ factors through $0$ and $a = b$. This gives $1 \iff 3$, and $1 \iff 4$ is dual. Finally $\operatorname{im} f' \to K$ is an isomorphism if and only if $f'$ is an epimorphism, and $i$ carries $\operatorname{im} f'$ onto $\operatorname{im} f$. This gives $3 \iff 5$. $\square$

**Corollary (Exactness of modules).** Let $R$ be a ring and $S$ a short complex of $R$-modules. Then $S$ is exact if and only if for each $x_2 \in X_2$ with $g(x_2) = 0$ there is $x_1 \in X_1$ with $f(x_1) = x_2$. Equivalently, $\ker g = \operatorname{im} f$, and equivalently the pair $(f, g)$ is exact in the sense of maps of sets.

*Proof.* The kernel of $g$ is the submodule $\ker g$ with its inclusion, and $f'$ is $f$ with its codomain restricted to $\ker g$. By condition 3 of the previous corollary, $S$ is exact if and only if $f'$ is surjective, which is the stated condition. Since $g \circ f = 0$ gives $\operatorname{im} f \subseteq \ker g$, the condition is $\ker g = \operatorname{im} f$. For each $y$, the equivalence $g(y) = 0 \iff y \in \operatorname{im} f$ is the same statement. $\square$

**Proposition (Special cases).** Let $C$ be abelian and $S$ a short complex.

1. If $f = 0$, then $S$ is exact if and only if $g$ is a monomorphism.
2. If $g = 0$, then $S$ is exact if and only if $f$ is an epimorphism.
3. If $S$ is exact and $f$ is a monomorphism, then $f$ is a kernel of $g$. If $S$ is exact and $g$ is an epimorphism, then $g$ is a cokernel of $f$.

*Proof.* If $f = 0$, then $f' = 0$, and $f'$ is an epimorphism if and only if $\ker g = 0$, which says that $g$ is a monomorphism. Part 2 is dual. For part 3, exactness gives $\operatorname{im} f = \ker g$. A monomorphism $f$ is isomorphic to the inclusion of its image. So $f$ is isomorphic over $X_2$ to the kernel of $g$, and is therefore a kernel of $g$. The second claim is dual. $\square$

**Theorem (Splitting lemma).** Let $C$ be preadditive and $S$ a short complex.

1. If $S$ has a splitting $(r, s)$, then $S$ is short exact, and $X_2$ is a biproduct of $X_1$ and $X_3$ with inclusions $f$, $s$ and projections $r$, $g$.
2. Let $C$ be abelian and $S$ short exact. If $f$ has a retraction $r$, then there is a unique $s$ such that $(r, s)$ is a splitting. If $g$ has a section $s$, then there is a unique $r$ such that $(r, s)$ is a splitting.

*Proof.* Part 1. From $r \circ f = 1$ the map $f$ is a monomorphism, and from $g \circ s = 1$ the map $g$ is an epimorphism. Compose $f \circ r + s \circ g = 1$ on the right with $s$: $f \circ r \circ s + s = s$, so $f \circ r \circ s = 0$, and $r \circ s = 0$ since $f$ is a monomorphism. The equations $r f = 1$, $g s = 1$, $r s = 0$, $g f = 0$ and $f r + s g = 1$ are the equations of a biproduct from Volume 24, Chapter 8. For exactness, let $t : T \to X_2$ with $g \circ t = 0$. Then $t = f \circ r \circ t + s \circ g \circ t = f \circ (r \circ t)$, so $t$ factors through $f$. Thus $f$ is a kernel of $g$, the map $f' : X_1 \to \ker g$ is an isomorphism, and $S$ is exact.

Part 2. Let $r \circ f = 1$. Put $u = 1 - f \circ r$. Then $u \circ f = f - f \circ r \circ f = 0$. In a short exact sequence $g$ is a cokernel of $f$ by the proposition. So $u = s \circ g$ for a unique $s : X_3 \to X_2$. Then $f \circ r + s \circ g = 1$. Also $g \circ s \circ g = g \circ u = g - g \circ f \circ r = g$, and $g \circ s = 1$ because $g$ is an epimorphism. So $(r, s)$ is a splitting. If $s_1$ also works, then $s_1 \circ g = 1 - f \circ r = s \circ g$, and $s_1 = s$. The second claim is dual. $\square$

**Corollary (Short five lemma).** Let $C$ be abelian and $\varphi : S \to S'$ a morphism of short exact sequences. If $\tau_1$ and $\tau_3$ are isomorphisms, then $\tau_2$ is an isomorphism.

*Proof.* Extend both rows by zero objects on the left and on the right, to $0 \to X_1 \to X_2 \to X_3 \to 0$. The rows are exact at each place by the definition of a short exact sequence. The five lemma of Volume 25, Chapter 2, applied with the identities of $0$ at the two ends, gives that $\tau_2$ is an isomorphism. $\square$

### Examples

**Example (Multiplication by $n$ on the integers).** For $n \ge 1$ the sequence $0 \to \mathbb{Z} \xrightarrow{n} \mathbb{Z} \to \mathbb{Z}/n \to 0$ is short exact: multiplication by $n$ is injective, reduction is surjective, and the kernel of reduction is $n\mathbb{Z}$, which is the image of $f$. It does not split for $n \ge 2$. A section $s : \mathbb{Z}/n \to \mathbb{Z}$ must send $1$ to an element $a$ with $na = 0$, so $a = 0$ and $g \circ s = 0 \ne 1$.

**Example (Two extensions of $\mathbb{Z}/2$ by $\mathbb{Z}/2$).** The sequence $0 \to \mathbb{Z}/2 \xrightarrow{2} \mathbb{Z}/4 \to \mathbb{Z}/2 \to 0$ is short exact. It does not split, because $\mathbb{Z}/4$ has an element of order $4$ and $\mathbb{Z}/2 \times \mathbb{Z}/2$ has none. The sequence $0 \to \mathbb{Z}/2 \to \mathbb{Z}/2 \times \mathbb{Z}/2 \to \mathbb{Z}/2 \to 0$ with the first inclusion and the second projection is split. By the short five lemma no morphism of short exact sequences with identities at the two ends connects these two sequences.

**Example (The Chinese remainder theorem).** The sequence $0 \to \mathbb{Z}/2 \xrightarrow{f} \mathbb{Z}/6 \xrightarrow{g} \mathbb{Z}/3 \to 0$ with $f(1) = 3$ and $g$ the reduction modulo $3$ is short exact. Reduction modulo $2$ is a retraction $r$ of $f$, since $r(f(1)) = 3 \bmod 2 = 1$. The proof of the splitting lemma gives $s$ by $s \circ g = 1 - f \circ r$. On $x = 1$: $f(r(1)) = 3$, so $s(g(1)) = 1 - 3 = -2 = 4$. Thus $s(1) = 4$, and $g(4) = 1$ in $\mathbb{Z}/3$, as required.

**Example (A polynomial ring).** Let $k$ be a field. The sequence of $k[x]$-modules $0 \to k[x] \xrightarrow{x} k[x] \to k \to 0$, with the evaluation at $0$ as the second map, is short exact. As a sequence of $k$-vector spaces it splits, by the inclusion of constants. As a sequence of $k[x]$-modules it does not split: a $k[x]$-linear section $s : k \to k[x]$ satisfies $x \cdot s(1) = s(x \cdot 1) = s(0) = 0$, so $s(1) = 0$.

**Counterexample (Exact is not short exact).** The complex $\mathbb{Z}/4 \xrightarrow{2} \mathbb{Z}/4 \xrightarrow{2} \mathbb{Z}/4$ is exact, since the kernel and the image of multiplication by $2$ are both $\{0, 2\}$. It is not short exact: $f$ is not injective and $g$ is not surjective. The complex $\mathbb{Z} \xrightarrow{4} \mathbb{Z} \to \mathbb{Z}/2$ satisfies $g \circ f = 0$ but is not exact. The kernel of reduction is $2\mathbb{Z}$, the image of $f$ is $4\mathbb{Z}$, and the homology is $2\mathbb{Z}/4\mathbb{Z} \cong \mathbb{Z}/2$.

### The library around it

::: mathlib
`CategoryTheory.ShortComplex.Exact` · `Mathlib.Algebra.Homology.ShortComplex.Exact`

The structure `S.Exact` has one field: there is `h : S.HomologyData` with `IsZero h.left.H`. It does not need `HasHomology`. Under `[S.HasHomology]`, `exact_iff_isZero_homology` gives the usual form. Other criteria are `exact_iff_epi_toCycles`, `exact_iff_mono_fromOpcycles` and `exact_iff_kernel_ι_comp_cokernel_π_zero`. `Exact.op` and `Exact.map` move exactness to the opposite category and through a functor that preserves the homology. For an exact `S` with `Mono S.f`, `Exact.fIsKernel` says that `f` is a kernel of `g`, and `Exact.lift` lifts a morphism killed by `g`.

<?decl CategoryTheory.ShortComplex.Exact?>
:::

::: mathlib
`CategoryTheory.ShortComplex.HomologyData.ofAbelian` · `Mathlib.Algebra.Homology.ShortComplex.Abelian`

In an abelian category, `LeftHomologyData.ofAbelian` takes as `H` the coimage of `kernel.ι S.g ≫ cokernel.π S.f`, and `RightHomologyData.ofAbelian` takes the image. The coimage-image isomorphism of Volume 25 joins them. The instance `categoryWithHomology_of_abelian` makes `S.homology` available without hypotheses, and `homologyIsoImageICyclesCompPOpcycles` is the isomorphism $H(S) \cong \operatorname{im}(p \circ i)$ of the theorem.

<?decl CategoryTheory.ShortComplex.HomologyData.ofAbelian?>
:::

::: mathlib
`CategoryTheory.ShortComplex.moduleCat_exact_iff` · `Mathlib.Algebra.Homology.ShortComplex.ModuleCat`

For `S : ShortComplex (ModuleCat R)`, exactness is `∀ x₂, S.g x₂ = 0 → ∃ x₁, S.f x₁ = x₂`. The variant `moduleCat_exact_iff_range_eq_ker` states `LinearMap.range S.f.hom = LinearMap.ker S.g.hom`. `ShortExact.moduleCat_injective_f` and `ShortExact.moduleCat_surjective_g` extract the injectivity and the surjectivity, and `moduleCatHomologyIso` identifies the homology with the quotient of the kernel by the range. The file `ShortComplex.Ab` gives the same results for abelian groups: `ab_exact_iff`, `ab_exact_iff_function_exact` and `abHomologyIso`.

<?decl CategoryTheory.ShortComplex.moduleCat_exact_iff?>
:::

::: mathlib
`Function.Exact` · `Mathlib.Algebra.Exact.Basic`

`Function.Exact f g` is `∀ y, g y = 0 ↔ y ∈ Set.range f`. It is stated for bare functions, so it applies to linear maps through their coercions and does not mention a category.

<?decl Function.Exact?>
:::

::: mathlib
`LinearMap.exact_iff` · `Mathlib.Algebra.Exact.Basic`

For linear maps, `Function.Exact f g ↔ ker g = range f`. The lemma `LinearMap.exact_subtype_mkQ` says that the inclusion of a submodule and the quotient map form an exact pair, and `LinearMap.exact_zero_iff_injective` turns an exact pair with $0$ in front into injectivity. `AddMonoidHom.exact_iff` is the version for additive maps.

<?decl LinearMap.exact_iff?>
:::

::: mathlib
`CategoryTheory.ShortComplex.ShortExact` · `Mathlib.Algebra.Homology.ShortComplex.ShortExact`

The fields are `exact`, `mono_f` and `epi_g`, the last two as instances. `ShortExact.mk'` builds one from the three facts. The short five lemma is `isIso₂_of_shortExact_of_isIso₁₃`, stated for a balanced preadditive category. In a short exact sequence with an injective object `S.X₁`, `ShortExact.splittingOfInjective` gives a splitting, and `ShortExact.splittingOfProjective` does the same for a projective `S.X₃`.

<?decl CategoryTheory.ShortComplex.ShortExact?>
:::

::: mathlib
`CategoryTheory.ShortComplex.Splitting` · `Mathlib.Algebra.Homology.ShortComplex.Exact`

The fields are `r`, `s`, `f_r : S.f ≫ r = 𝟙 _`, `s_g : s ≫ S.g = 𝟙 _` and `id : r ≫ S.f + S.g ≫ s = 𝟙 _`. Read in the order of the textbook, `id` is $f \circ r + s \circ g = 1$. `Splitting.exact`, `Splitting.shortExact` and `Splitting.isoBinaryBiproduct` are part 1 of the splitting lemma, and `Splitting.ofExactOfRetraction` and `Splitting.ofExactOfSection` are part 2.

<?decl CategoryTheory.ShortComplex.Splitting?>
:::

::: mathlib
`Function.Exact.split_tfae` · `Mathlib.Algebra.Exact.Basic`

This is the splitting lemma for modules. For linear maps with `Function.Exact f g`, `f` injective and `g` surjective, the list of three conditions is a `TFAE`: a section of `g`, a retraction of `f`, and a linear equivalence `N ≃ M × P` that matches `f` with `LinearMap.inl` and `g` with `LinearMap.snd`.

<?decl Function.Exact.split_tfae?>
:::

The module `Mathlib.Algebra.Exact` is deprecated, and it only imports `Mathlib.Algebra.Exact.Basic`. The module `Mathlib.Algebra.Exact.Sequence` proves that the alternating sum of the dimensions in an exact sequence $0 \to V_0 \to \cdots \to V_{n+1} \to 0$ of finite dimensional vector spaces is zero (`Module.sum_neg_one_pow_finrank_eq_zero_of_exact`), with the case of six spaces in `Module.sum_neg_one_pow_finrank_eq_zero_of_exact_six`.

Common errors of a learner:

- `S.Exact` says nothing about `f` and `g` themselves. Short exactness adds `Mono S.f` and `Epi S.g`.
- `Function.Exact f g` includes `g ∘ f = 0`, but a `ShortComplex` stores this in its field `zero`. To go from one to the other, use `ShortComplex.moduleCatMk` or the lemma `ShortExact.moduleCat_exact_iff_function_exact`.
- In `Splitting`, `r` goes from `X₂` to `X₁`, against the direction of `f`.

### Exercises

1. (A) Decide which of the following are exact: $\mathbb{Z}/6 \xrightarrow{2} \mathbb{Z}/6 \xrightarrow{3} \mathbb{Z}/6$, $\mathbb{Z}/8 \xrightarrow{4} \mathbb{Z}/8 \xrightarrow{2} \mathbb{Z}/8$, $\mathbb{Z} \xrightarrow{6} \mathbb{Z} \to \mathbb{Z}/3$.
2. (A) Show that $0 \to \mathbb{Z}/3 \to \mathbb{Z}/9 \to \mathbb{Z}/3 \to 0$, with $1 \mapsto 3$ and reduction, is short exact and does not split.
3. (A) Let $R$ be a ring and $I$ an ideal. Show that $0 \to I \to R \to R/I \to 0$ splits as a sequence of $R$-modules if and only if $I$ is generated by an idempotent.
4. (B) Show that in an abelian category, a short complex $0 \to A \xrightarrow{f} B$ (with $X_1 = 0$) is exact if and only if $f$ is a monomorphism.
5. (B) In the Chinese remainder example, find all retractions of $f : \mathbb{Z}/2 \to \mathbb{Z}/6$ and all sections of $g$. *Hint:* there is one of each, and they correspond under the splitting lemma.
6. (B) Prove part 2 of the splitting lemma for a section $s$ of $g$ directly, without duality.
7. (C) Show that a short exact sequence $0 \to A \to B \to \mathbb{Z}^n \to 0$ of abelian groups splits, and give a short exact sequence $0 \to \mathbb{Z} \to B \to \mathbb{Q} \to 0$ that does not split. *Hint:* $\mathbb{Z}^n$ is projective, and $\mathbb{Q}$ has no nonzero map to $\mathbb{Z}$.

### Notes and history

Exact sequences appear in the algebraic topology of the 1940s, and Eilenberg and Steenrod used them in the axioms for homology. Cartan and Eilenberg (1956) made exactness the central notion of homological algebra for modules, and Grothendieck (1957) defined it in abelian categories.

The Mathlib Author of `ShortComplex.Exact`, `ShortComplex.ShortExact`, `ShortComplex.Abelian`, `ShortComplex.ModuleCat` and `ShortComplex.Ab` is Joël Riou. The Mathlib Author of `Algebra.Exact.Basic` is Antoine Chambert-Loir.

### Reference

<?reference?>
