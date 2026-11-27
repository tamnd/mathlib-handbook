---
title: The snake lemma and exact sequences
kind: theory
modules:
  - Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
  - Mathlib.Algebra.Homology.ExactSequence
  - Mathlib.Algebra.Homology.ExactSequenceFour
  - Mathlib.Algebra.FiveLemma
explains:
  E3: [CategoryTheory.ShortComplex.SnakeInput, CategoryTheory.ShortComplex.SnakeInput.δ, CategoryTheory.ShortComplex.SnakeInput.δ_eq, CategoryTheory.ShortComplex.SnakeInput.snake_lemma, CategoryTheory.ComposableArrows.Exact, CategoryTheory.ComposableArrows.Exact.cokerIsoKer, LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective]
  E2: [CategoryTheory.ShortComplex.SnakeInput.L₀_exact, CategoryTheory.ShortComplex.SnakeInput.L₃_exact, CategoryTheory.ShortComplex.SnakeInput.L₁'_exact, CategoryTheory.ShortComplex.SnakeInput.L₂'_exact, CategoryTheory.ShortComplex.SnakeInput.mono_L₀_f, CategoryTheory.ShortComplex.SnakeInput.epi_L₃_g, CategoryTheory.ShortComplex.SnakeInput.mono_δ, CategoryTheory.ShortComplex.SnakeInput.epi_δ, CategoryTheory.ShortComplex.SnakeInput.op, CategoryTheory.ShortComplex.SnakeInput.composableArrows, CategoryTheory.ComposableArrows.IsComplex, CategoryTheory.ComposableArrows.exact_iff_δ₀, CategoryTheory.ComposableArrows.exact_iff_δlast, CategoryTheory.ComposableArrows.sc, CategoryTheory.ShortComplex.toComposableArrows, CategoryTheory.ShortComplex.Exact.exact_toComposableArrows, CategoryTheory.ComposableArrows.IsComplex.cokerToKer, LinearMap.surjective_of_surjective_of_surjective_of_injective, LinearMap.injective_of_surjective_of_injective_of_injective, AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective]
  E1: auto
families: []
requires: [V07, V24.C04, V24.C08, V25.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The snake lemma and exact sequences

### Overview

The snake lemma turns a morphism between two exact rows into an exact sequence of six terms, built from the kernels and the cokernels of the vertical maps. The middle map of that sequence, the *connecting morphism* $\delta$, goes from a kernel back to a cokernel. Chapter 2 applies it to a short exact sequence of complexes.

Volume 25, Chapter 2, did the snake lemma for $\mathbb{Z}$-modules with elements. This section proves it in each abelian category with the refinements of that chapter. It also gives exact sequences of any length, in the form that Mathlib uses, the isomorphism $\operatorname{coker} \cong \ker$ inside a four-term exact sequence, and the four and five lemmas for modules in the form of `Mathlib.Algebra.FiveLemma`.

Refinements are used in this form. A morphism $p : X \to Y$ is an epimorphism if and only if for each $y : T \to Y$ there are an epimorphism $\pi : T' \to T$ and $x : T' \to X$ with $p \circ x = y \circ \pi$. A short complex $X_1 \xrightarrow{f} X_2 \xrightarrow{g} X_3$ is exact if and only if for each $y : T \to X_2$ with $g \circ y = 0$ there are an epimorphism $\pi : T' \to T$ and $x : T' \to X_1$ with $f \circ x = y \circ \pi$. Both statements are proved in Volume 25, Chapter 2. The category $C$ is abelian throughout.

### Definitions

**Definition (Exact sequence).** A sequence of composable morphisms $X_0 \xrightarrow{f_0} X_1 \xrightarrow{f_1} \cdots \xrightarrow{f_{n-1}} X_n$ is a *complex* if $f_{k+1} \circ f_k = 0$ for each $k$. It is *exact* if it is a complex and each short complex $X_k \to X_{k+1} \to X_{k+2}$ is exact.

**Definition (Snake input).** A *snake input* consists of four short complexes $L_0, L_1, L_2, L_3$ and morphisms of short complexes $v_{01} : L_0 \to L_1$, $v_{12} : L_1 \to L_2$, $v_{23} : L_2 \to L_3$ such that:

1. $v_{12} \circ v_{01} = 0$ and $v_{23} \circ v_{12} = 0$;
2. in each of the three columns, $v_{01}$ is a kernel of $v_{12}$ and $v_{23}$ is a cokernel of $v_{12}$;
3. $L_1$ is exact and its second map is an epimorphism;
4. $L_2$ is exact and its first map is a monomorphism.

Write $L_1 = (A \xrightarrow{f} B \xrightarrow{g} C)$, $L_2 = (A' \xrightarrow{f'} B' \xrightarrow{g'} C')$ and $a, b, c$ for the three components of $v_{12}$. Then $L_0$ is the row of kernels $\ker a \to \ker b \to \ker c$, and $L_3$ is the row of cokernels $\operatorname{coker} a \to \operatorname{coker} b \to \operatorname{coker} c$. The maps in these rows are induced by $f, g$ and by $f', g'$.

### Theorems and proofs

**Theorem (Connecting morphism).** For a snake input there is a unique morphism $\delta : \ker c \to \operatorname{coker} a$ with the following property. Let $x_3 : T \to \ker c$, $x_2 : T \to B$ and $x_1 : T \to A'$ satisfy
$$g \circ x_2 = \iota_c \circ x_3, \qquad f' \circ x_1 = b \circ x_2,$$
where $\iota_c : \ker c \to C$ is the inclusion. Then $\delta \circ x_3 = \pi_a \circ x_1$, where $\pi_a : A' \to \operatorname{coker} a$ is the projection.

For modules this is the recipe of Volume 25: lift $z$ to $y$, write $b(y) = f'(x')$, put $\delta z = [x']$.

*Proof.* Let $P$ be the pullback of $g : B \to C$ and $\iota_c : \ker c \to C$, with projections $q_2 : P \to B$ and $q_3 : P \to \ker c$. Then $g' \circ b \circ q_2 = c \circ g \circ q_2 = c \circ \iota_c \circ q_3 = 0$. By condition 4, $f'$ is a kernel of $g'$, so $b \circ q_2 = f' \circ \varphi$ for a unique $\varphi : P \to A'$.

In an abelian category the pullback of an epimorphism is an epimorphism, so $q_3$ is an epimorphism, and $q_3$ is a cokernel of its kernel. The kernel of $q_3$ is the kernel of $g$, through $q_2$: a map $t : T \to P$ with $q_3 \circ t = 0$ is the same as a map $s = q_2 \circ t$ with $g \circ s = 0$. By condition 3 the map $A \to \ker g$ induced by $f$ is an epimorphism. Let $j : A \to P$ be the map with $q_2 \circ j = f$ and $q_3 \circ j = 0$. Then a map out of $P$ that vanishes on $j$ vanishes on the kernel of $q_3$. Now
$$f' \circ \varphi \circ j = b \circ q_2 \circ j = b \circ f = f' \circ a,$$
so $\varphi \circ j = a$ because $f'$ is a monomorphism. Hence $\pi_a \circ \varphi \circ j = \pi_a \circ a = 0$. So $\pi_a \circ \varphi$ factors through the cokernel $q_3$ of its kernel: there is a unique $\delta$ with $\delta \circ q_3 = \pi_a \circ \varphi$.

For the property, let $x_1, x_2, x_3$ be as stated. The pair $(x_2, x_3)$ defines $t : T \to P$ with $q_2 \circ t = x_2$ and $q_3 \circ t = x_3$. Then $f' \circ \varphi \circ t = b \circ x_2 = f' \circ x_1$, so $\varphi \circ t = x_1$. Thus $\delta \circ x_3 = \delta \circ q_3 \circ t = \pi_a \circ \varphi \circ t = \pi_a \circ x_1$. Uniqueness: apply the property to $T = P$, $x_3 = q_3$, $x_2 = q_2$, $x_1 = \varphi$. It forces $\delta \circ q_3 = \pi_a \circ \varphi$, and $q_3$ is an epimorphism. $\square$

**Theorem (Snake lemma).** For a snake input the sequence
$$\ker a \to \ker b \to \ker c \xrightarrow{\delta} \operatorname{coker} a \to \operatorname{coker} b \to \operatorname{coker} c$$
is exact. If also $f$ is a monomorphism, then $\ker a \to \ker b$ is a monomorphism. If $g'$ is an epimorphism, then $\operatorname{coker} b \to \operatorname{coker} c$ is an epimorphism.

*Proof.* The opposite of a snake input is a snake input in $C^{\mathrm{op}}$, with the rows $L_1$, $L_2$ exchanged and kernels and cokernels exchanged. By the uniqueness of $\delta$, its connecting morphism is $\delta^{\mathrm{op}}$, and its six-term sequence is ours read backwards. So exactness at $\operatorname{coker} b$ and at $\operatorname{coker} a$ are dual to exactness at $\ker b$ and at $\ker c$, and only the last two need a proof.

*Exactness at $\ker b$.* Let $x : T \to \ker b$ map to zero in $\ker c$. Put $y = \iota_b \circ x : T \to B$. Then $g \circ y = \iota_c \circ 0 = 0$. By exactness of $L_1$ and the refinement criterion, there are an epimorphism $\pi : T' \to T$ and $u : T' \to A$ with $f \circ u = y \circ \pi$. Then $f' \circ a \circ u = b \circ f \circ u = b \circ \iota_b \circ x \circ \pi = 0$. Since $f'$ is a monomorphism, $a \circ u = 0$, so $u = \iota_a \circ w$ for some $w : T' \to \ker a$. The image of $w$ in $\ker b$ satisfies $\iota_b \circ (\text{image of } w) = f \circ u = \iota_b \circ x \circ \pi$, and $\iota_b$ is a monomorphism. So $x \circ \pi$ lifts to $\ker a$, which is exactness by the criterion.

*The composite at $\ker c$ is zero.* Let $x : T \to \ker b$ and $x_3$ its image in $\ker c$. Take $x_2 = \iota_b \circ x$ and $x_1 = 0$. Then $g \circ x_2 = \iota_c \circ x_3$, and $f' \circ 0 = 0 = b \circ x_2$. The theorem on $\delta$ gives $\delta \circ x_3 = 0$. With $T = \ker b$ and $x = 1$, this says that $\delta$ kills the map $\ker b \to \ker c$.

*Exactness at $\ker c$.* Let $x_3 : T \to \ker c$ with $\delta \circ x_3 = 0$. Since $g$ is an epimorphism, there are an epimorphism $\pi_1 : T_1 \to T$ and $x_2 : T_1 \to B$ with $g \circ x_2 = \iota_c \circ x_3 \circ \pi_1$. Then $g' \circ b \circ x_2 = c \circ \iota_c \circ x_3 \circ \pi_1 = 0$, so $b \circ x_2 = f' \circ x_1$ for some $x_1 : T_1 \to A'$. By the theorem on $\delta$, $\pi_a \circ x_1 = \delta \circ x_3 \circ \pi_1 = 0$. The cokernel sequence $A \xrightarrow{a} A' \to \operatorname{coker} a$ is exact, so there are an epimorphism $\pi_2 : T_2 \to T_1$ and $x_0 : T_2 \to A$ with $a \circ x_0 = x_1 \circ \pi_2$. Put $y = x_2 \circ \pi_2 - f \circ x_0 : T_2 \to B$. Then
$$b \circ y = f' \circ x_1 \circ \pi_2 - f' \circ a \circ x_0 = 0,$$
so $y = \iota_b \circ w$ for some $w : T_2 \to \ker b$. The image of $w$ in $\ker c$ satisfies $\iota_c \circ (\text{image of } w) = g \circ y = g \circ x_2 \circ \pi_2 = \iota_c \circ x_3 \circ \pi_1 \circ \pi_2$, because $g \circ f = 0$. So $x_3 \circ (\pi_1 \circ \pi_2)$ lifts to $\ker b$, and $\pi_1 \circ \pi_2$ is an epimorphism.

*The two extra claims.* If $f$ is a monomorphism, then $\ker a \to \ker b$ is a monomorphism, since $\iota_b$ composed with it is $f \circ \iota_a$, a composite of monomorphisms. The claim on $\operatorname{coker} b \to \operatorname{coker} c$ is dual. $\square$

**Theorem (Four-term exact sequences).** Let $X_0 \xrightarrow{f_0} X_1 \xrightarrow{f_1} X_2 \xrightarrow{f_2} X_3$ be exact. The map $f_1$ induces an isomorphism $\operatorname{coker} f_0 \cong \ker f_2$.

*Proof.* Let $p : X_1 \to \operatorname{coker} f_0$ be the projection. Since $f_1 \circ f_0 = 0$, there is $u : \operatorname{coker} f_0 \to X_2$ with $u \circ p = f_1$. Since $f_2 \circ u \circ p = f_2 \circ f_1 = 0$ and $p$ is an epimorphism, $f_2 \circ u = 0$, so $u$ factors as $\iota \circ v$ with $\iota : \ker f_2 \to X_2$ and $v : \operatorname{coker} f_0 \to \ker f_2$. The map $v \circ p : X_1 \to \ker f_2$ is the map induced by $f_1$, which is an epimorphism by exactness at $X_2$. So $v$ is an epimorphism. For the monomorphism, let $z : T \to \operatorname{coker} f_0$ with $v \circ z = 0$. Refine: $z \circ \pi = p \circ x$ for an epimorphism $\pi$ and some $x : T' \to X_1$. Then $f_1 \circ x = u \circ p \circ x = \iota \circ v \circ z \circ \pi = 0$. By exactness at $X_1$, after a second refinement $\pi'$, $x \circ \pi' = f_0 \circ w$. Then $z \circ \pi \circ \pi' = p \circ f_0 \circ w = 0$, so $z = 0$ because $\pi \circ \pi'$ is an epimorphism. In an abelian category a morphism that is a monomorphism and an epimorphism is an isomorphism. $\square$

**Theorem (Four and five lemmas for modules).** Consider a commutative diagram of $R$-modules with rows $M_1 \xrightarrow{f_1} M_2 \xrightarrow{f_2} M_3 \xrightarrow{f_3} M_4$ and $N_1 \xrightarrow{g_1} N_2 \xrightarrow{g_2} N_3 \xrightarrow{g_3} N_4$ and vertical maps $i_1, \ldots, i_4$.

1. If the pairs $(f_2, f_3)$, $(g_1, g_2)$, $(g_2, g_3)$ are exact, $i_1$ and $i_3$ are surjective and $i_4$ is injective, then $i_2$ is surjective.
2. If the pairs $(f_1, f_2)$, $(f_2, f_3)$, $(g_1, g_2)$ are exact, $i_1$ is surjective and $i_2$, $i_4$ are injective, then $i_3$ is injective.
3. For rows of five modules, exact at the three inner places, with $i_1$ surjective, $i_2$ and $i_4$ bijective and $i_5$ injective, $i_3$ is bijective.

*Proof.* Part 1. Let $n_2 \in N_2$. Choose $m_3$ with $i_3(m_3) = g_2(n_2)$. Then $i_4(f_3(m_3)) = g_3(g_2(n_2)) = 0$, so $f_3(m_3) = 0$ and $m_3 = f_2(m_2)$ for some $m_2$. Now $g_2(n_2 - i_2(m_2)) = g_2(n_2) - i_3(m_3) = 0$, so $n_2 - i_2(m_2) = g_1(n_1)$, and $n_1 = i_1(m_1)$. Hence $n_2 = i_2(m_2 + f_1(m_1))$.

Part 2. Let $i_3(m_3) = 0$. Then $i_4(f_3(m_3)) = g_3(i_3(m_3)) = 0$, so $f_3(m_3) = 0$ and $m_3 = f_2(m_2)$. Then $g_2(i_2(m_2)) = i_3(m_3) = 0$, so $i_2(m_2) = g_1(n_1) = g_1(i_1(m_1)) = i_2(f_1(m_1))$. Since $i_2$ is injective, $m_2 = f_1(m_1)$, and $m_3 = f_2(f_1(m_1)) = 0$.

Part 3. Part 2 applied to the first four columns gives that $i_3$ is injective, and part 1 applied to the last four columns gives that $i_3$ is surjective. $\square$

### Examples

**Example (The snake for multiplication by $n$).** Take both rows equal to $0 \to \mathbb{Z} \xrightarrow{m} \mathbb{Z} \to \mathbb{Z}/m \to 0$ and all three vertical maps equal to multiplication by $n$. Volume 25 did the case $m = 4$, $n = 6$. Take now $m = 6$ and $n = 4$, so $d = \gcd(6, 4) = 2$. The kernels are $\ker a = \ker b = 0$ and $\ker c = \{x \in \mathbb{Z}/6 : 4x = 0\} = \{0, 3\}$. The cokernels are $\mathbb{Z}/4$, $\mathbb{Z}/4$ and $(\mathbb{Z}/6)/4(\mathbb{Z}/6) = (\mathbb{Z}/6)/\{0, 2, 4\} \cong \mathbb{Z}/2$. For $\delta(3)$: lift $3$ to $y = 3 \in \mathbb{Z}$, then $b(y) = 12 = 6 \cdot 2 = f'(2)$, so $\delta(3) = [2] \in \mathbb{Z}/4$. The snake sequence is
$$0 \to 0 \to \mathbb{Z}/2 \xrightarrow{\delta} \mathbb{Z}/4 \xrightarrow{6} \mathbb{Z}/4 \to \mathbb{Z}/2 \to 0.$$
Multiplication by $6$ on $\mathbb{Z}/4$ is multiplication by $2$. Its kernel is $\{0, 2\}$, the image of $\delta$. Its image is $\{0, 2\}$, and $\mathbb{Z}/4 \to \mathbb{Z}/2$ is the reduction, with kernel $\{0, 2\}$. Each place is exact.

**Example (Multiplication by 2 on a non split sequence).** Take both rows equal to $0 \to \mathbb{Z}/2 \xrightarrow{f} \mathbb{Z}/4 \xrightarrow{g} \mathbb{Z}/2 \to 0$, with $f(1) = 2$ and $g$ the reduction, and all vertical maps multiplication by $2$. Then $a = c = 0$, and the squares commute because $b \circ f = 4 = 0$ and $g' \circ b = 0$. All six kernels and cokernels are cyclic of order $2$: $\ker b = \{0, 2\}$ and $\operatorname{coker} b = \mathbb{Z}/4/\{0, 2\}$. The map $\ker a \to \ker b$ sends $1$ to $2$, an isomorphism, and $\ker b \to \ker c$ sends $2$ to $g(2) = 0$. For $\delta(1)$: lift $1$ to $y = 1$, then $b(y) = 2 = f'(1)$, so $\delta(1) = [1]$, an isomorphism. Then $\operatorname{coker} a \to \operatorname{coker} b$ sends $[1]$ to $[2] = 0$, and $\operatorname{coker} b \to \operatorname{coker} c$ is an isomorphism. The sequence alternates between isomorphisms and zero maps, and it is exact.

**Counterexample (The hypotheses on the rows).** Drop condition 3. Let $L_1$ be $0 \to 0 \to \mathbb{Z}$, so that $g : 0 \to \mathbb{Z}$ is not an epimorphism, and let $L_2$ be $0 \to 0 \to 0$. Both rows are exact as short complexes, and $a = b = c = 0$. The kernels are $0, 0, \mathbb{Z}$ and the cokernels are $0, 0, 0$. The six-term sequence $0 \to 0 \to \mathbb{Z} \to 0 \to 0 \to 0$ is not exact at $\mathbb{Z}$.

### The library around it

::: mathlib
`CategoryTheory.ComposableArrows.Exact` · `Mathlib.Algebra.Homology.ExactSequence`

A sequence $X_0 \to \cdots \to X_n$ is a functor `ComposableArrows C n` from $\{0, \ldots, n\}$ to `C`. `S.IsComplex` says that consecutive composites vanish, and `S.Exact` adds the exactness of each `S.sc hS k`, the short complex at place `k`. `ShortComplex.toComposableArrows` turns a short complex into a sequence, and `exact_iff_δ₀` and `exact_iff_δlast` cut off the first or the last arrow, for proofs by induction on the length.

<?decl CategoryTheory.ComposableArrows.Exact?>
:::

::: mathlib
`CategoryTheory.ShortComplex.SnakeInput` · `Mathlib.Algebra.Homology.ShortComplex.SnakeLemma`

The fields are `L₀`, `L₁`, `L₂`, `L₃`, the morphisms `v₀₁`, `v₁₂`, `v₂₃`, the vanishing `w₀₂` and `w₁₃`, the limit and colimit conditions `h₀` and `h₃`, and `L₁_exact`, `epi_L₁_g`, `L₂_exact`, `mono_L₂_f`. `SnakeInput.op` is the opposite input, used for the dual half of the proof.

<?decl CategoryTheory.ShortComplex.SnakeInput?>
:::

::: mathlib
`CategoryTheory.ShortComplex.SnakeInput.δ` · `Mathlib.Algebra.Homology.ShortComplex.SnakeLemma`

The source builds `δ : S.L₀.X₃ ⟶ S.L₃.X₁` with the pullback `P` of `L₁.g` along `v₀₁.τ₃`, as in the proof, and with a dual pushout `P'`. The characterization is `δ_eq`: from `x₂ ≫ S.L₁.g = x₃ ≫ S.v₀₁.τ₃` and `x₁ ≫ S.L₂.f = x₂ ≫ S.v₁₂.τ₂` it gives `x₃ ≫ S.δ = x₁ ≫ S.v₂₃.τ₁`.

<?decl CategoryTheory.ShortComplex.SnakeInput.δ_eq?>
:::

::: mathlib
`CategoryTheory.ShortComplex.SnakeInput.snake_lemma` · `Mathlib.Algebra.Homology.ShortComplex.SnakeLemma`

The statement is `S.composableArrows.Exact`, where `S.composableArrows` is the sequence of six objects. The four parts are also available: `L₀_exact`, `L₁'_exact` (at $\ker c$), `L₂'_exact` (at $\operatorname{coker} a$) and `L₃_exact`. The instances `mono_L₀_f` and `epi_L₃_g` are the two extra claims. `mono_δ` and `epi_δ` give conditions for $\delta$ to be a monomorphism or an epimorphism.

<?decl CategoryTheory.ShortComplex.SnakeInput.snake_lemma?>
:::

::: mathlib
`CategoryTheory.ComposableArrows.Exact.cokerIsoKer` · `Mathlib.Algebra.Homology.ExactSequenceFour`

For an exact `S : ComposableArrows C (n + 3)` and `k ≤ n`, this is the isomorphism from the cokernel of the arrow at `k` to the kernel of the arrow at `k + 2`. `IsComplex.cokerToKer` is the map for a complex.

<?decl CategoryTheory.ComposableArrows.Exact.cokerIsoKer?>
:::

::: mathlib
`LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective` · `Mathlib.Algebra.FiveLemma`

The five lemma for modules over a commutative ring. The squares are `hc₁ : g₁.comp i₁ = i₂.comp f₁` and so on. The two four lemmas are `LinearMap.surjective_of_surjective_of_surjective_of_injective` and `LinearMap.injective_of_surjective_of_injective_of_injective`. The `AddMonoidHom` versions hold for abelian groups. The five lemma in an abelian category is `CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono` in Volume 25.

<?decl LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective?>
:::

Common errors of a learner:

- A snake input takes the kernel and cokernel rows `L₀` and `L₃` as data, with proofs `h₀` and `h₃`. The lemma does not build them.
- `δ` goes from `L₀.X₃` to `L₃.X₁`, the kernel of the third column to the cokernel of the first.

### Exercises

1. (A) Compute the snake sequence for both rows $0 \to \mathbb{Z} \xrightarrow{m} \mathbb{Z} \to \mathbb{Z}/m \to 0$ and vertical maps multiplication by $n$, for $m = 9$ and $n = 6$. Give $\delta$ explicitly.
2. (A) Show that the exact sequence $0 \to X_1 \to X_2 \to X_3 \to 0$ of length four is exact if and only if the short complex is short exact.
3. (B) Let $\varphi : M \to N$ be a map of $R$-modules and $r \in R$ central. Apply the snake lemma to multiplication by $r$ on $0 \to \ker \varphi \to M \to \operatorname{im} \varphi \to 0$ and write down the resulting exact sequence of the $r$-torsion submodules and the quotients by $r$.
4. (B) Prove the theorem on four-term exact sequences for modules with elements, and check it on $\mathbb{Z} \xrightarrow{4} \mathbb{Z} \xrightarrow{u} \mathbb{Z}/8 \xrightarrow{4} \mathbb{Z}/8$ with $u(x) = 2x$. *Hint:* first check that this sequence is exact.
5. (C) Show that $\delta$ is natural: a morphism of snake inputs gives a commutative square with the two connecting morphisms. *Hint:* use the characterization of $\delta$ and the uniqueness.
6. (C) Prove part 1 of the four lemma in an abelian category with refinements, step by step along the module proof.

### Notes and history

The snake lemma is in Cartan and Eilenberg (1956), where the connecting map of homology is built by the same recipe. The source says that the Mathlib proof uses refinements and duality, and that the result was proved in the Liquid Tensor Experiment too.

The Mathlib Author of `ShortComplex.SnakeLemma`, `ExactSequence` and `ExactSequenceFour` is Joël Riou. The Mathlib Author of `Algebra.FiveLemma` is Christian Merten.

### Reference

<?reference?>
