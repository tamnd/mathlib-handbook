---
title: Smooth, étale and unramified morphisms
kind: theory
modules:
  - Mathlib.AlgebraicGeometry.Morphisms.Etale
  - Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
  - Mathlib.AlgebraicGeometry.Morphisms.Smooth
  - Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
  - Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
explains:
  E3: [AlgebraicGeometry.FormallyUnramified, AlgebraicGeometry.FormallyUnramified.hom_ext, AlgebraicGeometry.FormallyUnramified.isOpenImmersion_diagonal, AlgebraicGeometry.Smooth, AlgebraicGeometry.SmoothOfRelativeDimension, AlgebraicGeometry.Etale, AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified, AlgebraicGeometry.WeaklyEtale, AlgebraicGeometry.etale_le_weaklyEtale]
  E2: [AlgebraicGeometry.FormallyUnramified.of_hom_ext, AlgebraicGeometry.Smooth.iff_forall_exists_isStandardSmooth, AlgebraicGeometry.Scheme.Hom.smoothLocus, AlgebraicGeometry.Scheme.Hom.isOpen_smoothLocus, AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_top_iff, AlgebraicGeometry.Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField, AlgebraicGeometry.Scheme.Hom.dense_smoothLocus_of_perfectField, AlgebraicGeometry.formallySmooth_stalkMap_iff, AlgebraicGeometry.Etale.of_formallyUnramified_of_flat, AlgebraicGeometry.Etale.iff_smoothOfRelativeDimension_zero, AlgebraicGeometry.Scheme.Etale, AlgebraicGeometry.Smooth.of_smooth_fiberToSpecResidueField, AlgebraicGeometry.WeaklyEtale.weaklyEtale_eq_flat_inf_diagonal_flat]
  E1: auto
families: []
requires: [V09.C04, V10.C08, V28.C03, V28.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Smooth, étale and unramified morphisms

### Overview

In differential geometry a submersion is a smooth map whose differential is surjective, and a local diffeomorphism is a submersion of relative dimension zero. Algebraic geometry has the same three notions. A smooth morphism is locally cut out by equations with a Jacobian of full rank. An étale morphism is smooth of relative dimension zero, the algebraic analogue of a local diffeomorphism. An unramified morphism has no infinitesimal directions in its fibers: its module of differentials vanishes. Chapter 6 builds the étale topology on étale morphisms.

Volume 10, Chapter 8 treats the ring theory: Kähler differentials, formally smooth and formally étale algebras, and standard smooth presentations. This section transfers it to schemes, proves the infinitesimal uniqueness of unramified morphisms and the open diagonal, and works out the examples $\mathbb{A}^n \to \operatorname{Spec} k$ and $x \mapsto x^2$.

### Definitions

As in Section 2, each property here holds for $f : X \to Y$ when it holds for every $f^\sharp_{U,V} : \mathcal{O}_Y(U) \to \mathcal{O}_X(V)$ with $U$, $V$ affine and $V \subseteq f^{-1}(U)$.

**Definition (Formally unramified).** An $R$-algebra $A$ is *formally unramified* when $\Omega_{A/R} = 0$. A morphism is *formally unramified* when every $f^\sharp_{U,V}$ is formally unramified. An *unramified* morphism is one that is formally unramified and locally of finite type.

The Stacks project asks finite type for unramified; some older sources ask finite presentation. Mathlib names only the formal property and lets the finiteness condition be a separate class.

**Definition (Smooth).** An $R$-algebra $A$ is *formally smooth* when for every $R$-algebra $C$ and ideal $I \subseteq C$ with $I^2 = 0$, every $R$-algebra map $A \to C/I$ lifts to $A \to C$. It is *smooth* when it is formally smooth and of finite presentation. A morphism is *smooth* when every $f^\sharp_{U,V}$ is smooth.

**Definition (Standard smooth).** A *submersive presentation* of an $R$-algebra $A$ is an isomorphism $A \cong R[x_1, \dots, x_n]/(g_1, \dots, g_c)$ with $c \leq n$ such that the determinant of the $c \times c$ matrix $(\partial g_i / \partial x_j)_{i, j \leq c}$ is a unit in $A$. An algebra with such a presentation is *standard smooth of relative dimension* $n - c$. A morphism is *smooth of relative dimension* $n$ when each $x \in X$ has affine neighbourhoods $V \ni x$ and $U \supseteq f(V)$ with $f^\sharp_{U,V}$ standard smooth of relative dimension $n$.

**Definition (Étale).** An $R$-algebra $A$ is *formally étale* when the lifts in the definition of formally smooth exist and are unique, and *étale* when it is formally étale and of finite presentation. A morphism is *étale* when every $f^\sharp_{U,V}$ is étale.

**Definition (Weakly étale).** A morphism $f$ is *weakly étale* when $f$ is flat and its diagonal $\Delta_f$ is flat.

**Definition (Smooth locus).** For $f$ locally of finite presentation, the *smooth locus* is the set of $x \in X$ whose stalk map $\mathcal{O}_{Y, f(x)} \to \mathcal{O}_{X, x}$ is formally smooth.

### Theorems and proofs

**Lemma (Infinitesimal uniqueness).** Let $R \to A$ be formally unramified, $C$ an $R$-algebra and $I \subseteq C$ an ideal with $I^2 = 0$. Two $R$-algebra maps $g_1, g_2 : A \to C$ that agree modulo $I$ are equal.

*Proof.* Let $D = g_1 - g_2 : A \to I$. It is $R$-linear and kills $R$. Make $I$ an $A$-module through $g_1$. Since $g_1(b) - g_2(b) \in I$ and $I^2 = 0$, the elements $g_1(b)$ and $g_2(b)$ act in the same way on $I$. For $a, b \in A$:
$$D(ab) = g_1(a) g_1(b) - g_2(a) g_2(b) = g_1(a)\big(g_1(b) - g_2(b)\big) + \big(g_1(a) - g_2(a)\big) g_2(b) = a \cdot D(b) + b \cdot D(a).$$
So $D$ is an $R$-derivation $A \to I$. It factors through $\Omega_{A/R} = 0$, so $D = 0$ and $g_1 = g_2$. $\square$

The scheme form in the index allows a closed immersion $i : Z' \to Z$ with nilpotent ideal: two morphisms $Z \to X$ over $Y$ that agree on $Z'$ are equal. A nilpotent ideal $J$ with $J^n = 0$ is a sequence of square-zero steps $C/J^{k+1} \to C/J^k$, so the lemma applies step by step.

**Lemma (Idempotent generators).** Let $J$ be a finitely generated ideal of a ring $B$ with $J = J^2$. Then $J = (e)$ for an idempotent $e$.

*Proof.* The module $J$ is finitely generated and $J \cdot J = J$. By the determinant form of Nakayama's lemma (Volume 9, Chapter 4), there is $r \in B$ with $r \equiv 1 \pmod J$ and $rJ = 0$. Put $e = 1 - r \in J$. For $y \in J$, $ey = y - ry = y$. So $J = eJ \subseteq (e) \subseteq J$, and $e^2 = e$ since $e \in J$. $\square$

**Theorem (Open diagonal).** Let $f$ be formally unramified and locally of finite type. Then $\Delta_f$ is an open immersion.

*Proof.* By Section 3, $\Delta_f$ is an immersion, and it is enough to treat $X = \operatorname{Spec} B$ and $Y = \operatorname{Spec} A$. Let $\mu : B \otimes_A B \to B$ be the multiplication with kernel $J$. If $B = A[b_1, \dots, b_m]$, then $J$ is generated by the elements $b_j \otimes 1 - 1 \otimes b_j$, so it is finitely generated. The $B$-module $J/J^2$ is $\Omega_{B/A}$, which is $0$. So $J = J^2$, and the lemma gives an idempotent $e$ with $J = (e)$. Then $\operatorname{Spec} B = V(e)$, and $V(e) = D(1 - e)$ since $e(1 - e) = 0$ and $e + (1 - e) = 1$. The ring map $B \otimes_A B \to (B \otimes_A B)_{1-e}$ is the quotient by $(e)$, so $\Delta_f$ is the inclusion of the open set $D(1 - e)$. $\square$

**Theorem (Étale, flat and unramified).** A morphism is étale if and only if it is flat, formally unramified and locally of finite presentation. A morphism is étale if and only if it is smooth of relative dimension $0$.

One step is short. Let $A$ be formally étale over $R$ and $C = A \oplus \Omega_{A/R}$ with $\Omega_{A/R}^2 = 0$. The maps $a \mapsto (a, 0)$ and $a \mapsto (a, da)$ are $R$-algebra maps $A \to C$ that both lift the identity of $A = C/\Omega_{A/R}$. Uniqueness of lifts gives $d = 0$, and $\Omega_{A/R}$ is generated by the image of $d$, so $\Omega_{A/R} = 0$. Flatness and the converse use the local structure theory of étale algebras of Volume 10, Chapter 8; the index proves both through the ring statements, and this section does not reproduce them.

**Proposition (Étale is weakly étale).** An étale morphism is weakly étale.

*Proof.* An étale $f$ is flat. It is formally unramified and locally of finite type, so $\Delta_f$ is an open immersion by the theorem. An open immersion is flat, since its stalk maps are isomorphisms. So $\Delta_f$ is flat and $f$ is weakly étale. $\square$

**Theorem (Smoothness on fibers).** Let $f : X \to Y$ be flat and locally of finite presentation, and let every fiber $X_y \to \operatorname{Spec} \kappa(y)$ be smooth. Then $f$ is smooth.

The index proves it from the ring statement: a flat finitely presented algebra with smooth fiber algebras is smooth. The smooth locus is open, and over a perfect field $K$ the smooth locus of a reduced $X$ locally of finite presentation over $K$ is dense; it contains the generic point when $X$ is integral.

### Examples

**Example (Affine space is smooth).** Let $A = R[x_1, \dots, x_n]$. The presentation with $n$ generators and no relations is submersive: $c = 0$, and the empty determinant is $1$. So $\mathbb{A}^n_R \to \operatorname{Spec} R$ is smooth of relative dimension $n$. A direct proof of formal smoothness: given $\bar g : A \to C/I$, choose $c_i \in C$ with image $\bar g(x_i)$; the map $x_i \mapsto c_i$ is an $R$-algebra map $A \to C$ that lifts $\bar g$, because $A$ is a polynomial ring. The module $\Omega_{A/R}$ is free with basis $dx_1, \dots, dx_n$, so $\mathbb{A}^n_R$ is not unramified for $n \geq 1$.

**Example (Squaring the line).** Let $k$ be a field with $\operatorname{char} k \neq 2$ and $f : \mathbb{A}^1 \to \mathbb{A}^1$ come from $\varphi : k[t] \to k[x]$, $t \mapsto x^2$. By Section 2, $f$ is finite and flat of rank $2$. The module of differentials is
$$\Omega_{k[x]/k[t]} = k[x]\, dx / (d(x^2)) = k[x]\, dx / (2x\, dx) \cong k[x]/(x),$$
since $2$ is a unit. Its support is the origin. So $f$ is unramified exactly on $D(x)$. On $D(x)$, write $k[x, x^{-1}] = k[t][x, y]/(x^2 - t, xy - 1)$: modulo $x^2 - t$ the ring is $k[x, y]$, and modulo $xy - 1$ it is $k[x, x^{-1}]$. The Jacobian of $(x^2 - t, xy - 1)$ with respect to $(x, y)$ is
$$\det \begin{pmatrix} 2x & 0 \\ y & x \end{pmatrix} = 2x^2,$$
a unit in $k[x, x^{-1}]$. So the restriction of $f$ to $D(x)$ is standard smooth of relative dimension $2 - 2 = 0$, that is, étale. At the origin the fiber is $\operatorname{Spec} k[x]/(x^2)$ and its differentials are $k[x]\,dx/(x^2, 2x\,dx) \cong k$, not $0$, so $f$ is not étale at the origin. Over $\mathbb{C}$ this is the branch point of $z \mapsto z^2$.

**Counterexample (Squaring in characteristic two).** Let $\operatorname{char} k = 2$. Then $d(x^2) = 2x\, dx = 0$, so $\Omega_{k[x]/k[t]} = k[x]\, dx$ is free of rank $1$. The map $x \mapsto x^2$ is ramified at every point. Each fiber ring $\kappa[x]/(x^2 - a)$ has one prime, and its residue field is purely inseparable over $\kappa$, since $x^2 = a$ there. So $f$ is universally injective but nowhere étale.

**Example (The Gaussian integers).** For $\mathbb{Z} \to \mathbb{Z}[i] = \mathbb{Z}[x]/(x^2 + 1)$, the differentials are $\mathbb{Z}[i]\, dx / (2i\, dx) \cong \mathbb{Z}[i]/(2)$, since $i$ is a unit. The primes of $\mathbb{Z}[i]$ that contain $2 = -i(1 + i)^2$ are the primes that contain $1 + i$, and $(1 + i)$ is maximal with residue field $\mathbb{F}_2$. So $\operatorname{Spec} \mathbb{Z}[i] \to \operatorname{Spec} \mathbb{Z}$ is unramified exactly away from $(1 + i)$. It is flat and finitely presented, so it is étale over $\operatorname{Spec} \mathbb{Z}[1/2]$. This matches the fibers of Section 2: the fiber over $2$ has a nilpotent, and the fibers over $3$ and $5$ are products of fields.

**Counterexample (The cusp).** Let $X = \operatorname{Spec} B$ with $B = k[x, y]/(y^2 - x^3)$. The module $\Omega_{B/k}$ is generated by $dx, dy$ with the relation $2y\,dy - 3x^2\,dx = 0$. At the origin the relation vanishes, so $\Omega_{B/k} \otimes \kappa(0)$ has dimension $2$. The fraction field of $B$ is $k(s)$ with $x = s^2$ and $y = s^3$, so at the generic point $\Omega$ has rank $1$. If $X$ were smooth near the origin, $\Omega_{B/k}$ would be locally free there, of constant rank on the irreducible $X$, hence of rank $1$ at the origin. So $X \to \operatorname{Spec} k$ is not smooth at the origin. Away from the origin, one of $2y$ and $3x^2$ is a unit when $\operatorname{char} k \notin \{2, 3\}$, and $X$ is smooth there.

### The library around it

::: mathlib
`AlgebraicGeometry.FormallyUnramified` · `Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified`

The field is `formallyUnramified_appLE`, with `RingHom.FormallyUnramified` from `Algebra.FormallyUnramified`, whose definition is `Subsingleton Ω[A⁄R]`. `FormallyUnramified.hom_ext` is the scheme form of infinitesimal uniqueness, for `i` a closed immersion with `IsNilpotent i.ker`. `FormallyUnramified.of_hom_ext` is the converse criterion with square-zero thickenings of affine schemes.

<?decl AlgebraicGeometry.FormallyUnramified?>
:::

::: mathlib
`AlgebraicGeometry.FormallyUnramified.isOpenImmersion_diagonal` · `Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified`

This instance needs `[FormallyUnramified f] [LocallyOfFiniteType f]` and gives `IsOpenImmersion (pullback.diagonal f)`. The idempotent criterion `isOpenImmersion_SpecMap_iff_of_surjective` of Section 1 is the affine form of the last step of the proof.

<?decl AlgebraicGeometry.FormallyUnramified.isOpenImmersion_diagonal?>
:::

::: mathlib
`AlgebraicGeometry.Smooth` · `Mathlib.AlgebraicGeometry.Morphisms.Smooth`

The field is `smooth_appLE`, with `Algebra.Smooth` from formal smoothness and finite presentation. `Smooth.iff_forall_exists_isStandardSmooth` gives standard smooth charts around every point. `SmoothOfRelativeDimension n f` asks `Algebra.IsStandardSmoothOfRelativeDimension n` on such charts; the presentations are `Algebra.SubmersivePresentation`. `Scheme.Hom.smoothLocus` is the smooth locus, with `Scheme.Hom.isOpen_smoothLocus`, `Scheme.Hom.smoothLocus_eq_top_iff`, `Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField` and `Scheme.Hom.dense_smoothLocus_of_perfectField`. `formallySmooth_stalkMap_iff` relates the stalks to the charts.

<?decl AlgebraicGeometry.Smooth?>
:::

::: mathlib
`AlgebraicGeometry.AffineSpace.smoothOfRelativeDimension` · `Mathlib.AlgebraicGeometry.AffineSpace`

For `n` finite, this instance gives `SmoothOfRelativeDimension (Nat.card n) (𝔸(n; S) ↘ S)`, the first example.

<?decl AlgebraicGeometry.AffineSpace.smoothOfRelativeDimension?>
:::

::: mathlib
`AlgebraicGeometry.Etale` · `Mathlib.AlgebraicGeometry.Morphisms.Etale`

The field is `etale_appLE`, with `RingHom.Etale`. `Etale.iff_flat_and_formallyUnramified` is `Etale f ↔ Flat f ∧ FormallyUnramified f ∧ LocallyOfFinitePresentation f`, and `Etale.of_formallyUnramified_of_flat` is the direction as instances. `Etale.iff_smoothOfRelativeDimension_zero` is the second equivalence. `Scheme.Etale X` is the category of schemes étale over `X`, used for the étale site in Chapter 6.

<?decl AlgebraicGeometry.Etale?>
:::

::: mathlib
`AlgebraicGeometry.Smooth.of_smooth_fiberToSpecResidueField` · `Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber`

Under `[LocallyOfFinitePresentation f] [Flat f]`, smoothness of every `f.fiberToSpecResidueField y` gives `Smooth f`.

<?decl AlgebraicGeometry.Smooth.of_smooth_fiberToSpecResidueField?>
:::

::: mathlib
`AlgebraicGeometry.WeaklyEtale` · `Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`

The fields are `flat` and `flat_diagonal`. `WeaklyEtale.weaklyEtale_eq_flat_inf_diagonal_flat` restates the definition, and `etale_le_weaklyEtale` is the proposition. Weakly étale morphisms define the pro-étale topology of Bhatt and Scholze; the index of this edition has no declaration for that site.

<?decl AlgebraicGeometry.WeaklyEtale?>
:::

Common errors of a learner: `FormallyUnramified f` has no finiteness condition, so the unramified morphism of the literature is `FormallyUnramified f ∧ LocallyOfFiniteType f`. `Smooth f` already includes finite presentation, through `Algebra.Smooth`. The relative dimension in `SmoothOfRelativeDimension n` is the number of generators minus the number of relations, not the dimension of the fibers as a definition, although the two agree. A finite flat morphism of rank $2$, such as $x \mapsto x^2$, can be étale on a dense open and still ramified at one point.

### Exercises

1. (A) Show that an open immersion is étale. *Hint:* A localization $A \to A_a$ has the presentation $A[y]/(ay - 1)$ with Jacobian $a$.
2. (A) Show that $\operatorname{Spec} L \to \operatorname{Spec} K$ is étale for a finite separable field extension $L = K[x]/(p)$. *Hint:* The Jacobian $p'(x)$ is a unit in $L$ because $p$ is separable.
3. (B) Let $n \geq 2$ and $\operatorname{char} k \nmid n$. Show that $x \mapsto x^n$ on $\mathbb{A}^1_k$ is étale exactly on $D(x)$. *Hint:* $\Omega = k[x]/(n x^{n-1})$.
4. (B) Show that a closed immersion is formally unramified, and that $\operatorname{Spec} A/I \to \operatorname{Spec} A$ with $I$ finitely generated is flat only if it is also open. *Hint:* For a surjection $A \to A/I$, $\Omega_{(A/I)/A} = 0$; for flatness, $\operatorname{Tor}_1^A(A/I, A/I) = I/I^2$, and use the lemma on idempotents.
5. (B) Show that $\mathbb{A}^1_{\mathbb{Z}} \to \operatorname{Spec} \mathbb{Z}$, $\operatorname{Spec} \mathbb{Z}[x] \to \operatorname{Spec} \mathbb{Z}$, is smooth, and that $\operatorname{Spec} \mathbb{Z}[\sqrt{-3}] \to \operatorname{Spec} \mathbb{Z}$ is étale exactly over $\mathbb{Z}[1/6]$. *Hint:* $\mathbb{Z}[\sqrt{-3}] = \mathbb{Z}[x]/(x^2 + 3)$ and $\Omega \cong \mathbb{Z}[\sqrt{-3}]/(2\sqrt{-3})$.
6. (C) Let $f$ be unramified and separated, and let $s, s' : Y \to X$ be two sections of $f$ with $Y$ connected. Show that $s = s'$ or the images of $s$ and $s'$ are disjoint. *Hint:* The equalizer of $s, s'$ is the preimage of the diagonal, which is open and closed.

### Notes and history

Smooth, étale and unramified morphisms in this form are due to Grothendieck in EGA IV and SGA 1, from the series of 1960 to 1967; SGA 1 uses étale morphisms to define the étale fundamental group. The formal notions with infinitesimal lifting are from EGA IV. Weakly étale morphisms are from the work of Bhatt and Scholze on the pro-étale topology. The smooth part of the library grew from the AIM workshop "Formalizing algebraic geometry" in June 2024, as the docstrings of `Morphisms.Smooth` record.

The Mathlib Author of `Morphisms.FormallyUnramified` is Andrew Yang. The Mathlib Author of `Morphisms.Etale`, `Morphisms.Smooth` and `Morphisms.SmoothFiber` is Christian Merten. The Mathlib Authors of `Morphisms.WeaklyEtale` are Jiedong Jiang and Christian Merten.

### Reference

<?reference?>
