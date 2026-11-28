---
title: Ideal sheaves, quasi-coherent modules and closed subschemes
kind: theory
modules:
  - Mathlib.AlgebraicGeometry.IdealSheaf.Basic
  - Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
  - Mathlib.AlgebraicGeometry.IdealSheaf.IrreducibleComponent
  - Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
  - Mathlib.AlgebraicGeometry.Modules.Presheaf
  - Mathlib.AlgebraicGeometry.Modules.Sheaf
  - Mathlib.AlgebraicGeometry.Modules.Tilde
explains:
  E3: [AlgebraicGeometry.Scheme.IdealSheafData, AlgebraicGeometry.Scheme.IdealSheafData.equivOfIsAffine, AlgebraicGeometry.Scheme.IdealSheafData.support, AlgebraicGeometry.Scheme.IdealSheafData.gc, AlgebraicGeometry.Scheme.Hom.ker, AlgebraicGeometry.Scheme.Hom.support_ker, AlgebraicGeometry.Scheme.IdealSheafData.subscheme, AlgebraicGeometry.Scheme.Hom.image, AlgebraicGeometry.Scheme.Modules, AlgebraicGeometry.tilde, AlgebraicGeometry.tilde.adjunction, AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ]
  E2: [AlgebraicGeometry.Scheme.IdealSheafData.ofIdeals, AlgebraicGeometry.Scheme.IdealSheafData.mem_support_iff_of_mem, AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal, AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_support, AlgebraicGeometry.Scheme.nilradical, AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_top, AlgebraicGeometry.Scheme.ker_of_isAffine, AlgebraicGeometry.Scheme.IdealSheafData.subschemeι, AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι, AlgebraicGeometry.Scheme.IdealSheafData.subschemeObjIso, AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι, AlgebraicGeometry.Scheme.isIso_subschemeι_iff_eq_bot, AlgebraicGeometry.Scheme.Hom.imageι, AlgebraicGeometry.Scheme.Hom.toImage, AlgebraicGeometry.Scheme.kerAdjunction, AlgebraicGeometry.Scheme.IdealSheafData.comap, AlgebraicGeometry.Scheme.IdealSheafData.map, AlgebraicGeometry.Scheme.IdealSheafData.map_gc, AlgebraicGeometry.Scheme.irreducibleComponentOpen, AlgebraicGeometry.Scheme.irreducibleComponentIdeal, AlgebraicGeometry.Scheme.irreducibleComponent, AlgebraicGeometry.Scheme.irreducibleComponentι, AlgebraicGeometry.Scheme.ringCatSheaf, AlgebraicGeometry.Scheme.Modules.pushforward, AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction, AlgebraicGeometry.tilde.functor, AlgebraicGeometry.tilde.isoTop, AlgebraicGeometry.tilde.fullyFaithfulFunctor, AlgebraicGeometry.Scheme.Modules.fromTildeΓ, AlgebraicGeometry.IsLocalizing, AlgebraicGeometry.isIso_fromTildeΓ_iff_isLocalizing, AlgebraicGeometry.essImage_tilde, AlgebraicGeometry.tildeEquiv]
  E1: auto
families: []
requires: [V07.C01, V09.C01, V09.C02, V24.C05, V24.C08, V28.C01, V28.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Ideal sheaves, quasi-coherent modules and closed subschemes

### Overview

An ideal $J$ of a ring $R$ gives the closed subscheme $\operatorname{Spec} R/J$ of $\operatorname{Spec} R$. On a general scheme the ideal must be given on each affine open, compatibly with localization. Such data is an *ideal sheaf*. It has a support, which is a closed set, and a closed subscheme, which is a scheme whose underlying set is the support. The ideals $(x)$ and $(x^2)$ of $k[x]$ have the same support, and the ideal sheaf keeps the difference.

This section treats ideal sheaves, kernels, scheme-theoretic images and irreducible components as subschemes. It then treats sheaves of modules and the sheaf $\widetilde{M}$ of an $R$-module, the model of a quasi-coherent sheaf.

### Definitions

For an affine open $U$ of $X$ and $f \in \Gamma(X, U)$, the basic open $D(f) \subseteq U$ is affine with $\Gamma(X, D(f)) = \Gamma(X, U)_f$. For an ideal $J$ of $\Gamma(X, U)$, write $J_f$ for the ideal of $\Gamma(X, U)_f$ that $J$ generates.

**Definition (Ideal sheaf).** An *ideal sheaf* $I$ on a scheme $X$ is a family of ideals $I(U) \subseteq \Gamma(X, U)$, one for each affine open $U$, such that $I(D(f)) = I(U)_f$ for each affine open $U$ and each $f \in \Gamma(X, U)$. Ideal sheaves are ordered by $I \leq I'$ when $I(U) \subseteq I'(U)$ for all $U$.

This is a quasi-coherent sheaf of ideals of $\mathcal{O}_X$, read on the affine opens; the compatibility condition expresses quasi-coherence. Ideal sheaves are closed under arbitrary sums, so for each family $J$ of ideals there is a largest ideal sheaf $I$ with $I(U) \subseteq J(U)$ for all $U$.

**Definition (Support).** The *support* of $I$ is the set of $x \in X$ such that $x \in V(I(U))$ for each affine open $U$ that contains $x$. Here $V(I(U))$ is the set of points $x \in U$ at which each element of $I(U)$ has germ in the maximal ideal $\mathfrak m_x$.

**Definition (Vanishing ideal).** For a closed set $Z \subseteq X$, the *vanishing ideal* $I_Z$ is the ideal sheaf with $I_Z(U)$ the set of $s \in \Gamma(X, U)$ whose germ lies in $\mathfrak m_x$ for each $x \in Z \cap U$. The vanishing ideal of $X$ itself is the *nilradical* $\mathcal{N}_X$, with $\mathcal{N}_X(U)$ the nilradical of $\Gamma(X, U)$.

**Definition (Kernel).** The *kernel* of a morphism $f : X \to Y$ is the largest ideal sheaf $\ker f$ on $Y$ with $(\ker f)(U) \subseteq \ker\big(\Gamma(Y, U) \to \Gamma(X, f^{-1} U)\big)$ for each affine open $U$.

**Definition (Sheaf of modules).** A *sheaf of modules* on $X$ is a sheaf $M$ of abelian groups with a compatible $\Gamma(X, U)$-module structure on each $M(U)$. A sheaf of modules is *quasi-coherent* when each point has an open neighbourhood $U$ on which $M|_U$ is the cokernel of a map $\mathcal{O}_U^{(J)} \to \mathcal{O}_U^{(I)}$ of free modules.

**Definition (The sheaf of a module).** Let $M$ be an $R$-module. The sheaf $\widetilde{M}$ on $\operatorname{Spec} R$ sends an open $U$ to the functions $s$ with $s(\mathfrak p) \in M_{\mathfrak p}$ for $\mathfrak p \in U$ that are locally of the form $m/g$, with $m \in M$ and $g \in R$ outside the primes nearby.

This repeats the structure sheaf of Chapter 3 with $M$ in place of $R$, and the same proof gives $\widetilde{M}(D(g)) \cong M_g$ and $\widetilde{M}_{\mathfrak p} \cong M_{\mathfrak p}$.

### Theorems and proofs

**Theorem (Ideal sheaves on an affine scheme).** Let $X = \operatorname{Spec} R$. The map $I \mapsto I(X)$ is an order isomorphism from the ideal sheaves on $X$ to the ideals of $R$. Its inverse sends $J$ to the family $U \mapsto J\,\Gamma(X, U)$.

*Proof.* *The family is an ideal sheaf,* since $J\,\Gamma(X, D(f)) = (J\,\Gamma(X, U))_f$, and its value at $X$ is $J$.

*An ideal sheaf is determined by $I(X)$.* Let $U$ be an affine open. The basic opens $D(g)$ of $X$ with $g \in R$ and $D(g) \subseteq U$ cover $U$, and $D(g) = D(g|_U)$ is also a basic open of $U$. As $U$ is quasi-compact, finitely many $g_1, \dots, g_n$ suffice, and the elements $g_i|_U$ generate the unit ideal of $\Gamma(X, U)$. The condition of the definition, applied twice, gives
$$I(U)_{g_i|_U} = I(D(g_i)) = I(X)_{g_i} = (I(X)\, \Gamma(X, U))_{g_i|_U}.$$
An ideal of a ring is determined by its localizations at elements that generate the unit ideal: if $J_1$ and $J_2$ have the same localizations and $r \in J_1$, then $g_i^m r \in J_2$ for all $i$ and some $m$, and $r = \sum c_i g_i^m r \in J_2$ for some $c_i$ with $\sum c_i g_i^m = 1$. So $I(U) = I(X)\,\Gamma(X, U)$.

The two maps are inverse, and both preserve the order. $\square$

**Lemma (Support on an affine open).** Let $U$ be an affine open and $x \in U$. Then $x$ lies in the support of $I$ if and only if $x \in V(I(U))$. In particular the support is closed.

*Proof.* Let $V$ be another affine open that contains $x$. There is an open $D$ with $x \in D \subseteq U \cap V$ that is a basic open $D(f)$ of $U$ and a basic open $D(g)$ of $V$. A prime of $\Gamma(X, U)$ that misses $f$ contains $I(U)$ if and only if its extension contains $I(U)_f = I(D)$. So $x \in V(I(U))$ if and only if $x \in V(I(D))$, and in the same way if and only if $x \in V(I(V))$. Hence the condition does not depend on the affine open. The support meets each affine open $U$ in the closed set $V(I(U))$ of $U$, so it is closed. $\square$

**Theorem (Support and vanishing ideal).** For an ideal sheaf $I$ and a closed set $Z$, $Z \subseteq \operatorname{supp} I$ if and only if $I \leq I_Z$. The vanishing ideal of $\operatorname{supp} I$ is the radical $\sqrt{I}$, given by $U \mapsto \sqrt{I(U)}$.

*Proof.* By the lemma, $Z \subseteq \operatorname{supp} I$ if and only if $Z \cap U \subseteq V(I(U))$ for each affine open $U$. A point $x \in U$ lies in $V(I(U))$ exactly when each $s \in I(U)$ has germ in $\mathfrak m_x$. So the condition says that each $s \in I(U)$ lies in $I_Z(U)$, that is, $I \leq I_Z$. For the second claim, $I_{\operatorname{supp} I}(U)$ is the intersection of the primes of $\Gamma(X, U)$ that contain $I(U)$. By the description of the radical as an intersection of primes, this is $\sqrt{I(U)}$. $\square$

So support and vanishing ideal form a Galois connection, with the reverse order on closed sets.

**Theorem (The closed subscheme of an ideal sheaf).** For each ideal sheaf $I$ on $X$ there is a scheme $V(I)$ with a closed immersion $\iota : V(I) \to X$ such that $\iota^{-1}(U) \cong \operatorname{Spec} \Gamma(X, U)/I(U)$ for each affine open $U$, the image of $\iota$ is $\operatorname{supp} I$, and $\ker \iota = I$. The morphism $\iota$ is an isomorphism if and only if $I = 0$.

*Proof.* For each affine open $U$ put $W_U = \operatorname{Spec} \Gamma(X, U)/I(U)$, a closed subscheme of $U$ with image $V(I(U))$. For $f \in \Gamma(X, U)$,
$$\big(\Gamma(X, U)/I(U)\big)_f \cong \Gamma(X, U)_f / I(U)_f = \Gamma(X, D(f))/I(D(f)),$$
so $W_U \cap D(f) = W_{D(f)}$ as subschemes of $D(f)$. Two affine opens meet in a union of opens basic in both, so the $W_U$ glue to a scheme $V(I)$ with a morphism $\iota$ to $X$. Over each $U$ the morphism is the closed immersion $W_U \to U$, so $\iota$ is a closed immersion, and its image meets $U$ in $V(I(U))$. By the lemma the image is $\operatorname{supp} I$. Over $U$, the kernel of $\Gamma(X, U) \to \Gamma(X, U)/I(U)$ is $I(U)$, so $\ker \iota = I$. If $\iota$ is an isomorphism, its kernel is $0$, so $I = 0$. If $I = 0$, then each $W_U \to U$ is the identity. $\square$

**Theorem (Kernel and closure of the image).** Let $f : X \to Y$ be quasi-compact. Then the support of $\ker f$ is the closure of $f(X)$.

*Proof.* Both sides meet an affine open $U \subseteq Y$ in the same set for the restriction $f^{-1}(U) \to U$, so assume $Y = \operatorname{Spec} R$. Then $X$ is quasi-compact. Let $\varphi : R \to \Gamma(X, X)$ be the ring map, so that $\ker f$ corresponds to $\ker \varphi$. The point $f(x)$ is the prime $\{ r : \varphi(r)_x \in \mathfrak m_x \}$, so the closure of $f(X)$ is $V(K)$, with $K$ the set of $r$ such that $\varphi(r)_x \in \mathfrak m_x$ for all $x$. Let $X = U_1 \cup \dots \cup U_n$ with $U_i$ affine. If $r \in K$, then $\varphi(r)|_{U_i}$ lies in each prime of $\Gamma(X, U_i)$, so it is nilpotent, say $\varphi(r)^{m}|_{U_i} = 0$ for all $i$ with one $m$. By the sheaf axiom $\varphi(r^m) = 0$. So $K = \sqrt{\ker \varphi}$, the other inclusion being clear. Then $V(K) = V(\ker \varphi)$, which is the support of $\ker f$. $\square$

**Theorem (Scheme-theoretic image).** Let $f : X \to Y$ be a morphism and $I$ an ideal sheaf on $Y$. Then $f$ factors through $V(I) \to Y$ if and only if $I \leq \ker f$, and the factorization is unique. So $f$ factors through the closed subscheme $V(\ker f)$, and this is the smallest closed subscheme of $Y$ of the form $V(I)$ through which $f$ factors.

*Proof.* The closed immersion $\iota$ is a monomorphism, so a factorization is unique. Both conditions are local on $Y$. Let $U \subseteq Y$ be affine open and $\varphi : \Gamma(Y, U) \to \Gamma(X, f^{-1} U)$. A morphism $f^{-1}(U) \to \operatorname{Spec} \Gamma(Y, U)$ corresponds to $\varphi$, and it factors through $\operatorname{Spec} \Gamma(Y, U)/I(U)$ if and only if $\varphi$ kills $I(U)$. This holds for each $U$ if and only if $I(U) \subseteq \ker \varphi$ for each $U$, that is, $I \leq \ker f$ by the maximality in the definition of the kernel. The ideal $\ker f$ satisfies the condition, and each $I$ that satisfies it is smaller. $\square$

The scheme $V(\ker f)$ is the *scheme-theoretic image* of $f$. When $f$ is quasi-compact, its underlying set is the closure of $f(X)$ by the previous theorem.

**Proposition (Irreducible components as subschemes).** Let $X$ be Noetherian and $Z$ an irreducible component of $X$. Let $U$ be the complement of the union of the other irreducible components, and $I$ the kernel of the open immersion $U \to X$. Then $V(I)$ is a closed subscheme with underlying set $Z$. If $X$ is irreducible, then $U = X$ and $V(I) = X$.

*Proof.* There are finitely many components, so $U$ is open, and $U \subseteq Z$. If $U$ were empty, the irreducible $Z$ would lie in the finite union of the other components, hence in one of them, against maximality. So $U$ is a nonempty open subset of the irreducible space $Z$, and it is dense in $Z$. The open immersion is quasi-compact since $X$ is Noetherian, so the support of $I$ is $\overline{U} = Z$. If $X$ is irreducible, $Z = X$ and $U = X$, the kernel is $0$, and $\iota$ is an isomorphism. $\square$

**Theorem (The sheaf of a module).** Let $R$ be a ring. The functor $M \mapsto \widetilde{M}$ is left adjoint to $N \mapsto \Gamma(N) = N(\operatorname{Spec} R)$, and it is fully faithful. The sheaf $\widetilde{M}$ is quasi-coherent.

*Proof.* *Adjunction.* Let $\alpha : M \to \Gamma(N)$ be $R$-linear. On $D(g)$ the element $g$ acts invertibly on $N(D(g))$, so $m/g^n \mapsto g^{-n} \cdot \alpha(m)|_{D(g)}$ is a well defined linear map $M_g \to N(D(g))$. They commute with restriction, so they define a morphism $\widetilde{M} \to N$ on the basis of basic opens. Conversely, a morphism $\widetilde{M} \to N$ gives $M = \widetilde{M}(\operatorname{Spec} R) \to \Gamma(N)$. These are inverse, since $M_g$ is generated by $M$ and $g^{-1}$.

*Full faithfulness.* The unit $M \to \Gamma(\widetilde{M}) = M_1 = M$ is invertible, and a left adjoint with invertible unit is fully faithful.

*Quasi-coherence.* Choose a presentation $R^{(J)} \to R^{(I)} \to M \to 0$. Localization at $g$ is exact and commutes with direct sums, so on each $D(g)$ the sequence $R_g^{(J)} \to R_g^{(I)} \to M_g \to 0$ is exact. Hence $\mathcal{O}^{(J)} \to \mathcal{O}^{(I)} \to \widetilde{M} \to 0$ is exact on stalks, and so exact. $\square$

**Theorem (Quasi-coherent modules on an affine scheme).** For a sheaf of modules $N$ on $\operatorname{Spec} R$, the counit $\widetilde{\Gamma(N)} \to N$ is an isomorphism if and only if $\Gamma(N) \to N(D(g))$ is a localization at $g$ for each $g \in R$. Such an $N$ is quasi-coherent.

*Proof.* Suppose the second condition. The counit on $D(g)$ is the map $\Gamma(N)_g \to N(D(g))$, which is then an isomorphism. A morphism of sheaves that is an isomorphism on a basis of opens is an isomorphism. Conversely, if the counit is an isomorphism, then $N \cong \widetilde{M}$ with $M = \Gamma(N)$, and $\Gamma(\widetilde{M}) \to \widetilde{M}(D(g))$ is the localization $M \to M_g$. The sheaf $\widetilde{M}$ is quasi-coherent by the previous theorem. $\square$

**Remark (The converse).** Each quasi-coherent $N$ on $\operatorname{Spec} R$ satisfies these conditions; the proof uses the sheaf axiom on a finite cover by basic opens on which $N$ has a presentation. So $M \mapsto \widetilde{M}$ is an equivalence between $R$-modules and quasi-coherent modules on $\operatorname{Spec} R$.

### Examples

**Example (A closed immersion from an ideal).** An ideal $J \subseteq R$ gives the ideal sheaf $U \mapsto J\,\Gamma(X, U)$ on $X = \operatorname{Spec} R$, and its closed subscheme is $\operatorname{Spec} R/J \to \operatorname{Spec} R$, with image $V(J)$. For $J = (p)$ in $\mathbb{Z}$, it is the closed point $\operatorname{Spec} \mathbb{F}_p$.

**Example (Same support, different ideals).** In $R = k[x]$, the ideals $(x)$ and $(x^2)$ have the same support $\{(x)\}$, a single closed point. The vanishing ideal of this point is $\sqrt{(x^2)} = (x)$. The closed subschemes differ: $\operatorname{Spec} k[x]/(x)$ is reduced, while $\operatorname{Spec} k[x]/(x^2)$ has the nilpotent function $x$.

**Example (The nilradical).** The closed subscheme $V(\mathcal{N}_X)$ is reduced, with the same underlying space as $X$. It is the *reduction* $X_{\mathrm{red}}$. For $X = \operatorname{Spec} k[x, y]/(y^2)$ it is $\operatorname{Spec} k[x]$.

**Example (The image of a curve).** Let $f : \operatorname{Spec} k[t] \to \operatorname{Spec} k[x, y]$ be given by $x \mapsto t^2$, $y \mapsto t^3$. The kernel of $\varphi : k[x, y] \to k[t]$ contains $y^2 - x^3$. Modulo $y^2 - x^3$, each element is $a(x) + y\, b(x)$, with image $a(t^2) + t^3 b(t^2)$. Even and odd powers of $t$ separate, so the image is zero only if $a = b = 0$. So $\ker \varphi = (y^2 - x^3)$, and the scheme-theoretic image is the cusp $\operatorname{Spec} k[x, y]/(y^2 - x^3)$.

**Example (A skyscraper module).** Let $M = k[x]/(x)$ on $\operatorname{Spec} k[x]$. For a prime $\mathfrak p$, $M_{\mathfrak p} = 0$ unless $x \in \mathfrak p$, since otherwise $x$ is a unit that acts as $0$. So $\widetilde{M}$ has stalk $k$ at the origin and $0$ elsewhere. It is the pushforward of $\mathcal{O}$ along the closed immersion of the origin.

### The library around it

::: mathlib
`AlgebraicGeometry.Scheme.IdealSheafData` · `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`

The fields are `ideal`, `map_ideal_basicOpen` and `supportSet`. The docstring states that ideal sheaves are not yet defined as subsheaves of `𝒪ₓ`. The largest ideal sheaf in a family is `ofIdeals`, and the affine theorem is `equivOfIsAffine`, an order isomorphism.

<?decl AlgebraicGeometry.Scheme.IdealSheafData?>
:::

::: mathlib
`AlgebraicGeometry.Scheme.IdealSheafData.gc` · `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`

The Galois connection between `support` and `vanishingIdeal`. See `mem_support_iff_of_mem`, `vanishingIdeal_support` for the radical, and `vanishingIdeal_top`, which equals `X.nilradical`.

<?decl AlgebraicGeometry.Scheme.IdealSheafData.gc?>
:::

::: mathlib
`AlgebraicGeometry.Scheme.Hom.support_ker` · `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`

For `[QuasiCompact f]`, `f.ker.support = closure (Set.range f)`. The kernel `Hom.ker` is `ofIdeals` of the kernels of `f.app U`, and `ker_of_isAffine` computes it over an affine target.

<?decl AlgebraicGeometry.Scheme.Hom.support_ker?>
:::

::: mathlib
`AlgebraicGeometry.Scheme.IdealSheafData.subscheme` · `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`

The closed subscheme, with `subschemeι`, `subschemeObjIso`, `range_subschemeι`, `ker_subschemeι` and `isIso_subschemeι_iff_eq_bot`. The image is `Hom.image`, with `Hom.imageι` and `Hom.toImage`, and `kerAdjunction` is the universal property. The pullback and pushforward of ideal sheaves are `IdealSheafData.comap` and `IdealSheafData.map`, related by `map_gc`. The irreducible components are `Scheme.irreducibleComponent` with `irreducibleComponentι`.

<?decl AlgebraicGeometry.Scheme.IdealSheafData.subscheme?>
:::

::: mathlib
`AlgebraicGeometry.Scheme.Modules` · `Mathlib.AlgebraicGeometry.Modules.Sheaf`

`X.Modules` is `SheafOfModules X.ringCatSheaf`, an abelian category, with `Modules.pushforward`, `Modules.pullback` and `pullbackPushforwardAdjunction`.

<?decl AlgebraicGeometry.Scheme.Modules?>
:::

::: mathlib
`AlgebraicGeometry.tilde` · `Mathlib.AlgebraicGeometry.Modules.Tilde`

The sheaf of a module, with `tilde.functor`, `tilde.isoTop`, `tilde.adjunction` against `moduleSpecΓFunctor`, and `tilde.fullyFaithfulFunctor`. The counit is `Scheme.Modules.fromTildeΓ`. The second condition of the theorem is `IsLocalizing`, and `isIso_fromTildeΓ_iff_isLocalizing` is its equivalence with the first. The equivalence of categories is `tildeEquiv`, and `essImage_tilde` describes the essential image.

<?decl AlgebraicGeometry.tilde?>
:::

::: mathlib
`AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ` · `Mathlib.AlgebraicGeometry.Modules.Tilde`

The equivalence of the theorem and the remark: `M.IsQuasicoherent ↔ IsIso M.fromTildeΓ`. Quasi-coherence is the class `SheafOfModules.IsQuasicoherent`, local presentations by free modules.

<?decl AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ?>
:::

Common errors of a learner: an `IdealSheafData` is not a subsheaf of `𝒪ₓ`; it is quasi-coherent data on affine opens. `Hom.ker f` is an ideal sheaf on the target. `Hom.image` has underlying set the closure of the range only for quasi-compact `f`. Only the quasi-coherent modules on `Spec R` are of the form `tilde M`.

### Exercises

1. (A) Find the support and the closed subscheme of the ideal $(x^2, xy)$ in $k[x, y]$. *Hint:* $(x^2, xy) = (x) \cap (x^2, y)$, and its radical is $(x)$.
2. (A) Show that the scheme-theoretic image of $D(x) \to \operatorname{Spec} k[x]$ is $\operatorname{Spec} k[x]$. *Hint:* $k[x] \to k[x, x^{-1}]$ is injective.
3. (B) Show that $\operatorname{supp} I \cup \operatorname{supp} I' = \operatorname{supp}(I \cap I')$ for ideal sheaves $I, I'$ on $\operatorname{Spec} R$. *Hint:* Use the affine theorem and $V(J) \cup V(J') = V(J \cap J')$.
4. (B) Let $M = k[x, x^{-1}]$ as a $k[x]$-module. Compute the stalks of $\widetilde{M}$. *Hint:* $M_{\mathfrak p} = k[x]_{\mathfrak p}[x^{-1}]$, which is $k(x)$ at $\mathfrak p = (x)$.
5. (B) Show that $M \mapsto \widetilde{M}$ is exact. *Hint:* Check on stalks.
6. (C) Let $f : \coprod_{n \geq 1} \operatorname{Spec} \mathbb{Q} \to \operatorname{Spec} \mathbb{Q}[x]$ send the $n$-th point to $(x - n)$. Show that $\ker f = 0$ and that $f$ has dense image. *Hint:* A nonzero polynomial has finitely many roots.
7. (C) Let $Z \subseteq X$ be closed. Show that $V(I_Z)$ is reduced, and that $I \leq I_Z$ for each ideal sheaf $I$ with support $Z$. *Hint:* $I_Z(U)$ is a radical ideal, and use the Galois connection.

### Notes and history

Quasi-coherent sheaves and the sheaf $\widetilde{M}$ come from Serre's FAC (1955), for varieties. Grothendieck extended them to schemes in EGA I (1960), with closed subschemes and the scheme-theoretic image. Hartshorne (1977) treats them in Section II.5. The Stacks project defines quasi-coherence by local presentations, as Mathlib does.

The Mathlib Author of `AlgebraicGeometry.IdealSheaf.Basic`, `.Functorial` and `.Subscheme` is Andrew Yang. The Mathlib Authors of `.IrreducibleComponent` are Thomas Browning and Andrew Yang. The Mathlib Author of `AlgebraicGeometry.Modules.Presheaf` is Joël Riou, and the Mathlib Authors of `.Sheaf` are Joël Riou and Andrew Yang. The Mathlib Authors of `AlgebraicGeometry.Modules.Tilde` are Kevin Buzzard, Johan Commelin, Amelia Livingston, Sophie Morel, Jujian Zhang, Weihong Xu, Andrew Yang and Brian Nugent.

### Reference

<?reference?>
