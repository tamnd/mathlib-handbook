---
title: The category of modules
kind: theory
modules:
  - Mathlib.Algebra.Category.ModuleCat.Basic
  - Mathlib.Algebra.Category.ModuleCat.Abelian
  - Mathlib.Algebra.Category.ModuleCat.Adjunctions
  - Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
  - Mathlib.Algebra.Category.ModuleCat.Projective
  - Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
  - Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
explains:
  E3: [ModuleCat.abelian, ModuleCat.normalMono, ModuleCat.normalEpi, ModuleCat.adj, ModuleCat.extendRestrictScalarsAdj, ModuleCat.restrictCoextendScalarsAdj, ModuleCat.enoughProjectives, ModuleCat.enoughInjectives, ModuleCat.monoidalCategory]
  E2: [ModuleCat, ModuleCat.of, ModuleCat.ofHom, ModuleCat.Hom, ModuleCat.Hom.hom, ModuleCat.hom_ext, ModuleCat.homEquiv, ModuleCat.isoMk, LinearEquiv.toModuleIso, CategoryTheory.Iso.toLinearEquiv, ModuleCat.instPreadditive, ModuleCat.instLinear, ModuleCat.instHasZeroObject, ModuleCat.homLinearEquiv, ModuleCat.endRingEquiv, ModuleCat.smulNatTrans, ModuleCat.free, ModuleCat.freeMk, ModuleCat.freeDesc, ModuleCat.freeHomEquiv, ModuleCat.restrictScalars, ModuleCat.extendScalars, ModuleCat.coextendScalars, ModuleCat.restrictScalarsEquivalenceOfRingEquiv, ModuleCat.projective_of_free, ModuleCat.projective_of_module_projective, instEnoughInjectivesModuleCatOfSmall, instEnoughInjectivesModuleCatInt, ModuleCat.MonoidalCategory.tensorLift, ModuleCat.instMonoidalPreadditive, ModuleCat.instMonoidalLinear]
  E1: auto
families: []
requires: [V24.C05, V24.C07, V24.C08, V25.C02, V07.C01, V08.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The category of modules

### Overview

For a ring $R$, the category $\mathrm{Mod}_R$ of left $R$-modules is the model of an abelian category. Each construction of the earlier chapters (homology, resolutions, Ext and Tor, the derived category) was first made in $\mathrm{Mod}_R$, and the examples of this volume compute there. This section collects the structure of $\mathrm{Mod}_R$ that homological algebra uses: the abelian structure, the free module adjunction, the three functors of change of rings and their two adjunctions, the existence of enough projectives and enough injectives, and the tensor product as a monoidal structure.

Volume 24, Chapter 8 states that $\mathrm{Mod}_R$ is abelian. Here the proof is complete. The proof of enough injectives is the most interesting one: it reduces the problem for $R$-modules to the problem for abelian groups through the coextension of scalars, an adjoint functor argument that Grothendieck used in his Tohoku paper. In the text $g \circ f$ is the composite of the textbook, and Mathlib writes `f ≫ g`. All rings have a unit, and all modules are left modules.

### Definitions

**Definition (Category of modules).** The category $\mathrm{Mod}_R$ has as objects the left $R$-modules and as morphisms the $R$-linear maps. The set $\mathrm{Hom}_R(M, N)$ is an abelian group under pointwise addition, and composition is bilinear: $(g + g') \circ f = g \circ f + g' \circ f$ and $g \circ (f + f') = g \circ f + g \circ f'$. So $\mathrm{Mod}_R$ is preadditive (Volume 25, Chapter 1). If $R$ is commutative, $\mathrm{Hom}_R(M, N)$ is an $R$-module, with $(rf)(m) = r f(m)$, and $\mathrm{Mod}_R$ is $R$-linear.

**Definition (Free module).** For a set $X$, the free module $R^{(X)}$ is the set of finitely supported functions $X \to R$. For $x \in X$, the basis element $e_x$ is the function with value $1$ at $x$ and $0$ elsewhere.

**Definition (Change of rings).** Let $\varphi \colon R \to S$ be a ring homomorphism.

- Restriction of scalars $\varphi^* \colon \mathrm{Mod}_S \to \mathrm{Mod}_R$ gives an $S$-module $N$ the action $r \cdot n = \varphi(r) n$.
- Extension of scalars $\varphi_! \colon \mathrm{Mod}_R \to \mathrm{Mod}_S$ sends $M$ to $S \otimes_R M$, where $S$ is a right $R$-module through $\varphi$, and $S$ acts on the left factor. This functor needs $R$ and $S$ commutative in Mathlib.
- Coextension of scalars $\varphi_* \colon \mathrm{Mod}_R \to \mathrm{Mod}_S$ sends $M$ to $\mathrm{Hom}_R(S, M)$, where $S$ is a left $R$-module through $\varphi$, with the action $(s \cdot f)(t) = f(ts)$.

**Definition (Projective and injective module).** An $R$-module $P$ is projective if for each surjection $g \colon M \to N$ and each map $f \colon P \to N$ there is $h \colon P \to M$ with $g \circ h = f$. A module $I$ is injective if for each injection $i \colon M \to N$ and each $f \colon M \to I$ there is $h \colon N \to I$ with $h \circ i = f$. A category has enough projectives if each object is a quotient of a projective object, and enough injectives if each object is a subobject of an injective object (Volume 25, Chapter 2).

**Definition (Monoidal structure).** For $R$ commutative, the tensor product $M \otimes_R N$ with unit $R$ makes $\mathrm{Mod}_R$ a monoidal category (Volume 24, Chapter 7). The associator sends $(m \otimes n) \otimes p$ to $m \otimes (n \otimes p)$, and the unitors send $r \otimes m$ and $m \otimes r$ to $rm$.

### Theorems and proofs

**Lemma (Monomorphisms and epimorphisms of modules).** An $R$-linear map $f \colon M \to N$ is a monomorphism of $\mathrm{Mod}_R$ if and only if it is injective, and an epimorphism if and only if it is surjective.

*Proof.* If $f$ is injective and $f \circ g = f \circ h$, then $g(x)$ and $h(x)$ have the same image, so $g = h$. Conversely, let $f$ be a monomorphism, let $\iota \colon \ker f \to M$ be the inclusion and $0 \colon \ker f \to M$ the zero map. Then $f \circ \iota = 0 = f \circ 0$, so $\iota = 0$ and $\ker f = 0$. The argument for epimorphisms is dual. A surjective $f$ is an epimorphism. If $f$ is an epimorphism, let $\pi \colon N \to N/f(M)$ be the quotient map. Then $\pi \circ f = 0 = 0 \circ f$, so $\pi = 0$ and $f(M) = N$. $\square$

**Theorem (Modules form an abelian category).** The category $\mathrm{Mod}_R$ is abelian.

*Proof.* The zero module is a zero object. The direct sum $M \oplus N$, with the inclusions and the projections, is a biproduct, because $\iota_1 \pi_1 + \iota_2 \pi_2 = \mathrm{id}$ and $\pi_i \iota_j = \delta_{ij}$. The kernel of $f \colon M \to N$ is the submodule $\ker f$ with its inclusion: a map $g \colon X \to M$ with $f \circ g = 0$ takes values in $\ker f$ and factors uniquely through it. The cokernel of $f$ is $N/f(M)$ with the quotient map: a map $h \colon N \to Y$ with $h \circ f = 0$ vanishes on $f(M)$ and factors uniquely through the quotient.

It remains to show that each monomorphism is a kernel and each epimorphism is a cokernel. Let $f \colon M \to N$ be a monomorphism. By the lemma it is injective. Let $\pi \colon N \to N/f(M)$. Then $\pi \circ f = 0$. Let $g \colon X \to N$ satisfy $\pi \circ g = 0$. Then $g(X) \subseteq f(M)$. Because $f$ is injective, $f$ is a bijection $M \to f(M)$ with inverse $f^{-1}$, which is linear. So $g = f \circ (f^{-1} \circ g)$, and the factorization is unique because $f$ is a monomorphism. So $f$ is a kernel of $\pi$.

Let $f \colon M \to N$ be an epimorphism. By the lemma it is surjective. Let $\iota \colon \ker f \to M$. Then $f \circ \iota = 0$. Let $h \colon M \to Y$ satisfy $h \circ \iota = 0$, so $\ker f \subseteq \ker h$. By the first isomorphism theorem $f$ induces a linear bijection $\bar f \colon M/\ker f \to N$, and $h$ induces $\bar h \colon M/\ker f \to Y$. Then $k = \bar h \circ \bar f^{-1}$ satisfies $k \circ f = h$, and it is unique because $f$ is an epimorphism. So $f$ is a cokernel of $\iota$. $\square$

**Proposition (Free modules).** The functor $X \mapsto R^{(X)}$ is left adjoint to the forgetful functor $\mathrm{Mod}_R \to \mathbf{Set}$. A free module is projective, and $\mathrm{Mod}_R$ has enough projectives.

*Proof.* A map of sets $\phi \colon X \to M$ extends to the unique linear map $\tilde\phi(\sum a_x e_x) = \sum a_x \phi(x)$, and restriction to the basis gives the inverse. Both directions are natural, so the bijection $\mathrm{Hom}_R(R^{(X)}, M) \cong \mathrm{Hom}_{\mathbf{Set}}(X, M)$ is an adjunction. Let $g \colon M \to N$ be surjective and $f \colon R^{(X)} \to N$ linear. For each $x$ choose $m_x \in M$ with $g(m_x) = f(e_x)$. The linear map $h$ with $h(e_x) = m_x$ satisfies $g \circ h = f$ on the basis, hence everywhere. So $R^{(X)}$ is projective. Finally, for any module $M$, take $X = M$ as a set. The map $R^{(M)} \to M$, $e_m \mapsto m$, is surjective. $\square$

**Theorem (Change of rings adjunctions).** For $\varphi \colon R \to S$, there are adjunctions $\varphi_! \dashv \varphi^* \dashv \varphi_*$. Here $\varphi_!$ needs commutative rings.

*Proof.* For $\varphi_! \dashv \varphi^*$: an $S$-linear map $u \colon S \otimes_R M \to N$ gives the $R$-linear map $m \mapsto u(1 \otimes m)$, from $M$ to $\varphi^* N$. Conversely, an $R$-linear $v \colon M \to \varphi^* N$ gives $s \otimes m \mapsto s\, v(m)$. This is well defined because $(s, m) \mapsto s v(m)$ is $R$-balanced: $s\varphi(r) v(m) = s v(rm)$. The two constructions are inverse: $s \otimes m = s(1 \otimes m)$ shows that $u$ is determined by its values on $1 \otimes m$.

For $\varphi^* \dashv \varphi_*$: an $R$-linear map $v \colon \varphi^* N \to M$ gives the $S$-linear map $\hat v \colon N \to \mathrm{Hom}_R(S, M)$, $\hat v(n)(t) = v(tn)$. It is $S$-linear: $\hat v(sn)(t) = v(tsn) = \hat v(n)(ts) = (s \cdot \hat v(n))(t)$. Conversely, an $S$-linear $w \colon N \to \mathrm{Hom}_R(S, M)$ gives $n \mapsto w(n)(1)$. These are inverse, because $w(n)(t) = (t \cdot w(n))(1) = w(tn)(1)$. Naturality is a direct check in each case. $\square$

**Theorem (Enough injectives).** The category $\mathrm{Mod}_R$ has enough injectives.

*Proof.* Step 1: abelian groups. A divisible abelian group is injective by Baer's criterion: to extend a map from an ideal $n\mathbb{Z}$ of $\mathbb{Z}$, send $1$ to an $n$-th root of the image of $n$. The group $\mathbb{Q}/\mathbb{Z}$ is divisible. For an abelian group $A$ and $a \neq 0$, there is a map $\langle a \rangle \to \mathbb{Q}/\mathbb{Z}$ that does not vanish at $a$, and it extends to $A$. So the map $A \to \prod_{\mathrm{Hom}(A, \mathbb{Q}/\mathbb{Z})} \mathbb{Q}/\mathbb{Z}$ is injective, and its target is a product of injectives, hence injective. So $\mathrm{Mod}_{\mathbb{Z}}$ has enough injectives.

Step 2: a right adjoint of an exact functor preserves injectives. Let $\varphi \colon \mathbb{Z} \to R$ be the unique ring map. Restriction $\varphi^*$ is exact, because it does not change the underlying groups. Let $I$ be an injective abelian group. A diagram $i \colon M \hookrightarrow N$, $f \colon M \to \varphi_* I$ of $R$-modules corresponds by the adjunction to $\varphi^* i \colon \varphi^* M \hookrightarrow \varphi^* N$ and $f^\flat \colon \varphi^* M \to I$. The map $\varphi^* i$ is still injective, so $f^\flat$ extends to $h^\flat \colon \varphi^* N \to I$. Its adjoint $h \colon N \to \varphi_* I$ extends $f$ by naturality of the adjunction. So $\varphi_* I = \mathrm{Hom}_{\mathbb{Z}}(R, I)$ is an injective $R$-module.

Step 3: embedding. Let $M$ be an $R$-module, and choose an injective map of groups $j \colon M \to I$ with $I$ injective, by Step 1. Its adjoint $\hat j \colon M \to \mathrm{Hom}_{\mathbb{Z}}(R, I)$, $\hat j(m)(r) = j(rm)$, is $R$-linear. It is injective: if $\hat j(m) = 0$ then $j(m) = \hat j(m)(1) = 0$, so $m = 0$. So $M$ embeds in an injective $R$-module. $\square$

### Examples

**Example (Hom groups).** In $\mathrm{Mod}_{\mathbb{Z}}$, a map $\mathbb{Z}/4 \to \mathbb{Z}/6$ is determined by the image $a$ of $1$, subject to $4a = 0$ in $\mathbb{Z}/6$. The solutions are $a = 0$ and $a = 3$. So $\mathrm{Hom}(\mathbb{Z}/4, \mathbb{Z}/6) \cong \mathbb{Z}/2 = \mathbb{Z}/\gcd(4,6)$.

**Example (Extension and coextension can kill a module).** Let $\varphi \colon \mathbb{Z} \to \mathbb{Q}$. Then $\varphi_!(\mathbb{Z}/n) = \mathbb{Q} \otimes \mathbb{Z}/n = 0$, because $q \otimes 1 = (q/n) \otimes n = 0$. Also $\varphi_*(\mathbb{Z}) = \mathrm{Hom}_{\mathbb{Z}}(\mathbb{Q}, \mathbb{Z}) = 0$, because the image of a divisible group in $\mathbb{Z}$ is a divisible subgroup of $\mathbb{Z}$, and the only one is $0$. In contrast, $\varphi_!(\mathbb{Z}) = \mathbb{Q}$.

**Example (Projective but not free).** Over $R = \mathbb{Z}/6$, the module $P = \mathbb{Z}/2$ is projective, because $\mathbb{Z}/6 \cong \mathbb{Z}/2 \times \mathbb{Z}/3$ and a direct summand of a free module is projective. It is not free: a free $\mathbb{Z}/6$-module has $6^k$ elements, and $P$ has $2$.

**Example (Injective embeddings over the integers).** The group $\mathbb{Z}$ is not injective: the map $2\mathbb{Z} \to \mathbb{Z}$, $2 \mapsto 1$, has no extension to $\mathbb{Z} \to \mathbb{Z}$, since $1 = 2k$ has no solution. The inclusion $\mathbb{Z} \hookrightarrow \mathbb{Q}$ embeds it in a divisible, so injective, group. The quotient $\mathbb{Q}/\mathbb{Z}$ is again divisible, so $0 \to \mathbb{Z} \to \mathbb{Q} \to \mathbb{Q}/\mathbb{Z} \to 0$ is an injective resolution of length $1$. This is the resolution that computes $\mathrm{Ext}^1(\mathbb{Z}/n, \mathbb{Z}) \cong \mathbb{Z}/n$ in Chapter 4.

**Example (Tensor products of cyclic groups).** In $\mathrm{Mod}_{\mathbb{Z}}$, $\mathbb{Z}/m \otimes \mathbb{Z}/n \cong \mathbb{Z}/\gcd(m,n)$. The functor $- \otimes \mathbb{Z}/n$ is right exact, so applying it to $\mathbb{Z} \xrightarrow{m} \mathbb{Z} \to \mathbb{Z}/m \to 0$ gives $\mathbb{Z}/n \xrightarrow{m} \mathbb{Z}/n \to \mathbb{Z}/m \otimes \mathbb{Z}/n \to 0$. The cokernel of multiplication by $m$ on $\mathbb{Z}/n$ is $\mathbb{Z}/\gcd(m,n)$. For example $\mathbb{Z}/4 \otimes \mathbb{Z}/6 \cong \mathbb{Z}/2$.

### The library around it

::: mathlib
`ModuleCat` · `Mathlib.Algebra.Category.ModuleCat.Basic`

`ModuleCat R` is a structure with a type `carrier` and instances of `AddCommGroup` and `Module R`. `ModuleCat.of R M` bundles a module, and a morphism is a term of `ModuleCat.Hom`, which wraps a linear map. One passes between morphisms and linear maps with `ModuleCat.ofHom f` and `f.hom`, and `ModuleCat.homEquiv` is the bijection. `ModuleCat.hom_ext` reduces equality of morphisms to equality of linear maps. `LinearEquiv.toModuleIso` and `CategoryTheory.Iso.toLinearEquiv` translate between linear equivalences and isomorphisms. The instances `ModuleCat.instPreadditive` and `ModuleCat.instLinear` give the additive and linear structure. `ModuleCat.endRingEquiv` identifies the endomorphisms of an object with the ring `Module.End R M`.

<?decl ModuleCat?>
:::

::: mathlib
`ModuleCat.abelian` · `Mathlib.Algebra.Category.ModuleCat.Abelian`

The abelian instance. Its proof follows the theorem above: `ModuleCat.normalMono` shows that a monomorphism is the kernel of the quotient map by its range, and `ModuleCat.normalEpi` shows that an epimorphism is the cokernel of the inclusion of its kernel, by the first isomorphism theorem. The lemma that monomorphisms are injective is `ModuleCat.mono_iff_injective` in `Mathlib.Algebra.Category.ModuleCat.EpiMono`.

<?decl ModuleCat.abelian?>
:::

::: mathlib
`ModuleCat.adj` · `Mathlib.Algebra.Category.ModuleCat.Adjunctions`

`ModuleCat.adj R : ModuleCat.free R ⊣ forget (ModuleCat R)`. The free module on `X` is `X →₀ R`, with `ModuleCat.freeMk x` the basis element and `ModuleCat.freeDesc f` the extension of a map of types. The file also makes `ModuleCat.free R` a monoidal functor from types with the cartesian product to modules with the tensor product.

<?decl ModuleCat.adj?>
:::

::: mathlib
`ModuleCat.restrictCoextendScalarsAdj` · `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`

`ModuleCat.restrictScalars f`, `ModuleCat.extendScalars f` and `ModuleCat.coextendScalars f` are the three functors for a ring map `f`. `ModuleCat.extendRestrictScalarsAdj f : extendScalars f ⊣ restrictScalars f` (for commutative rings) and `ModuleCat.restrictCoextendScalarsAdj f : restrictScalars f ⊣ coextendScalars f` are the two adjunctions. For a ring isomorphism, `ModuleCat.restrictScalarsEquivalenceOfRingEquiv` is an equivalence.

<?decl ModuleCat.restrictCoextendScalarsAdj?>
:::

::: mathlib
`ModuleCat.enoughInjectives` · `Mathlib.Algebra.Category.ModuleCat.EnoughInjectives`

The proof in the file follows Steps 2 and 3 above. It starts from the instance for `AddCommGrpCat` in `Mathlib.Algebra.Category.Grp.EnoughInjectives`, transfers it to `ModuleCat ℤ` by the equivalence (`instEnoughInjectivesModuleCatInt`), and then applies `EnoughInjectives.of_adjunction` to `restrictCoextendScalarsAdj (algebraMap ℤ R)`. The general instance `instEnoughInjectivesModuleCatOfSmall` handles a ring in a larger universe. In `Mathlib.Algebra.Category.ModuleCat.Projective`, `ModuleCat.enoughProjectives` uses the free module `M →₀ R` and `ModuleCat.projective_of_free`.

<?decl ModuleCat.enoughInjectives?>
:::

::: mathlib
`ModuleCat.monoidalCategory` · `Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic`

The monoidal structure of `ModuleCat R` for a commutative ring `R`, with `M ⊗ N` the tensor product `TensorProduct R M N` and unit `R`. `ModuleCat.MonoidalCategory.tensorLift` builds a map out of a tensor product from a bilinear map. The instances `ModuleCat.instMonoidalPreadditive` and `ModuleCat.instMonoidalLinear` say that the tensor product is additive and linear in each variable. The braiding and the closed structure are in the files `Monoidal.Symmetric` and `Monoidal.Closed`.

<?decl ModuleCat.monoidalCategory?>
:::

Common errors of a learner: The first error is to apply a `LinearMap` lemma to a morphism `f : M ⟶ N` of `ModuleCat R` directly. The lemma needs `f.hom`, for example `map_add f.hom x y`. The second error is to forget universes: `ModuleCat.{v} R` has carriers in `Type v`, and the results about enough projectives need `Small.{v} R`. The third error is to expect `extendScalars` for noncommutative rings; Mathlib defines it only for commutative rings. The fourth error is to confuse the two adjunctions: restriction is a right adjoint of extension and a left adjoint of coextension, so restriction preserves both limits and colimits. The fifth error is to think that a projective module is free; the example over $\mathbb{Z}/6$ shows otherwise.

### Exercises

1. (A) Compute $\mathrm{Hom}_{\mathbb{Z}}(\mathbb{Z}/12, \mathbb{Z}/18)$. Hint: the answer is $\mathbb{Z}/6$.
2. (A) Show that $\mathbb{Q}$ is not a projective $\mathbb{Z}$-module. Hint: a map $\mathbb{Q} \to \mathbb{Z}^{(X)}$ is zero, because $\mathbb{Z}^{(X)}$ has no nonzero divisible element.
3. (B) For $\varphi \colon \mathbb{Z} \to \mathbb{Z}/n$, describe $\varphi_!(M)$ and $\varphi_*(M)$ for an abelian group $M$. Hint: $M/nM$ and the $n$-torsion $M[n]$.
4. (B) Prove that extension of scalars $\varphi_!$ sends projective modules to projective modules, for any map $\varphi \colon R \to S$ of commutative rings. Hint: the dual of Step 2, with the exact right adjoint $\varphi^*$.
5. (B) Show that restriction of scalars along $\mathbb{Z} \to \mathbb{Z}[x]$ is faithful but not full. Hint: the $\mathbb{Z}$-linear map of $\mathbb{Z}[x]$ that swaps $1$ and $x$ and fixes the other powers of $x$.
6. (C) Prove that $\mathrm{Hom}_{\mathbb{Z}}(R, \mathbb{Q}/\mathbb{Z})$ is an injective cogenerator of $\mathrm{Mod}_R$: each nonzero $M$ has a nonzero map to it. Hint: Step 3 of the proof.
7. (C) Let $R$ be commutative. Show that $\mathrm{Hom}_R(M \otimes_R N, P) \cong \mathrm{Hom}_R(M, \mathrm{Hom}_R(N, P))$, naturally in $M$ and $P$, so that $\mathrm{Mod}_R$ is monoidal closed. Hint: a map out of the tensor product is a bilinear map.

### Notes and history

The systematic treatment of the category of modules with projective and injective objects is due to Cartan and Eilenberg, in *Homological Algebra* (1956). Baer proved the criterion for injectivity that Step 1 uses. Grothendieck, in the Tohoku paper of 1957, isolated the axioms of an abelian category and proved that categories with a generator and exact filtered colimits have enough injectives; the argument by coextension of scalars is a simple case of the adjoint functor method.

The Mathlib files are by these authors, read from their headers: `ModuleCat.Basic` by Robert A. Spencer and Markus Himmel; `ModuleCat.Abelian` by Markus Himmel; `ModuleCat.Adjunctions` by Kim Morrison and Johan Commelin; `ModuleCat.ChangeOfRings` and `ModuleCat.EnoughInjectives` by Jujian Zhang; `ModuleCat.Projective` by Markus Himmel and Kim Morrison; `ModuleCat.Monoidal.Basic` by Kevin Buzzard, Kim Morrison and Jakob von Raumer.

### Reference

<?reference?>
