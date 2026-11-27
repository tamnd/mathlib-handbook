---
title: Categories of monoids, groups and rings
kind: theory
modules:
  - Mathlib.Algebra.Category.MonCat.Basic
  - Mathlib.Algebra.Category.Grp.Basic
  - Mathlib.Algebra.Category.Ring.Basic
  - Mathlib.Algebra.Category.MonCat.Adjunctions
  - Mathlib.Algebra.Category.Grp.Adjunctions
  - Mathlib.Algebra.Category.Grp.EpiMono
  - Mathlib.Algebra.Category.Grp.Abelian
  - Mathlib.Algebra.Category.Ring.Limits
explains:
  E3: [GrpCat.surjective_of_epi, GrpCat.epi_iff_surjective, GrpCat.mono_iff_injective, RingCat.limitConeIsLimit, RingCat.forget_preservesLimits, MonCat.adj, GrpCat.adj, GrpCat.abelianizeAdj, GrpCat.forget₂MonAdj, AddCommGrpCat.instAbelian]
  E2: [MonCat, MonCat.of, MonCat.ofHom, MonCat.Hom, MonCat.Hom.hom, MonCat.hom_ext, MonCat.hom_ofHom, MonCat.coe_comp, GrpCat, CommGrpCat, AddCommGrpCat, Ab, RingCat, CommRingCat, RingCat.ofHom, RingEquiv.toRingCatIso, GrpCat.hasForgetToMonCat, GrpCat.fullyFaithfulForget₂ToMonCat, RingCat.sectionsSubring, RingCat.limitCone, RingCat.hasLimits, CommRingCat.hasLimits, CommRingCat.limitConeIsLimit, MonCat.free, MonCat.adjoinOneAdj, GrpCat.free, AddCommGrpCat.free, AddCommGrpCat.adj, GrpCat.abelianize, MonCat.units, AddCommGrpCat.epi_iff_surjective, AddCommGrpCat.normalMono, GrpCat.SurjectiveOfEpiAuxs.agree, GrpCat.SurjectiveOfEpiAuxs.g_ne_h]
  E1: auto
families: []
requires: [V24.C01, V24.C04, V24.C05, V24.C08, V05.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Categories of monoids, groups and rings

### Overview

Homological algebra takes place in categories whose objects are algebraic structures: abelian groups, modules, representations of a group. The earlier chapters of this volume work in an arbitrary abelian category. This chapter returns to the concrete categories, because the examples, the resolutions and the group cohomology of Chapter 8 live there. This first section treats the categories of monoids, groups, abelian groups and rings. It describes how Mathlib bundles an algebraic structure into an object of a category, how it wraps a homomorphism into a morphism, and which functors connect these categories.

The section proves three facts that a student uses all the time and that Volume 24 states without proof. First, a morphism of groups is an epimorphism if and only if it is surjective. Second, limits of rings are computed on the underlying sets: the limit of a diagram of rings is the set of compatible families with the pointwise operations. Third, the category of abelian groups is abelian, which is the base case of all of homological algebra. Counterexamples show that epimorphisms of monoids and rings need not be surjective and that colimits of groups are not computed in sets.

In the text $g \circ f$ is the composite of the textbook, and Mathlib writes `f ≫ g`. Volume 24, Chapter 1 proves that a monomorphism of groups is injective; Chapter 4 of that volume gives limits and colimits, and Chapter 5 gives adjunctions.

### Definitions

**Definition (Category of monoids).** The category $\mathbf{Mon}$ has as objects the monoids $M$ (a set with an associative operation and a unit) and as morphisms the monoid homomorphisms $f \colon M \to N$, that is, maps with $f(xy) = f(x)f(y)$ and $f(1) = 1$. Composition is composition of maps. The categories $\mathbf{Grp}$ of groups, $\mathbf{Ab}$ of abelian groups, $\mathbf{Ring}$ of rings with unit and $\mathbf{CRing}$ of commutative rings are defined in the same way, with group homomorphisms and unital ring homomorphisms as morphisms.

A group homomorphism preserves the unit and the inverse automatically: $f(1) = f(1 \cdot 1) = f(1)f(1)$ gives $f(1) = 1$ after cancellation, and $f(x)f(x^{-1}) = f(1) = 1$ gives $f(x^{-1}) = f(x)^{-1}$. So $\mathbf{Grp}$ is a full subcategory of $\mathbf{Mon}$. For rings the unit condition is a real condition: the map $\mathbb{Z} \to \mathbb{Z} \times \mathbb{Z}$, $n \mapsto (n, 0)$, preserves sums and products, but it does not send $1$ to $(1,1)$. It is not a morphism of $\mathbf{Ring}$.

**Definition (Forgetful functor).** The forgetful functor $U \colon \mathbf{Mon} \to \mathbf{Set}$ sends a monoid to its underlying set and a homomorphism to its underlying map. There are also forgetful functors between the algebraic categories: $\mathbf{Ab} \to \mathbf{Grp} \to \mathbf{Mon}$, $\mathbf{CRing} \to \mathbf{Ring}$, and $\mathbf{Ring} \to \mathbf{Ab}$, which keeps only the addition.

Each forgetful functor to $\mathbf{Set}$ is faithful, so these are concrete categories. The functor $\mathbf{Grp} \to \mathbf{Mon}$ is also full, by the remark above. The functor $\mathbf{Ring} \to \mathbf{Ab}$ is faithful but not full.

**Definition (Free monoid, free group, abelianization).** For a set $S$, the free monoid $F_{\mathrm{Mon}}(S)$ is the set of finite words in $S$ with concatenation. The free group $F(S)$ is the set of reduced words in $S \cup S^{-1}$. The free abelian group $\mathbb{Z}^{(S)}$ is the set of finitely supported functions $S \to \mathbb{Z}$. For a group $G$, the abelianization is $G^{\mathrm{ab}} = G/[G,G]$, where $[G,G]$ is the subgroup generated by the commutators $xyx^{-1}y^{-1}$. For a monoid $M$, the group of units $M^\times$ is the set of invertible elements.

**Definition (Sections of a diagram).** Let $J$ be a small category and $F \colon J \to \mathbf{Ring}$ a functor. The set of sections of $F$ is
$$\Gamma(F) = \Big\{ (x_j)_{j} \in \prod_{j \in J} F(j) \;:\; F(u)(x_j) = x_{j'} \text{ for each } u \colon j \to j' \Big\}.$$
It is the limit of $U \circ F$ in $\mathbf{Set}$, by Volume 24, Chapter 4.

### Theorems and proofs

**Proposition (Free and forgetful adjunctions).** The following functors are left adjoint to the forgetful functors: $S \mapsto F_{\mathrm{Mon}}(S)$ is left adjoint to $U \colon \mathbf{Mon} \to \mathbf{Set}$; $S \mapsto F(S)$ is left adjoint to $U \colon \mathbf{Grp} \to \mathbf{Set}$; $S \mapsto \mathbb{Z}^{(S)}$ is left adjoint to $U \colon \mathbf{Ab} \to \mathbf{Set}$; $G \mapsto G^{\mathrm{ab}}$ is left adjoint to the inclusion $\mathbf{Ab} \to \mathbf{Grp}$. The functor $M \mapsto M^\times$ is right adjoint to the inclusion $\mathbf{Grp} \to \mathbf{Mon}$.

*Proof.* In each case it suffices to give a bijection of hom-sets natural in both variables (Volume 24, Chapter 5). For the free group: a map of sets $\phi \colon S \to U(G)$ extends to a unique homomorphism $\tilde\phi \colon F(S) \to G$, with $\tilde\phi(s_1^{\epsilon_1} \cdots s_n^{\epsilon_n}) = \phi(s_1)^{\epsilon_1} \cdots \phi(s_n)^{\epsilon_n}$. Restriction to the generators gives the inverse map. Naturality in $G$ holds because $h \circ \tilde\phi$ and $\widetilde{h \circ \phi}$ agree on the generators, and naturality in $S$ is the same check. The free monoid and the free abelian group are the same argument with words and with finite sums $\sum n_s s$.

For the abelianization: a homomorphism $f \colon G \to A$ with $A$ abelian sends each commutator to $f(x)f(y)f(x)^{-1}f(y)^{-1} = 1$. So $[G,G] \subseteq \ker f$, and $f$ factors uniquely through $G \to G^{\mathrm{ab}}$. This gives the bijection $\mathrm{Hom}_{\mathbf{Ab}}(G^{\mathrm{ab}}, A) \cong \mathrm{Hom}_{\mathbf{Grp}}(G, A)$, natural in both variables.

For the units: a monoid homomorphism $f \colon G \to M$ from a group sends $x$ to an invertible element, with inverse $f(x^{-1})$. So $f$ factors uniquely through $M^\times \subseteq M$, and $\mathrm{Hom}_{\mathbf{Mon}}(G, M) \cong \mathrm{Hom}_{\mathbf{Grp}}(G, M^\times)$. $\square$

**Theorem (Limits of rings are computed in sets).** Let $F \colon J \to \mathbf{Ring}$ be a functor from a small category. The set $\Gamma(F)$ is a subring of $\prod_j F(j)$. With the projections $\pi_j \colon \Gamma(F) \to F(j)$ it is a limit cone of $F$ in $\mathbf{Ring}$. The forgetful functor $\mathbf{Ring} \to \mathbf{Set}$ preserves limits. The same holds for $\mathbf{CRing}$.

*Proof.* The product ring $\prod_j F(j)$ has the pointwise operations. Each $F(u)$ is a ring homomorphism. If $(x_j)$ and $(y_j)$ are sections, then $F(u)(x_j + y_j) = x_{j'} + y_{j'}$ and $F(u)(x_j y_j) = x_{j'} y_{j'}$, and $F(u)(1) = 1$, $F(u)(-x_j) = -x_{j'}$. So $\Gamma(F)$ contains $1$ and is closed under sums, negatives and products: it is a subring. The projections $\pi_j$ are ring homomorphisms, and $F(u) \circ \pi_j = \pi_{j'}$ by the definition of a section, so they form a cone.

Let $(R, \lambda_j \colon R \to F(j))$ be another cone. Define $\lambda \colon R \to \Gamma(F)$ by $\lambda(r) = (\lambda_j(r))_j$. The value is a section, because $F(u)(\lambda_j(r)) = \lambda_{j'}(r)$. The map $\lambda$ is a ring homomorphism, because each component is one and the operations are pointwise. It satisfies $\pi_j \circ \lambda = \lambda_j$. If $\mu \colon R \to \Gamma(F)$ also satisfies $\pi_j \circ \mu = \lambda_j$ for each $j$, then $\mu(r)$ and $\lambda(r)$ have the same components, so $\mu = \lambda$. So the cone is a limit cone. Its image under the forgetful functor is the cone of sections in $\mathbf{Set}$, which is a limit cone there. A limit cone that maps to a limit cone shows that the functor preserves this limit, and all limits are isomorphic to this one. For $\mathbf{CRing}$ the subring of a product of commutative rings is commutative, and the same argument works. $\square$

**Theorem (Epimorphisms of groups are surjective).** A morphism $f \colon A \to B$ in $\mathbf{Grp}$ is an epimorphism if and only if it is surjective. A morphism of groups is a monomorphism if and only if it is injective.

*Proof.* A surjective homomorphism is an epimorphism: if $g \circ f = h \circ f$ and each $b \in B$ is $f(a)$, then $g(b) = h(b)$. The statement about monomorphisms is in Volume 24, Chapter 1: one tests $f$ against the inclusion of $\ker f$ and the trivial map $\ker f \to A$.

Now let $f$ be an epimorphism, and put $H = f(A)$, a subgroup of $B$. Suppose that $H \neq B$. Let $X = B/H$ be the set of left cosets $bH$, and let $X' = X \sqcup \{\infty\}$ be $X$ with one more point. Let $\mathrm{Sym}(X')$ be the group of bijections of $X'$. Define $g \colon B \to \mathrm{Sym}(X')$ by
$$g(b)(cH) = bcH, \qquad g(b)(\infty) = \infty.$$
This is a homomorphism, because $g(bb')(cH) = bb'cH = g(b)(g(b')(cH))$. Let $\tau \in \mathrm{Sym}(X')$ be the transposition that exchanges the point $H \in X$ (the trivial coset) with $\infty$ and fixes all other points. Define $h \colon B \to \mathrm{Sym}(X')$ by $h(b) = \tau \, g(b) \, \tau^{-1}$. It is a homomorphism, because conjugation by $\tau$ is an automorphism of $\mathrm{Sym}(X')$.

Step 1: $g \circ f = h \circ f$. Let $a \in A$ and put $x = f(a) \in H$. Then $g(x)$ fixes the coset $H$, because $xH = H$, and it fixes $\infty$. So $g(x)$ permutes the other points among themselves. Compare $h(x)$ and $g(x)$ point by point. At $H$: $\tau^{-1}(H) = \infty$, $g(x)(\infty) = \infty$, $\tau(\infty) = H$, so $h(x)(H) = H = g(x)(H)$. At $\infty$: $\tau^{-1}(\infty) = H$, $g(x)(H) = H$, $\tau(H) = \infty$, so $h(x)(\infty) = \infty = g(x)(\infty)$. At any other point $y$: $\tau^{-1}(y) = y$, and $g(x)(y)$ is again a point other than $H$ and $\infty$, so $\tau$ fixes it and $h(x)(y) = g(x)(y)$. So $h(x) = g(x)$.

Step 2: $g \neq h$. Choose $b \in B \setminus H$. Then $g(b)(H) = bH \neq H$, because $b \notin H$. But $h(b)(H) = \tau(g(b)(\tau^{-1}(H))) = \tau(g(b)(\infty)) = \tau(\infty) = H$. So $g(b) \neq h(b)$.

Steps 1 and 2 contradict the assumption that $f$ is an epimorphism. So $H = B$, and $f$ is surjective. $\square$

For abelian groups there is a shorter proof: compare the quotient map $B \to B/f(A)$ with the zero map. Both vanish on $f(A)$, so they are equal when $f$ is an epimorphism, and $B/f(A) = 0$. This proof fails in $\mathbf{Grp}$, because $f(A)$ need not be normal, and the quotient set $B/f(A)$ is then not a group. The extra point $\infty$ in the proof above replaces the missing quotient group.

**Theorem (Abelian groups form an abelian category).** The category $\mathbf{Ab}$ is abelian.

*Proof.* An abelian group $A$ has exactly one structure of $\mathbb{Z}$-module, with $n \cdot a = a + \cdots + a$ for $n > 0$, and each group homomorphism is $\mathbb{Z}$-linear. So the forgetful functor $\mathrm{Mod}_{\mathbb{Z}} \to \mathbf{Ab}$ is an equivalence of categories. The category $\mathrm{Mod}_{\mathbb{Z}}$ is abelian (Volume 24, Chapter 8, and Section 2 of this chapter gives the proof for any ring). Each part of the definition of an abelian category transfers along an equivalence: the zero object, the biproducts, the additive structure on hom-sets, the kernels and cokernels, and the property that each monomorphism is the kernel of its cokernel and each epimorphism is the cokernel of its kernel. So $\mathbf{Ab}$ is abelian. In concrete terms, the kernel of $f \colon A \to B$ is $\{a : f(a) = 0\}$, the cokernel is $B/f(A)$, and a monomorphism $f$ is the kernel of $B \to B/f(A)$. $\square$

### Examples

**Counterexample (An epimorphism of monoids that is not surjective).** The inclusion $i \colon (\mathbb{N}, +) \to (\mathbb{Z}, +)$ is an epimorphism in $\mathbf{Mon}$. Let $g, h \colon \mathbb{Z} \to M$ be monoid homomorphisms that agree on $\mathbb{N}$. Write the operation of $M$ as multiplication. Then
$$g(-1) = g(-1)\, h(0) = g(-1)\, h(1)\, h(-1) = g(-1)\, g(1)\, h(-1) = g(0)\, h(-1) = h(-1).$$
So $g$ and $h$ agree on $-1$, hence on all of $\mathbb{Z}$. The map $i$ is not surjective. The group proof above fails at the start: $(\mathbb{N}, +)$ is not a group, so $\mathbf{Grp}$ does not see it.

**Counterexample (An epimorphism of rings that is not surjective).** The inclusion $\mathbb{Z} \to \mathbb{Q}$ is an epimorphism in $\mathbf{Ring}$. Let $g, h \colon \mathbb{Q} \to R$ agree on $\mathbb{Z}$, and let $n \geq 1$. Then $g(1/n) = g(1/n) h(n) h(1/n) = g(1/n) g(n) h(1/n) = g(1) h(1/n) = h(1/n)$. So $g$ and $h$ agree on each $m/n = m \cdot (1/n)$. The same argument shows that each localization $R \to S^{-1}R$ is an epimorphism of rings.

**Example (Colimits of groups are not computed in sets).** The coproduct of two copies of $\mathbb{Z}/2$ in $\mathbf{Grp}$ is the free product $\mathbb{Z}/2 * \mathbb{Z}/2$, the infinite dihedral group. It is generated by two elements $s, t$ of order $2$, and the elements $(st)^n$ for $n \in \mathbb{Z}$ are pairwise distinct. So the coproduct is infinite, while the disjoint union of the underlying sets has $4$ elements. In $\mathbf{Ab}$ the coproduct is the direct sum $\mathbb{Z}/2 \oplus \mathbb{Z}/2$, with $4$ elements, but it is still not the disjoint union. In $\mathbf{CRing}$ the coproduct of $A$ and $B$ is $A \otimes_{\mathbb{Z}} B$; for example $\mathbb{Z}[x] \otimes \mathbb{Z}[y] \cong \mathbb{Z}[x, y]$. The forgetful functors to $\mathbf{Set}$ preserve limits, as they must, being right adjoints, but they do not preserve coproducts.

**Example (Counting homomorphisms with the adjunction).** The free group $F(\{x, y\})$ on two letters has exactly $|S_3|^2 = 36$ homomorphisms to the symmetric group $S_3$: by the adjunction they correspond to maps of sets $\{x, y\} \to S_3$. The abelianization of $S_3$ is $\mathbb{Z}/2$, because $[S_3, S_3] = A_3$ has index $2$. So $\mathrm{Hom}_{\mathbf{Grp}}(S_3, \mathbb{Z}/3) \cong \mathrm{Hom}_{\mathbf{Ab}}(\mathbb{Z}/2, \mathbb{Z}/3) = 0$: the only homomorphism $S_3 \to \mathbb{Z}/3$ is trivial.

**Example (A limit of rings).** The $p$-adic integers are the limit of the diagram $\cdots \to \mathbb{Z}/p^3 \to \mathbb{Z}/p^2 \to \mathbb{Z}/p$ of reduction maps. By the theorem, $\mathbb{Z}_p$ is the ring of sequences $(x_n)$ with $x_n \in \mathbb{Z}/p^n$ and $x_{n+1} \equiv x_n \pmod{p^n}$, with componentwise operations. For $p = 5$, the sequence $(2, 7, 57, \dots)$ with $x_n^2 = -1$ in $\mathbb{Z}/5^n$ is a square root of $-1$ in $\mathbb{Z}_5$: $2^2 = 4 \equiv -1 \pmod 5$, $7^2 = 49 \equiv -1 \pmod{25}$, and $57^2 = 3249 = 26 \cdot 125 - 1 \equiv -1 \pmod{125}$.

### The library around it

::: mathlib
`MonCat` · `Mathlib.Algebra.Category.MonCat.Basic`

The category of monoids is a structure with a field `carrier` and an instance field `str : Monoid carrier`. The function `MonCat.of M` bundles a type with a monoid instance. A morphism `M ⟶ N` is a term of the structure `MonCat.Hom`, which wraps a `MonoidHom`. The wrapper is deliberate: if a morphism were literally a `MonoidHom`, Lean would see two different compositions (`≫` and `MonoidHom.comp`) on the same type and could confuse their simp lemmas. One passes between the two with `MonCat.ofHom f` and `f.hom`, and `MonCat.hom_ext` reduces an equation of morphisms to an equation of homomorphisms. `MonCat.coe_comp` states that the map of `f ≫ g` is `g ∘ f`. The categories `GrpCat`, `CommGrpCat`, `AddCommGrpCat` (with the abbreviation `Ab`), `RingCat` and `CommRingCat` follow the same pattern, with `RingCat.ofHom` and `RingEquiv.toRingCatIso`.

<?decl MonCat?>
:::

::: mathlib
`GrpCat.epi_iff_surjective` · `Mathlib.Algebra.Category.Grp.EpiMono`

This is the theorem above. The proof in the file follows the permutation argument. It lives in the namespace `GrpCat.SurjectiveOfEpiAuxs`, which defines the set of cosets with an extra point, the transposition `tau`, the two actions `g` and `h`, and proves `agree` (the range of $f$ is the set where $g$ and $h$ agree) and `g_ne_h`. The main step is `GrpCat.surjective_of_epi`. The file also proves `GrpCat.mono_iff_injective` and the abelian version `AddCommGrpCat.epi_iff_surjective`, with the short proof by the quotient map.

<?decl GrpCat.epi_iff_surjective?>
:::

::: mathlib
`MonCat.adj` · `Mathlib.Algebra.Category.MonCat.Adjunctions`

`MonCat.adj : MonCat.free ⊣ forget MonCat` is the free monoid adjunction, with `FreeMonoid` as the free object. The file also has `MonCat.adjoinOneAdj`, which adjoins a unit to a semigroup. The file `Mathlib.Algebra.Category.Grp.Adjunctions` has `GrpCat.adj` for the free group, `AddCommGrpCat.adj` for `FreeAddCommGroup`, `GrpCat.abelianizeAdj : GrpCat.abelianize ⊣ forget₂ CommGrpCat GrpCat` and `GrpCat.forget₂MonAdj : forget₂ GrpCat MonCat ⊣ MonCat.units`.

<?decl MonCat.adj?>
:::

::: mathlib
`RingCat.limitConeIsLimit` · `Mathlib.Algebra.Category.Ring.Limits`

The file builds `RingCat.sectionsSubring F`, the subring of sections of the underlying functor, and the cone `RingCat.limitCone F` on it. `RingCat.limitConeIsLimit` proves that it is a limit cone, and the instances `RingCat.hasLimits` and `RingCat.forget_preservesLimits` follow. The proof in the file lifts the limit in `Type` along the forgetful functor, which is the argument above. `CommRingCat.limitConeIsLimit` and `CommRingCat.hasLimits` are the commutative versions.

<?decl RingCat.limitConeIsLimit?>
:::

::: mathlib
`AddCommGrpCat.instAbelian` · `Mathlib.Algebra.Category.Grp.Abelian`

The instance that `AddCommGrpCat` is abelian. The file proves it as above: `AddCommGrpCat.normalMono` and `AddCommGrpCat.normalEpi` transfer the normal monomorphism and epimorphism structure from `ModuleCat ℤ` along the equivalence `forget₂ (ModuleCat ℤ) AddCommGrpCat`. All the homological algebra of the earlier chapters applies to `AddCommGrpCat` through this instance.

<?decl AddCommGrpCat.instAbelian?>
:::

Common errors of a learner: The first error is to write `f x` for a morphism `f : M ⟶ N` in `MonCat` and to expect a `MonoidHom` lemma to apply. The lemma needs `f.hom`, as in `map_mul f.hom x y`. The second error is to compose in the wrong order: `f ≫ g` applies `f` first, so `(f ≫ g).hom x = g.hom (f.hom x)`. The third error is to assume that an epimorphism in any algebraic category is surjective; the examples above show that this is false in `MonCat` and `RingCat`. The fourth error is to expect `forget` to preserve coproducts; it preserves only filtered colimits here.

### Exercises

1. (A) Show that the map $\mathbb{Z} \to \mathbb{Z} \times \mathbb{Z}$, $n \mapsto (n, n)$, is a morphism of rings and that $n \mapsto (n, 0)$ is not. Hint: check the unit.
2. (A) Use the adjunction for the free abelian group to count the homomorphisms $\mathbb{Z}^2 \to \mathbb{Z}/6$. Hint: the answer is $36$.
3. (B) Prove that the inclusion $\mathbb{Z} \to \mathbb{Z}[1/2]$ is an epimorphism of rings, by the argument for $\mathbb{Z} \to \mathbb{Q}$. Hint: show $g(1/2^k) = h(1/2^k)$.
4. (B) Let $H = \{e, (12)\} \subset S_3$. Write out the action of $S_3$ on $X' = S_3/H \sqcup \{\infty\}$ and the map $h = \tau g \tau^{-1}$ of the proof. Find an element $b$ with $g(b) \neq h(b)$. Hint: $X'$ has four points; take $b = (13)$.
5. (B) Prove that the forgetful functor $\mathbf{Ring} \to \mathbf{Ab}$ has a left adjoint. Hint: the tensor algebra $\bigoplus_{n \geq 0} A^{\otimes n}$.
6. (C) Prove that the forgetful functor $\mathbf{Grp} \to \mathbf{Set}$ preserves filtered colimits. Hint: on a filtered colimit of sets, define $[x] \cdot [y]$ by choosing an index where both $x$ and $y$ live.

### Notes and history

The idea that groups, rings and modules form categories, with homomorphisms as morphisms, comes from Eilenberg and MacLane, who introduced categories and functors in the 1940s.

The Mathlib files are by these authors, read from their headers: `MonCat.Basic` by Kim Morrison; `Grp.Basic` by Johan Commelin; `Ring.Basic` by Kim Morrison, Johannes Hölzl and Yury Kudryashov; `MonCat.Adjunctions` by Julian Kuelshammer; `Grp.Adjunctions` by Kim Morrison and Johannes Hölzl; `Grp.EpiMono` by Jujian Zhang; `Grp.Abelian` by Markus Himmel; `Ring.Limits` by Kim Morrison.

### Reference

<?reference?>
