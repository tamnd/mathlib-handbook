---
title: Projective and injective resolutions
kind: theory
modules:
  - Mathlib.CategoryTheory.Preadditive.Projective.Resolution
  - Mathlib.CategoryTheory.Preadditive.Injective.Resolution
  - Mathlib.CategoryTheory.Abelian.Projective.Resolution
  - Mathlib.CategoryTheory.Abelian.Injective.Resolution
  - Mathlib.Algebra.Homology.LeftResolution.Basic
  - Mathlib.Algebra.Homology.LeftResolution.Reduced
  - Mathlib.Algebra.Homology.LeftResolution.Transport
explains:
  E3: [CategoryTheory.ProjectiveResolution, CategoryTheory.InjectiveResolution, CategoryTheory.ProjectiveResolution.lift, CategoryTheory.ProjectiveResolution.liftHomotopy, CategoryTheory.ProjectiveResolution.homotopyEquiv, CategoryTheory.projectiveResolutions, CategoryTheory.ProjectiveResolution.of, CategoryTheory.InjectiveResolution.desc, CategoryTheory.InjectiveResolution.descHomotopy, CategoryTheory.InjectiveResolution.homotopyEquiv, CategoryTheory.injectiveResolutions]
  E2: [CategoryTheory.ProjectiveResolution.π, CategoryTheory.ProjectiveResolution.complex, CategoryTheory.HasProjectiveResolution, CategoryTheory.HasProjectiveResolutions, CategoryTheory.ProjectiveResolution.exact_succ, CategoryTheory.ProjectiveResolution.complex_exactAt_succ, CategoryTheory.ProjectiveResolution.π_f_succ, CategoryTheory.ProjectiveResolution.cokernelCofork, CategoryTheory.ProjectiveResolution.isColimitCokernelCofork, CategoryTheory.ProjectiveResolution.self, CategoryTheory.ProjectiveResolution.Hom, CategoryTheory.Functor.mapProjectiveResolution, CategoryTheory.ProjectiveResolution.liftFZero, CategoryTheory.ProjectiveResolution.liftFOne, CategoryTheory.ProjectiveResolution.liftFSucc, CategoryTheory.ProjectiveResolution.lift_commutes, CategoryTheory.ProjectiveResolution.liftHomotopyZero, CategoryTheory.ProjectiveResolution.liftIdHomotopy, CategoryTheory.ProjectiveResolution.liftCompHomotopy, CategoryTheory.ProjectiveResolution.exact₀, CategoryTheory.ProjectiveResolution.iso, CategoryTheory.ProjectiveResolution.ofComplex, CategoryTheory.exact_d_f, CategoryTheory.projectiveResolution, CategoryTheory.InjectiveResolution.ι, CategoryTheory.InjectiveResolution.cocomplex, CategoryTheory.HasInjectiveResolution, CategoryTheory.HasInjectiveResolutions, CategoryTheory.InjectiveResolution.exact_succ, CategoryTheory.InjectiveResolution.isLimitKernelFork, CategoryTheory.InjectiveResolution.self, CategoryTheory.InjectiveResolution.descFZero, CategoryTheory.InjectiveResolution.desc_commutes, CategoryTheory.InjectiveResolution.descHomotopyZero, CategoryTheory.InjectiveResolution.descIdHomotopy, CategoryTheory.InjectiveResolution.descCompHomotopy, CategoryTheory.InjectiveResolution.iso, CategoryTheory.InjectiveResolution.ofCocomplex, CategoryTheory.InjectiveResolution.of, CategoryTheory.InjectivePresentation.shortComplex, CategoryTheory.exact_f_d, CategoryTheory.injectiveResolution]
  E1: auto
families: []
requires: [V24.C08, V25.C02, V26.C01, V26.C02, V26.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Projective and injective resolutions

### Overview

A derived functor applies a functor to a resolution of an object and takes homology. For this to define anything, the resolution must be unique in a suitable sense. A projective resolution of $Z$ is an exact sequence $\cdots \to P_1 \to P_0 \to Z \to 0$ with projective terms. Two projective resolutions of the same object are never equal and rarely isomorphic, but they are homotopy equivalent, and the homotopy equivalence is unique up to homotopy. This is the comparison theorem of Cartan and Eilenberg. It is the main result of the section.

The section defines projective resolutions, constructs one for each object of an abelian category with enough projectives, and proves the comparison theorem: a map of objects lifts to a map of resolutions, and two lifts are homotopic. As a consequence the choice of a resolution is a functor from $C$ to the homotopy category of chain complexes. The second half dualizes everything to injective resolutions, with the abelian groups $\mathbb{Q}$ and $\mathbb{Q}/\mathbb{Z}$ as the main examples.

The category $C$ is abelian. Projective and injective objects, and enough projectives and injectives, are from Volume 25, Chapter 2. Homotopies and the homotopy category are from Chapter 3. Chain complexes are in `ChainComplex C ℕ`, with $d_n : P_n \to P_{n-1}$, and cochain complexes are in `CochainComplex C ℕ`. Mathlib writes `f ≫ g` for $g \circ f$.

### Definitions

**Definition (Projective resolution).** Let $Z$ be an object of $C$. A *projective resolution* of $Z$ is a chain complex $P$ indexed by $\mathbb{N}$ with each $P_n$ projective, together with a map $\pi : P_0 \to Z$ with $\pi \circ d_1 = 0$, such that the augmented sequence
$$\cdots \to P_2 \xrightarrow{d_2} P_1 \xrightarrow{d_1} P_0 \xrightarrow{\pi} Z \to 0$$
is exact. Equivalently, $\pi$ defines a map of complexes from $P$ to the complex $Z[0]$ that has $Z$ in degree $0$ and zero elsewhere, and this map is a quasi-isomorphism: $H_0(P) \cong Z$ through $\pi$, and $H_n(P) = 0$ for $n \geq 1$.

The equivalence of the two forms is a matter of reading the homology. Exactness at $Z$ says that $\pi$ is an epimorphism, exactness at $P_0$ says that $\ker \pi = \operatorname{im} d_1$, and so $H_0(P) = P_0 / \operatorname{im} d_1 \cong Z$. Exactness at $P_n$ for $n \geq 1$ is $H_n(P) = 0$.

**Definition (Injective resolution).** Dually, an *injective resolution* of $Z$ is a cochain complex $I$ indexed by $\mathbb{N}$ with each $I^n$ injective, together with $\iota : Z \to I^0$ with $d^0 \circ \iota = 0$, such that $0 \to Z \xrightarrow{\iota} I^0 \xrightarrow{d^0} I^1 \to \cdots$ is exact. Equivalently, $\iota : Z[0] \to I$ is a quasi-isomorphism.

::: mathlib
`CategoryTheory.ProjectiveResolution` · `Mathlib.CategoryTheory.Preadditive.Projective.Resolution`

The structure `ProjectiveResolution Z` has fields `complex : ChainComplex C ℕ`, `projective : ∀ n, Projective (complex.X n)`, an instance field `hasHomology`, `π : complex ⟶ (ChainComplex.single₀ C).obj Z` and `quasiIso : QuasiIso π`. So Mathlib takes the second form of the definition. The augmented form is recovered by `exact_succ` and `complex_exactAt_succ` for the degrees $n \geq 1$, and by `isColimitCokernelCofork`, which says that `π.f 0` is a cokernel of `complex.d 1 0`. The class `HasProjectiveResolution Z` asks for a resolution to exist, and `HasProjectiveResolutions C` asks it for every object. A projective object is its own resolution, by `ProjectiveResolution.self`.

<?decl CategoryTheory.ProjectiveResolution?>
:::

The dual structure `InjectiveResolution Z` has fields `cocomplex : CochainComplex C ℕ`, `injective`, `ι : (CochainComplex.single₀ C).obj Z ⟶ cocomplex` and `quasiIso`. `isLimitKernelFork` says that `ι.f 0` is a kernel of `cocomplex.d 0 1`.

### Theorems and proofs

**Theorem (Existence of projective resolutions).** If $C$ has enough projectives, each object of $C$ has a projective resolution.

*Proof.* Choose an epimorphism $\pi : P_0 \to Z$ with $P_0$ projective, which exists because $C$ has enough projectives. Let $K_0 = \ker \pi$ with inclusion $k_0 : K_0 \to P_0$. Choose an epimorphism $e_1 : P_1 \to K_0$ with $P_1$ projective, and set $d_1 = k_0 e_1$. In general, assume $d_n : P_n \to P_{n-1}$ is built. Let $K_n = \ker d_n$ with inclusion $k_n$, choose an epimorphism $e_{n+1} : P_{n+1} \to K_n$ from a projective, and set $d_{n+1} = k_n e_{n+1}$. Then $d_n d_{n+1} = d_n k_n e_{n+1} = 0$. The image of $d_{n+1}$ is $K_n = \ker d_n$, because $e_{n+1}$ is an epimorphism and $k_n$ is a monomorphism. In the same way $\operatorname{im} d_1 = K_0 = \ker \pi$, and $\pi$ is an epimorphism. So the augmented sequence is exact. $\square$

The kernels $K_n$ are the *syzygies* of $Z$. The resolution depends on the choices of the epimorphisms, and the next theorem controls this dependence.

**Theorem (Comparison theorem).** Let $f : Y \to Z$ be a morphism, let $P \to Y$ be a projective resolution of $Y$, and let $Q \to Z$ be a projective resolution of $Z$. Then:

1. there is a map of complexes $f_\bullet : P \to Q$ with $\pi_Q f_0 = f \pi_P$;
2. two such maps are homotopic.

The proof of part 1 uses only that the $P_n$ are projective and that the augmented $Q$ is exact.

*Proof of part 1.* Build $f_n$ by induction. In degree $0$, the map $f \pi_P : P_0 \to Z$ lifts through the epimorphism $\pi_Q : Q_0 \to Z$, because $P_0$ is projective. Call the lift $f_0$. In degree $1$, the map $f_0 d_1 : P_1 \to Q_0$ satisfies $\pi_Q f_0 d_1 = f \pi_P d_1 = 0$, so it lands in $\ker \pi_Q = \operatorname{im} d_1^Q$. The map $d_1^Q : Q_1 \to \operatorname{im} d_1^Q$ is an epimorphism and $P_1$ is projective, so $f_0 d_1 = d_1^Q f_1$ for some $f_1$. In degree $n + 1$, with $f_n$ and $f_{n-1}$ built and $d_n^Q f_n = f_{n-1} d_n$, the map $f_n d_{n+1}$ satisfies $d_n^Q f_n d_{n+1} = f_{n-1} d_n d_{n+1} = 0$. So it lands in $\ker d_n^Q = \operatorname{im} d_{n+1}^Q$, and projectivity of $P_{n+1}$ gives $f_{n+1}$ with $d_{n+1}^Q f_{n+1} = f_n d_{n+1}$. $\square$

*Proof of part 2.* Let $f_\bullet$ and $f'_\bullet$ be two lifts and set $g = f_\bullet - f'_\bullet$. Then $g$ is a map of complexes with $\pi_Q g_0 = 0$, and it suffices to show $g \simeq 0$. A homotopy is a family $h_n : P_n \to Q_{n+1}$ with
$$g_n = d_{n+1}^Q h_n + h_{n-1} d_n, \qquad h_{-1} = 0.$$
In degree $0$, $g_0$ lands in $\ker \pi_Q = \operatorname{im} d_1^Q$, so projectivity of $P_0$ gives $h_0$ with $d_1^Q h_0 = g_0$. Assume $h_0, \ldots, h_{n-1}$ satisfy the equations in degrees up to $n - 1$. Consider $u = g_n - h_{n-1} d_n : P_n \to Q_n$. Then
$$d_n^Q u = g_{n-1} d_n - d_n^Q h_{n-1} d_n = (g_{n-1} - d_n^Q h_{n-1}) d_n = h_{n-2} d_{n-1} d_n = 0,$$
by the equation in degree $n - 1$. So $u$ lands in $\ker d_n^Q = \operatorname{im} d_{n+1}^Q$, and projectivity of $P_n$ gives $h_n$ with $d_{n+1}^Q h_n = u$. This is the equation in degree $n$. $\square$

Each step solves an equation that involves only the two previous components, which is the pattern of `Homotopy.mkInductive` from Chapter 3, Section 1.

**Corollary (Uniqueness of resolutions).** Let $P$ and $Q$ be projective resolutions of the same object $Z$. The lifts $\alpha : P \to Q$ and $\beta : Q \to P$ of $1_Z$ are inverse homotopy equivalences, and $\alpha$ is unique up to homotopy.

*Proof.* The composite $\beta \alpha$ is a lift of $1_Z$ from $P$ to $P$, and so is $1_P$. By part 2, $\beta \alpha \simeq 1_P$. In the same way $\alpha \beta \simeq 1_Q$. Uniqueness is part 2. $\square$

**Corollary (The resolution functor).** Assume that $C$ has enough projectives and choose a projective resolution $P(Z)$ for each object $Z$. Then $Z \mapsto P(Z)$, with a morphism $f$ sent to the class of a lift $f_\bullet$, is a functor from $C$ to the homotopy category $K(C)$ of chain complexes indexed by $\mathbb{N}$.

*Proof.* The class of $f_\bullet$ does not depend on the choice of the lift, by part 2. The lift of $1_Z$ can be chosen as $1_{P(Z)}$. If $f_\bullet$ lifts $f$ and $g_\bullet$ lifts $g$, then $g_\bullet f_\bullet$ lifts $g f$, because $\pi g_0 f_0 = g \pi f_0 = g f \pi$. So the classes compose correctly. $\square$

**Theorem (Injective resolutions).** If $C$ has enough injectives, each object has an injective resolution. Given $f : Y \to Z$, an injective resolution $I$ of $Y$ and an injective resolution $J$ of $Z$, there is a map of complexes $f^\bullet : I \to J$ with $f^0 \iota_Y = \iota_Z f$, and any two such maps are homotopic. Two injective resolutions of the same object are homotopy equivalent, and the choice of resolutions gives a functor from $C$ to the homotopy category of cochain complexes indexed by $\mathbb{N}$.

*Proof.* Apply the results for projective resolutions in the opposite category $C^{\mathrm{op}}$. An object is injective in $C$ if and only if it is projective in $C^{\mathrm{op}}$, enough injectives in $C$ is enough projectives in $C^{\mathrm{op}}$, and an injective resolution of $Z$ in $C$ is a projective resolution of $Z$ in $C^{\mathrm{op}}$. Kernels in $C$ are cokernels in $C^{\mathrm{op}}$, so the existence proof uses cokernels and monomorphisms into injectives. A homotopy in $C^{\mathrm{op}}$ is a homotopy in $C$ with the arrows reversed. $\square$

Mathlib proves the injective case directly, with the same induction written with `Injective.factorThru`.

### Examples

**Example (A resolution of $\mathbb{Z}/n$).** Let $n \geq 1$. Over $\mathbb{Z}$, the sequence $0 \to \mathbb{Z} \xrightarrow{n} \mathbb{Z} \to \mathbb{Z}/n \to 0$ is exact, and $\mathbb{Z}$ is free, hence projective. So $P_1 = P_0 = \mathbb{Z}$, $d_1 = n$ and $P_k = 0$ for $k \geq 2$ is a projective resolution of $\mathbb{Z}/n$. More generally, every subgroup of a free abelian group is free, so every abelian group $A$ has a resolution of length $1$: a free group $F_0$ on generators of $A$, and the free kernel $F_1$.

**Example (Lifting a map, and a second lift).** Let $f : \mathbb{Z}/2 \to \mathbb{Z}/4$ send $1$ to $2$. Resolve $\mathbb{Z}/2$ by $\mathbb{Z} \xrightarrow{2} \mathbb{Z}$ and $\mathbb{Z}/4$ by $\mathbb{Z} \xrightarrow{4} \mathbb{Z}$. In degree $0$ choose $f_0 = 2$: then $\pi_Q(f_0(1)) = 2 = f(\pi_P(1))$. In degree $1$ solve $4 f_1 = f_0 \cdot 2 = 4$, so $f_1 = 1$. A second lift is $f'_0 = 6$, since $6 \equiv 2 \pmod 4$, with $4 f'_1 = 12$, so $f'_1 = 3$. The difference is $g_0 = 4$ and $g_1 = 2$. The homotopy of the proof is $h_0 = 1 : P_0 \to Q_1$: indeed $d_1^Q h_0 = 4 = g_0$, and $h_0 d_1^P = 2 = g_1$.

**Example (A resolution that does not stop).** Over the ring $R = \mathbb{Z}/4$, the module $\mathbb{Z}/2 = R/2R$ has the projective resolution
$$\cdots \xrightarrow{2} R \xrightarrow{2} R \xrightarrow{2} R \to \mathbb{Z}/2 \to 0.$$
It is exact, because the kernel and the image of multiplication by $2$ on $R$ are both $2R$. Every syzygy is $2R \cong \mathbb{Z}/2$, of order $2$. A projective module over the local ring $\mathbb{Z}/4$ is free, of order a power of $4$, so no syzygy is projective. Section 3 shows with Ext groups that $\mathbb{Z}/2$ has infinite projective dimension over $\mathbb{Z}/4$.

**Example (A resolution over a polynomial ring).** Let $k$ be a field and $R = k[x, y]$. The module $k = R/(x, y)$ has the Koszul resolution
$$0 \to R \xrightarrow{\begin{pmatrix} -y \\ x \end{pmatrix}} R^2 \xrightarrow{(x \ \ y)} R \to k \to 0.$$
The composite is $x(-y) + y x = 0$. Exactness at $R^2$: if $x a + y b = 0$, then $x$ divides $y b$, so $x$ divides $b$, say $b = x c$, and then $a = -y c$. So $(a, b) = c(-y, x)$. The first map is injective because $R$ is a domain.

**Example (Injective resolutions of abelian groups).** Divisible abelian groups are injective $\mathbb{Z}$-modules. So $0 \to \mathbb{Z} \to \mathbb{Q} \to \mathbb{Q}/\mathbb{Z} \to 0$ is an injective resolution of $\mathbb{Z}$, with $I^0 = \mathbb{Q}$, $I^1 = \mathbb{Q}/\mathbb{Z}$. For $\mathbb{Z}/n$, the map $1 \mapsto 1/n$ embeds $\mathbb{Z}/n$ into $\mathbb{Q}/\mathbb{Z}$ as the kernel of multiplication by $n$, and multiplication by $n$ is surjective on $\mathbb{Q}/\mathbb{Z}$. So $0 \to \mathbb{Z}/n \to \mathbb{Q}/\mathbb{Z} \xrightarrow{n} \mathbb{Q}/\mathbb{Z} \to 0$ is an injective resolution of $\mathbb{Z}/n$.

### The library around it

::: mathlib
`CategoryTheory.ProjectiveResolution.lift` · `Mathlib.CategoryTheory.Abelian.Projective.Resolution`

For `f : Y ⟶ Z`, `P : ProjectiveResolution Y` and `Q : ProjectiveResolution Z`, `lift f P Q : P.complex ⟶ Q.complex` is the lift of part 1, built from `liftFZero`, `liftFOne` and `liftFSucc` with `Projective.factorThru`. The lemma `lift_commutes` says `lift f P Q ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f`. `liftHomotopyZero` is part 2 for a map `f` with `f ≫ Q.π = 0`, built with `Homotopy.mkInductive`, and `liftHomotopy` is part 2 for two lifts. `liftIdHomotopy` and `liftCompHomotopy` are the identities used in the functor.

<?decl CategoryTheory.ProjectiveResolution.lift?>
:::

`ProjectiveResolution.homotopyEquiv P Q` is the homotopy equivalence of the first corollary, with `hom := lift (𝟙 X) P Q`. The functor of the second corollary is `projectiveResolutions C : C ⥤ HomotopyCategory C (ComplexShape.down ℕ)`. It needs `HasProjectiveResolutions C` and uses the chosen resolution `projectiveResolution Z`, and `ProjectiveResolution.iso P` compares its value with the class of any other resolution `P`. The construction of the existence theorem is `ProjectiveResolution.ofComplex Z`, which uses `Projective.over`, `Projective.π`, `Projective.syzygies` and `Projective.d` from the basic file, with the exactness lemma `exact_d_f`. `ProjectiveResolution.of Z` packages it, and an instance gives `HasProjectiveResolutions C` from `EnoughProjectives C`. An additive functor that preserves projectives and homology sends a resolution to a resolution by `Functor.mapProjectiveResolution`.

::: mathlib
`CategoryTheory.InjectiveResolution.desc` · `Mathlib.CategoryTheory.Abelian.Injective.Resolution`

For an injective resolution `I` of `Y`, an injective resolution `J` of `Z` and `f : Y ⟶ Z`, the map `desc f J I : I.cocomplex ⟶ J.cocomplex` extends `f`, and `desc_commutes` is the commuting square. Note the order of the arguments: the target resolution comes first. `descHomotopy`, `descIdHomotopy` and `descCompHomotopy` are the dual homotopies, `InjectiveResolution.homotopyEquiv` the dual corollary, and `injectiveResolutions C : C ⥤ HomotopyCategory C (ComplexShape.up ℕ)` the dual functor. `InjectiveResolution.of Z` is built from `Injective.under` and `Injective.syzygies`, with the exactness lemma `exact_f_d`.

<?decl CategoryTheory.InjectiveResolution.desc?>
:::

The resolutions above are chosen for each object, and the choices are not functorial. The structure `CategoryTheory.Abelian.LeftResolution` gives functorial resolutions by objects of a full subcategory. For a fully faithful functor $\iota : C \to A$ to an abelian category, it has a functor $F : A \to C$ and a natural epimorphism $\iota(F(X)) \to X$. The construction `CategoryTheory.Abelian.LeftResolution.chainComplexFunctor` then gives a functor from $A$ to chain complexes in $C$ indexed by $\mathbb{N}$. In degree $0$ the complex is $F(X)$, by `CategoryTheory.Abelian.LeftResolution.chainComplexXZeroIso`, and in each degree $n + 1$ it applies $F$ to a kernel of the previous step. The lemma `CategoryTheory.Abelian.LeftResolution.exactAt_map_chainComplex_succ` says that the image of the complex in $A$ is exact in each positive degree. To extend the construction to complexes, $F$ must send zero morphisms to zero. The module `Mathlib.Algebra.Homology.LeftResolution.Reduced` gives `CategoryTheory.Abelian.LeftResolution.reduced` with this property when $A$ and $C$ are idempotent complete, through the extension `CategoryTheory.Abelian.LeftResolution.karoubi` to the idempotent completions. The module `Mathlib.Algebra.Homology.LeftResolution.Transport` moves the structure along equivalences of categories, by `CategoryTheory.Abelian.LeftResolution.transport`, and along an isomorphism of functors, by `CategoryTheory.Abelian.LeftResolution.ofCompIso`. A typical use is a functorial resolution of modules by flat modules, with the free module on the elements of a module.

Common errors of a learner:

- The field `π` of a resolution is a map of complexes into `(single₀ C).obj Z`, not a morphism `P₀ ⟶ Z`. The morphism of $C$ is `P.π.f 0`.
- The lift is unique only up to homotopy. In the example the lifts with $f_0 = 2$ and $f_0 = 6$ differ as maps of complexes.
- The functor `projectiveResolutions C` takes values in the homotopy category, not in chain complexes. A statement about the actual complex goes through `projectiveResolution Z` and `ProjectiveResolution.iso`.
- An injective resolution is a `CochainComplex C ℕ`, with differential `d n (n + 1)`, while a projective resolution is a `ChainComplex C ℕ`, with `d (n + 1) n`.

### Exercises

1. (A) Write a projective resolution of $\mathbb{Z}/6$ over $\mathbb{Z}$ and one of $\mathbb{Z}/2 \oplus \mathbb{Z}/3$, and give a homotopy equivalence between them.
2. (A) Let $P$ be projective. Show that $P$ in degree $0$ with $\pi = 1_P$ is a projective resolution of $P$, and that every projective resolution of $P$ is contractible after the augmentation is added. *Hint:* the comparison theorem with $1_P$.
3. (B) Over $R = \mathbb{Z}/4$, lift the map $\mathbb{Z}/2 \to \mathbb{Z}/2$ that is multiplication by $1$ to the periodic resolution in two ways, and give the homotopy between the two lifts.
4. (B) Let $k$ be a field and $R = k[x]/(x^2)$. Give a projective resolution of $k = R/(x)$ and show that it does not stop.
5. (B) Show that the abelian category of finite abelian groups has no nonzero projective object, so it does not have enough projectives. *Hint:* for $P \ne 0$ take a surjection $P \to \mathbb{Z}/p$, and lift it along $\mathbb{Z}/p^k \to \mathbb{Z}/p$ with $p^k > |P|$.
6. (C) Prove the horseshoe lemma: given a short exact sequence $0 \to A \to B \to Q \to 0$ and projective resolutions $P^A$ and $P^Q$, build a projective resolution of $B$ with terms $P^A_n \oplus P^Q_n$ that fits in a short exact sequence of resolutions. *Hint:* lift $P^Q_0 \to Q$ to $B$ and continue with the kernels and the snake lemma.
7. (C) Show that the comparison theorem fails without the projectivity of $P$: find a resolution $P \to \mathbb{Z}/2$ by abelian groups that are not all projective and a map that does not lift. *Hint:* take $P_0 = \mathbb{Z}/2$.

### Notes and history

Cartan and Eilenberg, *Homological Algebra* (1956), introduced projective and injective resolutions in this generality, with the comparison theorem as the base of the theory of derived functors. Grothendieck, in the Tohoku paper of 1957, gave the axioms of abelian categories and proved that a category of sheaves of modules has enough injectives, so that injective resolutions exist there. Hilbert's syzygy theorem of 1890 says that each finitely generated module over $k[x_1, \ldots, x_n]$ has a free resolution of length at most $n$. The Koszul resolution of $k$ over $k[x, y]$ is a case of length $2$.

The Mathlib Authors of `Preadditive.Projective.Resolution` are Kim Morrison and Joël Riou, and of `Preadditive.Injective.Resolution` Jujian Zhang, Kim Morrison and Joël Riou. The file `Abelian.Projective.Resolution` is by Markus Himmel, Kim Morrison, Jakob von Raumer and Joël Riou, and `Abelian.Injective.Resolution` is by Jujian Zhang and Kim Morrison.

### Reference

<?reference?>
