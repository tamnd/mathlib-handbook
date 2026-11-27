---
title: The category of representations
kind: theory
modules:
  - Mathlib.RepresentationTheory.Action
  - Mathlib.RepresentationTheory.Rep.Basic
  - Mathlib.RepresentationTheory.Rep.Iso
  - Mathlib.RepresentationTheory.Rep.Res
  - Mathlib.RepresentationTheory.FDRep
explains:
  E3: [Rep, Rep.of, Rep.Hom, Rep.ofHom, Rep.repIsoAction, Rep.equivalenceModuleMonoidAlgebra, Rep.resFunctor, Rep.shortExact_res, Rep.mkIso, FDRep, FDRep.of, FDRep.finrank_hom_simple_simple, FDRep.dualTensorIsoLinHom, Representation.linearize, Rep.linearization, Rep.tensorHomEquiv, Rep.leftRegularHomEquiv]
  E2: [Rep.hom_comm_apply, Rep.trivial, Rep.trivialFunctor, Rep.leftRegular, Rep.ofMulAction, Rep.RepToAction, Rep.ActionToRep, Rep.isZero_iff, Rep.epi_iff_surjective, Rep.mono_iff_injective, Rep.tensor_ρ, Rep.tensorUnit_ρ, Rep.ihom, Rep.toModuleMonoidAlgebra, Rep.ofModuleMonoidAlgebra, Rep.free_projective, Rep.leftRegular_projective, Rep.res, Rep.full_res, Rep.isZero_res_iff, Rep.ofQuotient, Rep.liftHomOfSurj, Rep.res_map_exact, FDRep.ρ, FDRep.isoToLinearEquiv, FDRep.forget₂HomLinearEquiv, Representation.equivOfIso, Rep.homLinearEquiv, Rep.hom_braiding, Representation.linearizeMap, Rep.linearizationTrivialIso, Rep.linearizationOfMulActionIso, Rep.diagonalSuccIsoFree]
  E1: auto
families: []
requires: [V05.C06, V24.C02, V24.C05, V24.C07, V24.C08, V25.C02, V26.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The category of representations

### Overview

The representations of a fixed group $G$ over a fixed ring $k$ form a category $\mathbf{Rep}_k(G)$: the objects are representations and the morphisms are intertwining maps. This category carries the full apparatus of Volumes 24 to 26. It is abelian, it has a tensor product with an internal Hom, it has enough projectives, and restriction along a group homomorphism is an exact functor. Group cohomology in Volume 26, Chapter 8, is the derived functor of the invariants on this category, and it is the main user of the material of this section.

This section proves that $\mathbf{Rep}_k(G)$ is equivalent to the category of $k[G]$-modules and to the category of functors from $G$ to $k$-modules, studies its monoidal closed structure, proves that restriction is faithful and exact, and introduces the full subcategory $\mathbf{FDRep}_k(G)$ of finite dimensional representations over a field. The section closes with the dimension form of the lemma of Schur in $\mathbf{FDRep}$ and the linearization functor from $G$-sets to representations.

In this section $k$ is a commutative ring and $G$ a group, unless a statement says otherwise.

### Definitions

**Definition (The category Rep).** An object of $\mathbf{Rep}_k(G)$ is a pair $(V, \rho)$ of a $k$-module and a representation of $G$ on it. A morphism $(V, \rho) \to (W, \sigma)$ is an intertwining map, and composition is composition of maps.

**Definition (Action category).** Let $\mathcal{C}$ be a category and view $G$ as a category with one object. The category $\mathrm{Action}(\mathcal{C}, G)$ has as objects pairs of an object $X$ of $\mathcal{C}$ and a monoid homomorphism $G \to \mathrm{End}(X)$, and as morphisms the maps of $\mathcal{C}$ that commute with the actions. For $\mathcal{C}$ the category of sets this is the category of $G$-sets; for $\mathcal{C}$ the category of $k$-modules it is a second form of $\mathbf{Rep}_k(G)$.

**Definition (Restriction).** For a group homomorphism $f \colon H \to G$, the restriction functor $\mathrm{res}_f \colon \mathbf{Rep}_k(G) \to \mathbf{Rep}_k(H)$ sends $(V, \rho)$ to $(V, \rho \circ f)$ and an intertwining map to the same linear map.

**Definition (Tensor structure).** The tensor product of $(V, \rho)$ and $(W, \sigma)$ is the representation on $V \otimes_k W$ with $g(v \otimes w) = gv \otimes gw$. The unit is the trivial representation on $k$. The internal Hom $\underline{\mathrm{Hom}}(V, W)$ is $\mathrm{Hom}_k(V, W)$ with $g \cdot f = \sigma(g) f \rho(g)^{-1}$.

**Definition (Finite dimensional representations).** For a field $k$, the category $\mathbf{FDRep}_k(G)$ is $\mathrm{Action}(\mathcal{F}, G)$, where $\mathcal{F}$ is the category of finite dimensional $k$-vector spaces.

**Definition (Linearization).** The linearization of a $G$-set $X$ is the permutation representation on the free module $k[X]$. A $G$-map $\phi \colon X \to Y$ goes to the linear map $e_x \mapsto e_{\phi(x)}$.

### Theorems and proofs

**Theorem (Representations are modules).** The functor that sends $(V, \rho)$ to the $k[G]$-module $V$ of Section 1 is an equivalence $\mathbf{Rep}_k(G) \simeq \mathrm{Mod}_{k[G]}$. The same data give an equivalence $\mathbf{Rep}_k(G) \simeq \mathrm{Action}(\mathrm{Mod}_k, G)$.

*Proof.* Section 1 gives a bijection between representations on $V$ and $k[G]$-module structures on $V$ that extend the $k$-structure, and it proves that a $k$-linear map intertwines if and only if it is $k[G]$-linear. So the functor $F$ is fully faithful: on morphisms it is the identity map of sets between $\mathrm{Hom}_G(V, W)$ and $\mathrm{Hom}_{k[G]}(V, W)$. A $k[G]$-module $M$ is a $k$-module by restriction along $k \to k[G]$, $r \mapsto r e_1$, and the representation $g \mapsto (m \mapsto e_g m)$ goes to a module equal to $M$. So $F$ is essentially surjective, and a fully faithful, essentially surjective functor is an equivalence by Volume 24, Chapter 2. For the second equivalence, an object of $\mathrm{Action}(\mathrm{Mod}_k, G)$ is a $k$-module with a monoid homomorphism $G \to \mathrm{End}_k(V)$, which is a representation by definition, and the morphisms of both categories are the linear maps that commute with the action. $\square$

**Corollary (Kernels, monos and epis).** The category $\mathbf{Rep}_k(G)$ is abelian. A morphism is a monomorphism if and only if it is injective, and an epimorphism if and only if it is surjective. An object is zero if and only if its module is zero.

*Proof.* The category $\mathrm{Mod}_{k[G]}$ is abelian, with the monomorphisms the injective maps and the epimorphisms the surjective maps (Volume 26, Chapter 7). Each of these properties is invariant under an equivalence of categories, and the equivalence of the theorem does not change the underlying maps. $\square$

**Theorem (Tensor and Hom adjunction).** For representations $A$, $B$, $C$ there is a natural bijection
$$\mathrm{Hom}_G(A \otimes B, C) \cong \mathrm{Hom}_G(B, \underline{\mathrm{Hom}}(A, C)), \qquad \varphi \mapsto \big(b \mapsto (a \mapsto \varphi(a \otimes b))\big).$$
So $\mathbf{Rep}_k(G)$ is monoidal closed.

*Proof.* Over $k$ alone, the currying map $\varphi \mapsto \psi$ with $\psi(b)(a) = \varphi(a \otimes b)$ is a bijection $\mathrm{Hom}_k(A \otimes B, C) \cong \mathrm{Hom}_k(B, \mathrm{Hom}_k(A, C))$ (Volume 8, Chapter 2). It remains to show that $\varphi$ intertwines if and only if $\psi$ does. The map $\psi$ intertwines when $\psi(gb) = g \cdot \psi(b)$ for all $g$ and $b$, that is, when
$$\varphi(a \otimes gb) = g\,\varphi(g^{-1} a \otimes b) \quad \text{for all } a, b, g.$$
If $\varphi$ intertwines, the right side is $\varphi(g(g^{-1}a \otimes b)) = \varphi(a \otimes gb)$. Conversely, put $a = g a'$ in the displayed equation and apply it: $\varphi(g(a' \otimes b)) = \varphi(ga' \otimes gb) = g \varphi(a' \otimes b)$. Both sides are additive in the tensor, so $\varphi$ intertwines on all of $A \otimes B$. Naturality holds because the currying map over $k$ is natural. $\square$

**Proposition (Maps out of the regular representation).** For each representation $A$, the map $\mathrm{Hom}_G(k[G], A) \to A$, $f \mapsto f(e_1)$, is a $k$-linear isomorphism. Hence the left regular representation, and each free representation $k[G]^{(I)}$, is a projective object of $\mathbf{Rep}_k(G)$, and $\mathbf{Rep}_k(G)$ has enough projectives.

*Proof.* The isomorphism is the proposition of Section 1, transported along the identification of morphisms with intertwining maps. Let $p \colon B \to C$ be an epimorphism and $u \colon k[G] \to C$ a morphism. Then $p$ is surjective by the corollary, so there is $b \in B$ with $p(b) = u(e_1)$. The morphism $\tilde u$ with $\tilde u(e_1) = b$ satisfies $(p \circ \tilde u)(e_1) = u(e_1)$, so $p \circ \tilde u = u$ by the isomorphism. So $k[G]$ is projective; the same argument works one basis vector at a time for $k[G]^{(I)}$. Each $A$ receives the epimorphism $k[G]^{(A)} \to A$ that sends the basis vector $e_1$ of index $a$ to $a$. $\square$

**Theorem (Restriction is exact).** Let $f \colon H \to G$ be a group homomorphism. The functor $\mathrm{res}_f$ is faithful and exact, and a short complex in $\mathbf{Rep}_k(G)$ is short exact if and only if its restriction is. If $f$ is surjective, $\mathrm{res}_f$ is also full.

*Proof.* The functor does not change modules or maps, so it is faithful, and it preserves and reflects injectivity, surjectivity, kernels and images. Exactness of a short complex $A \to B \to C$ means that the kernel of the second map equals the image of the first, a statement about the underlying modules only; so restriction preserves and reflects it. If $f$ is surjective and $\phi \colon V \to W$ intertwines the actions of $H$, take $g \in G$ and choose $h$ with $f(h) = g$. Then $\phi \circ \rho(g) = \phi \circ \rho(f(h)) = \sigma(f(h)) \circ \phi = \sigma(g) \circ \phi$, so $\phi$ is a morphism of $\mathbf{Rep}_k(G)$. $\square$

**Theorem (Dimension of Hom between simple objects).** Let $k$ be an algebraically closed field and $V$, $W$ simple objects of $\mathbf{FDRep}_k(G)$. Then $\dim_k \mathrm{Hom}_G(V, W)$ is $1$ if $V \cong W$ and $0$ otherwise.

*Proof.* Let $\phi \colon V \to W$ be a nonzero morphism. Its kernel is a subrepresentation of $V$ different from $V$, so it is $0$; its image is a nonzero subrepresentation of $W$, so it is $W$. So $\phi$ is an isomorphism. If $V \not\cong W$, this shows $\mathrm{Hom}_G(V, W) = 0$. If $V \cong W$, then $\mathrm{Hom}_G(V, W) \cong \mathrm{End}_G(V)$ by composition with a fixed isomorphism. Let $\phi \in \mathrm{End}_G(V)$. Since $V \ne 0$ is finite dimensional and $k$ is algebraically closed, $\phi$ has an eigenvalue $\lambda$. Then $\phi - \lambda\,\mathrm{id}$ is a morphism with nonzero kernel, so it is not an isomorphism, and by the first step it is $0$. So $\mathrm{End}_G(V) = k \cdot \mathrm{id}$, which has dimension $1$. $\square$

**Proposition (Linearization is monoidal).** The linearization functor sends the product of $G$-sets to the tensor product: $k[X \times Y] \cong k[X] \otimes k[Y]$ as representations, by $e_{(x, y)} \mapsto e_x \otimes e_y$, and it sends the one-point $G$-set to the trivial representation $k$.

*Proof.* The map sends a basis of $k[X \times Y]$ bijectively to the basis $\{e_x \otimes e_y\}$ of $k[X] \otimes k[Y]$ (Volume 8, Chapter 2), so it is a linear isomorphism. It intertwines because $g e_{(x,y)} = e_{(gx, gy)} \mapsto e_{gx} \otimes e_{gy} = g(e_x \otimes e_y)$. On the one-point set, $k[\mathrm{pt}] = k e_{\mathrm{pt}}$ with $g e_{\mathrm{pt}} = e_{\mathrm{pt}}$. $\square$

### Examples

**Example (Restriction from $S_3$ to $A_3$).** Restrict the representation $W = \{x \in \mathbb{Q}^3 : x_1 + x_2 + x_3 = 0\}$ of $S_3$ to the subgroup $A_3 \cong \mathbb{Z}/3$. With basis $w_1 = e_1 - e_2$, $w_2 = e_2 - e_3$, the cycle $c = (1\,2\,3)$ sends $w_1 \mapsto e_2 - e_3 = w_2$ and $w_2 \mapsto e_3 - e_1 = -w_1 - w_2$, so $c$ acts by $\begin{pmatrix} 0 & -1 \\ 1 & -1 \end{pmatrix}$. The inclusion $A_3 \to S_3$ is not surjective, and restriction is not full: the linear map of order $3$ given by $c$ itself intertwines the action of $A_3$, because $A_3$ is abelian, but it does not commute with $(1\,2)$, which sends $w_1 \mapsto -w_1$.

**Example (Linearization of a coset space).** Let $H \le G$ and let $G$ act on $G/H$ by left multiplication. The linearization is the permutation representation $k[G/H]$. For $G = S_3$ and $H = \langle (1\,2) \rangle$ the set $G/H$ has three points, and $k[G/H]$ is isomorphic to the permutation representation on $k^3$, since $S_3$ acts on $\{1, 2, 3\}$ with the stabilizer of $3$ equal to $H$.

**Counterexample (A non-split epimorphism).** Let $p$ be a prime, $G = \mathbb{Z}/p$ and $k = \mathbb{F}_p$. The augmentation $\varepsilon \colon k[G] \to k$, $\sum a_g e_g \mapsto \sum a_g$, is an epimorphism onto the trivial representation. A section would send $1$ to an invariant element with augmentation $1$. The invariants of $k[G]$ are the multiples of $N = \sum_g e_g$, and $\varepsilon(cN) = cp = 0$. So $\varepsilon$ does not split, and the trivial representation is not projective in $\mathbf{Rep}_{\mathbb{F}_p}(\mathbb{Z}/p)$, although $k[G]$ is.

**Example (Internal Hom and the dual).** For $V$ the trivial representation $k$, $\underline{\mathrm{Hom}}(V, W) \cong W$ as representations. For $W = k$ trivial, $\underline{\mathrm{Hom}}(V, k)$ is the dual $V^*$. For the sign representation $\varepsilon$ of $S_3$, $\varepsilon^* \cong \varepsilon$, because $\varepsilon(g^{-1}) = \varepsilon(g)$.

### The library around it

::: mathlib
`Rep` · `Mathlib.RepresentationTheory.Rep.Basic`

`Rep k G` is a structure with a carrier `V`, its `AddCommGroup` and `Module k` instances, and `ρ : Representation k G V`; it is not defined as an `Action` category. `Rep.of ρ` makes an object from a representation, and a morphism `Rep.Hom A B` wraps an `IntertwiningMap A.ρ B.ρ`, built by `Rep.ofHom` and read back by `f.hom`; `homLinearEquiv` identifies the two as `k`-modules and `hom_comm_apply` is the intertwining equation. `Rep.trivial`, `Rep.leftRegular` and `Rep.ofMulAction` are the standard objects. The file provides the abelian structure, with `isZero_iff`, `mono_iff_injective` and `epi_iff_surjective`, the symmetric monoidal structure with `tensor_ρ`, `tensorUnit_ρ` and `hom_braiding`, the closed structure through `Rep.ihom` and `tensorHomEquiv`, and `leftRegularHomEquiv : (leftRegular k G ⟶ A) ≃ₗ[k] A`. `mkIso` turns a `Representation.Equiv` into an isomorphism and `Representation.equivOfIso` goes back.

<?decl Rep?>
:::

::: mathlib
`Rep.equivalenceModuleMonoidAlgebra` · `Mathlib.RepresentationTheory.Rep.Basic`

`equivalenceModuleMonoidAlgebra : Rep k G ≌ ModuleCat k[G]` has the functors `toModuleMonoidAlgebra` and `ofModuleMonoidAlgebra`. The source has a TODO to show that it is monoidal, so the index of this edition has no declaration for that statement. `repIsoAction : Rep k G ≌ Action (ModuleCat k) G` is the second equivalence, with functors `RepToAction` and `ActionToRep`. `free_projective` and `leftRegular_projective` (in `Rep.Iso`) give the projectives, and `diagonalSuccIsoFree` identifies the representation on $G^{n+1}$ with a free one, the start of the standard resolution of Volume 26.

<?decl Rep.equivalenceModuleMonoidAlgebra?>
:::

::: mathlib
`Rep.resFunctor` · `Mathlib.RepresentationTheory.Rep.Res`

`resFunctor (f : H →* G) : Rep k G ⥤ Rep k H` has object map `res f`. It is faithful, additive and preserves limits and colimits. `full_res` gives fullness for surjective `f`, through `liftHomOfSurj`, and `isZero_res_iff`, `res_map_exact` and `shortExact_res` say that restriction reflects zero objects, exactness and short exactness. `Rep.ofQuotient` is the descent to `G ⧸ S` of an object trivial on a normal subgroup `S`.

<?decl Rep.shortExact_res?>
:::

::: mathlib
`FDRep.finrank_hom_simple_simple` · `Mathlib.RepresentationTheory.FDRep`

`FDRep R G` is `Action (FGModuleCat R) G` and is still built on `Action`, unlike `Rep`. `FDRep.of ρ` makes an object from a representation on a finite dimensional space, `FDRep.ρ V` reads the representation back, and `isoToLinearEquiv` and `forget₂HomLinearEquiv` move to linear algebra. The category is monoidal, linear and rigid. `finrank_hom_simple_simple [IsAlgClosed k]` is the dimension theorem above, and `dualTensorIsoLinHom : FDRep.of ρV.dual ⊗ W ≅ FDRep.of (linHom ρV W.ρ)` is the categorical form of the duality of Section 1.

<?decl FDRep.finrank_hom_simple_simple?>
:::

::: mathlib
`Rep.linearization` · `Mathlib.RepresentationTheory.Rep.Basic`

`Representation.linearize k G X` is the representation on `k[X.V]` of an object `X` of `Action (Type w) G`, defined in `RepresentationTheory.Action`, and `linearizeMap` is its action on morphisms. `Rep.linearization : Action (Type w) G ⥤ Rep k G` packages them, with a monoidal structure. `linearizationTrivialIso` and `linearizationOfMulActionIso` compute it on trivial actions and on `Action.ofMulAction`.

<?decl Rep.linearization?>
:::

Common errors of a learner: The first error is to treat an object `A : Rep k G` as a type with a `k[G]`-module structure; the module is `A.V`, and the `k[G]`-module is the image under `toModuleMonoidAlgebra`. The second error is to apply a morphism directly as a linear map; write `f.hom` for the intertwining map and `f.hom.toLinearMap` for the linear map. The third error is to expect the API of `Action` on `Rep`; the two are only equivalent through `repIsoAction`, while `FDRep` is an `Action` category, so lemmas proved for one do not apply to the other without the equivalence.

### Exercises

1. (A) Show that the trivial functor from $k$-modules to $\mathbf{Rep}_k(G)$ is left adjoint to the invariants functor. Hint: an intertwining map from a trivial representation lands in the invariants.
2. (A) Show that $\underline{\mathrm{Hom}}(k, W) \cong W$ for the trivial representation $k$.
3. (A) Show that restriction along $f \colon H \to G$ sends the trivial representation to the trivial representation and commutes with tensor products.
4. (B) Show that $\mathrm{Hom}_G(k[G/H], V) \cong V^H$ for a subgroup $H$. Hint: a map is determined by the image $v$ of $e_H$, and $v$ must be fixed by $H$.
5. (B) Let $G$ be finite. Show that $k[G] \cong k[G]^*$ as representations. Hint: send $e_g$ to the dual basis vector $e_g^*$ and check $h \cdot e_g^* = e_{hg}^*$.
6. (C) Show that the trivial representation $\mathbb{F}_2$ of $\mathbb{Z}/2$ is not injective in $\mathbf{Rep}_{\mathbb{F}_2}(\mathbb{Z}/2)$. Hint: extend the identity of $\mathbb{F}_2$ along the inclusion $\mathbb{F}_2 N \to \mathbb{F}_2[\mathbb{Z}/2]$, $N = e_1 + e_s$.

### Notes and history

The use of the category of modules over the group algebra became standard through the work of Noether and of Brauer around 1930, and the categorical view of group cohomology as a derived functor on it is the view of Cartan and Eilenberg in 1956. Mathlib authors, read from the file headers: `RepresentationTheory.Action` by Yunzhou Xie; `RepresentationTheory.Rep.Basic` by Edison Xie and Kim Morrison; `RepresentationTheory.Rep.Iso` and `RepresentationTheory.Rep.Res` by Edison Xie; `RepresentationTheory.FDRep` by Kim Morrison.

### Reference

<?reference?>
