---
title: Representations and intertwining maps
kind: theory
modules:
  - Mathlib.RepresentationTheory.Basic
  - Mathlib.RepresentationTheory.Intertwining
  - Mathlib.RepresentationTheory.Equiv
  - Mathlib.RepresentationTheory.Subrepresentation
  - Mathlib.RepresentationTheory.Submodule
  - Mathlib.RepresentationTheory.Invariants
explains:
  E3: [Representation, Representation.asAlgebraHom, Representation.asModule, Representation.IntertwiningMap, Representation.Equiv, Subrepresentation, Representation.invariants, Representation.tprod, Representation.dual, Representation.linHom, Representation.IntertwiningMap.equivLinearMapAsModule, Subrepresentation.subrepresentationSubmoduleOrderIso, Representation.isProj_averageMap, Representation.invariantsEquivIntertwiningMap, Representation.leftRegularMapEquiv]
  E2: [Representation.trivial, Representation.IsTrivial, Representation.ofMulAction, Representation.leftRegular, Representation.ofDistribMulAction, Representation.asAlgebraHom_single, Representation.asModuleEquiv, Representation.ofModule, Representation.subrepresentation, Representation.quotient, Representation.ofQuotient, Representation.norm, Representation.tprod_apply, Representation.linHom_apply, Representation.dual_apply, Representation.dualTensorHom_comm, Representation.IsIntertwiningMap, Representation.IntertwiningMap.ker, Representation.IntertwiningMap.range, Representation.IntertwiningMap.comp, Representation.IntertwiningMap.equivAlgEnd, Representation.IntertwiningMap.ofBijective, Representation.IntertwiningMap.tensor, Representation.Equiv.mk, Representation.Equiv.symm, Representation.Equiv.conj_apply_self, Representation.Equiv.dualTensorHom, Subrepresentation.toRepresentation, Subrepresentation.quotient, Representation.invtSubmodule, Representation.mapSubmodule, Representation.mem_invariants, GroupAlgebra.average, Representation.averageMap, Representation.averageMap_invariant, Representation.averageMap_id, Representation.mem_linHom_invariants_iff_isIntertwining, Representation.ofMulActionSubsingletonEquivTrivial, Representation.freeLiftLEquiv, Representation.free, Representation.directSum, Representation.prod, Representation.apply_bijective]
  E1: auto
families: []
requires: [V05.C06, V05.C07, V06.C08, V07.C01, V07.C06, V08.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Representations and intertwining maps

### Overview

A group is an abstract object, and a representation makes it concrete: each element of the group becomes an invertible linear map, and the product of the group becomes the composition of maps. Linear algebra then gives tools that the group alone does not have: traces, eigenvalues, dimensions, tensor products and duals. The symmetric group $S_3$ acts on $\mathbb{Q}^3$ by permutation of the coordinates; the subspaces that $S_3$ preserves and the linear maps that commute with $S_3$ are the first objects of representation theory.

This section defines a representation of a monoid $G$ on a module $V$ over a commutative ring $k$, and the three ways to see it: as a homomorphism $G \to \mathrm{End}_k(V)$, as a module over the group algebra $k[G]$, and (in Section 2) as an object of a category. It defines intertwining maps, equivalences, subrepresentations and the invariants, and it builds new representations from old ones: direct sums, tensor products, duals and spaces of linear maps. The main results are the dictionary with $k[G]$-modules, the description of intertwining maps as the invariants of $\mathrm{Hom}_k(V, W)$, and the averaging projection onto the invariants when the order of a finite group is invertible in $k$. That projection is the core of the theorem of Maschke in Chapter 2.

In this section $k$ is a commutative ring, $G$ is a monoid (a group where inverses appear), and $V$, $W$ are $k$-modules. Write $g v$ for $\rho(g)(v)$ when the representation is clear.

### Definitions

**Definition (Representation).** A representation of $G$ on $V$ is a monoid homomorphism $\rho \colon G \to \mathrm{End}_k(V)$. So $\rho(1) = \mathrm{id}_V$ and $\rho(gh) = \rho(g) \circ \rho(h)$. If $G$ is a group, each $\rho(g)$ is invertible with inverse $\rho(g^{-1})$.

Mathlib takes this definition literally: `Representation k G V` is an abbreviation for `G →* (V →ₗ[k] V)`. The motivation for the linear form is that the action of $G$ on a set is often too coarse.

**Definition (Trivial and permutation representations).** The trivial representation sends each $g$ to $\mathrm{id}_V$. If $G$ acts on a set $X$, the permutation representation on $k[X]$, the free $k$-module with basis $\{e_x\}_{x \in X}$, is $g e_x = e_{gx}$. For $X = G$ with the action by left multiplication this is the left regular representation on $k[G]$.

**Definition (Group algebra).** The group algebra $k[G]$ is the free $k$-module on $G$ with the product $e_g e_h = e_{gh}$, extended bilinearly. Mathlib writes `k[G]` for `MonoidAlgebra k G` and `single g r` for $r e_g$.

**Definition (Intertwining map).** Let $\rho$ and $\sigma$ be representations of $G$ on $V$ and $W$. An intertwining map, or $G$-map, is a $k$-linear map $f \colon V \to W$ with $f \circ \rho(g) = \sigma(g) \circ f$ for each $g \in G$. It is an equivalence if it is also bijective, so that it is a linear isomorphism. Write $\mathrm{Hom}_G(V, W)$ for the $k$-module of intertwining maps.

**Definition (Subrepresentation and quotient).** A subrepresentation of $\rho$ is a submodule $U \subseteq V$ with $\rho(g) U \subseteq U$ for each $g$. Then $\rho$ restricts to a representation on $U$, and it induces a representation on $V / U$ by $g(v + U) = gv + U$.

**Definition (Invariants).** For a group $G$, the invariants of $\rho$ are $V^G = \{ v \in V : gv = v \text{ for all } g \in G\}$. It is the largest subrepresentation on which $G$ acts trivially.

**Definition (Constructions).** Let $\rho$ on $V$ and $\sigma$ on $W$ be representations of a group $G$.

1. The direct sum acts on $V \oplus W$ by $g(v, w) = (gv, gw)$.
2. The tensor product acts on $V \otimes_k W$ by $g(v \otimes w) = gv \otimes gw$.
3. The space of linear maps $\mathrm{Hom}_k(V, W)$ carries $g \cdot f = \sigma(g) \circ f \circ \rho(g^{-1})$.
4. The dual $V^* = \mathrm{Hom}_k(V, k)$ carries $g \cdot \lambda = \lambda \circ \rho(g^{-1})$. This is the third construction with $W = k$ trivial.

The inverse $g^{-1}$ in the last two constructions is necessary. The rule $g \cdot f = \sigma(g) \circ f \circ \rho(g)$ fails the law $(gh) \cdot f = g \cdot (h \cdot f)$ when $G$ is not abelian, because the right factor comes out in the order $\rho(h)\rho(g)$.

### Theorems and proofs

**Proposition (Representations are modules over the group algebra).** Let $V$ be a $k$-module. The representations of $G$ on $V$ correspond bijectively to the $k[G]$-module structures on $V$ whose restriction to $k = k e_1$ is the given $k$-module structure. The representation $\rho$ gives the action $\big(\sum_g a_g e_g\big) v = \sum_g a_g \rho(g) v$.

*Proof.* Let $\rho$ be a representation. The $k$-module $k[G]$ is free on $G$, so there is a unique $k$-linear map $\tilde\rho \colon k[G] \to \mathrm{End}_k(V)$ with $\tilde\rho(e_g) = \rho(g)$, namely $\tilde\rho(\sum a_g e_g) = \sum a_g \rho(g)$. It is multiplicative: both sides of $\tilde\rho(xy) = \tilde\rho(x)\tilde\rho(y)$ are $k$-bilinear in $(x, y)$, so it suffices to check basis elements, and there $\tilde\rho(e_g e_h) = \rho(gh) = \rho(g)\rho(h)$. Also $\tilde\rho(e_1) = \rho(1) = \mathrm{id}$. So $\tilde\rho$ is a $k$-algebra homomorphism, and $x v = \tilde\rho(x)(v)$ is a $k[G]$-module structure. Its restriction to $r e_1$ is $r \rho(1) v = rv$. Conversely, given such a module structure, put $\rho(g)(v) = e_g v$. Each $\rho(g)$ is $k$-linear, because $e_g (r v) = e_g (r e_1) v = (r e_g) v = r (e_g v)$. The relations $e_g e_h = e_{gh}$ and $e_1 = 1$ give $\rho(gh) = \rho(g)\rho(h)$ and $\rho(1) = \mathrm{id}$. The two constructions are inverse: starting from $\rho$, the element $e_g$ acts by $\tilde\rho(e_g) = \rho(g)$; starting from a module, the action of $\sum a_g e_g$ is $\sum a_g (e_g v)$ by linearity. $\square$

**Proposition (Intertwining maps are module maps).** A $k$-linear map $f \colon V \to W$ is an intertwining map if and only if it is $k[G]$-linear for the module structures of the previous proposition. A subset $U \subseteq V$ is a subrepresentation if and only if it is a $k[G]$-submodule.

*Proof.* If $f$ is $k[G]$-linear, then $f(\rho(g) v) = f(e_g v) = e_g f(v) = \sigma(g) f(v)$. Conversely, if $f$ intertwines, then $f(\sum a_g e_g v) = \sum a_g f(\rho(g) v) = \sum a_g \sigma(g) f(v) = (\sum a_g e_g) f(v)$, by $k$-linearity of $f$. For subsets: a $k[G]$-submodule is closed under $e_g$ and under $r e_1$, so it is a $k$-submodule stable under each $\rho(g)$; a stable $k$-submodule is closed under finite sums $\sum a_g \rho(g) v$. $\square$

**Proposition (Kernels, images and inverses).** Let $f \colon V \to W$ be an intertwining map. Then $\ker f$ is a subrepresentation of $V$ and $\operatorname{im} f$ is a subrepresentation of $W$. If $f$ is bijective, its inverse is an intertwining map, so $f$ is an equivalence.

*Proof.* If $f(v) = 0$ then $f(gv) = g f(v) = 0$, so $gv \in \ker f$. If $w = f(v)$ then $gw = f(gv) \in \operatorname{im} f$. If $f$ is bijective, its inverse $f^{-1}$ is linear, and for $w = f(v)$ the equation $f^{-1}(g w) = f^{-1}(g f(v)) = f^{-1}(f(gv)) = gv = g f^{-1}(w)$ shows that $f^{-1}$ intertwines. $\square$

**Proposition (Intertwining maps as invariants).** Let $G$ be a group. A linear map $f \colon V \to W$ is an intertwining map if and only if it is an invariant of the representation on $\mathrm{Hom}_k(V, W)$. So $\mathrm{Hom}_G(V, W) = \mathrm{Hom}_k(V, W)^G$ as $k$-modules.

*Proof.* The map $f$ is invariant if and only if $\sigma(g) \circ f \circ \rho(g^{-1}) = f$ for each $g$. Compose on the right with $\rho(g)$ and use $\rho(g^{-1})\rho(g) = \rho(1) = \mathrm{id}$: the condition becomes $\sigma(g) \circ f = f \circ \rho(g)$. The steps are reversible, since composition on the right with the invertible map $\rho(g^{-1})$ undoes the first step. $\square$

**Theorem (Averaging projection).** Let $G$ be a finite group of order $n$ with $n$ invertible in $k$, and put $e = \frac{1}{n}\sum_{g \in G} e_g \in k[G]$. The map $P = \rho(e) \colon v \mapsto \frac{1}{n} \sum_g g v$ is a projection of $V$ onto $V^G$: its image is $V^G$ and $P v = v$ for $v \in V^G$. In particular $V = V^G \oplus \ker P$, and both summands are subrepresentations.

*Proof.* For $h \in G$, the map $g \mapsto hg$ is a bijection of $G$, so $e_h e = \frac{1}{n}\sum_g e_{hg} = e$. Hence $h P v = \rho(e_h e) v = P v$, and $Pv \in V^G$. If $v \in V^G$, then $Pv = \frac{1}{n} \sum_g v = \frac{1}{n} (n v) = v$. So $P^2 = P$ with image $V^G$, and $V = \operatorname{im} P \oplus \ker P$ by the usual argument: $v = Pv + (v - Pv)$ and $P(v - Pv) = 0$, while $\operatorname{im} P \cap \ker P = 0$ because $P$ is the identity on its image. The relation $e e_h = e$ also holds, so $P$ commutes with each $\rho(h)$; therefore $P$ is an intertwining map and its kernel is a subrepresentation. $\square$

**Proposition (Duals, tensors and linear maps).** Let $G$ be a group and $V$, $W$ representations. The canonical map $\Phi \colon V^* \otimes W \to \mathrm{Hom}_k(V, W)$, $\lambda \otimes w \mapsto (v \mapsto \lambda(v) w)$, is an intertwining map. If $V$ is free of finite rank, it is an equivalence.

*Proof.* Compute both sides on $\lambda \otimes w$ at a vector $v$. First, $g(\lambda \otimes w) = (\lambda \circ \rho(g^{-1})) \otimes gw$, and $\Phi$ of it sends $v$ to $\lambda(g^{-1} v)\, g w$. Second, $g \cdot \Phi(\lambda \otimes w)$ sends $v$ to $\sigma(g)\big(\lambda(\rho(g^{-1})v) w\big) = \lambda(g^{-1} v)\, g w$. The two agree, and both sides are additive in the tensor, so $\Phi$ intertwines. If $V$ is free with basis $v_1, \dots, v_d$ and dual basis $\lambda_1, \dots, \lambda_d$, the map $f \mapsto \sum_i \lambda_i \otimes f(v_i)$ is inverse to $\Phi$, by evaluation on the basis. A bijective intertwining map is an equivalence by the earlier proposition. $\square$

**Proposition (Maps out of the regular representation).** For each representation $V$ of a monoid $G$, the map $\mathrm{Hom}_G(k[G], V) \to V$, $f \mapsto f(e_1)$, is an isomorphism of $k$-modules. Its inverse sends $v$ to the map $e_g \mapsto g v$.

*Proof.* An intertwining map $f$ satisfies $f(e_g) = f(g e_1) = g f(e_1)$, so it is determined by $f(e_1)$; this gives injectivity. Given $v$, the linear map $f_v(e_g) = gv$ intertwines, because $f_v(h e_g) = f_v(e_{hg}) = hg v = h f_v(e_g)$, and $f_v(e_1) = v$. So the map is surjective, and it is $k$-linear by definition. $\square$

### Examples

**Example (The permutation representation of $S_3$).** Let $S_3$ act on $V = \mathbb{Q}^3$ by $\sigma e_i = e_{\sigma(i)}$. The transposition $(1\,2)$ and the cycle $(1\,2\,3)$ act by the matrices
$$\rho((1\,2)) = \begin{pmatrix} 0 & 1 & 0 \\ 1 & 0 & 0 \\ 0 & 0 & 1 \end{pmatrix}, \qquad \rho((1\,2\,3)) = \begin{pmatrix} 0 & 0 & 1 \\ 1 & 0 & 0 \\ 0 & 1 & 0 \end{pmatrix}.$$
A vector is invariant if and only if its three coordinates are equal, so $V^{S_3} = \mathbb{Q}(1,1,1)$. The averaging projection sends $e_1$ to $\frac{1}{6}\sum_\sigma e_{\sigma(1)}$; each $e_j$ occurs twice, so $P e_1 = \frac{1}{3}(1,1,1)$, and $P$ is the matrix with each entry $\frac{1}{3}$. Its kernel is $W = \{x : x_1 + x_2 + x_3 = 0\}$, and $\mathbb{Q}^3 = \mathbb{Q}(1,1,1) \oplus W$ as representations.

**Example (The sign representation).** The sign $\operatorname{sgn} \colon S_3 \to \{\pm 1\}$ of Volume 5, Chapter 7, gives a representation on $\mathbb{Q}$ with $\sigma \cdot x = \operatorname{sgn}(\sigma) x$. Its invariants are $0$, since $(1\,2) x = -x$. The tensor product of the sign with itself is trivial, because $\operatorname{sgn}(\sigma)^2 = 1$. An intertwining map from the sign to the trivial representation is a scalar $c$ with $c \cdot (-1) = 1 \cdot c$, so $c = 0$, which shows that the two are not equivalent.

**Counterexample (No invariant complement).** Let $G = \mathbb{Z}$ act on $\mathbb{Q}^2$ by $m \mapsto \begin{pmatrix} 1 & m \\ 0 & 1 \end{pmatrix}$. The line $L = \mathbb{Q} e_1$ is a subrepresentation and is the space of invariants. A complement of $L$ that is a subrepresentation would be a line spanned by an eigenvector outside $L$, but the only eigenvectors of the matrix for $m = 1$ lie in $L$. So $L$ has no invariant complement. The averaging projection does not exist here because $G$ is infinite.

### The library around it

::: mathlib
`Representation` · `Mathlib.RepresentationTheory.Basic`

`Representation k G V` is `G →* (V →ₗ[k] V)`, for a semiring `k`, a monoid `G` and a `k`-module `V`. `Representation.trivial k G V` is the trivial one, and the class `IsTrivial ρ` records that each `ρ g` is the identity. `ofMulAction k G H` is the permutation representation on `k[H]` for a `MulAction G H`, with `ofMulAction_single : ofMulAction k G H g (single x r) = single (g • x) r`, and `leftRegular k G` is the case `H = G`. The constructions are `directSum`, `prod`, `tprod` (notation `ρV ⊗ ρW` in the file, with `tprod_apply`), `linHom` with `linHom_apply : linHom ρV ρW g f = ρW g ∘ₗ f ∘ₗ ρV g⁻¹`, and `dual` with `dual_apply`. The lemma `dualTensorHom_comm` is the proposition on duals, and `Representation.Equiv.dualTensorHom` (in `Intertwining`) packages it as an equivalence. `subrepresentation` and `quotient` restrict to and pass to the quotient by a stable submodule.

<?decl Representation?>
:::

::: mathlib
`Representation.asAlgebraHom` · `Mathlib.RepresentationTheory.Basic`

`asAlgebraHom ρ : k[G] →ₐ[k] Module.End k V` is the map $\tilde\rho$ of the first proposition, defined by `MonoidAlgebra.lift`, with `asAlgebraHom_single : asAlgebraHom ρ (single g r) = r • ρ g`. The module itself lives on a type synonym: `ρ.asModule` is `V` with the instance `Module k[G] ρ.asModule`, and `asModuleEquiv : ρ.asModule ≃ₗ[k] V` moves elements between the two types. Conversely, `ofModule M` is the representation on `RestrictScalars k k[G] M` of a `k[G]`-module `M`.

<?decl Representation.asAlgebraHom?>
:::

::: mathlib
`Representation.IntertwiningMap` · `Mathlib.RepresentationTheory.Intertwining`

`IntertwiningMap ρ σ` extends `V →ₗ[A] W` with the field `isIntertwining' g : toLinearMap ∘ₗ ρ g = σ g ∘ₗ toLinearMap`; the unbundled predicate is `IsIntertwiningMap ρ σ f`. It has `comp`, `ker` and `range` (the last two are `Subrepresentation`s), maps for products and `tensor` for tensor products. `IntertwiningMap ρ ρ` is an `A`-algebra, and `equivAlgEnd` identifies it with the endomorphisms of `ρ.asModule`. `equivLinearMapAsModule : IntertwiningMap ρ σ ≃ₗ[A] (ρ.asModule →ₗ[A[G]] σ.asModule)` is the second proposition. `Representation.Equiv ρ σ` extends both `IntertwiningMap ρ σ` and `V ≃ₗ[A] W`; it is built by `Equiv.mk` from a linear equivalence that commutes with the actions, or by `IntertwiningMap.ofBijective` from a bijective intertwining map, and `Equiv.symm` is the inverse. `Equiv.conj_apply_self` says that conjugation by an equivalence carries `ρ g` to `σ g`.

<?decl Representation.IntertwiningMap?>
:::

::: mathlib
`Subrepresentation.subrepresentationSubmoduleOrderIso` · `Mathlib.RepresentationTheory.Subrepresentation`

`Subrepresentation ρ` is a structure with a submodule `toSubmodule` and the field `apply_mem_toSubmodule`. It is a bounded lattice, `toRepresentation` is the restricted representation and `Subrepresentation.quotient` the quotient one. The order isomorphism `subrepresentationSubmoduleOrderIso : Subrepresentation ρ ≃o Submodule k[G] ρ.asModule` is the second half of the second proposition. In the module `Submodule`, `ρ.invtSubmodule` is the lattice of submodules invariant under each `ρ g`, and `mapSubmodule` matches it with the `k[G]`-submodules.

<?decl Subrepresentation.subrepresentationSubmoduleOrderIso?>
:::

::: mathlib
`Representation.isProj_averageMap` · `Mathlib.RepresentationTheory.Invariants`

`invariants ρ : Submodule k V` has `mem_invariants : v ∈ invariants ρ ↔ ∀ g, ρ g v = v`. Under `[Fintype G] [Invertible (Fintype.card G : k)]`, `GroupAlgebra.average k G` is the element $e$ of the theorem, `averageMap ρ = asAlgebraHom ρ (average k G)`, and `averageMap_invariant`, `averageMap_id` and `isProj_averageMap : LinearMap.IsProj ρ.invariants ρ.averageMap` are its two halves. `invariantsEquivIntertwiningMap : (linHom ρ σ).invariants ≃ₗ[k] IntertwiningMap ρ σ` is the proposition on invariants of `Hom`, and `mem_linHom_invariants_iff_isIntertwining` is its pointwise form.

<?decl Representation.isProj_averageMap?>
:::

::: mathlib
`Representation.leftRegularMapEquiv` · `Mathlib.RepresentationTheory.Equiv`

`leftRegularMapEquiv σ : (leftRegular k G).IntertwiningMap σ ≃ₗ[k] V` is the last proposition, and `freeLiftLEquiv` is its version for the free representation `free k G α` on `α →₀ k[G]`: intertwining maps out of it are functions `α → V`. The file also gives `ofMulActionSubsingletonEquivTrivial`: the permutation representation on a one-point set is trivial.

<?decl Representation.leftRegularMapEquiv?>
:::

Common errors of a learner: The first error is to apply a `k[G]`-scalar to an element of `V` directly; the instance `Module k[G]` lives on `ρ.asModule`, so the element must first pass through `ρ.asModuleEquiv.symm`. The second error is to forget the inverse in `linHom` and `dual`; the formula `ρW g ∘ₗ f ∘ₗ ρV g⁻¹` needs a group, and these constructions do not exist for a monoid. The third error is to look for `invariants` and the averaging map over a semiring; they need `CommRing k` and a group, and the averaging map needs `Invertible (Fintype.card G : k)`, which fails for $\mathbb{Z}/p$ over $\mathbb{F}_p$.

### Exercises

1. (A) Show that the permutation representation of $S_3$ on $\mathbb{Q}^3$ is equivalent to its dual. Hint: the permutation matrices are orthogonal, so $\rho(g^{-1})^{T} = \rho(g)$.
2. (A) Let $G$ act on a finite set $X$. Show that the invariants of the permutation representation on $k[X]$ have a basis indexed by the orbits of $G$ on $X$. Hint: an invariant vector has constant coefficients on each orbit.
3. (A) Find all intertwining maps from the trivial representation of $S_3$ on $\mathbb{Q}$ to the permutation representation on $\mathbb{Q}^3$. Hint: they correspond to $(\mathbb{Q}^3)^{S_3}$.
4. (B) Show that $\mathrm{Hom}_G(V, W)$ is a $k$-submodule of $\mathrm{Hom}_k(V, W)$ and that $\mathrm{Hom}_G(V, V)$ is a $k$-subalgebra. Find $\mathrm{Hom}_{S_3}(\mathbb{Q}^3, \mathbb{Q}^3)$ for the permutation representation. Hint: it has dimension $2$, spanned by the identity and the matrix with each entry $1$.
5. (B) Let $G$ be a group with a normal subgroup $N$, and let $V$ be a representation. Show that $V^N$ is a subrepresentation of $V$ for $G$, and that $G/N$ acts on it. Hint: for $n \in N$ and $v \in V^N$, $n (gv) = g (g^{-1} n g) v = gv$.
6. (C) Let $G = \mathbb{Z}/2$ act on $\mathbb{F}_2^2$ by swapping the coordinates. Show that the invariant line $\mathbb{F}_2(1,1)$ has no invariant complement. Hint: the only other lines are $\mathbb{F}_2(1,0)$ and $\mathbb{F}_2(0,1)$, and $s$ swaps them.

### Notes and history

Frobenius created the theory of group characters in 1896, and he soon reformulated it through matrix representations of finite groups. The view of a representation as a module over the group algebra goes back to Noether in the late 1920s, and it is the view that Mathlib takes through `asModule`.

Mathlib authors, read from their headers: `RepresentationTheory.Basic` and `RepresentationTheory.Invariants` by Antoine Labelle; `RepresentationTheory.Intertwining` by Stepan Nesterov and Edison Xie; `RepresentationTheory.Equiv` by Edison Xie; `RepresentationTheory.Subrepresentation` by the FLT Project; `RepresentationTheory.Submodule` by Oliver Nash.

### Reference

<?reference?>
