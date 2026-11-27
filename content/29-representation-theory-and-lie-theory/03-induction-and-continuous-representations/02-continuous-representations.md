---
title: Continuous representations
kind: theory
modules:
  - Mathlib.RepresentationTheory.Continuous.Basic
  - Mathlib.RepresentationTheory.Continuous.TopRep
explains:
  E3: [ContRepresentation, ContIntertwiningMap, ContRepresentation.coind, ContRepresentation.coind₁, ContRepresentation.coind₁ι, ContRepresentation.coindEquivCoind₁, TopRep, TopRep.TopRepEquivActionTop]
  E2: [ContRepresentation.ofMonoidHom, ContRepresentation.toMonoidHom, ContRepresentation.toRepresentation, ContIntertwiningMap.toIntertwiningMap, ContIntertwiningMap.id, ContIntertwiningMap.comp, ContRepresentation.Equiv, ContRepresentation.trivial, ContRepresentation.trivial_apply, ContRepresentation.restrict, ContRepresentation.invariants, ContRepresentation.mem_invariants, ContIntertwiningMap.mapInvariants, ContIntertwiningMap.mapInvariantsOfRes, ContRepresentation.coindV, ContRepresentation.mem_coindV, ContRepresentation.coind_apply_coe_apply, ContRepresentation.coind₁_apply_apply, ContRepresentation.coind₁Map, ContRepresentation.coindLEquivCoind₁, ContRepresentation.coind₁Res, ContRepresentation.coind₁ResMap, TopRep.of, TopRep.Hom, TopRep.ofHom, TopRep.hom_comm_apply, TopRep.toActionTopModFunc, TopRep.fromActionTopModFunc, TopRep.invariants, TopRep.invariantsFunctor, TopRep.coind₁, TopRep.coind₁Functor, TopRep.coind₁ι, TopRep.res, TopRep.resFunctor, TopRep.invariantsResMap]
  E1: auto
families: []
requires: [V13.C01, V13.C05, V14.C01, V14.C02, V24.C02, V29.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Continuous representations

### Overview

The groups of analysis and number theory carry a topology: the circle, the real line, the group $\mathbb{Z}_p$ of $p$-adic integers, and Galois groups of infinite extensions. Their representations live on topological modules, such as $\mathbb{C}^n$, Banach spaces and $p$-adic vector spaces. A representation of such a group is useful only if it respects both topologies. For a Galois group, the continuous representations are the ones that number theory studies, and continuous group cohomology is built from them.

Mathlib separates two conditions that the textbooks put together. In Mathlib, a continuous representation asks that each element $g$ acts by a continuous linear map. The group $G$ need not have a topology, and the action map $G \times V \to V$ need not be continuous. When a theorem needs the joint continuity, Mathlib states it as a hypothesis. This section explains the definition, the morphisms, invariants and restriction, the two coinduction constructions, and the category `TopRep k G` with its equivalence to the category of actions on topological modules. The examples are characters of the circle, a pathological action of $\mathbb{R}$, and representations of profinite groups through finite quotients.

Throughout, $R$ or $k$ is a topological ring and $V$, $W$ are $R$-modules that are topological additive groups with continuous scalar multiplication. The space $C(X, V)$ of continuous maps carries the compact-open topology (Volume 13).

### Definitions

**Definition (Continuous representation).** A continuous representation of a monoid $G$ on $V$ is a monoid homomorphism $\pi \colon G \to \mathrm{End}^{\mathrm{c}}_R(V)$ into the monoid of continuous $R$-linear maps $V \to V$.

Forgetting continuity gives a representation in the sense of Chapter 1. If $G$ is a topological group, the classical definition asks in addition that the map $G \times V \to V$, $(g, v) \mapsto \pi(g)v$, be continuous. This section calls such a $\pi$ jointly continuous. For finite dimensional $V$ over $\mathbb{R}$ or $\mathbb{C}$, joint continuity is the same as continuity of the homomorphism $G \to \mathrm{GL}_n$.

**Definition (Continuous intertwining map).** For continuous representations $\pi_1$ on $V$ and $\pi_2$ on $W$, a continuous intertwining map is a continuous linear map $f \colon V \to W$ with $f \circ \pi_1(g) = \pi_2(g) \circ f$ for each $g$. An equivalence is an intertwining map that is a homeomorphism.

**Definition (Invariants and restriction).** The invariants of $\pi$ are $V^G = \{ v \mid \pi(g)v = v \text{ for all } g\}$, with the subspace topology. For a monoid homomorphism $\varphi \colon H \to G$, the restriction is $\pi \circ \varphi$.

**Definition (Coinduction).** Let $\varphi \colon G \to H$ be a continuous homomorphism of topological groups, and let $\pi$ be a continuous representation of $G$ on $V$. The coinduced representation acts on
$$\mathrm{Coind}_\varphi V = \{ f \in C(H, V) \mid f(\varphi(g)h) = \pi(g) f(h) \text{ for all } g, h\}$$
by right translation, $(h' \cdot f)(h) = f(hh')$.

**Definition (The module $C(G, V)$ with the twisted action).** For a topological group $G$ and a continuous representation $\pi$, the group $G$ acts on $C(G, V)$ by
$$(g \cdot f)(x) = \pi(g)\big(f(g^{-1}x)\big).$$
This is the representation $\mathrm{coind}_1 \pi$. The map $\iota \colon V \to C(G, V)$ sends $v$ to the constant function with value $v$.

**Definition (Topological representations).** The category `TopRep k G` has as objects the pairs of a topological $k$-module $V$ and a continuous representation of $G$ on $V$. Its morphisms are the continuous intertwining maps.

### Theorems and proofs

**Proposition (Coinduction is a continuous representation).** The formula $(h' \cdot f)(h) = f(hh')$ defines a continuous representation of $H$ on $\mathrm{Coind}_\varphi V$.

*Proof.* The function $h \mapsto f(hh')$ is continuous, since right multiplication by $h'$ is continuous. It satisfies the condition: $f(\varphi(g)hh') = \pi(g)f(hh')$. The map $f \mapsto f \circ r_{h'}$, where $r_{h'}(h) = hh'$, is linear. It is continuous for the compact-open topology, because precomposition with a fixed continuous map is continuous for this topology: the inverse image of the basic open set $\{f \mid f(K) \subseteq U\}$ is $\{f \mid f(Kh') \subseteq U\}$, and $Kh'$ is compact. Finally $h_1 \cdot (h_2 \cdot f)(h) = (h_2 \cdot f)(hh_1) = f(hh_1h_2)$, so the formula is an action. $\square$

**Proposition (The twisted action on $C(G,V)$).** The formula $(g \cdot f)(x) = \pi(g)(f(g^{-1}x))$ defines a continuous representation of $G$ on $C(G, V)$. The map $\iota$ is a continuous injective intertwining map $V \to C(G, V)$.

*Proof.* The function $x \mapsto \pi(g)(f(g^{-1}x))$ is the composite of the continuous maps $x \mapsto g^{-1}x$, $f$ and $\pi(g)$. The map $f \mapsto \pi(g) \circ f \circ \ell_{g^{-1}}$ is linear. It is continuous for the compact-open topology, since precomposition and postcomposition with fixed continuous maps are continuous. It is an action:
$$\big(g \cdot (h \cdot f)\big)(x) = \pi(g)\big(\pi(h) f(h^{-1}g^{-1}x)\big) = \pi(gh)\big(f((gh)^{-1}x)\big).$$
For the map $\iota$: the function $g \cdot \iota(v)$ takes the value $\pi(g)v$ at each point, so $g \cdot \iota(v) = \iota(\pi(g)v)$. The map $\iota$ is linear and injective, and it is continuous because the inverse image of $\{f \mid f(K) \subseteq U\}$ is $U$ for $K$ nonempty, and all of $V$ for $K$ empty. $\square$

The map $\iota$ is the first step of the resolution $0 \to V \to C(G,V) \to C(G, C(G, V)) \to \cdots$ that defines continuous group cohomology. The twist by $\pi(g)$ in the definition makes $\iota$ an intertwining map. Without the twist, constant functions are invariant for right translation, but they do not carry $\pi$.

**Theorem (Untwisting $C(G, V)$).** Let $G$ be a topological group and let $\pi$ be jointly continuous. Let $C(G, V)_{\mathrm{rt}}$ be the space $C(G, V)$ with the right translation action $(h \cdot f)(x) = f(xh)$; this is the coinduction of $V$ along $1 \to G$. Then
$$T(f)(g) = \pi(g)\big(f(g^{-1})\big)$$
is an equivalence of continuous representations $C(G, V)_{\mathrm{rt}} \to \mathrm{coind}_1 \pi$, and $T \circ T = \mathrm{id}$.

*Proof.* First, $T(f)$ is continuous: it is the composite of $g \mapsto (g, f(g^{-1}))$, which is continuous, and the action map $G \times V \to V$, which is continuous by hypothesis. Second, $T$ is an involution: $T(T(f))(g) = \pi(g)\big(\pi(g^{-1}) f(g)\big) = f(g)$. Third, $T$ intertwines the actions. For $h \in G$,
$$T(h \cdot f)(x) = \pi(x)\big(f(x^{-1}h)\big),$$
and in $\mathrm{coind}_1 \pi$,
$$\big(h \cdot T(f)\big)(x) = \pi(h)\big(T(f)(h^{-1}x)\big) = \pi(h)\pi(h^{-1}x)\big(f(x^{-1}h)\big) = \pi(x)\big(f(x^{-1}h)\big).$$
Fourth, $T$ is continuous. Write $T = \Phi \circ c$, where $c(f) = f \circ \mathrm{inv}$ is precomposition with inversion and $\Phi(f)(g) = \pi(g)(f(g))$. The map $c$ is continuous. The map $f \mapsto (\mathrm{id}, f)$ from $C(G, V)$ to $C(G, G \times V)$ is continuous, because the compact-open topology on maps into a product is the product of the compact-open topologies. Postcomposition with the continuous action map $G \times V \to V$ is continuous. So $\Phi$ is continuous. Since $T$ is its own inverse, it is a homeomorphism. $\square$

The hypothesis is needed for the first step. If $\pi$ is not jointly continuous, $g \mapsto \pi(g)v$ can fail to be continuous for a constant $f = v$, and then $T(f) \notin C(G, V)$.

**Proposition (Invariants are closed).** If $V$ is Hausdorff, then $V^G$ is a closed submodule. A continuous intertwining map $f \colon V \to W$ sends $V^G$ into $W^G$, and an intertwining map $f$ from $\pi \circ \varphi$ to $\pi'$ sends $V^G$ into $W^H$.

*Proof.* The set $V^G$ is the intersection over $g$ of the kernels of $\pi(g) - \mathrm{id}$. Each such map is continuous, and $\{0\}$ is closed in a Hausdorff group, so each kernel is closed. If $v \in V^G$, then $\pi'(h) f(v) = f(\pi(\varphi(h)) v) = f(v)$ for each $h \in H$. The first claim of the second sentence is the case $\varphi = \mathrm{id}$. $\square$

**Theorem (Topological representations as actions).** The category `TopRep k G` is equivalent to the category $\mathrm{Action}(\mathrm{TopMod}_k, G)$ of objects of the category of topological $k$-modules with an action of $G$.

*Proof.* An object of $\mathrm{Action}(\mathrm{TopMod}_k, G)$ is a topological $k$-module $X$ with a monoid homomorphism $G \to \mathrm{End}(X)$, where $\mathrm{End}(X)$ is the monoid of endomorphisms of $X$ in $\mathrm{TopMod}_k$. These endomorphisms are the continuous linear maps $X \to X$. So the data of an action is exactly the data of a continuous representation on $X$. A morphism of actions is a continuous linear map that commutes with the action of each $g$, which is a continuous intertwining map. The functor in each direction keeps the underlying module and the maps and changes only the packaging of the data. Both composites are isomorphic to the identity functors by the identity maps of the underlying modules. $\square$

### Examples

**Example (Characters of the circle).** Let $G = \mathbb{T} = \{ z \in \mathbb{C} \mid |z| = 1\}$ and $V = \mathbb{C}$. For $n \in \mathbb{Z}$, $\pi_n(z)v = z^n v$ is a continuous representation, and it is jointly continuous because $(z, v) \mapsto z^n v$ is a polynomial map in $z$, $z^{-1}$ and $v$. Its invariants are $\mathbb{C}$ for $n = 0$ and $0$ for $n \neq 0$, since $z^n = 1$ for all $z \in \mathbb{T}$ only when $n = 0$. Two characters $\pi_m$ and $\pi_n$ with $m \neq n$ are not equivalent: an intertwining map $f(v) = cv$ satisfies $c z^m = z^n c$ for all $z$, so $c = 0$. The jointly continuous characters of $\mathbb{T}$ are exactly the $\pi_n$; this classical fact from harmonic analysis (Volume 19) is not proved here.

**Counterexample (An action that is not continuous in $g$).** Choose a basis of $\mathbb{R}$ as a vector space over $\mathbb{Q}$, which exists by the axiom of choice, and let $a \colon \mathbb{R} \to \mathbb{R}$ be a $\mathbb{Q}$-linear map that sends one basis element $b$ to $1$ and the others to $0$. Then $\pi(t)v = e^{2\pi i\, a(t)}v$ is a homomorphism $\mathbb{R} \to \mathbb{C}^\times$, and each $\pi(t)$ is a continuous linear map of $\mathbb{C}$. So $\pi$ is a continuous representation in the sense of Mathlib. It is not jointly continuous. If it were, $\chi(t) = \pi(t)1$ would be a continuous function of $t$, and its image $\chi(\mathbb{R})$ would be connected. The values of $a$ are rational, so $\chi(\mathbb{R})$ is countable, and it contains $\chi(0) = 1$ and $\chi(b/2) = e^{\pi i} = -1$. The continuous function $z \mapsto |z - 1|$ maps this connected set onto a connected subset of $\mathbb{R}$ that contains $0$ and $2$, hence onto a set that contains $[0, 2]$. This is impossible for a countable set. This example shows why the joint continuity in the untwisting theorem is a separate hypothesis.

**Example (Profinite groups through finite quotients).** Let $N$ be an open normal subgroup of a topological group $G$, and let $\sigma$ be a representation of the finite group $G/N$ on $\mathbb{C}^n$. The composite $\pi(g) = \sigma(gN)$ is jointly continuous. Indeed, on the open coset $g_0N$ the action map equals $(g, v) \mapsto \sigma(g_0N)v$, which is continuous. For $G = \mathbb{Z}_p$, the open subgroups $p^m\mathbb{Z}_p$ give the characters $x \mapsto \zeta^{x \bmod p^m}$ for a $p^m$-th root of unity $\zeta$.

**Proposition (Characters of profinite groups).** Let $G$ be a profinite group and let $\chi \colon G \to \mathbb{C}^\times$ be a continuous homomorphism. Then $\chi$ factors through a finite quotient $G/N$ with $N$ open and normal.

*Proof.* The image $\chi(G)$ is a compact subgroup of $\mathbb{C}^\times$. Its image under $|\cdot|$ is a compact subgroup of $\mathbb{R}_{>0}$, which is $\{1\}$, since $r > 1$ in a subgroup gives the unbounded sequence $r^n$. So $\chi(G) \subseteq \mathbb{T}$. The set $U = \{ z \in \mathbb{T} \mid \mathrm{Re}\, z > 0 \}$ contains no nontrivial subgroup: for $z = e^{i\theta}$ with $0 < |\theta| < \pi/2$, let $n$ be the least integer with $n|\theta| \geq \pi/2$; then $n|\theta| < \pi/2 + |\theta| < \pi$, so $\mathrm{Re}\, z^n \le 0$. The set $\chi^{-1}(U)$ is an open neighbourhood of $1$, and in a profinite group the open subgroups form a base of neighbourhoods of $1$. So it contains an open subgroup $V$, and $\chi(V)$ is a subgroup inside $U$, hence trivial. The open subgroup $V$ has finite index, since its cosets form an open cover of the compact group $G$ with no proper subcover. Its conjugates are finitely many, so their intersection $N$ is open, normal and of finite index, and $\chi$ is trivial on $N$. $\square$

**Example (Coinduction for a finite discrete group).** Let $G = \mathbb{Z}/2$ with the discrete topology and $\pi$ trivial on $V = \mathbb{C}$. Then $C(G, \mathbb{C}) = \mathbb{C}^2$, and the generator acts by $(f(0), f(1)) \mapsto (f(1), f(0))$. This is the regular representation. The image of $\iota$ is the diagonal $\{(v, v)\}$, which is the invariant line.

### The library around it

::: mathlib
`ContRepresentation` · `Mathlib.RepresentationTheory.Continuous.Basic`

`ContRepresentation R G V` is a structure with one field `toMonoidHom : G →* V →L[R] V` and constructor `ofMonoidHom`. The monoid `G` has no topology in the definition. `toRepresentation` forgets continuity, `trivial R G V` is the trivial representation with `trivial_apply`, `restrict` restricts along `H →* G`, and `invariants` is a `Submodule` with `mem_invariants`. `ContRepresentation.Equiv` is the type of equivalences.

<?decl ContRepresentation?>
:::

::: mathlib
`ContIntertwiningMap` · `Mathlib.RepresentationTheory.Continuous.Basic`

`ContIntertwiningMap π₁ π₂`, with notation `π₁ →ⁱL π₂`, extends `V →L[R] W` by the field `isIntertwining'`. It has `id`, `comp`, an additive group structure and `toIntertwiningMap`. `mapInvariants` and `mapInvariantsOfRes φ f` are the continuous linear maps on invariants of the proposition.

<?decl ContIntertwiningMap?>
:::

::: mathlib
`ContRepresentation.coind₁` · `Mathlib.RepresentationTheory.Continuous.Basic`

`coindV φ π` is a submodule of `C(H, V)` for `φ : G →ₜ* H`, with `mem_coindV`, and `coind φ π` acts by right translation under `[IsTopologicalGroup H]`, as `coind_apply_coe_apply` states. `coind₁ π` is the twisted action on `C(G, V)`, with `coind₁_apply_apply`, `coind₁Map` its functoriality and `coind₁ι π` the constant map. `coind₁Res φ π` precomposes with `φ : H →ₜ* G`, and `coind₁ResMap` combines it with an intertwining map. The resolution by `coind₁` is used to define `continuousCohomology`.

<?decl ContRepresentation.coind₁?>
:::

::: mathlib
`ContRepresentation.coindEquivCoind₁` · `Mathlib.RepresentationTheory.Continuous.Basic`

The hypothesis is `hπ : Continuous fun gv : G × V ↦ π gv.1 gv.2`. The result is an equivalence from `(trivial R Unit V).coind (1 : PUnit →ₜ* G)` to `π.coind₁`, and `coindLEquivCoind₁` is the underlying continuous linear equivalence, given by the twist `f ↦ fun g ↦ π g (f g⁻¹)` in both directions. This is the untwisting theorem. An older form `coind₁Equivcoind` is deprecated.

<?decl ContRepresentation.coindEquivCoind₁?>
:::

::: mathlib
`TopRep.TopRepEquivActionTop` · `Mathlib.RepresentationTheory.Continuous.TopRep`

`TopRep k G` bundles a type `V`, five instances (`AddCommGroup`, `Module k`, `TopologicalSpace`, `IsTopologicalAddGroup`, `ContinuousSMul k`) and `ρ : ContRepresentation k G V`. `TopRep.of` builds an object, `TopRep.Hom` wraps a `ContIntertwiningMap`, and `ofHom` and `hom_comm_apply` are the usual interface. The category is preadditive and `k`-linear. `toActionTopModFunc` and `fromActionTopModFunc` are the two functors of the theorem. For a topological group, `invariantsFunctor`, `coind₁Functor`, `coind₁ι`, `resFunctor` and `invariantsResMap` are the categorical forms of the constructions.

<?decl TopRep.TopRepEquivActionTop?>
:::

Common errors of a learner: The first error is to assume that `ContRepresentation` is continuous in `g`. It is not, and a proof that needs the continuity of $g \mapsto \pi(g)v$ must take the joint continuity as a hypothesis, as `coindEquivCoind₁` does. The second error is to confuse `coind₁` with right translation on `C(G, V)`; the two actions agree only after the twist $T$, and only for a jointly continuous $\pi$. The third error is to forget that `coind` takes a continuous homomorphism `G →ₜ* H` and a topological group `H`, while `restrict` takes a plain monoid homomorphism. The fourth error is to expect `invariants` to carry its closedness in its type; it is a plain `Submodule` with the subspace topology.

### Exercises

1. (A) Show that the restriction of a continuous representation along a monoid homomorphism is a continuous representation. Hint: the composite of two monoid homomorphisms is one.
2. (A) For $G = \mathbb{Z}/3$ with the discrete topology and $\pi$ trivial on $\mathbb{C}$, write the matrix of the generator on $\mathrm{coind}_1 \pi = \mathbb{C}^3$ and find its invariants. Hint: the generator permutes the three values of $f$ cyclically.
3. (A) Show that the circle character $\pi_n$ restricted to the subgroup $\mu_m$ of $m$-th roots of unity depends only on $n \bmod m$. Hint: $z^m = 1$ on $\mu_m$.
4. (B) Let $G$ be a topological group and $\pi$ jointly continuous. Show that $g \mapsto \pi(g)v$ is continuous for each $v$, and that the stabilizer of $v$ is closed when $V$ is Hausdorff. Hint: the stabilizer is the inverse image of $\{v\}$.
5. (B) Show that the map $C(G, V) \to V$, $f \mapsto f(1)$, is continuous and that it is a left inverse of $\iota$. Is it an intertwining map for $\mathrm{coind}_1 \pi$? Hint: evaluation at a point is continuous for the compact-open topology; compare $\pi(g)f(g^{-1})$ with $f(1)$.
6. (B) Let $\pi$ be a continuous representation of a profinite group $G$ on $\mathbb{C}^n$. Show that $\pi$ factors through a finite quotient. Hint: $\mathrm{GL}_n(\mathbb{C})$ has a neighbourhood of $1$ that contains no nontrivial subgroup; use the proof for characters.
7. (C) Prove that a continuous character $\chi \colon \mathbb{R} \to \mathbb{T}$ has the form $t \mapsto e^{i\lambda t}$. Hint: on a small interval $\chi$ lifts to a continuous additive map $\mathbb{R} \to \mathbb{R}$ near $0$, and a continuous additive map is linear over $\mathbb{R}$.

### Notes and history

Continuous representations of compact groups appear in the work of Peter and Weyl in 1927, who proved that the matrix coefficients of the finite dimensional irreducible ones span a dense subspace of the continuous functions. Unitary representations of locally compact groups were developed in the following decades by Gelfand, Raikov, Mackey and Harish-Chandra. Galois representations, the continuous representations of absolute Galois groups, are the central objects of modern number theory. The coinduction $C(G, V)$ and its iterates give the standard resolution for continuous cohomology, as in the work of Tate on Galois cohomology.

The Mathlib files are by these authors, read from their headers: `Continuous.Basic` by Edison Xie (the copyright line names Yunzhou Xie); `Continuous.TopRep` by Edison Xie and Richard Hill.

### Reference

<?reference?>
