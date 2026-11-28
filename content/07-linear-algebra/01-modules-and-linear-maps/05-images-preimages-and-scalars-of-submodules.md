---
title: Images, preimages and restriction of scalars of submodules
kind: api
modules:
  - Mathlib.Algebra.Module.Submodule.Basic
  - Mathlib.Algebra.Module.Submodule.Map
  - Mathlib.Algebra.Module.Submodule.Equiv
  - Mathlib.Algebra.Module.Submodule.LinearMap
  - Mathlib.Algebra.Module.Submodule.EqLocus
  - Mathlib.Algebra.Module.Submodule.Order
  - Mathlib.Algebra.Module.Submodule.Union
  - Mathlib.Algebra.Module.Submodule.Finsupp
  - Mathlib.Algebra.Module.Submodule.IterateMapComap
  - Mathlib.Algebra.Module.Submodule.Invariant
  - Mathlib.Algebra.Module.Submodule.RestrictScalars
explains:
  E2: [Submodule.gc_map_comap, Submodule.map_comap_eq_of_surjective, Submodule.comap_map_eq_of_injective, LinearEquiv.ofInjective, LinearMap.eqLocus_eq_ker_sub, Submodule.exists_forall_notMem_of_forall_ne_top, Module.End.mem_invtSubmodule, Submodule.restrictScalars]
  E1: auto
families: []
requires: [V04, V05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Images, preimages and restriction of scalars of submodules

### Overview

Section 2 defined the image $f(p)$ and the preimage $f^{-1}(q)$ of a submodule under a linear map. This section gives the library that computes with them. The two operations form a Galois connection between the lattices of submodules, and most of the lemmas of `Mathlib.Algebra.Module.Submodule.Map` are consequences of this one fact. The section also treats the maps that a submodule carries: the inclusion, the restriction of a linear map to a submodule, and the linear equivalence between a module and the image of an injective map. It ends with three topics that use these tools: the submodules that an endomorphism leaves invariant, the restriction of scalars along a tower $S \to R$, and the fact that a vector space over an infinite field is not a finite union of proper subspaces.

### The library around it

#### Image and preimage

For a semilinear map $f : M \to M_2$ and submodules $p \le M$, $q \le M_2$, the image is `Submodule.map f p` and the preimage is `Submodule.comap f q`. The membership lemmas are `Submodule.mem_map : x ∈ map f p ↔ ∃ y ∈ p, f y = x` and `Submodule.mem_comap : x ∈ comap f q ↔ f x ∈ q`. The carriers are the set image and the set preimage: `Submodule.map_coe` and `Submodule.comap_coe`.

**Theorem (Galois connection).** $f(p) \le q$ if and only if $p \le f^{-1}(q)$.

*Proof.* Both sides say that $f(x) \in q$ for each $x \in p$. $\square$

This is `Submodule.gc_map_comap`. A Galois connection gives a family of results for free. The image preserves joins, and the preimage preserves meets:

| Lean name | Statement |
|---|---|
| `Submodule.map_sup` | $f(p \sqcup p') = f(p) \sqcup f(p')$ |
| `Submodule.map_iSup` | $f(\bigsqcup_i p_i) = \bigsqcup_i f(p_i)$ |
| `Submodule.map_bot` | $f(0) = 0$ |
| `Submodule.comap_inf` | $f^{-1}(q \sqcap q') = f^{-1}(q) \sqcap f^{-1}(q')$ |
| `Submodule.comap_iInf` | $f^{-1}(\bigsqcap_i q_i) = \bigsqcap_i f^{-1}(q_i)$ |
| `Submodule.comap_top` | $f^{-1}(M_2) = M$ |
| `Submodule.le_comap_map` | $p \le f^{-1}(f(p))$ |
| `Submodule.map_comap_le` | $f(f^{-1}(q)) \le q$ |
| `Submodule.map_mono`, `Submodule.comap_mono` | both operations are monotone |

The other direction fails in general: `Submodule.map_inf_le` only gives $f(p \sqcap q) \le f(p) \sqcap f(q)$. The two lines of $\mathbb{R}^2$ spanned by $(1, 0)$ and $(1, 1)$ meet in $0$, but the projection to the first coordinate sends both onto the same line.

The functorial lemmas are `Submodule.map_id`, `Submodule.map_comp`, `Submodule.comap_id` and `Submodule.comap_comp`. The lemmas `Submodule.map_zero`, `Submodule.comap_zero`, `Submodule.map_neg`, `Submodule.map_smul` and `Submodule.map_add_le` describe the effect of the operations of the module of linear maps.

#### Injective and surjective maps

**Theorem.** If $f$ is surjective, then $f(f^{-1}(q)) = q$ for each $q \le M_2$. If $f$ is injective, then $f^{-1}(f(p)) = p$ for each $p \le M$.

*Proof.* For the first claim, let $y \in q$. Since $f$ is surjective, $y = f(x)$ for some $x$, and then $x \in f^{-1}(q)$. So $q \le f(f^{-1}(q))$, and the other inclusion is `Submodule.map_comap_le`. For the second claim, let $x \in f^{-1}(f(p))$. Then $f(x) = f(y)$ for some $y \in p$, and injectivity gives $x = y \in p$. $\square$

These are `Submodule.map_comap_eq_of_surjective` and `Submodule.comap_map_eq_of_injective`. In the language of order theory, a surjective $f$ gives a Galois insertion, `Submodule.giMapComap`, and an injective $f$ gives a Galois coinsertion, `Submodule.gciMapComap`. The consequences have names of the form `..._of_surjective` and `..._of_injective`: `Submodule.map_injective_of_injective`, `Submodule.comap_injective_of_surjective`, `Submodule.map_inf` (for injective $f$), `Submodule.map_le_map_iff_of_injective` and `Submodule.comap_le_comap_iff_of_surjective`. For a linear equivalence $e$, the image is the preimage under $e^{-1}$ (`Submodule.map_equiv_eq_comap_symm`), and `Submodule.orderIsoMapComap e` is the order isomorphism of the two lattices of submodules.

#### The inclusion and the restrictions

A submodule $p$ is a module, and its inclusion is the linear map `Submodule.subtype p : p →ₗ[R] M`, written `p.subtype`. It is injective (`Submodule.subtype_injective`). For $p \le p'$, the map `Submodule.inclusion h : p →ₗ[R] p'` is the inclusion between two submodules, and `Submodule.subtype_comp_inclusion` says that it commutes with the inclusions into $M$.

A linear map has three restrictions, all in `Mathlib.Algebra.Module.Submodule.LinearMap`:

| Lean name | Map | Condition |
|---|---|---|
| `LinearMap.domRestrict f p` | $p \to M_2$ | none |
| `LinearMap.codRestrict q f h` | $M \to q$ | $f(x) \in q$ for each $x$ |
| `LinearMap.restrict f h` | $p \to q$ | $f$ maps $p$ into $q$ |

The rewriting lemmas `LinearMap.subtype_comp_codRestrict`, `LinearMap.restrict_comp` and `LinearMap.restrict_eq_codRestrict_domRestrict` connect them. For an endomorphism with an invariant submodule $p$, `Module.End.pow_restrict` says that the restriction of $f^n$ is the $n$-th power of the restriction. The file `Mathlib.Algebra.Module.Submodule.Map` gives the image and preimage of submodules under these restrictions, such as `LinearMap.map_domRestrict` and `LinearMap.comap_restrict`. A submodule $p$ of $M$ also gives the submodule `Submodule.submoduleOf p q` of the module $q$, its trace on $q$, with `Submodule.submoduleOfEquivInf` to $q \sqcap p$.

#### Linear equivalences with images

**Theorem.** An injective linear map $f : M \to M_2$ is a linear equivalence from $M$ onto its range.

*Proof.* The map $M \to \operatorname{im} f$, $x \mapsto f(x)$, is linear and surjective by the definition of the range. It is injective since $f$ is. A bijective linear map has a linear inverse by Section 2. $\square$

This is `LinearEquiv.ofInjective` in `Mathlib.Algebra.Module.Submodule.Equiv`. The same file has the variants:

| Lean name | Equivalence |
|---|---|
| `LinearEquiv.ofBijective f h` | $M \simeq M_2$ for a bijective $f$ |
| `LinearEquiv.ofLeftInverse h` | $M \simeq \operatorname{im} f$ from a left inverse $g$ of $f$ |
| `LinearEquiv.ofEq p q h` | $p \simeq q$ for $p = q$ |
| `LinearEquiv.ofTop p h` | $p \simeq M$ for $p = \top$ |
| `LinearEquiv.ofSubmodules e p q h` | $p \simeq q$ when $e(p) = q$ |
| `Submodule.equivMapOfInjective f h p` | $p \simeq f(p)$ for an injective $f$ |
| `Submodule.equivSubtypeMap p q` | $q \simeq p.subtype(q)$ for $q \le p$ as a submodule of $p$ |

The map `LinearEquiv.ofEq` is the form to use when two submodules are equal by a proof and not by definition. A rewrite with the equality $p = q$ inside a type `↥p` often fails, and `LinearEquiv.ofEq` avoids it.

The definition `LinearMap.codRestrictOfInjective` lifts a map $f : M_1 \to M_3$ through an injective map $i : M_2 \to M_3$ whose range contains the range of $f$.

#### The equalizer of two maps

For two linear maps $f, g : M \to M_2$, the set $\{x : f(x) = g(x)\}$ is a submodule, `LinearMap.eqLocus f g`, in `Mathlib.Algebra.Module.Submodule.EqLocus`. The membership lemma is `LinearMap.mem_eqLocus`. Over a ring, `LinearMap.eqLocus_eq_ker_sub` says that it is the kernel of $f - g$, since $f(x) = g(x)$ if and only if $(f - g)(x) = 0$. The lemma `LinearMap.le_eqLocus` says that $p$ lies in the equalizer if and only if $f$ and $g$ agree on $p$, and `LinearMap.eqOn_sup` says that maps that agree on $p$ and on $q$ agree on $p \sqcup q$. The consequence `LinearMap.ext_on_codisjoint` says that two maps that agree on two submodules with sum $M$ are equal.

#### Invariant submodules

A submodule $p$ is invariant under an endomorphism $f$ if $f(p) \le p$. Mathlib collects these submodules into `Module.End.invtSubmodule f`, a sublattice of the lattice of submodules, in `Mathlib.Algebra.Module.Submodule.Invariant`. The lemma `Module.End.mem_invtSubmodule` states $p \in \operatorname{invt}(f) \iff p \le f^{-1}(p)$, and `Module.End.mem_invtSubmodule_iff_map_le` and `Module.End.mem_invtSubmodule_iff_forall_mem_of_mem` are the other two forms. The sublattice contains $0$ and $M$, and it is closed under $\sqcup$ and $\sqcap$ (`Module.End.invtSubmodule.sup_mem`, `Module.End.invtSubmodule.inf_mem`). A submodule invariant under $f$ and $g$ is invariant under $f + g$, $f g$ and $c f$ (`Module.End.invtSubmodule.mul`, `Module.End.invtSubmodule_le_invtSubmodule_smul`). The identity and the zero map leave every submodule invariant: `Module.End.invtSubmodule.id` and `Module.End.invtSubmodule.zero`. A conjugate $e f e^{-1}$ has the invariant submodules $e(p)$ (`LinearEquiv.map_mem_invtSubmodule_conj_iff`). The order notions agree with those of the full lattice: `Module.End.invtSubmodule.isCompl_iff` says that two invariant submodules are complements in the sublattice exactly when they are complements in the lattice of all submodules. These invariant subspaces are the start of the theory of eigenspaces in Chapter 5.

The file `Mathlib.Algebra.Module.Submodule.IterateMapComap` has a technical tool for the strong rank condition of Chapter 2. For two maps $f, i : N \to M$ and $K \le N$, `LinearMap.iterateMapComap f i n K` is $f^{-1}(i(\cdots f^{-1}(i(K))))$ with $n$ steps. If $f$ is surjective, $i$ is injective and two consecutive terms agree, then $\ker f \le K$ (`LinearMap.ker_le_of_iterateMapComap_eq_succ`).

#### Restriction of scalars

Let $S \to R$ be a scalar tower on $M$, for example $\mathbb{R} \subseteq \mathbb{C}$ acting on a complex vector space. An $R$-submodule is also an $S$-submodule. This is `Submodule.restrictScalars S p`, in `Mathlib.Algebra.Module.Submodule.RestrictScalars`. It has the same carrier (`Submodule.restrictScalars_mem`), and it is injective and order preserving: `Submodule.restrictScalarsEmbedding` is an order embedding, and `Submodule.restrictScalarsLatticeHom` is a complete lattice map. So it commutes with $\sqcup$, $\sqcap$, $\bigsqcup$ and $\bigsqcap$ (`Submodule.restrictScalars_sup`, `Submodule.restrictScalars_iInf`). The restricted submodule keeps its $R$-module structure by the instance `Submodule.restrictScalars.origModule`, and `Submodule.restrictScalarsEquiv` is the $R$-linear identity between the two. Not every $S$-submodule is of this form: the real line $\mathbb{R} \subseteq \mathbb{C}$ is an $\mathbb{R}$-submodule that is not a $\mathbb{C}$-submodule.

The case $S = \mathbb{Z}$ is a bridge to group theory. `AddSubgroup.toIntSubmodule` is the order isomorphism between the additive subgroups and the $\mathbb{Z}$-submodules, and `Submodule.toIntSubmodule_toAddSubgroup` says that it agrees with the restriction of scalars. The file `Mathlib.Algebra.Module.Submodule.Basic` has the forgetful maps `Submodule.toAddSubmonoid` and `Submodule.toAddSubgroup`, which are injective and strictly monotone (`Submodule.toAddSubgroup_strictMono`). It also has the abbreviation `Subspace R M` for a submodule over a division ring, the closure lemmas `Submodule.sum_mem` and `Submodule.sum_smul_mem`, and `Submodule.smul_mem_iff`: over a division ring, $s x \in p \iff x \in p$ for $s \ne 0$. The file `Mathlib.Algebra.Module.Submodule.Order` makes a submodule of an ordered module an ordered monoid. The file `Mathlib.Algebra.Module.Submodule.Finsupp` defines the product $s \cdot N$ of a set of scalars and a submodule, with `Submodule.mem_set_smul`: an element of $s \cdot N$ is a finite sum $\sum r_i x_i$ with $r_i \in s$ and $x_i \in N$.

#### Unions of subspaces

**Theorem.** Let $V$ be a vector space over an infinite field $K$, and let $p_1, \dots, p_n$ be proper subspaces. Then some $x \in V$ lies in no $p_i$.

*Proof.* Use induction on $n$. The case $n = 1$ is the fact that $p_1 \ne V$. For $n \ge 2$, the induction hypothesis gives $x \notin p_1 \cup \dots \cup p_{n-1}$. If $x \notin p_n$, the proof is done. Otherwise pick $y \notin p_n$, by $n = 1$. Consider the vectors $y + t x$ for $t \in K$. None of them lies in $p_n$, since $x \in p_n$ and $y \notin p_n$. If $y + t x$ and $y + t' x$ lie in the same $p_i$ with $t \ne t'$, then $(t - t') x \in p_i$, so $x \in p_i$, which is false for $i < n$. So each $p_i$ with $i < n$ contains at most one of these vectors. Since $K$ is infinite, some $y + t x$ lies in no $p_i$. $\square$

This is `Submodule.exists_forall_notMem_of_forall_ne_top` in `Mathlib.Algebra.Module.Submodule.Union`. The finer form `Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt` needs only that $n$ is less than the number of elements of $K$. The dual forms are `Module.exists_dual_forall_apply_ne_zero`, which gives one linear form that is nonzero at finitely many nonzero vectors, and `Module.Dual.exists_forall_ne_zero_of_forall_exists`. Over a finite field the theorem fails: $\mathbb{F}_2^2$ is the union of its three lines.

#### Common errors

1. Expecting `map f (p ⊓ q) = map f p ⊓ map f q` without injectivity. Only `Submodule.map_inf_le` holds in general. In the same way `comap` preserves meets but not joins.
2. Rewriting with an equality $p = q$ inside a type `↥p`. The rewrite produces a motive that is not type correct. Use `LinearEquiv.ofEq p q h` to move elements between the two types.
3. Confusing `LinearMap.domRestrict`, `LinearMap.codRestrict` and `LinearMap.restrict`. The first changes the domain only and needs no proof. The second changes the codomain and needs a proof that the values lie in $q$. The third changes both and needs a proof that $f$ maps $p$ into $q$.

### Exercises

1. (A) Let $f : \mathbb{Q}^3 \to \mathbb{Q}^2$, $f(x, y, z) = (x + y, y + z)$. Compute $f(p)$ for $p = \mathbb{Q}(1, -1, 1)$ and $f^{-1}(q)$ for $q = \mathbb{Q}(1, 0)$.
2. (A) Use the Galois connection to prove $f(p \sqcup p') = f(p) \sqcup f(p')$ without elements.
3. (B) Find a linear map $f$ and submodules $q, q'$ with $f^{-1}(q \sqcup q') \ne f^{-1}(q) \sqcup f^{-1}(q')$.
4. (B) Let $f$ be the endomorphism of $\mathbb{R}^2$ with matrix $\begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$. Find all invariant submodules of $f$, and show that the sublattice `Module.End.invtSubmodule f` has no pair of complements other than $0$ and $\mathbb{R}^2$.
5. (B) Show that $\mathbb{F}_p^2$ is the union of its $p + 1$ lines, and that it is not the union of $p$ proper subspaces.
6. (C) Let $V$ be a vector space over an infinite field, and let $W_1, \dots, W_n$ be subspaces of the same finite dimension $k$. Show that they have a common complement. Hint: choose the vectors of the complement one at a time with the theorem on unions.

### Reference

<?reference?>
