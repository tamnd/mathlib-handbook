---
title: Subsemigroups
kind: api
modules:
  - Mathlib.Algebra.Group.Subsemigroup.Defs
  - Mathlib.Algebra.Group.Subsemigroup.Basic
  - Mathlib.Algebra.Group.Subsemigroup.Lemmas
  - Mathlib.Algebra.Group.Subsemigroup.Membership
  - Mathlib.Algebra.Group.Subsemigroup.Operations
explains:
  E2: [Subsemigroup.closure_le, Subsemigroup.closure_induction, Subsemigroup.coe_bot, Subsemigroup.mem_iSup_of_directed, Subsemigroup.map_le_iff_le_comap, Subsemigroup.map_comap_eq, MulHom.srange_eq_top_iff_surjective, MulHom.eqOn_closure, isMulCommutative_iff_of_setLike]
  E1: auto
families: []
requires: [V01.C04, V04.C06, V05.C01, V05.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Subsemigroups

### Overview

A subsemigroup of a magma $M$ is a subset that is closed under the multiplication. It does not have to contain an identity, and $M$ does not have to have one. The library uses subsemigroups as the bottom layer of the tower of substructures. A submonoid is a subsemigroup that contains $1$, and a subgroup is a submonoid that is closed under inverses. Each layer repeats the same API: membership, the complete lattice, the closure of a set, the image and the preimage along a homomorphism, and products.

The five modules of this section build the bottom layer. The first two sections of the chapter treat subgroups, and the next two sections treat submonoids. A reader who knows the subgroup API finds the same names here, with the prefix `Subsemigroup` and with non-unital homomorphisms `M →ₙ* N` in place of `M →* N`. The differences come from the absence of an identity, and this section names them.

### The library around it

#### The structure and the membership classes

The module `Mathlib.Algebra.Group.Subsemigroup.Defs` defines the structure `Subsemigroup M` for a type with `Mul M`. It has a carrier set `Subsemigroup.carrier` and the closure axiom `Subsemigroup.mul_mem'`. The instance `Subsemigroup.instSetLike` makes a subsemigroup a set-like object, so `x ∈ S` and the coercion `↑S : Set M` work as for sets. The user-facing form of the axiom is `Subsemigroup.mul_mem`: if $x \in S$ and $y \in S$, then $x y \in S$. Extensionality is `Subsemigroup.ext`: two subsemigroups with the same members are equal.

The same module defines the class `MulMemClass S M`. It says that every object of a type $S$ of set-like objects is closed under multiplication. Subsemigroups, submonoids, subgroups, subrings and many other structures are instances. The lemma `MulMemClass.mul_mem` states closure once for all of them, and the instances `MulMemClass.toSemigroup` and `MulMemClass.toCommSemigroup` give each such object the induced semigroup structure. The coercion respects the product, by `MulMemClass.coe_mul`. A general lemma with a hypothesis `[MulMemClass S M]` applies to every substructure at once, so the library proves many facts at this level.

The function `Subsemigroup.copy` replaces the carrier by an equal set. It keeps a good definitional form when a construction gives the carrier in a different shape, and `Subsemigroup.copy_eq` says that the copy is equal to the original.

The commutativity of a substructure has its own lemmas. The statement `isMulCommutative_iff_of_setLike` says that the induced multiplication on `↥s` is commutative if and only if $a b = b a$ for all $a, b \in s$. The lemma `isMulCommutative_anti` passes commutativity down to a smaller substructure. For two homomorphisms $f, g$, the set `MulHom.eqLocus f g` of the points where $f$ and $g$ agree is a subsemigroup, by `MulHom.mem_eqLocus`.

#### The lattice and the empty subsemigroup

The subsemigroups of $M$ form a complete lattice under inclusion. The order is the inclusion of carriers. The meet of two subsemigroups is the intersection, by `Subsemigroup.coe_inf`, and the meet of a family is the intersection of the family, by `Subsemigroup.coe_iInf` and `Subsemigroup.coe_sInf`. The top element is all of $M$, by `Subsemigroup.coe_top`.

The bottom element is the first difference with the subgroup layer. The empty set is closed under multiplication, so it is a subsemigroup, and it is the smallest one. The lemma `Subsemigroup.coe_bot` states `↑⊥ = ∅`, and `Subsemigroup.notMem_bot` states that no element is in `⊥`. In the subgroup and submonoid layers the bottom element is $\{1\}$ instead. The instance `Subsemigroup.instNontrivialOfNonempty` says that the lattice has two different elements when $M$ is not empty, because then `⊥ ≠ ⊤`.

#### Closure

The module `Mathlib.Algebra.Group.Subsemigroup.Basic` defines the closure. For a set $s \subseteq M$, `Subsemigroup.closure s` is the smallest subsemigroup that contains $s$. Its members are the finite nonempty products of elements of $s$. The definition is the intersection of all subsemigroups that contain $s$, and `Subsemigroup.mem_closure` unfolds it.

The main property is the Galois connection `Subsemigroup.closure_le`:

$$\operatorname{closure}(s) \le S \iff s \subseteq S.$$

Proof sketch: if the closure is in $S$, then $s$ is in $S$, because $s$ is in its closure by `Subsemigroup.mem_closure_of_mem`. Conversely, if $s \subseteq S$, then $S$ is one of the subsemigroups in the intersection that defines the closure, so the closure is in $S$. The structure `Subsemigroup.gi` packs this as a Galois insertion of the closure into the coercion to sets. From it come `Subsemigroup.closure_mono`, `Subsemigroup.closure_eq` for a set that is already a subsemigroup, `Subsemigroup.closure_union` and `Subsemigroup.closure_iUnion`: the closure of a union is the supremum of the closures. The closure of the empty set is `⊥`, by `Subsemigroup.closure_empty`.

To prove that every element of a closure has a property $p$, use `Subsemigroup.closure_induction`. It needs two cases: $p$ holds on the elements of $s$, and $p$ is closed under products. There is no case for $1$, which is the second difference with the submonoid layer. The variant `Subsemigroup.closure_induction₂` handles a property of two elements, and `Subsemigroup.dense_induction` handles a set whose closure is `⊤`.

The induction gives the uniqueness of extensions. If two homomorphisms agree on $s$, they agree on the closure of $s$, by `MulHom.eqOn_closure`. Proof: the set where they agree is the subsemigroup `MulHom.eqLocus f g`, it contains $s$, so it contains the closure by `Subsemigroup.closure_le`. The construction `MulHom.ofDense` goes the other way: a function on a semigroup that is multiplicative when the right factor is in a generating set is a homomorphism.

#### Suprema of families

The supremum of two subsemigroups is not their union in general. It is the closure of the union, by `Subsemigroup.iSup_eq_closure`. The module `Mathlib.Algebra.Group.Subsemigroup.Membership` treats the case where the union is already closed. A family $S_i$ is directed if any two members lie in a third. Then `Subsemigroup.mem_iSup_of_directed` states

$$x \in \bigsqcup_i S_i \iff \exists i,\ x \in S_i,$$

and `Subsemigroup.coe_iSup_of_directed` states that the carrier of the supremum is the union of the carriers. Proof sketch: the union of a directed family is closed under products, because two elements $x \in S_i$ and $y \in S_j$ lie in a common $S_k$. So the union is a subsemigroup, and it is the supremum. The forms `Subsemigroup.mem_sSup_of_directed_on` and `Subsemigroup.coe_sSup_of_directed_on` do the same for a directed set of subsemigroups. For a family that is not directed, `Subsemigroup.iSup_induction` reduces a property of the supremum to the members and to products.

The module `Mathlib.Algebra.Group.Subsemigroup.Lemmas` has one result, `Subsemigroup.coe_iSup_eq_iUnion_finset_coe_biSup`. It writes the carrier of any supremum as the union, over finite sets of indices, of the finite suprema. The finite suprema form a directed family, so this is the directed case again.

#### Images, preimages and products

The module `Mathlib.Algebra.Group.Subsemigroup.Operations` moves subsemigroups along a non-unital homomorphism $f : M \to_{\mathrm n *} N$. The image `Subsemigroup.map f S` has the carrier $f(S)$, by `Subsemigroup.coe_map`, and the preimage `Subsemigroup.comap f T` has the carrier $f^{-1}(T)$, by `Subsemigroup.coe_comap`. They form a Galois connection, `Subsemigroup.gc_map_comap`, whose working form is `Subsemigroup.map_le_iff_le_comap`:

$$f(S) \le T \iff S \le f^{-1}(T).$$

The proof is the same statement for sets. The usual consequences follow from the Galois connection. The image preserves suprema (`Subsemigroup.map_sup`, `Subsemigroup.map_iSup`), and the preimage preserves infima (`Subsemigroup.comap_inf`, `Subsemigroup.comap_iInf`). For an injective $f$ the pair is a Galois coinsertion, `Subsemigroup.gciMapComap`. For a surjective $f$ it is a Galois insertion, `Subsemigroup.giMapComap`. Lemmas such as `Subsemigroup.map_injective_of_injective` and `Subsemigroup.comap_injective_of_surjective` state the special cases.

The range of $f$ is `MulHom.srange f`. The letter s says "subsemigroup", and it separates this range from the ranges `MonoidHom.mrange` of submonoids and `MonoidHom.range` of subgroups. Its carrier is `Set.range f`, by `MulHom.coe_srange`. The image of a preimage is the intersection with the range, `Subsemigroup.map_comap_eq`:

$$f(f^{-1}(T)) = T \sqcap \operatorname{srange} f.$$

The range is `⊤` exactly when $f$ is surjective, by `MulHom.srange_eq_top_iff_surjective`.

Three restrictions change the domain or the codomain. The map `MulHom.domRestrict` restricts $f$ to a subsemigroup of the domain. The map `MulHom.codRestrict` views $f$ as a map into a subsemigroup that contains all its values. The map `MulHom.srangeRestrict` corestricts $f$ to its range, and it is surjective by `MulHom.srangeRestrict_surjective`. Inclusions of subsemigroups are homomorphisms, by `Subsemigroup.inclusion`. An injective map is an isomorphism onto its image, by `Subsemigroup.equivMapOfInjective`, and a map with a left inverse is an isomorphism onto its range, by `MulEquiv.ofLeftInverse`. The top subsemigroup is isomorphic to $M$, by `Subsemigroup.topEquiv`.

The product of $S \le M$ and $T \le N$ is `Subsemigroup.prod S T`, with carrier $S \times T$ by `Subsemigroup.coe_prod`. The equivalence `Subsemigroup.prodEquiv` identifies the subtype of the product with the product of the subtypes. A product with `⊤` is a preimage under a projection, by `Subsemigroup.prod_top` and `Subsemigroup.top_prod`. The lemma `Subsemigroup.prod_eq_top_iff` needs both factors to be nonempty types, and `Subsemigroup.srange_fst` needs the other factor to be nonempty. These hypotheses come from the empty subsemigroup again: if $N$ is empty, then $M \times N$ is empty and every product is `⊥`.

#### Common errors

1. The bottom subsemigroup is empty, not $\{1\}$. A lemma about submonoids that uses `⊥ = {1}` has no subsemigroup analogue, and some product lemmas need `[Nonempty M]` for this reason. Check `Subsemigroup.coe_bot` before a proof that assumes $1 \in S$.
2. The ranges of the three layers have three names: `MulHom.srange` for subsemigroups, `MonoidHom.mrange` for submonoids and `MonoidHom.range` for subgroups. A search for the word range with the wrong prefix finds the wrong layer. A monoid homomorphism has `MonoidHom.mrange`, and its coercion to `M →ₙ* N` is needed before `MulHom.srange` applies.
3. The supremum of two subsemigroups is the closure of the union, not the union. The equality with the union needs a directed family, as in `Subsemigroup.mem_iSup_of_directed`. For two members, `Subsemigroup.mem_sup_left` and `Subsemigroup.mul_mem_sup` give elements of the supremum, but they do not describe all of them.

### Exercises

1. (A) Prove that `Subsemigroup.closure {x}` in a semigroup consists of the powers $x^n$ with $n \ge 1$. Use `Subsemigroup.closure_induction` for one inclusion and `Subsemigroup.closure_le` for the other.
2. (A) Let $M = \mathbb{N}$ with addition, and let $S$ be the additive subsemigroup of the elements $n \ge 1$. Show that $S$ is not the carrier of an additive submonoid, and compute the closure of $\{2, 3\}$ in this layer.
3. (A) Use `Subsemigroup.map_le_iff_le_comap` to prove that `Subsemigroup.map f (Subsemigroup.comap f T) ≤ T` for every non-unital homomorphism $f$ and every $T$.
4. (B) Prove `Subsemigroup.map_comap_eq`: the image of the preimage of $T$ is $T \sqcap \operatorname{srange} f$. Prove each inclusion with `Subsemigroup.mem_map` and `MulHom.mem_srange`.
5. (B) Give two subsemigroups $S, T$ of the free semigroup on two letters such that the union $S \cup T$ is not a subsemigroup. Then describe the elements of $S \sqcup T$.
6. (C) Let $M$ be a semigroup and $S_i$ a directed family of commutative subsemigroups. Prove that the supremum is commutative. Compare your proof with `Subsemigroup.isMulCommutative_iSup`, and explain why the hypothesis of directedness is necessary.

### Reference

<?reference?>
