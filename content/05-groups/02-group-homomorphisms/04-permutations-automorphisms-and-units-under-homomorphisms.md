---
title: Permutations, automorphisms and units under homomorphisms
kind: api
modules:
  - Mathlib.Algebra.Group.End
  - Mathlib.Algebra.Group.Units.Hom
  - Mathlib.Algebra.Group.Units.Equiv
explains:
  E2: [Equiv.Perm.mul_apply, Equiv.Perm.equivUnitsEnd, Equiv.permCongr_eq_mul, Equiv.swap_mul_swap_mul_swap, Units.map, IsUnit.map, isUnit_map_iff, MonoidHom.toHomUnits, Equiv.mulLeft, toUnits]
  E1: auto
families: []
requires: [V01.C03, V05.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Permutations, automorphisms and units under homomorphisms

### Overview

The maps of a set to itself form a monoid under composition, and the bijections form a group. This group is the symmetric group of the set, the model of every group by the theorem of Cayley. The module `Mathlib.Algebra.Group.End` puts these structures on the types `Function.End α` and `Equiv.Perm α`, and it does the same for the automorphisms `MulAut M` of a magma. It also holds the first algebraic lemmas on transpositions and the homomorphisms that build permutations of a large type from permutations of its parts.

The two other modules treat units and homomorphisms. A homomorphism of monoids sends units to units, so it gives a homomorphism of the groups of units. A homomorphism out of a group lands in the units of the target. Some homomorphisms also reflect units, and the class `IsLocalHom` names this property. Finally, the translations of a group are permutations of it, and a group is isomorphic to its own group of units. The section needs the equivalences of Volume 1 and the units of Chapter 1. Chapter 7 uses the permutation group in depth.

### The library around it

#### The monoid of maps and the group of permutations

**Definition (Endomorphisms and permutations).** For a type $\alpha$, `Function.End α` is the type of all maps $\alpha \to \alpha$, with the composite as product and the identity as unit. The group `Equiv.Perm α` is the type of bijections $\alpha \to \alpha$ with the composite as product and the inverse bijection as inverse.

The group instance is `Equiv.Perm.permGroup`. The convention for the product is the one of function composition: $f g$ is "first $g$, then $f$".

**Theorem (Product of permutations).** For $f, g$ in `Equiv.Perm α` and $x \in \alpha$, $(f g)(x) = f(g(x))$. As equivalences, $f g$ is `Equiv.trans g f`.

*Proof.* The product is defined as `Equiv.trans g f`, which applies $g$ first. $\square$

The lemmas are `Equiv.Perm.mul_apply` and `Equiv.Perm.mul_def`. The order in `Equiv.Perm.mul_def` is reversed with respect to `Equiv.trans`, and this is the main trap of the API. The companions are `Equiv.Perm.one_apply`, `Equiv.Perm.inv_def`, which states $f^{-1}$ = `Equiv.symm f`, and `Equiv.Perm.coe_mul` and `Equiv.Perm.coe_one`, which give the underlying functions $f \circ g$ and the identity. The power is the iterate, by `Equiv.Perm.coe_pow`. A point fixed by $f$ is fixed by every power, by `Equiv.Perm.pow_apply_eq_self_of_apply_eq_self` and its integer form `Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self`.

**Theorem (Permutations are the units of the maps).** The group `Equiv.Perm α` is isomorphic to the group of units of the monoid `Function.End α`.

*Proof.* A unit of `Function.End α` is a map $f$ with a two sided inverse $g$ under composition, so $f$ is a bijection with inverse $g$. Conversely, a bijection and its inverse form a unit. Both maps respect the composite. $\square$

The isomorphism is `Equiv.Perm.equivUnitsEnd`. With it, `MonoidHom.toHomPerm` turns an action of a group $G$ by maps, a homomorphism $G \to$ `Function.End α`, into a homomorphism $G \to$ `Equiv.Perm α`: the image of $g$ is invertible, with inverse the image of $g^{-1}$.

#### Conjugation and transpositions

**Theorem (Conjugation of permutations).** For permutations $e, p$ of $\alpha$, the transport of $p$ along $e$ is $e p e^{-1}$.

*Proof.* The transport `Equiv.permCongr e p` sends $x$ to $e(p(e^{-1}(x)))$, which is the value of $e p e^{-1}$ at $x$. $\square$

The lemma is `Equiv.permCongr_eq_mul`. The transport along an equivalence $\alpha \simeq \beta$ is an isomorphism of groups `Equiv.permCongrHom e`, from `Equiv.Perm α` to `Equiv.Perm β`. For transpositions this gives the rule that a conjugate of a transposition is a transposition: `Equiv.swap_apply_apply` states $f \circ (x\ y) \circ f^{-1} = (f(x)\ f(y))$, where $(x\ y)$ is `Equiv.swap x y`. The module has the basic identities:

| Lean name | Statement |
|---|---|
| `Equiv.swap_mul_self` | $(i\ j)(i\ j) = 1$ |
| `Equiv.swap_inv` | $(x\ y)^{-1} = (x\ y)$ |
| `Equiv.swap_eq_one_iff` | $(i\ j) = 1 \iff i = j$ |
| `Equiv.mul_swap_eq_swap_mul` | $f (x\ y) = (f(x)\ f(y)) f$ |
| `Equiv.swap_mul_swap_mul_swap` | $(y\ z)(x\ y)(y\ z) = (z\ x)$ for $x \neq y$, $x \neq z$ |

The last identity follows from the conjugation rule: $(y\ z)$ is its own inverse, so the left side is the conjugate of $(x\ y)$ by $(y\ z)$, which is $((y\ z)(x)\ (y\ z)(y)) = (x\ z) = (z\ x)$. The predicate `Equiv.Perm.IsSwap` states that a permutation is a transposition. Chapter 7 uses these lemmas to prove that transpositions generate the symmetric group.

#### Permutations of parts

Several homomorphisms build a permutation of a large type from permutations of smaller types:

| Lean name | Statement |
|---|---|
| `Equiv.Perm.ofSubtype` | extends a permutation of $\{x \mid p(x)\}$ by the identity outside |
| `Equiv.Perm.extendDomainHom` | extends along an equivalence $\alpha \simeq \{x \mid p(x)\}$ |
| `Equiv.Perm.sumCongrHom` | permutations of $\alpha$ and $\beta$ give one of $\alpha \oplus \beta$ |
| `Equiv.Perm.sigmaCongrRightHom` | a family of permutations of the fibres gives one of the sigma type |

All four are injective, by lemmas such as `Equiv.Perm.ofSubtype_injective` and `Equiv.Perm.extendDomainHom_injective`. In the other direction, `Equiv.Perm.subtypePerm` restricts a permutation to a subset that it preserves. The lemma `Equiv.Perm.ofSubtype_apply_of_not_mem` states that the extension fixes the points outside the subset.

#### Automorphisms and translations

For a magma $M$, `MulAut M` is the type `M ≃* M` of automorphisms, a group with the composite as product, by `MulAut.instGroup`. The lemmas `MulAut.mul_apply`, `MulAut.one_apply` and `MulAut.inv_apply` evaluate the operations. The homomorphism `MulAut.toPerm` forgets that an automorphism respects the product. An isomorphism $G \cong H$ gives an isomorphism of the automorphism groups by `MulAut.congr`. The conjugation homomorphism `MulAut.conj` of a group lives in this module too.

In a group, left multiplication by $a$ is a bijection, by `Group.mulLeft_bijective`. The module `Mathlib.Algebra.Group.Units.Equiv` bundles it as the permutation `Equiv.mulLeft a`, with inverse `Equiv.mulLeft a⁻¹` by `Equiv.mulLeft_symm`. The map $a \mapsto$ `Equiv.mulLeft a` is a homomorphism into `Equiv.Perm G`, by `Equiv.mulLeft_mul` and `Equiv.mulLeft_one`, and this is the embedding of the theorem of Cayley. Right multiplication reverses the order: `Equiv.mulRight_mul` states that the translation by $a b$ is the translation by $b$ composed after the one by $a$, in the order $\operatorname{mulRight}(b) \cdot \operatorname{mulRight}(a)$. The bijections `Equiv.divLeft a` and `Equiv.divRight a` send $b$ to $a / b$ and to $b / a$. In a monoid only the units translate bijectively, and `Units.mulLeft u` and `Units.mulRight u` are the permutations. In a commutative division monoid the inverse is an automorphism, `MulEquiv.inv G`.

#### Units and homomorphisms

**Theorem (Homomorphisms preserve units).** Let $f : M \to N$ be a homomorphism of monoids. If $x$ is a unit of $M$, then $f(x)$ is a unit of $N$. So $f$ restricts to a homomorphism $M^\times \to N^\times$.

*Proof.* If $x y = y x = 1$, then $f(x) f(y) = f(x y) = f(1) = 1$ and $f(y) f(x) = 1$. $\square$

The lemma is `IsUnit.map`, and the homomorphism of units is `Units.map f`, with `Units.coe_map`. The construction is a functor: `Units.map_id` and `Units.map_comp` respect identities and composites. An injective $f$ gives an injective `Units.map f`, by `Units.map_injective`, and a bijective $f$ a bijective one, by `Units.map_bijective`. For an isomorphism, `Units.mapEquiv h` is the isomorphism of the groups of units. The coercion $M^\times \to M$ is the injective homomorphism `Units.coeHom M`. For a homomorphism into a division monoid, `map_units_inv` states $f(u^{-1}) = f(u)^{-1}$.

A homomorphism out of a group sends every element to a unit, because every element of a group is a unit. The construction `MonoidHom.toHomUnits` turns $f : G \to M$ into a homomorphism $G \to M^\times$. When $M$ is commutative, `MonoidHom.toHomUnitsMulEquiv` makes this an isomorphism of the groups of homomorphisms. More generally, `IsUnit.liftRight` lifts a homomorphism whose values are all units, and `Units.liftRight` does the same with the units given explicitly. The isomorphism `toUnits` identifies a group $G$ with its group of units $G^\times$.

**Definition (Local homomorphism).** A homomorphism $f : R \to S$ of monoids is local when $f(a)$ a unit implies $a$ a unit.

The class is `IsLocalHom`, and `IsUnit.of_map` applies it. For a local $f$, `isUnit_map_iff` states that $f(a)$ is a unit if and only if $a$ is a unit: one direction is `IsUnit.map` and the other is the definition. Every isomorphism is local, by the instance `isLocalHom_equiv`, and the composite of local homomorphisms is local, by `MonoidHom.isLocalHom_comp`. The inclusion $\mathbb{Z} \to \mathbb{Q}$ is not local, because $2$ becomes a unit. The name comes from commutative algebra, where the local homomorphisms of local rings are those that send the maximal ideal into the maximal ideal.

The equivalence `unitsEquivProdSubtype` describes a unit of $M$ as a pair $(u, v)$ with $u v = 1$ and $v u = 1$. For an isomorphism $f$, `MulEquiv.isUnit_map` states that $f(x)$ is a unit if and only if $x$ is a unit.

#### Common errors

1. A learner proves $(f g)(x) = g(f(x))$ for permutations and the proof fails. The product of `Equiv.Perm α` applies $g$ first: $(f g)(x) = f(g(x))$, and `Equiv.Perm.mul_def` states $f g$ = `Equiv.trans g f`, with the factors in the reverse order.
2. A learner uses `Units.map` with a plain function. It needs a bundled homomorphism `M →* N`. For a map in a class of homomorphisms, coerce it first, as `Units.map (f : M →* N)`.
3. A learner expects `isUnit_map_iff` for every homomorphism. The converse of `IsUnit.map` needs the class `IsLocalHom f`, and it fails for the inclusion $\mathbb{Z} \to \mathbb{Q}$.

### Exercises

1. (A) Let $f, g$ be permutations of $\{1, 2, 3\}$ with $f = (1\ 2)$ and $g = (2\ 3)$. Compute $(f g)(1)$ with `Equiv.Perm.mul_apply`, and compare it with $(g f)(1)$.
2. (A) Prove that $(x\ y)$ commutes with $(z\ w)$ when $x, y, z, w$ are distinct, with `Equiv.mul_swap_eq_swap_mul`.
3. (B) Show that the map $a \mapsto$ `Equiv.mulLeft a` from a group $G$ into `Equiv.Perm G` is an injective homomorphism. This is the theorem of Cayley.
4. (B) Let $f : M \to N$ be a homomorphism of monoids that has a left inverse homomorphism $g$, so $g \circ f = \mathrm{id}$. Prove that $f$ is local.
5. (B) Show that `Units.map` of the inclusion $\mathbb{Z} \to \mathbb{Q}$ is injective but not surjective.
6. (C) Let $G$ be a group. Prove that the conjugation homomorphism $G \to$ `MulAut G` has the center of $G$ as kernel, and deduce that $G$ embeds into its automorphisms when the center is trivial.

### Reference

<?reference?>
