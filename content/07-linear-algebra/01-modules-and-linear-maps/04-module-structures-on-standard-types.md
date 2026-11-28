---
title: Module structures on standard types
kind: api
modules:
  - Mathlib.Algebra.Module.Basic
  - Mathlib.Algebra.Module.BigOperators
  - Mathlib.Algebra.Module.NatInt
  - Mathlib.Algebra.Module.Pi
  - Mathlib.Algebra.Module.Prod
  - Mathlib.Algebra.Module.PUnit
  - Mathlib.Algebra.Module.ULift
  - Mathlib.Algebra.Module.Opposite
  - Mathlib.Algebra.Module.Equiv.Opposite
  - Mathlib.Algebra.Module.MinimalAxioms
  - Mathlib.Algebra.Module.Card
  - Mathlib.Algebra.Module.Shrink
  - Mathlib.Algebra.Module.TransferInstance
  - Mathlib.Algebra.Module.Rat
  - Mathlib.Algebra.Module.ZMod
  - Mathlib.Algebra.Module.RingHom
  - Mathlib.Algebra.NoZeroSMulDivisors.Defs
  - Mathlib.Algebra.NoZeroSMulDivisors.Basic
  - Mathlib.Algebra.NoZeroSMulDivisors.Pi
  - Mathlib.Algebra.Module.PointwisePi
  - Mathlib.Algebra.Module.End
  - Mathlib.Algebra.Module.FunLike
  - Mathlib.Algebra.Module.Hom
explains:
  E2: [Module.ofMinimalAxioms, AddCommGroup.uniqueIntModule, Finset.sum_smul_sum, AddEquiv.module, Module.compHom, AddCommGroup.zmodModule, map_rat_smul, NoZeroSMulDivisors]
  E1: auto
families: []
requires: [V01, V03, V05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Module structures on standard types

### Overview

Section 1 defines a module over a ring. In practice a proof rarely builds a module by hand. It uses a module structure that Mathlib already puts on a standard type: the functions $I \to M$, the pairs $M \times N$, the one point type, the integers acting on an abelian group, the rationals acting on a divisible group, or the ring $\mathbb{Z}/n$ acting on a group of exponent $n$. This section lists these structures, explains which of them are instances and which are definitions that a proof must call, and gives the lemmas that move a scalar through a sum or through an additive map.

The modules of this section are small. Each one adds a few instances and a few lemmas, but together they decide how the type class search sees a module. A student who knows them can predict the scalar action that Lean finds on a type, and can avoid the common case of two different actions on the same type.

### The library around it

#### Building a module from fewer axioms

The class `Module R M` asks for six laws: $r(x + y) = rx + ry$, $(r + s)x = rx + sx$, $(rs)x = r(sx)$, $1x = x$, $r0 = 0$ and $0x = 0$. Over a ring, and with $M$ an additive group, the last two follow from the others. The definition `Module.ofMinimalAxioms` in `Mathlib.Algebra.Module.MinimalAxioms` takes the four first laws and returns a `Module R M`.

**Proof that the two laws follow.** From $r(0 + 0) = r0 + r0$ and $0 + 0 = 0$ one gets $r0 = r0 + r0$, so $r0 = 0$ after the cancellation in the group $M$. In the same way $(0 + 0)x = 0x + 0x$ gives $0x = 0$. $\square$

The definition is an `abbrev`, not an instance. A proof writes `letI := Module.ofMinimalAxioms h₁ h₂ h₃ h₄` when it builds a module on a new type.

#### The natural numbers and the integers

Each additive commutative monoid is a module over $\mathbb{N}$, and each additive commutative group is a module over $\mathbb{Z}$, with $n \cdot x = x + \dots + x$. The instances are `AddCommMonoid.toNatModule` and `AddCommGroup.toIntModule` in `Mathlib.Algebra.Module.NatInt`. These structures are unique: `AddCommMonoid.uniqueNatModule` and `AddCommGroup.uniqueIntModule` give a term of `Unique (Module ℤ M)`.

**Proof of uniqueness over $\mathbb{Z}$.** Let $\cdot$ be any $\mathbb{Z}$-module structure on $M$. The law $(m + n)x = mx + nx$ and $1x = x$ give $nx = x + \dots + x$ for $n \ge 0$ by induction on $n$. Then $(-n)x + nx = 0x = 0$ gives $(-n)x = -(nx)$. So the action is the iterated sum. $\square$

The uniqueness has a practical side. A type can carry `Module ℤ M` from two sources, for example from the instance and from a ring map $\mathbb{Z} \to R$. The two actions are equal, but not by `rfl`. The lemmas `Nat.cast_smul_eq_nsmul` and `Int.cast_smul_eq_zsmul` state $(n : R) \cdot b = n \cdot b$, where the left side uses the $R$-action and the right side the iterated sum. The lemmas `map_natCast_smul` and `map_intCast_smul` say that an additive map commutes with these scalars. The instances `AddCommMonoid.nat_isScalarTower` and `AddCommGroup.intIsScalarTower` give the scalar towers $\mathbb{N} \to R \to M$ and $\mathbb{Z} \to R \to M$.

The file also has `Module.addCommMonoidToAddCommGroup`: a module over a ring is automatically a group, with $-x = (-1)x$. And `CharZero.of_module` says that if $M$ has characteristic zero as an additive monoid with one and is an $R$-module, then $R$ has characteristic zero.

#### The rationals and the fields

A $\mathbb{Q}$-module structure on an additive group is also unique, by `subsingleton_rat_module` in `Mathlib.Algebra.Module.Rat`. The key lemma is `map_rat_smul`: an additive map $f : M \to M_2$ between two $\mathbb{Q}$-modules satisfies $f(c x) = c f(x)$ for $c \in \mathbb{Q}$.

**Proof.** Write $c = p/q$ with $q > 0$. The map $f$ commutes with integer scalars. So $q \cdot f(c x) = f(q c x) = f(p x) = p f(x)$. In a $\mathbb{Q}$-module, multiplication by $q$ is invertible, so $f(c x) = (p/q) f(x)$. $\square$

So each additive map between $\mathbb{Q}$-vector spaces is $\mathbb{Q}$-linear. The same holds for the nonnegative rationals with `map_nnrat_smul`. The lemma `Rat.cast_smul_eq_qsmul` compares the action of $(q : R)$ with the action of $q$, as above for integers, and `ratCast_smul_eq` compares two division rings acting on the same group. The instances `IsScalarTower.rat` and `SMulCommClass.rat` make $\mathbb{Q}$ compatible with each other action. The lemma `HasUniqueDiv.of_module_rat` says that a $\mathbb{Q}$-module has unique division by positive integers.

In `Mathlib.Algebra.Module.Basic` the same idea gives `inv_natCast_smul_eq` and `inv_intCast_smul_eq` for $(n)^{-1}$, and `map_inv_natCast_smul` for additive maps. The lemma `invOf_two_smul_add_invOf_two_smul` states $\tfrac12 x + \tfrac12 x = x$ when $2$ is invertible in $R$.

#### The groups of exponent n

Let $G$ be an additive group with $n x = 0$ for each $x$. Then $G$ is a module over $\mathbb{Z}/n$: the class of $k$ acts as $k x$, and the choice of the representative does not matter. This is the definition `AddCommGroup.zmodModule` in `Mathlib.Algebra.Module.ZMod`. It is an `abbrev` with the hypothesis `∀ x, n • x = 0`, so a proof calls it by hand. The same file has `QuotientAddGroup.zmodModule` for a quotient $G / H$ with $n x \in H$ for each $x$.

Over $\mathbb{Z}/n$, the subgroups are the submodules, and the additive maps are the linear maps:

| Lean name | Statement |
|---|---|
| `AddSubgroup.toZModSubmodule` | the order isomorphism between `AddSubgroup M` and `Submodule (ZMod n) M` |
| `AddSubgroup.mem_toZModSubmodule` | $x$ is in the submodule of $S$ if and only if $x \in S$ |
| `AddMonoidHom.toZModLinearMap` | an additive map $M \to M_1$ as a `ZMod n`-linear map |
| `AddMonoidHom.toZModLinearMapEquiv` | the additive equivalence `(M →+ M₁) ≃+ (M →ₗ[ZMod n] M₁)` |
| `ZMod.map_smul` | an additive map commutes with the action of `ZMod n` |
| `ZModModule.exists_submodule_subset_card_le` | for $p$ prime and $0 < k \le |H|$, a submodule $H' \le H$ with $|H'| \le k < p |H'|$ |

So an elementary abelian $p$-group is a vector space over $\mathbb{F}_p$, and linear algebra over a field applies to it.

#### Functions, pairs and the trivial module

For a family of modules $(M_i)_{i \in I}$, the product $\prod_i M_i$ is a module with the action $(r f)(i) = r f(i)$. This is `Pi.module` in `Mathlib.Algebra.Module.Pi`, with `Pi.Function.module` for the case of one module $M$ and the type $I \to M$. The variant `Pi.module'` lets a family of rings $R_i$ act on the family $M_i$ coordinate by coordinate. The pair $M \times N$ is a module by `Prod.instModule` in `Mathlib.Algebra.Module.Prod`. The linear maps of the product are in the same file:

| Lean name | Statement |
|---|---|
| `LinearMap.proj i` | the projection $\prod_j M_j \to M_i$ |
| `LinearMap.pi f` | the map $x \mapsto (f_i(x))_i$ built from maps $f_i : M_2 \to M_i$ |
| `LinearMap.proj_pi` | `LinearMap.proj i ∘ₗ LinearMap.pi f = f i` |
| `LinearMap.pi_proj` | `LinearMap.pi LinearMap.proj = LinearMap.id` |
| `LinearMap.const` | the diagonal map $M_2 \to (I \to M_2)$ |

These two lemmas say that $\prod_i M_i$ is the product in the category of modules. The rest of the theory of products is in `Mathlib.LinearAlgebra.Pi`.

The one point type is the zero module, by `PUnit.module` in `Mathlib.Algebra.Module.PUnit`, and `PUnit.smul_eq` says that each scalar sends the point to itself. The file also gives the weaker actions, such as `PUnit.mulAction` and `PUnit.distribMulAction`.

#### Changing the universe

Lean has a hierarchy of universes, and a statement sometimes needs a module in a larger universe. The type `ULift M` is a copy of `M` in a higher universe. The instance `ULift.module'` makes it an `R`-module, and `ULift.moduleEquiv` is the linear equivalence `ULift M ≃ₗ[R] M`. The instance `ULift.module` lets `ULift R` act on `M`. In the other direction, `Shrink α` is a copy of a small type in a smaller universe, with `Shrink.instModule` and the linear equivalence `Shrink.linearEquiv`.

#### Transport of structure

Let $e : \alpha \simeq \beta$ be an additive equivalence and let $\beta$ be an $R$-module. Then $\alpha$ has a unique module structure that makes $e$ linear: $r \cdot a = e^{-1}(r \cdot e(a))$. This is `AddEquiv.module` in `Mathlib.Algebra.Module.TransferInstance`, and `AddEquiv.linearEquiv` is $e$ as a linear equivalence. The equivalence must be additive, so that the new structure keeps the sum of $\alpha$. The lemmas `Equiv.noZeroSMulDivisors` and `AddEquiv.moduleIsTorsionFree` move these properties along $e$. The same file has `LinearEquiv.isScalarTower`.

#### Restriction along a ring map

A ring map $f : S \to R$ turns each $R$-module $M$ into an $S$-module with $s \cdot x = f(s) x$. This is `Module.compHom` in `Mathlib.Algebra.Module.RingHom`. The laws follow from the laws of $M$ and the fact that $f$ preserves sums, products and $1$. In particular, `RingHom.toModule` makes $S$ an $R$-module for $f : R \to S$, with `RingHom.toModule_smul : x • y = f x * y`. The map `RingHom.smulOneHom` goes back: from an $R$-module $S$ with a scalar tower, it gives the ring map $r \mapsto r \cdot 1$, and `ringHomEquivModuleIsScalarTower` says that the two constructions are inverse. For a surjective $f$, `Function.Surjective.moduleLeft` builds an $S$-module from an $R$-module.

These are definitions and not instances. An instance on each ring map would make the type class search loop and would give two actions on the same type.

#### The action as a ring map

The action of $R$ on $M$ is a ring map $R \to \operatorname{End}(M, +)$, where $\operatorname{End}(M, +)$ is the ring of additive endomorphisms. This is `Module.toAddMonoidEnd` in `Mathlib.Algebra.Module.End`, and `smulAddHom` is the same action as a biadditive map `R →+ M →+ M`. The lemmas `AddMonoid.End.natCast_def` and `AddMonoid.End.intCast_def` identify the integers in this ring with the maps $x \mapsto n x$. Conversely, `AddMonoid.End.applyModule` in `Mathlib.Algebra.Module.Hom` makes $M$ a module over the ring `AddMonoid.End M`, and `AddMonoidHom.instModule` makes the additive maps `A →+ B` an $R$-module when $B$ is one. `AddMonoidHom.smul` is the bundled action map. For types of bundled maps in general, `FunLike.module` in `Mathlib.Algebra.Module.FunLike` builds the module structure from the facts that zero, sum and scalar product are computed pointwise.

#### The opposite module

For a ring $R$, the opposite ring $R^{\mathrm{op}}$ acts on $R$ by right multiplication: `Semiring.toOppositeModule` in `Mathlib.Algebra.Module.Opposite`. The type $M^{\mathrm{op}}$ has the same module structure as $M$ by `MulOpposite.instModule`, and `MulOpposite.opLinearEquiv` is the linear equivalence $M \simeq M^{\mathrm{op}}$. The lemma `LinearMap.ext_ring_op` says that a semilinear map out of $R$ for an action of $R^{\mathrm{op}}$ is fixed by its value at $1$.

#### Sums and scalars

The file `Mathlib.Algebra.Module.BigOperators` moves a sum of scalars through the action. The lemma `Finset.sum_smul` is $(\sum_{i \in s} f_i) x = \sum_{i \in s} f_i x$, and `Finset.sum_smul_sum` is the product of two sums:
$$\Big(\sum_{i \in s} f_i\Big) \cdot \Big(\sum_{j \in t} g_j\Big) = \sum_{i \in s} \sum_{j \in t} f_i \cdot g_j.$$
It follows from `Finset.sum_smul` and the distributive law `Finset.smul_sum` of the other side. The same pattern holds for lists and multisets: `List.sum_smul`, `Multiset.sum_smul` and `Multiset.sum_smul_sum`. The lemma `Fintype.sum_single_smul` picks one term out of a sum with the function `Pi.single`.

The file `Mathlib.Algebra.Module.Basic` has the lemmas for indicator functions and supports. `Set.indicator_smul` says that the indicator of $a \mapsto r(a) f(a)$ is $r$ times the indicator of $f$. `Function.support_smul_subset_left` gives $\operatorname{supp}(f g) \subseteq \operatorname{supp} f$, and `Function.support_smul` gives $\operatorname{supp}(f g) = \operatorname{supp} f \cap \operatorname{supp} g$ when $M$ is torsion free over a domain. In `Mathlib.Algebra.Module.PointwisePi`, `smul_univ_pi` says that $r \cdot \prod_i t_i = \prod_i r \cdot t_i$ for sets $t_i$, and `smul_pi₀` gives the same for a product over a subset when $r \ne 0$ in a group with zero.

#### Modules with no zero divisors

The class `NoZeroSMulDivisors R M` in `Mathlib.Algebra.NoZeroSMulDivisors.Defs` says that $r x = 0$ implies $r = 0$ or $x = 0$. A vector space has this property: if $r \ne 0$ and $r x = 0$, then $x = r^{-1}(r x) = 0$. This is the instance `GroupWithZero.toNoZeroSMulDivisors` in `Mathlib.Algebra.NoZeroSMulDivisors.Basic`. A ring with no zero divisors acts on itself with no zero divisors (`NoZeroDivisors.toNoZeroSMulDivisors`). The property passes to subobjects along injective maps by `Function.Injective.noZeroSMulDivisors`, and to products by `Pi.noZeroSMulDivisors` in `Mathlib.Algebra.NoZeroSMulDivisors.Pi`. Over a domain, the instance `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors` turns it into the class `Module.IsTorsionFree` of Chapter 7. The lemma `Cardinal.mk_le_of_module` in `Mathlib.Algebra.Module.Card` says that a nonzero torsion free module over a domain is at least as large as the ring: the map $r \mapsto r x$ is injective for $x \ne 0$.

#### Common errors

1. Two module structures on one type. A type such as `ℤ` or `ZMod n → M` can get an action from two instances, and a lemma stated for one action does not apply to the other by `rfl`. The lemmas `Int.cast_smul_eq_zsmul` and `Rat.cast_smul_eq_qsmul` connect the two forms. A proof that builds an action with `Module.compHom` or `AddCommGroup.zmodModule` should do it with `letI` in a small scope.
2. Forgetting that `AddCommGroup.zmodModule` is not an instance. Lean does not find `Module (ZMod p) G` for a group of exponent $p$ by itself. The proof must give the hypothesis $p x = 0$ and call the definition.
3. Using `Finset.smul_sum` where `Finset.sum_smul` is needed. The first one moves a scalar into a sum of vectors, $r \sum x_i = \sum r x_i$; the second one moves a sum of scalars, $(\sum r_i) x = \sum r_i x$.

### Exercises

1. (A) Show that the $\mathbb{Z}$-module structure on $\mathbb{Z}/6$ is unique, and compute $(-4) \cdot \bar{5}$ in it.
2. (A) Let $f : \mathbb{Q}^2 \to \mathbb{Q}$ be additive with $f(1, 0) = 3$ and $f(0, 1) = -1$. Find $f(\tfrac23, \tfrac54)$ and explain which lemma of this section gives the answer.
3. (B) Let $G = (\mathbb{Z}/2)^3$. Make it a vector space over $\mathbb{F}_2$, count its subspaces of dimension 1 and 2, and check that they are exactly its subgroups of order 2 and 4.
4. (B) Show that an additive map $\mathbb{R} \to \mathbb{R}$ need not be $\mathbb{R}$-linear, but each additive map $\mathbb{R} \to \mathbb{R}$ is $\mathbb{Q}$-linear. Hint: use a basis of $\mathbb{R}$ over $\mathbb{Q}$ for the first part.
5. (B) Let $f : \mathbb{Z} \to \mathbb{Z}/n$ be the quotient map. Describe the $\mathbb{Z}$-module structure that `Module.compHom` gives on a $\mathbb{Z}/n$-module $M$, and show that it is the structure of `AddCommGroup.toIntModule`.
6. (C) Show that $\mathbb{Q}/\mathbb{Z}$ is not a $\mathbb{Q}$-module, although it is divisible. Hint: a $\mathbb{Q}$-module has unique division by $2$.

### Reference

<?reference?>
