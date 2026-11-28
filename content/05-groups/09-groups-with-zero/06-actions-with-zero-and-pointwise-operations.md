---
title: Actions that respect zero and pointwise operations
kind: api
modules:
  - Mathlib.Algebra.GroupWithZero.Action.Defs
  - Mathlib.Algebra.GroupWithZero.Action.Basic
  - Mathlib.Algebra.GroupWithZero.Action.Center
  - Mathlib.Algebra.GroupWithZero.Action.ConjAct
  - Mathlib.Algebra.GroupWithZero.Action.End
  - Mathlib.Algebra.GroupWithZero.Action.FunLike
  - Mathlib.Algebra.GroupWithZero.Action.Hom
  - Mathlib.Algebra.GroupWithZero.Action.Opposite
  - Mathlib.Algebra.GroupWithZero.Action.Pi
  - Mathlib.Algebra.GroupWithZero.Action.Prod
  - Mathlib.Algebra.GroupWithZero.Action.TransferInstance
  - Mathlib.Algebra.GroupWithZero.Action.Units
  - Mathlib.Algebra.GroupWithZero.Action.Pointwise.Finset
  - Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
  - Mathlib.Algebra.GroupWithZero.Pointwise.Finset
  - Mathlib.Algebra.GroupWithZero.Pointwise.Set.Basic
  - Mathlib.Algebra.GroupWithZero.Pointwise.Set.Card
  - Mathlib.Algebra.GroupWithZero.Submonoid.Pointwise
  - Mathlib.Algebra.GroupWithZero.Subgroup
explains:
  E2: [SMulZeroClass, SMulWithZero, MulActionWithZero, DistribMulAction, DistribMulAction.toAddMonoidEnd, inv_smul_smul₀, MulAction.bijective₀, Set.mem_smul_set_iff_inv_smul_mem₀, Finset.card_smul_finset₀, Subgroup.pointwise_smul_le_pointwise_smul_iff₀]
  E1: auto
families: []
requires: [V03.C01, V03.C03, V05.C01, V05.C03, V05.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Actions that respect zero and pointwise operations

### Overview

Chapter 6 studies an action of a group on a set. In algebra the set often has more structure. A ring acts on a module, and the action respects the addition and the zero of the module. A field acts on a vector space, and the scalar $0$ sends each vector to $0$. A group acts on a ring by automorphisms, and the action respects the product. Mathlib has a class for each of these cases, between the bare action `MulAction` and the class `Module` of Volume 7.

The modules of this section give these classes and their first lemmas. They also give the pointwise action on sets, finite sets, submonoids and subgroups when the acting monoid has a zero. The main new fact is that a nonzero element of a group with zero acts by a bijection, so it behaves like an element of a group. The section uses the actions and the stabilizers of Chapter 6 and the groups with zero of the earlier sections of this chapter.

### The library around it

#### The hierarchy of classes

The module `Mathlib.Algebra.GroupWithZero.Action.Defs` defines the classes. Each one adds one law to the notation `a • b`.

| Lean name | Law |
|---|---|
| `SMulZeroClass M A` | $a \cdot 0 = 0$ |
| `SMulWithZero M₀ A` | also $0 \cdot b = 0$, for a scalar type with zero |
| `MulActionWithZero M₀ A` | a monoid action with $a \cdot 0 = 0$ and $0 \cdot b = 0$ |
| `DistribSMul M A` | $a \cdot 0 = 0$ and $a \cdot (b + c) = a \cdot b + a \cdot c$ |
| `DistribMulAction M A` | a monoid action that is also a `DistribSMul` |
| `MulDistribMulAction M A` | a monoid action with $a \cdot (b c) = (a \cdot b)(a \cdot c)$ and $a \cdot 1 = 1$ |

The general lemmas are `smul_zero`, `zero_smul` and `smul_add`. They have no namespace, so they apply to each instance of the classes, from a module to an action on a set of functions. A monoid with zero acts on itself by multiplication with zero laws: this is `MonoidWithZero.toMulActionWithZero`. The laws also give `smul_eq_zero_of_left`, `smul_eq_zero_of_right` and `left_ne_zero_of_smul`: if $a \cdot b \neq 0$, then $a \neq 0$. When the scalars form a group, the lemma `smul_eq_zero_iff_eq` says that $a \cdot x = 0$ if and only if $x = 0$. The identity `boole_smul` says that $(\text{if } p \text{ then } 1 \text{ else } 0) \cdot a = \text{if } p \text{ then } a \text{ else } 0$.

A distributive action is the same as a homomorphism into the endomorphisms of the additive monoid. The map `DistribMulAction.toAddMonoidEnd M A` sends $a$ to the additive map $b \mapsto a \cdot b$, and it is a monoid homomorphism $M \to \mathrm{End}(A)$. In the other direction, the module `Mathlib.Algebra.GroupWithZero.Action.End` gives the action `AddMonoid.End.applyDistribMulAction` of $\mathrm{End}(A)$ on $A$, which is faithful (`AddMonoid.End.applyFaithfulSMul`). For a group $G$, the map `DistribMulAction.toAddAut` sends $g$ to an additive automorphism of $A$.

The classes pull back and push forward along maps, by the same pattern as the algebraic classes of Chapter 1. An injective map $B \to A$ that respects the scalar product carries a `DistribMulAction` on $A$ to one on $B$ (`Function.Injective.distribMulAction`), and a surjective map pushes it forward (`Function.Surjective.distribMulAction`). The constructions `DistribMulAction.compHom` and `MulActionWithZero.compHom` restrict the scalars along a monoid homomorphism $N \to M$. An additive equivalence $A \simeq B$ transfers an action, by `AddEquiv.distribMulAction`.

#### Products, functions and maps

The classes have instances on the standard constructions. Each one acts in each coordinate.

1. Products: `Prod.distribMulAction`, `Prod.mulActionWithZero` and `Prod.mulDistribMulAction`, with the simp lemmas `Prod.smul_mk_zero` and `Prod.smul_zero_mk`. The equivalence `DistribMulAction.prodEquiv` says that an action of $M \times N$ is the same as two commuting actions of $M$ and $N$.
2. Functions: `Pi.distribMulAction`, `Pi.mulActionWithZero` and `Pi.smulWithZero`. The primed forms let the scalar type depend on the index. The lemma `Pi.single_smul` says that $\mathrm{single}_i(r \cdot x) = r \cdot \mathrm{single}_i(x)$.
3. Homomorphisms: the type `A →+ B` of additive maps carries the pointwise action `AddMonoidHom.instDistribMulAction`, with $(m \cdot f)(a) = m \cdot f(a)$ (`AddMonoidHom.smul_apply`). The maps `ZeroHom A B` carry `ZeroHom.instMulActionWithZero`. The module `Mathlib.Algebra.GroupWithZero.Action.FunLike` gives the same instances for each bundled type of functions, as `FunLike.distribMulAction`.
4. Opposites and units: the instances `MulOpposite.instDistribMulAction` and `Units.instDistribMulAction` let $M^{\mathrm{mop}}$ and $M^\times$ act through $M$. In a monoid with zero with left cancellation, the right action of $M^{\mathrm{mop}}$ on $M$ is faithful (`IsLeftCancelMulZero.toFaithfulSMul_opposite`).

#### Actions of a group with zero

Let $G_0$ be a group with zero that acts on $\beta$. Each nonzero $a$ is a unit of $G_0$, and $a^{-1}$ acts as the inverse of $a$.

**Theorem (`inv_smul_smul₀`).** If $a \neq 0$, then $a^{-1} \cdot (a \cdot x) = x$ for each $x \in \beta$.

*Proof.* By the action laws, $a^{-1} \cdot (a \cdot x) = (a^{-1} a) \cdot x = 1 \cdot x = x$, because $a^{-1} a = 1$ for $a \neq 0$. $\square$

The same computation gives `smul_inv_smul₀`, and with both identities the map $x \mapsto a \cdot x$ is a bijection for $a \neq 0$ (`MulAction.bijective₀`, with `MulAction.injective₀` and `MulAction.surjective₀`). The bundled forms are the permutation `Equiv.smulRight` and, for a distributive action, the additive automorphism `DistribMulAction.toAddEquiv₀`. The lemma `inv_smul_eq_iff₀` moves the inverse to the other side: $a^{-1} \cdot x = y$ if and only if $x = a \cdot y$. The name suffix ₀ marks these lemmas: they are the group lemmas of Chapter 6 with the extra hypothesis $a \neq 0$.

The module `Mathlib.Algebra.GroupWithZero.Action.Units` also states the results for a unit $u$ of a monoid: `IsUnit.smul_eq_zero` says that $u \cdot x = 0$ if and only if $x = 0$, for a distributive action. Commutation survives a nonzero scalar: `Commute.smul_left_iff₀` says that $a \cdot x$ commutes with $y$ if and only if $x$ commutes with $y$.

The module `Mathlib.Algebra.GroupWithZero.Action.Basic` gives the action of a group with zero as a homomorphism of monoids with zero, `smulMonoidWithZeroHom`, and identities for division such as `div_smul_div_comm`: $(g / h) \cdot (a / b) = (g \cdot a) / (h \cdot b)$. The module `Mathlib.Algebra.GroupWithZero.Action.ConjAct` makes `ConjAct G₀` a group with zero (`ConjAct.instGroupWithZero`), with the conjugation action `ConjAct.mulAction₀` on $G_0$. The module `Mathlib.Algebra.GroupWithZero.Action.Center` gives the isomorphism `Subgroup.centerUnitsEquivUnitsCenter` between the center of the unit group and the units of the center.

#### Pointwise actions on sets and finite sets

For a set $s \subseteq \beta$ and a scalar $a$, the set $a \cdot s$ is $\{a \cdot x : x \in s\}$. Chapter 6 uses this action for a group. The modules `Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set` and `Mathlib.Algebra.GroupWithZero.Action.Pointwise.Finset` give the facts that involve a zero.

**Theorem (`Set.mem_smul_set_iff_inv_smul_mem₀`).** If $a \neq 0$, then $x \in a \cdot A$ if and only if $a^{-1} \cdot x \in A$.

*Proof.* If $x = a \cdot y$ with $y \in A$, then $a^{-1} \cdot x = y \in A$ by `inv_smul_smul₀`. Conversely, if $a^{-1} \cdot x \in A$, then $x = a \cdot (a^{-1} \cdot x) \in a \cdot A$ by `smul_inv_smul₀`. $\square$

So multiplication by a nonzero $a$ is a bijection on the subsets, and it commutes with the Boolean operations. The lemmas end in ₀ and assume $a \neq 0$: `Set.smul_set_inter₀`, `Set.smul_set_sdiff₀`, `Set.smul_set_symmDiff₀` and `Set.smul_set_univ₀`. The preimage of a set under $x \mapsto a \cdot x$ is $a^{-1} \cdot t$ (`Set.preimage_smul₀`). The scalar $0$ collapses a set: $0 \cdot s = 0$ for a nonempty set $s$ (`Set.zero_smul_set`), and $0 \cdot s$ has at most one point in all cases (`Set.subsingleton_zero_smul_set`). Each scalar keeps $0$ inside the set: $0 \in a \cdot t$ when $0 \in t$ (`Set.zero_mem_smul_set`).

The finite sets have the same lemmas in the namespace `Finset`, and they add a count.

**Theorem (`Finset.card_smul_finset₀`).** If $a \neq 0$, then $|a \cdot s| = |s|$ for each finite set $s$.

*Proof.* The map $x \mapsto a \cdot x$ is injective by `MulAction.injective₀`, and the image of a finite set under an injective map has the same size. $\square$

For sets the module `Mathlib.Algebra.GroupWithZero.Pointwise.Set.Card` gives the same result for `Nat.card` and for cardinals (`Set.natCard_smul_set₀`, `Cardinal.mk_smul_set₀`). If the sets $a \cdot t$ for $a \in s$ are pairwise disjoint and each $a$ is nonzero, then $|t|$ divides $|s \cdot t|$ (`Finset.card_dvd_card_smul_right₀`).

The modules `Mathlib.Algebra.GroupWithZero.Pointwise.Set.Basic` and `Mathlib.Algebra.GroupWithZero.Pointwise.Finset` treat the product of two sets in a monoid with zero. The set $s \cdot 0$ is contained in $0$ (`Set.mul_zero_subset`), and it equals $0$ when $s$ is nonempty (`Set.Nonempty.mul_zero`). In a monoid with left cancellation, $|t| \le |s \cdot t|$ when $s$ contains a nonzero element (`Finset.card_le_card_mul_left₀`), because $x \mapsto a x$ is injective for $a \neq 0$.

The sets of a monoid carry the induced structure: `Set.distribMulActionSet` and `Finset.distribMulAction` make the pointwise action distributive, and `Set.instNoZeroDivisors` says that the sets of a type with a product, a zero and no zero divisors have no zero divisors.

#### Pointwise actions on submonoids and subgroups

A distributive action of $M$ on $A$ acts on the additive submonoids of $A$ by $m \cdot S = \{m \cdot s : s \in S\}$. The image is again a submonoid, because $x \mapsto m \cdot x$ is an additive map. The instance is `AddSubmonoid.pointwiseMulAction`, and `AddSubgroup.pointwiseMulAction` is the version for subgroups. The action commutes with the lattice operations: `AddSubmonoid.smul_sup` gives $m \cdot (S \sqcup T) = m \cdot S \sqcup m \cdot T$, and `AddSubmonoid.smul_closure` gives $m \cdot \langle s \rangle = \langle m \cdot s \rangle$.

For a group with zero acting by a `MulDistribMulAction` on a group $G$, the modules `Mathlib.Algebra.GroupWithZero.Submonoid.Pointwise` and `Mathlib.Algebra.GroupWithZero.Subgroup` give the ₀ forms of the order lemmas.

**Theorem (`Subgroup.pointwise_smul_le_pointwise_smul_iff₀`).** If $a \neq 0$, then $a \cdot S \le a \cdot T$ if and only if $S \le T$.

*Proof sketch.* One direction is monotonicity. For the other, act by $a^{-1}$ on both sides: $a^{-1} \cdot (a \cdot S) = S$ by `inv_smul_smul₀` applied to each element. $\square$

The companions `Subgroup.pointwise_smul_le_iff₀`, `Subgroup.le_pointwise_smul_iff₀` and `Subgroup.mem_pointwise_smul_iff_inv_smul_mem₀` move $a$ to the other side as $a^{-1}$. The same names exist for `Submonoid`, `AddSubmonoid` and `AddSubgroup`.

#### Common errors

1. The lemma `zero_smul` takes the scalar type as an explicit argument: `zero_smul M₀ m` states $0 \cdot m = 0$ for $0 \in M_0$. A rewrite with `zero_smul` alone can fail to find the scalar type.
2. A `DistribMulAction` does not give `zero_smul`. The scalar $0$ need not act by $0$: a monoid with zero can act on an additive group through a map that sends $0$ to the identity. The law $0 \cdot b = 0$ needs `MulActionWithZero` or `Module`.
3. The ₀ lemmas need the hypothesis $a \neq 0$, and the group lemmas without ₀ do not apply to a group with zero. For a field acting on a vector space, use `inv_smul_smul₀` and not `inv_smul_smul`.

### Exercises

1. (A) Prove `smul_eq_zero_iff_eq`: for a group acting distributively on $\beta$, $a \cdot x = 0$ if and only if $x = 0$.
2. (A) Let $s = \{1, 2\} \subseteq \mathbb{Q}$. Compute $3 \cdot s$ and $0 \cdot s$, and check `Finset.card_smul_finset₀` and `Set.zero_smul_set` on them.
3. (B) Show that `DistribMulAction.toAddMonoidEnd M A` is a monoid homomorphism, and that each monoid homomorphism $M \to \mathrm{End}(A)$ comes from a distributive action.
4. (B) Give a distributive action of the monoid with zero $\{0, 1\}$ under multiplication on $\mathbb{Z}$ in which $0$ acts as the identity. Explain why it is not a `MulActionWithZero`.
5. (B) Prove `Set.preimage_smul₀`: for $a \neq 0$, the preimage of $t$ under $x \mapsto a \cdot x$ is $a^{-1} \cdot t$.
6. (C) Let a finite field $K$ act on a finite set $X$ by a `MulActionWithZero`. Show that the nonzero elements of $K$ permute $X \setminus \{0\}$. Assume that $a \cdot x = x$ with $x \neq 0$ implies $a = 1$, and deduce that $|K| - 1$ divides $|X| - 1$.

### Reference

<?reference?>
