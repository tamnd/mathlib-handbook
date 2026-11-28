---
title: Actions on products, sums, functions and opposites
kind: api
modules:
  - Mathlib.Algebra.Group.Action.Pi
  - Mathlib.Algebra.Group.Action.Prod
  - Mathlib.Algebra.Group.Action.Sigma
  - Mathlib.Algebra.Group.Action.Sum
  - Mathlib.Algebra.Group.Action.Option
  - Mathlib.Algebra.Group.Action.Opposite
  - Mathlib.Algebra.Group.Action.Units
  - Mathlib.Algebra.Group.Action.TypeTags
  - Mathlib.Algebra.Group.Action.TransferInstance
  - Mathlib.Algebra.Group.Action.FunLike
explains:
  E2: [Pi.faithfulSMul_at, Prod.faithfulSMulLeft, MulAction.prodEquiv, smulMulHom, Sigma.smul_mk, Sum.smul_inl, op_smul_mul, Units.instMulAction, Units.smul_inv, Equiv.mulAction]
  E1: auto
families: []
requires: [V01, V05.C01, V05.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Actions on products, sums, functions and opposites

### Overview

An action of a monoid $M$ on a set $\alpha$ gives actions of $M$ on many sets that are built from $\alpha$. The monoid $M$ acts on the functions $\iota \to \alpha$ point by point, on the pairs $\alpha \times \beta$ coordinate by coordinate, and on the disjoint union $\alpha \oplus \beta$ piece by piece. It also acts on `Option α`, where it fixes the extra point. An action also passes to the opposite type, to the units of $M$, to the type tags `Additive` and `Multiplicative`, and along an equivalence of types. In each case the new action is the obvious one, and Lean finds it as an instance.

This section describes the ten modules that hold these constructions. Each module gives the action, the lemmas that compute it on the constructors, and the instances for the compatibility classes `SMulCommClass` and `IsScalarTower` and for `FaithfulSMul`. The definitions of `MulAction`, `SMulCommClass` and `IsScalarTower` are in Section 1 of this chapter. The products, the opposite monoid and the units are in Chapters 1 and 2.

A student needs these instances often, and mostly without seeing them. When a group $G$ acts on a set $X$, the induced action on $X^n$ or on $X \times X$ is the start of many arguments about pairs of points. Section 7 uses the action on tuples for multiple transitivity. The module structure of $R^n$ in later volumes is the same construction for a ring.

### The library around it

#### Functions and families

The module `Mathlib.Algebra.Group.Action.Pi` treats a family of types $\alpha_i$ for $i \in \iota$, each with an action of $M$. The instance `Pi.mulAction` gives the action $(m \cdot f)(i) = m \cdot f(i)$ on the dependent functions $\prod_i \alpha_i$. The evaluation lemma `Pi.smul_apply` is in an earlier notation module. There is also a second form, where the acting type is itself a family: `Pi.smul'` and `Pi.mulAction'` give the action of $\prod_i M_i$ on $\prod_i \alpha_i$ by $(s \cdot x)(i) = s(i) \cdot x(i)$, and `Pi.smul_apply'` computes it. The instances `Pi.smulCommClass`, `Pi.isScalarTower` and their primed forms carry the compatibility classes to the family. For a constant family the instance is `Function.hasSMul`, with `Function.smulCommClass`.

Three lemmas say that the action commutes with the usual operations on functions. `Function.update_smul` states that updating $m \cdot f$ at $i$ with the value $m \cdot x$ gives $m \cdot$ the update of $f$. `Set.piecewise_smul` does the same for a function that is defined piece by piece, and `Function.extend_smul` for an extension along a map.

**Proposition.** Let each $\alpha_i$ be nonempty, and let the action of $M$ on $\alpha_{i_0}$ be faithful for one index $i_0$. Then the action of $M$ on $\prod_i \alpha_i$ is faithful.

*Proof.* Let $m_1 \cdot f = m_2 \cdot f$ for all $f$. Let $a \in \alpha_{i_0}$. Choose a point in each other $\alpha_i$, and let $f$ be the function with these values and $f(i_0) = a$. Then $m_1 \cdot a = (m_1 \cdot f)(i_0) = (m_2 \cdot f)(i_0) = m_2 \cdot a$. This holds for all $a$, so $m_1 = m_2$. $\square$

The library form is `Pi.faithfulSMul_at`. The instance `Pi.faithfulSMul` is the case where all the actions are faithful and $\iota$ is nonempty.

#### Products

The module `Mathlib.Algebra.Group.Action.Prod` gives `Prod.mulAction`, the action $m \cdot (a, b) = (m \cdot a, m \cdot b)$. The lemmas `Prod.smul_mk` and `Prod.smul_fst` compute it, and they are in a notation module. Faithfulness needs one faithful factor and one nonempty factor: `Prod.faithfulSMulLeft` asks for a faithful action on $\alpha$ and a nonempty $\beta$, and `Prod.faithfulSMulRight` is the mirror form. The proof is the proof above with two indices.

An action of a product $M \times N$ is a different matter. Two actions of $M$ and of $N$ on the same $\alpha$ give an action of $M \times N$ by $(m, n) \cdot a = m \cdot (n \cdot a)$ when they commute, and this is `MulAction.prodOfSMulCommClass`. Conversely, an action of $M \times N$ restricts to $M \times 1$ and $1 \times N$, and the two restrictions commute because $(m, 1)$ and $(1, n)$ commute in $M \times N$. The equivalence `MulAction.prodEquiv` states this correspondence: the actions of $M \times N$ on $\alpha$ are the pairs of actions of $M$ and $N$ with an `SMulCommClass` instance.

The action itself is a map on a product. If $M$ acts on a monoid $\beta$ with `IsScalarTower M β β` and `SMulCommClass M β β`, then $(m, b) \mapsto m \cdot b$ respects multiplication: $(m m') \cdot (b b') = (m \cdot b)(m' \cdot b')$ by `smul_mul_smul_comm`. The library packs this as `smulMulHom : M × β →ₙ* β` and, when $\beta$ has a unit, as the monoid homomorphism `smulMonoidHom`.

#### Disjoint unions and an extra point

The modules `Mathlib.Algebra.Group.Action.Sigma` and `Mathlib.Algebra.Group.Action.Sum` act on each piece of a disjoint union. For the sigma type $\Sigma_i \alpha_i$ the action keeps the index: `Sigma.smul_mk` states $m \cdot \langle i, b \rangle = \langle i, m \cdot b \rangle$, and `Sigma.instMulAction` is the action. For $\alpha \oplus \beta$, the lemmas `Sum.smul_inl` and `Sum.smul_inr` state $m \cdot \operatorname{inl}(a) = \operatorname{inl}(m \cdot a)$ and $m \cdot \operatorname{inr}(b) = \operatorname{inr}(m \cdot b)$, and `Sum.smul_swap` says that the action commutes with the swap of the two pieces. Here one faithful piece is enough, with no condition on the other piece: `Sum.FaithfulSMulLeft` and `Sum.FaithfulSMulRight` are instances, and `Sigma.FaithfulSMul'` is the version for one index of a sigma type.

The module `Mathlib.Algebra.Group.Action.Option` adds a fixed point. The action on `Option α` sends the extra point none to itself and some $b$ to some $(m \cdot b)$, by `Option.smul_none` and `Option.smul_some`, and `Option.instMulAction` is the action. So `Option α` is $\alpha$ with one extra orbit of size one.

The orbits of a sum are the orbits of the pieces. This is the reason that a disjoint union of $G$-sets is the coproduct of $G$-sets, in the same way as the product $\alpha \times \beta$ is the product.

#### The opposite type and actions on the right

The module `Mathlib.Algebra.Group.Action.Opposite` has two kinds of instances. Actions *on* the opposite type act on the underlying type: `MulOpposite.instMulAction` gives the action of $M$ on $\alpha^{\mathrm{op}}$. Actions *by* the opposite monoid are right actions. A monoid acts on itself on the right by `Monoid.toOppositeMulAction`, where $\operatorname{op}(a) \cdot b = b a$ by `op_smul_eq_mul`. In general a right action of $\alpha$ on $\beta$ is an action of $\alpha^{\mathrm{op}}$, and the order of a product reverses:

$$\operatorname{op}(a_1 a_2) \cdot b = \operatorname{op}(a_2) \cdot (\operatorname{op}(a_1) \cdot b).$$

This is `op_smul_mul`. In the notation of a right action, $b \cdot (a_1 a_2) = (b \cdot a_1) \cdot a_2$, so the formula is the associativity of a right action. With `open scoped RightActions` the library writes `m <• r` for `MulOpposite.op r • m`, and `r •> m` for the left action.

The left and right multiplications of a semigroup commute: `Semigroup.opposite_smulCommClass` is the instance `SMulCommClass αᵐᵒᵖ α α`. A commutative semigroup has `CommSemigroup.isCentralScalar`: its left and right actions on itself agree. The class `IsCentralScalar` is the general form of this, and `MulOpposite.op_smul_eq_op_smul_op` uses it.

#### Units

The module `Mathlib.Algebra.Group.Action.Units` treats two actions. First, the units of $M$ act wherever $M$ acts. The instance `Units.instMulAction` acts through the coercion, and `Units.smul_def` states $u \cdot a = \uparrow u \cdot a$. Since $u^{-1} \cdot (u \cdot a) = (u^{-1} u) \cdot a = a$, each unit acts by a bijection, and so the action of $M^\times$ is an action of a group. The instance `Units.instFaithfulSMul` keeps faithfulness. Second, a group $G$ that acts on a monoid $M$ acts on its units, when the action commutes with multiplication in the sense of `SMulCommClass G M M` and `IsScalarTower G M M`. This is `Units.mulAction'`. The inverse of $g \cdot u$ is $g^{-1} \cdot u^{-1}$, since

$$(g \cdot u)(g^{-1} \cdot u^{-1}) = (g g^{-1}) \cdot (u u^{-1}) = 1$$

by `smul_mul_smul_comm`. The lemma is `Units.smul_inv`, and `Units.val_smul` computes the underlying element. The companion lemma `IsUnit.smul` states that $g \cdot m$ is a unit when $m$ is a unit. For an action that respects multiplication, `Units.mulDistribMulActionRight` acts on $N^\times$ and `Units.coe_smul` computes it.

#### Type tags, transfer and function types

The module `Mathlib.Algebra.Group.Action.TypeTags` moves actions across the type tags of Chapter 1. A multiplicative action of $\alpha$ is an additive action of `Additive α`, by `Additive.addAction`, and an additive action of $\alpha$ is a multiplicative action of `Multiplicative α`, by `Multiplicative.mulAction`. The lemma `ofAdd_smul` states `Multiplicative.ofAdd a • b = a +ᵥ b`, and `toMul_smul` is the reverse direction.

The module `Mathlib.Algebra.Group.Action.TransferInstance` pulls an action back along an equivalence $e : \alpha \simeq \beta$. The definition `Equiv.mulAction` sets $m \cdot a = e^{-1}(m \cdot e(a))$, and `Equiv.mulDistribMulAction` is the version for an action on a monoid. The lemmas `Equiv.faithfulSMul`, `Equiv.smulCommClass` and `Equiv.isScalarTower` carry the classes back. These are definitions, not instances: the equivalence must be given explicitly.

The module `Mathlib.Algebra.Group.Action.FunLike` treats types of bundled maps, for example homomorphisms. When the scalar multiplication on such a type acts on the values, in the sense of the class `IsSMulApply`, the definition `FunLike.mulAction` builds the action from the action on the codomain, and `FunLike.smulCommClass` and `FunLike.isScalarTower` give the compatibility classes. The proofs reduce to the codomain, because two bundled maps are equal when they have the same values.

#### Common errors

1. A faithful action on $\alpha$ does not give a faithful action on $\alpha \times \beta$ when $\beta$ is empty, because then $\alpha \times \beta$ is empty. So `Prod.faithfulSMulLeft` needs `Nonempty β`, and `Pi.faithfulSMul` needs that each factor is nonempty. The sum $\alpha \oplus \beta$ has no such condition.
2. A right action is an action of $M^{\mathrm{op}}$, so the scalar is `MulOpposite.op r`, not $r$. The lemma `op_smul_mul` has the factors in reverse order on the right side. Do not use the lemma `smul_smul` of a left action in its place without the reversal.
3. `Equiv.mulAction` is not an instance. If a type already has an action, a second action from an equivalence gives a different instance, and the lemmas of the first action do not apply to it.

### Exercises

1. (A) Let $M$ act on $\alpha$. Show that the diagonal map $\alpha \to \alpha \times \alpha$, $a \mapsto (a, a)$, commutes with the action, and that its image is a union of orbits of $\alpha \times \alpha$.
2. (A) Let $G$ be a group that acts on $\alpha$ and on $\beta$. Describe the orbits of $G$ on $\alpha \oplus \beta$ and on `Option α`. Show that the number of orbits of $\alpha \oplus \beta$ is the sum of the numbers of orbits of $\alpha$ and of $\beta$.
3. (A) Let $M$ be a monoid. Show that $\operatorname{op}(a) \cdot b = b a$ defines an action of $M^{\mathrm{op}}$ on $M$, and that it commutes with the action of $M$ on itself by left multiplication.
4. (B) Let $G$ act on $\alpha$. Show that the extra point none is a fixed point of each element of $G$ in `Option α`. Deduce that the action on `Option α` is not free when $G$ is not trivial, even when the action on $\alpha$ is free, and that the action on $\alpha \times \beta$ is free when the action on $\alpha$ is free.
5. (B) Let $M$ and $N$ act on $\alpha$ with commuting actions. Show that $(m, n) \cdot a = m \cdot (n \cdot a)$ is an action of $M \times N$, and show by an example that it is not an action when the two actions do not commute.
6. (C) Let $G$ act on a finite set $X$, and let $G$ act on $X \times X$ by the product action. Show that $G$ is transitive on the pairs of distinct points if and only if $X \times X$ has at most two orbits. Show that in this case the number of orbits is exactly two when $|X| \ge 2$.

### Reference

<?reference?>
