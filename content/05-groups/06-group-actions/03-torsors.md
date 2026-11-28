---
title: Torsors of a group
kind: api
modules:
  - Mathlib.Algebra.Torsor.Defs
  - Mathlib.Algebra.Torsor.Basic
explains:
  E2: [Torsor.subsingleton_iff, sdiv_mul_sdiv_cancel, inv_sdiv_eq_sdiv_rev, Equiv.smulConst, Equiv.constSMulHom, sdiv_smul_comm, Equiv.pointReflection_fixed_iff_of_injective_two_nsmul]
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

## Torsors of a group

### Overview

A torsor of a group $G$ is a nonempty set $P$ with an action of $G$ that is free and transitive. For two points $p, q \in P$ there is then exactly one $g \in G$ with $g \cdot q = p$. This element is the quotient of $p$ by $q$, and the notation is $p /_s q$. A torsor is a copy of $G$ that has forgotten its identity element. If a point $p_0$ is chosen, the map $g \mapsto g \cdot p_0$ is a bijection $G \to P$, but no point of $P$ is special.

The standard example is an affine space. The points of a plane form a torsor of the group of translation vectors. Two points have a difference vector, a vector moves a point, but the sum of two points has no meaning. Other examples are the set of bases of a vector space under the general linear group, and the set of solutions of an inhomogeneous linear equation under the group of solutions of the homogeneous equation.

The modules `Mathlib.Algebra.Torsor.Defs` and `Mathlib.Algebra.Torsor.Basic` give the classes `Torsor` and `AddTorsor`, the calculus of the quotient of two points, the equivalences between $G$ and $P$, and torsors of products. The section uses the group actions of Section 1 and the homomorphisms of Chapter 2. Volume 22 builds affine spaces on the additive form.

### The library around it

#### The two classes

The class `Torsor G P` extends `MulAction G P` and `SDiv G P`. The field `SDiv.sdiv` is the quotient map $P \times P \to G$, with the notation `p /ₛ q`. The class asks for two axioms and for `Nonempty P`.

1. `sdiv_smul`: $(p /_s q) \cdot q = p$.
2. `smul_sdiv`: $(g \cdot p) /_s p = g$.

The first axiom says that the action is transitive, with an explicit element that moves $q$ to $p$. The second axiom says that the action is free: if $g \cdot p = h \cdot p$, then $g = (g \cdot p) /_s p = (h \cdot p) /_s p = h$. This is `smul_right_cancel_iff`, and `smul_right_injective'` says that the orbit map $g \mapsto g \cdot p$ is injective. The group $G$ is an `outParam` of the class, so the instance search finds $G$ from $P$.

The class `AddTorsor G P` is the additive form, for an additive group $G$. The action is `VAdd.vadd`, with the notation `g +ᵥ p`, and the difference is `VSub.vsub`, with the notation `p -ᵥ q`. The axioms are `vsub_vadd` and `vadd_vsub`. The attribute `to_additive` gives each multiplicative lemma its additive copy, so the two APIs match name for name: `sdiv` becomes `vsub`, `smul` becomes `vadd`, `one` becomes `zero` and `div` becomes `sub`.

| Multiplicative | Additive | Statement |
|---|---|---|
| `sdiv_smul` | `vsub_vadd` | $(p /_s q) \cdot q = p$ |
| `smul_sdiv` | `vadd_vsub` | $(g \cdot p) /_s p = g$ |
| `sdiv_self` | `vsub_self` | $p /_s p = 1$ |
| `sdiv_eq_one_iff_eq` | `vsub_eq_zero_iff_eq` | $p /_s q = 1 \iff p = q$ |
| `sdiv_mul_sdiv_cancel` | `vsub_add_vsub_cancel` | $(p_1 /_s p_2)(p_2 /_s p_3) = p_1 /_s p_3$ |
| `inv_sdiv_eq_sdiv_rev` | `neg_vsub_eq_vsub_rev` | $(p /_s q)^{-1} = q /_s p$ |
| `smul_sdiv_assoc` | `vadd_vsub_assoc` | $(g \cdot p) /_s q = g\,(p /_s q)$ |
| `sdiv_smul_eq_sdiv_div` | `vsub_vadd_eq_vsub_sub` | $p /_s (g \cdot q) = (p /_s q)\,g^{-1}$ |

Each group is a torsor of itself, by `Group.instTorsor` and `AddGroup.instAddTorsor`. There the quotient of two points is the quotient in the group: `sdiv_eq_div` and `vsub_eq_sub` are simp lemmas that rewrite $p /_s q$ to $p / q$ and $p -_v q$ to $p - q$.

#### The calculus of quotients

Most identities of a torsor follow from the two axioms and the freeness of the action. Here is the proof of the chain rule `sdiv_mul_sdiv_cancel`. Put $g = p_1 /_s p_2$ and $h = p_2 /_s p_3$. Then $(g h) \cdot p_3 = g \cdot (h \cdot p_3) = g \cdot p_2 = p_1$ by `sdiv_smul` twice. Apply $/_s\, p_3$ to both sides and use `smul_sdiv`: $g h = p_1 /_s p_3$. The rule for the inverse follows. Take $p_3 = p_1$ in the chain rule: $(p_1 /_s p_2)(p_2 /_s p_1) = p_1 /_s p_1 = 1$, so $(p_1 /_s p_2)^{-1} = p_2 /_s p_1$. This is `inv_sdiv_eq_sdiv_rev`.

The cancellation lemmas say that division by a fixed point, and division of a fixed point, are injective maps $P \to G$. The lemmas `sdiv_left_cancel_iff` and `sdiv_right_cancel_iff` state $p_1 /_s p = p_2 /_s p \iff p_1 = p_2$ and $p /_s p_1 = p /_s p_2 \iff p_1 = p_2$. Both are simp lemmas. The names `sdiv_left_injective` and `sdiv_right_injective` give the same facts as `Function.Injective` statements.

When $G$ is commutative, more identities hold, because the order of the factors does not matter. The lemma `smul_sdiv_smul_cancel_left` says $(g \cdot p) /_s (g \cdot q) = p /_s q$: a common translation does not change a difference. The lemma `sdiv_div_sdiv_cancel_left` says $(p_3 /_s p_2)/(p_3 /_s p_1) = p_1 /_s p_2$. The lemma `sdiv_smul_comm` says $(p_1 /_s p_2) \cdot p_3 = (p_3 /_s p_2) \cdot p_1$. For an affine plane this is the parallelogram rule: the vector from $p_2$ to $p_1$, applied at $p_3$, gives the same fourth vertex as the vector from $p_2$ to $p_3$, applied at $p_1$. In a commutative group the proof is short. Divide both sides by $p_1$. The right side gives $p_3 /_s p_2$ by `smul_sdiv`. The left side gives $(p_1 /_s p_2)(p_3 /_s p_1)$ by `smul_sdiv_assoc`, and this is $p_3 /_s p_2$ by commutativity and the chain rule. Then cancel by `sdiv_left_cancel_iff`. The additive forms are `vadd_vsub_vadd_cancel_left`, `vsub_sub_vsub_cancel_left` and `vsub_vadd_comm`.

The module `Mathlib.Algebra.Torsor.Basic` also extends the quotient to sets, with the pointwise operation $s /_s t = \{p /_s q : p \in s,\ q \in t\}$ of Chapter 1. The lemma `Set.one_mem_sdiv_iff` says that $1 \in s /_s t$ if and only if $s$ and $t$ meet, and `Set.smul_set_sdiv_smul_set` says that a common translation of two sets does not change their quotient set, for a commutative group. The additive forms are `Set.zero_mem_vsub_iff` and `Set.vadd_set_vsub_vadd_set`.

#### Equivalences between the group and the torsor

The choice of a point $p$ identifies $G$ with $P$. The library gives this identification in two directions.

| Lean name | Map | Inverse |
|---|---|---|
| `Equiv.smulConst p` | $g \mapsto g \cdot p$ | $q \mapsto q /_s p$ |
| `Equiv.constSDiv p` | $q \mapsto p /_s q$ | $g \mapsto g^{-1} \cdot p$ |
| `Equiv.vaddConst p` | $g \mapsto g +_v p$ | $q \mapsto q -_v p$ |
| `Equiv.constVSub p` | $q \mapsto p -_v q$ | $g \mapsto -g +_v p$ |

The two axioms of the class are exactly the two inverse laws of `Equiv.smulConst p`. So a torsor is the same as a nonempty $G$-set on which each orbit map is a bijection. This gives `Torsor.subsingleton_iff`: $G$ is a subsingleton if and only if $P$ is a subsingleton. The proof chooses a point $p$ of the nonempty type $P$ and moves the property along the bijection `Equiv.smulConst p`.

Each $g \in G$ also gives a permutation $p \mapsto g \cdot p$ of $P$. This is `Equiv.constSMul P g`, and the additive form is `Equiv.constVAdd P g`. The simp lemmas `Equiv.constSMul_one` and `Equiv.constSMul_mul` say that $g \mapsto$ `Equiv.constSMul P g` respects the unit and the product, and `Equiv.constSMulHom` bundles it as a homomorphism `G →* Equiv.Perm P`. For an additive group $G$, the target `Equiv.Perm P` is a multiplicative group, so the homomorphism `Equiv.constVAddHom` starts from `Multiplicative G`. The homomorphism `Equiv.constSMulHom` is injective, because the action is free. It is the permutation representation of Section 1 for this action.

#### Point reflections

In an additive torsor, the point reflection in $x$ sends $y$ to the point $x + (x - y)$. In Lean this is `Equiv.pointReflection x`, a permutation of $P$, and `Equiv.pointReflection_apply` gives `pointReflection x y = (x -ᵥ y) +ᵥ x`. The library proves the expected facts.

1. `Equiv.pointReflection_self`: $x$ is fixed.
2. `Equiv.pointReflection_involutive`: the reflection is an involution, and `Equiv.pointReflection_symm` says that it is its own inverse.
3. `Equiv.pointReflection_vsub_left` and `Equiv.pointReflection_vsub_right`: the image $y'$ of $y$ satisfies $y' - x = x - y$ and $y' - y = 2(x - y)$.
4. `Equiv.pointReflection_eq_subLeft`: in an additive commutative group, the reflection in $x$ is $y \mapsto 2x - y$, that is `Equiv.subLeft (2 • x)`.

Is $x$ the only fixed point? A fixed point $y$ satisfies $(x - y) + x = y$, so $2(x - y) = 0$. If multiplication by $2$ is injective on $G$, then $x = y$. Without this hypothesis the claim fails: in $\mathbb{Z}/2$ each reflection is the identity. The lemma `Equiv.pointReflection_fixed_iff_of_injective_two_nsmul` takes the injectivity of $g \mapsto 2 \cdot g$ as an explicit hypothesis, because no class states it. The lemma `Equiv.injective_pointReflection_left_of_injective_two_nsmul` uses the same hypothesis to show that $y$ and its image determine the centre.

#### Products and transport

A product of torsors is a torsor of the product group. The instance `Prod.instTorsor` makes $P \times P'$ a torsor of $G \times G'$, and `Pi.instTorsor` makes $\prod_i P_i$ a torsor of $\prod_i G_i$. The quotient is computed in each coordinate: `Prod.mk_sdiv_mk`, `Prod.fst_sdiv` and `Pi.sdiv_apply` are simp lemmas. The lemma `Set.prod_sdiv_prod_comm` gives the same rule for products of sets.

Two constructors transport a torsor structure along a map. If $f : Q \to P$ is injective and respects the action and the quotient, then `Function.Injective.torsor` gives $Q$ a torsor structure. If $f : P \to Q$ is surjective and respects them, then `Function.Surjective.torsor` gives $Q$ a torsor structure. They are `abbrev` definitions, to use in a `where` block of an instance, like the transport constructors of Chapter 1. The additive forms are `Function.Injective.addTorsor` and `Function.Surjective.addTorsor`.

#### Common errors

1. The quotient `p /ₛ q` is not the division `p / q`. For a group acting on itself, `sdiv_eq_div` rewrites one to the other. For a general torsor, `P` has no division at all, and `p / q` does not elaborate.
2. The group is an `outParam`. A type `P` can be a torsor of only one group up to the instance search, so a second `Torsor` instance on the same `P` for another group gives confusing goals. Use a type synonym for the second structure.
3. The commutative lemmas such as `sdiv_smul_comm` and `smul_sdiv_smul_cancel_left` need `CommGroup G`. For a noncommutative group, $(g \cdot p) /_s (g \cdot q)$ is the conjugate $g\,(p /_s q)\,g^{-1}$, not $p /_s q$.

### Exercises

1. (A) Prove from the two axioms of `Torsor` that $p /_s p = 1$ for each point $p$.
2. (A) Let $H$ be a subgroup of $G$ and $a \in G$. Show that the right coset $Ha$ is a torsor of $H$ under the action $h \cdot x = h x$, and compute the quotient of two points.
3. (B) Prove `sdiv_smul_eq_sdiv_div`: $p /_s (g \cdot q) = (p /_s q)\,g^{-1}$, with the chain rule and `inv_sdiv_eq_sdiv_rev`.
4. (B) Show that the set of solutions of $f(x) = b$, for a group homomorphism $f : G \to H$ and $b$ in the range of $f$, is a torsor of the kernel of $f$.
5. (B) In a torsor of a commutative group, prove $(g \cdot p) /_s (h \cdot q) = (g/h)\,(p /_s q)$. Compare with `smul_sdiv_smul_comm`.
6. (C) Let $P$ be a torsor of $G$ and let $\varphi : P \to P$ commute with the action of $G$. Show that there is $c \in G$ with $\varphi(g \cdot p_0) = g c \cdot p_0$ for all $g \in G$, where $p_0$ is a fixed point. Deduce that the group of $G$-equivariant permutations of $P$ is isomorphic to the opposite group of $G$.

### Reference

<?reference?>
