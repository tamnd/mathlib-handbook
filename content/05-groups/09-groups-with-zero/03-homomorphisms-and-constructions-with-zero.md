---
title: Homomorphisms with zero, adjoining a zero, and constructions
kind: api
modules:
  - Mathlib.Algebra.GroupWithZero.Hom
  - Mathlib.Algebra.GroupWithZero.FunLike
  - Mathlib.Algebra.GroupWithZero.ProdHom
  - Mathlib.Algebra.GroupWithZero.Range
  - Mathlib.Algebra.GroupWithZero.WithZero
  - Mathlib.Algebra.GroupWithZero.InjSurj
  - Mathlib.Algebra.GroupWithZero.Opposite
  - Mathlib.Algebra.GroupWithZero.Pi
  - Mathlib.Algebra.GroupWithZero.Prod
  - Mathlib.Algebra.GroupWithZero.ULift
  - Mathlib.Algebra.GroupWithZero.TransferInstance
  - Mathlib.Algebra.GroupWithZero.Shrink
  - Mathlib.Algebra.GroupWithZero.Indicator
explains:
  E2: [MonoidWithZeroHom, MonoidWithZeroHom.map_eq_zero_iff, WithZero.instGroupWithZero, WithZero.lift', WithZero.unitsWithZeroEquiv, WithZero.withZeroUnitsEquiv, MonoidWithZeroHom.valueGroup, MonoidWithZeroHom.mem_valueGroup_iff_of_comm, Function.Injective.groupWithZero]
  E1: auto
families: []
requires: [V05.C01, V05.C02, V05.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Homomorphisms with zero, adjoining a zero, and constructions

### Overview

A map between monoids with zero that respects the product and the unit need not respect the zero. The constant map with value $1$ from a monoid with zero to itself is a monoid homomorphism, and it sends $0$ to $1$. So the library has a separate type of maps that respect all three: the homomorphisms of monoids with zero, written `M₀ →*₀ N₀`. Absolute values, valuations and the norm of a field are of this kind.

This section first describes this type and its API. Then it treats the construction that adds a zero to a group: if $G$ is a group, then $G \cup \{0\}$ is a group with zero, and each group with zero arises in this way from its group of units. The value groups of valuations in Volume 10 are built with this construction. The section ends with the standard constructions: products, functions, opposites, lifts along injective and surjective maps, and the indicator function in a monoid with zero.

The section uses the homomorphisms of Chapter 2 and the submonoids and subgroups of Chapter 3.

### The library around it

#### Homomorphisms of monoids with zero

The module `Mathlib.Algebra.GroupWithZero.Hom` defines the structure `MonoidWithZeroHom` with the notation `M₀ →*₀ N₀`. A term has three fields beyond the function: `map_zero'`, `map_one'` and `map_mul'`. The structure extends `ZeroHom` and `MonoidHom`, so a homomorphism with zero gives a homomorphism of monoids by `MonoidWithZeroHom.toMonoidHom` and a zero-preserving map by `MonoidWithZeroHom.toZeroHom`. Both maps are injective (`MonoidWithZeroHom.toMonoidHom_injective`).

As for the other bundled maps of Chapter 2, the general lemmas are stated for a class. The class `MonoidWithZeroHomClass F M₀ N₀` says that each term of a `FunLike` type `F` is a homomorphism with zero. So the lemmas `map_zero`, `map_one` and `map_mul` apply to each such map, and a lemma about a general `F` applies at once to ring homomorphisms and to valuations. The function `MonoidWithZeroHom.ofClass` turns a term of such a class into a bundled homomorphism.

The API follows the usual pattern. `MonoidWithZeroHom.id` and `MonoidWithZeroHom.comp` give the identity and the composite, with the simp lemmas `MonoidWithZeroHom.coe_comp`, `MonoidWithZeroHom.comp_id` and `MonoidWithZeroHom.id_comp`. The lemma `MonoidWithZeroHom.ext` gives extensionality, `MonoidWithZeroHom.copy` replaces the function by an equal one with better definitional behaviour, and `MonoidWithZeroHom.cancel_right` cancels a surjective map on the right. When the target is commutative, two homomorphisms have a pointwise product. The map $x \mapsto x^n$ is a homomorphism with zero for $n \neq 0$, by `powMonoidWithZeroHom`, because $0^n = 0$ needs $n \neq 0$. In a commutative monoid with zero, the product $M_0 \times M_0 \to M_0$ is a homomorphism with zero (`mulMonoidWithZeroHom`), and in a commutative group with zero the quotient map $(a, b) \mapsto a / b$ is one too (`divMonoidWithZeroHom`).

There is no zero homomorphism, because a homomorphism with zero sends $1$ to $1$. There is a trivial one when the source has no zero divisors: $\chi(x) = 0$ for $x = 0$ and $\chi(x) = 1$ for $x \neq 0$. It is the unit `1 : M₀ →*₀ N₀`, with `MonoidWithZeroHom.one_apply_def`, `MonoidWithZeroHom.one_apply_zero` and `MonoidWithZeroHom.one_apply_of_ne_zero`. The hypothesis on zero divisors is needed: if $xy = 0$ with $x, y \neq 0$, then $\chi(xy) = 0$ but $\chi(x)\chi(y) = 1$.

**Proposition.** Let $f$ be a homomorphism with zero from a group with zero $G_0$ to a nontrivial monoid with zero. Then $f(x) = 0$ if and only if $x = 0$. This is `MonoidWithZeroHom.map_eq_zero_iff`.

*Proof.* If $x \neq 0$, then $x$ has an inverse, and $1 = f(1) = f(x) f(x^{-1})$. If $f(x) = 0$, then $1 = 0$, which is false in a nontrivial monoid. The converse is $f(0) = 0$. $\square$

The class form of this result is `map_ne_zero`. With it, `map_inv₀` and `map_div₀` say that a homomorphism with zero between groups with zero respects the inverse and the quotient. The two lemmas `NeZero.of_injective` and `NeZero.of_map` move the class `NeZero` along a zero-preserving map.

#### Adjoining a zero to a group

The type `WithZero α` is `α` with one new element $0$. The module `Mathlib.Algebra.GroupWithZero.WithZero` extends the operations of $\alpha$ to `WithZero α` by the rule $0 \cdot x = x \cdot 0 = 0$ and $0^{-1} = 0$. The coercion `α → WithZero α` respects the product, the powers and the inverse, by the `norm_cast` lemmas `WithZero.coe_mul`, `WithZero.coe_pow`, `WithZero.coe_inv` and `WithZero.coe_zpow`. As a monoid homomorphism it is `WithZero.coeMonoidHom`.

**Proposition.** If $G$ is a group, then `WithZero G` is a group with zero. This is the instance `WithZero.instGroupWithZero`.

*Proof.* The product is associative, because a product with a factor $0$ is $0$ on both sides, and a product of elements of $G$ is associative in $G$. The element $0$ is absorbing by definition, and $0 \neq 1$. The inverse of $0$ is $0$. Each $x \neq 0$ is the image of some $g \in G$, and $g \cdot g^{-1} = 1$ in $G$, so $x \cdot x^{-1} = 1$. $\square$

If $G$ is commutative, then `WithZero G` is a commutative group with zero by `WithZero.instCommGroupWithZero`. For a monoid $M$, `WithZero M` is a monoid with zero.

The universal property is the equivalence `WithZero.lift'`. Let $M$ be a monoid and $N_0$ a monoid with zero. Each monoid homomorphism $f \colon M \to N_0$ extends in exactly one way to a homomorphism with zero `WithZero M →*₀ N₀`, by $0 \mapsto 0$. So `WithZero.lift'` is an equivalence `(α →* β) ≃ (WithZero α →*₀ β)`, with `WithZero.lift'_coe` and `WithZero.lift'_zero` as its values. The ext lemma `WithZero.monoidWithZeroHom_ext` says that a homomorphism out of `WithZero α` is determined by its restriction to $\alpha$. The functorial form is `WithZero.map'`: a monoid homomorphism $f$ gives `WithZero.map' f`, and `WithZero.map'_injective_iff` and `WithZero.map'_surjective_iff` say that it is injective or surjective exactly when $f$ is.

The construction inverts the passage from a group with zero to its units.

| Lean name | Statement |
|---|---|
| `WithZero.unitsWithZeroEquiv` | for a group $G$, the units of $G \cup \{0\}$ form a group isomorphic to $G$ |
| `WithZero.withZeroUnitsEquiv` | for a group with zero $G_0$, $G_0^\times \cup \{0\} \cong G_0$ |
| `MulEquiv.withZero` | an isomorphism $G \cong H$ of groups gives $G \cup \{0\} \cong H \cup \{0\}$, and conversely |
| `MulEquiv.unzero` | the inverse direction: an isomorphism $G \cup \{0\} \cong H \cup \{0\}$ gives $G \cong H$ |

The proof of `WithZero.withZeroUnitsEquiv` is direct. The map sends $0$ to $0$ and a unit $u$ to its value. Its inverse sends $0$ to $0$ and $a \neq 0$ to the unit `Units.mk0 a h`. The map needs a decidable test for $a = 0$ to define the inverse. So a group with zero is the same thing as a group with a zero added, and `MulEquiv.unzero` says that the group determines the group with zero up to isomorphism.

In valuation theory the target of a discrete valuation is $\{0\} \cup \{c^n : n \in \mathbb{Z}\}$. The library writes it as `WithZero (Multiplicative ℤ)`, with the scoped notation `ℤᵐ⁰`. For an additive monoid $M$, the module defines `WithZero.exp`, which sends $a$ to the coercion of `Multiplicative.ofAdd a`, and `WithZero.log`, with the junk value $\log 0 = 0$. So `WithZero.exp_add` says $\exp(a + b) = \exp(a) \exp(b)$, `WithZero.log_exp` says $\log(\exp a) = a$, and `WithZero.exp_log` says $\exp(\log x) = x$ for $x \neq 0$. The lemma `WithZero.log_mul` needs both factors nonzero. The junk-free forms are the equivalences `WithZero.expEquiv` and `WithZero.logEquiv` between an additive group and the units of its multiplicative copy with zero, and `WithZero.expRecOn` is the matching recursion principle.

The module `Mathlib.Algebra.GroupWithZero.ProdHom` uses these equivalences to give a product of two groups with zero in the category of groups with zero. The product $G_0 \times H_0$ with the componentwise product is not a group with zero, because $(1, 0)$ is not zero and has no inverse. The library uses `WithZero (G₀ˣ × H₀ˣ)` instead, with the inclusions `MonoidWithZeroHom.inl` and `MonoidWithZeroHom.inr` and the projections `MonoidWithZeroHom.fst` and `MonoidWithZeroHom.snd`. The simp lemmas `MonoidWithZeroHom.fst_inl` and `MonoidWithZeroHom.snd_inr` give the identities, and `MonoidWithZeroHom.snd_comp_inl` says that the other composite is the trivial homomorphism `1`.

#### The value group of a homomorphism

Let $f \colon A \to B$ be a homomorphism with zero. The module `Mathlib.Algebra.GroupWithZero.Range` attaches a group to $f$. The submonoid `MonoidWithZeroHom.valueMonoid f` of $B^\times$ is the set of units that lie in the range of $f$. The subgroup `MonoidWithZeroHom.valueGroup f` of $B^\times$ is the subgroup that this set generates. Adding a zero gives `MonoidWithZeroHom.ValueMonoid₀ f` and `MonoidWithZeroHom.ValueGroup₀ f`, and the second one is a group with zero. For a valuation $v$ of a field, `ValueGroup₀ v` is the smallest group with zero that contains the values of $v$.

The map $f$ factors through its value group. The map `MonoidWithZeroHom.ValueGroup₀.restrict₀ f` sends $a$ into `ValueGroup₀ f`, the map `MonoidWithZeroHom.ValueGroup₀.embedding` sends `ValueGroup₀ f` into $B$, and `MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀` says that the composite is $f$. The embedding is injective, and `MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective` says that the restriction is surjective when $A$ is a group with zero.

When $B$ is a commutative group with zero, the value group has an explicit form. The lemma `MonoidWithZeroHom.mem_valueGroup_iff_of_comm` says that $y \in B^\times$ lies in the value group if and only if $f(a) y = f(x)$ for some $a$ with $f(a) \neq 0$ and some $x$. So each element of the value group is a quotient $f(s)/f(r)$ of two nonzero values. The map `MonoidWithZeroHom.valueGroup.mk f r s hr hs` gives this element, and `MonoidWithZeroHom.valueGroup.mk_eq_div` states its value. The proof of the lemma is an induction on the closure: the quotients $f(s)/f(r)$ contain the generators, contain $1$, and are closed under products and inverses because $f$ is multiplicative.

When the source $A$ is a group with zero, the inverse of a value is a value, so the two constructions agree: `MonoidWithZeroHom.valueMonoid_eq_valueGroup`. The module `Mathlib.Algebra.GroupWithZero.Submonoid.Instances` is the companion for the range submonoid `MonoidHom.mrange f`: it is a monoid with zero, and a group with zero when $f$ goes between groups with zero.

#### Constructions

The structures of monoid with zero and group with zero pass to the usual constructions. Each instance is in a short module.

| Module | Instances |
|---|---|
| `Mathlib.Algebra.GroupWithZero.Prod` | `Prod.instMonoidWithZero` and its relatives on $M_0 \times N_0$ |
| `Mathlib.Algebra.GroupWithZero.Pi` | `Pi.monoidWithZero` and its relatives on $\prod_i M_i$ |
| `Mathlib.Algebra.GroupWithZero.Opposite` | `MulOpposite.instGroupWithZero` and the cancellation classes on $M_0^{\mathrm{op}}$ |
| `Mathlib.Algebra.GroupWithZero.ULift` | `ULift.groupWithZero` and its relatives |
| `Mathlib.Algebra.GroupWithZero.Shrink` | the instances on `Shrink α` for a small type |

Products and functions keep the monoid with zero but not the group with zero, for the reason above. The opposite keeps both. The module on opposites also has `MulOpposite.isLeftCancelMulZero_iff` and its two relatives: the opposite of $M_0$ is left cancellative if and only if $M_0$ is right cancellative. In `Mathlib.Algebra.GroupWithZero.Pi`, the function `Pi.single i` respects the product (`Pi.single_mul`), and `MulHom.single` bundles it as a multiplicative map.

The constructions use a general tool from `Mathlib.Algebra.GroupWithZero.InjSurj`. Let $f \colon M' \to M_0$ be an injective map that respects the zero, the unit, the product and the other operations. Then $M'$ inherits each law of $M_0$, because an identity between images implies the identity between the arguments. This is `Function.Injective.monoidWithZero`, and `Function.Injective.groupWithZero` and `Function.Injective.commGroupWithZero` do the same for groups with zero. Dually, `Function.Surjective.groupWithZero` pushes a structure forward along a surjective map. These are definitions, not instances, so a user applies them by hand to build an instance. The theorems `Function.Injective.noZeroDivisors` and `Function.Injective.isCancelMulZero` pull back the absence of zero divisors and cancellation.

The module `Mathlib.Algebra.GroupWithZero.TransferInstance` transports a structure along an equivalence of types: `Equiv.monoidWithZero e` puts on $\alpha$ the monoid with zero of $\beta$, for $e \colon \alpha \simeq \beta$. The module `Mathlib.Algebra.GroupWithZero.FunLike` gives the same kind of definitions for a `FunLike` type with pointwise operations, such as `FunLike.monoidWithZero`, and for composition as the product, `FunLike.compMonoidWithZero`.

#### Supports and indicators

The module `Mathlib.Algebra.GroupWithZero.Indicator` connects the product with the support and the indicator of a function. The indicator $\mathbf{1}_s f$ agrees with $f$ on $s$ and is $0$ off $s$, and the support of $f$ is the set where $f \neq 0$. The main lemmas are the following.

| Lean name | Statement |
|---|---|
| `Set.indicator_mul` | $\mathbf{1}_s(fg) = \mathbf{1}_s f \cdot \mathbf{1}_s g$ |
| `Set.inter_indicator_one` | $\mathbf{1}_{s \cap t} = \mathbf{1}_s \mathbf{1}_t$ |
| `Set.indicator_one_inj` | $\mathbf{1}_s = \mathbf{1}_t$ implies $s = t$, in a nontrivial monoid with zero |
| `Function.support_mul` | $\operatorname{supp}(fg) = \operatorname{supp} f \cap \operatorname{supp} g$, without zero divisors |
| `Function.support_inv` | $\operatorname{supp}(f^{-1}) = \operatorname{supp} f$ in a group with zero |
| `Function.support_div` | $\operatorname{supp}(f/g) = \operatorname{supp} f \cap \operatorname{supp} g$ in a group with zero |

In a general monoid with zero only the inclusion $\operatorname{supp}(fg) \subseteq \operatorname{supp} f$ holds, as `Function.support_mul_subset_left`. The equality needs `NoZeroDivisors`. The lemma `Function.support_pow` needs a reduced monoid, because a nilpotent value has a power $0$.

#### Common errors

1. The product type `M₀ × N₀` is a monoid with zero but not a group with zero. A proof that needs a product of groups with zero uses `WithZero (G₀ˣ × H₀ˣ)` with `MonoidWithZeroHom.inl` and `MonoidWithZeroHom.inr`.
2. `WithZero.log` has the junk value `WithZero.log 0 = 0`, so `WithZero.log_mul` needs both factors nonzero. Use `WithZero.logEquiv` on the units to avoid side conditions.
3. The trivial homomorphism `1 : M₀ →*₀ N₀` exists only with `NoZeroDivisors M₀` and a decidable test for zero. There is no zero homomorphism `M₀ →*₀ N₀` at all.

### Exercises

1. (A) Show that the constant map with value $1$ on a nontrivial monoid with zero is a monoid homomorphism but not a homomorphism with zero.
2. (A) Use `WithZero.lift'` to extend the inclusion of the units of $\mathbb{Q}$ to a homomorphism with zero `WithZero ℚˣ →*₀ ℚ`, and show that it is bijective.
3. (B) Let $f \colon G_0 \to M_0$ be a homomorphism with zero from a group with zero to a nontrivial monoid with zero. Prove that $f$ is injective if and only if $f(x) = 1$ implies $x = 1$.
4. (B) Prove that $\{0\} \cup \{2^n : n \in \mathbb{Z}\}$ is a subgroup with zero of $\mathbb{Q}$, and that it is isomorphic to `WithZero (Multiplicative ℤ)` by `WithZero.exp`.
5. (B) For the $2$-adic valuation $v$ on $\mathbb{Q}$ with values in `WithZero (Multiplicative ℤ)`, describe the value group with `MonoidWithZeroHom.mem_valueGroup_iff_of_comm`.
6. (C) Prove `Function.support_mul` from the definition of `NoZeroDivisors`, and give a counterexample in $\mathbb{Z}/6$ when the hypothesis fails.

### Reference

<?reference?>
