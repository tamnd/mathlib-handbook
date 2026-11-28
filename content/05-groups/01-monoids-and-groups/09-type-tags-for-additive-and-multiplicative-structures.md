---
title: Type tags for additive and multiplicative structures
kind: api
modules:
  - Mathlib.Algebra.Group.TypeTags.Basic
  - Mathlib.Algebra.Group.TypeTags.Finite
  - Mathlib.Algebra.Group.TypeTags.Hom
  - Mathlib.Algebra.Group.Equiv.TypeTags
  - Mathlib.Algebra.Group.Int.TypeTags
  - Mathlib.Algebra.Group.Nat.TypeTags
explains:
  E2: [Multiplicative.ofAdd, Additive.ofMul, ofAdd_add, ofAdd_nsmul, AddMonoidHom.toMultiplicative, MonoidHom.toAdditive, MulEquiv.toAdditive, Int.ofAdd_mul]
  E1: auto
families: []
requires: [V01.C03, V01.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Type tags for additive and multiplicative structures

### Overview

A group is the same mathematical object in additive notation and in multiplicative notation. Lean distinguishes the two, because `Group G` and `AddGroup G` are different classes with different operations. Most of the time the attribute to_additive produces both forms of each result, so the reader does not see the difference. Sometimes, however, a construction needs the other notation for the same type. The group $\mathbb{Z}$ with addition is the infinite cyclic group, and a theorem about cyclic groups in multiplicative notation needs a multiplicative copy of it. The units of a ring form a multiplicative group, and a theorem about abelian groups in additive notation needs an additive copy.

The type tags solve this problem. For a type `α`, the type `Multiplicative α` is a copy of `α` in which the addition of `α` becomes the product. The type `Additive α` is a copy in which the product of `α` becomes the addition. This section describes the tags, the maps between a type and its copy, and the transfer of homomorphisms and isomorphisms. It needs only the classes of Chapter 1 and the homomorphisms of Chapter 2.

### The library around it

#### The tags and their equivalences

**Definition (Type tags).** For a type `α`, the types `Multiplicative α` and `Additive α` are equal to `α` as types. The instance `Multiplicative.mul` defines the product on `Multiplicative α` as the sum in `α`, and `Additive.add` defines the sum on `Additive α` as the product in `α`.

The tags are definitions, not structures, so Lean does not see through them during instance search. This is the reason for their use: the instances of `α` do not leak into the copy. To move an element between `α` and its copy, the library uses two equivalences of types:

| Lean name | Statement |
|---|---|
| `Multiplicative.ofAdd` | `α ≃ Multiplicative α` |
| `Multiplicative.toAdd` | `Multiplicative α ≃ α` |
| `Additive.ofMul` | `α ≃ Additive α` |
| `Additive.toMul` | `Additive α ≃ α` |

The pairs are mutual inverses, by `ofAdd_toAdd` and `toAdd_ofAdd`, and by `Multiplicative.ofAdd_symm_eq`, which states that the inverse of `Multiplicative.ofAdd` is `Multiplicative.toAdd`. The lemmas `Multiplicative.forall` and `Multiplicative.exists` turn a quantifier over the copy into a quantifier over `α`, and `Multiplicative.ext` gives equality in the copy from equality in `α`.

The tags carry each structure of the hierarchy across. A group structure gives an additive group structure on the copy: the instances `Multiplicative.group`, `Multiplicative.commGroup`, `Additive.addGroup` and `Additive.addCommGroup` are examples, and the list continues with the cancellative monoids, the division monoids and the involutive inverses. The predicates of Chapter 1 also pass, for example by `instIsMulTorsionFreeMultiplicativeOfIsAddTorsionFree`. The equality and the finiteness of `α` pass to the copy: `instDecidableEqMultiplicative`, `Multiplicative.fintype`, `instFiniteMultiplicative` and `instInfiniteMultiplicative`. The lemmas `Fintype.card_multiplicative` and `Fintype.card_additive` state that the copy has the same number of elements.

#### The simp lemmas for the operations

**Theorem (The tags carry the operations).** For $x, y \in \alpha$ with an addition, $\operatorname{ofAdd}(x + y) = \operatorname{ofAdd}(x) \operatorname{ofAdd}(y)$. In an additive monoid, $\operatorname{ofAdd}(0) = 1$ and $\operatorname{ofAdd}(n \cdot x) = \operatorname{ofAdd}(x)^n$.

*Proof.* The product on `Multiplicative α` is the sum of `α` by definition, so the first two equations hold by definition. The third follows by induction on $n$ from the first two. $\square$

The lemmas are `ofAdd_add`, `ofAdd_zero` and `ofAdd_nsmul`. Each of the four equivalences has a lemma for each operation, with a name of the form `<map>_<operation>`:

| Lean name | Statement |
|---|---|
| `ofAdd_add` | $\operatorname{ofAdd}(x + y) = \operatorname{ofAdd} x \cdot \operatorname{ofAdd} y$ |
| `ofAdd_neg` | $\operatorname{ofAdd}(-x) = (\operatorname{ofAdd} x)^{-1}$ |
| `ofAdd_sub` | $\operatorname{ofAdd}(x - y) = \operatorname{ofAdd} x / \operatorname{ofAdd} y$ |
| `ofAdd_zsmul` | $\operatorname{ofAdd}(z \cdot a) = (\operatorname{ofAdd} a)^z$ |
| `toAdd_mul` | $\operatorname{toAdd}(x y) = \operatorname{toAdd} x + \operatorname{toAdd} y$ |
| `ofMul_mul` | $\operatorname{ofMul}(x y) = \operatorname{ofMul} x + \operatorname{ofMul} y$ |
| `ofMul_pow` | $\operatorname{ofMul}(a^n) = n \cdot \operatorname{ofMul} a$ |
| `toMul_add` | $\operatorname{toMul}(x + y) = \operatorname{toMul} x \cdot \operatorname{toMul} y$ |

All of them are simp lemmas. The simp normal form pushes the maps inside, so the simp tactic turns a statement about the copy into a statement about `α`. The lemmas `ofAdd_eq_one` and `ofMul_eq_zero` state that the identity corresponds to the zero. The regularity predicates also pass, for example `isRegular_ofAdd`.

On the numbers the product of `α` meets the tag. The lemmas `Nat.ofAdd_mul` and `Int.ofAdd_mul` state $\operatorname{ofAdd}(a b) = \operatorname{ofAdd}(a)^b$: in `Multiplicative ℤ`, the generator $\operatorname{ofAdd} 1$ raised to the power $b$ is $\operatorname{ofAdd} b$. The lemmas `Int.toAdd_zpow` and `Nat.toAdd_pow` give the converse direction. So `Multiplicative ℤ` is the free group on one generator in multiplicative notation, and the cyclic groups of Chapter 3 use it.

#### Homomorphisms and isomorphisms

**Theorem (Transfer of homomorphisms).** For additive monoids $A$ and $B$, the additive homomorphisms $A \to B$ correspond bijectively to the monoid homomorphisms `Multiplicative A →* Multiplicative B`.

*Proof.* Send $f$ to $\operatorname{ofAdd} \circ f \circ \operatorname{toAdd}$. The product in the copy is the sum, so this map is multiplicative exactly when $f$ is additive. The inverse sends $g$ to $\operatorname{toAdd} \circ g \circ \operatorname{ofAdd}$. $\square$

The equivalence is `AddMonoidHom.toMultiplicative`, and `MonoidHom.toAdditive` is the form for monoid homomorphisms. There are also mixed forms, in which only one side has a tag. The names end with Left or Right, by the side of the tag in the target type: `MonoidHom.toAdditiveLeft` is `(α →* Multiplicative β) ≃ (Additive α →+ β)`, and `AddMonoidHom.toMultiplicativeRight` is `(Additive α →+ β) ≃ (α →* Multiplicative β)`. The lemmas with the prefix coe, such as `MonoidHom.coe_toAdditive`, give the function as a composite. The lemmas `Additive.addMonoidHom_ext` and `Multiplicative.monoidHom_ext` give the extension principle for maps out of a copy. When the target is commutative, the equivalence respects the group structure on the homomorphisms: `AddMonoidHom.toMultiplicativeLeftAddEquiv` and `MonoidHom.toAdditiveRightMulEquiv` are examples.

The module `Mathlib.Algebra.Group.Equiv.TypeTags` does the same for isomorphisms. The equivalence `MulEquiv.toAdditive` sends `G ≃* H` to `Additive G ≃+ Additive H`, and `AddEquiv.toMultiplicative` is the converse construction. A double tag is the identity, up to isomorphism: `AddEquiv.additiveMultiplicative G` is `Additive (Multiplicative G) ≃+ G`, and `MulEquiv.multiplicativeAdditive H` is `Multiplicative (Additive H) ≃* H`. The tags commute with products and with functions: `MulEquiv.prodMultiplicative` and `MulEquiv.piMultiplicative` are examples. The monoid of endomorphisms is the same on both sides, by `MulEquiv.monoidEnd` and `MulEquiv.addMonoidEnd`.

#### Common errors

1. A learner writes `(x : Multiplicative ℤ) * y` and expects the product of integers. The product in the copy is the sum of integers. Use `Multiplicative.ofAdd` to make an element, and the simp set with `toAdd_mul` to compute.
2. A learner coerces an integer to `Multiplicative ℤ` with a type ascription and gets an error or a wrong instance. There is no coercion. Write `Multiplicative.ofAdd n`, and not `(n : Multiplicative ℤ)`.
3. A learner applies a lemma of `α` directly to an element of the copy. The instances do not pass through the tag. Move the statement to `α` with `Multiplicative.toAdd` or `Additive.toMul` first.

### Exercises

1. (A) Prove $\operatorname{ofAdd}(3) = \operatorname{ofAdd}(1)^3$ in `Multiplicative ℤ` with `Int.ofAdd_mul`.
2. (A) Prove that `Multiplicative (ZMod n)` has $n$ elements for $n \neq 0$, with `Fintype.card_multiplicative`.
3. (B) Let $G$ be a group. Show that the map $g \mapsto g^2$ is an additive homomorphism of `Additive G` when $G$ is commutative, and construct it with `MonoidHom.toAdditive`.
4. (B) Show that `MonoidHom.toAdditive` sends the composite of two homomorphisms to the composite of their images.
5. (B) Let $G$ be a group. Show that the monoid homomorphisms `Multiplicative ℤ →* G` correspond to the elements of $G$, by the value at $\operatorname{ofAdd} 1$. Compare the result with `zpowersHom`.
6. (C) Prove that a group $G$ is cyclic if and only if `Additive G` is an additive cyclic group, and find the Lean names of the two predicates.

### Reference

<?reference?>
