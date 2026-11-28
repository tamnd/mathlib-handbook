---
title: Ordered monoids on constructions and type synonyms
kind: api
modules:
  - Mathlib.Algebra.Order.Group.Synonym
  - Mathlib.Algebra.Order.Monoid.Unbundled.OrderDual
  - Mathlib.Algebra.Order.Monoid.OrderDual
  - Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
  - Mathlib.Algebra.Order.Monoid.TypeTags
  - Mathlib.Algebra.Order.Monoid.Prod
  - Mathlib.Algebra.Order.Monoid.Lex
  - Mathlib.Algebra.Order.Group.Equiv
  - Mathlib.Algebra.Order.Group.PiLex
  - Mathlib.Algebra.Order.Pi
  - Mathlib.Algebra.Order.PUnit
  - Mathlib.Algebra.Order.Sum
  - Mathlib.Algebra.Order.Group.Opposite
  - Mathlib.Algebra.Order.Monoid.Unbundled.Units
  - Mathlib.Algebra.Order.Monoid.Units
  - Mathlib.Algebra.Order.Group.Units
  - Mathlib.Algebra.Order.Monoid.Submonoid
  - Mathlib.Algebra.Order.Group.Subgroup
explains:
  E2: [toLex_mul, OrderDual.isOrderedMonoid, Multiplicative.isOrderedMonoid, Prod.instIsOrderedMonoid, Prod.Lex.isOrderedMonoid, Pi.isOrderedMonoid, Pi.Lex.isOrderedCancelMonoid, MulOpposite.op_le_op, Units.val_le_val, Submonoid.toIsOrderedMonoid]
  E1: auto
families: []
requires: [V04.C01, V04.C02, V01.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Ordered monoids on constructions and type synonyms

### Overview

The usual constructions of algebra make new monoids from old ones: products, function types, opposites, units and submonoids. The usual constructions of order theory make new orders: the order dual, the lexicographic order and the product order. When a type has both structures, the library must say how they fit together on each construction. This section lists the instances that do this, the conditions they need, and the lemmas that move an element between a type and its synonym.

Most of these files contain only instances, and a proof seldom names them. They matter when instance search fails, and the main cause of failure is a missing hypothesis, such as the strict monotonicity that a lexicographic product needs. The section explains these conditions.

### The library around it

#### Type synonyms

A type synonym such as `OrderDual α` or `Lex α` is the type $\alpha$ with a new order. The file `Mathlib.Algebra.Order.Group.Synonym` copies the algebraic structure of $\alpha$ to the synonyms `OrderDual α`, `Lex α` and `Colex α` without change. The instances have names such as `OrderDual.instGroup` and `Lex.instCommMonoid`. The functions that enter and leave a synonym keep the operations: `toLex_mul` states $\mathrm{toLex}(a b) = \mathrm{toLex}(a)\,\mathrm{toLex}(b)$, and `toDual_mul`, `ofLex_inv` and `toDual_pow` are similar. The file `Mathlib.Algebra.Order.Group.Equiv` makes these functions into isomorphisms, `toLexMulEquiv` and `toLexAddEquiv`.

On the order dual, the order changes but the multiplication does not. If $b \le c$ gives $a b \le a c$ in $\alpha$, then the same holds for the reversed order, because the implication $c \le b \Rightarrow a c \le a b$ is the same statement with the letters exchanged. So each covariant and contravariant class carries over, with instances such as `OrderDual.mulLeftMono` and `OrderDual.mulLeftReflectLE` in `Mathlib.Algebra.Order.Monoid.Unbundled.OrderDual`. The instance `OrderDual.isOrderedMonoid` gives the bundled form. With these instances, the dual of a lemma about ordered monoids is often a direct application of the lemma to `OrderDual α`.

The synonyms `Multiplicative α` and `Additive α` change the name of the operation and keep the order. The file `Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags` gives them the order of $\alpha$, with lemmas such as `Multiplicative.ofAdd_le`, which states $\mathrm{ofAdd}(a) \le \mathrm{ofAdd}(b) \leftrightarrow a \le b$. The instance `Multiplicative.isOrderedMonoid` turns an ordered additive monoid into an ordered monoid, and `Multiplicative.canonicallyOrderedMul` does the same for canonical orders. These instances let a single multiplicative lemma serve, through `Multiplicative`, a type such as $\mathbb{Z}$ whose operation is addition.

#### Products

The product $\alpha \times \beta$ has the order with $(a, b) \le (a', b')$ when $a \le a'$ and $b \le b'$. For this order, `Prod.instIsOrderedMonoid` in `Mathlib.Algebra.Order.Monoid.Prod` gives an ordered monoid, and `Prod.instCanonicallyOrderedAdd` gives a canonical order. The proof is a check in each coordinate. The product order is not linear, even when $\alpha$ and $\beta$ are linear: $(0, 1)$ and $(1, 0)$ are not comparable in $\mathbb{Z} \times \mathbb{Z}$. For a linearly ordered product, use the lexicographic order.

The lexicographic product `Lex (α × β)` compares the first coordinates, and the second coordinates only when the first ones are equal. Here the instance `Prod.Lex.isOrderedMonoid` asks for more than an ordered monoid $\alpha$. It asks for `MulLeftStrictMono α`, so that $a < a'$ gives $c a < c a'$. The reason is this. Suppose $(a, b) < (a', b')$ because $a < a'$, with $b > b'$. Multiplication by $(c, d)$ gives $(c a, d b)$ and $(c a', d b')$. If $c a = c a'$, the comparison goes to the second coordinates, and $b' < b$ can give $d b' < d b$, which is the wrong order. The strict hypothesis excludes $c a = c a'$. The file `Mathlib.Algebra.Order.Monoid.Lex` gives the inclusions as monotone maps. The map `OrderMonoidHom.inlₗ` sends $a$ to $(a, 1)$ in the lexicographic product, and `OrderMonoidHom.inlₗ_mul_inrₗ_eq_toLex` states $(a, 1)(1, b) = (a, b)$.

#### Function types

For a family of ordered monoids $Z_i$, the type of functions $(i : \iota) \to Z_i$ has the pointwise order, and `Pi.isOrderedMonoid` in `Mathlib.Algebra.Order.Pi` makes it an ordered monoid. The same file has lemmas about constant functions and single points. The lemma `Pi.single_le_single` states that $\mathrm{single}_i(a) \le \mathrm{single}_i(b) \leftrightarrow a \le b$, and `Function.const_nonneg` states that a constant function is nonnegative exactly when its value is, for a nonempty domain. The lexicographic order on functions has the instance `Pi.Lex.isOrderedCancelMonoid` in `Mathlib.Algebra.Order.Group.PiLex`, for a linearly ordered index type. In this order $x < y$ when, at some index $i$, the two functions agree below $i$ and $x_i < y_i$. It needs cancellation for the same reason as the lexicographic product.

The file `Mathlib.Algebra.Order.Sum` treats a function on a disjoint union. The lemma `Sum.nonneg_elim_iff` states that the function that is $v_1$ on the left summand and $v_2$ on the right summand is nonnegative exactly when $v_1$ and $v_2$ are. The file `Mathlib.Algebra.Order.PUnit` gives the one-point type its instances, such as `PUnit.canonicallyOrderedAdd`. Such instances let a general statement apply to the trivial case without a special proof.

#### Opposites and units

The opposite monoid $\alpha^{\mathrm{mop}}$ reverses the multiplication and keeps the order. The lemma `MulOpposite.op_le_op` states $\mathrm{op}(a) \le \mathrm{op}(b) \leftrightarrow a \le b$, and `MulOpposite.instIsOrderedMonoid` gives the ordered monoid structure, in `Mathlib.Algebra.Order.Group.Opposite`. In a noncommutative monoid, the opposite exchanges the classes `MulLeftMono` and `MulRightMono`.

The group of units $\alpha^\times$ gets the order of $\alpha$ through the coercion. The lemma `Units.val_le_val` states that $u \le v$ in $\alpha^\times$ exactly when the values satisfy $u \le v$ in $\alpha$, and `Units.orderEmbeddingVal` is the coercion as an order embedding for a linear order. For a commutative monoid, the instance `Units.isOrderedMonoid` gives an ordered commutative group. The file `Mathlib.Algebra.Order.Monoid.Unbundled.Units` has lemmas that move a unit across an inequality in a monoid, as in a group. For example, `Units.inv_mul_le_iff` states $u^{-1} a \le b \leftrightarrow a \le u b$. The lemma `IsUnit.mulLECancellable` states that a unit cancels.

#### Submonoids and subgroups

A submonoid of an ordered monoid is an ordered monoid with the induced order. The instance `Submonoid.toIsOrderedMonoid` in `Mathlib.Algebra.Order.Monoid.Submonoid` states this, and `SubmonoidClass.toIsOrderedMonoid` does the same for each type of submonoids, such as subgroups. The same file defines `Submonoid.oneLE`, the submonoid of elements at least $1$, with the membership lemma `Submonoid.mem_oneLE`. The file `Mathlib.Algebra.Order.Group.Subgroup` gives `Subgroup.topOrderMonoidIso`, the isomorphism from the subgroup $\top$ to the group that keeps the order and the multiplication.

#### Common errors

1. A lemma about `Lex (α × β)` fails to find `IsOrderedMonoid` when $\alpha$ has only `IsOrderedMonoid`. Add the strict class `MulLeftStrictMono α`, which holds for each ordered cancellative monoid.
2. The function `toLex` does not change the data, but the simplifier treats it as a function like any other. Rewrite with `toLex_mul` and the similar lemmas, or use `toLexMulEquiv`, and do not unfold the synonym.
3. On `Multiplicative ℤ`, the element $1$ is the image of $0$ under `Multiplicative.ofAdd`, and not of the integer $1$. Write `Multiplicative.ofAdd 1` for the generator.

### Exercises

1. (A) Show that `OrderDual α` has `MulLeftMono` when $\alpha$ has it, without the instance `OrderDual.mulLeftMono`.
2. (A) Use `Units.val_le_val` to show that in an ordered monoid each unit $u$ with $1 \le u$ satisfies $u^{-1} \le 1$.
3. (B) Find an ordered monoid $\alpha$ without `MulLeftStrictMono` for which multiplication on `Lex (α × ℤ)` is not monotone.
4. (B) Prove that a product of two canonically ordered monoids is canonically ordered, and state the corresponding instance.
5. (B) Show that the lexicographic order on $\mathbb{Z} \times \mathbb{Z}$ makes it a linearly ordered group that is not archimedean.
6. (C) For a linearly ordered index type and ordered cancellative monoids $Z_i$, prove that multiplication on the lexicographic order of functions is strictly monotone.

### Reference

<?reference?>
