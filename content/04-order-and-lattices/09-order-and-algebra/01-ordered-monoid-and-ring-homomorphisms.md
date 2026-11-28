---
title: Ordered monoid and ring homomorphisms
kind: api
modules:
  - Mathlib.Algebra.Order.Hom.Monoid
  - Mathlib.Algebra.Order.Hom.MonoidWithZero
  - Mathlib.Algebra.Order.Hom.Ring
  - Mathlib.Algebra.Order.Hom.Lattice
  - Mathlib.Algebra.Order.Hom.Submonoid
  - Mathlib.Algebra.Order.Hom.TypeTags
  - Mathlib.Algebra.Order.Hom.Units
  - Mathlib.Algebra.Order.Group.End
  - Mathlib.Algebra.Order.Group.Action.End
  - Mathlib.Algebra.Order.Hom.Basic
  - Mathlib.Algebra.Order.Hom.GroupNorm
  - Mathlib.Algebra.Order.Hom.RingNorm
explains:
  E2: [OrderMonoidHom, OrderMonoidWithZeroHom, OrderRingHom, OrderRingIso, monotone_iff_map_nonneg, SubadditiveHomClass, NonarchimedeanHomClass, AddGroupSeminormClass, map_sub_le_add, RingSeminormClass]
  E1: auto
families: []
requires: [V04.C02, V04.C08, V01.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Ordered monoid and ring homomorphisms

### Overview

Chapter 2 bundles the monotone maps between two orders as `OrderHom`, and the algebra volumes bundle the maps that keep an operation, such as `MonoidHom` and `RingHom`. A map between two ordered monoids that keeps both structures needs a third kind of bundle. This section describes these bundles for monoids, monoids with zero and rings, with the lemmas that link the order and the algebra for such maps.

The second part of the section treats maps that satisfy an inequality in place of an equation. A seminorm $p$ on a group satisfies $p(x y) \le p(x) + p(y)$, and an absolute value on a ring satisfies $|x y| = |x| |y|$ and $|x + y| \le |x| + |y|$. The library states these properties as classes of functions, so one lemma serves all the types of seminorms and norms. The section ends with the monoids of order maps of an order to itself.

### The library around it

#### Bundled maps of ordered monoids

The structure `OrderMonoidHom α β` is a monoid map from $\alpha$ to $\beta$ that is monotone, in `Mathlib.Algebra.Order.Hom.Monoid`. Its notation is `α →*o β`, and the additive form is `OrderAddMonoidHom` with the notation `α →+o β`. The constructor `OrderMonoidHom.mk` takes a monoid map and a proof that it is monotone. The maps `OrderMonoidHom.toMonoidHom` and `OrderMonoidHom.toOrderHom` forget one of the two structures. The composition is `OrderMonoidHom.comp`, the identity is `OrderMonoidHom.id`, and in a commutative ordered monoid the pointwise product of two such maps is again one, by `OrderMonoidHom.instMulOfIsOrderedMonoid`. The isomorphisms are `OrderMonoidIso`, with the notation `α ≃*o β`.

The general lemmas use the classes of functions. A type $F$ of maps with `OrderHomClass` and `MonoidHomClass` behaves as a type of ordered monoid maps, and `OrderMonoidHomClass.toOrderMonoidHom` turns an element of $F$ into an `OrderMonoidHom`.

For additive groups, monotonicity reduces to a condition at $0$. The lemma `monotone_iff_map_nonneg` states that an additive map $f$ is monotone if and only if $0 \le a$ gives $0 \le f(a)$. The proof uses $f(b) - f(a) = f(b - a)$: if $a \le b$ then $0 \le b - a$, and the condition gives $0 \le f(b) - f(a)$. The lemmas `strictMono_iff_map_pos` and `antitone_iff_map_nonpos` are the other cases. The lemma `MonoidHomClass.ext_iff_le` states that two monoid maps from a group are equal if one is below the other at each point. The reason is that $f(x) \le g(x)$ and $f(x^{-1}) \le g(x^{-1})$ give $g(x) \le f(x)$ after multiplication.

The structure `OrderMonoidWithZeroHom` in `Mathlib.Algebra.Order.Hom.MonoidWithZero` keeps also $0$, with the notation `α →*₀o β`. The structure `OrderRingHom` in `Mathlib.Algebra.Order.Hom.Ring` is a monotone ring map, with the notation `α →+*o β`, and `OrderRingIso` is an isomorphism of rings that keeps the order in both directions. The lemma `OrderRingIso.map_le_map_iff'` states the last property. The inclusion of $\mathbb{Q}$ in $\mathbb{R}$ is an example of an ordered ring map, and so is the identity of each ordered ring. An ordered ring map from a field is injective, as each ring map from a field to a nontrivial ring is, but it need not be surjective, so an `OrderRingHom` that is bijective still needs a proof of the order in the reverse direction before it becomes an `OrderRingIso`.

#### Constructions of maps

Several files build maps for the constructions of Chapter 8. The file `Mathlib.Algebra.Order.Hom.TypeTags` gives `Multiplicative.ofAddOrderIso`, the identity function from $M$ to `Multiplicative M` as an order isomorphism, with the form `Additive.ofMulOrderIso` in the other direction. The file `Mathlib.Algebra.Order.Hom.Units` gives `OrderMonoidIso.unitsCongr`, which turns an isomorphism of ordered monoids into an isomorphism of their groups of units. The file `Mathlib.Algebra.Order.Hom.Submonoid` gives `Submonoid.topOrderMonoidIso`, the isomorphism from the submonoid $\top$ to the monoid. The file `Mathlib.Algebra.Order.Hom.Lattice` gives `Finite.iSup_eq_iSup_subtype`, which removes the zero terms from a finite supremum of values of a map that is nonnegative and sends $0$ to $0$.

#### Maps that satisfy an inequality

The file `Mathlib.Algebra.Order.Hom.Basic` defines classes for functions that satisfy an inequality. The class `SubadditiveHomClass F α β` states $f(a + b) \le f(a) + f(b)$, and `SubmultiplicativeHomClass` states $f(a b) \le f(a) f(b)$. The class `MulLEAddHomClass` states $f(a b) \le f(a) + f(b)$, which is the form of a seminorm on a multiplicative group. The class `NonarchimedeanHomClass` states $f(a + b) \le \max(f(a), f(b))$, the inequality of a nonarchimedean absolute value. The class `NonnegHomClass` states $0 \le f(a)$. From these classes the file proves the forms with subtraction: `le_map_add_map_sub` states $f(a) \le f(b) + f(a - b)$, which follows from $a = b + (a - b)$.

The file `Mathlib.Algebra.Order.Hom.GroupNorm` combines these classes. The class `AddGroupSeminormClass` asks for $f(0) = 0$, subadditivity and $f(-a) = f(a)$, and `AddGroupNormClass` adds that $f(a) = 0$ gives $a = 0$. The lemma `map_sub_le_add` states $f(x - y) \le f(x) + f(y)$, and `map_sub_rev` states $f(x - y) = f(y - x)$. The lemma `abs_sub_map_le_sub` is the reverse triangle inequality $|f(x) - f(y)| \le f(x - y)$. For a norm, `map_eq_zero_iff_eq_zero` states $f(x) = 0 \leftrightarrow x = 0$. The multiplicative forms are `GroupSeminormClass` and `GroupNormClass`.

The file `Mathlib.Algebra.Order.Hom.RingNorm` gives the classes for rings. The class `RingSeminormClass` asks for an additive group seminorm that is submultiplicative, and `RingNormClass` adds that only $0$ has norm $0$. The classes `MulRingSeminormClass` and `MulRingNormClass` ask for multiplicativity, $f(x y) = f(x) f(y)$, as for an absolute value. The lemma `one_le_map_one` states $1 \le f(1)$ for a ring norm on a nontrivial ring. Its proof is short: $f(1) = f(1 \cdot 1) \le f(1)^2$, and $f(1) > 0$ because $1 \ne 0$. The bundled seminorms and norms that have these classes are in the volume on normed spaces.

#### Monoids of order maps

The order maps of an order to itself form a monoid under composition. The file `Mathlib.Algebra.Order.Group.End` gives the instances `OrderHom.instMonoid` for monotone maps and `RelIso.instGroup` for the isomorphisms of a relation, with the product as composition. The file `Mathlib.Algebra.Order.Group.Action.End` lets these monoids act on the order by application, as the instance `RelHom.applyMulAction`, and states that the action is faithful. So a monotone map of an order to itself is the same as an element of this monoid, and the general lemmas about monoid actions apply to the monotone maps and to the order isomorphisms. The powers $f^n$ in this monoid are the iterates of $f$.

#### Common errors

1. The product in `RelIso.instGroup` is composition with the left factor applied last, so $(e_1 e_2)(x) = e_1(e_2(x))$. A proof that uses the order of the factors should rewrite with `RelIso.mul_def` first.
2. A lemma about an `AddGroupSeminormClass` does not apply to a function that only satisfies the inequality. Bundle the function as a seminorm first, or prove the class for its type.
3. The lemma `monotone_iff_map_nonneg` needs groups, not monoids. For an additive map between canonically ordered monoids such as $\mathbb{N}$, prove monotonicity from the definition: $a \le a + c$ gives $f(a) \le f(a) + f(c) = f(a + c)$.

### Exercises

1. (A) Prove `monotone_iff_map_nonneg` without the lemma itself.
2. (A) Show that the map $x \mapsto 2x$ on $\mathbb{Z}$ is an `OrderAddMonoidHom`, and that $x \mapsto -x$ is not.
3. (B) Prove `abs_sub_map_le_sub` from `le_map_add_map_sub` and `map_sub_rev`.
4. (B) Prove `MonoidHomClass.ext_iff_le` for two monoid maps from a group to an ordered monoid.
5. (B) Show that the $p$-adic absolute value on $\mathbb{Q}$ satisfies the inequality of `NonarchimedeanHomClass`, and that the usual absolute value does not.
6. (C) Prove `one_le_map_one`, and show that the hypothesis that the ring is nontrivial is necessary.

### Reference

<?reference?>
