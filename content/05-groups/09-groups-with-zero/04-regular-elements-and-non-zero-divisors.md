---
title: Regular elements and non-zero-divisors
kind: api
modules:
  - Mathlib.Algebra.Regular.Defs
  - Mathlib.Algebra.Regular.Basic
  - Mathlib.Algebra.Regular.Pow
  - Mathlib.Algebra.Regular.Opposite
  - Mathlib.Algebra.Regular.Pi
  - Mathlib.Algebra.Regular.Prod
  - Mathlib.Algebra.Regular.ULift
  - Mathlib.Algebra.Regular.SMul
  - Mathlib.Algebra.GroupWithZero.Regular
  - Mathlib.Algebra.GroupWithZero.Action.Regular
  - Mathlib.Algebra.GroupWithZero.NonZeroDivisors
  - Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
  - Mathlib.Algebra.GroupWithZero.Submonoid.Instances
explains:
  E2: [IsLeftRegular, IsRegular, IsLeftRegular.mul, IsRegular.pow_iff, IsUnit.isRegular, isRegular_iff_ne_zero, IsSMulRegular, nonZeroDivisors, IsRegular.mem_nonZeroDivisors, nonZeroDivisorsEquivUnits]
  E1: auto
families: []
requires: [V05.C01, V05.C03, V05.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Regular elements and non-zero-divisors

### Overview

In a group each element can be cancelled: $ab = ac$ implies $b = c$. In a monoid only some elements have this property. An element $a$ is *left regular* if the map $x \mapsto ax$ is injective, *right regular* if $x \mapsto xa$ is injective, and *regular* if it is both. In a monoid with zero there is a weaker notion: $a$ is a *non-zero-divisor* if $ax = 0$ implies $x = 0$ and $xa = 0$ implies $x = 0$. In a ring the two notions agree, because $ab = ac$ is the same as $a(b - c) = 0$. In a monoid with zero they differ.

These notions control localization. A fraction $a/s$ makes sense when $s$ can be cancelled, and the total ring of fractions of a commutative ring inverts exactly the non-zero-divisors. So the submonoid of non-zero-divisors appears in each later volume on rings. This section gives the definitions, the closure properties, the version for an action, and the submonoid `nonZeroDivisors` with its notation.

The section uses units from Chapter 1, submonoids from Chapter 3 and actions from Chapter 6.

### The library around it

#### Regular elements in a semigroup

The module `Mathlib.Algebra.Regular.Defs` defines the three predicates for a type with a product.

| Lean name | Definition |
|---|---|
| `IsLeftRegular c` | the map $x \mapsto c x$ is injective |
| `IsRightRegular c` | the map $x \mapsto x c$ is injective |
| `IsRegular c` | a structure with fields `IsRegular.left` and `IsRegular.right` |

The first two are definitions in terms of `Function.Injective`, so a proof of `IsLeftRegular c` is a function that takes `c * x = c * y` to `x = y`. The lemma `isRegular_iff` splits a regular element into its two halves. The attribute `to_additive` gives the additive forms `IsAddLeftRegular`, `IsAddRightRegular` and `IsAddRegular`, and each result below has its additive copy.

The module `Mathlib.Algebra.Regular.Basic` proves the closure properties. The pattern of names is uniform: a lemma about left regular elements starts with `IsLeftRegular`, and the same lemma for right or two-sided regularity starts with `IsRightRegular` or `IsRegular`.

**Proposition.** In a semigroup, a product of two left regular elements is left regular, and if $ab$ is left regular then $b$ is left regular. These are `IsLeftRegular.mul` and `IsLeftRegular.of_mul`.

*Proof.* The map $x \mapsto (ab)x$ is the composite of $x \mapsto bx$ and $y \mapsto ay$, by associativity. A composite of injective maps is injective. For the second claim, if the composite $x \mapsto a(bx)$ is injective, then its first factor $x \mapsto bx$ is injective. $\square$

The order matters on the right side: `IsRightRegular.of_mul` says that if $ba$ is right regular then $b$ is right regular. The lemma `mul_isLeftRegular_iff` packs both directions when $a$ is known to be left regular. In a commutative semigroup `isRegular_mul_iff` says that $ab$ is regular if and only if both $a$ and $b$ are. If $a$ commutes with each element, then left and right regularity agree, by `Commute.isRegular_iff`.

In a monoid there are more facts. The unit $1$ is regular (`isRegular_one`). Each unit is regular, by `Units.isRegular` and `IsUnit.isRegular`: if $u v = 1$, then $u x = u y$ gives $x = v u x = v u y = y$. More generally `isLeftRegular_of_mul_eq_one` says that $a$ is left regular when $a$ has a left inverse $b$, with $ba = 1$. Powers keep regularity, by `IsLeftRegular.pow`, and `IsRegular.pow_iff` gives the converse.

**Proposition.** Let $a$ be an element of a monoid and $n > 0$. Then $a^n$ is regular if and only if $a$ is regular.

*Proof.* If $a$ is regular, then $a^n$ is a product of regular elements, so it is regular. Conversely, $a^n = a^{n-1} \cdot a = a \cdot a^{n-1}$. The first form and `IsRightRegular.of_mul` give that $a$ is right regular. The second form and `IsLeftRegular.of_mul` give that $a$ is left regular. $\square$

The lemma `IsDedekindFiniteMonoid.iff_isLeftRegular_of_mul_eq_one` connects regularity with Dedekind-finite monoids, where $xy = 1$ implies $yx = 1$. The module `Mathlib.Algebra.Regular.Pow` gives the finite products: `IsRegular.prod` says that a product $\prod_{i \in s} f(i)$ over a finite set in a commutative monoid is regular when each factor is regular.

#### Constructions

The predicates pass through the usual constructions in a predictable way.

| Lean name | Statement |
|---|---|
| `isRegular_op` | $a^{\mathrm{op}}$ is regular if and only if $a$ is regular |
| `isLeftRegular_op` | $a^{\mathrm{op}}$ is left regular if and only if $a$ is right regular |
| `Pi.isRegular_iff` | a function is regular if and only if each value is regular |
| `Prod.isRegular_mk` | $(a, b)$ is regular if and only if $a$ and $b$ are regular |
| `ULift.isRegular_up` | the lift of $a$ is regular if and only if $a$ is regular |

The opposite exchanges left and right, so `IsLeftRegular.op` takes a right regular element to a left regular one. The modules `Mathlib.Algebra.Regular.Opposite`, `Mathlib.Algebra.Regular.Pi`, `Mathlib.Algebra.Regular.Prod` and `Mathlib.Algebra.Regular.ULift` hold these lemmas, each with its left, right and additive forms. `IsRegular.prodMk` is the one-way form for pairs.

#### Regular elements and zero

The module `Mathlib.Algebra.GroupWithZero.Regular` relates regularity to the zero. The element $0$ is regular only in the trivial monoid: `isRegular_iff_subsingleton` says that $0$ is regular if and only if the type has at most one element. So in a nontrivial monoid with zero a regular element is nonzero, by `IsRegular.ne_zero`, and `not_isRegular_zero` says that $0$ is not regular. A left regular element $b$ cancels zero: `IsLeftRegular.mul_left_eq_zero_iff` says that $ba = 0$ if and only if $a = 0$, because $ba = 0 = b \cdot 0$.

**Proposition.** In a nontrivial monoid with zero with cancellation by nonzero elements, an element is regular if and only if it is nonzero. This is `isRegular_iff_ne_zero`.

*Proof.* A regular element is nonzero, as above. Conversely, the class `IsCancelMulZero` says that $ab = ac$ implies $b = c$ when $a \neq 0$, and the same on the right. These are the two halves of regularity, by `IsRegular.of_ne_zero`. $\square$

The module `Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero` gives the instances `MulZeroMemClass.isLeftCancelMulZero` and `MulZeroMemClass.isCancelMulZero`: a subset closed under the product and containing $0$ inherits cancellation. The proofs use `Function.Injective.isCancelMulZero` with the inclusion map.

#### Regularity for an action

Let a type $R$ act on a type $M$. The module `Mathlib.Algebra.Regular.SMul` defines `IsSMulRegular M c`: the map $m \mapsto c \cdot m$ on $M$ is injective. For a commutative ring acting on a module, a scalar $c$ is $M$-regular when multiplication by $c$ on $M$ has trivial kernel. This is the notion behind regular sequences in commutative algebra. The definition takes $M$ as an explicit argument, because $c$ alone does not determine it.

The action version contains the old one. `isLeftRegular_iff` says that `IsLeftRegular a` is `IsSMulRegular R a` for the action of $R$ on itself, and `isRightRegular_iff` says that `IsRightRegular a` is regularity of $a^{\mathrm{op}}$. The closure properties come in the same form: `IsSMulRegular.smul` for an action of a product in a scalar tower, `IsSMulRegular.mul_iff` and `IsSMulRegular.pow_iff` for products and powers, `IsSMulRegular.of_mul_eq_one` and `Units.isSMulRegular` for elements with an inverse. Each element of a group acts regularly, because a group action is left cancellative, and `IsSMulRegular.all` gives regularity for each action of class `IsLeftCancelSMul`. The lemmas `Pi.isSMulRegular_iff`, `Prod.isSMulRegular_iff` and `ULift.isSMulRegular_iff` treat the constructions. The additive form is `IsVAddRegular`.

The module `Mathlib.Algebra.GroupWithZero.Action.Regular` treats the zero. By `IsSMulRegular.zero_iff_subsingleton`, the scalar $0$ is $M$-regular if and only if $M$ has at most one element. If $M$ is an additive group, then `isSMulRegular_iff_right_eq_zero_of_smul` says that $c$ is $M$-regular if and only if $c \cdot m = 0$ implies $m = 0$. The proof uses $c \cdot m_1 - c \cdot m_2 = c \cdot (m_1 - m_2)$. This is the kernel criterion for injectivity, and it needs subtraction.

#### The submonoid of non-zero-divisors

The module `Mathlib.Algebra.GroupWithZero.NonZeroDivisors` defines three submonoids of a monoid with zero $M_0$.

| Lean name | Elements |
|---|---|
| `nonZeroDivisorsLeft M₀` | the $x$ such that $xy = 0$ implies $y = 0$ |
| `nonZeroDivisorsRight M₀` | the $x$ such that $yx = 0$ implies $y = 0$ |
| `nonZeroDivisors M₀` | the intersection of the two |

Each set is closed under products: if $xy \cdot z = 0$, then $y z = 0$ by the property of $x$, and then $z = 0$ by the property of $y$. The notation `M₀⁰` for `nonZeroDivisors M₀` is in the scope `nonZeroDivisors`, so a file needs `open scoped nonZeroDivisors` to use it. The lemma `mem_nonZeroDivisors_iff` unfolds the membership, and in a commutative monoid with zero `mem_nonZeroDivisors_iff_left` uses one side only, because `nonZeroDivisorsLeft_eq_right` says the two sides agree there. The lemmas `mul_right_mem_nonZeroDivisors_eq_zero_iff` and `mul_left_mem_nonZeroDivisors_eq_zero_iff` are the rewriting forms: $x r = 0$ if and only if $x = 0$, for $r$ in the submonoid.

The submonoid lies between the units and the nonzero elements. Each unit is a non-zero-divisor (`IsUnit.mem_nonZeroDivisors`), and in a nontrivial monoid with zero, $0$ is not one (`zero_notMem_nonZeroDivisors`). Without zero divisors the submonoid is the set of nonzero elements, by `mem_nonZeroDivisors_iff_ne_zero`, and `noZeroDivisors_iff_forall_mem_nonZeroDivisors` states this as a characterization of `NoZeroDivisors`. In a group with zero each nonzero element is a unit, so the submonoid is the group of units. This is the isomorphism `nonZeroDivisorsEquivUnits`, and `isUnit_of_mem_nonZeroDivisors` is the element form.

**Proposition.** In a monoid with zero, each regular element is a non-zero-divisor. This is `IsRegular.mem_nonZeroDivisors`.

*Proof.* Let $r$ be regular and $r y = 0$. Then $r y = r \cdot 0$, and left regularity gives $y = 0$. The other side is the same with right regularity. $\square$

The converse fails in a general monoid with zero. Let $M = \{1, e\}$ with $e^2 = e$, and add a zero. Then $e x = 0$ only for $x = 0$, so $e$ is a non-zero-divisor, but $e \cdot e = e \cdot 1$ with $e \neq 1$. In a ring the converse holds, by subtraction, and the library states it as `isRegular_iff_mem_nonZeroDivisors`.

Homomorphisms interact with the submonoid. `map_mem_nonZeroDivisors` sends a non-zero-divisor to a non-zero-divisor along an injective map into a monoid with zero without zero divisors, and `MulEquivClass.map_nonZeroDivisors` says that an isomorphism maps the submonoid onto the submonoid. The equivalences `unitsNonZeroDivisorsEquiv` and `associatesNonZeroDivisorsEquiv` identify the units and the associate classes of the submonoid with those of $M_0$. For an action of a monoid with zero on $M$, the submonoid `nonZeroSMulDivisors M₀ M`, with notation `M₀⁰[M]`, holds the $x$ such that $x \cdot m = 0$ implies $m = 0$, and `isSMulRegular_iff_mem_nonZeroSMulDivisors` matches it with `IsSMulRegular` when $M$ is an additive group.

The module `Mathlib.Algebra.GroupWithZero.Submonoid.Instances` puts a monoid with zero on the range `MonoidHom.mrange f` of a homomorphism with zero. The lemma `MonoidWithZeroHom.val_mrange_zero` says that its zero is the zero of the target.

#### Common errors

1. `nonZeroDivisors M₀` is two-sided. In a noncommutative monoid with zero, a proof that uses only $r x = 0 \Rightarrow x = 0$ needs `nonZeroDivisorsLeft`, or the commutative lemma `mem_nonZeroDivisors_iff_left`.
2. The notation `M₀⁰` needs `open scoped nonZeroDivisors`. Without it, the notation does not parse.
3. A non-zero-divisor need not be regular outside rings. To cancel $r$ in $r a = r b$, prove `IsLeftRegular r`, or work in a ring and use `isRegular_iff_mem_nonZeroDivisors`.

### Exercises

1. (A) Prove that the element $2$ of $\mathbb{Z}/6$ is not a non-zero-divisor, and that $5$ is regular.
2. (A) By `IsLeftRegular.of_mul`, if $ab$ is left regular then $b$ is left regular. Give a monoid with elements $a, b$ such that $ab$ is left regular but $a$ is not.
3. (B) Show that in the monoid of maps $\mathbb{N} \to \mathbb{N}$ under composition, the shift $n \mapsto n + 1$ is left regular but not right regular.
4. (B) Prove that in a finite monoid each left regular element is a unit.
5. (B) Let $M_0$ be a commutative monoid with zero. Prove that the non-zero-divisors of $M_0 \times M_0$ are the pairs of non-zero-divisors.
6. (C) Prove `isSMulRegular_iff_right_eq_zero_of_smul` from the definitions, and show by an example that the hypothesis that $M$ is an additive group is needed.

### Reference

<?reference?>
