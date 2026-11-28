---
title: Pi groups and finitely supported functions
kind: api
modules:
  - Mathlib.Algebra.Group.Pi.Basic
  - Mathlib.Algebra.Group.Pi.Hom
  - Mathlib.Algebra.Group.Pi.Lemmas
  - Mathlib.Algebra.Group.Pi.Units
  - Mathlib.Algebra.Group.Finsupp
explains:
  E2: [Pi.mulSingle_mul, Pi.mulSingle_commute, Pi.update_eq_div_mul_mulSingle, Pi.isUnit_iff, MulEquiv.piUnits, MonoidHom.pi, Finsupp.induction]
  E1: auto
families: []
requires: [V01.C03, V03.C07, V05.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Pi groups and finitely supported functions

### Overview

Let $I$ be a type and let $G_i$ be a group for each $i \in I$. The type of dependent functions $(i : I) \to G_i$ is a group under the pointwise operations: $(f g)(i) = f(i) g(i)$, $1(i) = 1$ and $f^{-1}(i) = f(i)^{-1}$. This group is the *direct product* $\prod_i G_i$ of the family. The previous section treats the product $G \times H$ of two groups. The Pi construction is the same idea for a family of any size, and the library uses it for the groups $G^n = \mathrm{Fin}\ n \to G$, for the group of functions from a set to $\mathbb{R}$, and for many other examples.

The five modules of this section give the Pi type each structure of the hierarchy, give the homomorphisms into and out of a product, compute the units of a product, and give the additive group of finitely supported functions $I \to_0 M$. The last type is the direct sum of copies of $M$: a function that is zero outside a finite set.

### The library around it

#### The instances

The module `Mathlib.Algebra.Group.Pi.Basic` gives one instance for each class of the hierarchy of Chapter 1. If each $G_i$ is a group, then `Pi.group` makes the product a group. In the same way `Pi.monoid`, `Pi.commMonoid`, `Pi.commGroup`, `Pi.divisionMonoid`, `Pi.cancelMonoid` and `Pi.leftCancelMonoid` give the other structures, and the additive copies, such as `Pi.addCommGroup`, come from the same declarations by to_additive. The instances are pointwise, so each operation evaluates by definition: `(f * g) i` and `f i * g i` are equal by rfl. The simp lemmas `Pi.mul_apply`, `Pi.one_apply` and `Pi.inv_apply` state these equalities.

The same module proves that the operations commute with the constructions on functions. The lemmas `Function.extend_mul`, `Function.extend_inv` and `Function.extend_one` treat the extension of a function along a map, and `Sum.elim_mul_mul` and `Sum.elim_one_one` treat a function on a sum type. The lemma `Function.comp_eq_one_iff` says that $g \circ f = 1$ if and only if $f = 1$, when $g$ is injective and $g(1) = 1$.

#### The function with one value

Let $I$ have decidable equality. The function `Pi.mulSingle i x` has the value $x$ at $i$ and the value $1$ at each other index. Its additive copy `Pi.single i x` has the value $x$ at $i$ and $0$ elsewhere. The definitions are in `Mathlib.Algebra.Notation.Pi.Basic`, with the evaluation lemmas `Pi.mulSingle_eq_same` and `Pi.mulSingle_eq_of_ne`. The module `Mathlib.Algebra.Group.Pi.Lemmas` gives their algebra.

**Theorem (The single function is a homomorphism).** Let each $G_i$ be a monoid. Then $\operatorname{mulSingle}_i(x y) = \operatorname{mulSingle}_i(x) \operatorname{mulSingle}_i(y)$.

*Proof.* Evaluate both sides at an index $j$. If $j = i$, both sides are $x y$. If $j \neq i$, the left side is $1$ and the right side is $1 \cdot 1 = 1$. Two functions with equal values are equal. $\square$

This is `Pi.mulSingle_mul`. With `Pi.mulSingle_pow`, `Pi.mulSingle_inv`, `Pi.mulSingle_div` and `Pi.mulSingle_zpow` it makes `Pi.mulSingle i` a homomorphism of groups. The bundled forms are `MonoidHom.mulSingle` and `OneHom.mulSingle`, and the additive form is `AddMonoidHom.single`.

**Theorem (Singles at different indices commute).** Let $i \neq j$. For each $x \in G_i$ and $y \in G_j$, the functions $\operatorname{mulSingle}_i(x)$ and $\operatorname{mulSingle}_j(y)$ commute.

*Proof.* At each index $k$, at least one of the two values is $1$, since $k$ cannot be equal to both $i$ and $j$. So the two products have the same value at $k$. $\square$

This is `Pi.mulSingle_commute`, stated with `Pairwise`. The groups $G_i$ need not be commutative. The lemma `Pi.commute_iff` gives the general rule: two functions commute if and only if their values commute at each index. The lemmas `Pi.semiconjBy_iff` and `Pi.isSelfInv_iff` are the same rule for `SemiconjBy` and `IsSelfInv`.

**Theorem (Update by singles).** In a product of groups, $\operatorname{update}(g, i, x) = g \cdot \operatorname{mulSingle}_i(g(i))^{-1} \cdot \operatorname{mulSingle}_i(x)$.

*Proof.* At the index $i$ the right side is $g(i) g(i)^{-1} x = x$. At an index $j \neq i$ it is $g(j) \cdot 1 \cdot 1 = g(j)$. These are the values of the updated function. $\square$

This is `Pi.update_eq_div_mul_mulSingle`, written with a division. The lemmas `Function.update_mul`, `Function.update_inv` and `Function.update_one` give the pointwise algebra of `Function.update`, and `Set.piecewise_mul` does the same for a function that is defined by cases on a set. The lemma `Pi.mulSingle_mul_mulSingle_eq_mulSingle_mul_mulSingle` decides when two products of two singles are equal in a commutative monoid. For $u, v \neq 1$ the equation $\operatorname{mulSingle}_k(u) \operatorname{mulSingle}_l(v) = \operatorname{mulSingle}_m(u) \operatorname{mulSingle}_n(v)$ holds exactly when $k = m$ and $l = n$, or $u = v$ and $k = n$ and $l = m$, or $u v = 1$ and $k = l$ and $m = n$.

#### Homomorphisms into and out of a product

The module `Mathlib.Algebra.Group.Pi.Hom` gives the universal property of the product. A family of homomorphisms $g_i : H \to G_i$ gives one homomorphism $H \to \prod_i G_i$, defined by $x \mapsto (g_i(x))_i$.

**Theorem (Universal property).** The map $x \mapsto (g_i(x))_i$ is a monoid homomorphism, and it is the only homomorphism whose composite with each evaluation $\operatorname{ev}_i$ is $g_i$.

*Proof.* At each index $i$ the value of the product $x y$ is $g_i(x y) = g_i(x) g_i(y)$, so the map respects products. It respects $1$ in the same way. A homomorphism $\varphi$ with $\operatorname{ev}_i \circ \varphi = g_i$ has the value $g_i(x)$ at $i$, for each $x$. So $\varphi(x) = (g_i(x))_i$. $\square$

The construction is `MonoidHom.pi`, with the evaluation lemma `MonoidHom.pi_apply`. The evaluations are the homomorphisms `Pi.evalMonoidHom f i`. The lemma `MonoidHom.pi_injective` says that the product map is injective when each $g_i$ is injective and $I$ is nonempty. Other maps in the module:

| Lean name | Map |
| --- | --- |
| `Pi.constMonoidHom` | the diagonal $x \mapsto (x)_i$, from $G$ to $I \to G$ |
| `MonoidHom.compLeft` | $h \mapsto f \circ h$, from $I \to G$ to $I \to H$, for $f : G \to H$ |
| `MonoidHom.piMap` | $(x_i) \mapsto (f_i(x_i))$, for a family $f_i : G_i \to H_i$ |
| `Pi.evalMulHom` | the evaluation, as a semigroup homomorphism |
| `MulHom.pi` | the universal property for semigroup homomorphisms |

The module `Mathlib.Algebra.Group.Pi.Lemmas` adds `MonoidHom.coeFn`, the map that sends a homomorphism to its function, when the codomain is commutative. It also adds `Function.ExtendByOne.hom`, the extension by $1$ along a map $s : \iota \to \eta$, as a homomorphism of function monoids.

#### The units of a product

The module `Mathlib.Algebra.Group.Pi.Units` computes the units.

**Theorem (Units of a product).** Let each $M_i$ be a monoid. A function $x$ is a unit of $\prod_i M_i$ if and only if each value $x(i)$ is a unit of $M_i$.

*Proof.* Let $x y = 1$ and $y x = 1$. Evaluate at $i$: $x(i) y(i) = 1$ and $y(i) x(i) = 1$, so $x(i)$ is a unit. Conversely, choose an inverse $y(i)$ of $x(i)$ for each $i$. Then $y$ is an inverse of $x$, because the equations hold at each index. $\square$

This is `Pi.isUnit_iff`, with the one-way form `IsUnit.apply`. The bundled form is the isomorphism `MulEquiv.piUnits`, from the units of the product to the product of the unit groups. The instance `Pi.instSubsingletonUnits` says that the product has only the unit $1$ when each factor has only the unit $1$.

#### Finitely supported functions

The type `I →₀ M` of the library is the type of functions $I \to M$ with finite support, where $M$ has a zero. Its definition and the function `Finsupp.single` are in Volume 3, in the chapter on finitely supported functions. The module `Mathlib.Algebra.Group.Finsupp` gives the additive structures. They are pointwise, as for the Pi type, and the sum of two finitely supported functions has finite support, since its support is in the union of the two supports. The instances are `Finsupp.instAddMonoid`, `Finsupp.instAddCommMonoid`, `Finsupp.instAddGroup` and `Finsupp.instAddCommGroup`. Cancellation and torsion freeness pass from $M$ to `I →₀ M`, by `Finsupp.instIsCancelAdd` and `Finsupp.instIsAddTorsionFree`. The lemma `Finsupp.coe_nsmul` says that the coercion to functions respects the multiples $n \cdot f$.

The main results of the module are the induction principles.

**Theorem (Induction on finitely supported functions).** Let $P$ be a property of finitely supported functions. Assume that $P(0)$ holds. Assume that $P(f)$ implies $P(\operatorname{single}(a, b) + f)$, for each $a$ outside the support of $f$ and each $b \neq 0$. Then $P(f)$ holds for each $f$.

*Proof sketch.* Use induction on the finite support $s$ of $f$. If $s$ is empty, then $f = 0$. Otherwise choose $a \in s$ and let $g$ be $f$ with the value $0$ at $a$. Then $f = \operatorname{single}(a, f(a)) + g$, the support of $g$ is $s \setminus \{a\}$, and $f(a) \neq 0$. The hypothesis on $g$ gives $P(f)$. $\square$

This is `Finsupp.induction`. The variant `Finsupp.induction₂` adds the single on the right. The variant `Finsupp.induction_linear` needs only $P(0)$, closure under sums and $P(\operatorname{single}(a, b))$, and it is the common tool to prove that two additive maps out of `I →₀ M` are equal. When $I$ is linearly ordered, `Finsupp.induction_on_max` and `Finsupp.induction_on_min` add the single at an index that is larger or smaller than each index of the support.

#### Common errors

1. A product over a family is a function type, so simp uses `Pi.mul_apply` only after the function is applied to an index. To prove an equality of two functions, apply funext first, or use the lemmas for `Pi.mulSingle` as rewrite rules.
2. `Pi.mulSingle` and `Pi.single` need decidable equality on the index type. Two different instances of decidable equality can give two terms that look the same but are not equal by rfl. A goal with `Classical.decEq` in it often has this problem.
3. The type `I →₀ M` is not the Pi type `I → M`. A lemma for `Pi.single` does not apply to `Finsupp.single`, and the coercion to functions must be inserted by hand. The induction principles of this section are for `I →₀ M` only.

### Exercises

1. (A) Prove `Pi.mulSingle_mul` by evaluation at an index, with `Pi.mulSingle_apply` and a case split on $j = i$.
2. (A) Let each $G_i$ be a group in which $x^2 = 1$ for all $x$. Show that $f^2 = 1$ for each $f \in \prod_i G_i$, and state the result with `Pi.isSelfInv_iff`.
3. (B) Use `Pi.isUnit_iff` to describe the units of the monoid $\mathbb{N} \to \mathbb{Z}$ under pointwise multiplication. Show that this unit group is not finite.
4. (B) Prove `Pi.update_eq_div_mul_mulSingle`. Then deduce that the product $\prod_i G_i$ over a finite $I$ is generated by the images of the maps `MonoidHom.mulSingle`.
5. (B) Let $\varphi, \psi : (I \to_0 M) \to N$ be additive homomorphisms with $\varphi(\operatorname{single}(a, b)) = \psi(\operatorname{single}(a, b))$ for all $a$ and $b$. Prove $\varphi = \psi$ with `Finsupp.induction_linear`.
6. (C) Prove the case analysis of `Pi.mulSingle_mul_mulSingle_eq_mulSingle_mul_mulSingle` for $u, v \neq 1$. Hint: compare the supports of the two sides, and treat the cases $k = l$ and $k \neq l$ apart.

### Reference

<?reference?>
