---
title: Homomorphisms and isomorphisms
kind: theory
modules:
  - Mathlib.Algebra.Group.Hom.Defs
  - Mathlib.Algebra.Group.Equiv.Defs
explains:
  E3: [MonoidHom]
  E2: [map_mul, map_one, map_inv, map_pow, map_zpow, MonoidHom.mk', MonoidHom.comp, MonoidHom.ext, MulEquiv, MulEquiv.ofBijective]
  E1: auto
families: []
requires: [V05.C01]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V05/C02/Examples.lean
  - MathlibHandbook/V05/C02/Exercises.lean
  - MathlibHandbook/V05/C02/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Homomorphisms and isomorphisms

### Overview

A homomorphism is a map between groups that respects the product. Homomorphisms compare groups. The exponential map turns addition of real numbers into multiplication of positive reals, the determinant turns the product of matrices into the product of numbers, and the reduction modulo $n$ turns integers into classes. In each case a property of the source passes to the target.

An isomorphism is a bijective homomorphism. Two isomorphic groups have the same structure, and they differ only in the names of their elements. The main results of the section are that a homomorphism of groups respects the unit, the inverses and the powers as soon as it respects the product, and that the inverse map of a bijective homomorphism is again a homomorphism.

In Mathlib a homomorphism is not a function with a property. It is a term of the type `G →* H`, a structure that holds the function and the proofs. The section explains this design, the lemmas `map_mul`, `map_one` and `map_inv` that hold for each kind of homomorphism, the composite, and the isomorphisms `G ≃* H`.

### Definitions

**Definition (Monoid homomorphism).** Let $M$ and $N$ be monoids. A homomorphism $f : M \to N$ is a map with $f(1) = 1$ and $f(a b) = f(a) f(b)$ for all $a, b \in M$.

For groups, the condition $f(1) = 1$ follows from the other condition, as the first theorem shows. For monoids it does not, and the examples give a map that respects products but not the unit. This is the reason why the definition for monoids has two conditions.

::: mathlib
`MonoidHom` · `Mathlib.Algebra.Group.Hom.Defs`

The structure `MonoidHom M N`, with the notation `M →* N`, has three fields: the function, the field `map_one'` and the field `map_mul'`. A term `f : M →* N` coerces to a function, so `f a` makes sense. The coercion comes from the class `FunLike` of Volume 1. Use the lemmas `map_one` and `map_mul` in a proof, not the fields with a prime. The additive copy is `AddMonoidHom`, with the notation `A →+ B`.

<?decl MonoidHom?>
:::

::: mathlib
`MonoidHom.ext` · `Mathlib.Algebra.Group.Hom.Defs`

Two homomorphisms are equal if they agree at each point. The proofs in the structure do not matter, by proof irrelevance. The tactic `ext x` applies this lemma and leaves the goal `f x = g x`.

<?decl MonoidHom.ext?>
:::

**Definition (Composite).** If $f : M \to N$ and $g : N \to P$ are homomorphisms, then the composite $g \circ f : M \to P$ is a homomorphism, by the theorem below. The identity map $\mathrm{id}_M$ is a homomorphism.

**Definition (Isomorphism).** An isomorphism $f : G \to H$ is a homomorphism that is a bijection. If there is one, then $G$ and $H$ are isomorphic, written $G \cong H$. An isomorphism $G \to G$ is an automorphism of $G$.

::: mathlib
`MulEquiv` · `Mathlib.Algebra.Group.Equiv.Defs`

The structure `MulEquiv G H`, with the notation `G ≃* H`, extends the equivalence `G ≃ H` of Volume 1 with the field `map_mul'`. So an isomorphism holds its inverse map as data, with the two proofs that the maps are inverse. The inverse isomorphism is `e.symm`, and `e.toMonoidHom` forgets the inverse. The class `MulEquiv` asks only for `Mul` on the two types, not for a unit, because a bijection that respects products respects the unit, as an exercise shows.

<?decl MulEquiv?>
:::

### Theorems and proofs

**Theorem (Unit).** Let $G$ and $H$ be groups, and let $f : G \to H$ satisfy $f(a b) = f(a) f(b)$ for all $a, b$. Then $f(1) = 1$.

*Proof.* The unit satisfies $1 \cdot 1 = 1$. So $f(1) = f(1 \cdot 1) = f(1) f(1)$. Write this as $f(1) \cdot 1 = f(1) \cdot f(1)$ and cancel $f(1)$ on the left in the group $H$. Then $1 = f(1)$. $\square$

The proof uses cancellation in $H$. In a monoid without cancellation the argument fails, and the counterexample below shows that the claim fails too.

::: mathlib
`MonoidHom.mk'` · `Mathlib.Algebra.Group.Hom.Defs`

The constructor of a homomorphism into a group from a map that respects products. It applies the theorem above to fill the field `map_one'`. The source need only be a `MulOneClass`, and the target must be a group.

<?decl MonoidHom.mk'?>
:::

::: mathlib
`map_one` · `Mathlib.Algebra.Group.Hom.Defs`

The lemma $f(1) = 1$ for each `f : F` with `[OneHomClass F M N]`. So it holds for monoid homomorphisms, isomorphisms and ring homomorphisms alike. It is a `simp` lemma.

<?decl map_one?>
:::

::: mathlib
`map_mul` · `Mathlib.Algebra.Group.Hom.Defs`

The lemma $f(a b) = f(a) f(b)$ for each `f : F` with `[MulHomClass F M N]`. It is a `simp` lemma. Read from right to left, with `rw [← map_mul]`, it collects a product of images into one image.

<?decl map_mul?>
:::

**Theorem (Inverse).** A homomorphism of groups $f : G \to H$ satisfies $f(a^{-1}) = f(a)^{-1}$ for each $a$.

*Proof.* Compute $f(a^{-1}) f(a) = f(a^{-1} a) = f(1) = 1$. So $f(a^{-1})$ is a left inverse of $f(a)$ in $H$. In a group the inverse of an element is its only left inverse, by the lemma on left and right inverses of Chapter 1. So $f(a^{-1}) = f(a)^{-1}$. $\square$

::: mathlib
`map_inv` · `Mathlib.Algebra.Group.Hom.Defs`

The lemma needs a `MonoidHomClass` and that the source is a group and the target a `DivisionMonoid`. Its partner `map_div` gives $f(a / b) = f(a) / f(b)$.

<?decl map_inv?>
:::

**Theorem (Powers).** A monoid homomorphism satisfies $f(a^n) = f(a)^n$ for $n \in \mathbb{N}$. A homomorphism of groups satisfies it also for $n \in \mathbb{Z}$.

*Proof.* By induction on $n \in \mathbb{N}$. For $n = 0$, $f(a^0) = f(1) = 1 = f(a)^0$. If $f(a^n) = f(a)^n$, then $f(a^{n+1}) = f(a^n a) = f(a^n) f(a) = f(a)^n f(a) = f(a)^{n+1}$. For a negative exponent $-n$, $f(a^{-n}) = f((a^n)^{-1}) = f(a^n)^{-1} = (f(a)^n)^{-1} = f(a)^{-n}$, by the theorem on inverses. $\square$

::: mathlib
`map_pow` · `Mathlib.Algebra.Group.Hom.Defs`

The natural power. It is a `simp` lemma.

<?decl map_pow?>
:::

::: mathlib
`map_zpow` · `Mathlib.Algebra.Group.Hom.Defs`

The integer power, for a source that is a group and a target that is a `DivisionMonoid`.

<?decl map_zpow?>
:::

**Theorem (Composite).** The composite of two homomorphisms is a homomorphism.

*Proof.* Let $f : M \to N$ and $g : N \to P$ be homomorphisms. Then $g(f(a b)) = g(f(a) f(b)) = g(f(a)) g(f(b))$, by the property of $f$ and then of $g$. Also $g(f(1)) = g(1) = 1$. $\square$

::: mathlib
`MonoidHom.comp` · `Mathlib.Algebra.Group.Hom.Defs`

The argument order follows the composite of functions: `g.comp f` is $g \circ f$, and it applies `f` first. The lemma `MonoidHom.comp_apply` unfolds it at a point, and `MonoidHom.coe_comp` says that its function is `g ∘ f`.

<?decl MonoidHom.comp?>
:::

**Theorem (The inverse of an isomorphism).** Let $f : G \to H$ be a bijective homomorphism, and let $f^{-1} : H \to G$ be its inverse map. Then $f^{-1}$ is a homomorphism. So $\cong$ is a symmetric relation.

*Proof.* Let $x, y \in H$. Put $a = f^{-1}(x)$ and $b = f^{-1}(y)$, so $f(a) = x$ and $f(b) = y$. Then $f(a b) = f(a) f(b) = x y$. Apply $f^{-1}$ to both sides: $a b = f^{-1}(x y)$. That is, $f^{-1}(x) f^{-1}(y) = f^{-1}(x y)$. $\square$

The composite of two isomorphisms is an isomorphism, because the composite of two bijections is a bijection. The identity is an isomorphism. So $\cong$ is an equivalence relation on groups.

::: mathlib
`MulEquiv.ofBijective` · `Mathlib.Algebra.Group.Equiv.Defs`

The isomorphism from a bijective homomorphism. The inverse map is chosen with the axiom of choice, so the definition is `noncomputable`. If the inverse is known, it is better to build the `MulEquiv` with its fields, or with `MonoidHom.toMulEquiv` from two homomorphisms whose composites are the identities.

<?decl MulEquiv.ofBijective?>
:::

### Examples

**Example (The exponential).** The map $\exp : (\mathbb{R}, +) \to (\mathbb{R}_{>0}, \cdot)$ satisfies $\exp(x + y) = \exp(x) \exp(y)$. So it is a homomorphism from an additive group to a multiplicative group. It is a bijection with inverse $\log$, so it is an isomorphism. By the theorem on the inverse of an isomorphism, $\log(x y) = \log x + \log y$. The law of logarithms is a consequence of the law of exponents. In Mathlib a homomorphism from an additive to a multiplicative group has the type `Multiplicative ℝ →* ℝ` or `ℝ →+ Additive ℝ`, with the type tags `Multiplicative` and `Additive`.

**Example (Reduction modulo $n$).** The map $\mathbb{Z} \to \mathbb{Z}/n$, $a \mapsto \bar a$, is a homomorphism of additive groups, because $\overline{a + b} = \bar a + \bar b$ by the definition of the addition of classes. It is onto, and it is not injective for $n \ge 1$, since $\bar n = \bar 0$.

**Example (The determinant).** The determinant $\det : \mathrm{GL}_2(\mathbb{R}) \to \mathbb{R}^\times$ is a homomorphism, by the product rule $\det(A B) = \det A \det B$. It is onto: the matrix with diagonal $(t, 1)$ has determinant $t$. It is not injective: each rotation matrix has determinant $1$.

**Example (Powers in a commutative group).** Let $A$ be a commutative group and $n \in \mathbb{Z}$. The map $a \mapsto a^n$ is a homomorphism $A \to A$, because $(a b)^n = a^n b^n$ when $a$ and $b$ commute. In a group that is not commutative, the square map can fail to be a homomorphism. In $D_3$, $(r s)^2 = 1$ but $r^2 s^2 = r^2 \neq 1$, as Chapter 1 computed.

**Counterexample (The unit needs its own axiom in a monoid).** Let $M = (\mathbb{N}, \cdot)$ and let $f : M \to M$ be the constant map $f(a) = 0$. Then $f(a b) = 0 = 0 \cdot 0 = f(a) f(b)$, so $f$ respects products. But $f(1) = 0 \neq 1$. So $f$ is not a monoid homomorphism. The proof of the theorem on the unit cancels $f(1)$, and $0$ cannot be cancelled in $(\mathbb{N}, \cdot)$. This is the reason why `MonoidHom` has the field `map_one'`.

**Counterexample (A bijection that is not an isomorphism).** The map $\mathbb{Z}/4 \to \mathbb{Z}/4$, $x \mapsto x + 1$, is a bijection. It is not a homomorphism, because it sends $0$ to $1$, and a homomorphism of additive groups sends $0$ to $0$.

**Example (Products and the unit in Lean).**

<?lean MathlibHandbook/V05/C02/Examples.lean#map_mul?>

**Example (Inverses in Lean).**

<?lean MathlibHandbook/V05/C02/Examples.lean#map_inv?>

**Example (A homomorphism from a map).** On a commutative group, the square map is a homomorphism. The constructor `MonoidHom.mk'` needs only the product, because the source is a group.

<?lean MathlibHandbook/V05/C02/Examples.lean#hom_mk?>

**Example (The composite in Lean).**

<?lean MathlibHandbook/V05/C02/Examples.lean#comp?>

**Example (An isomorphism and its inverse).**

<?lean MathlibHandbook/V05/C02/Examples.lean#mul_equiv?>

### The library around it

The general lemmas `map_mul`, `map_one`, `map_inv`, `map_div`, `map_pow` and `map_zpow` are stated for a class of maps, not for `MonoidHom`. This is the design of the class `FunLike` of Volume 1, with the classes `MulHomClass`, `OneHomClass` and `MonoidHomClass` on top. One lemma then works for `G →* H`, for `G ≃* H` and for a ring homomorphism. The lemmas that are special to `MonoidHom` have the prefix `MonoidHom.`: `MonoidHom.id_apply`, `MonoidHom.comp_apply`, `MonoidHom.comp_id`, `MonoidHom.id_comp` and `MonoidHom.comp_assoc`.

The structure `MulEquiv` has the lemmas `MulEquiv.apply_symm_apply` and `MulEquiv.symm_apply_apply`, which cancel an isomorphism with its inverse, and `MulEquiv.trans` for the composite. The homomorphisms of a monoid to a commutative monoid are themselves a commutative monoid under the pointwise product, and Mathlib gives that instance too. The products of groups have the homomorphisms `MonoidHom.fst`, `MonoidHom.snd`, `MonoidHom.inl` and `MonoidHom.prod`, in `Mathlib.Algebra.Group.Prod`. For the additive side, change `Monoid` to `AddMonoid` and `mul` to `add`.

### Exercises

1. (A) Write the type of the additive homomorphisms from `ℤ` to `ℚ`, and of the isomorphisms of a group `G` with itself.
2. (A) Explain why `g.comp f` applies `f` first.
3. (A) Show that the map $\mathbb{Z} \to \mathbb{Z}$, $a \mapsto 3 a$, is an injective homomorphism of additive groups that is not onto.
4. (B) Show that the map $x \mapsto x^{-1}$ on a group $G$ is a homomorphism if and only if $G$ is commutative. Hint: compare $(a b)^{-1}$ with $a^{-1} b^{-1}$.
5. (B) Show that the composite of two isomorphisms is an isomorphism, and that its inverse is the composite of the inverses in the opposite order.
6. (B) Let $f : M \to N$ be a bijection between monoids with $f(a b) = f(a) f(b)$. Show that $f(1) = 1$. Hint: $f(1) f(b) = f(b)$ for each $b$, and $f$ is onto.
7. (B) Show that there is no isomorphism $(\mathbb{Q}, +) \to (\mathbb{Q}_{>0}, \cdot)$. Hint: an isomorphism $f$ gives $f(x) = f(x/2)^2$, so each positive rational would be a square of a rational.
8. (L) Prove that $f(a^n) = f(a)^n$. The solution is `map_pow_example`.
9. (L) Prove that $f(a / b) = f(a) / f(b)$ for groups. The solution is `map_div_example`.
10. (L) Prove that the identity homomorphism sends $x$ to $x$. The solution is `id_apply_example`.

### Notes and history

The word homomorphism comes from the work of Klein and of Frobenius in the 1880s. Jordan used isomorphism in his *Traité des substitutions* of 1870, with "isomorphisme holoédrique" for a bijective homomorphism and "isomorphisme mériédrique" for one that is onto but not injective. The modern terms became standard with the textbooks of the 1920s and 1930s.

In Lean 3, Mathlib first used the predicate `is_monoid_hom` on plain functions. The bundled homomorphism, a structure with the map and the proofs, replaced it. The change made the composite and the inverse into terms with a type, so `simp` can use them. The classes such as `MonoidHomClass` came later, so that one lemma covers each kind of map. The port to Lean 4 kept this design.

### Reference

<?reference?>
