---
title: Ordered modules
kind: api
modules:
  - Mathlib.Algebra.Order.Module.Defs
  - Mathlib.Algebra.Order.Module.Basic
  - Mathlib.Algebra.Order.Module.Equiv
  - Mathlib.Algebra.Order.Module.Field
  - Mathlib.Algebra.Order.Module.Pointwise
  - Mathlib.Algebra.Order.Module.Rat
  - Mathlib.Algebra.Order.Module.Synonym
  - Mathlib.Algebra.Order.Module.PositiveLinearMap
explains:
  E2: [PosSMulMono, SMulPosMono, IsOrderedModule, PosSMulMono.of_pos, PosSMulMono.toSMulPosMono, smul_le_smul_iff_of_neg_left, abs_smul, OrderIso.smulRightDual, PositiveLinearMap, PositiveLinearMap.mk₀]
  E1: auto
families: []
requires: [V04, V05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Ordered modules

### Overview

An ordered vector space is a real vector space with an order that respects the sum and the multiplication by nonnegative scalars: if $x \le y$ and $a \ge 0$, then $a x \le a y$. Examples are $\mathbb{R}^n$ with the coordinatewise order, spaces of functions with the pointwise order, and the self-adjoint matrices with the order of positive semidefinite matrices. Mathlib states these conditions with small classes about the monotonicity of $b \mapsto a \cdot b$ and of $a \mapsto a \cdot b$, and it uses them for each action of an ordered type on an ordered type. This section describes the classes, the bundled class `IsOrderedModule`, the inequalities that follow from them, the order duals and lexicographic orders, and the positive linear maps.

### The library around it

#### The granular classes

Let $\alpha$ act on $\beta$, where both are preorders with a zero. Eight classes describe the interaction of the action with the order. Four are about the left map $b \mapsto a \cdot b$:

| Class | Condition |
|---|---|
| `PosSMulMono` | $a \ge 0$ and $b_1 \le b_2$ imply $a b_1 \le a b_2$ |
| `PosSMulStrictMono` | $a > 0$ and $b_1 < b_2$ imply $a b_1 < a b_2$ |
| `PosSMulReflectLT` | $a \ge 0$ and $a b_1 < a b_2$ imply $b_1 < b_2$ |
| `PosSMulReflectLE` | $a > 0$ and $a b_1 \le a b_2$ imply $b_1 \le b_2$ |

The four classes `SMulPosMono`, `SMulPosStrictMono`, `SMulPosReflectLT` and `SMulPosReflectLE` are the same conditions for the right map $a \mapsto a \cdot b$ with $b \ge 0$ or $b > 0$. The classes do not use the laws of an action, so they apply to each map $\alpha \to \beta \to \beta$ written as `•`. They are the analogues for an action of the classes `PosMulMono` and its relatives for the multiplication of a ring, and a ring acting on itself has them by instances such as `MulPosMono.toSMulPosMono`.

The conditions on nonnegative inputs are trivial when an input is $0$, so it is enough to check them on positive inputs. The constructors are `PosSMulMono.of_pos`, `SMulPosMono.of_pos`, `PosSMulReflectLT.of_pos` and `SMulPosReflectLT.of_pos`.

#### Implications and the bundled class

With more structure the classes are related. The strict classes imply the weak ones on partial orders (`PosSMulStrictMono.toPosSMulMono`), and over a linear order the strict monotone class implies the reflecting one (`PosSMulStrictMono.toPosSMulReflectLE`). In a module the two weak classes are the same.

**Theorem.** Let $\alpha$ be an ordered ring and $\beta$ an ordered additive group that is an $\alpha$-module. If $\beta$ satisfies `PosSMulMono`, then it satisfies `SMulPosMono`.

*Proof.* Let $b \ge 0$ and $a_1 \le a_2$. Then $a_2 - a_1 \ge 0$, so $(a_2 - a_1) b \ge (a_2 - a_1) 0 = 0$ by `PosSMulMono`. Thus $a_2 b - a_1 b \ge 0$, which is $a_1 b \le a_2 b$. $\square$

This is the instance `PosSMulMono.toSMulPosMono`. Both classes say that $a \ge 0$ and $b \ge 0$ imply $a b \ge 0$ (`smul_nonneg`). To avoid a loop of instances in both directions, Mathlib has the bundled class `IsOrderedModule α β`, which extends `PosSMulMono` and `SMulPosMono`, and `IsStrictOrderedModule` for the strict forms. Most statements should assume these. An ordered ring is a strict ordered module over itself (`IsStrictOrderedRing.toIsStrictOrderedModule`), and an algebra whose structure map is monotone is an ordered module (`IsOrderedModule.of_algebraMap_mono`). Over a linear ordered field, `PosSMulMono` gives the reflecting class (`PosSMulMono.toPosSMulReflectLE`), so a positive scalar can be cancelled in inequalities.

The instances cover the standard constructions: functions (`Pi.instPosSMulStrictMono`), products (`Prod.instPosSMulReflectLE`), and the order dual. Each ordered additive monoid is an ordered module over $\mathbb{N}$, and each ordered additive group is an ordered module over $\mathbb{Z}$ (`instPosSMulStrictMonoIntOfIsOrderedAddMonoid`). The file `Mathlib.Algebra.Order.Module.Rat` gives the action of $\mathbb{Q}_{\ge 0}$ and $\mathbb{Q}$ on a linear ordered field (`LinearOrderedField.toPosSMulStrictMono_rat`).

#### The inequalities

The left lemmas have the names of the multiplication lemmas, with smul in place of mul: `smul_le_smul_of_nonneg_left`, `smul_lt_smul_of_pos_left`, `smul_le_smul_iff_of_pos_left`, `smul_pos`, and `le_of_smul_le_smul_of_pos_left`. The names of the right lemmas end in right, such as `smul_le_smul_iff_of_pos_right`. The lemma `smul_le_smul'` combines both sides.

Over a ring, a negative scalar reverses the order.

**Theorem.** Let $\beta$ be an ordered module over an ordered ring $\alpha$ with `PosSMulMono` and `PosSMulReflectLE`. If $a < 0$, then $a b_1 \le a b_2$ if and only if $b_2 \le b_1$.

*Proof.* Put $c = -a > 0$. Then $a b_1 \le a b_2$ is $-c b_1 \le -c b_2$, which is $c b_2 \le c b_1$. Since $c > 0$, the two classes give that this holds if and only if $b_2 \le b_1$. $\square$

This is `smul_le_smul_iff_of_neg_left`, with the strict form `smul_lt_smul_iff_of_neg_left`. Over a linear ordered field, the map $b \mapsto a b$ is an order isomorphism for $a > 0$, `OrderIso.smulRight`, and an order isomorphism onto the order dual for $a < 0$, `OrderIso.smulRightDual`. The file `Mathlib.Algebra.Order.Module.Field` has the forms with inverses, such as `inv_smul_le_iff_of_neg`, and an extension of the `positivity` tactic for the action.

Over a linear order, the absolute value is multiplicative: $|a b| = |a| \, |b|$. This is `abs_smul`, and `abs_nnqsmul` is the case of a nonnegative rational. In a vector space over a field of characteristic $0$, the lattice operations are given by the absolute value: $x \sqcup y = \frac{1}{2}(x + y + |y - x|)$ (`sup_eq_half_smul_add_add_abs_sub'`, and `inf_eq_half_smul_add_sub_abs_sub'` for the infimum).

For a set $s \subseteq \beta$, the action keeps the bounds. For $a > 0$ the upper bounds of $a s$ are $a$ times the upper bounds of $s$ (`upperBounds_smul_of_pos`), and for $a < 0$ the upper and lower bounds are exchanged (`upperBounds_smul_of_neg`). The forms for bounded sets are `BddAbove.smul_of_nonneg` and `bddAbove_smul_iff_of_neg`.

#### Order synonyms

The order dual $\beta^{\mathrm{od}}$ and the lexicographic type `Lex β` are new names for $\beta$ with another order. The file `Mathlib.Algebra.Order.Module.Synonym` moves the module structure to them, by `OrderDual.instModule'` and `Lex.instModule'`. The ordered module classes are moved to the order dual as well, with the inequalities reversed in $\beta$. The file `Mathlib.Algebra.Order.Module.Equiv` gives the linear equivalences `toLexLinearEquiv` and `ofLexLinearEquiv` between $\beta$ and `Lex β`, whose functions are `toLex` and `ofLex`.

#### Positive linear maps

A positive linear map $f : E_1 \to E_2$ between ordered modules is a linear map that is monotone. The type is `PositiveLinearMap R E₁ E₂`, written `E₁ →ₚ[R] E₂`, and it has the classes `LinearMapClass` and `OrderHomClass`. For ordered groups, a linear map is monotone if and only if it sends nonnegative elements to nonnegative elements.

**Theorem.** Let $f : E_1 \to E_2$ be an additive map between ordered additive groups. If $f(x) \ge 0$ for each $x \ge 0$, then $f$ is monotone.

*Proof.* Let $x \le y$. Then $y - x \ge 0$, so $f(y) - f(x) = f(y - x) \ge 0$. Thus $f(x) \le f(y)$. $\square$

The constructor from this condition is `PositiveLinearMap.mk₀`, and the class form is `OrderHomClass.of_addMonoidHom`. The basic lemma is `PositiveLinearMap.map_nonneg`. Positive maps compose (`PositiveLinearMap.comp`), the identity is `PositiveLinearMap.id`, and they form an additive monoid under the pointwise sum. A positive map forgets to a linear map with `PositiveLinearMap.toLinearMap` and to an order map with `PositiveLinearMap.toOrderHom`. States on $C^*$-algebras and integrals are the main examples; their continuity is proved in the analysis volumes.

#### Common errors

1. Assuming `PosSMulMono` and `SMulPosMono` together where `IsOrderedModule` is enough. The bundled class gives both by instances, and a statement with the two granular classes is harder to apply.
2. Expecting a cancellation lemma such as `le_of_smul_le_smul_of_pos_left` from `PosSMulMono` alone. It needs `PosSMulReflectLE`, which follows over a linear ordered field but not over a general ordered ring.
3. Using `smul_le_smul_of_nonneg_left` with a negative scalar. The order is reversed; use `smul_le_smul_iff_of_neg_left`, which needs a ring of scalars.

### Exercises

1. (A) Show that $\mathbb{R}^2$ with the coordinatewise order satisfies `PosSMulMono` over $\mathbb{R}$, and that it is not a linear order.
2. (A) Show that $\mathbb{R}^2$ with the lexicographic order is an ordered module over $\mathbb{R}$.
3. (B) Give an action of an ordered ring on an ordered group that satisfies `PosSMulMono` and not `PosSMulStrictMono`.
4. (B) Show that each additive map $f : \mathbb{R}^n \to \mathbb{R}$ that is positive on the nonnegative orthant has the form $f(x) = \sum_i c_i x_i$ with $c_i \ge 0$.
5. (B) Prove $x \sqcup y = \frac{1}{2}(x + y + |y - x|)$ in a linear ordered vector space over $\mathbb{Q}$.
6. (C) Show that the trace is a positive linear map on the real symmetric matrices with the order of positive semidefinite matrices.

### Reference

<?reference?>
