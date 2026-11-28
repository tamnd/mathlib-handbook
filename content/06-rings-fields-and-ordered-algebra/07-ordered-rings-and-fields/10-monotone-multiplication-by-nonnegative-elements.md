---
title: Monotone multiplication by nonnegative elements
kind: api
modules:
  - Mathlib.Algebra.Order.GroupWithZero.Defs
  - Mathlib.Algebra.Order.GroupWithZero.Basic
  - Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
  - Mathlib.Algebra.Order.GroupWithZero.Unbundled.Defs
  - Mathlib.Algebra.Order.GroupWithZero.Unbundled.OrderIso
  - Mathlib.Algebra.Order.GroupWithZero.OrderIso
  - Mathlib.Algebra.Order.GroupWithZero.Bounds
  - Mathlib.Algebra.Order.GroupWithZero.Finset
  - Mathlib.Algebra.Order.GroupWithZero.Synonym
  - Mathlib.Algebra.Order.GroupWithZero.Action.Synonym
  - Mathlib.Algebra.Order.GroupWithZero.Submonoid
explains:
  E2: [PosMulMono, PosMulStrictMono, PosMulReflectLT, PosMulReflectLE, posMulMono_iff_mulPosMono, mul_le_mul_iff_of_pos_left, pow_le_pow_left₀, zpow_le_zpow_right₀, OrderIso.mulLeft₀, Finset.sup_mul_le_mul_sup_of_nonneg]
  E1: auto
families: []
requires: [V06.C01, V06.C03, V04, V05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Monotone multiplication by nonnegative elements

### Overview

Section 1 says that the mixin `IsOrderedRing` contains the classes `PosMulMono` and `MulPosMono`, and that the order lemmas of Mathlib are stated with these small classes. This section is the library behind that remark. It gives the eight classes that say how multiplication by a nonnegative or a positive element interacts with the order, the relations between them, and the lemmas about products, powers, inverses and quotients that only need these classes. The lemmas apply to ordered semirings and fields, but also to $\mathbb{N}$, to the nonnegative reals, to linearly ordered groups with zero and to other structures that are not rings.

The section needs the ordered rings and fields of Sections 1 and 2, the units and groups with zero of Chapter 3, the lattices of Volume 4 and the monoids of Volume 5. The lemmas with the suffix `₀` that Section 2 uses for fields come from this section.

### The library around it

#### The eight classes

Let $\alpha$ have a multiplication, a zero and a preorder. The four classes for left multiplication $b \mapsto a b$ are below. Each has a twin for right multiplication, with the prefix MulPos in place of PosMul.

| Class | Statement |
| --- | --- |
| `PosMulMono α` | $0 \le a$ and $b_1 \le b_2$ give $a b_1 \le a b_2$ |
| `PosMulStrictMono α` | $0 < a$ and $b_1 < b_2$ give $a b_1 < a b_2$ |
| `PosMulReflectLT α` | $0 \le a$ and $a b_1 < a b_2$ give $b_1 < b_2$ |
| `PosMulReflectLE α` | $0 < a$ and $a b_1 \le a b_2$ give $b_1 \le b_2$ |

The basic lemmas are the fields of these classes, in the form of named theorems: `mul_le_mul_of_nonneg_left`, `mul_lt_mul_of_pos_left`, `lt_of_mul_lt_mul_left` and `le_of_mul_le_mul_left`, and the right forms `mul_le_mul_of_nonneg_right` and so on. The two directions together give the equivalences `mul_le_mul_iff_of_pos_left`, $a b \le a c \iff b \le c$ for $0 < a$, which needs `PosMulMono` and `PosMulReflectLE`, and `mul_lt_mul_iff_of_pos_left` for the strict form.

#### Relations between the classes

In a partial order, the strict form gives the weak form: `PosMulStrictMono.toPosMulMono` is an instance, and `PosMulReflectLE.toPosMulReflectLT` is another. In a linear order, the classes are dual in pairs: `PosMulStrictMono.toPosMulReflectLE` is an instance, and `PosMulReflectLT.toPosMulMono` is a theorem. Proof of the first: if $a > 0$ and $a b_1 \le a b_2$ but $b_1 > b_2$, then strict monotonicity gives $a b_2 < a b_1$, a contradiction. When multiplication is commutative, the left and the right classes are the same: `posMulMono_iff_mulPosMono` and `posMulStrictMono_iff_mulPosStrictMono`, with the instance `PosMulMono.toMulPosMono`.

A structure that embeds into one with these classes inherits them. The lemmas `Function.Injective.posMulMono` and `Function.Injective.posMulStrictMono` take a map that preserves $0$ and products and reflects the order. The mixins of Section 1 give all four monotonicity classes: `IsOrderedRing` gives `PosMulMono` and `MulPosMono`, and `IsStrictOrderedRing` gives the strict forms.

#### Products and signs

The two-sided lemmas need a left class and a right class. `mul_le_mul` says that $a \le b$, $c \le d$, $0 \le c$ and $0 \le b$ give $a c \le b d$; `mul_le_mul_of_nonneg` is the form with the hypotheses $0 \le a$ and $0 \le d$, and `mul_lt_mul`, `mul_lt_mul'` and `mul_lt_mul_of_pos` are strict forms. Check the hypotheses: each lemma needs nonnegativity of a different pair of the four numbers.

The sign lemmas are `mul_pos` and `mul_nonneg`, which need only `PosMulStrictMono` and `PosMulMono`. Proof of `mul_pos`: $0 = a \cdot 0 < a \cdot b$ by strict monotonicity of left multiplication by $a > 0$. In a linear order, `pos_and_pos_or_neg_and_neg_of_mul_pos` says that a positive product has two factors of the same sign. For functions, `Monotone.mul_const` and `StrictMono.mul` give the monotonicity of $x \mapsto f(x) a$ and of $x \mapsto f(x) g(x)$ for nonnegative $f, g$.

#### Powers

In a monoid with zero, the powers of nonnegative elements behave as in $\mathbb{R}$.

- `pow_pos` and `pow_nonneg` give the sign of $a^n$.
- `pow_le_pow_left₀` says that $0 \le a \le b$ gives $a^n \le b^n$. In a linear order, `pow_le_pow_iff_left₀` and `pow_left_inj₀` give the converse for nonnegative $a, b$ and $n \ne 0$, and `sq_le_sq₀` is the case $n = 2$.
- `pow_le_pow_right₀` says that $1 \le a$ and $m \le n$ give $a^m \le a^n$, and `pow_lt_pow_right₀` is the strict form for $1 < a$.
- `one_le_pow₀`, `pow_le_one₀` and `pow_lt_one₀` compare $a^n$ with $1$. `lt_self_pow₀` says that $a < a^m$ for $1 < a$ and $1 < m$.

#### Inverses, quotients and integer powers

In a group with zero with a partial order, the reflecting classes are the ones that the lemmas about inverses need. The lemmas below need `PosMulReflectLT`, and some also `MulPosReflectLT`; a linearly ordered field has both.

- `inv_le_one₀` and `inv_lt_one₀` say that for $0 < a$, $a^{-1} \le 1 \iff 1 \le a$. In a linear order, `inv_le_one_iff₀` drops the hypothesis: $a^{-1} \le 1 \iff a \le 0 \vee 1 \le a$, since $0^{-1} = 0$.
- `inv_anti₀` says that $0 < b \le a$ gives $a^{-1} \le b^{-1}$, and `le_inv_comm₀` says $a \le b^{-1} \iff b \le a^{-1}$ for positive $a, b$.
- `div_le_one₀` says $a / b \le 1 \iff a \le b$ for $0 < b$; `div_le_div₀` and `div_le_div_iff_of_pos_left` compare quotients.
- `zpow_le_zpow_right₀` says that $1 \le a$ and $m \le n$ give $a^m \le a^n$ for integers $m, n$, and `zpow_right_strictMono₀` is the strict form. `one_lt_zpow₀` and `zpow_left_injOn₀` are other forms.

#### Order isomorphisms, lattices and bounds

Multiplication by a positive element of a group with zero is an order isomorphism. `OrderIso.mulLeft₀ a ha` is $x \mapsto a x$ as an element of `G₀ ≃o G₀`, and `OrderIso.mulRight₀` and `OrderIso.divRight₀` are the right forms. An order isomorphism preserves suprema and infima, so `mul_sup₀` says $c (a \sqcup b) = c a \sqcup c b$ for $0 \le c$, and `inf_mul₀` is a form for the infimum. The case $c = 0$ is direct.

The module `Mathlib.Algebra.Order.GroupWithZero.Finset` extends this to finite suprema. `Finset.mul₀_sup'` and `Finset.sup'_mul₀` say that multiplication by a nonnegative element commutes with `Finset.sup'`. `Finset.sup_mul_le_mul_sup_of_nonneg` gives the inequality $\sup_i (a_i b_i) \le (\sup_i a_i)(\sup_i b_i)$ for nonnegative families, and `Finset.sup_div₀` is the form with a quotient. The module `Mathlib.Algebra.Order.GroupWithZero.Bounds` has two lemmas on bounded ranges: `bddAbove_range_mul` says that the product of two bounded nonnegative functions is bounded, and `BddAbove.range_comp_of_nonneg` is the form with a monotone function.

#### Small modules

The module `Mathlib.Algebra.Order.GroupWithZero.Submonoid` defines the submonoid `Submonoid.pos α` of positive elements, with `Submonoid.mem_pos` for its members. The module `Mathlib.Algebra.Order.GroupWithZero.Synonym` transfers the structures of monoid with zero and group with zero to $\alpha^{\mathrm{od}}$ and `Lex α`, and the module `Mathlib.Algebra.Order.GroupWithZero.Action.Synonym` does the same for actions with zero. The three modules under `Mathlib.Algebra.Order.GroupWithZero.Unbundled` are deprecated and have no declarations. Each one only imports its replacement: `Mathlib.Algebra.Order.GroupWithZero.Defs`, `Mathlib.Algebra.Order.GroupWithZero.Basic` or `Mathlib.Algebra.Order.GroupWithZero.OrderIso`. Import the replacement in new code.

#### Common errors

1. `mul_le_mul` needs $0 \le c$ and $0 \le b$, and not $0 \le a$. In $\mathbb{Z}$, $-3 \le -1$ and $-2 \le 5$, but $(-3)(-2) = 6 > -5 = (-1) \cdot 5$; here $c$ and $b$ are negative.
2. The lemmas `PosMulReflectLT.toPosMulMono` and `PosMulStrictMono.toPosMulReflectLE` need a linear order. In a partial order, such as the product order on $\mathbb{R} \times \mathbb{R}$, give the classes by hand or derive them from `IsOrderedRing`.
3. The lemmas with the suffix `₀` are the general forms. A lemma without the suffix, such as `div_le_one` in `Mathlib.Algebra.Order.Field.Basic`, can need a semifield. In a structure that is not a semifield, such as a linearly ordered group with zero, use the forms with `₀`, such as `div_le_one₀`.

### Exercises

1. (A) Show that `PosMulMono ℕ` holds, by the distributive law $a c = a b + a (c - b)$ for $b \le c$.
2. (A) Use `mul_le_mul_iff_of_pos_left` to prove $3 x \le 3 y \iff x \le y$ in $\mathbb{Q}$.
3. (B) Prove `mul_pos` from `PosMulStrictMono`, and `mul_nonneg` from `PosMulMono`.
4. (B) Prove `PosMulStrictMono.toPosMulReflectLE` in a linear order.
5. (B) Prove `pow_le_pow_left₀` by induction on $n$, with `mul_le_mul`. State where the hypothesis $0 \le a$ is used.
6. (C) Show that `OrderIso.mulLeft₀` gives $c (a \sqcup b) = c a \sqcup c b$ for $c > 0$, and prove that an order isomorphism preserves binary suprema.

### Reference

<?reference?>
