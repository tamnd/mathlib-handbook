---
title: Multiplicative and additive forms
kind: theory
modules: []
explains:
  E1: [Mathlib.Tactic.ToAdditive.to_additive, mul_one, add_zero, mul_inv_cancel, add_neg_cancel, pow_succ, succ_nsmul, pow_add, add_nsmul, Finset.prod_empty, Finset.sum_empty, Multiplicative, Additive, two_mul, mul_inv_rev, neg_add_rev]
families: []
requires: [V01.C04]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V01/C06/Examples.lean
  - MathlibHandbook/V01/C06/Exercises.lean
  - MathlibHandbook/V01/C06/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Multiplicative and additive forms

### Overview

A group can be written with multiplication, $g h$, $1$ and $g^{-1}$, or with addition, $a + b$, $0$ and $-a$. The two notations describe the same mathematics. A textbook proves a theorem once and uses it in both notations. In Lean, `Group G` and `AddGroup A` are two different classes, because a ring has both an additive group and a multiplicative monoid on the same type, and the two structures must not mix. So each theorem about groups must exist twice: `mul_one` and `add_zero`, `mul_inv_cancel` and `add_neg_cancel`, `pow_succ` and `succ_nsmul`.

Mathlib does not write the second form by hand. The attribute `@[to_additive]` reads a multiplicative declaration and makes the additive one. It translates the statement, the proof and the name. This section explains the translation, proves that it is correct, and shows its limits. The next section explains the naming convention, which the translation follows.

### Definitions

**Definition (Multiplicative and additive classes).** Each multiplicative class has an additive twin with the same fields under other names:

| Multiplicative | Additive |
|---|---|
| `Mul`, `*` | `Add`, `+` |
| `One`, `1` | `Zero`, `0` |
| `Inv`, `⁻¹` | `Neg`, `-` |
| `Div`, `/` | `Sub`, `-` |
| `Pow M ℕ`, `a ^ n` | `SMul ℕ A`, `n • a` |
| `Monoid`, `Group`, `CommGroup` | `AddMonoid`, `AddGroup`, `AddCommGroup` |

**Definition (Translation).** The *additive translation* of a declaration replaces each multiplicative class, operation and constant by its twin, and replaces each part of the name by its twin: `mul` by `add`, `one` by `zero`, `inv` by `neg`, `div` by `sub`, `pow` by `nsmul` or `smul`, and `prod` by `sum`.

**Definition (The attribute).** A declaration with the attribute `@[to_additive]` gets a second declaration, its additive translation. The attribute also records the pair of names, so a later translation that meets the first name uses the second.

::: mathlib
`Mathlib.Tactic.ToAdditive.to_additive` · `Mathlib.Tactic.Translate.ToAdditive`

This is the syntax of the attribute. The forms are `@[to_additive]`, which guesses the name, `@[to_additive my_name]`, which gives the name, and `@[to_additive (attr := simp)]`, which puts the attribute `simp` on both forms. The command `to_additive_dont_translate` marks types that the translation must not change.

<?decl Mathlib.Tactic.ToAdditive.to_additive?>
:::

### Theorems and proofs

The translation is correct because of a fact about structures: a group in additive notation is a group in multiplicative notation with other names.

**Theorem (Additive groups are groups).** Let $(A, +, 0, -)$ be an additive group. Define on $A$ the operation $a \cdot b = a + b$, the constant $1 = 0$ and the inverse $a^{-1} = -a$. Then $(A, \cdot, 1, {}^{-1})$ is a group. The converse also holds.

*Proof.* Each group axiom in the new notation is the corresponding axiom in the old notation, read with the new names. For example, $(a \cdot b) \cdot c = (a + b) + c = a + (b + c) = a \cdot (b \cdot c)$, and $a^{-1} \cdot a = -a + a = 0 = 1$. The converse is the same with the names reversed. $\square$

**Corollary (Correctness of the translation).** If a statement $S$ holds in every group, then its additive translation holds in every additive group.

*Proof.* Let $A$ be an additive group. By the theorem, $A$ with the new names is a group, so $S$ holds there. The statement $S$ about this group is, after the names are replaced, the additive translation of $S$ about $A$. $\square$

In Mathlib, the pair of types in the theorem is `Multiplicative A` and `Additive G`, from `Mathlib.Algebra.Group.TypeTags.Basic`. The attribute does not use this theorem. It copies the proof term and replaces the names. The theorem explains why the copy is a correct proof.

**Theorem (A cancellation law, in both forms).** In a group, $(a b) b^{-1} = a$. In an additive group, $(a + b) + (-b) = a$.

*Proof.* $(a b) b^{-1} = a (b b^{-1}) = a \cdot 1 = a$, by associativity, the inverse law and the identity law. The additive form is the translation. $\square$

**Theorem (Powers and multiples).** Let $M$ be a monoid, $a \in M$ and $m, n \in \mathbb{N}$. Then $a^{m+n} = a^m a^n$. In an additive monoid, $(m + n) \bullet a = m \bullet a + n \bullet a$.

*Proof.* Induction on $n$. For $n = 0$, $a^{m+0} = a^m = a^m \cdot 1 = a^m a^0$, by the definition $a^0 = 1$ and the identity law. For the step, assume $a^{m+n} = a^m a^n$. Then $a^{m+(n+1)} = a^{(m+n)+1} = a^{m+n} a = (a^m a^n) a = a^m (a^n a) = a^m a^{n+1}$, by the definition $a^{k+1} = a^k a$, the hypothesis and associativity. The additive form is the translation, with $n \bullet a$ for $a^n$. $\square$

In Mathlib, the two forms are `pow_add` and `add_nsmul`. The second name shows that the translation of a name is not always word by word: the multiple is written $n \bullet a$, and the name puts `nsmul` after the operation on the exponents.

### Examples

**Example (One lemma in two forms).** `mul_one` and `add_zero` are the two forms of the right identity law. `to_additive` made `add_zero` from `mul_one`.

<?lean MathlibHandbook/V01/C06/Examples.lean#mul_one_add_zero?>

**Example (A new lemma with the attribute).** The theorem `mul_inv_cancel_right_example` has the attribute `@[to_additive]`. Lean makes `add_neg_cancel_right_example` from it, with the statement $a + b + (-b) = a$.

<?lean MathlibHandbook/V01/C06/Examples.lean#own_to_additive?>

The additive form can be used as any other theorem.

<?lean MathlibHandbook/V01/C06/Examples.lean#use_additive?>

**Example (Powers and multiples).** In a monoid, $a^{n+1} = a^n a$ is `pow_succ`. Its translation is $(n + 1) \bullet a = n \bullet a + a$, which is `succ_nsmul`. The name does not follow the simple rule here: the translation of `pow` is `nsmul`, and Mathlib gives the additive name by hand in the attribute.

**Example (Products and sums).** The product over the empty finset is $1$, and the sum over the empty finset is $0$. The lemmas are `Finset.prod_empty` and `Finset.sum_empty`, and the second is the translation of the first. In the same way, $\prod_{i \in s} f(i) g(i) = \prod_{i \in s} f(i) \prod_{i \in s} g(i)$ in a commutative monoid has the additive form $\sum_{i \in s} (f(i) + g(i)) = \sum_{i \in s} f(i) + \sum_{i \in s} g(i)$.

**Counterexample (A statement that does not translate).** The statement "$1 \neq 0$ in a field" uses both structures of the field. A naive translation would replace $1$ by $0$ and give $0 \neq 0$, which is false. So Mathlib puts the attribute only on statements about one multiplicative structure, and not on statements about rings. Lemmas about rings, such as `two_mul`, have no additive form.

### The library around it

The attribute is defined in `Mathlib.Tactic.Translate.ToAdditive`. Most lemmas in `Mathlib.Algebra.Group.Defs` and `Mathlib.Algebra.Group.Basic` carry it. The big operators $\prod$ and $\sum$ are a pair: `Finset.prod_empty` and `Finset.sum_empty` are the two forms of one lemma. The types `Multiplicative` and `Additive` turn a structure of one kind into the other, as in the theorem above. A similar attribute, `@[to_dual]`, translates statements about an order to statements about the dual order.

To find the additive form of a lemma, replace the words in the name. To find the source of an additive lemma, the documentation shows the link between the two forms.

#### Common errors

1. A learner looks for `add_inv_cancel`. The additive inverse is `neg`, so the name is `add_neg_cancel`.
2. A learner puts `@[to_additive]` on a lemma that uses both `*` and `+`. The translation replaces both operations, and the result is wrong or fails. Such a lemma must have no additive form.
3. A learner writes a lemma for `AddGroup` and then needs it for `Group`. The attribute only goes from multiplicative to additive, so state the multiplicative form first.

### Exercises

1. (A) Give the additive forms of `mul_assoc`, `one_mul`, `inv_inv`, `mul_inv_rev` and `div_eq_mul_inv`.
2. (A) Give the multiplicative forms of `neg_neg`, `sub_self` and `zero_add`.
3. (B) Prove that $(ab)^{-1} = b^{-1} a^{-1}$ in a group, and state the additive translation.
4. (B) Explain why `two_mul : 2 * a = a + a` has no additive form.
5. (C) Prove that $\mathbb{R}_{>0}$ with multiplication and $\mathbb{R}$ with addition are isomorphic groups by $\log$, and state one lemma that the translation then transfers.
6. (L) Prove that $-a + a = 0$ in an additive group. The solution is `neg_add_cancel_example` in `Solutions.lean`.

### Notes and history

The two notations for groups have been standard since the nineteenth century. Additive notation is usual for abelian groups and modules, and multiplicative notation for general groups. Mathlib for Lean 3 already had `to_additive`, and it was ported to Lean 4 with the rest of the library.

### Reference

<?reference?>
