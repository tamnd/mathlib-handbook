---
title: Type classes and the hierarchy
kind: guide
modules: []
explains: {}
families: []
requires: [V00.C01]
reads_with: ["TPIL", "MIL Ch. 7"]
lean:
  - MathlibHandbook/V00/C02/Examples.lean
  - MathlibHandbook/V00/C02/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Type classes and the hierarchy

### Overview

Most signatures of Mathlib have arguments in square brackets: `[Group G]`, `[Field K]`, `[LinearOrder α]`, `[PosMulStrictMono α]`. These are the *type classes*. A type class is a structure on a type, such as the structure of a group, and Lean finds it by itself. The type classes of Mathlib form a large hierarchy, from a type with a multiplication up to a complete ordered field. A lemma is stated with the weakest class that its proof needs, and then it applies to every type higher in the hierarchy.

This section explains how a class is defined, how Lean finds an instance, and how to read the conditions of a lemma. It reads the definition of a group in Mathlib, which has fewer axioms than the definition of a textbook, and proves that the missing axioms follow. It then reads the order conditions of two lemmas, `add_pos` and `mul_pos`, and proves the lemmas from those conditions. After this section a reader can tell from a signature to which types a lemma applies.

### Classes and instances

**Definition (Class).** A *class* is a structure, a record with named fields, that is marked for the instance search. A field can be an operation, such as a multiplication, or an axiom, such as associativity.

**Definition (Instance).** An *instance* of a class `C` for a type `T` is a term of type `C T` that is registered in the database of the instance search. When a lemma needs an argument `[C T]`, Lean searches the database for a term of that type.

Here is the definition of a group in Mathlib, quoted from `Mathlib/Algebra/Group/Defs.lean`.

```lean
class Group (G : Type*) extends DivInvMonoid G where
  protected inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1
```

The keyword `extends` says that a group is a `DivInvMonoid` with one more field. A `DivInvMonoid` is a monoid with an operation `⁻¹` and a division with $a / b = a b^{-1}$, with no axiom on `⁻¹`. A monoid is a semigroup with a unit $1$ such that $1 a = a$ and $a 1 = a$. A semigroup is a type with an associative multiplication. So a group in Mathlib is a type with an associative multiplication, a two-sided unit, an inverse, and the one axiom $a^{-1} a = 1$.

The definition of a textbook also asks for $a a^{-1} = 1$. Mathlib does not ask for it, because it follows.

**Theorem (Right inverses).** Let $G$ be a monoid with an operation $a \mapsto a^{-1}$ such that $a^{-1} a = 1$ for each $a \in G$. Then $a a^{-1} = 1$ for each $a \in G$.

*Proof.* Let $a \in G$ and put $b = a^{-1}$. The axiom for the element $b$ gives $b^{-1} b = 1$. The axiom for $a$ gives $b a = 1$. Now compute, with associativity used freely:
$$a b = 1 \cdot (a b) = (b^{-1} b)(a b) = b^{-1} (b a) b = b^{-1} \cdot 1 \cdot b = b^{-1} b = 1.$$
The first step uses $1 x = x$, the second uses $b^{-1} b = 1$, the third uses associativity, the fourth uses $b a = 1$, the fifth uses $1 x = x$, and the last uses $b^{-1} b = 1$ again. So $a a^{-1} = ab = 1$. $\square$

::: mathlib
`mul_inv_cancel` · `Mathlib.Algebra.Group.Defs`

In Mathlib, $a a^{-1} = 1$ is a theorem, proved in the file of the definition of `Group`. The axiom `Group.inv_mul_cancel` is `protected`, so the user writes the lemma `inv_mul_cancel` and does not see the difference between an axiom and a theorem. The attribute `simp` makes the lemma a rule of the tactic `simp`.

<?decl mul_inv_cancel?>
:::

Fewer axioms make a class easier to build: to give an instance of `Group G`, the user proves one axiom of inverses, not two. The class keeps the operation of division as a field, with a default value $a b^{-1}$. A field with a default value lets a type use a better definition of division, for example a faster one, as long as it proves that it agrees with $a b^{-1}$.

### The hierarchy

The classes of algebra form chains. Each arrow below means "extends", so each structure on the right gives the structure on the left.

1. `Mul` → `Semigroup` → `Monoid` → `DivInvMonoid` → `Group` → `CommGroup`.
2. `Mul` → `CommMagma` → `CommSemigroup` → `CommMonoid` → `CommGroup`.
3. `Semiring` → `CommSemiring` → `CommRing` → `Field`, and `Semiring` → `Ring` → `DivisionRing` → `Field`.
4. `Preorder` → `PartialOrder` → `LinearOrder`, and the order conditions of the next subsection.

Each class of additive structure has a twin: `AddMonoid`, `AddGroup`, `AddCommGroup`. A ring has an additive commutative group and a multiplicative monoid. The attribute `@[to_additive]` writes the additive lemma from the multiplicative one, so `add_comm` comes from `mul_comm`.

When a lemma needs `[CommMagma ℝ]`, the instance search starts from the instances that Mathlib gives for `ℝ`. One of them is `Real.instField`, the proof that `ℝ` is a field. A field is a commutative ring, a commutative ring is a commutative monoid, and a commutative monoid is a commutative magma. The search follows these steps and builds the term of `CommMagma ℝ`. The user sees none of this.

::: mathlib
`Real.instField` · `Mathlib.Basic.Real.Basic`

The instance that `ℝ` is a field. Its name begins with `inst`, the habit for the names of instances. The user almost never writes the name of an instance. The instance search uses it.

<?decl Real.instField?>
:::

### Why a lemma has the weakest class

The lemma `mul_comm` needs only `CommMagma`. So it applies to `ℕ`, `ℤ`, `ℚ`, `ℝ`, `ℂ`, to each commutative group and to each commutative ring. If Mathlib had stated it for fields, it would not apply to `ℕ` or `ℤ`. The rule of Mathlib is: state each lemma with the weakest class that the proof needs. The lemma `mul_one` needs `MulOneClass`, a type with a multiplication and a two-sided unit, with no associativity. The lemma `mul_assoc` needs `Semigroup`. The lemma `add_sq` needs `CommSemiring`.

The class in a signature is therefore a list of the axioms that the proof uses. A reader can learn from it which hypotheses matter. For example, `Finset.sum_const` needs only `AddCommMonoid`: the sum of a constant over a finite set is the number of elements times the constant, and this uses only that addition is associative and commutative and has a zero.

### Groups with zero

A field is not a group under multiplication, because $0$ has no inverse. Mathlib has the class `GroupWithZero`: a monoid with a zero, in which each nonzero element has an inverse. The inverse of $0$ is $0$, a junk value, Section 5.1. A lemma about inverses in a field is a lemma about groups with zero, and its name ends with `₀`.

::: mathlib
`mul_inv_cancel₀` · `Mathlib.Algebra.GroupWithZero.Defs`

The version of `mul_inv_cancel` for groups with zero. It has the hypothesis `a ≠ 0`, and the element `a` is implicit. In a field, the user writes `mul_inv_cancel₀ h` with `h : a ≠ 0`. The lemma `mul_inv_cancel` without `₀` does not apply to `ℝ`: the instance search for `Group ℝ` fails, because `ℝ` is not a group under multiplication.

<?decl mul_inv_cancel₀?>
:::

### Order conditions

The classes of ordered algebra in Mathlib are *unbundled*: an ordered ring is a ring, a partial order, and separate conditions that connect them. Each condition is a small class with a single property. The main ones are these.

1. `AddLeftMono α`: for all $a, b, c$, if $b \le c$ then $a + b \le a + c$.
2. `AddLeftStrictMono α`: for all $a, b, c$, if $b < c$ then $a + b < a + c$.
3. `PosMulStrictMono α`: for all $a, b, c$, if $0 < a$ and $b < c$ then $a b < a c$.
4. `IsOrderedRing R` and `IsStrictOrderedRing R`: the conditions of an ordered ring and of a strictly ordered ring, which give the conditions above.

The real numbers, the rationals and the integers satisfy all of them. A lemma lists only the conditions that its proof uses. Read two of them.

::: mathlib
`add_pos` · `Mathlib.Algebra.Order.Monoid.Unbundled.Basic`

At the commit of this edition, the statement of `add_pos` is more general than its name: from $b < c$ and $0 < a$ it concludes $b < c + a$. With $b = 0$, it is the usual statement that a sum of two positive elements is positive. The conditions are `AddZeroClass`, a `Preorder`, and `AddLeftStrictMono`.

<?decl add_pos?>
:::

**Theorem (A sum with a positive term).** Let $\alpha$ be a type with an addition and a zero with $c + 0 = c$, a preorder, and the condition that $b < c$ implies $a + b < a + c$. If $b < c$ and $0 < a$, then $b < c + a$.

*Proof.* The condition `AddLeftStrictMono` for the element $c$ and the inequality $0 < a$ gives $c + 0 < c + a$. Since $c + 0 = c$, this reads $c < c + a$. Together with $b < c$, transitivity of $<$ in a preorder gives $b < c + a$. $\square$

The companion uses the lemma for $0 < a + b$. The term `add_pos ha hb` with `ha : 0 < a` and `hb : 0 < b` unifies the first hypothesis `b < c` of the lemma with `0 < a`, and the second hypothesis `0 < a` of the lemma with `0 < b`. The conclusion is then `0 < a + b`.

<?lean MathlibHandbook/V00/C04/Examples.lean#add_pos?>

::: mathlib
`mul_pos` · `Mathlib.Algebra.Order.GroupWithZero.Basic`

The product of two positive elements is positive. The conditions are `MulZeroClass` (a multiplication and a zero with $a \cdot 0 = 0 = 0 \cdot a$), a `Preorder`, and `PosMulStrictMono`.

<?decl mul_pos?>
:::

**Theorem (Products of positive elements).** Let $\alpha$ be a type with a multiplication and a zero such that $a \cdot 0 = 0$, with a preorder, and with the condition that $0 < a$ and $b < c$ imply $ab < ac$. If $0 < a$ and $0 < b$, then $0 < ab$.

*Proof.* Apply the condition with $b := 0$ and $c := b$: from $0 < a$ and $0 < b$ it gives $a \cdot 0 < a b$. Since $a \cdot 0 = 0$, this is $0 < ab$. $\square$

### Examples

**Example (A lemma that does not apply to ℕ).** The lemma `sub_nonneg` states `0 ≤ a - b ↔ b ≤ a`, and it needs `[AddGroup α]`. The type `ℕ` is not an additive group, since $1$ has no negative in $\mathbb{N}$. The class matters here: the statement is false in `ℕ`. Take $a = 1$ and $b = 3$. Then $a - b = 0$ in `ℕ`, so $0 \le a - b$ is true, but $3 \le 1$ is false. A user who tries `sub_nonneg` in `ℕ` gets the error `failed to synthesize AddGroup ℕ`. The right lemma for `ℕ` is `tsub_eq_zero_iff_le` of Section 5.1.

::: mathlib
`sub_nonneg` · `Mathlib.Algebra.Order.Group.Unbundled.Basic`

The class `AddGroup α` comes first, then a relation `LE α`, then the condition `AddRightMono α`. The lemma has the attribute `simp`, so `simp` rewrites `0 ≤ a - b` to `b ≤ a`.

<?decl sub_nonneg?>
:::

**Example (Where an instance comes from).** The command `#synth CommRing ℤ` in the editor prints the instance that the search finds, here `Int.instCommRing`. The command `#synth Group ℝ` fails. It is a quick test of whether a lemma can apply to a type.

**Example (The class of the companion).** The example `instance_args` of the companion assumes `[Group G]` for an arbitrary type `G`. Inside the proof, the instance search finds the group structure from the context, not from a database: an instance argument of the statement is a local instance.

<?lean MathlibHandbook/V00/C02/Examples.lean#instance_args?>

### Common errors

1. Using a lemma of groups in a field. Use the version with `₀` and a hypothesis `≠ 0`.
2. Using a lemma of ordered groups in `ℕ`. The subtraction of `ℕ` is truncated, and Mathlib calls it `tsub`. Look for the lemma with `tsub` in the name.
3. Writing two instance arguments for the same structure, as `[Ring R] [CommRing R]`. This gives two different multiplications on `R`, and the lemmas of one do not apply to the other. Write only `[CommRing R]`.
4. Reading a long list of conditions as a sign of a hard lemma. The conditions are only the axioms that the proof uses.

### Exercises

1. (A) List the axioms of `Semigroup`, `Monoid` and `Group` in Mathlib. Compare them with the axioms of a group in a textbook.
2. (A) Explain why `mul_comm` applies to `ℕ` and `mul_inv_cancel` does not.
3. (A) Prove on paper, in a monoid with $a^{-1} a = 1$ for each $a$, that $(a^{-1})^{-1} = a$. Hint: use the theorem on right inverses.
4. (B) Show that a monoid with an operation $a \mapsto a^{-1}$ and $a a^{-1} = 1$ for each $a$ is a group. That is, prove the version of the theorem of this section with the sides exchanged.
5. (B) Give a type with a multiplication and a two-sided unit that is not associative. Hint: take a set of three elements and define a table.
6. (B) Prove that `PosMulStrictMono` holds in each ordered field. That is, prove that $0 < a$ and $b < c$ give $ab < ac$.
7. (C) Let $G$ be a semigroup with an element $e$ such that $e a = a$ for each $a$, and such that for each $a$ there is $b$ with $b a = e$. Prove that $G$ is a group with unit $e$: show that $a b = e$ and $a e = a$. Hint: follow the proof of the theorem on right inverses, with $e$ in place of $1$.

### Notes and history

Type classes come from the programming language Haskell, in a paper of Wadler and Blott (1989). The algebraic hierarchy of Mathlib was rebuilt several times. The unbundled order conditions such as `AddLeftMono` and `PosMulStrictMono` replaced the older bundled classes of ordered rings and ordered fields in 2024 and 2025. The book *Mathematics in Lean*, Chapter 7, explains how to build a class and its instances.
