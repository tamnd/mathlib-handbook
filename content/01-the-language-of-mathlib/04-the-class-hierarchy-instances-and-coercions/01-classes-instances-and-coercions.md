---
title: Structures, classes and instances
kind: theory
modules:
  - Mathlib.Algebra.HierarchyDesign
  - Mathlib.Data.Bracket
explains:
  E1: [LibraryNote.lower_instance_priority, LibraryNote.the_algebraic_hierarchy, div_mul_cancel₀, Rat.instField, Field.toCommRing, Field.toDivisionRing, CommRing.toCommSemiring, Field, GroupWithZero, Monoid, Group, mul_one, add_zero]
families: []
requires: [V01.C03]
reads_with: ["TPIL", "MIL"]
lean:
  - MathlibHandbook/V01/C04/Examples.lean
  - MathlibHandbook/V01/C04/Exercises.lean
  - MathlibHandbook/V01/C04/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Structures, classes and instances

### Overview

A textbook says "let $G$ be a group" and then uses the group axioms. A group is a set with an operation, an identity, an inverse and some laws. Mathlib follows the same plan with two tools. A *structure* packs several pieces of data and proofs into one term, as an equivalence packs a function, its inverse and two laws. A *class* is a structure that Lean finds by itself. The hypothesis `[Group G]` asks for a group structure on the type `G`, and Lean supplies it from a list of known *instances*. So one lemma about all groups applies at once to $\mathbb{Z}$, to the permutations of a set and to the units of a ring.

This section explains structures, classes, instance search and the hierarchy of algebraic classes in Mathlib. It proves two facts from the axioms of a class, to show how a proof "for all fields" works: the identity of a monoid is unique, and a field has no zero divisors. The next section treats bundled maps, which are structures that act as functions.

### Definitions

**Definition (Structure).** A *structure* is an inductive type with one constructor. Its arguments are the *fields*. A term of the structure is given by a value for each field, and each field has a *projection*. Equality of two terms of a structure holds when all fields are equal.

For example, a structure `Point` with fields `x : ℝ` and `y : ℝ` has terms `⟨1, 2⟩`, and `p.x` is the first projection. The structure `Equiv α β` of Chapter 3 has four fields, two of them proofs.

**Definition (Extension).** A structure can *extend* another structure. It then has all the fields of the old structure and some new ones. Lean gives a projection from the new structure to the old one. A group extends a monoid: it adds an inverse and the law $a^{-1} a = 1$.

**Definition (Class and instance).** A *class* is a structure marked for instance search. An *instance* is a definition of a term of a class, marked so that Lean can find it. An argument in square brackets, such as `[Field K]`, is an *instance argument*. Lean fills it by a search among the instances. Instances can depend on other instances: an instance of `Field K` gives instances of `CommRing K`, of `DivisionRing K` and of many other classes, by the projections.

**Definition (Unbundled and bundled classes).** In Mathlib the algebraic structure is a class on a type. The carrier is the type, and the operations and laws are the fields of the class. The type `ℚ` stays the same, and `Field ℚ` is a separate term found by search. This is called the *unbundled* form. The *bundled* form is a structure that contains the type as a field, as in a category of groups.

::: mathlib
`LibraryNote.lower_instance_priority` · `Mathlib.Algebra.HierarchyDesign`

The module `Mathlib.Algebra.HierarchyDesign` has no theorems. It has the library notes that describe the design of the algebraic hierarchy. This note explains why an instance that goes from a class to a weaker class, such as from `Field` to `Ring`, gets a low priority: the search should try the direct instances first.

<?decl LibraryNote.lower_instance_priority?>
:::

**Definition (The algebraic hierarchy).** The main algebraic classes form a hierarchy by extension. Some of the chains:

1. `Semigroup`, `Monoid`, `Group`, `CommGroup` for a multiplication, with the additive forms `AddSemigroup`, `AddMonoid`, `AddGroup` and `AddCommGroup`;
2. `Semiring`, `Ring`, `CommRing`, with `CommSemiring` between;
3. `DivisionRing` and `Field`, where `Field` extends `CommRing` and `DivisionRing`;
4. `GroupWithZero`, for a monoid with a zero in which every nonzero element has an inverse.

A field is a commutative ring with an inverse $a^{-1}$ for each $a \neq 0$, and with $0 \neq 1$. In Mathlib the inverse is a total function, and $0^{-1} = 0$. Chapter 5 explains this choice.

### Theorems and proofs

**Theorem (Uniqueness of the identity).** Let $M$ be a type with a binary operation $\cdot$. If $e$ and $e'$ are both two-sided identities, that is, $e \cdot a = a = a \cdot e$ and $e' \cdot a = a = a \cdot e'$ for every $a$, then $e = e'$.

*Proof.* Compute $e \cdot e'$ in two ways. Since $e$ is a left identity, $e \cdot e' = e'$. Since $e'$ is a right identity, $e \cdot e' = e$. So $e = e'$. $\square$

The theorem shows why a monoid can store its identity as data: there is only one choice. For two monoid structures on the same type with the same multiplication, the identities are equal, and the two structures are equal.

**Theorem (Fields have no zero divisors).** Let $K$ be a field and $a, b \in K$. If $ab = 0$, then $a = 0$ or $b = 0$.

*Proof.* By the excluded middle, $a = 0$ or $a \neq 0$. In the first case, done. In the second case, $a$ has an inverse with $a^{-1} a = 1$. Then
$$b = 1 \cdot b = (a^{-1} a) b = a^{-1}(ab) = a^{-1} \cdot 0 = 0.$$
The steps use the identity law, the inverse law, associativity and the law $x \cdot 0 = 0$. The last law holds in every ring: $x \cdot 0 = x \cdot (0 + 0) = x \cdot 0 + x \cdot 0$, and cancellation of $x \cdot 0$ in the additive group gives $x \cdot 0 = 0$. $\square$

In Mathlib, this theorem is the instance that a field is a domain. A lemma that needs `[NoZeroDivisors K]` then applies to every field, with no extra hypothesis. This is the effect of instance search: the theorem is proved once, as an instance, and the search uses it whenever it is needed.

**Theorem (Cancellation in a field).** Let $K$ be a field, $a, b \in K$ and $b \neq 0$. Then $(a / b) \cdot b = a$.

*Proof.* In Mathlib, $a / b$ is $a \cdot b^{-1}$. So $(a / b) \cdot b = (a \cdot b^{-1}) \cdot b = a \cdot (b^{-1} \cdot b) = a \cdot 1 = a$, by associativity, the inverse law for $b \neq 0$ and the identity law. $\square$

The proof uses only the axioms of a group with zero, so the lemma `div_mul_cancel₀` holds in every `GroupWithZero`. A field gives such a structure by an instance, and the lemma applies to $\mathbb{Q}$ and $\mathbb{R}$.

### Examples

**Example (The field of rational numbers).** The instance `Rat.instField` gives the field structure on `ℚ`. The term `inferInstance` asks Lean to find an instance of the goal. Here the goal is `Field ℚ`, and the search finds `Rat.instField`.

<?lean MathlibHandbook/V01/C04/Examples.lean#field_rat?>

**Example (A lemma for all fields).** The lemma `div_mul_cancel₀` is stated for a group with zero. For `a b : ℚ`, Lean must find `GroupWithZero ℚ`. There is no instance for `ℚ` directly. The search finds `Field ℚ`, and an instance from fields to division rings to groups with zero, and so it succeeds.

<?lean MathlibHandbook/V01/C04/Examples.lean#div_mul_cancel?>

**Example (Two monoid structures on one type).** The natural numbers have two monoid structures: addition with $0$, and multiplication with $1$. Lean resolves the conflict by notation. `Monoid ℕ` is the multiplicative structure, and `AddMonoid ℕ` is the additive one. A lemma such as `mul_one` uses the first, and `add_zero` uses the second. Chapter 6 shows how Mathlib proves both lemmas from one source.

**Counterexample (A ring with zero divisors).** The theorem on zero divisors fails in $\mathbb{Z}/6\mathbb{Z}$: $2 \cdot 3 = 0$, and $2 \neq 0 \neq 3$. The proof fails at the step that inverts $a$, since $2$ has no inverse modulo $6$. So $\mathbb{Z}/6\mathbb{Z}$ is a commutative ring that is not a field, and Mathlib has no instance of `Field (ZMod 6)`. For a prime $p$, the instance for `ZMod p` exists under the hypothesis `[Fact p.Prime]`.

### The library around it

The algebraic classes live in `Mathlib.Algebra.Group.Defs`, `Mathlib.Algebra.Ring.Defs`, `Mathlib.Algebra.Field.Defs` and `Mathlib.Algebra.GroupWithZero.Defs`. Each class has instances for the standard types: `Int.instCommRing`, `Nat.instCommSemiring`, `Rat.instField` and `Real.instField`. The projections from a class to its parents are instances such as `Field.toCommRing`, `Field.toDivisionRing` and `CommRing.toCommSemiring`.

The command `#synth Field ℚ` shows the instance that Lean finds. The option `set_option trace.Meta.synthInstance true` shows the steps of the search. A missing instance causes the error "failed to synthesize". The fix is often to add an instance argument to the statement, such as `[Field K]`, or to import the module that contains the instance.

A *diamond* occurs when two paths of instances give two structures on one type, for example two different paths from `Field ℚ` to `Monoid ℚ`. Mathlib designs its classes so that the two paths give terms that are equal by definition, so the diamond causes no error. The library notes in `Mathlib.Algebra.HierarchyDesign` describe the methods.

#### Common errors

1. A learner states a lemma with `(h : Field K)` in round brackets. Lean does not use `h` for instance search. Use `[Field K]`.
2. A learner writes two instance arguments `[Ring K] [Field K]`. This makes two unrelated ring structures on `K`, and lemmas mix them. Use only `[Field K]`.

### Exercises

1. (A) Write a structure for intervals $[a, b]$ of real numbers with $a \leq b$, and give two terms of it.
2. (A) List the classes on the path from `Field` to `Monoid` in Mathlib.
3. (B) Prove that in a monoid, if $a$ has a left inverse $b$ and a right inverse $c$, then $b = c$.
4. (B) Prove from the field axioms that $(-1) \cdot (-1) = 1$ in any field. Which axioms does the proof use? Does it need a field, or only a ring?
5. (B) Prove that in a field, $a^2 = 1$ implies $a = 1$ or $a = -1$. Find a ring where the statement fails.
6. (C) Show that a finite commutative ring with $0 \neq 1$ and no zero divisors is a field. Hint: multiplication by $a \neq 0$ is injective, and Exercise 7 of Section 1 of Chapter 3 applies.
7. (L) Prove that $2 \cdot 2^{-1} = 1$ in $\mathbb{Q}$. The solution is `two_mul_inv_example` in `Solutions.lean`.

### Notes and history

The axioms of a group were stated by Cayley (1854) and in modern form by Weber (1882). The axioms of a field were stated by Steinitz (1910) and the axioms of a ring by Fraenkel (1914) and Noether (1921). The hierarchy of structures, in which each structure extends the previous one, is the plan of Bourbaki's *Éléments*.

### Reference

<?reference?>
