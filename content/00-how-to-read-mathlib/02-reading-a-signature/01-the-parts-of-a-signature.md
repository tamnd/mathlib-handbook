---
title: The parts of a signature
kind: guide
modules: []
explains: {}
families: []
requires: [V00.C01]
reads_with: ["TPIL", "MIL Ch. 2"]
lean:
  - MathlibHandbook/V00/C02/Examples.lean
  - MathlibHandbook/V00/C02/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The parts of a signature

### Overview

Each declaration of Mathlib has a signature: its name, its arguments and its type. The Mathlib box of each section of the handbook shows the signature, as Lean prints it at the commit of the edition. A reader who can read a signature can use a lemma without its proof, in the same way that a mathematician uses a theorem of a book after reading only its statement.

This section shows how to read a signature. It explains the four kinds of argument and how Lean finds the arguments that the user does not give. It shows how hypotheses appear as arrows, and it reads several signatures of Mathlib in full. The next sections of this chapter explain the arguments in square brackets (Section 2.2), the arrows `↑` of the coercions (Section 2.3) and the common forms of the statement itself (Section 2.4).

### A first signature

The signature of `mul_comm` is in the box below.

::: mathlib
`mul_comm` · `Mathlib.Algebra.Group.Semigroup`

The lemma `mul_comm` states that multiplication is commutative in each commutative magma: a type with a multiplication that is commutative, with no other axiom. A commutative group, a commutative ring and a field are all commutative magmas, so the lemma applies to each of them.

<?decl mul_comm?>
:::

The printed form is a single statement that begins with `∀`. Read it from left to right.

1. `{G : Type u_1}`: for each type `G`. The braces make the argument implicit.
2. `[inst : CommMagma G]`: and each structure of commutative magma on `G`. The square brackets make it an instance argument.
3. `(a b : G)`: and all elements `a` and `b` of `G`. The parentheses make them explicit.
4. `a * b = b * a`: the statement.

In words: for each type $G$ with a commutative multiplication, and for all $a, b \in G$, $ab = ba$. Lean prints the same signature in a second form, with the arguments before a colon, as `mul_comm {G : Type u_1} [CommMagma G] (a b : G) : a * b = b * a`. The two forms mean the same: an argument before the colon is a variable bound by `∀`.

### The four kinds of argument

1. An *explicit* argument is in parentheses, as `(a b : G)`. The user gives it. In the term `mul_comm x y`, the first explicit argument is `x` and the second is `y`.
2. An *implicit* argument is in braces, as `{G : Type u_1}`. Lean finds its value from the other arguments or from the goal. The user does not give it.
3. An *instance* argument is in square brackets, as `[inst : CommMagma G]`. Lean finds its value by the instance search, a search in a database of instances. The value is a structure: here, the multiplication of `G` with the proof that it is commutative. The name `inst` has no role, and Lean often omits it.
4. A *strict implicit* argument is in double braces, as `⦃x : α⦄`. Lean fills it only when an explicit argument after it is given. This kind is rare. It appears in the definition of the inclusion of sets: `s ⊆ t` is `∀ ⦃a⦄, a ∈ s → a ∈ t`. A proof `h : s ⊆ t` stays a proof of an inclusion until it gets a proof of `a ∈ s`, and then `h ha` is a proof of `a ∈ t`.

The rule for the choice of the kind is simple. An argument that Lean can find from the types of the later arguments is implicit. A structure on a type is an instance argument. All other arguments are explicit. In `mul_comm`, the type `G` is implicit, because Lean finds it from the type of `a`.

### How Lean finds an implicit argument

Lean finds an implicit argument by *unification*: it compares the type that the lemma needs with the type that the user gives, and it solves for the unknown. Follow it on an example.

**Example (Unification step by step).** In the goal `(3 : ℤ) * x = x * 3`, the user writes `mul_comm 3 x`.

1. Lean creates an unknown $?G$ for the implicit type and an unknown $?inst$ for the instance.
2. The first explicit argument must have type $?G$. The term `3` with `x : ℤ` in the goal has type `ℤ`, so $?G := ℤ$.
3. The instance search looks for a term of `CommMagma ℤ`. It finds one, built from the instance `Int.instCommRing` that `ℤ` is a commutative ring.
4. The term `mul_comm 3 x` has type `3 * x = x * 3`, which is the goal.

The example blocks of the companion show the same steps.

**Example (Explicit arguments).** The arguments `a` and `b` of `add_comm` are explicit, so the proof gives them.

<?lean MathlibHandbook/V00/C02/Examples.lean#explicit_args?>

**Example (Implicit arguments).** The type `ℤ` and the instance are implicit. Lean finds them from `a` and `b`.

<?lean MathlibHandbook/V00/C02/Examples.lean#implicit_args?>

**Example (All arguments explicit).** The symbol `@` before a name makes each argument explicit. The symbol `_` asks Lean to find that argument, here the instance.

<?lean MathlibHandbook/V00/C02/Examples.lean#at_explicit?>

**Example (An instance argument).** The argument `[Group G]` gives the group structure of `G`. The lemma `mul_inv_cancel` then applies to each element of `G`.

<?lean MathlibHandbook/V00/C02/Examples.lean#instance_args?>

**Example (A named argument).** An explicit argument can go by its name, in any position. The name is the name in the signature.

<?lean MathlibHandbook/V00/C02/Examples.lean#named_args?>

### Hypotheses are arguments

A hypothesis of a theorem is an argument whose type is a statement. The signature writes it in one of two ways: as a named argument, as `(h : a ≠ 0)`, or as an arrow, as `a ≠ 0 → a / a = 1`. The two forms are the same statement. An arrow `P → Q` is the type of the functions that take a proof of `P` to a proof of `Q`, and Section 3.1 explains this.

::: mathlib
`div_self` · `Mathlib.Algebra.GroupWithZero.Units.Basic`

The element `a` is implicit, in braces. The only explicit argument is the hypothesis `a ≠ 0`, written as an arrow. So `div_self h` is a proof of `a / a = 1` when `h` is a proof of `a ≠ 0`, and Lean finds `a` from the type of `h`.

<?decl div_self?>
:::

The theorem below is the rule that justifies the arrow form. It is a fact of logic.

**Theorem (Curried hypotheses).** For statements $P$, $Q$ and $R$, the statement $P \land Q \to R$ holds if and only if $P \to (Q \to R)$ holds.

*Proof.* Suppose $P \land Q \to R$. To prove $P \to (Q \to R)$, assume $P$ and then assume $Q$. Then $P \land Q$ holds, so $R$ holds. Conversely, suppose $P \to (Q \to R)$, and assume $P \land Q$. Then $P$ holds, so $Q \to R$ holds. Also $Q$ holds, so $R$ holds. $\square$

Mathlib writes a theorem with two hypotheses as `P → Q → R`, which Lean reads as `P → (Q → R)`, because the arrow groups to the right. The curried form lets the user give the hypotheses one at a time: if `h : P → Q → R` and `hp : P`, then `h hp : Q → R`.

::: mathlib
`le_antisymm` · `Mathlib.Order.Defs.PartialOrder`

Antisymmetry of a partial order: $a \le b$ and $b \le a$ give $a = b$. The two hypotheses are two arrows. The elements `a` and `b` are implicit, because Lean finds them from the hypotheses. So `le_antisymm h₁ h₂` is a proof of `a = b` when `h₁ : a ≤ b` and `h₂ : b ≤ a`.

<?decl le_antisymm?>
:::

### Equivalences

A statement `P ↔ Q` is a pair of implications. If `h : P ↔ Q`, then `h.mp : P → Q` and `h.mpr : Q → P`. The names come from *modus ponens*. Lean also accepts `h.1` and `h.2`.

**Example (An equivalence).** The lemma `Nat.pos_iff_ne_zero` has the statement `0 < n ↔ n ≠ 0`. Its direction `.mpr` proves `0 < n` from `n ≠ 0`.

<?lean MathlibHandbook/V00/C02/Examples.lean#iff_use?>

An equivalence is also a rule of rewriting. The tactic `rw [h]` with `h : P ↔ Q` replaces `P` by `Q` in the goal. Section 3.3 explains rewriting.

### Reading a longer signature

**Example (The infinitude of the primes).** The signature `∀ (n : ℕ), ∃ p, n ≤ p ∧ Nat.Prime p` of `Nat.exists_infinite_primes` has one explicit argument `n`, no implicit argument and no instance. The statement is an existence statement: there is `p` with `n ≤ p` and `p` prime. The term `Nat.exists_infinite_primes 100` is a proof of `∃ p, 100 ≤ p ∧ Nat.Prime p`.

**Example (A lemma about a power).** The lemma `Nat.Prime.dvd_of_dvd_pow` has the signature below. The three numbers `p`, `m` and `n` are implicit. There are two hypotheses: `Nat.Prime p` and `p ∣ m ^ n`. Lean finds `p`, `m` and `n` from the types of the two proofs. So `Nat.Prime.dvd_of_dvd_pow hp h` proves `p ∣ m`. In words: if a prime divides a power, then it divides the base.

::: mathlib
`Nat.Prime.dvd_of_dvd_pow` · `Mathlib.Data.Nat.Prime.Basic`

The name lives in the namespace `Nat.Prime`, so dot notation applies: `hp.dvd_of_dvd_pow h` is the same term as `Nat.Prime.dvd_of_dvd_pow hp h`.

<?decl Nat.Prime.dvd_of_dvd_pow?>
:::

**Example (A lemma of analysis).** The lemma `Real.sqrt_eq_zero_of_nonpos` has the signature `∀ {x : ℝ}, x ≤ 0 → √x = 0`. There is one implicit real number and one hypothesis. The conclusion is the junk value of the square root of a negative number, Section 5.1.

### Universes

A type of types has a level. `Type` is `Type 0`, and `Type 1` is the type of `Type 0`. A signature writes `Type u_1` or `Type*` when the lemma is true at each level. The level exists to avoid the paradox of a type of all types, in the same way that set theory avoids a set of all sets. For most uses of the handbook, the level has no effect, and the reader can read `Type u_1` as "a type". A signature also uses `Sort u`, which includes `Prop`, the type of statements, as `Sort 0`.

### What the signature does not show

The signature shows the statement and no more. It does not show the proof, the attributes such as `@[simp]`, or the documentation. The page of the declaration on the site shows all of them. The signature also does not show how a definition is defined: the signature of `Nat.Prime` is only `ℕ → Prop`. To see the body of a definition, use `#print Nat.Prime` in the editor, or open the source.

### Common errors

1. Giving an implicit argument as an explicit one. The term `mul_comm ℤ 2 3` fails, because the first explicit argument of `mul_comm` is an element, not a type. Write `mul_comm (2 : ℤ) 3` or `@mul_comm ℤ _ 2 3`.
2. Forgetting a hypothesis. The term `div_self` alone is a function that waits for a proof of `a ≠ 0`. The error message says that the type is `?a ≠ 0 → ?a / ?a = 1`, with unknowns.
3. Reading `P → Q → R` as `(P → Q) → R`. The arrow groups to the right.
4. Expecting Lean to find an explicit argument. Lean finds only implicit and instance arguments. The user can write `_` for an explicit argument when Lean can find it by unification.

### Exercises

1. (A) In the signature of `mul_comm`, which arguments must a user give? Which ones does Lean find?
2. (A) Write the signature of `add_comm` from memory, then compare it with its page on the site.
3. (A) The lemma `Nat.pos_iff_ne_zero` has the statement `0 < n ↔ n ≠ 0`. Write the type of `Nat.pos_iff_ne_zero.mp`.
4. (B) In the signature of `le_antisymm`, the elements `a` and `b` are implicit. Explain why Lean can always find them. Give a lemma in which an element must be explicit, and explain why.
5. (B) The definition `Set.Subset` has a strict implicit argument. Let `h : s ⊆ t` and `ha : x ∈ s`. Give the type of `h ha`, and the type of `h` itself.
6. (B) Prove on paper the equivalence of $P \to (Q \to R)$ and $Q \to (P \to R)$. Explain what it means for the order of the hypotheses of a lemma.
7. (L) Prove `MathlibHandbook.V00.C02.Exercises.add_comm_three` with `rw` and `add_comm`.
8. (L) Prove `MathlibHandbook.V00.C02.Exercises.inv_mul_example`. Find the lemma by its name: the inverse of `a`, times `a` times `b`, on the left.
9. (L) Prove `MathlibHandbook.V00.C02.Exercises.pos_of_ne_zero_example` with the `.mpr` direction of a lemma.

### Notes and history

The four kinds of argument are part of the type theory of Lean. *Theorem Proving in Lean 4* explains them in its chapter on dependent type theory and its chapter on type classes. The curried form of a statement is named after Haskell Curry, although the idea goes back to Moses Schönfinkel (1924) and Gottlob Frege. The Mathlib box of the handbook prints the signature that Lean prints with the command `#check @name`.
