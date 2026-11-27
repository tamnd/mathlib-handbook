---
title: Sets as predicates
kind: theory
modules: []
explains:
  E2: [Set.mem_ofPred_eq]
  E1: auto
families: []
requires: [V01.C01]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V01/C02/Examples.lean
  - MathlibHandbook/V01/C02/Exercises.lean
  - MathlibHandbook/V01/C02/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Sets as predicates

### Overview

In Zermelo-Fraenkel set theory, everything is a set, and an element can belong to many sets. In Lean, every term has exactly one type, and a type is not a set. Mathlib uses two tools to speak about collections. A *set* `s : Set α` collects some elements of one fixed type $\alpha$, the *ambient type*. A *subtype* is a new type made of the elements with a property. This section treats sets. The third section of this chapter treats subtypes.

A set of elements of $\alpha$ is given by a property: an element is in the set exactly when it has the property. So a set is the same information as a predicate $\alpha \to \mathrm{Prop}$. With this reading, the operations on sets become the connectives of Chapter 1: intersection is "and", union is "or", complement is "not", and inclusion is "implies". Every law of the algebra of sets then follows from a law of logic. The section proves the standard laws in this way.

### Definitions

**Definition (Set).** For a type $\alpha$, the type `Set α` is a structure with one field, `Set.Mem : α → Prop`. The constructor `Set.ofPred` turns a predicate $p$ into a set, written $\{x \mid p(x)\}$. For $s$ a set and $a : \alpha$, the statement $a \in s$ is $\texttt{Set.Mem}\ s\ a$. So $a \in \{x \mid p(x)\}$ unfolds to $p(a)$.

*Remark.* In earlier versions of Mathlib, `Set α` was defined as the function type `α → Prop` itself. In this edition, it is a structure that wraps the predicate. The two forms carry the same information, and membership still unfolds by definition. The structure prevents a set from being used as a function by mistake, so the term `s a` is no longer valid. Write `a ∈ s`.

**Definition (Inclusion and equality).** For sets $s, t$ in `Set α`, the set $s$ is a *subset* of $t$, written $s \subseteq t$, when $\forall x,\ x \in s \to x \in t$. The sets are equal when they are equal as terms of `Set α`.

**Definition (Operations).** For sets $s, t$ in `Set α`:

1. the *intersection* is $s \cap t = \{x \mid x \in s \land x \in t\}$;
2. the *union* is $s \cup t = \{x \mid x \in s \lor x \in t\}$;
3. the *complement* is $s^{c} = \{x \mid x \notin s\}$;
4. the *difference* is $s \setminus t = \{x \mid x \in s \land x \notin t\}$;
5. the *empty set* is $\emptyset = \{x \mid \mathrm{False}\}$ and the *universal set* is $\mathrm{univ} = \{x \mid \mathrm{True}\}$;
6. for a predicate $p$, the *separation* is $\{x \in s \mid p(x)\} = \{x \mid x \in s \land p(x)\}$.

The complement is relative to the ambient type. The set $\{n : \mathbb{N} \mid n < 3\}^{c}$ is the set of natural numbers at least $3$, and it contains no negative numbers, because the ambient type is $\mathbb{N}$.

::: mathlib
`Set.mem_ofPred_eq` · `Mathlib.Data.Set.Operations`

The lemma states `(a ∈ {x | p x}) = p a`. It is a simp lemma, so `simp` turns membership in a set-builder set into the property. The old name `Set.mem_setOf_eq` is deprecated in this edition. The same unfolding also holds by definition, so `Iff.rfl` and `id` prove it, and `show p a` changes the goal.

<?decl Set.mem_ofPred_eq?>
:::

### Theorems and proofs

**Theorem (Extensionality).** Let $s, t$ be sets in `Set α`. If $x \in s \leftrightarrow x \in t$ for every $x$, then $s = t$.

*Proof.* Write $s = \texttt{ofPred}\ p$ and $t = \texttt{ofPred}\ q$, by the structure. The hypothesis says $p(x) \leftrightarrow q(x)$ for every $x$. By propositional extensionality, $p(x) = q(x)$ for every $x$. By function extensionality, $p = q$. So $s = \texttt{ofPred}\ p = \texttt{ofPred}\ q = t$. $\square$

::: mathlib
`Set.ext` · `Mathlib.Data.Set.Defs`

The statement is `(∀ x, x ∈ a ↔ x ∈ b) → a = b`. The tactic `ext x` applies it and introduces `x`. A goal `s = t` about sets almost always starts with `ext x` and `simp`, or with `Set.Subset.antisymm`.

<?decl Set.ext?>
:::

**Theorem (Inclusion is a partial order).** For sets $r, s, t$ in `Set α`:

1. $s \subseteq s$;
2. if $r \subseteq s$ and $s \subseteq t$, then $r \subseteq t$;
3. if $s \subseteq t$ and $t \subseteq s$, then $s = t$.

*Proof.* 1. For each $x$, the identity function sends a proof of $x \in s$ to itself. 2. Let $x \in r$. The first inclusion gives $x \in s$, and the second gives $x \in t$. 3. For each $x$, the two inclusions give the two directions of $x \in s \leftrightarrow x \in t$. Extensionality gives $s = t$. $\square$

::: mathlib
`Set.Subset.antisymm` · `Mathlib.Data.Set.Basic`

This is part 3. The two goals `s ⊆ t` and `t ⊆ s` each start with `intro x hx`. A proof of equality by "double inclusion" in a textbook becomes `Set.Subset.antisymm (fun x hx => ...) (fun x hx => ...)`.

<?decl Set.Subset.antisymm?>
:::

**Theorem (Distributive laws).** For sets $r, s, t$ in `Set α`:
$$r \cap (s \cup t) = (r \cap s) \cup (r \cap t), \qquad r \cup (s \cap t) = (r \cup s) \cap (r \cup t).$$

*Proof.* Fix $x$, and write $a$, $b$, $c$ for $x \in r$, $x \in s$, $x \in t$. By extensionality and the definitions, the first equation is the equivalence $a \land (b \lor c) \leftrightarrow (a \land b) \lor (a \land c)$. From left to right: from $a$ and $b \lor c$, take cases. If $b$, then $a \land b$, so the left disjunct holds. If $c$, then $a \land c$. From right to left: in each case, $a$ holds, and $b \lor c$ holds.

The second equation is $a \lor (b \land c) \leftrightarrow (a \lor b) \land (a \lor c)$. From left to right: if $a$, then both disjunctions hold. If $b \land c$, then $a \lor b$ by $b$ and $a \lor c$ by $c$. From right to left: take cases on $a \lor b$. If $a$, done. If $b$, take cases on $a \lor c$. If $a$, done. If $c$, then $b \land c$. $\square$

**Theorem (De Morgan laws for sets).** For sets $s, t$ in `Set α`:
$$(s \cup t)^{c} = s^{c} \cap t^{c}, \qquad (s \cap t)^{c} = s^{c} \cup t^{c}.$$
The first law holds in intuitionistic logic. The second law needs the excluded middle.

*Proof.* Fix $x$, and write $a$ for $x \in s$ and $b$ for $x \in t$. The first equation is $\lnot(a \lor b) \leftrightarrow \lnot a \land \lnot b$. From left to right: if $a$, then $a \lor b$, which contradicts the hypothesis, so $\lnot a$. In the same way $\lnot b$. From right to left: assume $a \lor b$. Each case contradicts one of $\lnot a$ and $\lnot b$.

The second equation is $\lnot(a \land b) \leftrightarrow \lnot a \lor \lnot b$. From right to left: in each case, $a \land b$ gives a contradiction. From left to right: by the excluded middle, $a$ or $\lnot a$. If $\lnot a$, the left disjunct holds. If $a$, then $b$ would give $a \land b$, so $\lnot b$, and the right disjunct holds. $\square$

::: mathlib
`Set.compl_inter` · `Mathlib.Order.BooleanAlgebra.Set`

Mathlib proves the laws of complement once, for every Boolean algebra, and `Set α` is an instance. The lemmas for sets, such as `Set.compl_union` and `Set.compl_inter`, are the general lemmas for this instance. Volume 4 develops the lattice point of view. For sets, a proof by `ext x` and `simp` with the membership lemmas also works, and `tauto` finishes the logic.

<?decl Set.compl_inter?>
:::

**Theorem (Difference).** For sets $s, t$ in `Set α`, the difference is $s \setminus t = s \cap t^{c}$, and $s \setminus t = \emptyset$ if and only if $s \subseteq t$.

*Proof.* The first equation holds for each $x$ by the definitions: both sides are $x \in s \land x \notin t$.

Assume $s \subseteq t$ and let $x \in s \setminus t$. Then $x \in s$ gives $x \in t$, which contradicts $x \notin t$. So $s \setminus t$ has no element, and it equals $\emptyset$ by extensionality. Conversely, assume $s \setminus t = \emptyset$ and let $x \in s$. By the excluded middle, $x \in t$ or $x \notin t$. In the second case, $x \in s \setminus t = \emptyset$, which is false. So $x \in t$. $\square$

### Examples

**Example (Membership by definition).** The membership `x ∈ {n | Even n}` is `Even x`. Both sides are the same proposition after unfolding, so `Iff.rfl` proves the equivalence.

<?lean MathlibHandbook/V01/C02/Examples.lean#mem_setOf?>

**Example (Two equal sets).** The set of natural numbers below $2$ is $\{0, 1\}$. On paper: if $n < 2$, then $n = 0$ or $n = 1$, and both $0$ and $1$ are below $2$. In Lean, the tactic `ext` reduces the equation to membership, `simp only` unfolds the memberships, and `omega` closes the arithmetic.

<?lean MathlibHandbook/V01/C02/Examples.lean#set_ext?>

**Example (A law with a direct proof).** For sets of integers, let $E$ be the even numbers and $T$ the multiples of $3$. Then $E \cap T$ is the multiples of $6$. If $2 \mid n$ and $3 \mid n$, write $n = 2k$. Then $3 \mid 2k$, and since $\gcd(2, 3) = 1$, $3 \mid k$. So $k = 3j$ and $n = 6j$. Conversely, $6j = 2(3j) = 3(2j)$. The proof uses the definition of $\cap$ and nothing else about sets.

**Example (Complement depends on the type).** Let $s = \{x \mid 0 < x\}$. In `Set ℕ`, the complement $s^{c}$ is $\{0\}$. In `Set ℤ`, it is the set of $x \leq 0$, an infinite set. In Lean, the type of $s$ is part of the term, so the two complements are different terms, and a proof must say which one it means.

**Counterexample (A wrong De Morgan law).** The equation $(s \cap t)^{c} = s^{c} \cap t^{c}$ is false in general. Take $\alpha = \mathbb{N}$, $s = \{0\}$ and $t = \{1\}$. Then $s \cap t = \emptyset$, so $(s \cap t)^{c} = \mathbb{N}$. But $s^{c} \cap t^{c}$ does not contain $0$. The correct law has $\cup$ on the right.

### The library around it

Each operation on sets has a membership lemma named `Set.mem_` and the operation: `Set.mem_inter_iff`, `Set.mem_union`, `Set.mem_compl_iff`, `Set.mem_sdiff`, `Set.mem_univ`, `Set.notMem_empty` and `Set.mem_sep_iff`. They are simp lemmas, so `simp` reduces a statement about sets to a statement in logic. Then `tauto` or a direct proof finishes. The laws of the algebra of sets have names that describe them: `Set.inter_comm`, `Set.union_comm`, `Set.inter_union_distrib_left`, `Set.union_inter_distrib_left`, `Set.compl_union` and `Set.compl_inter`. The difference is written `s \ t` and its lemmas use `sdiff` in this edition, for example `Set.mem_sdiff` and `Set.sdiff_eq`.

The basic definitions are in `Mathlib.Data.Set.Defs` and `Mathlib.Data.Set.Operations`. The lemmas are in `Mathlib.Data.Set.Basic`. Volume 3 treats sets and their images under functions in detail.

#### Common errors

1. A learner writes `s x` for membership. With the structure form of `Set`, this is an error. Write `x ∈ s`.
2. A learner tries `rw [Set.mem_setOf_eq]` and gets a warning about a deprecated name. Use `Set.mem_ofPred_eq`, or `simp only [Set.mem_ofPred_eq]`.
3. A learner forgets that the complement is relative to the type. A statement about `(sᶜ : Set ℕ)` does not hold for `Set ℤ`.
4. A learner proves `s = t` with `simp` and no `ext`, and `simp` makes no progress. Start with `ext x`.

### Exercises

1. (A) Write the set of even integers in set-builder form, and state what membership of $6$ in it unfolds to.
2. (A) Explain why the membership $3 \in \{n : \mathbb{N} \mid n < 5\}$ and the statement $3 < 5$ have the same proof.
3. (A) Prove $s \cap t \subseteq s$ and $s \subseteq s \cup t$ from the definitions.
4. (B) Show that $\{n \in \mathbb{N} \mid n^2 < 10\} = \{0, 1, 2, 3\}$.
5. (B) Prove that $s \subseteq t$ if and only if $s \cap t = s$, and if and only if $s \cup t = t$.
6. (B) Prove $(s^{c})^{c} = s$. Say where the proof uses the excluded middle.
7. (C) The symmetric difference is $s \mathbin{\triangle} t = (s \setminus t) \cup (t \setminus s)$. Prove that it is associative. Hint: $x \in s \mathbin{\triangle} t$ holds exactly when the propositions $x \in s$ and $x \in t$ have different truth values.
8. (L) Prove that an element of both sets is in the intersection. The solution is `mem_inter_example` in `Solutions.lean`.
9. (L) Prove that a set is a subset of its union with another set. The solution is `subset_union_example` in `Solutions.lean`.

### Notes and history

Cantor introduced sets in the 1870s, and Zermelo gave the first axioms in 1908. The separation axiom of Zermelo, which forms $\{x \in s \mid p(x)\}$ only inside a given set $s$, is close to the Lean rule that a set lives inside an ambient type.

### Reference

<?reference?>
