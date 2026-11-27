---
title: Subtypes, products and sums
kind: theory
modules:
  - Mathlib.Data.Subtype
  - Mathlib.Data.Prod.Basic
  - Mathlib.Data.Sum.Basic
  - Mathlib.Data.Sigma.Basic
explains:
  E3: [Subtype.val_injective, Prod.mk_inj]
  E2: [Subtype.coe_injective, Subtype.prop, Subtype.coe_mk, Sum.inl_injective, Sum.inr_injective, Sigma.mk.inj_iff, Sigma.forall, Prod.fst_surjective, Prod.swap_injective]
  E1: auto
families: []
requires: [V01.C01]
reads_with: ["TPIL", "MIL"]
lean:
  - MathlibHandbook/V01/C02/Examples.lean
  - MathlibHandbook/V01/C02/Exercises.lean
  - MathlibHandbook/V01/C02/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Subtypes, products and sums

### Overview

A set in Lean is not a type, but many constructions need a type. A function has a type as its domain, a group is a structure on a type, and a sum $\sum_{x} f(x)$ ranges over a type. This section gives the four ways to build new types from old ones: the subtype of the elements with a property, the product of two types, the sum (disjoint union) of two types, and the dependent pair type.

These constructions replace the set-theoretic constructions of a textbook. The set $\{x \in A \mid p(x)\}$ becomes a subtype. The Cartesian product $A \times B$ becomes a product type. The disjoint union $A \sqcup B$ becomes a sum type. The family of sets $\{(i, x) \mid i \in I,\ x \in A_i\}$ becomes a dependent pair type.

This section uses the word *injective* before Chapter 3 defines it: a function $f$ is injective when $f(a) = f(b)$ implies $a = b$.

### Definitions

**Definition (Subtype).** Let $p$ be a predicate on a type $\alpha$. The *subtype* $\{x : \alpha \mathrel{/\!/} p(x)\}$ is the type whose terms are the pairs $\langle a, h\rangle$ with $a : \alpha$ and $h : p(a)$. The *value* map $\mathrm{val}$ sends $\langle a, h\rangle$ to $a$. Lean inserts it as a coercion, written $\uparrow x$. The field $x.2$, also written `x.prop`, is a proof of $p(\uparrow x)$.

**Definition (Set as a type).** For a set $s$ in `Set α`, the type $\uparrow s$ is the subtype $\{x : \alpha \mathrel{/\!/} x \in s\}$. Lean inserts this coercion when a set appears where a type is needed, for example in `f : s → ℝ`.

**Definition (Product).** For types $\alpha$ and $\beta$, the *product* $\alpha \times \beta$ is the type of pairs $(a, b)$ with $a : \alpha$ and $b : \beta$. The projections are $\mathrm{fst}(a, b) = a$ and $\mathrm{snd}(a, b) = b$.

**Definition (Sum).** For types $\alpha$ and $\beta$, the *sum* $\alpha \oplus \beta$ has two constructors: $\mathrm{inl}(a)$ for $a : \alpha$ and $\mathrm{inr}(b)$ for $b : \beta$. A function out of $\alpha \oplus \beta$ is defined by cases: one value for each $\mathrm{inl}(a)$ and one for each $\mathrm{inr}(b)$.

**Definition (Dependent pairs).** For a type $\alpha$ and a family of types $\beta : \alpha \to \mathrm{Type}$, the *sigma type* $(a : \alpha) \times \beta(a)$ has as terms the pairs $\langle a, b\rangle$ with $a : \alpha$ and $b : \beta(a)$. The product is the case where $\beta$ is constant. The subtype is the analogue for a family of propositions.

The constructors of an inductive type are *injective* and *disjoint*: this is a rule of Lean's type theory. So $\mathrm{inl}(a) = \mathrm{inl}(a')$ implies $a = a'$, and $\mathrm{inl}(a) \neq \mathrm{inr}(b)$. The tactics `injection` and `cases` use this rule, and `simp` knows it.

### Theorems and proofs

**Theorem (Equality in a subtype).** Let $x, y$ be terms of $\{x : \alpha \mathrel{/\!/} p(x)\}$. If $\uparrow x = \uparrow y$, then $x = y$. So the value map is injective.

*Proof.* Write $x = \langle a, h\rangle$ and $y = \langle a', h'\rangle$. The hypothesis is $a = a'$. Substitute $a'$ by $a$. Then $h$ and $h'$ are both proofs of $p(a)$. By proof irrelevance, any two proofs of one proposition are equal, so $h = h'$. Hence $x = y$. $\square$

This theorem is the main reason that a subtype behaves like a subset. Two elements of the subtype are equal exactly when they are equal in $\alpha$. The proof part carries no information.

::: mathlib
`Subtype.val_injective` · `Mathlib.Data.Subtype`

The statement is `Function.Injective Subtype.val`. The tactic form is `Subtype.ext : (x : α) = y → x = y`, in the core library. A goal `x = y` for terms of a subtype usually starts with `ext` or `apply Subtype.ext`, and the new goal is an equation in `α`. The lemma `Subtype.coe_injective` is the same fact for the coercion.

<?decl Subtype.val_injective?>
:::

**Theorem (Equality of pairs).** For $a, a' : \alpha$ and $b, b' : \beta$:
$$(a, b) = (a', b') \iff a = a' \land b = b'.$$
Also, every $z : \alpha \times \beta$ is equal to $(\mathrm{fst}\ z, \mathrm{snd}\ z)$.

*Proof.* From left to right: apply $\mathrm{fst}$ to both sides. Then $\mathrm{fst}(a, b) = a$ and $\mathrm{fst}(a', b') = a'$, so $a = a'$. In the same way $\mathrm{snd}$ gives $b = b'$. From right to left: substitute $a'$ by $a$ and $b'$ by $b$, and use reflexivity. For the last claim, take cases on $z$: it is a pair $(a, b)$, and $(\mathrm{fst}(a, b), \mathrm{snd}(a, b)) = (a, b)$ by definition. $\square$

::: mathlib
`Prod.mk_inj` · `Mathlib.Data.Prod.Basic`

The statement is `(a₁, b₁) = (a₂, b₂) ↔ a₁ = a₂ ∧ b₁ = b₂`. It is a simp lemma. For a goal `z = w` with `z w : α × β`, the tactic `ext` produces the goals `z.1 = w.1` and `z.2 = w.2`.

<?decl Prod.mk_inj?>
:::

**Theorem (Projections).** If $\beta$ has an element, then $\mathrm{fst} : \alpha \times \beta \to \alpha$ is surjective: every $a$ is $\mathrm{fst}(z)$ for some $z$. If $\beta$ is empty, then $\alpha \times \beta$ is empty.

*Proof.* Let $b_0 : \beta$. For $a : \alpha$, the pair $(a, b_0)$ has $\mathrm{fst}(a, b_0) = a$. If $\beta$ is empty and $z : \alpha \times \beta$, then $\mathrm{snd}(z)$ is an element of $\beta$, which is impossible. $\square$

This is `Prod.fst_surjective`. Its hypothesis `[Nonempty β]` is needed by the second part.

**Theorem (Equality in a sum).** For $a, a' : \alpha$ and $b, b' : \beta$:

1. $\mathrm{inl}(a) = \mathrm{inl}(a') \iff a = a'$;
2. $\mathrm{inr}(b) = \mathrm{inr}(b') \iff b = b'$;
3. $\mathrm{inl}(a) \neq \mathrm{inr}(b)$.

*Proof.* For part 1, assume $\mathrm{inl}(a) = \mathrm{inl}(a')$. Define $g : \alpha \oplus \beta \to \alpha$ by cases: $g(\mathrm{inl}\ x) = x$ and $g(\mathrm{inr}\ y) = a$. Apply $g$ to both sides of the hypothesis. This gives $a = a'$. The converse holds by substitution. Part 2 is the same with the roles of $\alpha$ and $\beta$ exchanged.

For part 3, define $d : \alpha \oplus \beta \to \mathrm{Prop}$ by $d(\mathrm{inl}\ a) = \mathrm{True}$ and $d(\mathrm{inr}\ b) = \mathrm{False}$. If $\mathrm{inl}(a) = \mathrm{inr}(b)$, then $d(\mathrm{inl}\ a) = d(\mathrm{inr}\ b)$, so $\mathrm{True} = \mathrm{False}$. Since $\mathrm{True}$ holds, $\mathrm{False}$ holds. $\square$

The proof shows the general method: a function defined by cases separates the constructors. Lean's kernel uses the same method for every inductive type, and it gives the tactics `injection` and `cases` for free.

::: mathlib
`Sum.inl_injective` · `Mathlib.Data.Sum.Basic`

The statements are `Function.Injective Sum.inl` and `Function.Injective Sum.inr`. In a proof, `simp` closes `Sum.inl a = Sum.inr b` as `False`, and it rewrites `Sum.inl a = Sum.inl a'` to `a = a'`.

<?decl Sum.inl_injective?>
:::

**Theorem (Equality of dependent pairs).** For $\langle a, b\rangle$ and $\langle a', b'\rangle$ in $(a : \alpha) \times \beta(a)$, the pairs are equal if and only if $a = a'$ and $b$ equals $b'$ after the substitution of $a'$ by $a$.

*Proof.* From left to right, apply the first projection to get $a = a'$. After the substitution, both second components have the type $\beta(a)$, and the second projection gives $b = b'$. From right to left, substitute and use reflexivity. $\square$

The condition "after the substitution" is needed: before it, $b : \beta(a)$ and $b' : \beta(a')$ have different types, and an equation $b = b'$ is not even a valid statement. Lean writes the condition as *heterogeneous equality* `b ≍ b'`, which allows two sides of different types.

::: mathlib
`Sigma.mk.inj_iff` · `Mathlib.Data.Sigma.Basic`

The statement is `⟨a₁, b₁⟩ = ⟨a₂, b₂⟩ ↔ a₁ = a₂ ∧ b₁ ≍ b₂`. Heterogeneous equality is hard to use. In practice a proof first proves `a₁ = a₂`, then uses `subst` or `cases` so that the two types agree, and then proves an ordinary equation.

<?decl Sigma.mk.inj_iff?>
:::

### Examples

**Example (An element of a subtype).** The pair of $4$ and a proof that $4$ is even is a term of the subtype of even natural numbers. Its value is $4$, by definition. The proof part comes from `decide`, since evenness on $\mathbb{N}$ is decidable.

<?lean MathlibHandbook/V01/C02/Examples.lean#subtype?>

**Example (A function on a set).** Let $s = \{x : \mathbb{R} \mid x \neq 0\}$. The function $x \mapsto 1/x$ on $s$ has the type $\uparrow s \to \mathbb{R}$, and it is written `fun x : s => 1 / (x : ℝ)`. Each argument comes with a proof that it is nonzero, so a proof about the function can use `x.2 : (x : ℝ) ≠ 0`. Chapter 5 shows the other approach of Mathlib: define $1/x$ on all of $\mathbb{R}$ with the value $0$ at $0$.

**Example (Swapping the factors).** The function $\mathrm{swap}(a, b) = (b, a)$ from $\alpha \times \beta$ to $\beta \times \alpha$ is injective. If $(b, a) = (b', a')$, then $b = b'$ and $a = a'$ by the theorem on pairs, so $(a, b) = (a', b')$. The function is its own inverse when $\alpha = \beta$. This is `Prod.swap_injective`.

**Example (A sum type as a disjoint union).** The type $\mathrm{Bool} \oplus \mathrm{Bool}$ has four elements: $\mathrm{inl}\ \mathrm{true}$, $\mathrm{inl}\ \mathrm{false}$, $\mathrm{inr}\ \mathrm{true}$ and $\mathrm{inr}\ \mathrm{false}$. They are distinct by the theorem on sums. The set union $\{\mathrm{true}, \mathrm{false}\} \cup \{\mathrm{true}, \mathrm{false}\}$ has only two elements. The sum type keeps the two copies apart, and the union does not.

**Example (A family of types).** Let $\beta(n) = \mathrm{Fin}\ n$ for $n : \mathbb{N}$, the type of numbers below $n$. The sigma type $(n : \mathbb{N}) \times \mathrm{Fin}\ n$ has as terms the pairs $\langle n, k\rangle$ with $k < n$. A statement for all such pairs reduces to a statement for all $n$ and all $k : \mathrm{Fin}\ n$, by `Sigma.forall`.

**Counterexample (Subtypes of different predicates).** The subtypes $\{n : \mathbb{N} \mathrel{/\!/} n < 3\}$ and $\{n : \mathbb{N} \mathrel{/\!/} n \leq 2\}$ have the same elements in $\mathbb{N}$, but they are different types, and a term of one is not a term of the other. The predicates are equal by propositional extensionality, so the types are equal, but a rewrite along this equation is hard to use. The correct tool is an equivalence of types, `Equiv.subtypeEquivRight`, from Chapter 3.

### The library around it

The module `Mathlib.Data.Subtype` has the basic lemmas: `Subtype.val_injective`, `Subtype.coe_injective`, `Subtype.coe_mk` and `Subtype.prop`. The core library has `Subtype.ext`, `Subtype.forall` and `Subtype.exists`. The coercion from sets to types is `Set.Elem`, in `Mathlib.Data.Set.CoeSort`. For an inclusion $s \subseteq t$, the map `Set.inclusion h : s → t` sends an element of $s$ to the same element as an element of $t$, and `Set.inclusion_injective` states that it is injective.

The modules `Mathlib.Data.Prod.Basic`, `Mathlib.Data.Sum.Basic` and `Mathlib.Data.Sigma.Basic` have the lemmas for products, sums and dependent pairs. The function `Sum.elim f g : α ⊕ β → γ` is the definition by cases. The notation `α × β` is `Prod α β`, `α ⊕ β` is `Sum α β`, and `(a : α) × β a` is `Sigma β`.

#### Common errors

1. A learner writes `x ∈ s` for `x : s`. The term `x` already has the type `↑s`. Use `(x : α) ∈ s` or `x.2`.
2. A learner proves `x = y` in a subtype with `rfl` and fails. Use `Subtype.ext` and prove `(x : α) = y`.
3. A learner tries to state `b₁ = b₂` for the second components of two dependent pairs with different first components. The statement does not typecheck. Prove the first components equal and substitute first.
4. A learner uses a subtype where a set suffices. If the collection is not the domain of a function or the carrier of a structure, a set is easier to use.

### Exercises

1. (A) Write the subtype of positive real numbers, and give one term of it.
2. (A) Prove that $\mathrm{swap} \circ \mathrm{swap}$ is the identity on $\alpha \times \beta$.
3. (A) Prove that $\mathrm{inr}(b) \neq \mathrm{inl}(a)$ for all $a$ and $b$.
4. (B) Let $s \subseteq t$ be sets. Prove that the inclusion map $\uparrow s \to \uparrow t$ is injective.
5. (B) Prove that a function $\alpha \oplus \beta \to \gamma$ is the same as a pair of functions $\alpha \to \gamma$ and $\beta \to \gamma$: the map $h \mapsto (h \circ \mathrm{inl}, h \circ \mathrm{inr})$ is a bijection.
6. (B) Prove that $\alpha \times \beta$ and $\beta \times \alpha$ have the same number of elements when both are finite.
7. (C) Prove that a function $\gamma \to \alpha \times \beta$ is the same as a pair of functions $\gamma \to \alpha$ and $\gamma \to \beta$. Compare with Exercise 5, and explain in which sense products and sums are dual.
8. (C) Show that $(n : \mathbb{N}) \times \mathrm{Fin}\ n$ and $\{(n, k) : \mathbb{N} \times \mathbb{N} \mid k < n\}$ are in bijection.

### Notes and history

The Cartesian product is named after Descartes, whose coordinates identify the plane with pairs of numbers. The disjoint union and the dependent sum come from category theory and from Martin-Löf type theory (1972), where the sigma type is the basic form of an existential statement with a witness.

### Reference

<?reference?>
