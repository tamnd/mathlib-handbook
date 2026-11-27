---
title: Monotone functions and order maps
kind: theory
modules:
  - Mathlib.Order.Monotone.Defs
  - Mathlib.Order.Hom.Basic
explains:
  E3: [Monotone, OrderIso]
  E2: [StrictMono, Antitone, Monotone.comp, OrderHom, OrderEmbedding, StrictMono.injective]
  E1: [StrictMono.monotone, StrictMono.comp, MonotoneOn, monotone_id, StrictMono.lt_iff_lt, OrderIso.le_iff_le, OrderIso.symm, OrderHom.comp]
families: []
requires: [V04.C01]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V04/C02/Examples.lean
  - MathlibHandbook/V04/C02/Exercises.lean
  - MathlibHandbook/V04/C02/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Monotone functions and order maps

### Overview

A function $f$ between two preorders is monotone when $a \le b$ gives $f(a) \le f(b)$. Mathlib states this property as a predicate `Monotone f`, and it has the variants `StrictMono`, `Antitone` and `MonotoneOn`. A predicate is a proposition about a plain function. Mathlib also has bundled maps, which are structures that hold a function and a proof. The type `α →o β` holds monotone functions, `α ↪o β` holds order embeddings, and `α ≃o β` holds order isomorphisms. This section shows the predicates, the bundled maps, and when to use each of them.

### Definitions

**Definition (Monotone and antitone).** A function $f : \alpha \to \beta$ between preorders is monotone if $a \le b \Rightarrow f(a) \le f(b)$ for all $a$ and $b$. It is antitone if $a \le b \Rightarrow f(b) \le f(a)$.

**Definition (Strictly monotone).** The function $f$ is strictly monotone if $a < b \Rightarrow f(a) < f(b)$.

**Definition (Order homomorphism).** An order homomorphism `α →o β` is a structure with a function `toFun` and a proof `monotone'` that the function is monotone.

**Definition (Order embedding and order isomorphism).** An order embedding `α ↪o β` is an injective function with $f(a) \le f(b) \iff a \le b$. An order isomorphism `α ≃o β` is a bijection with the same property.

### Theorems and proofs

**Theorem (Composition).** If $f : \alpha \to \beta$ and $g : \beta \to \gamma$ are monotone, then $g \circ f$ is monotone.

*Proof.* Let $a \le b$. Then $f(a) \le f(b)$ because $f$ is monotone, and $g(f(a)) \le g(f(b))$ because $g$ is monotone. $\square$

**Theorem (Strict gives weak).** On a partial order, a strictly monotone function is monotone.

*Proof.* Let $a \le b$. If $a = b$, then $f(a) = f(b)$. If not, then $a < b$, so $f(a) < f(b)$ and $f(a) \le f(b)$. $\square$

**Theorem (Injectivity).** On a linear order, a strictly monotone function is injective.

*Proof.* Let $a \ne b$. By totality, $a < b$ or $b < a$. In the first case $f(a) < f(b)$, and in the second case $f(b) < f(a)$. In both cases $f(a) \ne f(b)$ by irreflexivity. $\square$

::: mathlib
`Monotone` · `Mathlib.Order.Monotone.Defs`

The predicate is a definition with the binders `⦃a b⦄`. So `hf h` is a proof of `f a ≤ f b` when `h : a ≤ b`, and the two points come from the type of `h`. The lemma `Monotone.comp` composes two monotone functions, in the order of `Function.comp`.

<?decl Monotone?>
:::

::: mathlib
`StrictMono.injective` · `Mathlib.Order.Monotone.Basic`

The lemma needs a linear order on the domain. The lemma `StrictMono.lt_iff_lt` gives the equivalence $f(a) < f(b) \iff a < b$ on the same hypothesis.

<?decl StrictMono.injective?>
:::

::: mathlib
`OrderIso` · `Mathlib.Order.Hom.Basic`

An order isomorphism is an `Equiv` with the field `map_rel_iff'`. The lemma `OrderIso.le_iff_le` states the field, and `OrderIso.symm` gives the inverse map, which is an order isomorphism too.

<?decl OrderIso?>
:::

### Examples

**Example (A monotone function).** The tactic `omega` proves the inequality after `dsimp only` removes the lambda.

<?lean MathlibHandbook/V04/C02/Examples.lean#monotone?>

**Example (A strictly monotone function).**

<?lean MathlibHandbook/V04/C02/Examples.lean#strictMono?>

**Example (An antitone function).** On `ℕ`, the subtraction is truncated, but the function is still antitone.

<?lean MathlibHandbook/V04/C02/Examples.lean#antitone?>

**Example (Composition).**

<?lean MathlibHandbook/V04/C02/Examples.lean#comp?>

**Example (Injectivity).**

<?lean MathlibHandbook/V04/C02/Examples.lean#injective?>

**Example (A bundled map).** A term of `ℕ →o ℕ` is a function, so it can take an argument, and `rfl` computes the value.

<?lean MathlibHandbook/V04/C02/Examples.lean#orderHom?>

**Example (An order isomorphism).**

<?lean MathlibHandbook/V04/C02/Examples.lean#orderIso?>

**Counterexample (Monotone and not strictly monotone).** A constant function is monotone, but it is not strictly monotone on `ℕ`, because $0 < 1$ and $f(0) = f(1)$.

### The library around it

Use the predicates when the function is a plain term, for example a function that a proof defines with `fun`. Use the bundled maps when the set of maps is an object of study, for example when the maps form a lattice or when a fixed point theorem takes a monotone map. The bundled types have a coercion to functions, and `OrderHom.monotone` gives the predicate back. The file `Mathlib.Order.Monotone.Basic` has more lemmas, for example the criteria for a function on `ℕ` or `ℤ` that compare each value with the next value. The tactic `gcongr` proves many goals of the form `f a ≤ f b` from `a ≤ b`, and it uses the lemmas with the attribute `@[gcongr]`. An order embedding is also a `RelEmbedding`, so the lemmas of `Mathlib.Order.RelIso.Basic` apply to it.

### Exercises

1. (A) Give a function from `ℤ` to `ℤ` that is antitone and not strictly antitone.
2. (A) Explain why `hf h` has the type `f a ≤ f b` when `hf : Monotone f` and `h : a ≤ b`.
3. (B) Show that the composition of two antitone functions is monotone.
4. (B) Show that a strictly monotone function $f : \mathbb{N} \to \mathbb{N}$ satisfies $n \le f(n)$ for each $n$.
5. (B) Show that an order isomorphism maps the least element to the least element.
6. (L) Prove that $n \mapsto n + 3$ is monotone on `ℕ`. The solution is `monotone_add_three`.
7. (L) Prove that the composition of two strictly monotone functions is strictly monotone. The solution is `strictMono_comp_example`.
8. (L) Prove that negation is antitone on `ℤ`. The solution is `antitone_neg_example`.

### Notes and history

The bundled maps follow the pattern of the morphisms in algebra, such as `MonoidHom`. Each type has a `FunLike` instance, so the maps coerce to functions, and the classes `OrderHomClass` and `OrderIsoClass` give lemmas for each bundled type at the same time.

### Reference

<?reference?>
