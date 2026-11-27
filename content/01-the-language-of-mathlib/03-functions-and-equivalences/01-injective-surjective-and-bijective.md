---
title: Injective, surjective and bijective functions
kind: theory
modules:
  - Mathlib.Logic.Function.Basic
explains:
  E3: [Function.bijective_iff_has_inverse, Function.injective_iff_hasLeftInverse]
  E2: [Function.Bijective, Function.surjective_iff_hasRightInverse, Function.invFun, Function.leftInverse_invFun, Function.surjInv, Function.rightInverse_surjInv, Function.Surjective.of_comp, Function.Injective.of_comp, Function.Bijective.comp, Function.Involutive, Function.Involutive.injective]
  E1: auto
families: []
requires: [V01.C02]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V01/C03/Examples.lean
  - MathlibHandbook/V01/C03/Exercises.lean
  - MathlibHandbook/V01/C03/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Injective, surjective and bijective functions

### Overview

A function $f : \alpha \to \beta$ can lose information in two ways. It can send two different inputs to one output, and then the input cannot be recovered from the output. It can miss some outputs, and then some elements of $\beta$ have no input. A function that loses no information in the first sense is *injective*. A function that misses no output is *surjective*. A function with both properties is *bijective*, and it matches the elements of $\alpha$ and $\beta$ one to one.

This section proves the standard facts about these three properties: their behaviour under composition, and their characterization by inverses. An injective function has a left inverse, a surjective function has a right inverse, and a bijective function has a two-sided inverse. The second and the third facts need the axiom of choice in general, and the first needs that the domain is nonempty. The section shows where each hypothesis enters.

In Lean, a function is a term of the type `α → β`. Its domain is the whole type $\alpha$, and its codomain is the whole type $\beta$. So "injective" and "surjective" always refer to these types.

### Definitions

**Definition (Injective, surjective, bijective).** Let $f : \alpha \to \beta$.

1. $f$ is *injective* when $\forall a\ b,\ f(a) = f(b) \to a = b$.
2. $f$ is *surjective* when $\forall b,\ \exists a,\ f(a) = b$.
3. $f$ is *bijective* when it is injective and surjective.

The contrapositive of injectivity is often easier to check: $a \neq b \to f(a) \neq f(b)$.

**Definition (Composition and identity).** For $f : \alpha \to \beta$ and $g : \beta \to \gamma$, the *composite* $g \circ f : \alpha \to \gamma$ is $x \mapsto g(f(x))$. The *identity* $\mathrm{id} : \alpha \to \alpha$ is $x \mapsto x$. Two functions are equal when they agree at every point, by function extensionality.

**Definition (Inverses).** Let $f : \alpha \to \beta$ and $g : \beta \to \alpha$.

1. $g$ is a *left inverse* of $f$ when $g(f(a)) = a$ for every $a$, that is, $g \circ f = \mathrm{id}$.
2. $g$ is a *right inverse* of $f$ when $f(g(b)) = b$ for every $b$, that is, $f \circ g = \mathrm{id}$.
3. $g$ is a *two-sided inverse* of $f$ when it is both.

The two notions are dual: $g$ is a left inverse of $f$ exactly when $f$ is a right inverse of $g$.

::: mathlib
`Function.Bijective` · `Mathlib.Logic.Function.Defs`

The core library defines `Function.Injective` and `Function.Surjective` as in the definition. Mathlib defines `Function.Bijective f` as `Injective f ∧ Surjective f`, and `Function.LeftInverse g f` as `∀ x, g (f x) = x`. In `Function.LeftInverse g f`, the left inverse comes first. `Function.RightInverse g f` means `Function.LeftInverse f g`.

<?decl Function.Bijective?>
:::

**Definition (Involution).** A function $f : \alpha \to \alpha$ is an *involution* when $f(f(a)) = a$ for every $a$, that is, $f$ is its own two-sided inverse.

### Theorems and proofs

**Theorem (Composition).** Let $f : \alpha \to \beta$ and $g : \beta \to \gamma$.

1. If $f$ and $g$ are injective, then $g \circ f$ is injective.
2. If $f$ and $g$ are surjective, then $g \circ f$ is surjective.
3. If $f$ and $g$ are bijective, then $g \circ f$ is bijective.

*Proof.* 1. Let $g(f(a)) = g(f(a'))$. Injectivity of $g$ gives $f(a) = f(a')$. Injectivity of $f$ gives $a = a'$.

2. Let $c : \gamma$. Surjectivity of $g$ gives $b$ with $g(b) = c$. Surjectivity of $f$ gives $a$ with $f(a) = b$. Then $g(f(a)) = g(b) = c$.

3. Combine parts 1 and 2. $\square$

**Theorem (Cancellation).** Let $f : \alpha \to \beta$ and $g : \beta \to \gamma$.

1. If $g \circ f$ is injective, then $f$ is injective.
2. If $g \circ f$ is surjective, then $g$ is surjective.

*Proof.* 1. Let $f(a) = f(a')$. Apply $g$: $g(f(a)) = g(f(a'))$. Injectivity of $g \circ f$ gives $a = a'$.

2. Let $c : \gamma$. There is $a$ with $g(f(a)) = c$. So $b = f(a)$ is a witness for $\exists b,\ g(b) = c$. $\square$

The converse statements fail. In part 1, $g$ need not be injective, and in part 2, $f$ need not be surjective. The counterexample in the examples shows both.

::: mathlib
`Function.Injective.of_comp` · `Mathlib.Logic.Function.Basic`

The statement is `Injective (f ∘ g) → Injective g`. Note the letters: in Mathlib the inner function is `g`. The dual is `Function.Surjective.of_comp : Surjective (f ∘ g) → Surjective f`. The composition lemmas are `Function.Injective.comp`, in the core library, and `Function.Bijective.comp`.

<?decl Function.Injective.of_comp?>
:::

**Theorem (Inverses give injectivity and surjectivity).** Let $f : \alpha \to \beta$ and $g : \beta \to \alpha$.

1. If $g$ is a left inverse of $f$, then $f$ is injective and $g$ is surjective.
2. If $g$ is a right inverse of $f$, then $f$ is surjective and $g$ is injective.

*Proof.* 1. The composite $g \circ f = \mathrm{id}$ is injective and surjective. By cancellation, $f$ is injective and $g$ is surjective. 2. This is part 1 with the roles of $f$ and $g$ exchanged. $\square$

**Theorem (Injective maps have left inverses).** Let $f : \alpha \to \beta$, and let $\alpha$ have an element. Then $f$ is injective if and only if $f$ has a left inverse.

*Proof.* If $f$ has a left inverse, then $f$ is injective by the previous theorem.

Conversely, let $f$ be injective, and fix $a_0 : \alpha$. Define $g : \beta \to \alpha$ as follows. For $b : \beta$, if $\exists a,\ f(a) = b$, let $g(b)$ be an $a$ with $f(a) = b$, chosen by the axiom of choice. Otherwise, let $g(b) = a_0$. The case distinction uses the excluded middle.

Let $a : \alpha$ and $b = f(a)$. Then $\exists a',\ f(a') = b$ holds with the witness $a$, so $g(b)$ is an element $a'$ with $f(a') = b = f(a)$. Injectivity gives $a' = a$. So $g(f(a)) = a$. $\square$

The hypothesis that $\alpha$ has an element is necessary. If $\alpha$ is empty and $\beta$ is not, then the unique function $\alpha \to \beta$ is injective, since there is nothing to check, but no function $\beta \to \alpha$ exists.

::: mathlib
`Function.injective_iff_hasLeftInverse` · `Mathlib.Logic.Function.Basic`

The statement has the hypothesis `[Nonempty α]`, as in the theorem. The left inverse of the proof is `Function.invFun f`, and `Function.leftInverse_invFun` states that it is a left inverse when `f` is injective. The definition `Function.invFun` is noncomputable, because it uses choice.

<?decl Function.injective_iff_hasLeftInverse?>
:::

**Theorem (Surjective maps have right inverses).** Let $f : \alpha \to \beta$. Then $f$ is surjective if and only if $f$ has a right inverse.

*Proof.* If $f$ has a right inverse, then $f$ is surjective by the theorem on inverses.

Conversely, let $f$ be surjective. For each $b : \beta$ the statement $\exists a,\ f(a) = b$ holds. By the axiom of choice (Section 3 of Chapter 1), there is a function $g : \beta \to \alpha$ with $f(g(b)) = b$ for every $b$. This $g$ is a right inverse. $\square$

This theorem is equivalent to the axiom of choice in set theory: given a family of nonempty sets $A_i$, the projection from $\{(i, x) \mid x \in A_i\}$ to the index set is surjective, and a right inverse picks an element of each $A_i$.

::: mathlib
`Function.surjective_iff_hasRightInverse` · `Mathlib.Logic.Function.Basic`

The right inverse is `Function.surjInv hf`, where `hf` is the proof of surjectivity. The lemma `Function.rightInverse_surjInv hf` states that it is a right inverse. The lemma `Function.surjInv_eq` gives the equation `f (surjInv hf b) = b`, which is often more convenient.

<?decl Function.surjective_iff_hasRightInverse?>
:::

**Theorem (Bijective maps have inverses).** Let $f : \alpha \to \beta$. Then $f$ is bijective if and only if there is $g : \beta \to \alpha$ that is a two-sided inverse of $f$. Such a $g$ is unique.

*Proof.* If $g$ is a two-sided inverse, then $f$ is injective and surjective by the theorem on inverses.

Conversely, let $f$ be bijective. By the previous theorem, $f$ has a right inverse $g$, with $f(g(b)) = b$. To show that $g$ is also a left inverse, let $a : \alpha$. Then $f(g(f(a))) = f(a)$, by the right inverse property at $b = f(a)$. Injectivity of $f$ gives $g(f(a)) = a$.

For uniqueness, let $g$ and $h$ be two-sided inverses. For $b : \beta$:
$$g(b) = g(f(h(b))) = h(b),$$
where the first step uses $f \circ h = \mathrm{id}$ and the second uses $g \circ f = \mathrm{id}$. $\square$

The uniqueness proof used only that $g$ is a left inverse and that $h$ is a right inverse. So if $f$ has a left inverse and a right inverse, they are equal, and $f$ is bijective.

::: mathlib
`Function.bijective_iff_has_inverse` · `Mathlib.Logic.Function.Basic`

The statement is `Bijective f ↔ ∃ g, LeftInverse g f ∧ RightInverse g f`. The next section packs a function and its two-sided inverse into one structure, an equivalence `α ≃ β`. An equivalence stores the inverse, so it needs no choice, and its inverse can be computed when the inverse is given explicitly.

<?decl Function.bijective_iff_has_inverse?>
:::

**Theorem (Involutions are bijective).** An involution $f : \alpha \to \alpha$ is bijective.

*Proof.* $f$ is a two-sided inverse of itself. Apply the previous theorem. $\square$

### Examples

**Example (Composite of injective maps).** The proof of part 1 of the composition theorem is a single term in Lean: `hg.comp hf`. The dot notation finds `Function.Injective.comp` from the type of `hg`.

<?lean MathlibHandbook/V01/C03/Examples.lean#injective_comp?>

**Example (Doubling on the natural numbers).** The map $d(n) = 2n$ on $\mathbb{N}$ is injective: if $2a = 2b$, then $a = b$, by cancellation of the nonzero factor $2$. It is not surjective: an $n$ with $2n = 1$ would make $1$ even. The tactic `omega` proves both facts about linear arithmetic.

<?lean MathlibHandbook/V01/C03/Examples.lean#double_injective?>

<?lean MathlibHandbook/V01/C03/Examples.lean#double_not_surjective?>

**Example (A left inverse in Lean).** The map $n \mapsto n + 3$ on $\mathbb{N}$ has the left inverse $m \mapsto m - 3$, with truncated subtraction: $(n + 3) - 3 = n$. So it is injective.

<?lean MathlibHandbook/V01/C03/Examples.lean#leftInverse?>

**Example (An involution).** Negation $x \mapsto -x$ on $\mathbb{Z}$ is an involution, since $-(-x) = x$. So it is bijective, by the theorem on involutions. Complement $s \mapsto s^{c}$ on `Set α` is another involution, by the double complement law.

**Counterexample (Cancellation is one-sided).** Let $f : \{0\} \to \mathbb{N}$ be $f(0) = 0$, and let $g : \mathbb{N} \to \{0\}$ be the constant map. Then $g \circ f = \mathrm{id}$ on $\{0\}$, so $g \circ f$ is bijective. The function $f$ is injective, as the cancellation theorem says, but it is not surjective. The function $g$ is surjective, but it is not injective, since $g(1) = g(2)$. So the cancellation theorem cannot be strengthened.

### The library around it

The core library defines `Function.Injective`, `Function.Surjective`, `Function.comp`, `Function.LeftInverse` and `Function.RightInverse`, with the basic lemmas `Function.Injective.comp`, `Function.Surjective.comp`, `Function.injective_id` and `Function.surjective_id`. The module `Mathlib.Logic.Function.Defs` adds `Function.Bijective` and `Function.Bijective.comp`. The module `Mathlib.Logic.Function.Basic` has the theorems of this section, the choice-based inverses `Function.invFun` and `Function.surjInv`, and many smaller facts. Among them are `Function.Injective.comp_left`, for composition on the left, and `Function.Surjective.forall`, which turns `∀ y, p y` into `∀ x, p (f x)` when `f` is surjective.

A proof of injectivity in Lean starts with `intro a b h`. The hypothesis `h` is `f a = f b`, often in a beta-unreduced form such as `(fun n => 2 * n) a = (fun n => 2 * n) b`. The tactic `simp only at h` reduces it. A proof of surjectivity starts with `intro b` and then gives the witness with `use` or `refine ⟨_, ?_⟩`.

#### Common errors

1. A learner forgets the hypothesis `[Nonempty α]` of `Function.injective_iff_hasLeftInverse` and gets an instance error. Supply an element, for example with `haveI : Nonempty α := ⟨a⟩`.
2. A learner reads `Function.LeftInverse g f` as "f is a left inverse of g". It means `∀ x, g (f x) = x`.
3. A learner states surjectivity onto a set by `Surjective f` with `f : α → β`. Surjectivity is onto the whole type `β`. For a set `s`, the statement is `Set.SurjOn f univ s` or `s ⊆ Set.range f`.

### Exercises

1. (A) Decide which of these maps are injective, surjective or bijective, with proofs: $n \mapsto n + 1$ on $\mathbb{N}$; $n \mapsto n + 1$ on $\mathbb{Z}$; $x \mapsto x^2$ on $\mathbb{R}$; $x \mapsto x^3$ on $\mathbb{R}$.
2. (A) Prove that the identity map is bijective.
3. (B) Let $f : \alpha \to \beta$ and $g : \beta \to \gamma$. Prove that if $g \circ f$ is injective and $f$ is surjective, then $g$ is injective.
4. (B) Find all left inverses of $f : \{0, 1\} \to \{0, 1, 2\}$ with $f(0) = 0$ and $f(1) = 2$. How many are there?
5. (B) Prove that if $f : \alpha \to \beta$ has a left inverse $g$ and a right inverse $h$, then $g = h$.
6. (B) Prove that $f$ is injective if and only if $f \circ u = f \circ v$ implies $u = v$ for all $u, v : \gamma \to \alpha$ and every type $\gamma$. Hint: for one direction, take $\gamma$ with one element.
7. (C) Let $\alpha$ be finite, and let $f : \alpha \to \alpha$. Prove that $f$ is injective if and only if $f$ is surjective. Give a counterexample on $\mathbb{N}$.
8. (L) Prove that $n \mapsto n + 1$ is injective on $\mathbb{N}$. The solution is `injective_add_one` in `Solutions.lean`.
9. (L) Prove that the identity map on $\mathbb{N}$ is surjective. The solution is `surjective_id_example` in `Solutions.lean`.

### Notes and history

The words *injection*, *surjection* and *bijection* come from the Bourbaki group, in the first volume of the *Éléments de mathématique* on set theory (1954). The equivalence between "every surjection has a right inverse" and the axiom of choice is a standard fact of set theory, and it explains why `Function.surjInv` is noncomputable.

### Reference

<?reference?>
