---
title: Bundled maps and coercions
kind: theory
modules:
  - Mathlib.Basic.FunLike.Basic
  - Mathlib.Basic.FunLike.Embedding
  - Mathlib.Basic.FunLike.Equiv
  - Mathlib.Data.FunLike.Fintype
  - Mathlib.Data.FunLike.Basic
  - Mathlib.Data.FunLike.Embedding
  - Mathlib.Data.FunLike.Equiv
  - Mathlib.Data.FunLike.Graded
  - Mathlib.Data.FunLike.Group
  - Mathlib.Data.FunLike.IsApply
  - Mathlib.Data.FunLike.Module
  - Mathlib.Data.FunLike.Ring
explains:
  E3: [DFunLike]
  E2: [DFunLike.ext, DFunLike.coe_injective, DFunLike.congr_fun, DFunLike.congr_arg, DFunLike.ext_iff, FunLike, EquivLike, EmbeddingLike, EmbeddingLike.injective]
  E1: auto
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

## Bundled maps and coercions

### Overview

A ring homomorphism $f : R \to S$ is a function with properties: $f(a + b) = f(a) + f(b)$, $f(ab) = f(a) f(b)$, $f(0) = 0$ and $f(1) = 1$. Mathlib stores such a map as a structure, a *bundled map*, that contains the function and the proofs of the properties. The type `R →+* S` is the type of ring homomorphisms. A term of it is not a function, but Lean lets it act as one through a *coercion*.

This section explains the coercion to functions, the class `DFunLike` that provides it for every kind of bundled map, and the lemmas that hold for all bundled maps at once: two maps are equal when they agree at each point, and the map `f ↦ ⇑f` is injective. It also explains the coercions between number types, such as $\mathbb{N} \to \mathbb{Z} \to \mathbb{Q}$, and the tactics `push_cast` and `exact_mod_cast` that handle them.

### Definitions

**Definition (Bundled homomorphism).** For monoids $M$ and $N$, a *monoid homomorphism* $M \to^{*} N$ is a structure with a function $f : M \to N$ and proofs of $f(1) = 1$ and $f(ab) = f(a) f(b)$. For semirings $R$ and $S$, a *ring homomorphism* $R \to^{+*} S$ is a structure with a function and proofs of the four laws for $0$, $1$, addition and multiplication. The other kinds follow the same pattern: additive homomorphisms `M →+ N`, linear maps `M →ₗ[R] N`, order homomorphisms `α →o β`, continuous maps `C(X, Y)`.

**Definition (Coercion to functions).** A *coercion* is a function that Lean inserts by itself when a term of one type appears where a term of another type is expected. For a bundled map $f$, the term $f(a)$ means $\Uparrow\! f\,(a)$, where $\Uparrow\! f$ is the underlying function. Lean prints the coercion as `⇑f`.

**Definition (DFunLike).** For a type $F$ and types $\alpha$ and $\beta(a)$, the class `DFunLike F α β` states that the terms of $F$ act as dependent functions $(a : \alpha) \to \beta(a)$. It has two fields: the coercion $\mathrm{coe} : F \to ((a : \alpha) \to \beta(a))$, and a proof that $\mathrm{coe}$ is injective. The class `FunLike F α β` is the case of a constant $\beta$.

The injectivity field says: a bundled map is determined by its function. The proofs of the laws carry no extra information, by proof irrelevance, so this is true for every kind of bundled map, and each instance proves it once.

::: mathlib
`DFunLike` · `Mathlib.Basic.FunLike.Basic`

The class has the fields `coe : F → ∀ a, β a` and `coe_injective'`. Every type of bundled maps in Mathlib has an instance of `FunLike`. The classes `EmbeddingLike` and `EquivLike` extend it for injective maps and for maps with an inverse. So `Equiv α β` has an `EquivLike` instance, and an equivalence acts as a function by the same coercion.

<?decl DFunLike?>
:::

**Definition (Hom classes).** A *hom class* is a class on a type $F$ of bundled maps that states a property of all its terms. For example `AddMonoidHomClass F M N` states that every $f : F$ preserves $0$ and addition. A lemma stated for a hom class applies to every type of maps with an instance. The lemma `map_add` is stated for all $F$ with an additive hom class, so it applies to additive homomorphisms, ring homomorphisms, linear maps and ring isomorphisms.

**Definition (Casts).** For a semiring $R$, the *cast* $\mathbb{N} \to R$ sends $n$ to $1 + \cdots + 1$, with $n$ terms. It is a coercion, written $(n : R)$ or $\uparrow n$. For a ring $R$, the cast $\mathbb{Z} \to R$ sends $n \geq 0$ to the cast of $n$ and $-n$ to the negation. For a field of characteristic $0$, there is a cast from $\mathbb{Q}$.

### Theorems and proofs

**Theorem (Extensionality of bundled maps).** Let $F$ have a `DFunLike` instance, and let $f, g : F$. If $f(a) = g(a)$ for every $a$, then $f = g$.

*Proof.* By function extensionality, $\Uparrow\! f = \Uparrow\! g$. The coercion is injective by the field of the class. So $f = g$. $\square$

::: mathlib
`DFunLike.ext` · `Mathlib.Basic.FunLike.Basic`

The statement is `(∀ x, f x = g x) → f = g`. Each type of maps has its own copy with the `@[ext]` attribute, for example `RingHom.ext` and `MonoidHom.ext`, so the tactic `ext x` works on a goal `f = g`. The converse is `DFunLike.congr_fun : f = g → ∀ x, f x = g x`, and `DFunLike.ext_iff` gives both.

<?decl DFunLike.ext?>
:::

**Theorem (Additive maps preserve zero and negation).** Let $G$ and $H$ be additive groups and $f : G \to H$ a function with $f(a + b) = f(a) + f(b)$ for all $a, b$. Then $f(0) = 0$, $f(-a) = -f(a)$ and $f(a - b) = f(a) - f(b)$.

*Proof.* From $f(0) = f(0 + 0) = f(0) + f(0)$, add $-f(0)$ to both sides: $0 = f(0)$. Then $f(a) + f(-a) = f(a + (-a)) = f(0) = 0$. In a group, an element $y$ with $x + y = 0$ is the inverse of $x$: add $-x$ on the left to get $y = -x$. So $f(-a) = -f(a)$. Finally, $f(a - b) = f(a + (-b)) = f(a) + f(-b) = f(a) - f(b)$. $\square$

So for groups, a map that preserves addition is already an additive homomorphism. For monoids this fails, and the structure `M →+ N` asks for $f(0) = 0$ separately. In Mathlib the lemmas are `map_zero`, `map_neg` and `map_sub`.

**Theorem (Ring homomorphisms from the integers).** Let $R$ be a ring. There is exactly one ring homomorphism $\mathbb{Z} \to R$, namely the cast.

*Proof.* *Uniqueness.* Let $f, g : \mathbb{Z} \to R$ be ring homomorphisms. By extensionality, it suffices to show $f(n) = g(n)$ for every $n$. For $n \geq 0$, use induction. $f(0) = 0 = g(0)$. If $f(n) = g(n)$, then $f(n + 1) = f(n) + f(1) = g(n) + 1 = g(n) + g(1) = g(n + 1)$. For $n < 0$, write $n = -m$ with $m > 0$. Then $f(n) = -f(m) = -g(m) = g(n)$ by the previous theorem.

*Existence.* The cast preserves $0$, $1$, addition and multiplication. The proofs are inductions of the same kind, with the definition of the cast, and Mathlib packs them as `Int.castRingHom R`. $\square$

The proof uses only that $\mathbb{Z}$ is generated by $1$ under addition and negation. The same argument gives that a ring homomorphism from $\mathbb{Q}$ to a field is unique, because a homomorphism must send $a/b$ to $f(a)/f(b)$.

::: mathlib
`DFunLike.coe_injective` · `Mathlib.Basic.FunLike.Basic`

The statement is `Function.Injective (fun f : F => (f : ∀ a, β a))`. It is the field of the class, and it is the basis of all the extensionality lemmas. The uniqueness of a ring homomorphism from `ℤ` is `RingHom.ext_int`, in `Mathlib.Data.Int.Cast.Lemmas`. Volume 2 treats the casts in detail.

<?decl DFunLike.coe_injective?>
:::

**Theorem (Injectivity of the cast).** The cast $\mathbb{N} \to \mathbb{Z}$ is injective, and it preserves and reflects the order: $(m : \mathbb{Z}) \leq (n : \mathbb{Z}) \iff m \leq n$.

*Proof.* The cast sends $n$ to the nonnegative integer $n$. The integers are built so that the nonnegative integers are a copy of $\mathbb{N}$: the constructor `Int.ofNat` is the cast, and constructors are injective. The order on $\mathbb{Z}$ is defined by $a \leq b \iff b - a$ is a cast of a natural number. For $m, n : \mathbb{N}$, $(n : \mathbb{Z}) - (m : \mathbb{Z})$ is the cast of a natural number exactly when $m \leq n$, and then it is the cast of $n - m$. $\square$

The tactic `exact_mod_cast` uses such lemmas, tagged `@[norm_cast]`. It moves the casts in the hypothesis and the goal to the same place, and then compares.

### Examples

**Example (A ring homomorphism preserves addition).** For `f : ℤ →+* ℚ`, the lemma `map_add` gives `f (a + b) = f a + f b`. The lemma is stated for every type with `AddHomClass`, and the search finds the instance for `RingHom`.

<?lean MathlibHandbook/V01/C04/Examples.lean#map_add?>

**Example (A ring homomorphism preserves one).** In the same way `map_one` uses the instance `RingHomClass` and its parent `OneHomClass`.

<?lean MathlibHandbook/V01/C04/Examples.lean#map_one?>

**Example (Moving a cast).** The equation $\uparrow(n + 1) = \uparrow n + 1$ in $\mathbb{Z}$ holds because the cast preserves addition and $1$. The tactic `push_cast` rewrites the left side with `Nat.cast_add` and `Nat.cast_one`, from the outside in.

<?lean MathlibHandbook/V01/C04/Examples.lean#push_cast?>

**Example (Removing a cast).** From `(a : ℤ) = b`, the injectivity of the cast gives `a = b` in `ℕ`. The tactic `exact_mod_cast` finds the lemma `Nat.cast_inj` by itself.

<?lean MathlibHandbook/V01/C04/Examples.lean#exact_mod_cast?>

**Example (An equivalence as a function).** For `e : ℕ ≃ ℕ`, the term `e 3` is a natural number. The coercion comes from the instance `Equiv.instEquivLike` and its parent `FunLike`. The lemma `DFunLike.ext` applies to equivalences, and `Equiv.ext` is the copy for equivalences.

**Counterexample (Subtraction and the cast).** The cast does not preserve truncated subtraction. In $\mathbb{N}$, $2 - 5 = 0$, so $\uparrow(2 - 5) = 0$ in $\mathbb{Z}$. But $\uparrow 2 - \uparrow 5 = -3$. The lemma `Nat.cast_sub` has the hypothesis $m \leq n$, and `push_cast` moves the cast past a subtraction only when it can prove this hypothesis.

### The library around it

The module `Mathlib.Basic.FunLike.Basic` defines `DFunLike`, `FunLike` and the general lemmas. The modules `Mathlib.Basic.FunLike.Embedding` and `Mathlib.Basic.FunLike.Equiv` define `EmbeddingLike` and `EquivLike`. The homomorphisms of algebra are in `Mathlib.Algebra.Group.Hom.Defs` and `Mathlib.Algebra.Ring.Hom.Defs`, with the hom classes `MonoidHomClass`, `AddMonoidHomClass` and `RingHomClass`, and the lemmas `map_add`, `map_zero`, `map_neg`, `map_sub`, `map_mul` and `map_one`.

The module `Mathlib.Data.FunLike.Fintype` shows that a type of bundled maps between finite types is finite. The lemma `DFunLike.finite` states that `F` is `Finite` when `α` and each `β a` are finite, and `FunLike.finite` is the form for a fixed codomain. The proof is one line: the coercion `F → (a : α) → β a` is injective by `DFunLike.coe_injective`, and a type that injects into a finite type is finite. The definitions `DFunLike.fintype` and `FunLike.fintype` give a `Fintype` structure in the same way. They are definitions and not instances, so a file uses them to build the instance for one kind of map. The other modules `Mathlib.Data.FunLike.Basic`, `Mathlib.Data.FunLike.Embedding`, `Mathlib.Data.FunLike.Equiv`, `Mathlib.Data.FunLike.Graded`, `Mathlib.Data.FunLike.Group`, `Mathlib.Data.FunLike.IsApply`, `Mathlib.Data.FunLike.Module` and `Mathlib.Data.FunLike.Ring` have no live declarations: they only import the modules that now hold the same material.

The casts are in `Mathlib.Data.Nat.Cast.Defs`, `Mathlib.Data.Nat.Cast.Basic` and `Mathlib.Data.Int.Cast.Lemmas`. Their names follow a pattern: `Nat.cast_add`, `Nat.cast_mul`, `Nat.cast_one`, `Nat.cast_zero`, `Nat.cast_inj`, `Nat.cast_le` and `Int.cast_add`. The ring homomorphism that the cast defines is `Nat.castRingHom` or `Int.castRingHom`, and `map_natCast` states that a ring homomorphism commutes with the cast.

#### Common errors

1. A learner writes `f.toFun a` in a statement. The simp lemmas are stated with `⇑f a`, so they do not apply. Write `f a`.
2. A learner looks for `RingHom.map_add`. It exists but the general `map_add` is preferred, because it works for all kinds of maps.
3. A learner proves a goal with casts by `simp` and it fails. Try `push_cast` first, or `norm_cast`, or `exact_mod_cast`.
4. A learner writes `(2 - 5 : ℤ)` and `((2 - 5 : ℕ) : ℤ)` and expects the same value.

### Exercises

1. (A) Prove that a monoid homomorphism sends a unit to a unit.
2. (A) Let $f : \mathbb{Z} \to \mathbb{Z}$ be a ring homomorphism. Prove that $f(n) = n$ for every $n$.
3. (B) Prove that there is no ring homomorphism from $\mathbb{Q}$ to $\mathbb{Z}$.
4. (B) Prove that the composite of two ring homomorphisms is a ring homomorphism, and that the identity is one.
5. (B) Prove that a ring homomorphism from a field to a ring with $0 \neq 1$ is injective. Hint: its kernel is an ideal, and the only ideals of a field are $0$ and the whole field.
6. (C) Prove that the only ring homomorphism $\mathbb{R} \to \mathbb{R}$ is the identity. Hint: it sends squares to squares, so it preserves the order, and it fixes $\mathbb{Q}$.
7. (L) Prove that a ring homomorphism $\mathbb{Z} \to \mathbb{Q}$ preserves products. The solution is `map_mul_example` in `Solutions.lean`.
8. (L) Prove that the cast $\mathbb{N} \to \mathbb{Q}$ preserves sums. The solution is `cast_add_example` in `Solutions.lean`.

### Notes and history

The notion of a map that preserves structure became central with the algebra of Noether and her school in the 1920s. The uniqueness of the map from $\mathbb{Z}$ says that $\mathbb{Z}$ is the *initial ring*, in the language of the category theory of Eilenberg and Mac Lane (1945).

### Reference

<?reference?>
