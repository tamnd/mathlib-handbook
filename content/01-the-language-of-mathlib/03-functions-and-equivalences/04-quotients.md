---
title: Quotient types
kind: theory
modules:
  - Mathlib.Data.Quot
explains:
  E3: [Quotient.eq, Quotient.out]
  E2: [Quotient.lift_mk, Quotient.lift_comp_mk, Quotient.mk_surjective, Quot.mk_surjective, Quotient.out_eq, Quotient.mk_out, Quotient.map, Quotient.map_mk, Quotient.lift₂_mk, Quot.lift_mk, Quot.induction_on, Quot.eqvGen_exact, Quot.eqvGen_sound, Setoid.ext, Quotient.out_inj]
  E1: auto
families: []
requires: [V01.C02]
reads_with: ["TPIL", "MIL"]
lean:
  - MathlibHandbook/V01/C03/Examples.lean
  - MathlibHandbook/V01/C03/Exercises.lean
  - MathlibHandbook/V01/C03/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Quotient types

### Overview

The previous section cut a type into the classes of an equivalence relation. A quotient makes each class into a single element. The integers modulo $n$ are the quotient of $\mathbb{Z}$ by congruence modulo $n$. The rational numbers can be built as a quotient of pairs of integers. A quotient group, a quotient ring and a quotient space are quotients of this kind with extra structure.

In set theory, the quotient $\alpha/{\sim}$ is the set of equivalence classes. In Lean, a quotient is a primitive type former with its own rules. This section states these rules, derives from them the universal property of the quotient and the first isomorphism theorem for types, and gives the standard constructions: $\mathbb{Z}/n\mathbb{Z}$ and $\mathbb{Z}$ from pairs of natural numbers. It also proves function extensionality from the rules of the quotient.

### Definitions

**Definition (Quotient type).** Let $r$ be a relation on $\alpha$. The *quotient* $\texttt{Quot}\ r$ is a type with:

1. a function $\mathrm{mk} : \alpha \to \texttt{Quot}\ r$, written $a \mapsto [a]$;
2. the *soundness* rule: if $r(a, b)$, then $[a] = [b]$;
3. the *lift* rule: if $f : \alpha \to \beta$ satisfies $r(a, b) \to f(a) = f(b)$ for all $a, b$, then there is $\bar f : \texttt{Quot}\ r \to \beta$ with $\bar f([a]) = f(a)$ for every $a$;
4. the *induction* rule: if a predicate $P$ on $\texttt{Quot}\ r$ holds for every $[a]$, then it holds for every element of $\texttt{Quot}\ r$.

The equation $\bar f([a]) = f(a)$ holds by definition, so Lean computes with it.

**Definition (Quotient by an equivalence relation).** A *setoid* on $\alpha$ is an equivalence relation on $\alpha$, bundled with its proof. For a setoid $s$, the type $\texttt{Quotient}\ s$ is $\texttt{Quot}\ s$. Its class map is written $a \mapsto \llbracket a \rrbracket$, and the relation is written $a \approx b$.

`Quot r` makes sense for any relation $r$. `Quotient s` asks for an equivalence relation, and then the classes of $a$ and $b$ are equal *exactly* when $a \approx b$. For an arbitrary $r$, the classes are equal exactly when $\mathrm{EqvGen}(r)(a, b)$, by a theorem below.

**Definition (Respecting a relation).** A function $f : \alpha \to \beta$ *respects* a relation $r$ on $\alpha$ when $r(a, b) \to f(a) = f(b)$ for all $a, b$. A function $f : \alpha \to \alpha'$ respects relations $r$ on $\alpha$ and $r'$ on $\alpha'$ when $r(a, b) \to r'(f(a), f(b))$.

**Definition (Representative).** For $q : \texttt{Quotient}\ s$, a *representative* of $q$ is an $a$ with $\llbracket a \rrbracket = q$. The function `Quotient.out` chooses a representative of each class, by the axiom of choice.

### Theorems and proofs

**Theorem (Surjectivity of the class map).** The function $\mathrm{mk} : \alpha \to \texttt{Quot}\ r$ is surjective.

*Proof.* Apply the induction rule to the predicate $P(q) := \exists a,\ [a] = q$. For $q = [a]$, the element $a$ is a witness. So $P(q)$ holds for every $q$. $\square$

**Theorem (Exactness).** Let $s$ be a setoid on $\alpha$. Then $\llbracket a \rrbracket = \llbracket b \rrbracket$ if and only if $a \approx b$.

*Proof.* The direction from right to left is the soundness rule. For the other direction, fix $b$ and define $f : \alpha \to \mathrm{Prop}$ by $f(x) = (x \approx b)$. Then $f$ respects $\approx$: if $x \approx y$, then $x \approx b \leftrightarrow y \approx b$ by symmetry and transitivity, and propositional extensionality gives $f(x) = f(y)$. So $f$ lifts to $\bar f : \texttt{Quotient}\ s \to \mathrm{Prop}$ with $\bar f(\llbracket x \rrbracket) = (x \approx b)$. Assume $\llbracket a \rrbracket = \llbracket b \rrbracket$. Apply $\bar f$: $(a \approx b) = (b \approx b)$. The right side is true by reflexivity, so $a \approx b$. $\square$

This proof is the reason that `Quotient` asks for an equivalence relation. The function $x \mapsto (x \approx b)$ respects $\approx$ only because $\approx$ is symmetric and transitive.

::: mathlib
`Quotient.eq` · `Mathlib.Data.Quot`

The statement is `⟦x⟧ = ⟦y⟧ ↔ r x y` for `r : Setoid α`. The core library has the two directions `Quotient.sound` and `Quotient.exact`. A proof that two classes are equal usually reads `Quotient.sound h` or `Quotient.eq.2 h`. The variant `Quotient.eq'` is for the class map `Quotient.mk'`, which finds the setoid by unification and not by instance search.

<?decl Quotient.eq?>
:::

**Theorem (Exactness for an arbitrary relation).** Let $r$ be a relation on $\alpha$. Then $[a] = [b]$ in $\texttt{Quot}\ r$ if and only if $\mathrm{EqvGen}(r)(a, b)$.

*Proof.* From right to left, by induction on $\mathrm{EqvGen}(r)(a, b)$. The rule $r(a, b)$ gives $[a] = [b]$ by soundness. Reflexivity, symmetry and transitivity of $\mathrm{EqvGen}$ correspond to the same properties of equality.

From left to right, let $e = \mathrm{EqvGen}(r)$, an equivalence relation. The class map $x \mapsto \llbracket x \rrbracket_e$ into $\texttt{Quotient}\ e$ respects $r$, because $r \subseteq e$ and soundness. So it lifts to $g : \texttt{Quot}\ r \to \texttt{Quotient}\ e$ with $g([x]) = \llbracket x \rrbracket_e$. If $[a] = [b]$, then $\llbracket a \rrbracket_e = \llbracket b \rrbracket_e$, and exactness for the setoid $e$ gives $e(a, b)$. $\square$

::: mathlib
`Quot.eqvGen_exact` · `Mathlib.Logic.Relation`

The two directions are `Quot.eqvGen_exact : Quot.mk r a = Quot.mk r b → EqvGen r a b` and `Quot.eqvGen_sound`. They are in `Mathlib.Logic.Relation`, next to the definition of `EqvGen`.

<?decl Quot.eqvGen_exact?>
:::

**Theorem (Universal property).** Let $s$ be a setoid on $\alpha$, and let $f : \alpha \to \beta$ respect $\approx$. Then there is exactly one function $\bar f : \texttt{Quotient}\ s \to \beta$ with $\bar f \circ \mathrm{mk} = f$.

*Proof.* Existence is the lift rule, and $\bar f(\llbracket a \rrbracket) = f(a)$ holds for each $a$. For uniqueness, let $g$ also satisfy $g(\llbracket a \rrbracket) = f(a)$ for each $a$. By function extensionality, it suffices to show $g(q) = \bar f(q)$ for each $q$. By the induction rule, it suffices to show this for $q = \llbracket a \rrbracket$, and there both sides are $f(a)$. $\square$

The uniqueness part can also be stated as: $\mathrm{mk}$ is surjective, and two functions that agree after composition with a surjective function are equal.

::: mathlib
`Quotient.lift_mk` · `Mathlib.Data.Quot`

The lift is `Quotient.lift f h`, where `h : ∀ a b, a ≈ b → f a = f b`. The equation `Quotient.lift f h ⟦x⟧ = f x` is `Quotient.lift_mk`, and it holds by `rfl`. The form `Quotient.lift_comp_mk` states `Quotient.lift f h ∘ Quotient.mk _ = f`. For a function of two arguments there is `Quotient.lift₂`, and for a map between quotients there is `Quotient.map`, with `Quotient.map_mk`.

<?decl Quotient.lift_mk?>
:::

**Theorem (First isomorphism theorem for types).** Let $f : \alpha \to \beta$, and let $\sim_f$ be its kernel. Then the lift $\bar f : \alpha/{\sim_f} \to \beta$ is injective, and it gives an equivalence between $\alpha/{\sim_f}$ and the range $\{f(a) \mid a : \alpha\}$. If $f$ is surjective, then $\alpha/{\sim_f} \simeq \beta$.

*Proof.* The function $f$ respects its kernel by definition, so $\bar f$ exists with $\bar f(\llbracket a \rrbracket) = f(a)$. For injectivity, let $\bar f(q) = \bar f(q')$. By surjectivity of the class map, $q = \llbracket a \rrbracket$ and $q' = \llbracket a' \rrbracket$. Then $f(a) = f(a')$, that is, $a \sim_f a'$, and soundness gives $q = q'$. The image of $\bar f$ is the image of $f$, since $\mathrm{mk}$ is surjective. So $\bar f$, with its codomain restricted to the range, is injective and surjective, and the theorem on bijections of Section 2 gives the equivalence. If $f$ is surjective, the range is all of $\beta$. $\square$

::: mathlib
`Setoid.quotientKerEquivRange` · `Mathlib.Order.Setoid.Basic`

The equivalence is `Setoid.quotientKerEquivRange f : Quotient (Setoid.ker f) ≃ Set.range f`, and the surjective case is `Setoid.quotientKerEquivOfSurjective`. The lift is `Setoid.kerLift f`, and `Setoid.kerLift_injective` is the injectivity. Volume 5 proves the same theorem for groups, where the kernel is a normal subgroup.

<?decl Setoid.quotientKerEquivRange?>
:::

**Theorem (Function extensionality).** Let $f, g : \alpha \to \beta$ with $f(x) = g(x)$ for every $x$. Then $f = g$.

*Proof.* Let $r$ be the relation on $\alpha \to \beta$ given by $r(u, v) \iff \forall x,\ u(x) = v(x)$. Define $E : \texttt{Quot}\ r \to \alpha \to \beta$ by lifting $u \mapsto (x \mapsto u(x))$: write $E(q)(x)$ as the lift of $u \mapsto u(x)$, applied to $q$. This lift respects $r$, because $r(u, v)$ gives $u(x) = v(x)$. Then $E([u]) = (x \mapsto u(x))$, which is $u$ by the eta rule of Lean. By hypothesis $r(f, g)$, so $[f] = [g]$ by soundness. Apply $E$: $f = E([f]) = E([g]) = g$. $\square$

In Lean, this theorem is `funext`, and its proof in the core library is the argument above. So function extensionality is not an extra axiom: it follows from the soundness rule of quotients.

**Theorem (Choice of representatives).** For $q : \texttt{Quotient}\ s$, the representative $a = \mathrm{out}(q)$ satisfies $\llbracket a \rrbracket = q$. For $a : \alpha$, $\mathrm{out}(\llbracket a \rrbracket) \approx a$. The function $\mathrm{out}$ is injective.

*Proof.* The first claim is the definition of $\mathrm{out}$: by surjectivity of $\mathrm{mk}$, there is a representative of $q$, and choice picks one. For the second claim, apply the first to $q = \llbracket a \rrbracket$: $\llbracket \mathrm{out}(\llbracket a \rrbracket) \rrbracket = \llbracket a \rrbracket$, and exactness gives $\mathrm{out}(\llbracket a \rrbracket) \approx a$. For injectivity, $\mathrm{out}$ has the left inverse $\mathrm{mk}$, by the first claim. $\square$

::: mathlib
`Quotient.out` · `Mathlib.Data.Quot`

`Quotient.out q` is noncomputable. The lemmas are `Quotient.out_eq : ⟦q.out⟧ = q`, `Quotient.mk_out : ⟦a⟧.out ≈ a` and `Quotient.out_inj`. A definition on a quotient should use `Quotient.lift` and not `Quotient.out`, because `Quotient.lift` computes and comes with the equation `Quotient.lift_mk`. A proof may use `Quotient.out` freely.

<?decl Quotient.out?>
:::

### Examples

**Example (The integers modulo $n$).** Let $n \geq 1$ and let $a \approx b \iff n \mid a - b$ on $\mathbb{Z}$. The quotient $\mathbb{Z}/{\approx}$ has the classes $\llbracket 0 \rrbracket, \ldots, \llbracket n - 1 \rrbracket$. Addition is defined by $\llbracket a \rrbracket + \llbracket b \rrbracket = \llbracket a + b \rrbracket$, by `Quotient.lift₂` of the function $(a, b) \mapsto \llbracket a + b \rrbracket$. It respects $\approx$: if $n \mid a - a'$ and $n \mid b - b'$, then $n \mid (a + b) - (a' + b')$, the sum of the two differences. Multiplication is similar, with $ab - a'b' = a(b - b') + (a - a')b'$.

**Example (The integers from pairs).** On $\mathbb{N} \times \mathbb{N}$, let $(a, b) \approx (c, d)$ when $a + d = b + c$. The class of $(a, b)$ stands for the integer $a - b$. The map $\mathbb{N} \times \mathbb{N} \to \mathbb{Z}$, $(a, b) \mapsto a - b$, is surjective, and its kernel is $\approx$: $a - b = c - d$ if and only if $a + d = b + c$. By the first isomorphism theorem, $(\mathbb{N} \times \mathbb{N})/{\approx} \simeq \mathbb{Z}$. Each class has a unique representative of the form $(k, 0)$ or $(0, k + 1)$.

**Example (A function that does not descend).** On $\mathbb{Z}$ with congruence modulo $3$, the function $f(a) = a^2 \bmod 6$ does not respect the relation: $0 \equiv 3$, but $f(0) = 0$ and $f(3) = 3$. So there is no lift. The function $g(a) = a^2 \bmod 3$ does respect it, since $a \equiv a' \pmod 3$ gives $a^2 \equiv a'^2 \pmod 3$. Its lift sends $\llbracket 0 \rrbracket \mapsto 0$, $\llbracket 1 \rrbracket \mapsto 1$ and $\llbracket 2 \rrbracket \mapsto 1$.

**Example (A quotient by a relation that is not an equivalence).** Let $r(a, b) \iff b = a + 1$ on $\mathbb{Z}$. By the exactness theorem for an arbitrary relation, $[a] = [b]$ in $\texttt{Quot}\ r$ exactly when $\mathrm{EqvGen}(r)(a, b)$, which holds for all $a, b$ by the example of the previous section. So $\texttt{Quot}\ r$ has one element. A function out of it is a function $f$ on $\mathbb{Z}$ with $f(a) = f(a + 1)$, that is, a constant function.

**Counterexample (Out does not respect the class map).** Let $\approx$ be congruence modulo $2$ on $\mathbb{Z}$. Then $\mathrm{out}(\llbracket 5 \rrbracket)$ is some odd number, but nothing says which one. It need not be $5$, and the equation $\mathrm{out}(\llbracket 5 \rrbracket) = 5$ has no proof. Only $\mathrm{out}(\llbracket 5 \rrbracket) \approx 5$ holds. A definition of $f(q) = \mathrm{out}(q)^2$ is valid but useless, because its values cannot be computed.

### The library around it

The core library defines `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` and the axiom `Quot.sound`, and on top of them `Setoid`, `Quotient`, `Quotient.mk`, `Quotient.lift`, `Quotient.sound` and `Quotient.exact`. The notation `⟦a⟧` is `Quotient.mk _ a`. The module `Mathlib.Data.Quot` has the lemmas `Quotient.eq`, `Quotient.lift_mk`, `Quotient.mk_surjective`, `Quot.mk_surjective`, `Quotient.map`, `Quotient.map₂`, `Quotient.out` with its lemmas, and `Setoid.ext`, which states that two setoids with the same relation are equal.

A proof about every element of a quotient starts with `induction q using Quotient.inductionOn` or with `obtain ⟨a, rfl⟩ := Quotient.mk_surjective q`. The second form is often easier: it replaces `q` by `⟦a⟧`, and then `Quotient.lift_mk` and `simp` work.

#### Common errors

1. A learner defines a function on a quotient with `Quotient.out` and then cannot prove anything about its values. Use `Quotient.lift`.
2. A learner applies `Quotient.lift f h` and forgets that `h` must be proved. The proof of `h` is the mathematical content: the check that `f` is well defined.
3. A learner uses `Quot` with a relation that is not an equivalence relation and expects `Quot.mk r a = Quot.mk r b ↔ r a b`. This holds only for `EqvGen r`.

### Exercises

1. (A) In $\mathbb{Z}$ modulo $5$, show that $\llbracket 7 \rrbracket = \llbracket -3 \rrbracket$ and $\llbracket 7 \rrbracket \neq \llbracket 3 \rrbracket$.
2. (A) Prove that the function $a \mapsto (-1)^a$ on $\mathbb{N}$ descends to the quotient of $\mathbb{N}$ by congruence modulo $2$.
3. (B) Show that multiplication on $\mathbb{Z}$ modulo $n$ is well defined. Then show that $\llbracket a \rrbracket \mapsto \llbracket a \rrbracket^{-1}$, defined by an integer $b$ with $ab \equiv 1$, is well defined on the classes of $a$ coprime to $n$.
4. (B) Let $f : \alpha \to \beta$ be surjective. Prove that every function $g : \alpha \to \gamma$ that respects the kernel of $f$ factors uniquely as $g = h \circ f$.
5. (B) In the construction of $\mathbb{Z}$ from pairs, define negation and addition on the quotient and prove that they are well defined.
6. (C) Construct $\mathbb{Q}$ as a quotient of $\mathbb{Z} \times (\mathbb{Z} \setminus \{0\})$, define addition and multiplication, and prove that they are well defined.
7. (C) Prove that the quotient of $\alpha \to \beta$ by the relation $r(u, v) \iff \forall x,\ u(x) = v(x)$ is equivalent to $\alpha \to \beta$. Explain why this is a restatement of function extensionality.
8. (C) Let $r$ and $r'$ be setoids on $\alpha$ with $r \subseteq r'$. Construct a surjection $\alpha/r \to \alpha/r'$ and describe its kernel.

### Notes and history

Gauss calculated with residue classes in 1801, without the language of sets. Dedekind built quotient structures for ideals in the 1870s, and the general notion of a quotient set came with the set theory of the early twentieth century. The construction of $\mathbb{Z}$ from pairs of natural numbers and of $\mathbb{Q}$ from pairs of integers is in Landau's *Grundlagen der Analysis* (1930).

### Reference

<?reference?>
