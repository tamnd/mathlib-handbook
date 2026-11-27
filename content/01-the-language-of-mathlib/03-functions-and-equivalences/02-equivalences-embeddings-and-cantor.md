---
title: Equivalences, embeddings and Cantor's theorem
kind: theory
modules:
  - Mathlib.Logic.Equiv.Defs
  - Mathlib.Logic.Embedding.Basic
explains:
  E3: [Equiv, Function.Embedding]
  E2: [Equiv.bijective, Equiv.symm_apply_apply, Equiv.apply_symm_apply, Equiv.symm, Equiv.trans, Equiv.refl, Equiv.ofBijective, Equiv.Perm, Equiv.ext, Equiv.symm_symm, Function.Embedding.injective, Equiv.toEmbedding, Function.Embedding.trans, Function.cantor_injective]
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

## Equivalences, embeddings and Cantor's theorem

### Overview

Two sets have the same size when there is a bijection between them. Mathlib does not use the property "bijective" for this. It uses a structure, the *equivalence* `α ≃ β`, that stores a function, its inverse and the two inverse laws. An equivalence carries more data than a proof of bijectivity, and so it is easier to use: the inverse is part of the data, and no choice is needed to recover it. In the same way, an *embedding* `α ↪ β` stores an injective function with its proof.

This section defines both structures and gives their algebra: identity, inverse, composition, and the passage between an equivalence and a bijective function. It then proves the two basic theorems on the comparison of sizes. Cantor's theorem states that no type is equivalent to its power set, and in fact that there is no surjection from a type onto its power set. The Schröder-Bernstein theorem states that two embeddings $\alpha \hookrightarrow \beta$ and $\beta \hookrightarrow \alpha$ give an equivalence $\alpha \simeq \beta$.

### Definitions

**Definition (Equivalence).** An *equivalence* between types $\alpha$ and $\beta$ is a structure with four fields:

1. a function $\mathrm{toFun} : \alpha \to \beta$;
2. a function $\mathrm{invFun} : \beta \to \alpha$;
3. a proof that $\mathrm{invFun}$ is a left inverse of $\mathrm{toFun}$;
4. a proof that $\mathrm{invFun}$ is a right inverse of $\mathrm{toFun}$.

The type of equivalences is written $\alpha \simeq \beta$. For $e : \alpha \simeq \beta$, Lean lets $e$ act as a function, so $e(a)$ means $\mathrm{toFun}(a)$. Chapter 4 explains the coercion that does this.

::: mathlib
`Equiv` · `Mathlib.Logic.Equiv.Defs`

The structure `Equiv α β` has the fields `toFun`, `invFun`, `left_inv` and `right_inv`. The notation is `α ≃ β`. The fields `left_inv` and `right_inv` have the types `LeftInverse invFun toFun` and `RightInverse invFun toFun`. A term is written `⟨f, g, h₁, h₂⟩` or with `where`.

<?decl Equiv?>
:::

**Definition (Operations on equivalences).** Let $e : \alpha \simeq \beta$ and $e' : \beta \simeq \gamma$.

1. The *identity* $\mathrm{refl}_\alpha : \alpha \simeq \alpha$ has both functions equal to $\mathrm{id}$.
2. The *inverse* $e^{-1} : \beta \simeq \alpha$, written `e.symm`, exchanges $\mathrm{toFun}$ with $\mathrm{invFun}$ and the two proofs.
3. The *composite* $e \cdot e' : \alpha \simeq \gamma$, written `e.trans e'`, has the function $e' \circ e$ and the inverse $e^{-1} \circ e'^{-1}$.

The order in `e.trans e'` is the order of application: first $e$, then $e'$. This is the reverse of the order in $e' \circ e$.

**Definition (Permutation).** A *permutation* of $\alpha$ is an equivalence $\alpha \simeq \alpha$. The type of permutations is `Equiv.Perm α`.

**Definition (Embedding).** An *embedding* of $\alpha$ into $\beta$ is a structure with a function $\mathrm{toFun} : \alpha \to \beta$ and a proof that it is injective. The type of embeddings is written $\alpha \hookrightarrow \beta$.

::: mathlib
`Function.Embedding` · `Mathlib.Logic.Embedding.Basic`

The structure has the fields `toFun` and `inj'`, and the notation is `α ↪ β`. The lemma `Function.Embedding.injective` gives injectivity. An equivalence gives an embedding by `Equiv.toEmbedding`, and embeddings compose by `Function.Embedding.trans`. The subtype inclusion is `Function.Embedding.subtype p : {x // p x} ↪ α`.

<?decl Function.Embedding?>
:::

### Theorems and proofs

**Theorem (Equivalences are bijective).** Let $e : \alpha \simeq \beta$. Then $e$ is bijective, and $e^{-1}(e(a)) = a$ and $e(e^{-1}(b)) = b$ for every $a$ and $b$.

*Proof.* The two equations are the fields $\mathrm{left\_inv}$ and $\mathrm{right\_inv}$. So $e^{-1}$ is a two-sided inverse of $e$, and $e$ is bijective by the theorem on bijective maps of the previous section. $\square$

::: mathlib
`Equiv.symm_apply_apply` · `Mathlib.Logic.Equiv.Defs`

The two equations are `e.symm (e x) = x` and `e (e.symm y) = y`, the latter as `Equiv.apply_symm_apply`. Both are simp lemmas. Bijectivity is `Equiv.bijective`, and its parts are `Equiv.injective` and `Equiv.surjective`.

<?decl Equiv.symm_apply_apply?>
:::

**Theorem (Bijections give equivalences).** Let $f : \alpha \to \beta$ be bijective. Then there is an equivalence $e : \alpha \simeq \beta$ with $e(a) = f(a)$ for every $a$.

*Proof.* By the theorem on bijective maps, $f$ has a two-sided inverse $g$. The structure $\langle f, g, h_1, h_2\rangle$, with the two inverse laws, is an equivalence whose function is $f$. $\square$

The inverse $g$ comes from the axiom of choice, so this construction is noncomputable. In Mathlib it is `Equiv.ofBijective f hf`. When the inverse is known, the direct construction $\langle f, g, h_1, h_2\rangle$ is better, because its inverse has a formula.

**Theorem (Extensionality).** Two equivalences $e, e' : \alpha \simeq \beta$ are equal if $e(a) = e'(a)$ for every $a$.

*Proof.* By function extensionality, the two functions $\mathrm{toFun}$ are equal. Write $g$ and $g'$ for the two inverse functions. Both are two-sided inverses of the same function, and the uniqueness part of the theorem on bijective maps gives $g = g'$. The two proof fields are equal by proof irrelevance. So the structures are equal. $\square$

**Theorem (Groupoid laws).** For $e : \alpha \simeq \beta$, $e' : \beta \simeq \gamma$ and $e'' : \gamma \simeq \delta$:

1. $(e \cdot e') \cdot e'' = e \cdot (e' \cdot e'')$;
2. $\mathrm{refl} \cdot e = e = e \cdot \mathrm{refl}$;
3. $e \cdot e^{-1} = \mathrm{refl}_\alpha$ and $e^{-1} \cdot e = \mathrm{refl}_\beta$;
4. $(e^{-1})^{-1} = e$.

So the permutations of $\alpha$ form a group under composition.

*Proof.* By extensionality, it suffices to check each equation at a point. 1. Both sides send $a$ to $e''(e'(e(a)))$. 2. Both sides send $a$ to $e(a)$. 3. The left side sends $a$ to $e^{-1}(e(a)) = a$ by the previous theorem, and the second equation is the same at a point $b$. 4. The function of $(e^{-1})^{-1}$ is the function of $e$, by the definition of $\mathrm{symm}$, so this holds by definition. $\square$

::: mathlib
`Equiv.ext` · `Mathlib.Logic.Equiv.Defs`

The statement is `(∀ x, f x = g x) → f = g` for `f g : α ≃ β`. The tactic `ext x` applies it. The groupoid laws are `Equiv.trans_assoc`, `Equiv.refl_trans`, `Equiv.trans_refl`, `Equiv.self_trans_symm`, `Equiv.symm_trans_self` and `Equiv.symm_symm`. The group of permutations is the instance `Equiv.Perm.permGroup`, in Volume 5. Its multiplication is composition in the order of functions: `(σ * τ) x = σ (τ x)`.

<?decl Equiv.ext?>
:::

**Theorem (Cantor).** For every type $\alpha$, there is no surjective function $f : \alpha \to \texttt{Set}\ \alpha$. So $\alpha$ is not equivalent to $\texttt{Set}\ \alpha$.

*Proof.* Let $f : \alpha \to \texttt{Set}\ \alpha$. Define the *diagonal set*
$$D = \{x \mid x \notin f(x)\}.$$
Assume that $f$ is surjective. Then there is $a$ with $f(a) = D$. By the definition of $D$, the statement $a \in D$ is the statement $a \notin f(a)$, which is $a \notin D$. So $a \in D \leftrightarrow \lnot(a \in D)$. A proposition $p$ with $p \leftrightarrow \lnot p$ gives a contradiction: if $p$, then $\lnot p$, which with $p$ gives $\mathrm{False}$; so $\lnot p$; then $p$ by the equivalence; and $\lnot p$ and $p$ give $\mathrm{False}$. So $f$ is not surjective. An equivalence would be surjective, so there is none. $\square$

The proof does not use the excluded middle: the last step is a constructive argument about $p \leftrightarrow \lnot p$.

**Theorem (Cantor, injective form).** For every type $\alpha$, there is no injective function $g : \texttt{Set}\ \alpha \to \alpha$.

*Proof.* Let $g$ be injective. Define $f : \alpha \to \texttt{Set}\ \alpha$ by $f(x) = \{y \mid \exists s,\ g(s) = x \land y \in s\}$, the union of all sets that $g$ sends to $x$. For every set $s$, injectivity of $g$ gives $f(g(s)) = s$: if $g(s') = g(s)$, then $s' = s$, so the only set in the union is $s$. So $f$ has the right inverse $g$, and $f$ is surjective. This contradicts the previous theorem. $\square$

::: mathlib
`Function.cantor_injective` · `Mathlib.Logic.Function.Basic`

The statement is `¬Function.Injective f` for `f : Set α → α`. The surjective form is `Function.cantor_surjective : ¬Function.Surjective f` for `f : α → Set α`. Volume 31 uses these theorems to show that the cardinal of `Set α` is larger than the cardinal of `α`.

<?decl Function.cantor_injective?>
:::

**Theorem (Schröder-Bernstein).** Let $f : \alpha \to \beta$ and $g : \beta \to \alpha$ be injective. Then there is a bijection $h : \alpha \to \beta$.

*Proof.* The proof uses the excluded middle. Call an element of $\alpha$ a *$g$-image* when it is $g(b)$ for some $b$; this $b$ is unique by injectivity of $g$, and the proof writes it $g^{-1}(a)$. Define the sets $C_n \subseteq \alpha$ by
$$C_0 = \alpha \setminus g(\beta), \qquad C_{n + 1} = g(f(C_n)),$$
and let $C = \bigcup_n C_n$. Define $h : \alpha \to \beta$ by
$$h(a) = \begin{cases} f(a) & \text{if } a \in C, \\ g^{-1}(a) & \text{if } a \notin C. \end{cases}$$
The second case is well defined: if $a \notin C$, then $a \notin C_0$, so $a$ is a $g$-image.

*$h$ is injective.* Let $h(a) = h(a')$. If $a, a' \in C$, then $f(a) = f(a')$, and $a = a'$ by injectivity of $f$. If $a, a' \notin C$, then $g^{-1}(a) = g^{-1}(a')$, and applying $g$ gives $a = a'$. The mixed case cannot occur. Assume $a \in C$, $a' \notin C$ and $f(a) = g^{-1}(a')$. Then $a' = g(f(a))$. Since $a \in C_n$ for some $n$, this gives $a' \in C_{n + 1} \subseteq C$, a contradiction.

*$h$ is surjective.* Let $b : \beta$, and consider $a = g(b)$. If $a \notin C$, then $h(a) = g^{-1}(g(b)) = b$. If $a \in C$, then $a \in C_n$ for some $n$. The case $n = 0$ is impossible, because $a = g(b)$ is a $g$-image. So $n = m + 1$, and $a = g(f(c))$ with $c \in C_m$. Injectivity of $g$ gives $b = f(c)$. Since $c \in C$, $h(c) = f(c) = b$. $\square$

The set $C$ collects the elements of $\alpha$ whose chain of preimages, under $g$ and $f$ alternately, stops in $\alpha \setminus g(\beta)$. On $C$ the bijection follows $f$, and outside $C$ it follows $g^{-1}$.

::: mathlib
`Function.Embedding.schroeder_bernstein` · `Mathlib.SetTheory.Cardinal.SchroederBernstein`

The statement is `Injective f → Injective g → ∃ h, Bijective h` for `f : α → β` and `g : β → α`. The form with embeddings is `Function.Embedding.antisymm : (α ↪ β) → (β ↪ α) → Nonempty (α ≃ β)`. The Mathlib proof uses the Knaster-Tarski fixed point theorem on `Set α` in place of the union of the $C_n$, but the set it finds is the set $C$ of the proof above.

<?decl Function.Embedding.schroeder_bernstein?>
:::

### Examples

**Example (Swapping a pair).** The map $(a, b) \mapsto (b, a)$ is an equivalence $\mathbb{N} \times \mathbb{Z} \simeq \mathbb{Z} \times \mathbb{N}$, with inverse $(b, a) \mapsto (a, b)$. In Mathlib it is `Equiv.prodComm`. It sends $(1, -1)$ to $(-1, 1)$ by definition, so `rfl` proves the value. Its bijectivity is the general theorem.

<?lean MathlibHandbook/V01/C03/Examples.lean#equiv?>

**Example (The inverse undoes the equivalence).** For any $e : \alpha \simeq \beta$ and $x : \alpha$, the equation $e^{-1}(e(x)) = x$ is the field $\mathrm{left\_inv}$, with the name `Equiv.symm_apply_apply`.

<?lean MathlibHandbook/V01/C03/Examples.lean#equiv_symm?>

**Example (Cantor's diagonal for $\mathbb{N}$).** Let $f : \mathbb{N} \to \texttt{Set}\ \mathbb{N}$ be $f(n) = \{k \mid n \mid k\}$, the multiples of $n$. The diagonal set is $D = \{n \mid n \notin f(n)\} = \{n \mid \lnot(n \mid n)\}$. Every $n$ divides itself, so $D = \emptyset$. The proof says that $D$ is not of the form $f(a)$. Indeed, $f(a)$ always contains $0$, and $D$ does not.

**Example (Schröder-Bernstein on intervals).** Let $\alpha = [0, 1]$ and $\beta = [0, 1)$ in $\mathbb{R}$. The map $f(x) = x/2$ from $\alpha$ to $\beta$ and the inclusion $g$ from $\beta$ to $\alpha$ are injective. The construction of the proof gives $C_0 = \alpha \setminus g(\beta) = \{1\}$, then $C_1 = g(f(C_0)) = \{1/2\}$, and in general $C_n = \{1/2^n\}$. So $C = \{1, 1/2, 1/4, \ldots\}$. The bijection $h$ sends $1/2^n$ to $f(1/2^n) = 1/2^{n + 1}$, and it sends every other $x$ to $g^{-1}(x) = x$. So $h(1) = 1/2$, $h(1/2) = 1/4$, and so on, and $h$ fixes all other points.

**Counterexample (Bijective is not an equivalence).** A proof `hf : Function.Bijective f` and an equivalence `e : α ≃ β` with `⇑e = f` hold the same mathematical content, but they are different terms. From `hf`, the inverse function is `Function.surjInv hf.2`, and Lean cannot evaluate it. From an explicit `e`, the inverse `e.symm` has the formula that the definition gave. For example, the inverse of `Equiv.prodComm` is again a swap, and `(Equiv.prodComm ℕ ℤ).symm (-1, 1) = (1, -1)` holds by `rfl`. The same equation for `Equiv.ofBijective` does not hold by `rfl`.

### The library around it

The module `Mathlib.Logic.Equiv.Defs` defines `Equiv`, `Equiv.Perm`, the operations `Equiv.refl`, `Equiv.symm` and `Equiv.trans`, and `Equiv.ofBijective`. The modules `Mathlib.Logic.Equiv.Prod`, `Mathlib.Logic.Equiv.Sum`, `Mathlib.Logic.Equiv.Set` and `Mathlib.Logic.Equiv.Basic` have the standard equivalences of type theory. Some of them:

| Equivalence | Statement |
|---|---|
| `Equiv.prodComm` | `α × β ≃ β × α` |
| `Equiv.prodAssoc` | `(α × β) × γ ≃ α × (β × γ)` |
| `Equiv.sumComm` | `α ⊕ β ≃ β ⊕ α` |
| `Equiv.sumProdDistrib` | `(α ⊕ β) × γ ≃ α × γ ⊕ β × γ` |
| `Equiv.curry` | `(α × β → γ) ≃ (α → β → γ)` |
| `Equiv.boolArrowEquivProd` | `(Bool → α) ≃ α × α` |
| `Equiv.Set.univ` | `↥(Set.univ : Set α) ≃ α` |
| `Equiv.ofInjective` | `α ≃ Set.range f` for injective `f` |
| `Equiv.subtypeEquivRight` | `{x // p x} ≃ {x // q x}` when `p x ↔ q x` |

These equivalences are the "canonical isomorphisms" of a textbook. A textbook identifies the two sides. Mathlib keeps them apart and transports results along the equivalence.

The module `Mathlib.Logic.Embedding.Basic` defines `Function.Embedding`. The module `Mathlib.SetTheory.Cardinal.SchroederBernstein` has the Schröder-Bernstein theorem and `Function.Embedding.total`, which states that for any two types one embeds in the other. Volume 31 treats cardinals.

#### Common errors

1. A learner composes `e.trans e'` and expects `e (e' x)`. The value is `e' (e x)`.
2. A learner uses `Equiv.ofBijective` and then cannot compute the inverse. Build the equivalence with an explicit inverse when one is known.
3. A learner proves `e = e'` by `rfl` for equivalences with the same function and different inverse formulas. Use `Equiv.ext`.

### Exercises

1. (A) Write the equivalence $\mathbb{Z} \simeq \mathbb{Z}$ given by $x \mapsto x + 1$. Give its inverse and the proofs of the two laws.
2. (A) Prove that $(e \cdot e')^{-1} = e'^{-1} \cdot e^{-1}$.
3. (B) Construct an equivalence $\mathbb{N} \oplus \mathbb{N} \simeq \mathbb{N}$. Hint: even and odd numbers.
4. (B) Construct an equivalence $\texttt{Set}\ (\alpha \oplus \beta) \simeq \texttt{Set}\ \alpha \times \texttt{Set}\ \beta$.
5. (B) Prove that no type $\alpha$ has a surjection $\alpha \to (\alpha \to \mathrm{Bool})$, without the use of `Set`.
6. (C) Use Schröder-Bernstein to prove that $\mathbb{N} \times \mathbb{N}$ and $\mathbb{N}$ are equivalent. Find injections in both directions.
7. (C) Use Schröder-Bernstein to prove that $\mathbb{R}$ and $\texttt{Set}\ \mathbb{N}$ are equivalent. Hint: binary and ternary expansions.
8. (L) Prove that an equivalence undoes its inverse, $e(e^{-1}(y)) = y$. The solution is `apply_symm_apply_example` in `Solutions.lean`.

### Notes and history

Cantor proved in 1874 that the real numbers are uncountable, and in 1891 he gave the diagonal argument, which proves the theorem of this section for any set. The theorem of Schröder and Bernstein was stated by Cantor, proved by Dedekind in 1887 in an unpublished note, and proved independently by Bernstein (1897) and Schröder (1898). The proof of Schröder had a gap. The proof above follows the chain argument of König (1906).

### Reference

<?reference?>
