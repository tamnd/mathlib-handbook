---
title: The type of finitely supported functions
kind: theory
modules:
  - Mathlib.Data.Finsupp.Defs
  - Mathlib.Data.Finsupp.Single
explains:
  E3: [Finsupp, Finsupp.single]
  E2: [Finsupp.support, Finsupp.mem_support_iff, Finsupp.ext, Finsupp.single_apply, Finsupp.support_single, Finsupp.single_injective, Finsupp.erase, Finsupp.onFinset, Finsupp.mapRange, Finsupp.equivFunOnFinite]
  E1: auto
families: []
requires: [V03.C03, V03.C06]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V03/C07/Examples.lean
  - MathlibHandbook/V03/C07/Exercises.lean
  - MathlibHandbook/V03/C07/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The type of finitely supported functions

### Overview

The polynomial $3 + 2X^5$ is a list of coefficients. It is also a function from the exponents to the coefficients: it sends $0$ to $3$, $5$ to $2$ and each other natural number to $0$. The factorization $360 = 2^3 \cdot 3^2 \cdot 5$ is a function from the primes to the exponents: it sends $2$ to $3$, $3$ to $2$, $5$ to $1$ and each other prime to $0$. A linear combination $2v_1 - v_4$ of vectors is a function from the index set to the scalars with the same property. In each case the function is zero at all points except finitely many. Such a function is a *finitely supported function*.

The finite support is what makes these functions useful. A sum $\sum_{a} g(a, f(a))$ over all points $a$ of an infinite set has no meaning in general. When $f$ is finitely supported and $g(a, 0) = 0$, only finitely many terms are not zero, and the sum is a finite sum over the support.

This section gives the definition, the functions with one point, the operations on the values, the rule of extensionality and the decomposition of each finitely supported function into a finite sum of functions with one point. Section 2 gives the sums over the support and the change of the points. After this section, the reader can read and write the type `α →₀ M` of Mathlib and compute with its terms.

### Definitions

**Definition (Support).** Let $X$ be a set and let $M$ be a set with a distinguished element $0$. The *support* of a function $f : X \to M$ is the set $\operatorname{supp}(f) = \{x \in X : f(x) \ne 0\}$.

**Definition (Finitely supported function).** A function $f : X \to M$ is *finitely supported* if its support is a finite set. The set of the finitely supported functions from $X$ to $M$ is written $X \to_0 M$ in this book. Other books write $M^{(X)}$ or $\bigoplus_{x \in X} M$.

The definition needs only a zero in $M$; the addition comes in when $M$ is an additive monoid. When $X$ is finite, each function $X \to M$ is finitely supported, so $X \to_0 M$ is the set of all functions. The notion has content only for an infinite $X$.

::: mathlib
`Finsupp` · `Mathlib.Data.Finsupp.Defs`

A term `f : α →₀ M` is a structure with three fields: `support : Finset α`, `toFun : α → M`, and `mem_support_toFun : ∀ a, a ∈ support ↔ toFun a ≠ 0`. The type `M` needs only an instance `Zero M`. The support is stored as a finset, so it is data and not only a property. The instance `Finsupp.instFunLike` lets the reader write `f a` for the value. The support is a field, not a definition, because no program can compute $\{a : f(a) \ne 0\}$ from the function alone when `α` is infinite. So whoever builds a term must give the finset.

<?decl Finsupp?>
:::

**Definition (Single).** For $a \in X$ and $b \in M$, the function $\operatorname{single}(a, b) : X \to M$ is given by $\operatorname{single}(a, b)(a) = b$ and $\operatorname{single}(a, b)(x) = 0$ for $x \ne a$. Its support is $\{a\}$ when $b \ne 0$ and $\emptyset$ when $b = 0$. So it is finitely supported.

::: mathlib
`Finsupp.single` · `Mathlib.Data.Finsupp.Single`

The function with one point. Mathlib prints `Finsupp.single a b` as `fun₀ | a => b`. The value is given by `Finsupp.single_apply`: `single a b a' = if a = a' then b else 0`. The lemmas `Finsupp.single_eq_same` and `Finsupp.single_eq_of_ne` are the two cases, and `simp` uses them.

<?decl Finsupp.single?>
:::

**Definition (Pointwise operations).** Let $M$ be an additive monoid. For $f, g \in X \to_0 M$, the sum $f + g$ is the function $x \mapsto f(x) + g(x)$, and the zero is the function with the value $0$ at each point. When $M$ is an additive group, $-f$ is the function $x \mapsto -f(x)$.

These functions are again finitely supported, by Theorem (Support of a sum) below. With them, $X \to_0 M$ is an additive monoid, commutative when $M$ is commutative, and a group when $M$ is a group.

**Definition (Map on the values).** Let $h : M \to N$ be a function with $h(0) = 0$. For $f \in X \to_0 M$, the function $h \circ f$ has $\operatorname{supp}(h \circ f) \subseteq \operatorname{supp}(f)$, because $f(x) = 0$ gives $h(f(x)) = h(0) = 0$. So $h \circ f \in X \to_0 N$. This is the map on the values.

::: mathlib
`Finsupp.mapRange` · `Mathlib.Data.Finsupp.Defs`

`Finsupp.mapRange h hh f` is $h \circ f$. The second argument `hh : h 0 = 0` is the hypothesis of the definition. If it were absent, the result would not be finitely supported in general: the constant map $h(m) = 1$ sends each function to a function with the full support. The value is `Finsupp.mapRange_apply`.

<?decl Finsupp.mapRange?>
:::

**Definition (Erase).** For $a \in X$ and $f \in X \to_0 M$, the function $\operatorname{erase}(a, f)$ has the value $0$ at $a$ and the value $f(x)$ at each $x \ne a$. Its support is $\operatorname{supp}(f) \setminus \{a\}$.

::: mathlib
`Finsupp.erase` · `Mathlib.Data.Finsupp.Single`

The function `Finsupp.erase a f`. The support is `Finsupp.support_erase`: `(erase a f).support = f.support.erase a`. The lemmas `Finsupp.erase_same` and `Finsupp.erase_ne` give the values.

<?decl Finsupp.erase?>
:::

### Theorems and proofs

**Theorem (Extensionality).** Let $f, g \in X \to_0 M$. If $f(x) = g(x)$ for each $x \in X$, then $f = g$.

*Proof.* On paper there is nothing to prove, because a finitely supported function is a function with a property. In the structure form of Mathlib the support is one more field, and the proof must check it. The functions are equal by hypothesis. For each $x$, the statement $x \in \operatorname{supp}(f)$ is equivalent to $f(x) \ne 0$, and this is equivalent to $g(x) \ne 0$, and this is equivalent to $x \in \operatorname{supp}(g)$. So the two finsets have the same elements, and they are equal. The third fields are proofs, and two proofs of the same proposition are equal. So the two structures are equal. $\square$

::: mathlib
`Finsupp.ext` · `Mathlib.Data.Finsupp.Defs`

The rule of extensionality has the attribute `ext`, so the tactic `ext a` changes a goal `f = g` into the goal `f a = g a`. The form with an equivalence is `Finsupp.ext_iff`. Most equalities of finitely supported functions are proved this way: `ext a`, then `simp` with the rules for the values.

<?decl Finsupp.ext?>
:::

**Theorem (Values and support of single).** Let $a \in X$ and $b \in M$. Then $\operatorname{supp}(\operatorname{single}(a, b)) \subseteq \{a\}$. If $b \ne 0$, then $\operatorname{supp}(\operatorname{single}(a, b)) = \{a\}$.

*Proof.* Let $x \in \operatorname{supp}(\operatorname{single}(a, b))$. Then $\operatorname{single}(a, b)(x) \ne 0$. If $x \ne a$, the value is $0$ by the definition, a contradiction. So $x = a$. This proves the inclusion. Now let $b \ne 0$. The value at $a$ is $b \ne 0$, so $a$ is in the support. With the inclusion, the support is $\{a\}$. $\square$

::: mathlib
`Finsupp.support_single` · `Mathlib.Data.Finsupp.Single`

The equality `(single a b).support = {a}` with the hypothesis `b ≠ 0`. The inclusion with no hypothesis is `Finsupp.support_single_subset`. The old name `Finsupp.support_single_ne_zero` is deprecated in this edition.

<?decl Finsupp.support_single?>
:::

**Theorem (Single is injective).** Let $a \in X$. If $\operatorname{single}(a, b) = \operatorname{single}(a, b')$, then $b = b'$.

*Proof.* Evaluate both functions at $a$. The left side gives $b$ and the right side gives $b'$. $\square$

::: mathlib
`Finsupp.single_injective` · `Mathlib.Data.Finsupp.Single`

The statement is `Function.Injective (Finsupp.single a)`. The point $a$ is fixed and the value varies. For the other variable, `Finsupp.single_left_injective` says that $a \mapsto \operatorname{single}(a, b)$ is injective when $b \ne 0$. The full criterion of equality of two singles is `Finsupp.single_eq_single_iff`.

<?decl Finsupp.single_injective?>
:::

**Theorem (Support of a sum).** Let $M$ be an additive monoid and let $f, g \in X \to_0 M$. Then $\operatorname{supp}(f + g) \subseteq \operatorname{supp}(f) \cup \operatorname{supp}(g)$. In particular $f + g$ is finitely supported.

*Proof.* Let $x \notin \operatorname{supp}(f) \cup \operatorname{supp}(g)$. Then $f(x) = 0$ and $g(x) = 0$, so $(f + g)(x) = 0 + 0 = 0$, and $x \notin \operatorname{supp}(f + g)$. This is the contrapositive of the inclusion. A subset of a finite set is finite, so $f + g$ is finitely supported. $\square$

The inclusion can be strict. Take $f = \operatorname{single}(1, 1)$ and $g = \operatorname{single}(1, -1)$ in $\mathbb{N} \to_0 \mathbb{Z}$. Then $f + g = 0$ has the empty support, and $\operatorname{supp}(f) \cup \operatorname{supp}(g) = \{1\}$. So the support of a sum is not a simple function of the supports.

**Theorem (Decomposition).** Let $M$ be an additive commutative monoid and let $f \in X \to_0 M$. Then $$f = \sum_{a \in \operatorname{supp}(f)} \operatorname{single}(a, f(a)).$$

*Proof.* The right side is a finite sum of elements of the monoid $X \to_0 M$, so it is an element of $X \to_0 M$. By extensionality it is enough to compare the values at a point $x$. The value of a finite sum of functions at $x$ is the sum of the values at $x$, because the operations are pointwise. So the value of the right side at $x$ is $\sum_{a \in \operatorname{supp}(f)} \operatorname{single}(a, f(a))(x)$. The term for $a$ is $f(a)$ if $a = x$ and $0$ if $a \ne x$. If $x \in \operatorname{supp}(f)$, exactly one term has $a = x$, and the sum is $f(x)$. If $x \notin \operatorname{supp}(f)$, all terms are $0$, the sum is $0$, and $f(x) = 0$ because $x$ is not in the support. In both cases the value is $f(x)$. $\square$

::: mathlib
`Finsupp.sum_single` · `Mathlib.Algebra.BigOperators.Finsupp.Basic`

Mathlib states the decomposition as `f.sum Finsupp.single = f`. Here `f.sum g` is the sum of `g a (f a)` over the support, the operation of Section 2. So the statement is the theorem above in the notation of the library.

<?decl Finsupp.sum_single?>
:::

**Theorem (Induction).** Let $M$ be an additive monoid and let $P$ be a property of the elements of $X \to_0 M$. Assume that $P(0)$ holds, and that $P(f)$ implies $P(\operatorname{single}(a, b) + f)$ for each $f$, each $a \notin \operatorname{supp}(f)$ and each $b \ne 0$. Then $P(f)$ holds for each $f \in X \to_0 M$.

*Proof.* Use induction on $n = |\operatorname{supp}(f)|$, for all $f$ with a support of this size at once. If $n = 0$, the support is empty, so $f(x) = 0$ for each $x$, and $f = 0$ by extensionality. Then $P(f)$ holds by the first hypothesis. Now let $n \ge 1$ and assume the statement for the supports of size $n - 1$. Pick $a \in \operatorname{supp}(f)$ and put $b = f(a)$, so $b \ne 0$. Let $f' = \operatorname{erase}(a, f)$. Its support is $\operatorname{supp}(f) \setminus \{a\}$, of size $n - 1$, so $P(f')$ holds by the induction hypothesis. Also $a \notin \operatorname{supp}(f')$. Compare the values of $\operatorname{single}(a, b) + f'$ and $f$. At $a$ the left side is $b + 0 = b = f(a)$. At $x \ne a$ the left side is $0 + f(x) = f(x)$. So $f = \operatorname{single}(a, b) + f'$ by extensionality, and the second hypothesis gives $P(f)$. $\square$

::: mathlib
`Finsupp.induction` · `Mathlib.Algebra.Group.Finsupp`

The principle of the theorem, with the motive `motive : (ι →₀ M) → Prop`. Use it with `induction f using Finsupp.induction with ...`. The forms `Finsupp.induction₂` (the single on the right) and `Finsupp.induction_linear` (the cases $0$, $f + g$ and $\operatorname{single}(a, b)$, with no condition on the supports) are often easier when the property is additive. The splitting of the proof is `Finsupp.erase_add_single`.

<?decl Finsupp.induction?>
:::

**Theorem (Finite domain).** Let $X$ be a finite set. Then the map that sends $f \in X \to_0 M$ to its underlying function $X \to M$ is a bijection onto the set of all functions $X \to M$.

*Proof.* The map is injective by extensionality. For surjectivity, let $\varphi : X \to M$ be any function. The set $\{x \in X : \varphi(x) \ne 0\}$ is a subset of the finite set $X$, so it is finite. So $\varphi$ is finitely supported, and it is the image of itself. $\square$

::: mathlib
`Finsupp.equivFunOnFinite` · `Mathlib.Data.Finsupp.Defs`

The equivalence `(α →₀ M) ≃ (α → M)` for `[Finite α]`. The inverse needs the support as a finset, and `Finite α` gives no list of the elements, so the inverse is built with classical logic. When a finset `s` that contains the support is at hand, `Finsupp.onFinset s φ h` builds the term directly, with `h : ∀ a, φ a ≠ 0 → a ∈ s`.

<?decl Finsupp.equivFunOnFinite?>
:::

### Examples

**Example (The values of single).** The function $\operatorname{single}(2, 5) \in \mathbb{N} \to_0 \mathbb{Z}$ has the value $5$ at $2$ and $0$ at $3$. Both facts come from the rule `Finsupp.single_apply`, and `simp` proves them.

<?lean MathlibHandbook/V03/C07/Examples.lean#single?>

**Example (A computation of a sum).** Let $f = \operatorname{single}(2, 5) + \operatorname{single}(3, -1) + \operatorname{single}(2, -5)$ in $\mathbb{N} \to_0 \mathbb{Z}$. At $2$ the value is $5 + 0 - 5 = 0$. At $3$ the value is $0 - 1 + 0 = -1$. At each other point the value is $0$. So $f = \operatorname{single}(3, -1)$ by extensionality, and $\operatorname{supp}(f) = \{3\}$. The union of the supports of the three terms is $\{2, 3\}$, so the support of the sum is smaller than the union.

**Example (Pointwise sum).** The value of a sum is the sum of the values.

<?lean MathlibHandbook/V03/C07/Examples.lean#add?>

**Example (Single is additive).** For a fixed point $a$, the map $b \mapsto \operatorname{single}(a, b)$ is additive: $\operatorname{single}(a, b + c) = \operatorname{single}(a, b) + \operatorname{single}(a, c)$. Compare the values: at $a$ both sides are $b + c$, and at $x \ne a$ both sides are $0$.

<?lean MathlibHandbook/V03/C07/Examples.lean#single_add?>

**Example (A support).** The support of $\operatorname{single}(2, 5)$ is $\{2\}$, by Theorem (Values and support of single) with $b = 5 \ne 0$.

<?lean MathlibHandbook/V03/C07/Examples.lean#support?>

**Example (Membership in the support).** The defining property of the support is the field `mem_support_toFun`, in the form of the lemma `Finsupp.mem_support_iff`.

<?lean MathlibHandbook/V03/C07/Examples.lean#mem_support?>

**Example (A polynomial).** The polynomial $p = 3 + 2X^5 - X^7$ with integer coefficients is the element $\operatorname{single}(0, 3) + \operatorname{single}(5, 2) + \operatorname{single}(7, -1)$ of $\mathbb{N} \to_0 \mathbb{Z}$. Its support $\{0, 5, 7\}$ is the set of the exponents that occur. The degree is the largest element of the support, $7$. The sum of two polynomials is the pointwise sum of the coefficients. For example $p + (X^7 + 1) = \operatorname{single}(0, 4) + \operatorname{single}(5, 2)$, of degree $5$: the term of degree $7$ cancels, so the support drops the point $7$.

**Example (A factorization).** The number $360 = 2^3 \cdot 3^2 \cdot 5$ gives the function $e = \operatorname{single}(2, 3) + \operatorname{single}(3, 2) + \operatorname{single}(5, 1)$ in $\mathbb{N} \to_0 \mathbb{N}$, with support $\{2, 3, 5\}$. The number $84 = 2^2 \cdot 3 \cdot 7$ gives $e' = \operatorname{single}(2, 2) + \operatorname{single}(3, 1) + \operatorname{single}(7, 1)$. The product $360 \cdot 84 = 30240 = 2^5 \cdot 3^3 \cdot 5 \cdot 7$ gives $e + e'$: the exponents add. Mathlib calls this function `Nat.factorization`, and the rule is `Nat.factorization_mul` for two nonzero numbers.

**Counterexample (A function with infinite support).** The constant function $\varphi(n) = 1$ on $\mathbb{N}$ is not in $\mathbb{N} \to_0 \mathbb{Z}$, because its support is all of $\mathbb{N}$. The function $\psi(n) = 1$ for $n$ even and $0$ for $n$ odd also fails. So the theorem (Finite domain) needs the hypothesis that $X$ is finite: for $X = \mathbb{N}$ the map $X \to_0 M \to (X \to M)$ is injective and not surjective.

### Common errors

1. A learner reads `f.support` as "the set where $f$ is defined". It is the set where $f$ is not zero. The function `f` is defined at every point.
2. A learner expects $\operatorname{supp}(f + g) = \operatorname{supp}(f) \cup \operatorname{supp}(g)$. Only the inclusion holds, as the example of the cancelling singles shows. The equality holds when the supports are disjoint (`Finsupp.support_add_eq`).
3. A learner writes `Finsupp.single a b` with `a` and `b` in the wrong order. The point comes first and the value second.
### The library around it

The file `Mathlib.Data.Finsupp.Defs` has the structure, the coercion to a function, `Finsupp.ext` and `Finsupp.ext_iff`, the zero function with `Finsupp.support_zero`, the tests of zero `Finsupp.support_eq_empty` and `Finsupp.support_nonempty_iff`, and the constructions `Finsupp.onFinset`, `Finsupp.mapRange` and `Finsupp.equivFunOnFinite`. Each construction comes with a rule `_apply` for the values and a rule `support_` for the support. The file `Mathlib.Data.Finsupp.Single` has `single`, `erase` and `update` with the same pattern: `Finsupp.single_apply`, `Finsupp.single_eq_same`, `Finsupp.single_eq_of_ne`, `Finsupp.single_zero`, `Finsupp.erase_same`, `Finsupp.erase_ne`, `Finsupp.support_erase`. The additive structure is in `Mathlib.Algebra.Group.Finsupp`, a file of the volume on groups: `Finsupp.add_apply`, `Finsupp.single_add`, `Finsupp.support_add` and the induction principles. For a family of value types that depends on the point, Mathlib has `DFinsupp`, with the notation `Π₀ i, M i`. The table at the end lists the declarations of this section.

### Exercises

1. (A) Give the support of `Finsupp.single 3 0 + Finsupp.single 4 1` in `ℕ →₀ ℤ`.
2. (A) Explain why the support of a sum $f + g$ can be smaller than the union of the supports, and give an example in $\mathbb{N} \to_0 \mathbb{Z}/2$ with $f \ne 0$ and $g \ne 0$.
3. (B) Show that $a \mapsto \operatorname{single}(a, b)$ is injective when $b \ne 0$, and that it is constant when $b = 0$.
4. (B) Show that $\operatorname{supp}(f + g) = \operatorname{supp}(f) \cup \operatorname{supp}(g)$ when the two supports are disjoint. Hint: at a point of $\operatorname{supp}(f)$, the value of $g$ is $0$.
5. (B) Let $M = \mathbb{N}$. Show that $\operatorname{supp}(f + g) = \operatorname{supp}(f) \cup \operatorname{supp}(g)$ for all $f, g$. Hint: in $\mathbb{N}$, a sum $m + n$ is $0$ only if $m = n = 0$.
6. (C) Let $X$ be infinite and let $M$ have an element $m \ne 0$. Show that $X \to_0 M$ is a proper subset of the set of all functions $X \to M$, and show that, for $X = \mathbb{N}$ and $M = \mathbb{Z}$, the set $\mathbb{N} \to_0 \mathbb{Z}$ is countable. Hint: map $f$ to the finite list of its values on $\{0, \ldots, N\}$, with $N$ the largest element of the support.
7. (L) Prove that the value of `single a b` at `a` is `b`. The solution is `single_eq_same_example`.
8. (L) Prove that the value of `single a b` at a point other than `a` is zero. The solution is `single_eq_of_ne_example`.
9. (L) Prove the rule of extensionality. The solution is `ext_example`.
10. (L) Prove that the zero function has an empty support. The solution is `support_zero_example`.

### Notes and history

The finitely supported functions from a set $X$ to a ring $R$ form the free $R$-module on $X$. In algebra this module is often written as the direct sum $\bigoplus_{x \in X} R$ or as $R^{(X)}$, as in Bourbaki, *Algèbre*, Chapter II, §1. The same construction with a monoid $X$ and the convolution product gives the monoid algebra $R[X]$, and with $X = \mathbb{N}$ it gives the polynomials. Lang, *Algebra*, Chapter III, §4, builds the free modules in this way.

In Mathlib the type `Finsupp` comes from the Lean 3 library, where Johannes Hölzl wrote the first version of `data.finsupp` in 2017. Mathlib uses `Finsupp` for the free modules and the coordinates in a basis, for `MvPolynomial` and for `Nat.factorization`. The type `Polynomial R` is built on `AddMonoidAlgebra R ℕ`, a structure with one field: its coefficients, a term of `ℕ →₀ R`.

### Reference

<?reference?>
