---
title: Aleph null and countable cardinals
kind: theory
modules:
  - Mathlib.SetTheory.Cardinal.Basic
explains:
  E3: [Cardinal.lt_aleph0, Cardinal.aleph0_le, Cardinal.mk_le_aleph0_iff, Cardinal.aleph0_mul_aleph0, Cardinal.mk_iUnion_le]
  E2: [Cardinal.lt_aleph0_iff_finite, Cardinal.infinite_iff, Cardinal.natCast_lt_aleph0, Cardinal.aleph0_add_aleph0, Cardinal.nat_mul_aleph0, Cardinal.mk_int, Cardinal.denumerable_iff, Cardinal.mk_iUnion_le_sum_mk, Cardinal.mk_union_le, Cardinal.mk_image_le, Cardinal.mk_range_le, Cardinal.mk_preimage_of_injective, Cardinal.isSuccLimit_aleph0, Cardinal.isStrongLimit_aleph0, Cardinal.powerlt, Cardinal.mk_list_eq_sum_pow, Cardinal.bddAbove_iff_small]
  E1: auto
families: []
requires: [V03.C04, V03.C05, V03.C08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Aleph null and countable cardinals

### Overview

The first infinite cardinal is $\aleph_0 = \#\mathbb{N}$. This section places it in the order of Section 2. The cardinals below $\aleph_0$ are exactly the natural numbers, and $\aleph_0$ is the least infinite cardinal. A type is countable if and only if its cardinal is at most $\aleph_0$. Then the arithmetic starts: $\aleph_0 \cdot \aleph_0 = \aleph_0$, so sums and products of finitely many copies of $\aleph_0$ collapse, and $a + 1 = a$ for each infinite $a$. The last part bounds the cardinals of images, unions and ranges. These bounds give the cardinal form of the theorem that a countable union of countable sets is countable.

Volume 3, Chapter 8 treats countable and denumerable types with explicit bijections. This section does not repeat those constructions. It uses them, and it states their content in the language of cardinals.

### Definitions

**Definition (Aleph null).** $\aleph_0$ is the cardinal of $\mathbb{N}$. In each universe $u$, $\aleph_0 = \mathrm{lift}\,\#\mathbb{N}$, since $\mathbb{N}$ lives in the lowest universe.

**Definition (Finite, countable and infinite cardinals).** For $n \in \mathbb{N}$, the cardinal $n$ is $\#\mathrm{Fin}\,n$, which agrees with the cast of $n$ into the semiring of Section 1. A cardinal $c$ is *finite* when $c = n$ for some $n$, *countable* when $c \le \aleph_0$, and *infinite* when $\aleph_0 \le c$.

**Definition (Weak power).** For cardinals $a$ and $b$, the weak power is $a^{<b} = \sup_{c < b} a^c$.

The supremum exists by Section 2, since the cardinals below $b$ form a small set.

### Theorems and proofs

**Proposition (The cast of natural numbers).** For $m, n \in \mathbb{N}$, $(m : \mathrm{Cardinal}) \le n$ if and only if $m \le n$. In particular the cast is injective.

*Proof.* If $m \le n$, the inclusion $\mathrm{Fin}\,m \hookrightarrow \mathrm{Fin}\,n$ is injective. If $m > n$, no map $\mathrm{Fin}\,m \to \mathrm{Fin}\,n$ is injective, by the pigeonhole principle of Volume 3, Chapter 4. $\square$

**Theorem (The cardinals below aleph null).** For a cardinal $c$, $c < \aleph_0$ if and only if $c = n$ for some $n \in \mathbb{N}$.

*Proof.* First, $n < \aleph_0$. The inclusion $\mathrm{Fin}\,n \hookrightarrow \mathbb{N}$ gives $n \le \aleph_0$. An injection $\mathbb{N} \to \mathrm{Fin}\,n$ restricts to an injection $\mathrm{Fin}(n+1) \to \mathrm{Fin}\,n$, which the pigeonhole principle forbids.

Conversely, let $c < \aleph_0$ and $c = \#\alpha$. An embedding $e : \alpha \hookrightarrow \mathbb{N}$ makes $\alpha$ equivalent to its range $S \subseteq \mathbb{N}$. Suppose that $S$ is infinite. Enumerate $S$ in increasing order: $s_0$ is the least element of $S$ and $s_{k+1}$ is the least element of $S$ above $s_k$, which exists because $S$ is infinite. The map $k \mapsto s_k$ is injective, so $\aleph_0 \le \#S = c$, against $c < \aleph_0$. So $S$ is finite, say with $n$ elements, and $S \simeq \mathrm{Fin}\,n$ gives $c = n$. $\square$

**Corollary (Aleph null is the least infinite cardinal).** For each cardinal $c$:

1. $\aleph_0 \le c$ if and only if $n \le c$ for each $n \in \mathbb{N}$;
2. $\#\alpha < \aleph_0$ if and only if $\alpha$ is finite, and $\aleph_0 \le \#\alpha$ if and only if $\alpha$ is infinite;
3. $\#\alpha \le \aleph_0$ if and only if $\alpha$ is countable;
4. $\aleph_0$ is a limit cardinal: it is not $0$, and $\mathrm{succ}\,x < \aleph_0$ for each $x < \aleph_0$.

*Proof.* For (1), if $\aleph_0 \le c$ then $n < \aleph_0 \le c$. If $c < \aleph_0$ then $c = n$ by the theorem, and $n + 1 \le c$ fails. Item (2) is the theorem with the fact that $\alpha \simeq \mathrm{Fin}\,n$ for some $n$ exactly when $\alpha$ is finite. A type is countable when it has an injection into $\mathbb{N}$, so (3) is the definition of $\le$. For (4), each $x < \aleph_0$ is some $n$, and $\mathrm{succ}\,n = n + 1 < \aleph_0$ by Section 2. $\square$

Item 2 is a dichotomy: each cardinal is finite or infinite. This uses the linear order, and so the axiom of choice.

**Theorem (Aleph null squared).** $\aleph_0 \cdot \aleph_0 = \aleph_0$.

*Proof.* Define $p : \mathbb{N} \times \mathbb{N} \to \mathbb{N}$ by $p(m, n) = 2^m (2n + 1) - 1$. The value $2^m(2n+1)$ is at least $1$, so $p$ takes values in $\mathbb{N}$. It is a bijection. Each integer $k \ge 1$ has a unique form $k = 2^m \cdot q$ with $q$ odd: $m$ is the number of times $2$ divides $k$, and $q = k / 2^m$. Write $q = 2n + 1$. So for each $j \in \mathbb{N}$ the equation $p(m, n) = j$, that is $2^m(2n+1) = j + 1$, has exactly one solution. Thus $\mathbb{N} \times \mathbb{N} \simeq \mathbb{N}$. $\square$

Volume 3, Chapter 8 uses the pairing function of Cantor in place of $p$. Any bijection gives the theorem.

**Corollary (Absorption).** For $n \ge 1$, $n \cdot \aleph_0 = \aleph_0$, $n + \aleph_0 = \aleph_0$ and $\aleph_0^n = \aleph_0$. Also $\aleph_0 + \aleph_0 = \aleph_0$, and $a + 1 = a$ for each infinite cardinal $a$.

*Proof.* Monotonicity gives $\aleph_0 \le n \cdot \aleph_0 \le \aleph_0 \cdot \aleph_0 = \aleph_0$, and $\aleph_0 \le n + \aleph_0 \le \aleph_0 + \aleph_0 = 2 \aleph_0 \le \aleph_0$. Induction on $n$ gives $\aleph_0^{n+1} = \aleph_0^n \cdot \aleph_0 = \aleph_0$. For $a = \#\alpha$ infinite, $\aleph_0 \le a$ gives an injection $j : \mathbb{N} \to \alpha$. Define $h : \alpha \oplus \mathrm{Unit} \to \alpha$ by $h(\star) = j(0)$, $h(j(k)) = j(k + 1)$, and $h(x) = x$ for $x$ outside the range of $j$. This map is a bijection, so $a + 1 = a$. $\square$

The map $h$ is Hilbert's hotel. The rule $a + b = \max(a, b)$ for infinite $a$ or $b$, and $a \cdot a = a$ for each infinite $a$, need more work. Chapter 3 proves them.

**Theorem (Unions, images and ranges).** Let $\alpha$ and $\iota$ be types of universe $u$.

1. For sets $A_i \subseteq \alpha$, $\#\bigcup_i A_i \le \sum_i \#A_i \le \#\iota \cdot \sup_i \#A_i$.
2. For $S, T \subseteq \alpha$, $\#(S \cup T) \le \#S + \#T$.
3. For $f : \alpha \to \beta$ and $S \subseteq \alpha$, $\#f[S] \le \#S$ and $\#\mathrm{range}\,f \le \#\alpha$.
4. For an injective $f : \alpha \to \beta$ and $T \subseteq \beta$, $\#f^{-1}[T] \le \#T$.

*Proof.* (1) The map $\Sigma i, A_i \to \bigcup_i A_i$, $\langle i, x\rangle \mapsto x$, is surjective. A surjection $\sigma : X \to Y$ has a right inverse by choice, and the right inverse is injective, so $\#Y \le \#X$. This gives the first inequality, since $\#(\Sigma i, A_i) = \sum_i \#A_i$. For the second, let $m = \sup_i \#A_i$, which exists by Section 2, and fix a type $M$ with $\#M = m$. Choose embeddings $A_i \hookrightarrow M$. They give an embedding $\Sigma i, A_i \hookrightarrow \iota \times M$. (2) is (1) for the family indexed by $\mathrm{Bool}$, in the form with the sum. (3) The maps $S \to f[S]$ and $\alpha \to \mathrm{range}\,f$ are surjective. (4) The map $f$ restricts to an injection $f^{-1}[T] \to T$. $\square$

**Corollary (Countable unions).** If $\iota$ is countable and each $A_i$ is countable, then $\bigcup_i A_i$ is countable.

*Proof.* By (1), $\#\bigcup_i A_i \le \#\iota \cdot \sup_i \#A_i \le \aleph_0 \cdot \aleph_0 = \aleph_0$. $\square$

The proof uses choice twice: for the right inverse, and for the embeddings $A_i \hookrightarrow M$. Without choice, a countable union of countable sets need not be countable.

### Examples

**Example (Integers and lists).** The map $\mathrm{inl}\,n \mapsto n$, $\mathrm{inr}\,n \mapsto -(n+1)$ is a bijection $\mathbb{N} \oplus \mathbb{N} \to \mathbb{Z}$, so $\#\mathbb{Z} = \aleph_0 + \aleph_0 = \aleph_0$. For lists, splitting by length gives $\mathrm{List}\,\alpha \simeq \Sigma n, (\mathrm{Fin}\,n \to \alpha)$, so $\#\mathrm{List}\,\alpha = \sum_n \#\alpha^n$. For $\alpha = \mathbb{N}$ the terms are $\aleph_0^0 = 1$ and $\aleph_0^n = \aleph_0$ for $n \ge 1$. So
$$\#\mathrm{List}\,\mathbb{N} = 1 + \sum_{n \ge 1} \aleph_0 = 1 + \aleph_0 \cdot \aleph_0 = \aleph_0.$$

**Example (A weak power).** $2^{<\aleph_0} = \sup_n 2^n = \aleph_0$. Each $2^n$ is finite, so the supremum is at most $\aleph_0$. It is at least each $n$, since $n < 2^n$, so it is at least $\aleph_0$. In contrast, $2^{\aleph_0}$ is uncountable by Cantor. So $a^{<b}$ and $a^b$ differ at $b = \aleph_0$.

**Counterexample (Preimages need injectivity).** The bound $\#f^{-1}[T] \le \#T$ fails without injectivity. Let $f : \mathbb{N} \to \mathrm{Unit}$ be the constant map and $T = \mathrm{Unit}$. Then $f^{-1}[T] = \mathbb{N}$, with cardinal $\aleph_0 > 1 = \#T$. Images behave the other way: $\#f[S] \le \#S$ holds for each $f$.

**Counterexample (The union bound is not an equality).** Let $A_n = \{0\} \subseteq \mathbb{N}$ for each $n \in \mathbb{N}$. Then $\sum_n \#A_n = \aleph_0$, but $\bigcup_n A_n = \{0\}$ has cardinal $1$. The bound counts the overlaps again. It is an equality for pairwise disjoint sets.

### The library around it

::: mathlib
`Cardinal.lt_aleph0` · `Mathlib.SetTheory.Cardinal.Basic`

`lt_aleph0 {c : Cardinal} : c < ℵ₀ ↔ ∃ n : ℕ, c = n`. The definition `Cardinal.aleph0` is in `Mathlib.SetTheory.Cardinal.Defs`, as `lift #ℕ`, with notation `ℵ₀` in the `Cardinal` scope. For types, `Cardinal.lt_aleph0_iff_finite` gives `#α < ℵ₀ ↔ Finite α`, and `Cardinal.infinite_iff` gives `Infinite α ↔ ℵ₀ ≤ #α`. The lemma `Cardinal.natCast_lt_aleph0` is `(n : Cardinal) < ℵ₀`.

<?decl Cardinal.lt_aleph0?>
:::

::: mathlib
`Cardinal.aleph0_le` · `Mathlib.SetTheory.Cardinal.Basic`

`aleph0_le {c : Cardinal} : ℵ₀ ≤ c ↔ ∀ n : ℕ, ↑n ≤ c`. The limit properties are `Cardinal.isSuccLimit_aleph0` and `Cardinal.isStrongLimit_aleph0`.

<?decl Cardinal.aleph0_le?>
:::

::: mathlib
`Cardinal.mk_le_aleph0_iff` · `Mathlib.SetTheory.Cardinal.Basic`

`mk_le_aleph0_iff : #α ≤ ℵ₀ ↔ Countable α`. The class `Countable α` of Volume 3, Chapter 8 asks for an injection into `ℕ`, so the proof is a rewrite with `Cardinal.lift_mk_le'`. The equality case is `Cardinal.denumerable_iff : Nonempty (Denumerable α) ↔ #α = ℵ₀`.

<?decl Cardinal.mk_le_aleph0_iff?>
:::

::: mathlib
`Cardinal.aleph0_mul_aleph0` · `Mathlib.SetTheory.Cardinal.Basic`

`aleph0_mul_aleph0 : ℵ₀ * ℵ₀ = ℵ₀`. The proof is `mk_denumerable _`: the instance `Denumerable (ℕ × ℕ)` from Volume 3 gives the bijection. In the same way `Cardinal.aleph0_add_aleph0` and `Cardinal.mk_int` come from instances. The variant `Cardinal.nat_mul_aleph0` needs `n ≠ 0`. The rule `a + 1 = a` for infinite `a` is `Cardinal.add_one_of_aleph0_le`, in `Mathlib.SetTheory.Ordinal.Arithmetic`.

<?decl Cardinal.aleph0_mul_aleph0?>
:::

::: mathlib
`Cardinal.mk_iUnion_le` · `Mathlib.SetTheory.Cardinal.Basic`

`mk_iUnion_le {α ι : Type u} (f : ι → Set α) : #(⋃ i, f i) ≤ #ι * ⨆ i, #(f i)`. The proof goes through `Cardinal.mk_iUnion_le_sum_mk`, the first inequality of the theorem. The neighbours are `Cardinal.mk_union_le`, `Cardinal.mk_image_le`, `Cardinal.mk_range_le` and `Cardinal.mk_preimage_of_injective`. Variants with `_lift` allow `ι` and `α` in different universes.

<?decl Cardinal.mk_iUnion_le?>
:::

The weak power `Cardinal.powerlt a b` has the notation `a ^< b`. The lemma `Cardinal.mk_list_eq_sum_pow` is the computation for lists above. The module also has `Cardinal.bddAbove_iff_small`, used in Section 2.

Common errors of a learner:

- `ℵ₀` needs `open Cardinal`. Its type is `Cardinal.{u}` for a universe that Lean infers, and a mismatch shows up as a `lift` in the goal.
- For a set `s : Set α`, `#s` is the cardinal of the subtype. The lemma `Cardinal.le_aleph0_iff_set_countable` links `#s ≤ ℵ₀` to `s.Countable`.
- `mk_iUnion_le` gives the bound with a supremum. When the family is not bounded, the supremum is junk, but for `ι : Type u` and sets of `α : Type u` the family is always bounded.
- `Infinite α` and `ℵ₀ ≤ #α` are the same statement, but Lean does not see this without `Cardinal.infinite_iff`.

### Exercises

1. (A) Show $\#\mathbb{N}^{+} = \aleph_0$ and $\#(\mathbb{N} \oplus \mathrm{Fin}\,5) = \aleph_0$ with explicit bijections.
2. (A) Show that $a + n = a$ for each infinite $a$ and each $n \in \mathbb{N}$.
3. (A) Show $\#\mathbb{Q} \le \aleph_0$ using $\#\mathbb{Z} = \aleph_0$, $\aleph_0 \cdot \aleph_0 = \aleph_0$ and a surjection $\mathbb{Z} \times \mathbb{N} \to \mathbb{Q}$.
4. (B) Show that the set of finite subsets of $\mathbb{N}$ has cardinal $\aleph_0$. Hint: a finite subset is the range of a list.
5. (B) Show that the set of algebraic real numbers is countable. Hint: each nonzero polynomial with integer coefficients has finitely many roots, and the polynomials are indexed by lists.
6. (B) Show that $2^{<b} \le 2^b$ for each $b$, and compute $\aleph_0^{<\aleph_0}$.
7. (C) Show that a type $\alpha$ is infinite if and only if $\#\alpha = \#\alpha + 1$. Explain why the direction from right to left holds without choice, while the proof above of the other direction used the injection $j$.

### Notes and history

Cantor introduced the symbol $\aleph_0$ in 1895. He proved the countability of the algebraic numbers in 1874. The use of choice in the theorem on countable unions was noticed later: there are models of ZF in which the real numbers are a countable union of countable sets, a result of Feferman and Lévy. Jech, *Set Theory*, Chapter 3, gives the ZFC treatment. Volume 3, Chapter 8 gives the constructions behind each bijection of this section.

### Reference

<?reference?>
