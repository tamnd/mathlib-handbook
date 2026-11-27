---
title: Finite cardinals and conversions
kind: theory
modules:
  - Mathlib.SetTheory.Cardinal.Finite
  - Mathlib.SetTheory.Cardinal.NatCard
  - Mathlib.SetTheory.Cardinal.ToNat
  - Mathlib.SetTheory.Cardinal.ENat
  - Mathlib.SetTheory.Cardinal.NatCount
explains:
  E3: [Cardinal.toNat, Cardinal.toENat, ENat.card, Cardinal.toNat_mk, Cardinal.toNat_add]
  E2: [Cardinal.ofENat, Cardinal.enat_gc, Cardinal.ofENat_toENat_eq_self, Cardinal.range_ofENat, Cardinal.toENat_mk, Cardinal.toNat_eq_zero, Cardinal.cast_toNat_of_lt_aleph0, Cardinal.toNat_mul, Cardinal.aleph0_toNat, Cardinal.toNat_lift, ENat.card_eq_top, ENat.card_fun, Nat.card_eq_zero, Nat.card_prod, Nat.card_sum, Nat.card_fun, Nat.cast_card, Finite.equivFin, Nat.card_eq, Nat.count_le_cardinal]
  E1: auto
families: []
requires: [V03.C04, V03.C05, V04.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Finite cardinals and conversions

### Overview

A finite type has three counts in Mathlib. Its cardinal $\#\alpha$ is exact but lives in a large type. The natural number `Nat.card α` is easy to compute with, but it has the value $0$ on infinite types. The extended natural number `ENat.card α` has the value $\infty$ on infinite types. This section defines the maps between the three codomains:
$$\mathbb{N}^{\infty} \xrightarrow{\ \mathrm{ofENat}\ } \mathrm{Cardinal}, \qquad \mathrm{Cardinal} \xrightarrow{\ \mathrm{toENat}\ } \mathbb{N}^{\infty} \xrightarrow{\ \mathrm{toNat}\ } \mathbb{N}.$$
It proves that `toENat` is a homomorphism of ordered semirings and the right adjoint of `ofENat`, and it gives the exact rules for `toNat`, which is multiplicative but only additive on finite cardinals.

Volume 3, Chapter 5 introduced `Nat.card`, `Set.ncard` and `Set.encard` and their use for finite sets. This section explains their definition through cardinals and the source of each hypothesis of finiteness.

### Definitions

**Definition (From extended naturals to cardinals).** $\mathrm{ofENat} : \mathbb{N}^{\infty} \to \mathrm{Cardinal}$ sends $n \in \mathbb{N}$ to the cardinal $n$ and $\infty$ to $\aleph_0$.

**Definition (From cardinals to extended naturals).** $\mathrm{toENat} : \mathrm{Cardinal} \to \mathbb{N}^{\infty}$ sends a finite cardinal $n$ to $n$ and each infinite cardinal to $\infty$.

The definition is complete, since each cardinal is finite or infinite (Section 3).

**Definition (From cardinals to naturals).** $\mathrm{toNat}\,c = \mathrm{toNat}^{\infty}(\mathrm{toENat}\,c)$, where $\mathrm{toNat}^{\infty} : \mathbb{N}^{\infty} \to \mathbb{N}$ sends $n$ to $n$ and $\infty$ to $0$. So $\mathrm{toNat}\,n = n$ and $\mathrm{toNat}\,c = 0$ for infinite $c$.

**Definition (Counts of a type).** For a type $\alpha$, $\mathrm{Nat.card}\,\alpha = \mathrm{toNat}\,\#\alpha$ and $\mathrm{ENat.card}\,\alpha = \mathrm{toENat}\,\#\alpha$.

### Theorems and proofs

**Proposition (ofENat).** The map $\mathrm{ofENat}$ is strictly monotone, and its range is the set of cardinals $c$ with $c \le \aleph_0$.

*Proof.* On $\mathbb{N}$ it is the cast, which is strictly monotone by Section 3. For $n \in \mathbb{N}$, $\mathrm{ofENat}\,n = n < \aleph_0 = \mathrm{ofENat}\,\infty$. So the map is strictly monotone. Each value is at most $\aleph_0$. Conversely, if $c \le \aleph_0$, then $c < \aleph_0$ and $c = n$ for some $n$, or $c = \aleph_0$. $\square$

**Theorem (Galois connection).** For $m \in \mathbb{N}^{\infty}$ and a cardinal $c$,
$$\mathrm{ofENat}\,m \le c \iff m \le \mathrm{toENat}\,c.$$
Also $\mathrm{toENat}(\mathrm{ofENat}\,m) = m$, and $\mathrm{ofENat}(\mathrm{toENat}\,c) = c$ if and only if $c \le \aleph_0$.

*Proof.* Suppose first that $c$ is infinite. Then $\mathrm{toENat}\,c = \infty$, so the right side holds. The left side holds too, since $\mathrm{ofENat}\,m \le \aleph_0 \le c$. Suppose now that $c = n$ is finite. If $m = \infty$, the left side says $\aleph_0 \le n$ and the right side says $\infty \le n$. Both are false. If $m \in \mathbb{N}$, both sides say $m \le n$, by Section 3. The equality $\mathrm{toENat}(\mathrm{ofENat}\,m) = m$ holds for $m \in \mathbb{N}$ by definition, and for $m = \infty$ because $\aleph_0$ is infinite. Last, $\mathrm{ofENat}(\mathrm{toENat}\,c)$ is $c$ for finite $c$ and $\aleph_0$ for infinite $c$, and this equals $c$ exactly when $c \le \aleph_0$. $\square$

A Galois connection in which the left adjoint is injective is a Galois coinsertion, in the sense of Volume 4, Chapter 6. The composite $c \mapsto \mathrm{ofENat}(\mathrm{toENat}\,c)$ is $c \mapsto \min(c, \aleph_0)$.

**Theorem (toENat is a homomorphism).** The map $\mathrm{toENat}$ is monotone, sends $0$ to $0$ and $1$ to $1$, and for all cardinals $c$, $d$,
$$\mathrm{toENat}(c + d) = \mathrm{toENat}\,c + \mathrm{toENat}\,d, \qquad \mathrm{toENat}(c \cdot d) = \mathrm{toENat}\,c \cdot \mathrm{toENat}\,d.$$

*Proof.* Monotonicity follows from the Galois connection: the right adjoint of a Galois connection is monotone. By symmetry assume $c \le d$. If $d$ is finite, both are natural numbers and the sum and the product in the cardinals agree with those in $\mathbb{N}$, by the equivalences $\mathrm{Fin}\,m \oplus \mathrm{Fin}\,n \simeq \mathrm{Fin}(m + n)$ and $\mathrm{Fin}\,m \times \mathrm{Fin}\,n \simeq \mathrm{Fin}(mn)$. Suppose $d$ is infinite. Then $c + d \ge d$ is infinite, so both sides of the first equation are $\infty$. For the product, if $c = 0$ then $c \cdot d = 0$, and in $\mathbb{N}^{\infty}$ also $0 \cdot \infty = 0$. If $c \ne 0$, then $c \cdot d \ge 1 \cdot d$ is infinite, and both sides are $\infty$. $\square$

The proof uses the convention $0 \cdot \infty = 0$ in $\mathbb{N}^{\infty}$. It matches $0 \cdot \aleph_0 = 0$, since a product with an empty factor is empty.

**Corollary (Rules for toNat).** For all cardinals $c$, $d$:

1. $\mathrm{toNat}(c \cdot d) = \mathrm{toNat}\,c \cdot \mathrm{toNat}\,d$;
2. $\mathrm{toNat}\,c = 0$ if and only if $c = 0$ or $\aleph_0 \le c$;
3. if $c < \aleph_0$ and $d < \aleph_0$, then $\mathrm{toNat}(c + d) = \mathrm{toNat}\,c + \mathrm{toNat}\,d$;
4. if $c < \aleph_0$, then the cast of $\mathrm{toNat}\,c$ is $c$.

*Proof.* (1) The map $\mathrm{toNat}^{\infty}$ is multiplicative: if both factors are finite this is clear. If one factor is $\infty$ and the other is $0$, the product is $0$ and both sides are $0$. If one is $\infty$ and the other is not $0$, the product is $\infty$, and both sides are $0$. Compose with the theorem. (2) $\mathrm{toNat}^{\infty}\,m = 0$ exactly when $m = 0$ or $m = \infty$, and $\mathrm{toENat}\,c = 0$ exactly when $c = 0$. (3) Both cardinals are natural numbers, and the cast is additive. (4) $c = n$ and $\mathrm{toNat}\,n = n$. $\square$

**Proposition (Counts of types).** For types $\alpha$ and $\beta$:

1. $\mathrm{Nat.card}\,\alpha = 0$ if and only if $\alpha$ is empty or infinite;
2. $\mathrm{Nat.card}(\alpha \times \beta) = \mathrm{Nat.card}\,\alpha \cdot \mathrm{Nat.card}\,\beta$;
3. if $\alpha$ and $\beta$ are finite, $\mathrm{Nat.card}(\alpha \oplus \beta) = \mathrm{Nat.card}\,\alpha + \mathrm{Nat.card}\,\beta$;
4. if $\alpha$ is finite, $\mathrm{Nat.card}(\alpha \to \beta) = (\mathrm{Nat.card}\,\beta)^{\mathrm{Nat.card}\,\alpha}$;
5. $\mathrm{ENat.card}\,\alpha = \infty$ if and only if $\alpha$ is infinite, and $\mathrm{ENat.card}$ turns sums, products and function types into $+$, $\cdot$ and powers in $\mathbb{N}^{\infty}$, with no hypothesis.

*Proof.* Items 1 to 3 are the corollary applied to $\#\alpha$ and $\#\beta$, with $\#\alpha = 0$ if and only if $\alpha$ is empty and $\#\alpha < \aleph_0$ if and only if $\alpha$ is finite. For item 4, let $\mathrm{Nat.card}\,\alpha = n$. If $\beta$ is finite with $m$ elements, $(\alpha \to \beta) \simeq (\mathrm{Fin}\,n \to \mathrm{Fin}\,m)$ has $m^n$ elements. If $\beta$ is infinite and $n \ge 1$, then $\alpha \to \beta$ is infinite, and both sides are $0$ since $0^n = 0$. If $n = 0$, then $\alpha$ is empty, and both sides are $1$. Item 5 follows from the theorem for sums and products. For function types, $\mathbb{N}^{\infty}$ has $a^{\infty} = \infty$ for $a \ge 2$, $1^{\infty} = 1$ and $0^{\infty} = 0$, and these values match the cardinal powers. $\square$

**Proposition (Finite types).** If $\alpha$ is finite, then $\alpha \simeq \mathrm{Fin}(\mathrm{Nat.card}\,\alpha)$, the cast of $\mathrm{Nat.card}\,\alpha$ is $\#\alpha$, and $\mathrm{Nat.card}\,\alpha$ equals $\mathrm{Fintype.card}\,\alpha$ for each `Fintype` structure on $\alpha$. For finite $\alpha$ and $\beta$, $\mathrm{Nat.card}\,\alpha = \mathrm{Nat.card}\,\beta$ if and only if $\alpha \simeq \beta$.

*Proof.* A finite type has an equivalence $\alpha \simeq \mathrm{Fin}\,n$ for some $n$. Then $\#\alpha = n$, and $\mathrm{Nat.card}\,\alpha = \mathrm{toNat}\,n = n$. A `Fintype` structure counts the elements of a list without repetition that covers $\alpha$, and this number is also $n$, by Volume 3, Chapter 4. For the last claim, both types are equivalent to $\mathrm{Fin}$ of their counts. $\square$

### Examples

**Example (A computation through the conversions).** Let $\alpha = \mathrm{Fin}\,3 \to \mathrm{Bool}$. The domain is finite, so item 4 gives $\mathrm{Nat.card}\,\alpha = 2^3 = 8$. Through cardinals, $\#\alpha = 2^3 = 8$ by Section 1, and $\mathrm{toNat}\,8 = 8$. Through $\mathbb{N}^{\infty}$, $\mathrm{ENat.card}\,\alpha = 2^3 = 8$. For $\beta = \mathbb{N} \times \mathrm{Fin}\,0$, item 2 gives $\mathrm{Nat.card}\,\beta = 0 \cdot 0 = 0$, which is correct since $\beta$ is empty. For $\gamma = \mathbb{N} \times \mathrm{Fin}\,2$, it gives $0 \cdot 2 = 0$, correct since $\gamma$ is infinite.

**Counterexample (Additivity needs finiteness).** Let $c = \aleph_0$ and $d = 1$. Then $c + d = \aleph_0$, so $\mathrm{toNat}(c + d) = 0$, while $\mathrm{toNat}\,c + \mathrm{toNat}\,d = 0 + 1 = 1$. For types, $\mathrm{Nat.card}(\mathbb{N} \oplus \mathrm{Unit}) = 0 \ne 1 = \mathrm{Nat.card}\,\mathbb{N} + \mathrm{Nat.card}\,\mathrm{Unit}$. Products survive because the junk value $0$ absorbs everything in a product. Sums do not.

**Counterexample (Function types need a finite domain).** Let $\alpha = \mathbb{N}$ and $\beta = \mathrm{Bool}$. Then $\alpha \to \beta$ is infinite, so $\mathrm{Nat.card}(\alpha \to \beta) = 0$. The formula would give $2^{\mathrm{Nat.card}\,\mathbb{N}} = 2^0 = 1$. In $\mathbb{N}^{\infty}$ the formula holds: $\mathrm{ENat.card}(\mathbb{N} \to \mathrm{Bool}) = \infty = 2^{\infty}$.

### The library around it

::: mathlib
`Cardinal.toNat` · `Mathlib.SetTheory.Cardinal.ToNat`

`toNat : Cardinal →*₀ ℕ`, defined as `ENat.toNatHom.comp toENat`. It is a bundled homomorphism of monoids with zero, so `Cardinal.toNat_mul` holds with no hypothesis. The junk value is described by `Cardinal.toNat_eq_zero : toNat c = 0 ↔ c = 0 ∨ ℵ₀ ≤ c` and `Cardinal.aleph0_toNat`. The lemma `Cardinal.cast_toNat_of_lt_aleph0` recovers a finite cardinal, and `Cardinal.toNat_lift` shows that lifts do not change the value.

<?decl Cardinal.toNat?>
:::

::: mathlib
`Cardinal.toNat_add` · `Mathlib.SetTheory.Cardinal.ToNat`

`toNat_add (hc : c < ℵ₀) (hd : d < ℵ₀) : toNat (c + d) = toNat c + toNat d`. The two hypotheses are the ones of the counterexample. A proof that uses `Nat.card` of a sum must provide them, usually as instances `Finite α` and `Finite β`, as in `Nat.card_sum`.

<?decl Cardinal.toNat_add?>
:::

::: mathlib
`Cardinal.toENat` · `Mathlib.SetTheory.Cardinal.ENat`

`toENat : Cardinal →+*o ℕ∞`, a bundled homomorphism of ordered semirings. Its left adjoint is the coercion `Cardinal.ofENat`, with `ofENat ⊤ = ℵ₀`. The Galois connection is `Cardinal.enat_gc : GaloisConnection (↑) toENat`, and `Cardinal.gciENat` is the coinsertion. The lemmas `Cardinal.ofENat_toENat_eq_self : toENat a = a ↔ a ≤ ℵ₀` and `Cardinal.range_ofENat : range ofENat = Iic ℵ₀` are the last part of the theorem and the proposition on `ofENat`.

<?decl Cardinal.toENat?>
:::

::: mathlib
`Cardinal.toNat_mk` · `Mathlib.SetTheory.Cardinal.Finite`

`toNat_mk (α) : (mk α).toNat = Nat.card α`, proved by `rfl`: `Nat.card α` is defined as `toNat (mk α)`. The simplifier uses the lemma to turn a goal about cardinals into a goal about `Nat.card`. The lemma `Cardinal.toENat_mk` does the same for `ENat.card`. The rules of the proposition on counts are `Nat.card_eq_zero`, `Nat.card_prod`, `Nat.card_sum` and `Nat.card_fun`, and `Nat.cast_card` says `(Nat.card α : Cardinal) = #α` for finite `α`.

<?decl Cardinal.toNat_mk?>
:::

::: mathlib
`ENat.card` · `Mathlib.SetTheory.Cardinal.Finite`

`ENat.card α : ℕ∞` is `toENat (mk α)`. Its lemmas need no finiteness: `ENat.card_eq_top : card α = ⊤ ↔ Infinite α`, and `ENat.card_fun : card (α → β) = card β ^ card α`. `Set.encard s` of Volume 3 is `ENat.card s`.

<?decl ENat.card?>
:::

::: mathlib
`Finite.equivFin` · `Mathlib.SetTheory.Cardinal.NatCard`

`Finite.equivFin (α) [Finite α] : α ≃ Fin (Nat.card α)`. It is noncomputable, since `Finite α` is a proposition. The lemma `Nat.card_eq` states `Nat.card α = if Finite α then Fintype.card α else 0` with the classical `Fintype` instance.

<?decl Finite.equivFin?>
:::

The module `Mathlib.SetTheory.Cardinal.NatCount` links `Nat.count p n`, the number of `k < n` with `p k`, to cardinals. The lemma `Nat.count_le_cardinal` states `(count p n : Cardinal) ≤ #{k | p k}`, and the variants for `Set.encard` and `Set.ncard` follow from it.

Common errors of a learner:

- `Nat.card α = 0` does not mean that `α` is empty. Check `Finite α` first, or use `ENat.card`.
- A rewrite with `Nat.card_sum` leaves goals `Finite α` and `Finite β`. Without them the lemma does not apply, and the statement is false in general.
- `toNat` and `toENat` are bundled maps, so `map_add` and `map_mul` apply to `toENat`. The coercion from `ℕ∞` to `Cardinal` is `ofENat`, and `push_cast` moves it through sums and products.
- In `ℕ∞`, `0 * ⊤ = 0`. A proof by cases on `⊤` must treat the factor `0` apart.

### Exercises

1. (A) Compute $\mathrm{Nat.card}$, $\mathrm{ENat.card}$ and $\#$ of $\mathrm{Fin}\,2 \times \mathrm{Fin}\,5$, of $\mathbb{Z}$, and of $\mathrm{Fin}\,0 \to \mathbb{N}$.
2. (A) Show that $\mathrm{toNat}$ is strictly monotone on the cardinals below $\aleph_0$ and that it is not monotone on all cardinals.
3. (A) Show that $\mathrm{toENat}\,c = 0$ if and only if $c = 0$, and that $\mathrm{toNat}\,c = 1$ if and only if $c = 1$.
4. (B) Show that $\mathrm{toNat}(c^n) = (\mathrm{toNat}\,c)^n$ for each cardinal $c$ and each $n \in \mathbb{N}$. Find $c$ and $d$ with $\mathrm{toNat}(c^d) \ne (\mathrm{toNat}\,c)^{\mathrm{toNat}\,d}$.
5. (B) Show that $\mathrm{Nat.card}\,\alpha \le \mathrm{Nat.card}\,\beta$ for an embedding $\alpha \hookrightarrow \beta$ with $\beta$ finite. Give an example with $\beta$ infinite where the inequality fails.
6. (B) Show that $\mathrm{ofENat}$ is a homomorphism of semirings, using that $\aleph_0 + n = \aleph_0 \cdot \aleph_0 = \aleph_0$.
7. (C) Let $p$ be a predicate on $\mathbb{N}$. Show that $\{k : p\,k\}$ is infinite if and only if the number of $k < n$ with $p\,k$ is unbounded in $n$. State the result with $\mathrm{Nat.count}$ and $\mathrm{ENat.card}$.

### Notes and history

The values $0$ of `Nat.card` and $\infty$ of `ENat.card` on infinite types are design choices of Mathlib. They make each count a total function, in the same way as division by zero in a field. The conventions of the textbooks differ: most texts leave the number of elements of an infinite set undefined. The identity $0 \cdot \infty = 0$ in $\mathbb{N}^{\infty}$ is the convention of measure theory too.

### Reference

<?reference?>
