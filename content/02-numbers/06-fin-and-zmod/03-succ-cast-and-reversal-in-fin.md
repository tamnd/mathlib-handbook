---
title: Successor, cast and reversal in Fin n
kind: api
modules:
  - Mathlib.Data.Fin.SuccPred
  - Mathlib.Data.Fin.SuccPredOrder
  - Mathlib.Data.Fin.Rev
  - Mathlib.Data.Fin.Embedding
  - Mathlib.Data.Fin.EquivOfInjective
  - Mathlib.Data.Fin.Pigeonhole
  - Mathlib.Data.Fin.Parity
  - Mathlib.Data.Fin.FlagRange
  - Mathlib.Data.Fin.Init
  - Mathlib.Data.Fin.Fin2
explains:
  E2: [Fin.succAbove, Fin.range_succAbove, Fin.predAbove, Fin.succAbove_predAbove, Fin.add_rev_cast, Fin.nonempty_embedding_iff, Fin.le_of_injective, Fin.even_iff]
  E1: auto
families: []
requires: [V02.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Successor, cast and reversal in Fin n

### Overview

Section 1 defined `Fin n` as the set $\{0, 1, \dots, n - 1\}$ and used it as a type of indices. An index of a list of length $n + 1$ often comes from an index of a list of length $n$. There are several ways to send $\operatorname{Fin}(n)$ into $\operatorname{Fin}(n + 1)$: add one, keep the value, or skip one chosen value. There are also maps back, the predecessors. This section describes these maps, the reversal $i \mapsto n - 1 - i$, and the embeddings between `Fin` types that they give.

The modules of this section also hold the pigeonhole principle for maps between `Fin` types, the parity of elements of `Fin n`, the range of a tuple as a maximal chain, and `Fin2`, an inductive copy of `Fin n`. The next section uses all of these maps to add and remove entries of tuples.

### The library around it

#### The basic maps

Lean core defines the maps of this table. The module `Mathlib.Data.Fin.SuccPred` proves most of the lemmas about them. Each map keeps the order, and each map is injective: see `Fin.succ_injective`, `Fin.castSucc_injective` and `Fin.castLE_injective`.

| Map | Type | Value |
|---|---|---|
| `Fin.succ` | $\operatorname{Fin}(n) \to \operatorname{Fin}(n + 1)$ | $i \mapsto i + 1$ |
| `Fin.castSucc` | $\operatorname{Fin}(n) \to \operatorname{Fin}(n + 1)$ | $i \mapsto i$ |
| `Fin.last` | an element of $\operatorname{Fin}(n + 1)$ | $n$ |
| `Fin.castLE` | $\operatorname{Fin}(n) \to \operatorname{Fin}(m)$ for $n \leq m$ | $i \mapsto i$ |
| `Fin.castAdd` | $\operatorname{Fin}(n) \to \operatorname{Fin}(n + m)$ | $i \mapsto i$ |
| `Fin.addNat` | $\operatorname{Fin}(n) \to \operatorname{Fin}(n + m)$ | $i \mapsto i + m$ |
| `Fin.natAdd` | $\operatorname{Fin}(m) \to \operatorname{Fin}(n + m)$ | $i \mapsto n + i$ |
| `Fin.cast` | $\operatorname{Fin}(n) \to \operatorname{Fin}(m)$ for $n = m$ | $i \mapsto i$ |

The images of the first two maps are complements of one point. The lemma `Fin.range_succ` says that the range of `Fin.succ` is $\{0\}^c$, and `Fin.range_castSucc` says that the range of `Fin.castSucc` is the set of $i$ with $i < n$. The lemma `Fin.exists_succ_eq` says that $x$ is a successor if and only if $x \neq 0$.

The map `Fin.cast` changes the type and not the value. It is needed because `Fin (n + 0)` and `Fin n` are equal types only after a proof. The equivalence form is `finCongr`, with `finCongr_apply`. The lemma `Fin.cast_eq_cast` compares `Fin.cast` with the general `cast`, and `finCongr_eq_equivCast` does the same for equivalences. A good rule: use `Fin.cast` and `finCongr`, because their simp lemmas compute the value.

The predecessors go back. `Fin.pred i h` needs `h : i ≠ 0` and gives $i - 1$. `Fin.castPred i h` needs `h : i ≠ Fin.last n` and gives $i$ in $\operatorname{Fin}(n)$. The cancellation lemmas are `Fin.castPred_castSucc` and `Fin.castSucc_castPred`, and the value lemma is `Fin.coe_castPred`. The order lemmas have the form `Fin.pred_lt_iff` and `Fin.castPred_lt_castPred_iff`: an inequality after the map is the same as an inequality before it, with `Fin.succ` or `Fin.castSucc` on the other side. The lemma `Fin.castLT_eq_castPred` connects `Fin.castPred` with the core map `Fin.castLT`.

#### Skipping one value: succAbove and predAbove

**Definition.** For a pivot $p \in \operatorname{Fin}(n + 1)$ and $i \in \operatorname{Fin}(n)$,
$$\operatorname{succAbove}_p(i) = \begin{cases} i & \text{if } i < p, \\ i + 1 & \text{if } i \geq p. \end{cases}$$

This is `Fin.succAbove p i`. The Lean definition tests `castSucc i < p`. The two cases are the lemmas `Fin.succAbove_of_castSucc_lt` and `Fin.succAbove_of_le_castSucc`. For $p = 0$ the map is `Fin.succ` (`Fin.succAbove_zero`), and for $p = n$ it is `Fin.castSucc` (`Fin.succAbove_last`).

**Theorem.** The map $\operatorname{succAbove}_p$ is strictly increasing, and its range is $\operatorname{Fin}(n + 1) \setminus \{p\}$.

*Proof.* On $\{i < p\}$ the map is $i \mapsto i$, and on $\{i \geq p\}$ it is $i \mapsto i + 1$. Both pieces increase. If $i < p \leq j$, then $\operatorname{succAbove}_p(i) = i < p \leq j < j + 1$. So the map is strictly increasing. The value $p$ is not taken: if $i < p$ the value is $i \neq p$, and if $i \geq p$ the value is $i + 1 > p$. Let $x \neq p$. If $x < p$, then $x \leq n - 1$ and $x = \operatorname{succAbove}_p(x)$. If $x > p$, then $x - 1 \geq p$ and $x = \operatorname{succAbove}_p(x - 1)$. $\square$

In Lean, the range statement is `Fin.range_succAbove`, the inequality `Fin.succAbove_ne` says $\operatorname{succAbove}_p(i) \neq p$, injectivity is `Fin.succAbove_right_injective` with the iff form `Fin.succAbove_right_inj`, and strict monotonicity is `Fin.strictMono_succAbove` in `Mathlib.Order.Fin.Basic`. The map is also injective in the pivot: this is `Fin.succAbove_left_injective`. The order lemmas `Fin.succAbove_lt_iff_succ_le` and `Fin.lt_succAbove_iff_le_castSucc` compare a value with the pivot.

**Definition.** For $p \in \operatorname{Fin}(n)$ and $i \in \operatorname{Fin}(n + 1)$,
$$\operatorname{predAbove}_p(i) = \begin{cases} i - 1 & \text{if } i > p, \\ i & \text{if } i \leq p. \end{cases}$$

This is `Fin.predAbove p i`, with the cases `Fin.predAbove_of_castSucc_lt` and `Fin.predAbove_of_le_castSucc`. It is a surjection (`Fin.predAbove_surjective`) that takes the value $p$ twice, at $p$ and at $p + 1$. It is a left inverse of the map that skips $p$:

**Theorem.** For $p \in \operatorname{Fin}(n)$, $\operatorname{predAbove}_p(\operatorname{succAbove}_p(i)) = i$ for each $i$, and $\operatorname{succAbove}_p(\operatorname{predAbove}_p(x)) = x$ for each $x \neq p$, with $p$ viewed in $\operatorname{Fin}(n + 1)$.

*Proof.* If $i < p$, then $\operatorname{succAbove}_p(i) = i \leq p$ and $\operatorname{predAbove}_p$ keeps it. If $i \geq p$, then $\operatorname{succAbove}_p(i) = i + 1 > p$, and $\operatorname{predAbove}_p$ subtracts one. For the second claim, if $x < p$ both maps keep $x$. If $x > p$, then $\operatorname{predAbove}_p(x) = x - 1 \geq p$ and $\operatorname{succAbove}_p$ adds one back. $\square$

The Lean forms are `Fin.predAbove_succAbove` and `Fin.succAbove_predAbove`; in both, the pivot of `Fin.succAbove` is `castSucc p`. The module also proves how the maps commute. For example, `Fin.succ_succAbove_succ` says $\operatorname{succAbove}_{p + 1}(i + 1) = \operatorname{succAbove}_p(i) + 1$. The lemma `Fin.succAbove_succAbove_succAbove_predAbove` says that there are two ways to skip two values of $\operatorname{Fin}(n + 2)$, and they give the same map. The next section uses it to remove two entries of a tuple in either order.

#### Reversal

The core map `Fin.rev` sends $i$ to $n - 1 - i$. It is an involution, `Fin.rev_involutive`, and the module `Mathlib.Data.Fin.Rev` packs it as a permutation, `Fin.revPerm`. The map reverses the order: `Fin.rev_le_iff` says $\operatorname{rev}(i) \leq j \iff \operatorname{rev}(j) \leq i$. To move `Fin.rev` across an equation, use `Fin.rev_eq_iff`.

**Theorem.** For $j \in \operatorname{Fin}(n + 1)$, $j + \operatorname{rev}(j) = n$ as natural numbers.

*Proof.* The value of $\operatorname{rev}(j)$ is $(n + 1) - (j + 1) = n - j$, and $j \leq n$. So $j + (n - j) = n$. $\square$

This is `Fin.add_rev_cast`, and `Fin.rev_add_cast` is the same sum in the other order. Reversal exchanges the successor and the cast: `Fin.rev_pred` and `Fin.rev_castPred` turn `Fin.pred` into `Fin.castPred` and back. It also exchanges the two sides of a pivot: `Fin.rev_succAbove` gives $\operatorname{rev}(\operatorname{succAbove}_p(i)) = \operatorname{succAbove}_{\operatorname{rev} p}(\operatorname{rev} i)$, and `Fin.rev_predAbove` is the same rule for `Fin.predAbove`. The forms `Fin.succAbove_rev_left` and `Fin.predAbove_rev_left` move `Fin.rev` from the pivot to the argument.

#### Embeddings

The module `Mathlib.Data.Fin.Embedding` packs the injective maps as terms of the type `α ↪ β` of embeddings. The naming pattern is the name of the map with the suffix `Emb`: `Fin.succEmb`, `Fin.castSuccEmb`, `Fin.castLEEmb`, `Fin.castAddEmb`, `Fin.addNatEmb`, `Fin.natAddEmb` and `Fin.succAboveEmb`. The embedding `Fin.valEmbedding` sends $i$ to its value in $\mathbb{N}$. The embedding `Fin.natAdd_castLEEmb` puts $\operatorname{Fin}(n)$ at the top of $\operatorname{Fin}(m)$, and `Fin.range_natAdd_castLEEmb` gives its range $\{i : m - n \leq i\}$. Each embedding has an apply lemma, such as `Fin.castSuccEmb_apply`, that simp uses to go back to the map.

**Theorem.** There is an injection $\operatorname{Fin}(n) \to \operatorname{Fin}(m)$ if and only if $n \leq m$.

*Proof.* If $n \leq m$, the map `Fin.castLE` is an injection. Conversely, an injection between finite sets cannot have a larger domain, by the pigeonhole principle. $\square$

The theorem is `Fin.nonempty_embedding_iff`. Its corollary `Fin.equiv_iff_eq` says that $\operatorname{Fin}(m) \simeq \operatorname{Fin}(n)$ if and only if $m = n$. So the type `Fin n` determines $n$, even though two equal types `Fin n` and `Fin m` need a proof of $n = m$ to compare their elements.

The module `Mathlib.Data.Fin.Pigeonhole` states the pigeonhole principle for `Fin`. The lemma `Fin.le_of_injective` says that an injective map $\operatorname{Fin}(m) \to \operatorname{Fin}(n)$ gives $m \leq n$, and `Fin.le_of_embedding` is the same for an embedding. The lemma `Fin.le_of_surjective` gives $n \leq m$ for a surjection, and `Fin.lt_of_injective_of_notMem` gives $m < n$ when an injection misses a value. The lemma `Fin.card_range_le` says that a map from $\operatorname{Fin}(m)$ takes at most $m$ values. Each is a special case of a lemma for finite types, such as `Fintype.card_le_of_injective`, with $|\operatorname{Fin}(n)| = n$.

The module `Mathlib.Data.Fin.EquivOfInjective` holds only deprecated lemmas about `Equiv.ofInjective` for the maps `Fin.castLE` and `Fin.castSucc`. The module `Mathlib.Data.Fin.SuccPredOrder` is a deprecated alias: the instances of `SuccOrder` and `PredOrder` on `Fin n` are now in `Mathlib.Order.SuccPred.Fin`.

#### Parity

The group $\operatorname{Fin}(n)$ has the addition modulo $n$, so an element $k$ is *even* when $k = r + r$ for some $r$. This is not always the parity of the value of $k$.

**Theorem.** Let $k \in \operatorname{Fin}(n)$. Then $k$ is even if and only if $n$ is odd or the value of $k$ is even.

*Proof.* Suppose $n$ is odd, so $n = 2 m + 1$. Then $2(m + 1) = n + 1 \equiv 1 \pmod n$, so $2$ is invertible modulo $n$. Take $r = (m + 1) k \bmod n$; then $r + r \equiv k$. Suppose $n$ is even. If $k = r + r$ in $\operatorname{Fin}(n)$, then $k \equiv 2 r \pmod n$, and $n$ is even, so the value of $k$ is even. If the value of $k$ is $2 s$, then $s < n$ and $k = s + s$. $\square$

This is `Fin.even_iff`, and `Fin.odd_iff` is the odd form. The special cases are `Fin.even_of_odd` (each element is even when $n$ is odd) and `Fin.even_iff_of_even` (the parity of the value, when $n$ is even). The lemmas `Fin.even_add_one_iff_odd` and `Fin.odd_add_one_iff_even` flip the parity under $k \mapsto k + 1$. The lemma `Fin.neg_one_pow_succAbove_add_predAbove` computes a sign that appears in the alternating sums of homological algebra: $(-1)^{\operatorname{succAbove}_i(j) + \operatorname{predAbove}_j(i)} = -(-1)^{i + j}$.

The small module `Mathlib.Data.Fin.Init` proves rules for the bitwise exclusive or on `Fin k`: `Fin.xor_comm`, `Fin.xor_self` and `Fin.xor_zero`, and `Fin.xor_assoc` when $k = 2^n$.

#### Flags from tuples

The module `Mathlib.Data.Fin.FlagRange` turns a tuple into a maximal chain. Let $f : \operatorname{Fin}(n + 1) \to \alpha$ in a bounded partial order, with $f_0 = \bot$, $f_n = \top$, and $f_{k + 1}$ a weak cover of $f_k$ for each $k$: $f_k \leq f_{k + 1}$ with no element strictly between. Then `IsMaxChain.range_fin_of_covBy` says that the range of $f$ is a maximal chain, and `Flag.rangeFin` is this range as a `Flag`. For example, the subspaces $0 = V_0 \subset V_1 \subset \dots \subset V_n = V$ of a vector space $V$ with $\dim V_k = k$ form a maximal chain of subspaces.

#### Fin2

The module `Mathlib.Data.Fin.Fin2` defines `Fin2 n`, an inductive type with two constructors: `fz : Fin2 (n + 1)` for $0$ and `fs : Fin2 n → Fin2 (n + 1)` for the successor. A function on `Fin2 n` is defined by pattern matching on these constructors, with no proof of a bound. This suits definitions by recursion on $n$, for example in the theory of polynomial functors. The conversions are `Fin2.toNat`, `Fin2.optOfNat`, `Fin2.toFin` and `Fin2.ofFin`, and `Fin2.equivFin` is the equivalence with `Fin n`. The class `Fin2.IsLT` lets `Fin2.ofNat'` find the proof of $m < n$ by instance search. The maps `Fin2.add`, `Fin2.left`, `Fin2.remapLeft`, `Fin2.insertPerm` and `Fin2.rev` copy the maps of `Fin`. The eliminators are `Fin2.cases'` and `Fin2.elim0`.

#### Common errors

1. The pivot of `Fin.succAbove` lives in `Fin (n + 1)`, but the pivot of `Fin.predAbove` lives in `Fin n`. In the cancellation lemmas the same pivot appears as `p` and as `castSucc p`.
2. `Fin.pred i h` and `Fin.castPred i h` take a proof. A rewrite that changes `i` can leave a proof of the old fact. Use the simp lemmas, which carry the proofs along, or state the goal with the value.
3. `Even k` for `k : Fin n` refers to the addition modulo $n$. For odd $n$ each element is even, so `Even k` does not say that `k.val` is even.

### Exercises

1. (A) Compute $\operatorname{succAbove}_2(i)$ for each $i \in \operatorname{Fin}(4)$, and $\operatorname{predAbove}_2(x)$ for each $x \in \operatorname{Fin}(5)$.
2. (A) Show that $\operatorname{rev}(\operatorname{last}(n)) = 0$ and $\operatorname{rev}(0) = \operatorname{last}(n)$ in $\operatorname{Fin}(n + 1)$.
3. (B) Show that each strictly increasing map $\operatorname{Fin}(n) \to \operatorname{Fin}(n + 1)$ is $\operatorname{succAbove}_p$ for exactly one $p$.
4. (B) Show that $\operatorname{succAbove}_p \circ \operatorname{rev} = \operatorname{rev} \circ \operatorname{succAbove}_{\operatorname{rev} p}$, from `Fin.rev_succAbove`.
5. (B) Decide for which $n$ the element $1 \in \operatorname{Fin}(n)$ is even, with a proof.
6. (C) Prove the pigeonhole principle $m \leq n$ for an injection $\operatorname{Fin}(m) \to \operatorname{Fin}(n)$ by induction on $m$, with `Fin.succAbove` and `Fin.predAbove` to remove one value from the codomain.

### Reference

<?reference?>
