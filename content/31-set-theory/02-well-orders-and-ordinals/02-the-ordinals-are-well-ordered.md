---
title: The ordinals are well-ordered
kind: theory
modules:
  - Mathlib.SetTheory.Ordinal.Family
  - Mathlib.SetTheory.Ordinal.Univ
  - Mathlib.SetTheory.Ordinal.Rank
explains:
  E3: [Ordinal.bddAbove_iff_small, not_small_ordinal, Ordinal.univ, WellFounded.rank, WellFounded.rank_eq_typein]
  E2: [Ordinal.bddAbove_of_small, Ordinal.le_iSup, Ordinal.iSup_le, Ordinal.lt_iSup_iff, Ordinal.iSup_add_one_le, Ordinal.lt_iSup_add_one, Ordinal.iSup_natCast, Ordinal.iSup_add_natCast, not_surjective_of_ordinal, not_injective_of_ordinal, Ordinal.not_bddAbove_compl_of_small, Ordinal.type_lt_ordinal, Ordinal.liftPrincipalSeg, Cardinal.univ, Cardinal.lift_lt_univ, Cardinal.aleph0_lt_univ, Acc.rank, Acc.rank_eq, WellFounded.rank_eq, WellFounded.rank_lt_of_rel, WellFounded.mem_range_rank_of_le]
  E1: auto
families: []
requires: [V31.C01, V04.C01, V04.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The ordinals are well-ordered

### Overview

Section 1 defined an ordinal as the type of a well-order, and showed that the order on the ordinals is well-founded. This section studies the ordinals of one universe as a single well-ordered type, $\mathrm{Ordinal}_u$. Three facts carry the rest of the volume.

First, each set of ordinals that is *small*, that is, indexed by a type of the universe $u$, has a supremum. So the ordinals have no gaps. Second, the type $\mathrm{Ordinal}_u$ itself is not small. This is the theorem of Burali-Forti. In set theory it says that the ordinals do not form a set. In Lean it says that the order type of $\mathrm{Ordinal}_u$ exists, but only one universe higher. Third, each element of a well-founded relation has a rank, an ordinal that measures how far it is from the minimal elements. The rank turns well-founded induction into induction on ordinals, and it gives the transfinite induction in its three cases: zero, successor and limit.

### Definitions

**Definition (Small family).** A type $\iota$ is *small* in the universe $u$ if it is equivalent to a type of `Type u`. A family $(o_i)_{i \in \iota}$ of ordinals of $\mathrm{Ordinal}_u$ is *small* if $\iota$ is small in $u$.

The index type of a family can live in a higher universe. The family of all ordinals of $\mathrm{Ordinal}_u$ is indexed by $\mathrm{Ordinal}_u$ itself, which lives in `Type (u + 1)`. The theorem of Burali-Forti says that this family is not small.

**Definition (Supremum of a family).** The *supremum* $\sup_i o_i$ of a family of ordinals is the least upper bound of the family, when one exists.

Mathlib writes `⨆ i, o i`. The ordinals form a conditionally complete linear order, so `⨆` is defined for each family, and its value on a family without an upper bound is the junk value 0. Each lemma on suprema in Mathlib therefore takes a hypothesis that the family is bounded, or that it is small.

**Definition (The ordinal of a universe).** The ordinal $\mathrm{univ}_u$ is the order type of $(\mathrm{Ordinal}_u, <)$. It is an element of $\mathrm{Ordinal}_{u+1}$. The cardinal $\mathrm{univ}_u$ is the cardinality of $\mathrm{Ordinal}_u$, an element of $\mathrm{Cardinal}_{u+1}$.

**Definition (Rank).** Let $r$ be a well-founded relation on a type $\alpha$. The *rank* of $a \in \alpha$ is defined by well-founded recursion: $$\mathrm{rank}(a) = \sup \{\, \mathrm{rank}(b) + 1 : r\,b\,a \,\}.$$

So a minimal element has rank 0, an element whose predecessors are all minimal has rank 1, and so on. The definition is a recursion on $r$, and it makes sense because $r$ is well-founded (V04, Chapter 1). If only one element $a$ is accessible, Mathlib defines the rank of $a$ from the proof of accessibility.

### Theorems and proofs

**Theorem (Small sets are bounded).** A set $S$ of ordinals of $\mathrm{Ordinal}_u$ is bounded above if and only if $S$ is small in $u$.

*Proof.* Assume that $S$ is bounded by $a$. Then $S$ is a subset of $\{o : o \le a\}$, which is the set of ordinals below $a + 1$. Section 1 shows that this set is in bijection with a well-ordered type of `Type u` of type $a + 1$. So $S$ is small.

Conversely, assume that $S$ is small. For each $o \in S$, the cardinal $|o|^+$ is a cardinal of the universe $u$. A small family of cardinals is bounded, because the sum of the family is a cardinal of the universe $u$ above each member (Chapter 1). Let $\kappa$ be such a bound. For each $o \in S$, $|o| < |o|^+ \le \kappa$, so $o < \kappa.\mathrm{ord}$ by the Galois property of $\mathrm{ord}$ (Section 1). So $\kappa.\mathrm{ord}$ is an upper bound of $S$. $\square$

**Corollary (Suprema).** Let $(o_i)_{i \in \iota}$ be a small family of ordinals. Then $\sup_i o_i$ exists, $o_i \le \sup_i o_i$ for each $i$, and $\sup_i o_i \le a$ if and only if $o_i \le a$ for each $i$. Also $\sup_i (o_i + 1)$ is the least ordinal strictly above each $o_i$.

*Proof.* The set of values is small, so it is bounded by the theorem. A nonempty bounded set of a well-order has a least upper bound: take the least element of the set of upper bounds, which exists because the order is well-founded. The last claim follows, because $o < b$ if and only if $o + 1 \le b$. $\square$

The supremum can be a member of the family, as for $\sup \{1, 2, 5\} = 5$, or not, as for $\sup_n n = \omega$. In the second case, the supremum is a limit ordinal.

**Theorem (Burali-Forti).** The type $\mathrm{Ordinal}_u$ is not small in $u$. Equivalently, no map from a type of `Type u` to $\mathrm{Ordinal}_u$ is surjective.

*Proof.* Let $f : \iota \to \mathrm{Ordinal}_u$ with $\iota$ small. By the corollary, $b = \sup_i (f(i) + 1)$ exists, and $f(i) < b$ for each $i$. So $b$ is not in the range of $f$. If $\mathrm{Ordinal}_u$ were small, the identity map would be such an $f$, and it is surjective. $\square$

In naive set theory, the ordinals of all well-orders form a well-ordered set, and its order type is an ordinal larger than each ordinal. Burali-Forti found this contradiction in 1897. Lean avoids the paradox with universes. The order type of $\mathrm{Ordinal}_u$ is an honest ordinal, $\mathrm{univ}_u$, but it lives in $\mathrm{Ordinal}_{u+1}$. The lift $\mathrm{Ordinal}_u \to \mathrm{Ordinal}_{u+1}$ is an embedding onto the initial segment below $\mathrm{univ}_u$.

**Corollary.** The complement of a small set of ordinals is not bounded above. In particular, $\mathrm{Ordinal}_u$ is uncountable, and each cardinal of the universe $u$ is below $\mathrm{univ}_u$ after the lift. Also $\aleph_0 < \mathrm{univ}_u$.

*Proof.* If $S$ is small and its complement is bounded by $a$, then $\mathrm{Ordinal}_u = S \cup \{o : o \le a\}$ is a union of two small sets, and so small. This contradicts the theorem. The other claims follow, because a countable type and each type of `Type u` are small. $\square$

**Theorem (The rank of an order).** Let $r$ be a well-founded relation on $\alpha$.

1. If $r\,a\,b$, then $\mathrm{rank}(a) < \mathrm{rank}(b)$.
2. The range of $\mathrm{rank}$ is closed downwards: if $o \le \mathrm{rank}(a)$, then $o = \mathrm{rank}(b)$ for some $b$.
3. If $r$ is a well-order, then $\mathrm{rank}(a) = \mathrm{typein}(a)$, the order type of the initial segment below $a$.

*Proof.* (1) The value $\mathrm{rank}(a) + 1$ occurs in the supremum that defines $\mathrm{rank}(b)$, so $\mathrm{rank}(a) < \mathrm{rank}(a) + 1 \le \mathrm{rank}(b)$.

(2) Use well-founded induction on $a$. If $o = \mathrm{rank}(a)$, take $b = a$. If $o < \mathrm{rank}(a)$, then $o$ is below the supremum of the values $\mathrm{rank}(c) + 1$ for $r\,c\,a$, so $o < \mathrm{rank}(c) + 1$ for some such $c$, that is, $o \le \mathrm{rank}(c)$. The induction hypothesis for $c$ gives $b$.

(3) Use well-founded induction on $a$. Both sides are the least ordinal strictly above the values at the predecessors of $a$. For the rank, this is the definition. For $\mathrm{typein}$, the initial segment below $a$ is the union of the initial segments below its elements together with these elements, and Section 1 gives $\mathrm{typein}(c) < \mathrm{typein}(a)$ for $c < a$. Each ordinal below $\mathrm{typein}(a)$ is $\mathrm{typein}(c)$ for some $c < a$, also by Section 1. $\square$

Part 3 says that the rank generalizes the position in a well-order. For a well-founded relation that is not linear, the rank compresses: different elements can have the same rank.

**Theorem (Transfinite induction).** Let $P$ be a property of ordinals. Assume that $P(0)$ holds, that $P(o)$ implies $P(o + 1)$, and that for each limit ordinal $o$, if $P(b)$ holds for each $b < o$, then $P(o)$ holds. Then $P(o)$ holds for each ordinal $o$.

*Proof.* Each ordinal is 0, a successor $b + 1$, or a limit, and the three cases exclude each other. Assume that $P$ fails somewhere. The ordinals are well-ordered (Section 1), so there is a least $o$ at which $P$ fails. Then $P(b)$ holds for each $b < o$. If $o = 0$ or $o$ is a limit, the hypotheses give $P(o)$. If $o = b + 1$, then $P(b)$ holds, and so $P(o)$ holds. Each case is a contradiction. $\square$

The same argument gives *transfinite recursion*: a function on the ordinals is defined by its value at 0, a rule from the value at $b$ to the value at $b + 1$, and a rule from the values below a limit $o$ to the value at $o$. Chapter 3 defines the ordinal operations in this way.

### Examples

**Example (Suprema of sequences).** $\sup_n n = \omega$, because each natural number is below $\omega$, and an ordinal above each $n$ is infinite. In the same way, $\sup_n (o + n) = o + \omega$ for each ordinal $o$, and $\sup_n (o \cdot n) = o \cdot \omega$. The supremum of $1, \omega, \omega^2, \dots$ is $\omega^\omega$, which Chapter 3 defines.

**Example (Rank of finite sets).** Let $\alpha$ be the finite subsets of $\mathbb{N}$ with the relation of strict inclusion. It is well-founded. The rank of a finite set is its number of elements: the empty set has rank 0, and a set $s$ with $n$ elements is above sets with $n - 1$ elements and no larger. So the rank takes the values $0, 1, 2, \dots$, although the relation is not linear.

**Example (Rank of a tree).** Let $T$ be a tree with root, in which each path is finite, and let $r\,a\,b$ hold when $a$ is a child of $b$. This relation is well-founded. A leaf has rank 0. A node whose children have ranks $0, 1, 2, \dots$ has rank $\omega$. In this way, ranks above each countable ordinal occur on trees with countably many nodes. This is the base of the descriptive trees of Chapter 7.

**Counterexample (Large families).** Let $f : \mathrm{Ordinal}_u \to \mathrm{Ordinal}_u$ be the identity. The family is not small, so the corollary on suprema does not apply. In Mathlib, `⨆ o, o` is the junk value 0, because the range has no upper bound. A proof that uses `Ordinal.le_iSup` on this family cannot find the instance `Small.{u}`.

### The library around it

::: mathlib
`Ordinal.bddAbove_iff_small` · `Mathlib.SetTheory.Ordinal.Family`

`bddAbove_iff_small {s : Set Ordinal.{u}} : BddAbove s ↔ Small.{u} s`. One direction is `bddAbove_of_small`. The lemmas on suprema take the instance `[Small.{u} ι]`: `Ordinal.le_iSup f : ∀ i, f i ≤ ⨆ i, f i`, `Ordinal.lt_iSup_iff`, and `Ordinal.iSup_add_one_le`, `Ordinal.lt_iSup_add_one` for the strict bound. `Ordinal.iSup_le` needs no instance, because an unbounded family has the supremum 0. Concrete suprema: `Ordinal.iSup_natCast : iSup Nat.cast = ω` and `Ordinal.iSup_add_natCast`.

<?decl Ordinal.bddAbove_iff_small?>
:::

::: mathlib
`not_small_ordinal` · `Mathlib.SetTheory.Ordinal.Family`

`not_small_ordinal : ¬Small.{u} Ordinal.{max u v}` is the theorem of Burali-Forti. The forms with maps are `not_surjective_of_ordinal` and `not_injective_of_ordinal`, for a small type `α`. The corollary is `Ordinal.not_bddAbove_compl_of_small`, and the instance `Ordinal.uncountable` follows.

<?decl not_small_ordinal?>
:::

::: mathlib
`Ordinal.univ` · `Mathlib.SetTheory.Ordinal.Univ`

`Ordinal.univ.{u, v} : Ordinal.{max (u + 1) v}` is the lift of `typeLT Ordinal.{u}`, and `Ordinal.type_lt_ordinal` states it. `Ordinal.liftPrincipalSeg : Ordinal.{u} <i Ordinal.{max (u + 1) v}` is the lift as a principal segment with top `univ`. The cardinal version is `Cardinal.univ`, with `Cardinal.lift_lt_univ` and `Cardinal.aleph0_lt_univ`. Chapter 6 proves that `Cardinal.univ` is inaccessible.

<?decl Ordinal.univ?>
:::

<?decl Cardinal.univ?>

::: mathlib
`WellFounded.rank` · `Mathlib.SetTheory.Ordinal.Rank`

`WellFounded.rank r a` needs `[WellFounded r]` as an instance argument, and `WellFounded.rank_eq` is the defining equation `rank r a = ⨆ b : {b // r b a}, succ (rank r b)`. `WellFounded.rank_lt_of_rel` and `WellFounded.mem_range_rank_of_le` are parts 1 and 2 of the theorem. Part 3 is `WellFounded.rank_eq_typein`. For one accessible element, `Acc.rank` and `Acc.rank_eq` do the same.

<?decl WellFounded.rank?>
:::

<?decl WellFounded.rank_eq_typein?>

::: mathlib
`Ordinal.limitRecOn` · `Mathlib.SetTheory.Ordinal.Arithmetic`

Transfinite recursion in three cases is `Ordinal.limitRecOn`, with the equations `limitRecOn_zero`, `limitRecOn_add_one` and `limitRecOn_limit`. It is the eliminator for `induction o using Ordinal.limitRecOn`. The case split is `Ordinal.zero_or_succ_or_isSuccLimit`. Chapter 3 uses both.

<?decl Ordinal.limitRecOn?>
:::

The type of the ordinals below an ordinal is in `Mathlib.SetTheory.Ordinal.Basic`, the module of Section 1: `Ordinal.type_lt_Iio o : typeLT (Iio o) = lift.{u + 1} o` and `Ordinal.typein_ordinal`. The lift appears because `Iio o` is a type of `Type (u + 1)`.

Common errors:

- `⨆ i, f i` without the instance `Small.{u} ι` can be the junk value 0. Before a rewrite with `Ordinal.le_iSup`, check that Lean finds the instance. For `ι : Type u`, it finds it at once.
- Older code uses the functions `Ordinal.sup`, `Ordinal.bsup` and `Ordinal.lsub`. The index of this edition has no declaration for them. Use `⨆` and `⨆ i, f i + 1`.
- `WellFounded.rank` takes the well-foundedness as an instance argument `[hwf : WellFounded r]`. For a proof `h : WellFounded r` that is not an instance, write `haveI := h` first.
- `Ordinal.univ.{u, v}` has two universe parameters. Write them, because Lean cannot infer them from the context.

### Exercises

1. (A) Compute $\sup \{\omega + n : n \in \mathbb{N}\}$, $\sup \{\omega \cdot n + 1 : n \in \mathbb{N}\}$ and $\sup \{o + 1 : o < \omega \cdot 2\}$.
2. (A) Show that $\sup_i (o_i + 1) = \sup_i o_i$ if the family has no largest element, and $\sup_i (o_i + 1) = (\sup_i o_i) + 1$ otherwise.
3. (A) Compute the rank of each element of the relation $r\,a\,b \iff a \mid b,\ a \ne b$ on the positive integers.
4. (B) Show that the rank of a finite subset of $\mathbb{N}$ under strict inclusion is its number of elements.
5. (B) Let $f : \alpha \to \beta$ satisfy $s\,(f\,a)\,(f\,b)$ whenever $r\,a\,b$, with $s$ well-founded. Show that $\mathrm{rank}_r(a) \le \mathrm{rank}_s(f\,a)$.
6. (B) Show that each ordinal $o$ is the supremum of $b + 1$ for $b < o$.
7. (C) Show that for each countable ordinal $o$, there is a tree on $\mathbb{N}$ with finite paths whose root has rank $o$. Hint: use transfinite induction and join countably many trees below a new root.
8. (L) In Lean, prove `Ordinal.iSup_natCast` again from `Ordinal.lt_iSup_iff` and the fact that each natural number is below `ω`.

### Notes and history

Burali-Forti published the paradox of the largest ordinal in 1897. Cantor had found it earlier, and his letters to Dedekind of 1899 distinguish the "consistent" multiplicities, the sets, from the inconsistent ones, such as the totality of the ordinals. In ZFC the ordinals are a proper class (Chapter 7). In Lean, the hierarchy of universes takes the role of the classes.

### Reference

<?reference?>
