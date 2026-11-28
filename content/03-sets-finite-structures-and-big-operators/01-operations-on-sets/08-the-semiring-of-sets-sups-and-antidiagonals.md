---
title: The semiring of sets, sups of sets and antidiagonals
kind: api
modules:
  - Mathlib.Data.Set.Semiring
  - Mathlib.Data.Set.Sups
  - Mathlib.Data.Set.MulAntidiagonal
  - Mathlib.Data.Set.SMulAntidiagonal
  - Mathlib.Data.Set.Pointwise.Support
explains:
  E2: [SetSemiring, SetSemiring.add_def, SetSemiring.imageHom, Set.mem_sups, Set.sups_subset_iff, Set.infs_eq_inter, Set.mem_mulAntidiagonal, Set.MulAntidiagonal.finite_of_isPWO, Set.SMulAntidiagonal.finite_of_finite_fst, support_comp_inv_smul]
  E1: auto
families: []
requires: [V01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The semiring of sets, sups of sets and antidiagonals

### Overview

Sets of a type with an operation carry operations of their own. For sets $s, t$ of a monoid, the pointwise product $s \cdot t = \{a b \mid a \in s,\ b \in t\}$ is the binary image of Section 6. With union as the sum and the pointwise product as the product, the sets of a monoid form a semiring. The type `Set α` cannot carry this semiring as an instance, because `+` on `Set α` already means the pointwise sum. So the library puts it on a copy of the type, `SetSemiring α`.

The other modules of this section are about two more binary operations and about the sets of solutions of an equation. For sets of a lattice, $s \vee t = \{a \sqcup b\}$ and $s \wedge t = \{a \sqcap b\}$ are the sups and the infs of two sets. For sets $s, t$ of a monoid and a point $a$, the *antidiagonal* is the set of pairs $(x, y) \in s \times t$ with $x y = a$. The finiteness of antidiagonals is the key fact behind the product of Hahn series.

### The library around it

#### The semiring of sets

The structure `SetSemiring α` has one field, `SetSemiring.toSet`, and the constructor `SetSemiring.ofSet`. The equivalence with `Set α` is `SetSemiring.toSetEquiv`, and the rules `SetSemiring.toSet_ofSet` and `SetSemiring.ofSet_toSet` say that the two maps are inverse. The order is inclusion: `SetSemiring.ofSet_le_ofSet` gives $\operatorname{ofSet}(s) \le \operatorname{ofSet}(t) \iff s \subseteq t$, and the type is a complete atomic Boolean algebra by transfer.

The operations are defined through the sets:

$$s + t = \operatorname{ofSet}(s \cup t), \qquad 0 = \operatorname{ofSet}(\varnothing), \qquad s \cdot t = \operatorname{ofSet}(s \cdot t), \qquad 1 = \operatorname{ofSet}(\{1\}).$$

These are `SetSemiring.add_def`, `SetSemiring.zero_def`, `SetSemiring.mul_def` and `SetSemiring.one_def`, and the rules `SetSemiring.ofSet_union`, `SetSemiring.ofSet_mul` and `SetSemiring.ofSet_pow` move the operations through `SetSemiring.ofSet`. The sum is idempotent, $s + s = s$, because $s \cup s = s$.

The instances follow the structure of $\alpha$:

1. for a type with a multiplication, a nonunital nonassociative semiring, with no zero divisors (`SetSemiring.instNoZeroDivisors`): if $s \cdot t = \varnothing$ then $s$ or $t$ is empty;
2. for a monoid, an idempotent semiring (`SetSemiring.instIdemSemiringOfMonoid`);
3. for a commutative monoid, an idempotent commutative semiring (`SetSemiring.instIdemCommSemiringOfCommMonoid`);
4. for a commutative monoid, an ordered semiring (`SetSemiring.instIsOrderedRing`), in which the sum is the supremum.

A monoid homomorphism $f : \alpha \to \beta$ gives a ring homomorphism between the semirings of sets, by images: `SetSemiring.imageHom f` sends $s$ to $f(s)$, with the rule `SetSemiring.imageHom_apply`. And `SetSemiring.singletonMonoidHom` is the monoid homomorphism $a \mapsto \{a\}$. With this structure, the algebra of the semiring of sets of a monoid applies to sets: for example, the binomial expansion of $(s + t)^n$ in a commutative monoid becomes a rule for $(s \cup t)^n$.

#### Sups and infs of sets

The module `Mathlib.Data.Set.Sups` defines the operations `s ⊻ t` and `s ⊼ t` through the classes `HasSups` and `HasInfs`, with the structures `Set.hasSups` and `Set.hasInfs`. These are scoped instances: the notation works only after `open SetFamily`. The membership rule is

$$c \in s \vee t \iff \exists a \in s,\ \exists b \in t,\ a \sqcup b = c.$$

This is `Set.mem_sups`, and `Set.mem_infs` is the dual. The operation is a binary image: `Set.image_sup_prod` says that $s \vee t$ is `Set.image2 (· ⊔ ·) s t`. So the rules of Section 6 transfer, and the module states them for sups and infs. The table gives the main ones. Each has a form for infs, such as `Set.infs_subset_iff`.

| Lean name | Statement |
|---|---|
| `Set.sups_subset_iff` | $s \vee t \subseteq u \iff \forall a \in s,\ \forall b \in t,\ a \sqcup b \in u$ |
| `Set.sups_subset` | monotone in $s$ and $t$ |
| `Set.empty_sups` | $\varnothing \vee t = \varnothing$ |
| `Set.sups_union_left` | $(s_1 \cup s_2) \vee t = (s_1 \vee t) \cup (s_2 \vee t)$ |
| `Set.sups_comm` | $s \vee t = t \vee s$ |
| `Set.sups_assoc` | $(s \vee t) \vee u = s \vee (t \vee u)$ |
| `Set.image_sups` | a sup homomorphism $f$ gives $f(s \vee t) = f(s) \vee f(t)$ |

The sups of a set with itself is the set if and only if the set is closed under $\sqcup$: `Set.sups_eq_self` gives $s \vee s = s \iff$ `SupClosed s`. For lower sets the infs are intersections:

$$s, t \text{ lower sets} \implies s \wedge t = s \cap t.$$

This is `Set.infs_eq_inter`. In a distributive lattice the operations satisfy the inclusions `Set.sups_infs_subset_left` and `Set.infs_sups_subset_left`, which are only inclusions, not equalities. The upper closure of a sup is the sup of the upper closures (`upperClosure_sups`). The forms for finsets are in the module `Mathlib.Data.Finset.Sups`, and the combinatorics of set families uses them.

#### Antidiagonals in a set

For sets $s, t$ of a type with a multiplication and a point $a$, `Set.mulAntidiagonal s t a` is the set of pairs $(x, y)$ with $x \in s$, $y \in t$ and $x y = a$. The additive form is `Set.antidiagonal`. The membership rule is `Set.mem_mulAntidiagonal`, the set is monotone in $s$ and in $t$ (`Set.mulAntidiagonal_mono_left`), and swapping the pairs swaps $s$ and $t$ in a commutative magma (`Set.swap_mem_mulAntidiagonal`). In a cancellative commutative monoid, two points of the antidiagonal with the same first entry have the same second entry, since $y = x^{-1} a$ in the group of fractions (`Set.MulAntidiagonal.fst_eq_fst_iff_snd_eq_snd`).

The main result is finiteness. Let $\alpha$ be an ordered cancellative commutative monoid, and let $s$ and $t$ be partially well ordered: each sequence in them has an increasing pair. Then each antidiagonal is finite:

$$s, t \text{ partially well ordered} \implies \{(x, y) \in s \times t \mid x y = a\} \text{ finite}.$$

This is `Set.MulAntidiagonal.finite_of_isPWO`, and `Set.MulAntidiagonal.finite_of_isWF` is the form for well founded sets in a linear order. The proof: an infinite antidiagonal gives a sequence of distinct pairs. A subsequence is increasing in the first entry, and then a further subsequence is increasing in the second entry. Two pairs with $x \le x'$ and $y \le y'$ and $x y = x' y'$ must be equal by cancellation, which is a contradiction. For finitely supported functions this argument is in Chapter 7, and the finset `Finset.mulAntidiagonal` of Chapter 3 is built on this theorem: it is the antidiagonal seen as a finset.

#### Antidiagonals for an action

The module `Mathlib.Data.Set.SMulAntidiagonal` gives the same construction for an action $G$ on $P$: `Set.smulAntidiagonal s t a` is the set of pairs $(g, p) \in s \times t$ with $g \cdot p = a$, with the rule `Set.mem_smulAntidiagonal` and the additive form `Set.vaddAntidiagonal`. Two finiteness results hold. If the action is cancellative on the left and $s$ is finite, then each antidiagonal is finite, because $p$ is then fixed by $g$:

$$s \text{ finite} \implies \{(g, p) \in s \times t \mid g \cdot p = a\} \text{ finite}.$$

This is `Set.SMulAntidiagonal.finite_of_finite_fst`. If the action is ordered and cancellative and both sets are partially well ordered, the argument of the last subsection gives `Set.SMulAntidiagonal.finite_of_isPWO`. These results serve the action of Hahn series on Hahn modules.

#### Supports under an action

The module `Mathlib.Data.Set.Pointwise.Support` has four results on the support of a function composed with an action. For a group $\alpha$ that acts on $\beta$ and a function $f : \beta \to \gamma$ into a type with a zero,

$$\operatorname{supp}(x \mapsto f(c^{-1} \cdot x)) = c \cdot \operatorname{supp}(f).$$

This is `support_comp_inv_smul`, and `mulSupport_comp_inv_smul` is the form for `Function.mulSupport`. The forms `support_comp_inv_smul₀` and `mulSupport_comp_inv_smul₀` hold for a group with zero and $c \ne 0$. A translation of the graph of a function translates its support by the same element.

#### Common errors

1. A learner writes `s + t` for two sets and expects the union. On `Set α` the sum is the pointwise sum $\{a + b\}$. Use `SetSemiring.ofSet s + SetSemiring.ofSet t` for the semiring of sets, or write `s ∪ t`.
2. A learner applies `Set.infs_eq_inter` to sets that are not lower sets. In general $s \wedge t$ is not contained in $s \cap t$; for example $\{a\} \wedge \{b\} = \{a \sqcap b\}$.
3. A learner applies `Set.MulAntidiagonal.finite_of_isPWO` in $\mathbb{Z}$ to the set of all integers. The set is not partially well ordered, and in fact each antidiagonal of $\mathbb{Z} \times \mathbb{Z}$ for addition is infinite.

### Exercises

1. (A) Compute $\{1, 2\} \vee \{2, 3\}$ and $\{1, 2\} \wedge \{2, 3\}$ for the order on $\mathbb{N}$.
2. (A) In `SetSemiring ℕ`, for the multiplication of $\mathbb{N}$, compute $(\operatorname{ofSet}\{1, 2\} + \operatorname{ofSet}\{3\}) \cdot \operatorname{ofSet}\{1, 2\}$.
3. (B) Show that $s \wedge t \subseteq s \cap t$ fails for $s = \{2\}$ and $t = \{3\}$ in the divisibility lattice of $\mathbb{N}$, and check that $s$ and $t$ are not lower sets there.
4. (B) Give the antidiagonal `Set.antidiagonal s s 5` for $s = \{0, 1, 2, 3, 4, 5\}$ in $\mathbb{N}$.
5. (B) Prove `Set.sups_subset_iff` from `Set.mem_sups`.
6. (C) Follow the proof in the text to prove `Set.MulAntidiagonal.finite_of_isPWO` for $\alpha = \mathbb{N} \times \mathbb{N}$ under addition with the product order, and say where cancellation is used.

### Reference

<?reference?>
