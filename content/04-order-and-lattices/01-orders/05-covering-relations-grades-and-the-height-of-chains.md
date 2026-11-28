---
title: Covering relations, grades and the height of chains
kind: api
modules:
  - Mathlib.Order.Cover
  - Mathlib.Order.Grade
  - Mathlib.Order.Height
explains:
  E2: [covBy_iff_Ioo_eq, CovBy.unique_left, Set.covBy_iff_exists_insert, Prod.covBy_iff, exists_covBy_of_wellFoundedLT, covBy_iff_lt_covBy_grade, GradeOrder.wellFoundedLT, Set.encard_le_chainHeight_of_isChain]
  E1: auto
families: []
requires: [V01, V03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Covering relations, grades and the height of chains

### Overview

In a partial order, $b$ *covers* $a$ when $a < b$ and no element lies strictly between them. The covering pairs are the edges of the Hasse diagram of a finite order. They are the steps of the order: in $\mathbb{N}$ the number $n + 1$ covers $n$, in the subsets of a type the set $s \cup \{a\}$ covers $s$ when $a \notin s$, and in $\mathbb{Q}$ no element covers another. Mathlib writes `a ⋖ b` for `CovBy a b` and uses a second symbol for the weak form `WCovBy a b`, which also allows $a = b$; this text writes the weak form as $a \lessdot^{=} b$. The two predicates are defined in `Mathlib.Order.Defs.PartialOrder`, next to the axioms of the first section of this chapter.

The three modules of this section build on the covering relation. `Mathlib.Order.Cover` has its API: the links with intervals, with linear orders, with products and with the order dual. `Mathlib.Order.Grade` defines graded orders, where a function `grade 𝕆` counts the steps from the bottom. `Mathlib.Order.Height` measures the longest chain in a set. The ideas come back in the successor orders, in the Jordan and Hölder theorem of group theory and in the Krull dimension of a ring.

### The library around it

**The definition and the first characterizations.** By definition, `a ⋖ b` means `a < b ∧ ∀ c, a < c → ¬c < b`, and `WCovBy a b` means `a ≤ b ∧ ∀ c, a < c → ¬c < b`. The basic lemmas `CovBy.lt`, `CovBy.le`, `CovBy.wcovBy` and `WCovBy.le` extract the order part. The condition "nothing between" is the emptiness of an open interval, and the lemma `covBy_iff_Ioo_eq` states

$$a \lessdot b \iff a < b \text{ and } (a, b) = \emptyset.$$

The proof is a rewriting: $c \in (a, b)$ means $a < c$ and $c < b$, so the set is empty exactly when no $c$ satisfies both. The same holds for the weak form in `wcovBy_iff_Ioo_eq`. In a partial order, `wcovBy_iff_covBy_or_eq` states $a \lessdot^{=} b \iff a \lessdot b \lor a = b$, and in a preorder `wcovBy_iff_covBy_or_le_and_le` replaces the equality by $a \le b \le a$. To prove a covering, the constructor `covBy_of_eq_or_eq` asks for $a < b$ and for each $c$ with $a \le c \le b$ a proof that $c = a$ or $c = b$. The negation is `not_covBy_iff`: if $a < b$, then $b$ does not cover $a$ exactly when some $c$ satisfies $a < c < b$. Dense orders are the orders without covers: `denselyOrdered_iff_forall_not_covBy`, and its consequence `not_covBy_of_denselyOrdered`.

**Intervals.** A covering pair has a very small closed interval. In a partial order `CovBy.Icc_eq` gives $[a, b] = \{a, b\}$, and `CovBy.Ico_eq` gives $[a, b) = \{a\}$. The converses are `Set.Ico_eq_singleton_left_iff` and `Set.Ioc_eq_singleton_right_iff`. In a linear order the cover glues two rays: `CovBy.Ioi_eq` gives $(a, \infty) = [b, \infty)$ and `CovBy.Iio_eq` gives $(-\infty, b) = (-\infty, a]$. So `CovBy.le_iff_lt_left` states $z \le a \iff z < b$, which is the rule that turns $n < m + 1$ into $n \le m$ in $\mathbb{N}$.

**Linear orders.** In a linear order an element has at most one lower cover and at most one upper cover. This is `CovBy.unique_left`: if $a \lessdot c$ and $b \lessdot c$, then $a = b$. The proof is short. Suppose $a < b$. Then $a < b < c$, so $b$ lies strictly between $a$ and $c$, which contradicts $a \lessdot c$. So $b \le a$, and by symmetry $a \le b$. The dual statement is `CovBy.unique_right`. In a lattice, two distinct elements that weakly cover the same element meet in it: `WCovBy.inf_eq` and `WCovBy.sup_eq`.

**Existence of covers.** A well-founded order has covers above each element that is not maximal. This is `exists_covBy_of_wellFoundedLT`: if `¬IsMax a`, then there is $a'$ with $a \lessdot a'$. Proof: the set $\{x \mid a < x\}$ is nonempty because $a$ is not maximal, so it has a minimal element $a'$ by well-foundedness. An element $c$ with $a < c < a'$ would be in the set and below $a'$, which contradicts the minimality. The dual is `exists_covBy_of_wellFoundedGT`.

**Sets, products and functions.** In `Set α` the covers are the steps of one element. The lemma `Set.covBy_iff_exists_insert` states $s \lessdot t \iff \exists a \notin s,\ \{a\} \cup s = t$. For the direction from left to right, $s \subsetneq t$ gives some $a \in t \setminus s$, and then $s \subsetneq \{a\} \cup s \subseteq t$; the cover forces $\{a\} \cup s = t$. For the converse, a set strictly between $s$ and $s \cup \{a\}$ would have to contain a point of $s \cup \{a\}$ outside $s$, so it would contain $a$. The relatives are `Set.covBy_insert`, `Set.sdiff_singleton_covBy` and `Set.empty_covBy_singleton`. In a product of two partial orders, `Prod.covBy_iff` states that $(a, b) \lessdot (a', b')$ exactly when one coordinate covers and the other is equal:

$$x \lessdot y \iff (x_1 \lessdot y_1 \land x_2 = y_2) \lor (x_2 \lessdot y_2 \land x_1 = y_1).$$

Proof sketch: if both coordinates go up strictly, then $(y_1, x_2)$ lies strictly between $x$ and $y$; if one coordinate is equal, a point between $x$ and $y$ is a point between the other coordinates. The family `Prod.mk_covBy_mk_iff_left`, `Prod.mk_covBy_mk_iff_right` and `Prod.swap_covBy_swap` follows. For functions, `Pi.covBy_iff` says that $a \lessdot b$ when exactly one coordinate covers and all others agree.

**Duality, maps and adjoined elements.** The lemma `toDual_covBy_toDual_iff` states that $b$ covers $a$ in `αᵒᵈ` exactly when $a$ covers $b$ in `α`. An order isomorphism keeps covers, by `apply_covBy_apply_iff`. An order embedding keeps them when its range is order-connected: `CovBy.image`, with the converse `CovBy.of_image`. The lemmas `WithTop.coe_covBy_top` and `WithBot.bot_covBy_coe` say that the new top covers exactly the maximal elements and the new bottom is covered by exactly the minimal elements. The relation lemma `reflTransGen_wcovBy_eq_reflTransGen_covBy` says that chains of weak covers and chains of covers reach the same elements.

**Graded orders.** The module `Mathlib.Order.Grade` defines an `𝕆`-graded order as a class `GradeOrder 𝕆 α` with a function `α → 𝕆` that is strictly monotone (`grade_strictMono`) and maps covers to covers (`CovBy.grade`). The function is `grade 𝕆 a`, and the grading type `𝕆` is an explicit argument, because one order can carry several gradings. In $\mathbb{N}$ the grade of $a$ is the height of $a$ in the Hasse diagram. The refinements `GradeMinOrder`, `GradeMaxOrder` and `GradeBoundedOrder` add that minimal elements have minimal grades and maximal elements have maximal grades. With a bottom element, `grade_eq_zero_iff` states $\operatorname{grade}_{\mathbb{N}} a = 0 \iff a = \bot$. Each preorder is graded by itself through the instance `Preorder.toGradeBoundedOrder`, with `grade_self`. The instance `GradeOrder.natToInt` passes from $\mathbb{N}$ to $\mathbb{Z}$, and the definitions `GradeOrder.liftLeft` and `GradeOrder.liftRight` move a grading along strictly monotone maps that keep covers. The module `Mathlib.Data.Finset.Grade` grades `Finset α` by the number of elements.

The grade detects covers: `covBy_iff_lt_covBy_grade` states $a \lessdot b \iff a < b \land \operatorname{grade} a \lessdot \operatorname{grade} b$. The direction from left to right is the axiom. For the converse, suppose $a < c < b$. Then $\operatorname{grade} a < \operatorname{grade} c < \operatorname{grade} b$ by strict monotonicity, which contradicts the cover of the grades. In a linear order the grade is an order embedding, and `grade_le_grade_iff`, `grade_lt_grade_iff` and `grade_injective` state it. A grading by a well-founded order makes the graded order well-founded: `GradeOrder.wellFoundedLT`. The proof pulls a descending sequence of $\alpha$ back to a descending sequence of grades, which cannot exist. As a consequence, an `ℕ`-graded order has the instance `WellFoundedLT`. Each flag of a graded order, that is each maximal chain `Flag α`, is graded again by the restriction of the grade.

**The height of chains.** The module `Mathlib.Order.Height` defines `Set.chainHeight s r : ℕ∞`, the supremum of the numbers of elements `Set.encard t` over the chains $t \subseteq s$ for the relation $r$. The value `⊤` means that $s$ has arbitrarily long finite chains, by `Set.chainHeight_eq_top_iff`. The basic bounds are `Set.chainHeight_le_encard` and `Set.chainHeight_mono`. A chain inside $s$ gives a lower bound, `Set.encard_le_chainHeight_of_isChain`: if $t \subseteq s$ and $t$ is an $r$-chain, then $|t| \le \operatorname{chainHeight}(s)$. This is the definition of a supremum applied to the term $t$. When the height is finite, `Set.exists_eq_chainHeight_of_chainHeight_ne_top` finds a chain that reaches it, and `Set.exists_isChain_of_le_chainHeight` finds a chain of each smaller size. The height does not change under relation embeddings (`Set.chainHeight_eq_of_relEmbedding`) or under reversal of the relation (`Set.chainHeight_flip`). The height of one element in a preorder is `Order.height`, in `Mathlib.Order.KrullDimension`.

#### Common errors

1. The arrow points up. `a ⋖ b` means that $b$ covers $a$, so $a$ is the smaller element. The lemma `CovBy.lt` gives `a < b`.
2. `grade` needs the grading type. Write `grade ℕ a`, not `grade a`. Without `ℕ` Lean cannot find the instance, because the same order can have gradings by `ℕ`, by `ℤ` and by `Fin n`.
3. `Set.chainHeight` counts elements, not steps. A chain $a_0 < a_1 < \dots < a_n$ has height $n + 1$ in Mathlib, while some books call its length $n$. So `Set.one_le_chainHeight_iff` says that the height is at least $1$ exactly for a nonempty set.

### Exercises

1. (A) Prove that in `ℤ` the element $n + 1$ covers $n$, with `covBy_iff_Ioo_eq` or with `covBy_of_eq_or_eq`.
2. (A) Show that in `Set α` the empty set is covered exactly by the singletons, with `Set.covBy_iff_exists_insert`.
3. (B) Prove `Prod.covBy_iff` from the definition of the product order, and find a cover in `ℕ × ℕ` that is not of the form $(n, m) \lessdot (n + 1, m)$ or $(n, m) \lessdot (n, m + 1)$, or prove that none exists.
4. (B) Let $\alpha$ be a linear order with a grading by `ℕ`. Prove that the grade is injective, and compare with `grade_injective`.
5. (B) Give a partial order where two different elements are covered by the same element, and explain why this does not contradict `CovBy.unique_left`.
6. (C) Prove that a finite set $s$ of a partial order has `Set.chainHeight` at most $k$ for the relation `<` if and only if $s$ is a union of at most $k$ antichains (Mirsky's theorem). Use the height of each element inside $s$.

### Reference

<?reference?>
