---
title: Minimal and maximal elements of a predicate
kind: api
modules:
  - Mathlib.Order.Minimal
  - Mathlib.Order.Preorder.Finite
  - Mathlib.Order.SetIsMax
explains:
  E2: [minimal_iff_forall_lt, Minimal.le, Minimal.mono, minimal_iff_isMin, Set.maximal_iff_forall_insert, exists_minimal_le_of_wellFoundedLT, Set.Finite.exists_le_maximal, StrictMono.apply_eq, Set.not_isMax_coe]
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

## Minimal and maximal elements of a predicate

### Overview

The section on bounds defines `Maximal P x`: the element $x$ satisfies $P$, and no element that satisfies $P$ lies strictly above $x$. The minimal elements, `Minimal P x`, are the dual notion. The predicate $P$ is a function `α → Prop`, not a set. A maximal element of a set $s$ is `Maximal (· ∈ s) x`, and a maximal element of the whole type is `IsMax x`. Zorn's lemma gives its result in this form: `zorn_subset` gives an $m$ with `Maximal (· ∈ S) m`.

The module `Mathlib.Order.Minimal` holds the API of these two predicates. It gives other forms of the definition, the rules for a change of the predicate, the behaviour under duality and under order embeddings, the special form for predicates on sets, and the existence of minimal elements in a well-founded order. The module `Mathlib.Order.Preorder.Finite` proves that a nonempty finite set has minimal and maximal elements, and draws consequences for finite linear orders. The small module `Mathlib.Order.SetIsMax` compares maximality in a subtype with maximality in the whole type.

All the lemmas come in pairs. A lemma about `Minimal` has a twin about `Maximal` with the order reversed, and Mathlib generates most twins with the attribute `to_dual`. This section states the minimal form, unless the maximal form is the more common one.

### The library around it

#### The definition and its other forms

The definition is `Minimal P x = P x ∧ ∀ ⦃y⦄, P y → y ≤ x → x ≤ y`. It needs only `LE α`. The two parts are `Minimal.prop` and `Minimal.le_of_le`, and for maximal elements `Maximal.prop` and `Maximal.le_of_ge`. In a preorder the condition "$y \le x$ gives $x \le y$" says that $y < x$ is false. So `minimal_iff_forall_lt` states

$$\operatorname{Minimal} P\,x \iff P\,x \land \forall y,\ y < x \to \lnot P\,y.$$

The proof unfolds $y < x$ as $y \le x \land \lnot (x \le y)$. In a partial order the condition becomes an equality, `minimal_iff`: $P\,y$ and $y \le x$ give $x = y$. The negative forms `not_minimal_iff_exists_lt` and `exists_lt_of_not_minimal` give an element $y < x$ with $P\,y$ when $x$ is not minimal. The lemmas `Minimal.not_lt` and `Minimal.not_prop_of_lt` use a minimal element.

In a linear order a minimal element is a least element. This is `Minimal.le`: if `Minimal P x` and $P\,y$, then $x \le y$. Proof: by totality, $x \le y$ or $y \le x$. In the second case minimality gives $x \le y$. In a partial order this fails: in the discrete order on two points both points are minimal, and neither is below the other.

The module computes the minimal and maximal elements of the common predicates.

| Lean name | Statement |
|---|---|
| `minimal_true` | `Minimal (fun _ ↦ True) x ↔ IsMin x` |
| `minimal_false` | no element is minimal for `False` |
| `minimal_eq_iff` | `Minimal (· = y) x ↔ x = y` |
| `minimal_ge_iff` | `Minimal (y ≤ ·) x ↔ x = y` in a partial order |
| `minimal_le_iff` | `Minimal (· ≤ y) x ↔ x ≤ y ∧ IsMin x` |
| `minimal_mem_Icc` | for $a \le b$, the only minimal element of $[a, b]$ is $a$ |
| `maximal_mem_Ioc` | for $b < a$, the only maximal element of $(b, a]$ is $a$ |
| `IsLeast.minimal_iff` | if $a$ is least in $s$, then $a$ is the only minimal element of $s$ |
| `minimal_minimal` | `Minimal (Minimal P) x ↔ Minimal P x` |

The general tool behind the last rows is `minimal_iff_eq`: if $y$ satisfies $P$ and lies below each element that satisfies $P$, then $y$ is the only minimal element.

#### Changing the predicate

A minimal element of a large predicate stays minimal in a smaller one. This is `Minimal.mono`: if `Minimal P x`, $Q \le P$ and $Q\,x$, then `Minimal Q x`. The proof is one line: an element $y$ with $Q\,y$ and $y \le x$ satisfies $P\,y$, so minimality for $P$ gives $x \le y$. The lemmas `Minimal.and_right` and `Minimal.and_left` add a condition that $x$ satisfies. The lemma `minimal_and_iff_right_of_imp` removes a condition that follows from $P$, and `Minimal.or` splits a minimal element of $P \lor Q$.

A predicate that is closed downward has a simple answer. If $P\,y$ and $x \le y$ always give $P\,x$, then `minimal_iff_isMin` states `Minimal P x ↔ P x ∧ IsMin x`. Proof: if $x$ is minimal for $P$ and $y \le x$, then $P\,y$ holds by the closure, so $x \le y$. Thus $x$ is minimal in the whole type. The converse is clear. The lemma `minimal_iff_minimal_of_imp_of_forall` compares two predicates $Q \Rightarrow P$ such that each element of $P$ lies above an element of $Q$.

For a subtype, `minimal_subtype` translates a minimal element of `Subtype Q` into a minimal element of $P \sqcap Q$, and `minimal_true_subtype` gives the minimal elements of the whole subtype.

#### Duality and order maps

The lemma `minimal_toDual` states that $x$ is minimal for $P$ in `αᵒᵈ` exactly when $x$ is maximal for $P$ in $\alpha$, and `maximal_toDual` is the converse. The one-way forms `Minimal.dual` and `Maximal.dual` have names from the attribute `to_dual`: `Maximal.dual` takes a `Minimal` hypothesis. The iff forms are easier to read.

An order embedding $f$ keeps minimal elements of sets: `OrderEmbedding.minimal_mem_image_iff` states that $f\,a$ is minimal in $f(s)$ if and only if $a$ is minimal in $s$. The lemma `OrderIso.image_setOfPred_minimal` computes the image of the set of minimal elements under an order isomorphism. For a map that is only an embedding on $s$, the lemmas `image_monotone_setOfPred_minimal` and `minimal_mem_image_monotone_iff` ask for $f\,x \le f\,y \leftrightarrow x \le y$ for the elements $x, y$ of the predicate or the set, and the antitone forms exchange minimal and maximal elements. The definition `OrderIso.mapSetOfPredMinimal` turns an order isomorphism $s \simeq t$ into an order isomorphism between the sets of minimal elements, and `OrderIso.setOfPredMinimalIsoSetOfPredMaximal` does the same for an antitone isomorphism.

#### Predicates on sets

When $\alpha$ is `Set β`, the order is inclusion, and the module states the lemmas with `⊆` and `⊂`. The basic forms are `minimal_subset_iff` and `maximal_subset_iff`: a set $s$ is minimal for $P$ if $P\,s$ holds and each $t \subseteq s$ with $P\,t$ is equal to $s$. The strict forms are `Set.minimal_iff_forall_ssubset` and `Set.maximal_iff_forall_ssuperset`.

The useful case is a predicate that is closed under subsets, such as "linearly independent". For such a $P$, `Set.maximal_iff_forall_insert` states

$$\operatorname{Maximal} P\,s \iff P\,s \land \forall x \notin s,\ \lnot P(s \cup \{x\}).$$

Proof: the direction from left to right holds because $s \cup \{x\}$ is strictly larger than $s$ when $x \notin s$. For the converse, let $t \supseteq s$ with $P\,t$, and suppose $x \in t \setminus s$. Then $s \cup \{x\} \subseteq t$, so $P(s \cup \{x\})$ holds by the closure, a contradiction. So $t = s$. The dual `Set.minimal_iff_forall_sdiff_singleton` treats a predicate closed under supersets: $s$ is minimal when no single point can be removed. The one-way lemmas are `Set.exists_insert_of_not_maximal`, `Maximal.mem_of_prop_insert` and `Minimal.notMem_of_prop_sdiff_singleton`.

#### Minimal values of a function

The predicate `MinimalFor P f i` says that $i$ satisfies $P$ and that $f\,i$ is minimal among the values $f\,j$ with $P\,j$. Its definition is `P i ∧ ∀ ⦃j⦄, P j → f j ≤ f i → f i ≤ f j`, and `minimalFor_id` says that `MinimalFor P id x` is `Minimal P x`. The index $i$ is not unique, even in a linear order, because two indices can have the same value. The lemmas `minimalFor_iff_forall_lt`, `MinimalFor.not_lt` and `MinimalFor.le` are the forms of the lemmas above. The lemma `MinimalFor.minimal_of_strictMonoOn` turns a minimal value of a strictly monotone $g$ into a minimal element, and `MinimalFor.of_strictMonoOn_comp` removes a strictly monotone map $g$ from `MinimalFor Q (g ∘ f) i`.

#### Existence of minimal elements

In a well-founded order each nonempty predicate has a minimal element: `exists_minimal_of_wellFoundedLT`. The stronger form `exists_minimal_le_of_wellFoundedLT` finds a minimal element below a given element $a$ with $P\,a$. Proof: apply the first lemma to the predicate $y \mapsto P\,y \land y \le a$. This gives a minimal element $b$ of that predicate. If $P\,y$ and $y \le b$, then $y \le a$, so $b \le y$ by minimality. Thus $b$ is minimal for $P$. The maximal form `exists_maximal_ge_of_wellFoundedGT` uses the ascending chain condition, and `exists_minimalFor_of_wellFoundedLT` finds a minimal value of a function.

The module `Mathlib.Order.Preorder.Finite` proves the same for finite sets in an arbitrary preorder. The main lemma is `Set.Finite.exists_le_maximal`: if $s$ is finite and $a \in s$, then some $b \ge a$ is maximal in $s$. Proof: suppose not. Then $a$ is not maximal, so there is $b_1 > a$ in $s$. The element $b_1$ is not maximal, so there is $b_2 > b_1$ in $s$, and so on. The sequence $a < b_1 < b_2 < \dots$ has no repeated element, because $<$ is transitive and irreflexive. This contradicts the finiteness of $s$. The variants are `Set.Finite.exists_maximal`, `Set.Finite.exists_le_minimal`, the `Finset` forms such as `Finset.exists_maximal` and `Finset.exists_le_minimal`, the forms `Finite.exists_le_maximal` for a finite type, and the forms `Set.Finite.exists_maximalFor` for a function. The weakest forms need only `LE α` with a transitive relation.

The contrapositive gives infinite sets. The lemma `Set.infinite_of_forall_exists_gt` says that a set with elements above each element of a nonempty type is infinite. The lemmas `Set.finite_isTop` and `Set.finite_isBot` say that a partial order has finitely many top elements; in fact it has at most one.

For finite linear orders the module has three uniqueness results. The lemma `StrictMono.apply_eq` states that a strictly monotone map $f$ from a finite linear order to itself is the identity. Proof: suppose $f\,x \ne x$ for some $x$, and take $x$ minimal with this property. If $f\,x < x$, then $f(f\,x) = f\,x$ by minimality, but strict monotonicity gives $f(f\,x) < f\,x$. If $f\,x > x$, then $f$ maps the finite set $\{y \mid y \ge x\}$ injectively into $\{y \mid y > x\}$, which is smaller. The lemma `OrderEmbedding.range_eq_iff` says that two order embeddings of a finite linear order with the same range are equal, and `OrderHom.range_eq_iff` gives the same for injective monotone maps. The pigeonhole lemma `Set.Infinite.exists_lt_map_eq_of_mapsTo` finds $x < y$ in an infinite set with $f\,x = f\,y$ when $f$ takes values in a finite set.

#### Maximality in a subtype

The module `Mathlib.Order.SetIsMax` has two lemmas. For a set $S \subseteq J$ and $m \in S$, `Set.not_isMax_coe` says: if $m$ is not maximal in the subtype $S$, then $m$ is not maximal in $J$. Proof: an element of $S$ strictly above $m$ is an element of $J$ strictly above $m$. The converse is false, because an element above $m$ in $J$ need not lie in $S$. The twin `Set.not_isMin_coe` treats minimal elements.

#### Common errors

1. The lemmas state the maximal elements of a set $s$ in the form `Maximal (· ∈ s) x`, that is, `Maximal (fun x ↦ x ∈ s) x`. Lean can accept `Maximal s x` when it unfolds `Set α` to a predicate, but the lemmas of the module do not match this form. Write the membership form.
2. In a partial order two minimal elements can differ, and a minimal element need not be least. The lemma `Minimal.le` needs a linear order. In a partial order use `minimal_iff` or `Minimal.le_of_le`.
3. The one-way duality lemmas have surprising names: `Maximal.dual` takes a hypothesis `Minimal P x`. Use `minimal_toDual` and `maximal_toDual` and rewrite with them.

### Exercises

1. (A) Show that in `ℕ` the only minimal element of a nonempty set $s$ is its least element, with `Minimal.le` and `minimal_iff`.
2. (A) Let $P$ be closed upward. Show `Maximal P x ↔ P x ∧ IsMax x`.
3. (B) Show that the set of minimal elements of a set $s$ in a partial order is an antichain: two distinct minimal elements are incomparable.
4. (B) In the power set of $\{1, 2, 3\}$, let $P\,s$ say that $s$ meets both $\{1, 2\}$ and $\{2, 3\}$. Find the minimal elements of $P$, and check `Set.minimal_iff_forall_sdiff_singleton` on them.
5. (B) Prove `Set.infinite_of_forall_exists_gt` from `Set.Finite.exists_le_maximal`.
6. (C) Give a preorder that is not a partial order and a finite set in it with a minimal element that is not unique up to equality, but is unique up to the relation $x \le y \land y \le x$. Show that this always holds for a finite chain.

### Reference

<?reference?>
