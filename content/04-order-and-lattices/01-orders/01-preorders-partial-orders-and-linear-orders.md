---
title: Preorders, partial orders and linear orders
kind: theory
modules:
  - Mathlib.Order.Defs.PartialOrder
  - Mathlib.Order.Defs.LinearOrder
  - Mathlib.Order.Antisymmetrization
  - Mathlib.Order.Basic
  - Mathlib.Order.Defs.Unbundled
  - Mathlib.Order.Defs.Prop
  - Mathlib.Order.Compare
  - Mathlib.Order.Comparable
  - Mathlib.Order.Circular
  - Mathlib.Order.Circular.ZMod
explains:
  E3: [PartialOrder, LinearOrder]
  E2: [Preorder, le_antisymm, lt_iff_le_not_ge, le_total, not_lt, lt_trichotomy, Preorder.lift, PartialOrder.lift, Antisymmetrization, AntisymmRel, Prod.mk_le_mk, Prod.Lex.le_iff]
  E1: [le_refl, le_trans, lt_irrefl, lt_of_le_of_lt, lt_of_lt_of_le, le_antisymm_iff, min_le_left, le_max_left, lt_of_le_of_ne, not_le, le_rfl, toAntisymmetrization_le_toAntisymmetrization_iff]
families: []
requires: [V01]
reads_with: ["MIL", "TPIL"]
lean:
  - MathlibHandbook/V04/C01/Examples.lean
  - MathlibHandbook/V04/C01/Exercises.lean
  - MathlibHandbook/V04/C01/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Preorders, partial orders and linear orders

### Overview

Many parts of mathematics compare objects. Numbers are compared by size, sets by inclusion, natural numbers by divisibility, functions by their values at each point. Each of these comparisons is a relation $\le$ with a few common properties. Order theory studies them once, so that a theorem proved for an abstract order applies to each of them.

There are three levels of axioms. A preorder has a reflexive and transitive relation. A partial order adds antisymmetry: two elements that are below each other are equal. A linear order adds totality: any two elements are comparable. The relation "$|x| \le |y|$" on the integers is a preorder that is not a partial order, because $-1$ and $1$ are below each other.

This section gives the three definitions, the strict relation $<$, the basic lemmas with complete proofs, and four ways to build new orders: the product order, the lexicographic order, the pulled-back order and the quotient of a preorder that makes it a partial order.

### Definitions

**Definition (Preorder).** A preorder on a set $\alpha$ is a relation $\le$ on $\alpha$ such that:

1. $a \le a$ for each $a \in \alpha$ (reflexivity);
2. $a \le b$ and $b \le c$ give $a \le c$ (transitivity).

The strict relation of a preorder is $a < b$ if and only if $a \le b$ and $\lnot(b \le a)$.

The definition of $<$ needs care. In a preorder, the form "$a \le b$ and $a \ne b$" is not correct: in the preorder $|x| \le |y|$ on $\mathbb{Z}$, $-1 \le 1$ and $-1 \ne 1$, but $1 \le -1$ also holds, so $-1 < 1$ is false. In a partial order the two forms agree (Theorem (Strict order in a partial order) below).

::: mathlib
`Preorder` · `Mathlib.Order.Defs.PartialOrder`

The class `Preorder α` has the fields `le`, `lt`, `le_refl`, `le_trans` and `lt_iff_le_not_ge`. So `<` is a field, not a definition. An instance can give its own `<`, for example the `<` of `ℕ` that the kernel computes, and then prove that it agrees with the formula. The notation `a ≥ b` is `b ≤ a` by definition.

<?decl Preorder?>
:::

**Definition (Partial order).** A partial order is a preorder such that $a \le b$ and $b \le a$ give $a = b$ (antisymmetry).

Antisymmetry is the main way to prove that two elements are equal: two sets are equal when each is a subset of the other.

::: mathlib
`PartialOrder` · `Mathlib.Order.Defs.PartialOrder`

The class extends `Preorder` with the field `le_antisymm`. The lemma `le_antisymm` takes the two inequalities and gives the equality. The lemma `le_antisymm_iff` states the equivalence $a = b \iff a \le b \land b \le a$. The tactic `apply le_antisymm` leaves one goal for each inequality.

<?decl PartialOrder?>
:::

**Definition (Linear order).** A linear order, or total order, is a partial order such that $a \le b$ or $b \le a$ for any two elements $a$ and $b$ (totality).

::: mathlib
`LinearOrder` · `Mathlib.Order.Defs.LinearOrder`

The class has the field `le_total`, the functions `min` and `max`, and three decision procedures: one for `≤`, one for `<` and one for `=`. So the term `if a ≤ b then x else y` is correct on each linear order. The lemmas `min_le_left` and `le_max_left` give the basic facts.

<?decl LinearOrder?>
:::

**Definition (Antisymmetrization).** Let $\le$ be a preorder on $\alpha$. Write $a \sim b$ when $a \le b$ and $b \le a$. The antisymmetrization of $\alpha$ is the quotient $\alpha/{\sim}$ with the relation $[a] \le [b]$ if and only if $a \le b$.

The relation $\sim$ is an equivalence relation. It is reflexive because $a \le a$. It is symmetric by its form. It is transitive: $a \sim b$ and $b \sim c$ give $a \le b \le c$ and $c \le b \le a$. The relation on the classes is well defined: if $a \sim a'$ and $b \sim b'$ and $a \le b$, then $a' \le a \le b \le b'$, so $a' \le b'$.

::: mathlib
`Antisymmetrization` · `Mathlib.Order.Antisymmetrization`

The relation $\sim$ is `AntisymmRel (· ≤ ·)`, and the quotient is `Antisymmetrization α (· ≤ ·)`. The map to the quotient is `toAntisymmetrization`, and the lemma `toAntisymmetrization_le_toAntisymmetrization_iff` says that the order on the classes is the order on the representatives. The instance `instPartialOrderAntisymmetrization` gives the partial order.

<?decl Antisymmetrization?>
:::

### Theorems and proofs

**Theorem (Irreflexivity and asymmetry).** In a preorder, $\lnot(a < a)$ for each $a$. If $a < b$, then $\lnot(b < a)$.

*Proof.* Suppose $a < a$. By the definition of $<$, this means $a \le a$ and $\lnot(a \le a)$. This is a contradiction. For the second claim, suppose $a < b$ and $b < a$. Then $a \le b$ from the first, and $\lnot(a \le b)$ from the second. This is again a contradiction. $\square$

**Theorem (Mixed transitivity).** In a preorder, $a < b$ and $b \le c$ give $a < c$. Also, $a \le b$ and $b < c$ give $a < c$. In particular, $<$ is transitive.

*Proof.* Assume $a < b$ and $b \le c$. From $a < b$ there is $a \le b$, and transitivity gives $a \le c$. It remains to show $\lnot(c \le a)$. Suppose $c \le a$. Then $b \le c$ and $c \le a$ give $b \le a$. This contradicts $a < b$, which contains $\lnot(b \le a)$. So $a < c$.

Now assume $a \le b$ and $b < c$. Then $a \le c$ by transitivity. Suppose $c \le a$. Then $c \le a$ and $a \le b$ give $c \le b$, and this contradicts $b < c$. So $a < c$.

For the transitivity of $<$, assume $a < b$ and $b < c$. Then $b \le c$, and the first part gives $a < c$. $\square$

**Theorem (Strict order in a partial order).** In a partial order, $a < b$ if and only if $a \le b$ and $a \ne b$.

*Proof.* Assume $a < b$. Then $a \le b$. If $a = b$, then $a < a$, which is false by irreflexivity. So $a \ne b$. Conversely, assume $a \le b$ and $a \ne b$. Suppose $b \le a$. Then antisymmetry gives $a = b$, a contradiction. So $\lnot(b \le a)$, and $a < b$. $\square$

**Theorem (The quotient is a partial order).** The antisymmetrization of a preorder is a partial order.

*Proof.* Reflexivity and transitivity on the classes follow from the same properties of the representatives, because $[a] \le [b]$ means $a \le b$. For antisymmetry, let $[a] \le [b]$ and $[b] \le [a]$. Then $a \le b$ and $b \le a$, so $a \sim b$, and $[a] = [b]$ by the definition of the quotient. $\square$

**Theorem (Negation of a strict inequality).** In a linear order, $\lnot(a < b)$ if and only if $b \le a$. Also, $\lnot(a \le b)$ if and only if $b < a$.

*Proof.* Assume $b \le a$. If $a < b$, then $\lnot(b \le a)$, a contradiction. So $\lnot(a < b)$. Conversely, assume $\lnot(a < b)$. By totality, $a \le b$ or $b \le a$. In the second case the claim holds. In the first case, $a \le b$ holds and $a < b$ fails, so by the definition of $<$ the part $\lnot(b \le a)$ fails, that is, $b \le a$.

For the second statement, assume $\lnot(a \le b)$. By totality, $b \le a$, and with $\lnot(a \le b)$ this is the definition of $b < a$. Conversely, $b < a$ contains $\lnot(a \le b)$. $\square$

**Theorem (Trichotomy).** In a linear order, exactly one of $a < b$, $a = b$, $b < a$ holds.

*Proof.* First, at least one holds. If $a = b$, the claim holds. Assume $a \ne b$. By totality, $a \le b$ or $b \le a$. In the first case, $a \le b$ and $a \ne b$ give $a < b$ by Theorem (Strict order in a partial order). In the second case, $b < a$ in the same way.

Second, at most one holds. The relations $a < b$ and $b < a$ exclude each other by asymmetry. The relation $a = b$ excludes $a < b$, because $a < a$ is false, and in the same way it excludes $b < a$. $\square$

::: mathlib
`lt_iff_le_not_ge` · `Mathlib.Order.Defs.PartialOrder`

This lemma is the field of `Preorder` that links `<` and `≤`. In a partial order, `lt_iff_le_and_ne` gives the other form, and `lt_of_le_of_ne` builds `a < b` from the two parts. The proof of irreflexivity is `lt_irrefl`, and the mixed forms of transitivity are `lt_of_lt_of_le` and `lt_of_le_of_lt`.

<?decl lt_iff_le_not_ge?>
:::

::: mathlib
`not_lt` · `Mathlib.Order.Defs.LinearOrder`

The lemmas `not_lt` and `not_le` are `simp` lemmas, so `simp` turns a negated inequality into an inequality in a linear order. The lemma `lt_trichotomy` gives the three cases as a disjunction.

<?decl not_lt?>
:::

::: mathlib
`le_total` · `Mathlib.Order.Defs.LinearOrder`

The lemma `le_total a b` is the proof of `a ≤ b ∨ b ≤ a`. A proof by cases on the order of two elements starts with `rcases le_total a b with h | h`.

<?decl le_total?>
:::

### Examples

**Example (The natural numbers).** The usual order on $\mathbb{N}$ is a linear order. Each order axiom is a lemma about $\mathbb{N}$, and the lemma `le_trans` of a general preorder applies to it.

<?lean MathlibHandbook/V04/C01/Examples.lean#preorder?>

**Example (Antisymmetry).** On $\mathbb{N}$, the two inequalities $m \le n$ and $n \le m$ give $m = n$.

<?lean MathlibHandbook/V04/C01/Examples.lean#antisymm?>

**Example (The strict order).** In a general preorder, the strict relation unfolds to the formula of the definition.

<?lean MathlibHandbook/V04/C01/Examples.lean#lt?>

**Example (Divisibility).** On $\mathbb{N}$, let $a \preceq b$ mean $a \mid b$. This is a partial order. It is reflexive, since $a = 1 \cdot a$. It is transitive: if $b = ka$ and $c = lb$, then $c = (lk)a$. It is antisymmetric: let $a \mid b$ and $b \mid a$. If $a = 0$, then $b = k \cdot 0 = 0$, so $a = b$. If $a \ne 0$, then $b = ka$ and $a = lb = lka$, so $lk = 1$ and $l = k = 1$, which gives $a = b$. The order is not linear, because neither $2 \mid 3$ nor $3 \mid 2$. In this order, $1$ is the least element and $0$ is the greatest element, since $n \mid 0$ for each $n$. On $\mathbb{Z}$ the same relation is only a preorder, because $1 \mid -1$ and $-1 \mid 1$ but $1 \ne -1$.

**Counterexample (A partial order that is not linear).** The subsets of $\mathbb{N}$ with $\subseteq$ are a partial order. The sets $\{0\}$ and $\{1\}$ are not comparable, so the order is not linear.

<?lean MathlibHandbook/V04/C01/Examples.lean#not_linear?>

**Example (Totality on the reals).** On $\mathbb{R}$, any two numbers are comparable.

<?lean MathlibHandbook/V04/C01/Examples.lean#total?>

**Example (A negated inequality).** In a linear order, $\lnot(x < y)$ turns into $y \le x$.

<?lean MathlibHandbook/V04/C01/Examples.lean#not_lt?>

**Example (Minimum and maximum).** A linear order has the functions $\min$ and $\max$, with $\min(a,b) \le a$ and $a \le \max(a,b)$.

<?lean MathlibHandbook/V04/C01/Examples.lean#min_max?>

**Example (The product order).** Let $\alpha$ and $\beta$ be preorders. On $\alpha \times \beta$ put $(a_1, b_1) \le (a_2, b_2)$ if and only if $a_1 \le a_2$ and $b_1 \le b_2$. This is a preorder, and it is a partial order when $\alpha$ and $\beta$ are partial orders: from $(a_1,b_1) \le (a_2,b_2)$ and the reverse, antisymmetry in each factor gives $a_1 = a_2$ and $b_1 = b_2$. It is almost never linear. In $\mathbb{N} \times \mathbb{N}$, the pairs $(1, 0)$ and $(0, 1)$ are not comparable. Compute the strict relation: $(0,0) < (1,0)$, because $(0,0) \le (1,0)$ and $(1,0) \not\le (0,0)$. So $<$ in the product is not "$<$ in each coordinate". The same construction on functions gives the pointwise order on $\iota \to \alpha$: $f \le g$ if and only if $f(i) \le g(i)$ for each $i$.

**Example (The lexicographic order).** On $\mathbb{N} \times \mathbb{N}$ put $(a_1, b_1) \le_{\mathrm{lex}} (a_2, b_2)$ if and only if $a_1 < a_2$, or $a_1 = a_2$ and $b_1 \le b_2$. This is the order of a dictionary. It is a linear order. Totality: if $a_1 \ne a_2$, then one of $a_1 < a_2$ and $a_2 < a_1$ holds by trichotomy; if $a_1 = a_2$, then $b_1 \le b_2$ or $b_2 \le b_1$. Antisymmetry: if both inequalities hold, then $a_1 < a_2$ is impossible, because the reverse inequality would need $a_2 < a_1$ or $a_2 = a_1$, and both contradict $a_1 < a_2$. So $a_1 = a_2$, and then $b_1 \le b_2 \le b_1$ gives $b_1 = b_2$. Transitivity is a check of four cases, given as Exercise 6. Compute: $(0, 100) <_{\mathrm{lex}} (1, 0)$, and $(2, 3) <_{\mathrm{lex}} (2, 5)$.

**Example (An order pulled back along a function).** Let $f : \alpha \to \beta$ and let $\beta$ be a preorder. Put $a \le_f a'$ if and only if $f(a) \le f(a')$. This is a preorder on $\alpha$: reflexivity and transitivity come from $\beta$. When $\beta$ is a partial order and $f$ is injective, it is a partial order: $f(a) \le f(a')$ and $f(a') \le f(a)$ give $f(a) = f(a')$, and injectivity gives $a = a'$. When $f$ is not injective, antisymmetry fails. For $f = |\cdot| : \mathbb{Z} \to \mathbb{N}$, the preorder $\le_f$ has $1 \le_f -1$ and $-1 \le_f 1$. Its antisymmetrization identifies $n$ with $-n$, and the quotient is isomorphic to $\mathbb{N}$ with its usual order.

::: mathlib
`Preorder.lift` · `Mathlib.Order.Basic`

The pulled back order of the last example is `Preorder.lift f`, and `PartialOrder.lift f hf` needs the proof `hf` that `f` is injective. Mathlib uses these to define the order on a subtype, where `f` is the coercion `Subtype.val`.

<?decl Preorder.lift?>
:::

::: mathlib
`Prod.mk_le_mk` · `Mathlib.Order.Basic`

The instance on `α × β` is the product order, and `Prod.mk_le_mk` unfolds it on pairs. The lexicographic order lives on the type synonym `Lex (α × β)`, written `α ×ₗ β`, with the maps `toLex` and `ofLex`. The lemma `Prod.Lex.le_iff` gives the rule of the dictionary. This is how Mathlib puts two orders on one set without a conflict.

<?decl Prod.Lex.le_iff?>
:::

### The library around it

The names of the lemmas follow a pattern. A name such as `lt_of_le_of_lt` gives the conclusion first and then the hypotheses in order. The dot notation `h.trans` is a short form of `le_trans h`, `h.le` turns `h : a < b` into `a ≤ b`, and `h.ne` turns it into `a ≠ b`. The lemma `le_rfl` is `le_refl` with an implicit argument, and it is the usual term for a goal `a ≤ a`.

Several tactics use these axioms. The tactic `order` proves goals that follow from the hypotheses by the axioms of a partial order or of a linear order. The tactics `omega` and `linarith` prove linear goals on `ℕ`, `ℤ` and `ℝ`.

The file `Mathlib.Order.Basic` holds most of the small rules that mix `≤`, `<` and `=`, in the dot notation of the first paragraph. Examples are `LE.le.trans_lt`, `LT.lt.trans_le`, `LE.le.lt_of_ne`, `LE.le.lt_or_eq` and `Ne.lt_of_le`, with the two characterizations `le_iff_eq_or_lt` and `lt_iff_le_and_ne`. The lemma `le_of_forall_le` says that $a \le b$ when each $c \le a$ satisfies $c \le b$, and in a linear order `le_of_forall_lt` gives the same conclusion from strict inequalities. The file also gives the orders on the standard constructions. On a product, `Prod.mk_le_mk` compares the two coordinates, and `Prod.mk_lt_mk` says that $(a_1, b_1) < (a_2, b_2)$ if and only if $a_1 < a_2$ and $b_1 \le b_2$, or $a_1 \le a_2$ and $b_1 < b_2$. On functions, `Pi.le_def` (in `Mathlib.Order.Defs.Prop`) is the pointwise order, `Pi.lt_def` says that $f < g$ when $f \le g$ and $f\,i < g\,i$ for one $i$, and `StrongLT` is the stronger relation "$f\,i < g\,i$ for each $i$". On `Prop`, `le_Prop_eq` says that $p \le q$ is the implication $p \to q$. To move an order along a map, `Preorder.lift` and `PartialOrder.lift` pull back the order of the codomain, `LinearOrder.lift'` does the same for an injective map into a linear order, and `Function.Injective.partialOrder` keeps the given `≤` and `<` of the domain and only asks that the map respects them. The class `DenselyOrdered` says that there is an element strictly between two elements $a < b$. Its main lemmas are `exists_between`, `le_of_forall_lt_imp_le_of_dense` and `dense_or_discrete`.

The file `Mathlib.Order.Defs.Unbundled` has the unbundled form of the axioms, as classes on a relation `r : α → α → Prop` and not on a type. The classes `IsTrans`, `IsPreorder`, `IsPartialOrder`, `IsLinearOrder`, `IsStrictOrder`, `IsStrictTotalOrder` and `IsEquiv` say that $r$ is transitive, a preorder, and so on, and the lemmas `refl_of`, `trans_of`, `antisymm`, `irrefl` and `trichotomous_of` take the relation as an explicit argument. These classes occur where the relation is not the `≤` of a type, for example in the well-founded relations of this chapter and in the relation embeddings of Chapter 2. The same file defines the predicates `IsUpperSet` and `IsLowerSet`, the bundled `UpperSet` and `LowerSet`, and `Maximal` and `Minimal`, which the next section uses.

For a linear order, `Mathlib.Order.Compare` connects `≤` and `<` with the function `cmp`, which returns a value of type `Ordering`. The lemmas `cmp_eq_lt_iff`, `cmp_eq_eq_iff` and `cmp_eq_gt_iff` translate each value back, `cmp_compares` packs the three cases in `Ordering.Compares`, and `linearOrderOfCompares` builds a linear order from a comparison function. The file `Mathlib.Order.Comparable` names the incomparable pairs: `IncompRel r a b` means $\neg\, r\,a\,b \wedge \neg\, r\,b\,a$, and `Relation.SymmGen r` is the comparability relation. In a partial order, `lt_or_eq_or_gt_or_incompRel` says that two elements satisfy exactly one of $a < b$, $a = b$, $b < a$ or "incomparable", and `not_le_iff_lt_or_incompRel` refines `not_le` to partial orders.

The file `Mathlib.Order.Circular` treats the order of points on a circle, where "$b$ lies between $a$ and $c$" makes sense but "$a < b$" does not. The relation is ternary: `Btw.btw a b c` and its strict form `SBtw.sbtw a b c`. A `CircularOrder` asks that the relation is reflexive, cyclic (`btw_cyclic`), antisymmetric and total, and `CircularPartialOrder` and `CircularPreorder` drop the last axioms. A linear order gives a circular order by `LinearOrder.toCircularOrder`, with the rule `btw_iff`: $a, b, c$ are in circular order if they are in increasing order after a cyclic shift. The circular intervals are `Set.cIcc` and `Set.cIoo`, and `Set.compl_cIcc` says that the complement of a closed arc is the open arc in the other direction. The file `Mathlib.Order.Circular.ZMod` gives the instances on `ℤ`, `Fin n` and `ZMod n`, with `Int.btw_iff` and `Fin.btw_iff`.

### Exercises

1. (A) State the axioms of a preorder, of a partial order and of a linear order. For each of the relations $<$ on $\mathbb{R}$, $\subseteq$ on the subsets of $\{0,1\}$, and "$x - y \in \mathbb{Z}$" on $\mathbb{R}$, say which axioms hold. *Hint:* the first is not reflexive; the last is symmetric.
2. (A) Give a preorder that is not a partial order, and compute its antisymmetrization. *Hint:* use the cardinality of finite sets.
3. (A) Draw the divisors of $12$ with the divisibility order, with an edge from $a$ up to $b$ when $a \mid b$ and no divisor lies strictly between them.
4. (B) Show that in a preorder, $a < b$ and $b < c$ give $a < c$, without the mixed form of transitivity. *Hint:* unfold both hypotheses.
5. (B) Show that divisibility on $\mathbb{Z}$ is a preorder and not a partial order. *Hint:* $a \mid b$ and $b \mid a$ give $b = \pm a$.
6. (B) Prove that the lexicographic order on $\mathbb{N} \times \mathbb{N}$ is transitive. *Hint:* split each inequality into its two cases.
7. (B) Show that in a linear order, $\min(a, b) \le \max(a, b)$, and that $\min(a,b) = a$ if and only if $a \le b$.
8. (C) Let $\le$ be a relation that is irreflexive and transitive, and define $a \le' b$ as $a < b$ or $a = b$. Show that $\le'$ is a partial order whose strict relation is $<$. *Hint:* for antisymmetry, $a < b$ and $b < a$ give $a < a$.
9. (L) Prove that $a < b$ and $b \le c$ give $a < c$ in a preorder. The solution is `lt_of_lt_of_le_example`.
10. (L) Prove that $a \le b$ and $b \le a$ give $b = a$ in a partial order. The solution is `eq_of_le_of_le_example`.
11. (L) Prove that $b \le \max(a, b)$ in a linear order. The solution is `le_max_example`.

### Notes and history

The axioms of a partial order go back to the work of Peirce and Schröder on the algebra of logic in the 1880s. Hausdorff studied ordered sets in his *Grundzüge der Mengenlehre* (1914). Birkhoff, *Lattice Theory* (1940, third edition 1967), Chapter I, gives the standard treatment. Davey and Priestley, *Introduction to Lattices and Order* (2002), Chapter 1, is a modern textbook at the level of this volume.

In Mathlib, the classes were first in the core library of Lean 3, and they moved to Mathlib with the port to Lean 4. The use of type synonyms such as `Lex` and `OrderDual` for a second order on the same set is a design rule of the library.

### Reference

<?reference?>
