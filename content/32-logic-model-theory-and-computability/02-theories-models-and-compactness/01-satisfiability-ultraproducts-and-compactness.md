---
title: Satisfiability, ultraproducts and compactness
kind: theory
modules:
  - Mathlib.ModelTheory.Satisfiability
  - Mathlib.ModelTheory.Ultraproducts
  - Mathlib.ModelTheory.Skolem
  - Mathlib.ModelTheory.Equivalence
explains:
  E3: [FirstOrder.Language.Theory.IsSatisfiable, FirstOrder.Language.Theory.IsFinitelySatisfiable, FirstOrder.Language.Theory.ModelsBoundedFormula, FirstOrder.Language.Theory.IsComplete, FirstOrder.Language.Theory.isSatisfiable_iff_isFinitelySatisfiable, FirstOrder.Language.Theory.models_iff_not_satisfiable, FirstOrder.Language.Ultraproduct.sentence_realize, FirstOrder.Language.Ultraproduct.boundedFormula_realize_cast, FirstOrder.Language.Theory.exists_large_model_of_infinite_model, FirstOrder.Language.Theory.IsComplete.isComplete_iff_models_elementarily_equivalent, FirstOrder.Language.skolem₁, FirstOrder.Language.Theory.Iff]
  E2: [FirstOrder.Language.Theory.Model.isSatisfiable, FirstOrder.Language.Theory.IsSatisfiable.mono, FirstOrder.Language.Theory.IsSatisfiable.isFinitelySatisfiable, FirstOrder.Language.Theory.isSatisfiable_directed_union_iff, FirstOrder.Language.Theory.isSatisfiable_union_distinctConstantsTheory_of_infinite, FirstOrder.Language.Theory.models_sentence_iff, FirstOrder.Language.Theory.models_iff_finset_models, FirstOrder.Language.Theory.IsComplete.models_not_iff, FirstOrder.Language.Theory.IsComplete.realize_sentence_iff, FirstOrder.Language.Theory.IsMaximal, FirstOrder.Language.Theory.IsMaximal.isComplete, FirstOrder.Language.completeTheory.isComplete, FirstOrder.Language.completeTheory.isMaximal, FirstOrder.Language.Ultraproduct.setoidPrestructure, FirstOrder.Language.Ultraproduct.funMap_cast, FirstOrder.Language.Ultraproduct.term_realize_cast, FirstOrder.Language.Ultraproduct.realize_formula_cast, FirstOrder.Language.Ultraproduct.Product.instNonempty, FirstOrder.Language.skolem₁Structure, FirstOrder.Language.card_functions_sum_skolem₁_le, FirstOrder.Language.Substructure.skolem₁_reduct_isElementary, FirstOrder.Language.Substructure.elementarySkolem₁Reduct, FirstOrder.Language.exists_small_elementarySubstructure, FirstOrder.Language.exists_elementarySubstructure_card_eq, FirstOrder.Language.exists_elementaryEmbedding_card_eq, FirstOrder.Language.exists_elementarilyEquivalent_card_eq, FirstOrder.Language.Theory.exists_model_card_eq, Cardinal.Categorical, Cardinal.Categorical.isComplete, Cardinal.empty_infinite_Theory_isComplete, FirstOrder.Language.Theory.Imp, FirstOrder.Language.Theory.iff_iff_imp_and_imp, FirstOrder.Language.Theory.imp_antisymm, FirstOrder.Language.Theory.iffSetoid, FirstOrder.Language.Theory.Iff.all, FirstOrder.Language.Theory.Iff.not, FirstOrder.Language.Theory.Iff.imp, FirstOrder.Language.BoundedFormula.iff_not_not, FirstOrder.Language.BoundedFormula.imp_iff_not_sup, FirstOrder.Language.BoundedFormula.all_iff_not_ex_not]
  E1: auto
families: []
requires: [V32.C01, V13.C02, V03.C08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Satisfiability, ultraproducts and compactness

### Overview

A theory is satisfiable if it has a model. The compactness theorem says that a theory is satisfiable as soon as each finite part of it is. It is the main tool of model theory: it builds models with prescribed properties out of finite pieces. Gödel derived it from his completeness theorem, through finite proofs. The index of this edition has no declaration for a proof calculus of first-order logic, and Mathlib proves compactness by a purely semantic route: the ultraproduct of models of the finite parts is a model of the whole theory. The key step is the theorem of Łoś, which computes the truth of a formula in an ultraproduct coordinate by coordinate.

The section first fixes the semantic notions: satisfiable and finitely satisfiable theories, semantic consequence $T \models \varphi$, complete theories and equivalence of formulas modulo a theory. It then builds ultraproducts, proves Łoś's theorem and derives compactness with two consequences: theories with infinite models have arbitrarily large models, and finiteness is not first-order. It ends with Skolem functions, which the downward Löwenheim-Skolem theorem of Section 2 uses.

### Definitions

**Definition (Satisfiable).** A theory $T$ is satisfiable if it has a nonempty model. It is finitely satisfiable if each finite subset $T_0 \subseteq T$ is satisfiable.

In Mathlib, `T.IsSatisfiable` asks for an element of `T.ModelType` in the universe `max u v` of the language. A model in any universe is enough, by `Model.isSatisfiable`: the Skolem hull of the empty set, defined below, is a small elementary substructure.

**Definition (Semantic consequence).** Let $\varphi$ be a bounded formula. The theory $T$ models $\varphi$, written $T \models \varphi$, if $\varphi$ holds in each nonempty model of $T$ under each assignment of its free and bound variables.

**Definition (Complete and maximal theories).** A theory $T$ is complete if it is satisfiable and for each sentence $\varphi$, $T \models \varphi$ or $T \models \neg \varphi$. It is maximal if it is satisfiable and for each sentence $\varphi$, $\varphi \in T$ or $\neg\varphi \in T$.

**Definition (Equivalence modulo a theory).** Two bounded formulas $\varphi, \psi$ at the same level are equivalent modulo $T$, written $\varphi \Leftrightarrow_T \psi$, if $T \models \varphi \Leftrightarrow \psi$. The formula $\varphi$ implies $\psi$ modulo $T$ if $T \models \varphi \Rightarrow \psi$.

**Definition (Ultraproduct).** Let $(M_i)_{i \in I}$ be $L$-structures and let $u$ be an ultrafilter on $I$. On the product $\prod_i M_i$, put $x \sim y$ when $\{i : x_i = y_i\} \in u$. Define $f(x) := (f^{M_i}(x_{\cdot, i}))_i$ coordinatewise, and let $R(x)$ hold when $\{i : R^{M_i}(x_{\cdot, i})\} \in u$. These data respect $\sim$, so they define a structure on the quotient $\prod_u M_i := \prod_i M_i / {\sim}$, the ultraproduct.

For the claim that the data respect $\sim$, let $x \sim y$ coordinatewise in a tuple of length $n$. The finite intersection $E = \bigcap_{k < n} \{i : x_{k,i} = y_{k,i}\}$ lies in $u$. On $E$ the values $f^{M_i}$ agree, and the sets for $R(x)$ and $R(y)$ agree on $E$, so one is in $u$ if and only if the other is.

**Definition (Skolem functions).** For a language $L$, the language $L^{\mathrm{sk}}$ has, for each $n$, one $n$-ary function symbol $f_\varphi$ for each formula $\varphi(x_0, \dots, x_{n-1}, y)$ of $L$ at level $n + 1$ with no free variables, and no relation symbols. On a nonempty $L$-structure $M$, $f_\varphi(\bar a)$ is an element $b$ with $M \models \varphi(\bar a, b)$ if one exists, and an arbitrary element otherwise. The choice uses Hilbert's $\varepsilon$ operator, so it needs no further data.

### Theorems and proofs

**Proposition (Consequence and satisfiability).** For a sentence $\varphi$, $T \models \varphi$ if and only if $T \cup \{\neg \varphi\}$ is not satisfiable.

*Proof.* If $T \models \varphi$, then each model of $T$ satisfies $\varphi$, so no model of $T$ satisfies $\neg\varphi$. Conversely, suppose $T \cup \{\neg\varphi\}$ has no model, and let $M$ be a nonempty model of $T$. If $M \not\models \varphi$, then $M \models \neg\varphi$ and $M$ is a model of $T \cup \{\neg \varphi\}$, a contradiction. $\square$

**Lemma (Terms in an ultraproduct).** For a term $t$ and elements $[x_b]$ of the ultraproduct, $t$ has the value $[(t^{M_i}[i\text{-th coordinates}])_i]$.

*Proof.* This is the proposition on terms in a quotient of Chapter 1, Section 2, since the functions act coordinatewise. $\square$

**Theorem (Łoś).** Let $u$ be an ultrafilter on $I$ and let each $M_i$ be nonempty. For each bounded formula $\varphi$ and each tuple of elements $[x]$, $$\prod_u M_i \models \varphi([x]) \iff \{\, i \in I : M_i \models \varphi(x_i) \,\} \in u.$$ In particular, a sentence holds in $\prod_u M_i$ if and only if it holds in $M_i$ for $u$-almost all $i$.

*Proof.* Induction on $\varphi$, for all tuples at once. Write $A_\varphi = \{ i : M_i \models \varphi(x_i) \}$.

For $\bot$, the left side is false and $A_\bot = \varnothing \notin u$. For an equation $t_1 = t_2$, the lemma reduces the left side to $(t_1^{M_i}[x_i])_i \sim (t_2^{M_i}[x_i])_i$, which is $A_\varphi \in u$ by the definition of $\sim$. For a relation, the lemma and the definition of $R$ give the claim.

For $\varphi \Rightarrow \psi$, the set is $A = A_\varphi^c \cup A_\psi$. By induction, the left side says: $A_\varphi \in u$ implies $A_\psi \in u$. If $A_\varphi \notin u$, then $A_\varphi^c \in u$, since $u$ is an ultrafilter, so $A \in u$. If $A_\varphi \in u$ and $A_\psi \in u$, then $A \supseteq A_\psi$ is in $u$. Conversely, let $A \in u$ and $A_\varphi \in u$. Then $A \cap A_\varphi \subseteq A_\psi$, so $A_\psi \in u$.

For $\forall y\, \varphi$, let $A = \{ i : M_i \models \forall y\, \varphi(x_i, y) \}$. Suppose $A \in u$, and let $[y]$ be any element. The set $A_{\varphi}$ for the tuple $x, y$ contains $A$, so it is in $u$, and by induction $\varphi([x], [y])$ holds. Conversely, suppose $\varphi([x], [y])$ holds for every $[y]$, and suppose $A \notin u$. For $i \notin A$, choose $y_i \in M_i$ with $M_i \not\models \varphi(x_i, y_i)$. For $i \in A$, choose any $y_i \in M_i$; this uses that $M_i$ is nonempty. Then $\{ i : M_i \models \varphi(x_i, y_i) \} \subseteq A$, which is not in $u$. By induction, $\varphi([x], [y])$ fails, a contradiction. $\square$

**Theorem (Compactness).** A theory is satisfiable if and only if it is finitely satisfiable.

*Proof.* A model of $T$ is a model of each subset, so one direction is trivial. Conversely, let $T$ be finitely satisfiable. Let $I$ be the set of finite subsets of $T$. For $T_0 \in I$, choose a nonempty model $M_{T_0}$ of $T_0$. The sets $\{T_0 : T_0 \supseteq S\}$ for $S \in I$ generate the filter $\mathrm{atTop}$ on $I$. This filter is proper, since a finite intersection $\{T_0 \supseteq S_1\} \cap \cdots \cap \{T_0 \supseteq S_k\}$ contains $S_1 \cup \cdots \cup S_k$. Let $u$ be an ultrafilter that contains $\mathrm{atTop}$. For $\varphi \in T$, the set $\{T_0 : \varphi \in T_0\}$ contains $\{T_0 : T_0 \supseteq \{\varphi\}\}$, so it is in $u$, and $M_{T_0} \models \varphi$ on this set. By Łoś, $\prod_u M_{T_0} \models \varphi$. The ultraproduct is nonempty, since each factor is. So it is a model of $T$. $\square$

**Corollary (Finite consequence).** $T \models \varphi$ if and only if $T_0 \models \varphi$ for some finite $T_0 \subseteq T$.

*Proof.* By the proposition, $T \models \varphi$ means that $T \cup \{\neg\varphi\}$ is not satisfiable. By compactness, some finite subset $T_0 \cup \{\neg \varphi\}$ is not satisfiable, with $T_0 \subseteq T$ finite. By the proposition again, $T_0 \models \varphi$. The other direction holds because each model of $T$ is a model of $T_0$. $\square$

**Theorem (Large models).** Let $T$ have an infinite model $M$, and let $\kappa$ be a cardinal. Then $T$ has a model of cardinality at least $\kappa$.

*Proof.* Let $A$ be a set of cardinality $\kappa$, and work in $L[[A]]$ with the new constants $c_a$. Let $T' = T \cup \{ c_a \ne c_b : a \ne b \in A \}$. A finite subset of $T'$ names only finitely many constants $c_{a_1}, \dots, c_{a_k}$. Since $M$ is infinite, choose distinct $m_1, \dots, m_k \in M$, interpret $c_{a_j}$ as $m_j$ and the other constants as any element. This is a model of the finite subset. By compactness, $T'$ has a model $N$. The map $a \mapsto c_a^N$ is injective, so $\#N \ge \kappa$, and the reduct of $N$ to $L$ is a model of $T$. $\square$

**Proposition (Completeness and elementary equivalence).** A satisfiable theory $T$ is complete if and only if any two of its models are elementarily equivalent. For each nonempty structure $M$, the theory $\mathrm{Th}(M)$ is maximal, hence complete.

*Proof.* Let $T$ be complete and let $M, N \models T$. For a sentence $\varphi$, either $T \models \varphi$, and both satisfy $\varphi$, or $T \models \neg \varphi$, and neither does. So $M \equiv N$. Conversely, let all models be elementarily equivalent, and let $\varphi$ be a sentence with $T \not\models \varphi$. Then some model $M$ satisfies $\neg\varphi$. Each model $N$ satisfies $\neg \varphi$, since $N \equiv M$. So $T \models \neg\varphi$. For $\mathrm{Th}(M)$: it is satisfied by $M$, and for each sentence $\varphi$, either $M \models \varphi$ or $M \models \neg \varphi$, so $\varphi$ or $\neg\varphi$ is in $\mathrm{Th}(M)$. A maximal theory is complete, because each member of $T$ is a consequence of $T$. $\square$

**Proposition (Equivalence modulo $T$).** The relation $\Leftrightarrow_T$ is an equivalence relation on the bounded formulas at each level, and it is a congruence: if $\varphi \Leftrightarrow_T \psi$ and $\varphi' \Leftrightarrow_T \psi'$, then $\neg\varphi \Leftrightarrow_T \neg\psi$, $(\varphi \Rightarrow \varphi') \Leftrightarrow_T (\psi \Rightarrow \psi')$, and $\forall' \varphi \Leftrightarrow_T \forall' \psi$.

*Proof.* Each claim holds pointwise in each model under each assignment, because truth in a model is a propositional function of the truth of the parts. For the quantifier, the equivalence of $\varphi$ and $\psi$ at each tuple $x \frown a$ gives the equivalence of $\forall' \varphi$ and $\forall' \psi$ at $x$. $\square$

### Examples

**Example (An ultraproduct of finite fields).** Let $I$ be the set of primes and let $u$ be a nonprincipal ultrafilter on $I$. It contains each cofinite set, since it contains no finite set. Let $K = \prod_u \mathbb{F}_p$ in the language of rings. Each field axiom is a sentence true in each $\mathbb{F}_p$, so by Łoś it holds in $K$, and $K$ is a field. For $n \ge 1$, let $\chi_n$ be the sentence $1 + \cdots + 1 \ne 0$ with $n$ summands. It holds in $\mathbb{F}_p$ for all $p > n$, a cofinite set. So $K \models \chi_n$ for all $n$, and $K$ has characteristic $0$. A sentence of the language of rings that holds in $\mathbb{F}_p$ for almost all $p$ holds in $K$, although no $\mathbb{F}_p$ has characteristic $0$. Chapter 4 uses the same method for algebraically closed fields.

**Example (A nonstandard model of arithmetic).** Let $L$ have constants $0, 1$ and binary symbols $+, \cdot$, and let $\bar n$ be the term $1 + \cdots + 1$ with $n$ summands, with $\bar 0 = 0$. Take $T = \mathrm{Th}(\mathbb{N}) \cup \{ c \ne \bar n : n \in \mathbb{N} \}$ in $L[[\{c\}]]$. A finite subset names only $\bar n$ for $n < N$, and $\mathbb{N}$ with $c := N$ is a model of it. By compactness, $T$ has a model $\mathcal{N}$. It is elementarily equivalent to $\mathbb{N}$, but $c^{\mathcal N}$ is not the value of any $\bar n$. In $\mathbb{N}$ each element is the value of some $\bar n$, so $\mathcal{N}$ is not equivalent to $\mathbb{N}$ as a structure.

**Counterexample (Finiteness is not first-order).** No theory $T$ has as its models exactly the nonempty finite structures of all sizes. Suppose $T$ does. Then $T$ has models of each finite size, so $T \cup \{ \mathrm{cardGe}\ n : n \in \mathbb{N} \}$ is finitely satisfiable: a finite part names only $\mathrm{cardGe}\ n$ for $n \le N$, and a model of $T$ of size $N$ satisfies it. By compactness it has a model, which is an infinite model of $T$, a contradiction.

**Example (Skolem functions for a density axiom).** In $(\mathbb{Q}, <)$, take $\varphi(x_0, x_1, y) := x_0 < x_1 \Rightarrow (x_0 < y \wedge y < x_1)$. The Skolem function $f_\varphi$ is binary. On a pair $a < b$ it returns some element strictly between, such as $(a + b)/2$ if $\varepsilon$ makes that choice; on other pairs any element satisfies $\varphi$. The library makes no promise about which element $\varepsilon$ returns, only that it is a witness when one exists.

### The library around it

::: mathlib
`FirstOrder.Language.Theory.IsSatisfiable` · `Mathlib.ModelTheory.Satisfiability`

`T.IsSatisfiable` is `Nonempty (ModelType.{u, v, max u v} T)`. `IsSatisfiable.mono` passes to subsets and `IsSatisfiable.isFinitelySatisfiable` is the trivial direction of compactness. `Model.isSatisfiable` accepts a model in any universe. `isSatisfiable_directed_union_iff` states compactness for a directed union, and `isSatisfiable_union_distinctConstantsTheory_of_infinite` is the step of the proof of large models.

<?decl FirstOrder.Language.Theory.IsSatisfiable?>
:::

::: mathlib
`FirstOrder.Language.Theory.isSatisfiable_iff_isFinitelySatisfiable` · `Mathlib.ModelTheory.Satisfiability`

This is compactness. The proof in the source follows the text: it indexes the models by `Finset T`, takes `Ultrafilter.of Filter.atTop`, and applies `Ultraproduct.sentence_realize`. `models_iff_finset_models` is the corollary on finite consequence, and `exists_large_model_of_infinite_model` is the theorem on large models.

<?decl FirstOrder.Language.Theory.isSatisfiable_iff_isFinitelySatisfiable?>
:::

::: mathlib
`FirstOrder.Language.Theory.ModelsBoundedFormula` · `Mathlib.ModelTheory.Satisfiability`

`T ⊨ᵇ φ` quantifies over all nonempty models in a fixed universe, with `models_sentence_iff` for sentences and `models_iff_not_satisfiable` for the first proposition. `T.IsComplete` and `T.IsMaximal` are as in the text, with `IsComplete.models_not_iff`, `IsComplete.realize_sentence_iff`, `IsMaximal.isComplete` and `completeTheory.isMaximal`. `isComplete_iff_models_elementarily_equivalent` is the proposition on elementary equivalence.

<?decl FirstOrder.Language.Theory.ModelsBoundedFormula?>
:::

::: mathlib
`FirstOrder.Language.Ultraproduct.sentence_realize` · `Mathlib.ModelTheory.Ultraproducts`

The ultraproduct is `(u : Filter α).Product M` for `u : Ultrafilter α`, the germs of sections along `u`. The instance `setoidPrestructure` gives the structure, and `funMap_cast` and `term_realize_cast` compute in it. `boundedFormula_realize_cast` is Łoś's theorem for bounded formulas, under `[∀ a, Nonempty (M a)]`; `realize_formula_cast` and `sentence_realize` are the cases of formulas and sentences. `Product.instNonempty` makes the ultraproduct nonempty.

<?decl FirstOrder.Language.Ultraproduct.sentence_realize?>
:::

::: mathlib
`FirstOrder.Language.skolem₁` · `Mathlib.ModelTheory.Skolem`

`L.skolem₁` has `Functions n = L.BoundedFormula Empty (n + 1)` and no relations. `skolem₁Structure` interprets it by `Classical.epsilon`, and `card_functions_sum_skolem₁_le` bounds the function symbols of `L.sum L.skolem₁` by `max ℵ₀ L.card`. `Substructure.skolem₁_reduct_isElementary` states that a substructure for `L.sum L.skolem₁` is an elementary substructure for `L`; Section 2 proves this with the Tarski-Vaught test. `elementarySkolem₁Reduct` and `exists_small_elementarySubstructure` follow. The same file proves the downward Löwenheim-Skolem theorem `exists_elementarySubstructure_card_eq`, and `Satisfiability` proves the upward forms `exists_elementaryEmbedding_card_eq`, `exists_elementarilyEquivalent_card_eq` and `Theory.exists_model_card_eq`, with the Łoś-Vaught test `Cardinal.Categorical.isComplete` and its instance `Cardinal.empty_infinite_Theory_isComplete`. Section 2 treats all of them.

<?decl FirstOrder.Language.skolem₁?>
:::

::: mathlib
`FirstOrder.Language.Theory.Iff` · `Mathlib.ModelTheory.Equivalence`

`φ ⟹[T] ψ` is `Theory.Imp` and `φ ⇔[T] ψ` is `Theory.Iff`, with `iff_iff_imp_and_imp` and `imp_antisymm`. `Iff.not`, `Iff.imp` and `Iff.all` are the congruence rules, and `iffSetoid T` is the setoid of formulas modulo `T`. The rules of classical logic appear as `BoundedFormula.iff_not_not`, `imp_iff_not_sup` and `all_iff_not_ex_not`, all modulo any theory.

<?decl FirstOrder.Language.Theory.Iff?>
:::

Common errors of a learner: The first error is to look for a proof system; the index of this edition has no declaration for derivations in first-order logic, and `T ⊨ᵇ φ` is semantic consequence. The second error is to forget the universe of `IsSatisfiable`; a model in a large universe must be shrunk, and `Model.isSatisfiable` does this. The third error is to apply Łoś to a filter that is not an ultrafilter; the implication step uses that $A \notin u$ gives $A^c \in u$. The fourth error is to drop `[∀ a, Nonempty (M a)]`, which the universal step needs. The fifth error is to expect `skolem₁` to be a full Skolemization; it adds one layer of Skolem functions for formulas of `L`, not for formulas that use the new symbols.

### Exercises

1. (A) Show that a principal ultrafilter at $j$ gives $\prod_u M_i \cong M_j$. Hint: the map $[x] \mapsto x_j$ is well defined and bijective.
2. (A) Show that $T$ is complete if and only if $T \cup \{\varphi\}$ or $T \cup \{\neg \varphi\}$ is unsatisfiable for each sentence $\varphi$, given that $T$ is satisfiable. Hint: the first proposition.
3. (A) Show that $\varphi \Leftrightarrow_T \psi$ holds for sentences if and only if $\varphi$ and $\psi$ have the same truth value in each model of $T$. Then show that $\Leftrightarrow_\varnothing$ identifies $\forall x\, \varphi$ with $\neg \exists x\, \neg \varphi$. Hint: compare `all_iff_not_ex_not`.
4. (B) Let $T$ be the theory of groups in the language $(\cdot, {}^{-1}, 1)$. Show that there is no set of sentences whose models are exactly the torsion groups. Hint: add a constant $c$ and the sentences $c^n \ne 1$.
5. (B) Show that a sentence that holds in all fields of characteristic $0$ holds in all fields of characteristic $p$ for all large $p$. Hint: the corollary on finite consequence, with the theory of fields and all $\chi_n$.
6. (B) Prove that $\prod_u \mathbb{R}$, for a nonprincipal ultrafilter $u$ on $\mathbb{N}$, is a real closed ordered field with an element larger than each natural number. Hint: the class of $(0, 1, 2, \dots)$; Mathlib has this field as `Hyperreal`.
7. (C) Show that a theory $T$ with only finite models has a finite bound on the size of its models. Hint: otherwise use the counterexample on finiteness.

### Notes and history

Gödel proved the completeness theorem in his dissertation of 1929, published in 1930, and the compactness theorem for countable languages follows from it. Mal'cev extended compactness to arbitrary languages in the 1930s. Łoś proved his theorem on ultraproducts in 1955, and the proof of compactness by ultraproducts became standard after the work of Frayne, Morel and Scott. Skolem introduced the functions named after him in his work of 1920 on the theorem of Löwenheim.

The Mathlib files are by these authors, read from their headers: `Satisfiability`, `Ultraproducts`, `Skolem` and `Equivalence` (all under `Mathlib.ModelTheory`) by Aaron Anderson.

### Reference

<?reference?>
