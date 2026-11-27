---
title: Languages, terms and formulas
kind: theory
modules:
  - Mathlib.ModelTheory.Basic
  - Mathlib.ModelTheory.Syntax
  - Mathlib.ModelTheory.LanguageMap
  - Mathlib.ModelTheory.Complexity
  - Mathlib.ModelTheory.Encoding
explains:
  E3: [FirstOrder.Language, FirstOrder.Language.Term, FirstOrder.Language.BoundedFormula, FirstOrder.Language.Formula, FirstOrder.Language.Sentence, FirstOrder.Language.Theory, FirstOrder.Language.LHom, FirstOrder.Language.withConstants, FirstOrder.Language.BoundedFormula.IsPrenex, FirstOrder.Language.BoundedFormula.toPrenex, FirstOrder.Language.BoundedFormula.toPrenex_isPrenex, FirstOrder.Language.Term.listEncode, FirstOrder.Language.Term.listDecode_encode_list, FirstOrder.Language.Term.card_le, FirstOrder.Language.BoundedFormula.card_le]
  E2: [FirstOrder.Language.Constants, FirstOrder.Language.IsRelational, FirstOrder.Language.IsAlgebraic, FirstOrder.Language.sum, FirstOrder.Language.card, FirstOrder.Language.Symbols, FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst, FirstOrder.Language.Term.varFinset, FirstOrder.Language.Term.bdEqual, FirstOrder.Language.Relations.boundedFormula, FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.subst, FirstOrder.Language.BoundedFormula.castLE, FirstOrder.Language.BoundedFormula.liftAt, FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.ex, FirstOrder.Language.BoundedFormula.alls, FirstOrder.Language.BoundedFormula.toFormula, FirstOrder.Language.Formula.equivSentence, FirstOrder.Language.Relations.reflexive, FirstOrder.Language.Sentence.cardGe, FirstOrder.Language.infiniteTheory, FirstOrder.Language.distinctConstantsTheory, FirstOrder.Language.LHom.onFormula, FirstOrder.Language.LHom.onSentence, FirstOrder.Language.LHom.onTheory, FirstOrder.Language.LHom.reduct, FirstOrder.Language.LHom.IsExpansionOn, FirstOrder.Language.LEquiv, FirstOrder.Language.constantsOn, FirstOrder.Language.lhomWithConstants, FirstOrder.Language.card_withConstants, FirstOrder.Language.BoundedFormula.IsAtomic, FirstOrder.Language.BoundedFormula.IsQF, FirstOrder.Language.BoundedFormula.IsUniversal, FirstOrder.Language.BoundedFormula.IsExistential, FirstOrder.Language.BoundedFormula.toPrenexImp, FirstOrder.Language.BoundedFormula.toPrenexImpRight, FirstOrder.Language.BoundedFormula.realize_toPrenex, FirstOrder.Language.BoundedFormula.iff_toPrenex, FirstOrder.Language.Term.listDecode, FirstOrder.Language.Term.listEncode_injective, FirstOrder.Language.Term.card_sigma, FirstOrder.Language.BoundedFormula.listEncode, FirstOrder.Language.BoundedFormula.instCountableFormula]
  E1: auto
families: []
requires: [V01.C01, V01.C04, V03.C02, V03.C08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Languages, terms and formulas

### Overview

First-order logic speaks about a structure through fixed symbols. The language of orders has one binary relation symbol $\le$. The language of rings has the binary function symbols $+$ and $\cdot$, the unary symbol $-$ and the constants $0$ and $1$. From the symbols and a supply of variables, the syntax builds terms, which name elements, and formulas, which state properties. A sentence is a formula with no free variable, and a theory is a set of sentences. This section builds the syntax as Mathlib does, as inductive data types.

Three choices of the library shape the rest of the volume. A symbol carries its arity in its type. Bound variables are de Bruijn levels, and a formula with $n$ open bound variables lives in `L.BoundedFormula α n`. The primitive formulas are $\bot$, equations, relations, implication and the universal quantifier, and the other connectives are abbreviations. The section ends with two results about the syntax as a set: each formula has an equivalent prenex form, and the formulas of a countable language form a countable set, by an explicit encoding into lists.

### Definitions

**Definition (Language).** A first-order language $L$ is a pair of families $(F_n)_{n \in \mathbb{N}}$ and $(R_n)_{n \in \mathbb{N}}$ of types. An element of $F_n$ is an $n$-ary function symbol, and an element of $R_n$ is an $n$-ary relation symbol. A constant symbol is a $0$-ary function symbol. The cardinality of $L$ is the cardinality of the type $\Sigma_n F_n \oplus \Sigma_n R_n$ of all symbols. The language is relational when it has no function symbols, and algebraic when it has no relation symbols. Equality is a logical symbol, not a relation symbol of $L$.

**Definition (Term).** Let $\alpha$ be a type of variables. The terms of $L$ over $\alpha$ form the least type `L.Term α` with these two constructors: each variable $a \in \alpha$ is a term `var a`, and for each $f \in F_l$ and each family $t : \mathrm{Fin}\, l \to$ `L.Term α`, the expression `func f t` is a term. A constant $c$ gives the term `func c ![]`, with the empty family. So a term is a finite tree whose inner nodes carry function symbols.

**Definition (Bounded formula).** Fix $\alpha$. The bounded formulas form a family of types `L.BoundedFormula α n`, indexed by $n \in \mathbb{N}$, with these constructors.

1. `falsum` is a formula at each level $n$. It is written $\bot$.
2. If $t_1, t_2$ are terms over $\alpha \oplus \mathrm{Fin}\, n$, then `equal t₁ t₂` is a formula at level $n$.
3. If $R \in R_l$ and $t : \mathrm{Fin}\, l \to$ `L.Term (α ⊕ Fin n)`, then `rel R t` is a formula at level $n$.
4. If $\varphi, \psi$ are at level $n$, then `imp φ ψ` is at level $n$. It is written $\varphi \Rightarrow \psi$.
5. If $\varphi$ is at level $n + 1$, then `all φ` is at level $n$. It is written $\forall' \varphi$.

The variables in $\alpha$ are free. The term `&i := var (Sum.inr i)`, for $i < n$, is a bound variable that no quantifier has closed yet. The constructor `all` binds the last variable `&n` of a formula at level $n + 1$. So in $\forall' \forall' \varphi$ at level $0$, the outer quantifier binds `&0` and the inner one binds `&1`. These are de Bruijn levels: the index counts the quantifiers from the outside in.

**Definition (Formula, sentence, theory).** A formula over $\alpha$ is a bounded formula at level $0$, so `L.Formula α` is `L.BoundedFormula α 0`. A sentence is a formula over the empty type, `L.Sentence = L.Formula Empty`. A theory is a set of sentences, `L.Theory = Set L.Sentence`.

**Definition (Derived connectives).** Negation is $\neg \varphi := \varphi \Rightarrow \bot$, written `∼φ`. Truth is $\top := \neg \bot$. Conjunction is $\varphi \sqcap \psi := \neg(\varphi \Rightarrow \neg \psi)$, disjunction is $\varphi \sqcup \psi := \neg\varphi \Rightarrow \psi$, and $\varphi \Leftrightarrow \psi$ is the conjunction of the two implications. The existential quantifier is $\exists' \varphi := \neg \forall' \neg \varphi$.

**Definition (Relabeling and substitution).** For $g : \alpha \to \beta$, the relabeling `t.relabel g` replaces each variable $a$ of a term by $g(a)$. For $\sigma : \alpha \to$ `L.Term β`, the substitution `t.subst σ` replaces each variable $a$ by the term $\sigma(a)$. On bounded formulas, `φ.subst σ` substitutes the free variables and leaves the bound ones alone. The relabeling of a bounded formula takes $g : \alpha \to \beta \oplus \mathrm{Fin}\, n$: it may send a free variable to a new bound variable, and it raises the level from $k$ to $n + k$.

**Definition (Language map).** A language map $\phi : L \to L'$ is a pair of maps $F_n \to F'_n$ and $R_n \to R'_n$ for each $n$; it keeps the arity. Mathlib writes it `L →ᴸ L'`. It acts on terms, formulas and theories by a change of symbols. A structure for $L$ and $L'$ is an expansion along $\phi$ when each symbol $s$ of $L$ and $\phi(s)$ have the same interpretation.

**Definition (Language with constants).** For a type $A$, the language `constantsOn A` has one constant symbol for each element of $A$ and no other symbol. The language $L[[A]]$ is the sum of $L$ and `constantsOn A`. Its cardinality is $\operatorname{lift}\#L + \operatorname{lift}\#A$, and the inclusion $L \to L[[A]]$ is a language map.

**Definition (Complexity classes).** A bounded formula is atomic if it is an equation `equal t₁ t₂` or a relation `rel R t`. It is quantifier-free if it is built from atomic formulas and $\bot$ by implication. It is prenex if it is a quantifier-free formula with a string of quantifiers $\forall'$ and $\exists'$ in front. It is universal if the string contains only $\forall'$, and existential if it contains only $\exists'$.

The formula $\bot$ is not atomic in Mathlib, but it is quantifier-free.

### Theorems and proofs

The prenex form uses the shift `φ.liftAt 1 n`, which moves $\varphi$ from level $n$ to level $n + 1$ and makes room for a new bound variable at position $n$. The new variable does not occur in the shifted formula, so the shift keeps the truth value. The proofs below use the semantics of Section 2 in this informal form.

**Lemma (Prenex form of an implication).** Let $\varphi$ and $\psi$ be prenex at level $n$. There is a prenex formula $\varphi \hookrightarrow \psi$ at level $n$ that has the same truth value as $\varphi \Rightarrow \psi$ in each nonempty structure, under each assignment.

*Proof.* First let $\varphi$ be quantifier-free. Define $\varphi \hookrightarrow_r \psi$ by induction on the prenex formula $\psi$. If $\psi$ is quantifier-free, the result is $\varphi \Rightarrow \psi$. If $\psi = \forall' \psi_1$, the result is $\forall' (\varphi^{\uparrow} \hookrightarrow_r \psi_1)$, where $\varphi^{\uparrow}$ is the shift of $\varphi$ to level $n + 1$. If $\psi = \exists' \psi_1$, the result is $\exists' (\varphi^{\uparrow} \hookrightarrow_r \psi_1)$. The universal case uses $(\varphi \Rightarrow \forall x\, \psi_1) \leftrightarrow \forall x\, (\varphi \Rightarrow \psi_1)$, valid since $x$ does not occur in $\varphi$. The existential case uses $(\varphi \Rightarrow \exists x\, \psi_1) \leftrightarrow \exists x\, (\varphi \Rightarrow \psi_1)$. From left to right: if $\varphi$ is false, any element is a witness, and one exists since the domain is nonempty; if $\varphi$ is true, the left side gives a witness. From right to left, a witness for the right side is a witness for the left side.

Now let $\varphi$ be any prenex formula and define $\varphi \hookrightarrow \psi$ by induction on $\varphi$. If $\varphi$ is quantifier-free, use $\varphi \hookrightarrow_r \psi$. If $\varphi = \exists' \varphi_1$, the result is $\forall' (\varphi_1 \hookrightarrow \psi^{\uparrow})$, by the equivalence $(\exists x\, \varphi_1(x) \Rightarrow \psi) \leftrightarrow \forall x\, (\varphi_1(x) \Rightarrow \psi)$. If $\varphi = \forall' \varphi_1$, the result is $\exists' (\varphi_1 \hookrightarrow \psi^{\uparrow})$, by $(\forall x\, \varphi_1(x) \Rightarrow \psi) \leftrightarrow \exists x\, (\varphi_1(x) \Rightarrow \psi)$. The first equivalence holds in all structures. The second needs a nonempty domain from left to right. If $\psi$ is true, any element is a witness. If $\psi$ is false, then $\forall x\, \varphi_1$ is false, and an $x$ that falsifies $\varphi_1$ is a witness. From right to left, if $\varphi_1(x) \Rightarrow \psi$ and $\forall x\, \varphi_1$, then $\psi$. In each case the result is prenex by induction. $\square$

In Mathlib the two operations are `toPrenexImpRight` and `toPrenexImp`, with exactly these clauses.

**Theorem (Prenex normal form).** Each bounded formula $\varphi$ has a prenex formula $\varphi^{p}$ at the same level such that $\varphi^{p}$ and $\varphi$ have the same truth value in each nonempty structure, under each assignment.

*Proof.* Define $\varphi^{p}$ by induction on $\varphi$. Atomic formulas and $\bot$ are their own prenex forms. For an implication, put $(\varphi \Rightarrow \psi)^{p} := \varphi^{p} \hookrightarrow \psi^{p}$. For a universal formula, put $(\forall' \varphi)^{p} := \forall' (\varphi^{p})$. The result is prenex: the base cases are quantifier-free, the implication case is prenex by the lemma, and $\forall'$ of a prenex formula is prenex. The truth value is preserved by the lemma in the implication case and by the induction hypothesis under the quantifier. $\square$

**Theorem (Unique readability of terms).** Encode a term as a list in Polish notation: a variable $a$ becomes the list $[a]$, and `func f t` with $f \in F_l$ becomes the symbol $f$ followed by the codes of $t_0, \dots, t_{l-1}$. A list of terms can be read back from the concatenation of their codes, so the encoding is injective.

*Proof.* Define a decoder that reads the list from the end and keeps a stack of decoded terms. A variable pushes a one-node term. A function symbol $f$ of arity $l$ pops $l$ terms $t_0, \dots, t_{l-1}$ from the stack and pushes `func f t`. Prove by induction on a term $t$ that decoding the list $\mathrm{code}(t) \mathbin{+\!\!+} w$ gives $t$ on top of the decoding of $w$. For a variable this is the push step. For `func f t`, the list is $f$ followed by $\mathrm{code}(t_0) \cdots \mathrm{code}(t_{l-1})\, w$. By induction, the decoding of the tail is $t_0, \dots, t_{l-1}$ on top of the decoding of $w$. The symbol $f$ pops these $l$ terms and pushes `func f t`. Induction on the list of terms gives the statement, and injectivity follows. $\square$

**Theorem (Number of terms and formulas).** For any language $L$ and type $\alpha$, $$\#(\text{L.Term}\ \alpha) \le \max(\aleph_0, \#(\alpha \oplus \Sigma_l F_l)), \qquad \#\Big(\Sigma_n\, \text{L.BoundedFormula}\ \alpha\ n\Big) \le \max(\aleph_0, \#\alpha + \#L).$$ If $L$ and $\alpha$ are countable, then the type of formulas over $\alpha$ is countable.

*Proof.* The encoding of terms is an injection into the lists over the alphabet $\alpha \oplus \Sigma_l F_l$. The lists over $X$ are the union over $k$ of the sets $X^k$, so they number at most $\max(\aleph_0, \#X)$. A formula is encoded as a list over an alphabet whose letters are terms over $\alpha \oplus \mathrm{Fin}\, k$ for some $k$, relation symbols, and natural numbers that mark $\bot$, implication and the quantifier. By the bound for terms, this alphabet has cardinality at most $\max(\aleph_0, \#\alpha + \#L)$, and the bound on lists applies again. The countable case is the case $\max = \aleph_0$. $\square$

### Examples

**Example (The languages of orders and of rings).** The language of orders has $R_2 = \{\le\}$, all other $R_n$ empty, and all $F_n$ empty. It is relational, and its cardinality is $1$. The language of rings has $F_0 = \{0, 1\}$, $F_1 = \{-\}$, $F_2 = \{+, \cdot\}$ and no relation symbols. It is algebraic, and its cardinality is $5$. In Mathlib these are `FirstOrder.Language.order` and `FirstOrder.Language.ring`. Chapter 3 studies the first and Chapter 4 the second.

**Example (A formula with de Bruijn levels).** In the language of orders, the sentence "$\le$ is transitive" is $\forall x\, \forall y\, \forall z\, (x \le y \Rightarrow (y \le z \Rightarrow x \le z))$. In Mathlib, with $r$ the symbol $\le$, it is `∀' ∀' ∀' (r.boundedFormula₂ &0 &1 ⟹ r.boundedFormula₂ &1 &2 ⟹ r.boundedFormula₂ &0 &2)`, and the library has it as `Relations.transitive r`. The outer quantifier binds `&0`, the middle one `&1`, and the inner one `&2`. The body is at level $3$ and the sentence at level $0$. The formula `r.boundedFormula₂ &0 &1` alone is at level $2$, and `alls` closes it to the sentence $\forall x\, \forall y\, x \le y$.

**Example (Polish code of a term).** In the language of rings, with variables $x, y$, take the term $x + 1 \cdot y$. Its tree has $+$ at the root, with children $x$ and $\cdot(1, y)$. The code is the list $[+, x, \cdot, 1, y]$ of five symbols. To decode it from the right, push $y$, then push $1$. The symbol $\cdot$ pops $1$ and $y$ and pushes $1 \cdot y$. Next push $x$. The symbol $+$ pops $x$ and $1 \cdot y$ and pushes $x + 1 \cdot y$. The stack ends with this one term, which is the original term.

**Counterexample (Prenex form needs a nonempty domain).** Take the sentence $\sigma = (\forall x\, \bot) \Rightarrow \top$. It is true in every structure, because its conclusion is true. The prenex algorithm turns $\forall x\, \varphi_1 \Rightarrow \psi$ into $\exists x\, (\varphi_1 \Rightarrow \psi)$, so the prenex form of $\sigma$ is $\exists x\, (\bot \Rightarrow \top)$. In a nonempty structure this sentence is true. In the empty structure it is false, because an existential sentence has no witness there. So $\sigma$ and its prenex form differ on the empty structure, and the hypothesis `Nonempty M` in `realize_toPrenex` is necessary.

### The library around it

::: mathlib
`FirstOrder.Language` · `Mathlib.ModelTheory.Basic`

A language is a structure with the two fields `Functions : ℕ → Type u` and `Relations : ℕ → Type v`. `L.Constants` is `L.Functions 0`, `L.Symbols` is the sum of the two sigma types, and `L.card` is its cardinality. `IsRelational L` and `IsAlgebraic L` are classes that state that `Functions n` or `Relations n` is empty for each `n`. `L.sum L'` is the disjoint union of two languages.

<?decl FirstOrder.Language?>
:::

::: mathlib
`FirstOrder.Language.Term` · `Mathlib.ModelTheory.Syntax`

`L.Term α` is the inductive type with the constructors `var` and `func`. Relabeling `Term.relabel`, substitution `Term.subst` and the finite set of variables `Term.varFinset` are defined by recursion on the tree. The notation `&n` needs `open FirstOrder`. `Term.bdEqual t₁ t₂`, written `t₁ =' t₂`, is the atomic formula of an equation.

<?decl FirstOrder.Language.Term?>
:::

::: mathlib
`FirstOrder.Language.BoundedFormula` · `Mathlib.ModelTheory.Syntax`

`L.BoundedFormula α n` has the constructors `falsum`, `equal`, `rel`, `imp` and `all`. The notation is `⊥`, `⟹`, `∀'`, `∃'`, `∼` and `⇔`, with `⊓` and `⊔` from the lattice notation. `Relations.boundedFormula R ts` applies a relation symbol to terms, and `Relations.boundedFormula₂` is the binary case. The level changes with `castLE` and `liftAt`, and `alls` closes all bound variables by universal quantifiers. `toFormula` turns the bound variables into free variables of the type `α ⊕ Fin n`. `Formula.equivSentence` reads the free variables of a formula as new constants of `L[[α]]`. `Sentence.cardGe L n` says that there are $n$ distinct elements, `L.infiniteTheory` collects these sentences, and `distinctConstantsTheory` says that given constants are distinct; Chapter 2 uses them.

<?decl FirstOrder.Language.BoundedFormula?>
:::

::: mathlib
`FirstOrder.Language.LHom` · `Mathlib.ModelTheory.LanguageMap`

`L →ᴸ L'` has the fields `onFunction` and `onRelation`. Its action on syntax is `LHom.onTerm`, `LHom.onBoundedFormula`, `LHom.onFormula`, `LHom.onSentence` and `LHom.onTheory`, all in `Syntax`. `LHom.reduct` turns an `L'`-structure into an `L`-structure, and the class `LHom.IsExpansionOn φ M` states that the two interpretations on `M` agree along `φ`. `L ≃ᴸ L'` is an equivalence of languages. The language `L[[α]]` is `withConstants L α`, with `lhomWithConstants` for the inclusion and `card_withConstants` for its cardinality.

<?decl FirstOrder.Language.LHom?>
:::

::: mathlib
`FirstOrder.Language.BoundedFormula.toPrenex` · `Mathlib.ModelTheory.Complexity`

The predicates `IsAtomic`, `IsQF`, `IsPrenex`, `IsUniversal` and `IsExistential` are inductive. `toPrenex_isPrenex` proves that `φ.toPrenex` is prenex. `realize_toPrenex` proves that it has the same realization, under the section variable `[Nonempty M]`. `iff_toPrenex` states `φ ⇔[∅] φ.toPrenex` with no hypothesis, because the models of a theory are nonempty by definition.

<?decl FirstOrder.Language.BoundedFormula.toPrenex?>
:::

::: mathlib
`FirstOrder.Language.Term.listEncode` · `Mathlib.ModelTheory.Encoding`

`Term.listEncode` and `Term.listDecode` are the Polish code and its decoder, and `Term.listDecode_encode_list` is unique readability. `Term.listEncode_injective`, `Term.card_le` and `Term.card_sigma` follow. For formulas, `BoundedFormula.listEncode` and `BoundedFormula.card_le` give the bound $\max(\aleph_0, \#\alpha + \#L)$, with universe lifts. The instance `BoundedFormula.instCountableFormula` makes `L.Formula α` countable when `α` and the symbols are countable.

<?decl FirstOrder.Language.Term.listEncode?>
:::

Common errors of a learner: The first error is to read `&0` as the innermost bound variable, as in de Bruijn indices; in Mathlib it is the outermost one. The second error is to write the existential quantifier as a constructor in a proof by induction on formulas; the constructors are `falsum`, `equal`, `rel`, `imp` and `all`, and `∃'` unfolds to `∼ ∀' ∼`. The third error is to use `Formula.relabel` when the target level is not $0$; for bounded formulas, the relabeling map has the type `α → β ⊕ Fin n` and the level of the result is `n + k`. The fourth error is to forget `[Nonempty M]` when a prenex form is used in a structure, as the counterexample shows.

### Exercises

1. (A) Write the sentence "there are at least two elements" in Mathlib syntax with `∃'`, `='` and `&i`. Then unfold it into the primitive constructors. Hint: the body is `∼ (&0 =' &1)` at level $2$.
2. (A) Give the Polish code of the term $(x + y) \cdot (-x)$ in the language of rings, and decode it from the right. Hint: the code has six symbols.
3. (A) Compute the prenex form of $\exists x\, R(x) \Rightarrow \forall y\, S(y)$ by the algorithm of the lemma, with the levels of all subformulas. Hint: the first step gives $\forall x\, (R(x) \Rightarrow \forall y\, S(y))$.
4. (B) Show that a relational language with finitely many symbols has countably many formulas over $\mathrm{Fin}\, k$, but uncountably many theories. Hint: a theory is any set of sentences, and the sentences $\mathrm{cardGe}\, n$ are pairwise distinct.
5. (B) Prove that relabeling of terms is functorial: $(t.\mathrm{relabel}\ g).\mathrm{relabel}\ h = t.\mathrm{relabel}\ (h \circ g)$, and that substitution by `var` is the identity. Hint: induction on the term; Mathlib has `Term.relabel_relabel`.
6. (B) Show that every quantifier-free formula is equivalent to a formula built from atomic formulas and $\bot$ by $\neg$ and $\sqcup$ only. Hint: $\varphi \Rightarrow \psi$ is equivalent to $\neg \varphi \sqcup \psi$; compare `IsQF.induction_on_sup_not`.
7. (C) Let $L$ have $\kappa \ge \aleph_0$ symbols. Show that $L$ has exactly $\kappa$ sentences. Hint: the upper bound is `BoundedFormula.card_le`; for the lower bound, each symbol occurs in some sentence, and each sentence contains finitely many symbols.

### Notes and history

Frege gave the first formal language with quantifiers in 1879. The name Polish notation honours Łukasiewicz, who used prefix notation to avoid brackets. De Bruijn introduced nameless variables for the Automath system; Mathlib uses his levels, not his indices. Prenex normal forms go back to the early work on the decision problem, and Skolem used them in his work of 1920.

The Mathlib files are by these authors, read from their headers: `Basic`, `Syntax` and `LanguageMap` (all under `Mathlib.ModelTheory`) by Aaron Anderson, Jesse Michael Han and Floris van Doorn; `Complexity` and `Encoding` by Aaron Anderson. The design follows the Flypitch project of Han and van Doorn, a formal proof of the independence of the continuum hypothesis.

### Reference

<?reference?>
