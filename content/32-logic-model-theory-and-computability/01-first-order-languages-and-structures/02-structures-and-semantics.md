---
title: Structures and semantics
kind: theory
modules:
  - Mathlib.ModelTheory.Semantics
  - Mathlib.ModelTheory.Bundled
  - Mathlib.ModelTheory.Substructures
  - Mathlib.ModelTheory.FinitelyGenerated
  - Mathlib.ModelTheory.Quotients
explains:
  E3: [FirstOrder.Language.Term.realize, FirstOrder.Language.BoundedFormula.Realize, FirstOrder.Language.Sentence.Realize, FirstOrder.Language.Theory.Model, FirstOrder.Language.completeTheory, FirstOrder.Language.ElementarilyEquivalent, FirstOrder.Language.HomClass.realize_term, FirstOrder.Language.StrongHomClass.realize_boundedFormula, FirstOrder.Language.Theory.ModelType, FirstOrder.Language.Substructure, FirstOrder.Language.Substructure.closure, FirstOrder.Language.Substructure.coe_closure_eq_range_term_realize, FirstOrder.Language.Substructure.lift_card_closure_le, FirstOrder.Language.Structure.FG, FirstOrder.Language.Structure.FG.countable_hom, FirstOrder.Language.Prestructure, FirstOrder.Language.Term.realize_quotient_mk']
  E2: [FirstOrder.Language.Formula.Realize, FirstOrder.Language.BoundedFormula.realize_all, FirstOrder.Language.BoundedFormula.realize_ex, FirstOrder.Language.BoundedFormula.realize_imp, FirstOrder.Language.BoundedFormula.realize_not, FirstOrder.Language.BoundedFormula.realize_alls, FirstOrder.Language.elementarilyEquivalent_iff, FirstOrder.Language.Theory.model_iff, FirstOrder.Language.StrongHomClass.realize_sentence, FirstOrder.Language.Sentence.realize_cardGe, FirstOrder.Language.model_infiniteTheory_iff, FirstOrder.Language.model_nonemptyTheory_iff, FirstOrder.Language.Relations.realize_reflexive, FirstOrder.Language.LHom.realize_onSentence, FirstOrder.Language.Theory.ModelType.of, FirstOrder.Language.Theory.Model.bundled, FirstOrder.Language.Theory.ModelType.shrink, FirstOrder.Language.Theory.ModelType.reduct, FirstOrder.Language.Theory.ModelType.subtheoryModel, FirstOrder.Language.equivSetoid, FirstOrder.Language.ClosedUnder, FirstOrder.Language.Substructure.mem_closure_iff_exists_term, FirstOrder.Language.Substructure.closure_le, FirstOrder.Language.Substructure.closure_induction, FirstOrder.Language.Substructure.subtype, FirstOrder.Language.Substructure.map, FirstOrder.Language.Substructure.comap, FirstOrder.Language.Substructure.gc_map_comap, FirstOrder.Language.Substructure.inducedStructure, FirstOrder.Language.Substructure.topEquiv, FirstOrder.Language.Hom.range, FirstOrder.Language.Hom.eqLocus, FirstOrder.Language.Hom.eqOn_closure, FirstOrder.Language.Embedding.equivRange, FirstOrder.Language.Substructure.closure_eq_of_isRelational, FirstOrder.Language.Substructure.FG, FirstOrder.Language.Substructure.CG, FirstOrder.Language.Substructure.fg_def, FirstOrder.Language.Substructure.fg_iff_finite, FirstOrder.Language.Structure.CG, FirstOrder.Language.Structure.cg_iff_countable, FirstOrder.Language.Substructure.countable_fg_substructures_of_countable, FirstOrder.Language.quotientStructure, FirstOrder.Language.funMap_quotient_mk', FirstOrder.Language.relMap_quotient_mk']
  E1: auto
families: []
requires: [V01.C02, V01.C03, V04.C04, V04.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Structures and semantics

### Overview

Section 1 built formulas as syntax. This section gives them meaning. A structure for a language $L$ is a type $M$ with an interpretation of each symbol: a function $M^n \to M$ for each $n$-ary function symbol and a relation on $M^n$ for each $n$-ary relation symbol. A term then has a value in $M$, a formula has a truth value, and a sentence is true or false in $M$. This is Tarski's definition of truth, by recursion on the formula.

The section also sets up the maps and the parts of structures. Homomorphisms preserve the symbols, embeddings also reflect the relations and are injective, and equivalences are bijective embeddings. A substructure is a subset closed under the functions, and the closure of a set is the set of values of terms at its elements. A structure is finitely generated if a finite set generates it. Quotients by an equivalence relation that respects the symbols are structures again. The two main facts are that equivalences preserve all formulas and that the closure of a set $s$ has at most $\max(\aleph_0, \#s + \#L)$ elements.

### Definitions

**Definition (Structure).** An $L$-structure on a type $M$ is a pair of interpretations: for each $f \in F_n$ a function $f^M : (\mathrm{Fin}\, n \to M) \to M$, and for each $R \in R_n$ a predicate $R^M$ on $\mathrm{Fin}\, n \to M$. A constant $c$ has the value $c^M := c^M(\,)$, the function applied to the empty tuple. In Mathlib this is the class `L.Structure M` with the fields `funMap` and `RelMap`.

The empty type is allowed as a structure, provided that the language has no constants. Mathlib does not require structures to be nonempty, but models of a theory in the bundled form are nonempty.

**Definition (Homomorphism, embedding, equivalence).** Let $M, N$ be $L$-structures. A homomorphism $h : M \to N$ is a function with $h(f^M(x)) = f^N(h \circ x)$ for each function symbol and with $R^M(x) \Rightarrow R^N(h \circ x)$ for each relation symbol. An embedding is an injective function with the same condition on functions and with $R^M(x) \Leftrightarrow R^N(h \circ x)$. An equivalence is a bijective embedding. Mathlib writes `M →[L] N`, `M ↪[L] N` and `M ≃[L] N`.

**Definition (Value of a term).** Let $v : \alpha \to M$ be an assignment. The value of a term is defined by recursion: $\mathrm{var}\ a$ has the value $v(a)$, and $\mathrm{func}\ f\ t$ has the value $f^M(i \mapsto t_i^M[v])$.

**Definition (Truth of a bounded formula).** Let $v : \alpha \to M$ and $x : \mathrm{Fin}\, n \to M$. The bound variables take their values from $x$ and the free ones from $v$, so terms are evaluated at the combined assignment $v \oplus x$ on $\alpha \oplus \mathrm{Fin}\, n$. Then $\bot$ is false; `equal t₁ t₂` is true when the two values are equal; `rel R t` is true when $R^M$ holds of the values; $\varphi \Rightarrow \psi$ is true when the truth of $\varphi$ implies the truth of $\psi$; and $\forall' \varphi$ is true when $\varphi$ is true at $v$ and $x \frown a$ for each $a \in M$. Here $x \frown a : \mathrm{Fin}(n + 1) \to M$ appends $a$ at the end, the position of `&n`.

A formula is realized at $v$ alone, with the empty tuple. A sentence $\varphi$ is true in $M$, written $M \models \varphi$, when it is realized at the empty assignment.

**Definition (Model, complete theory, elementary equivalence).** A structure $M$ is a model of a theory $T$, written $M \models T$, if each sentence of $T$ is true in $M$. The complete theory $\mathrm{Th}(M)$ is the set of sentences true in $M$. Two structures are elementarily equivalent, $M \equiv N$, if $\mathrm{Th}(M) = \mathrm{Th}(N)$.

**Definition (Bundled model).** For a theory $T$, the type `T.ModelType` has as elements the triples of a type, an $L$-structure on it that models $T$, and a proof that the type is nonempty.

**Definition (Substructure and closure).** A subset $S \subseteq M$ is closed under $f \in F_n$ if $f^M(x) \in S$ for each $x : \mathrm{Fin}\, n \to S$. A substructure is a subset closed under all function symbols; in particular it contains all constants. A substructure has an induced structure in which relations are restricted. The substructures of $M$ form a complete lattice, with the intersection as infimum. The closure $\langle s \rangle$ of a set $s$ is the least substructure that contains $s$.

**Definition (Finitely and countably generated).** A substructure $S$ is finitely generated if $S = \langle s \rangle$ for a finite set $s$, and countably generated if $S = \langle s \rangle$ for a countable set $s$. The structure $M$ is finitely generated if its top substructure is.

**Definition (Prestructure and quotient).** Let $\sim$ be an equivalence relation on $M$. A prestructure for $\sim$ is an $L$-structure on $M$ such that $x \sim y$ (coordinatewise) implies $f^M(x) \sim f^M(y)$ and $R^M(x) \Leftrightarrow R^M(y)$. Then $M / {\sim}$ has the structure $f([x]) := [f^M(x)]$ and $R([x]) :\Leftrightarrow R^M(x)$.

### Theorems and proofs

**Lemma (Homomorphisms commute with terms).** Let $h : M \to N$ be a homomorphism, $t$ a term and $v$ an assignment in $M$. Then $t^N[h \circ v] = h(t^M[v])$.

*Proof.* Induction on $t$. For a variable $a$, both sides are $h(v(a))$. For $\mathrm{func}\ f\ t$, the induction hypothesis gives $t_i^N[h \circ v] = h(t_i^M[v])$ for each $i$. So the left side is $f^N(i \mapsto h(t_i^M[v]))$, and this equals $h(f^M(i \mapsto t_i^M[v]))$ because $h$ is a homomorphism. $\square$

**Theorem (Equivalences preserve all formulas).** Let $g : M \to N$ be an equivalence. For each bounded formula $\varphi$, assignment $v$ and tuple $x$, $$\varphi \text{ holds in } N \text{ at } g \circ v,\ g \circ x \iff \varphi \text{ holds in } M \text{ at } v,\ x.$$ In particular $M \equiv N$.

*Proof.* Induction on $\varphi$, for all tuples $x$ at once. For $\bot$ both sides are false. For an equation, the values in $N$ are $g$ of the values in $M$ by the lemma, and $g$ is injective, so the equation holds in $N$ if and only if it holds in $M$. For a relation, the lemma and the condition $R^M(y) \Leftrightarrow R^N(g \circ y)$ give the claim. Implication follows from the two induction hypotheses. For $\forall' \varphi$: suppose $\varphi$ holds in $N$ at $g \circ x \frown b$ for all $b \in N$. Given $a \in M$, take $b = g(a)$. Then $g \circ x \frown g(a) = g \circ (x \frown a)$, and the induction hypothesis gives $\varphi$ in $M$ at $x \frown a$. Conversely, suppose $\varphi$ holds in $M$ at $x \frown a$ for all $a$. Given $b \in N$, write $b = g(a)$, which is possible since $g$ is surjective, and apply the induction hypothesis. For a sentence, both assignments are empty, so $M \models \varphi \Leftrightarrow N \models \varphi$. $\square$

**Proposition (Embeddings and complexity).** Let $g : M \to N$ be an embedding. A quantifier-free formula holds in $N$ at $g \circ v, g \circ x$ if and only if it holds in $M$ at $v, x$. A universal formula that holds in $N$ at $g \circ v, g \circ x$ holds in $M$ at $v, x$. An existential formula that holds in $M$ holds in $N$ at the images.

*Proof.* The quantifier-free case is the proof of the theorem without the quantifier step. For a universal formula $\forall' \varphi$, a value $a \in M$ gives the value $g(a) \in N$, and the induction hypothesis transfers $\varphi$ from $N$ to $M$; surjectivity is not used. For an existential formula $\exists' \varphi$, a witness $a \in M$ gives the witness $g(a) \in N$. $\square$

So a substructure of a model of a universal theory is again a model. For example, a substructure of a group in the language $(\cdot, {}^{-1}, 1)$ is a subgroup.

**Theorem (Closure is the set of term values).** For $s \subseteq M$, $$\langle s \rangle = \{\, t^M[\iota] : t \in \text{L.Term}\ s \,\},$$ where $\iota : s \to M$ is the inclusion.

*Proof.* Let $V$ be the right side. The set $V$ contains $s$, since $a = (\mathrm{var}\ a)^M[\iota]$. It is closed under each $f \in F_n$: if $y_i = t_i^M[\iota]$ for each $i$, then $f^M(y) = (\mathrm{func}\ f\ t)^M[\iota]$. So $V$ is a substructure that contains $s$, and $\langle s \rangle \subseteq V$. Conversely, each value $t^M[\iota]$ lies in $\langle s \rangle$, by induction on $t$: variables have values in $s$, and $\langle s \rangle$ is closed under each $f^M$. $\square$

**Corollary (Size of a closure).** $\#\langle s \rangle \le \max(\aleph_0, \#s + \#\Sigma_n F_n)$.

*Proof.* By the theorem, $t \mapsto t^M[\iota]$ maps `L.Term s` onto $\langle s \rangle$. So $\#\langle s \rangle \le \#\text{L.Term}\ s$, and Section 1 bounds the right side by $\max(\aleph_0, \#(s \oplus \Sigma_n F_n))$. $\square$

**Proposition (Homomorphisms on generators).** Two homomorphisms $h, k : M \to N$ that agree on $s$ agree on $\langle s \rangle$. If $M$ is finitely generated and $N$ is countable, then there are only countably many homomorphisms $M \to N$.

*Proof.* The set $\{ x : h(x) = k(x) \}$ is closed under each $f^M$: if $h(x_i) = k(x_i)$ for all $i$, then $h(f^M(x)) = f^N(h \circ x) = f^N(k \circ x) = k(f^M(x))$. So it is a substructure that contains $s$, and it contains $\langle s \rangle$. For the second claim, let $s$ be a finite generating set of $M$. By the first claim, the restriction map from homomorphisms to functions $s \to N$ is injective. There are countably many functions from a finite set into a countable set. $\square$

**Proposition (Terms in a quotient).** For a prestructure on $M$ and an assignment $v : \beta \to M$, the value of a term $t$ in $M / {\sim}$ at $[v]$ is $[t^M[v]]$.

*Proof.* Induction on $t$. A variable gives $[v(a)]$. For $\mathrm{func}\ f\ t$, the induction hypothesis gives $[t_i^M[v]]$ for each argument, and the definition of $f$ on the quotient gives $[f^M(i \mapsto t_i^M[v])]$. $\square$

### Examples

**Example (Truth of a sentence in two orders).** Let $\delta$ be the density sentence $\forall x\, \forall y\, (x < y \Rightarrow \exists z\, (x < z \wedge z < y))$ in the language with one binary symbol $<$. In $(\mathbb{Q}, <)$, for $x < y$ the element $z = (x + y)/2$ is a witness, so $\mathbb{Q} \models \delta$. In $(\mathbb{Z}, <)$, take $x = 0$ and $y = 1$. No integer $z$ has $0 < z < 1$, so $\mathbb{Z} \not\models \delta$. Hence $\delta \in \mathrm{Th}(\mathbb{Q}, <) \setminus \mathrm{Th}(\mathbb{Z}, <)$, and the two orders are not elementarily equivalent. They are also not equivalent as structures, since an equivalence would preserve $\delta$.

**Counterexample (A bijective homomorphism that is not an equivalence).** Take $M = \{0, 1\}$ with $R^M = \varnothing$ and $N = \{0, 1\}$ with $R^N = \{(0, 1)\}$, in the language with one binary relation symbol $R$. The identity $\{0, 1\} \to \{0, 1\}$ is a homomorphism $M \to N$, because the condition $R^M(x) \Rightarrow R^N(x)$ holds vacuously. It is bijective. It is not an embedding, because $R^N(0, 1)$ holds and $R^M(0, 1)$ does not. The sentence $\exists x\, \exists y\, R(x, y)$ is true in $N$ and false in $M$, so no equivalence exists. Homomorphisms preserve existential positive formulas but not negations.

**Example (A closure in the language of rings).** In $\mathbb{Q}$ with the ring language, the closure of $\varnothing$ is $\mathbb{Z}$: the constants $0, 1$ and the operations $+, -, \cdot$ generate exactly the integers, as the values of closed terms such as $1 + 1 + 1$ and $-(1 + 1)$. The closure of $\{1/2\}$ is the ring $\mathbb{Z}[1/2] = \{ a / 2^k : a \in \mathbb{Z},\ k \ge 0 \}$. Each value of a term is a polynomial with integer coefficients at $1/2$, and each $a/2^k$ is the value of the term $a \cdot (1/2)^k$. The closure of $\{1/2\}$ is countable, as the corollary predicts for a finite language. In the language of orders, which is relational, the closure of any set $s$ is $s$ itself.

**Example (A quotient).** Fix $n \ge 1$ and let $x \sim y$ mean $n \mid x - y$ on $\mathbb{Z}$ in the language of rings. The ring operations respect $\sim$, and the language has no relation symbols, so the ring structure is a prestructure. The quotient is $\mathbb{Z}/n\mathbb{Z}$ with its usual operations. By the proposition on terms, the value of $x^2 + 1$ at $[3]$ in $\mathbb{Z}/5\mathbb{Z}$ is $[10] = [0]$. If the language has the order $\le$ as well, then $\sim$ is not a prestructure, because $0 \le 1$ but $5 \not\le 1$ while $0 \sim 5$.

### The library around it

::: mathlib
`FirstOrder.Language.Structure` · `Mathlib.ModelTheory.Basic`

The class `L.Structure M` has the fields `funMap` and `RelMap`. The maps are `L.Hom M N`, `L.Embedding M N` and `L.Equiv M N`, with the notation `M →[L] N`, `M ↪[L] N` and `M ≃[L] N`. The classes `HomClass` and `StrongHomClass` let the same lemma apply to all three. `Embedding.ofInjective` makes each injective homomorphism of an algebraic language into an embedding, because there are no relations to reflect.

<?decl FirstOrder.Language.Structure?>
:::

::: mathlib
`FirstOrder.Language.BoundedFormula.Realize` · `Mathlib.ModelTheory.Semantics`

`φ.Realize v xs` is defined by recursion, and the simp lemmas `realize_imp`, `realize_not`, `realize_all` and `realize_ex` unfold it; the last two use `Fin.snoc xs a`. `Formula.Realize φ v` uses the empty tuple, and `M ⊨ φ` is `Sentence.Realize`. `realize_alls` states that `φ.alls` holds when `φ` holds at each tuple. `Term.realize v t` is the value of a term, and `HomClass.realize_term` is the lemma above. `LHom.realize_onSentence` transfers truth along an expansion.

<?decl FirstOrder.Language.BoundedFormula.Realize?>
:::

::: mathlib
`FirstOrder.Language.StrongHomClass.realize_boundedFormula` · `Mathlib.ModelTheory.Semantics`

This is the theorem that equivalences preserve formulas; it needs `EquivLike` and `StrongHomClass`. `StrongHomClass.realize_sentence` is the case of sentences. `completeTheory L M` is `{φ | M ⊨ φ}`, `M ≅[L] N` is elementary equivalence, and `elementarilyEquivalent_iff` unfolds it. The class `M ⊨ T` is `Theory.Model`, with `Theory.model_iff`. `Sentence.realize_cardGe` reads $M \models \mathrm{cardGe}\ n$ as $n \le \#M$, and `model_infiniteTheory_iff` and `model_nonemptyTheory_iff` follow.

<?decl FirstOrder.Language.StrongHomClass.realize_boundedFormula?>
:::

::: mathlib
`FirstOrder.Language.BoundedFormula.IsUniversal.realize_embedding` · `Mathlib.ModelTheory.Complexity`

The proposition on embeddings lives in `Complexity`: `IsQF.realize_embedding` is the equivalence for quantifier-free formulas, and `IsUniversal.realize_embedding` and `IsExistential.realize_embedding` are the two transfers. `Theory.IsUniversal.models_of_embedding` and the instance `Substructure.models_of_isUniversal` state that a substructure of a model of a universal theory is a model.

<?decl FirstOrder.Language.BoundedFormula.IsUniversal.realize_embedding?>
:::

::: mathlib
`FirstOrder.Language.Theory.ModelType` · `Mathlib.ModelTheory.Bundled`

`T.ModelType` bundles a nonempty model. `ModelType.of T M` and `Model.bundled h` build elements. `ModelType.shrink` moves a model to a smaller universe along `Small`, `ModelType.reduct` takes a reduct along a language map, and `ModelType.subtheoryModel` views a model of `T` as a model of a subtheory. The instance `equivSetoid` relates structures that are equivalent.

<?decl FirstOrder.Language.Theory.ModelType?>
:::

::: mathlib
`FirstOrder.Language.Substructure.closure` · `Mathlib.ModelTheory.Substructures`

`L.Substructure M` has the fields `carrier` and `fun_mem`, the latter in terms of `ClosedUnder`. `closure L` is a lower adjoint to the coercion to sets, with `closure_le` and `closure_induction`. The theorem above is `coe_closure_eq_range_term_realize`, with `mem_closure_iff_exists_term`, and the corollary is `lift_card_closure_le`. `closure_eq_of_isRelational` is the case of a relational language. `Substructure.subtype S : S ↪[L] M` is the inclusion, `map` and `comap` form a Galois connection `gc_map_comap`, and `topEquiv` identifies `⊤` with `M`. For maps, `Hom.range`, `Hom.eqLocus` and `Hom.eqOn_closure` give the first part of the proposition on generators, and `Embedding.equivRange` identifies a structure with the range of an embedding.

<?decl FirstOrder.Language.Substructure.closure?>
:::

::: mathlib
`FirstOrder.Language.Structure.FG` · `Mathlib.ModelTheory.FinitelyGenerated`

`Substructure.FG` is defined with a `Finset` and `fg_def` restates it with `Set.Finite`; `Substructure.CG` uses a countable set. `Structure.FG L M` and `Structure.CG L M` are classes on the top substructure. `Substructure.fg_iff_finite` holds for relational languages, `Structure.cg_iff_countable` holds when there are countably many function symbols, and `Structure.FG.countable_hom` is the second part of the proposition on generators. `Substructure.countable_fg_substructures_of_countable` counts the finitely generated substructures of a countable structure.

<?decl FirstOrder.Language.Structure.FG?>
:::

::: mathlib
`FirstOrder.Language.Prestructure` · `Mathlib.ModelTheory.Quotients`

`L.Prestructure s` is a class with the fields `toStructure`, `fun_equiv` and `rel_equiv`. The instance `quotientStructure` puts the structure on `Quotient s`, and `funMap_quotient_mk'`, `relMap_quotient_mk'` and `Term.realize_quotient_mk'` compute in it.

<?decl FirstOrder.Language.Prestructure?>
:::

Common errors of a learner: The first error is to expect a homomorphism to reflect relations; only embeddings do, and the counterexample above shows a bijective homomorphism that is not an equivalence. The second error is to assume that `M` is nonempty; the class `L.Structure M` allows the empty type, and lemmas such as `realize_toPrenex` need `[Nonempty M]`. The third error is to read `M ⊨ φ` for a formula with free variables; `⊨` applies to sentences and theories, and a formula needs `φ.Realize v`. The fourth error is to state a substructure fact for `S` when the lemma is about the coercion `(S : Set M)`; many closure lemmas, such as `coe_closure_eq_range_term_realize`, are equations of sets.

### Exercises

1. (A) Show that $(\mathbb{Z}, <)$ and $(\mathbb{N}, <)$ are not elementarily equivalent, by a sentence that one satisfies and the other does not. Hint: $\mathbb{N}$ has a least element.
2. (A) In the language of rings, find the closure of $\{\sqrt{2}\}$ in $\mathbb{R}$, and show that it is countable. Hint: it is $\mathbb{Z}[\sqrt{2}]$.
3. (A) Prove that the composite of two embeddings is an embedding, and that the inverse of an equivalence is an equivalence. Hint: compare `Embedding.comp` and `Equiv.symm`.
4. (B) Prove that a homomorphism preserves each formula built from atomic formulas by $\wedge$, $\vee$ and $\exists$. Give a sentence with $\forall$ that a surjective homomorphism does not preserve. Hint: use the counterexample, and the sentence $\forall x\, \forall y\, \neg R(x, y)$.
5. (B) Let $L$ be relational. Show that every subset of $M$ is a substructure, and that $M$ is finitely generated if and only if $M$ is finite. Hint: with no function symbols, the condition `ClosedUnder` is empty.
6. (B) Show that the equivalence relation $x \sim y \iff n \mid x - y$ on $\mathbb{Z}$ is not a prestructure for the language of ordered rings, and find the largest equivalence relation on $\mathbb{Z}$ that is. Hint: $\le$ must be constant on classes.
7. (C) Let $M$ be finitely generated, in a language with countably many function symbols. Show that $M$ is countable, and that a countable structure has only countably many finitely generated substructures. Hint: the corollary on closures, and a finitely generated substructure is the closure of a finite set.

### Notes and history

Tarski gave the definition of truth by recursion on formulas in his work on the concept of truth in formalized languages, first published in Polish in 1933. The model theoretic notion of satisfaction, with structures as the primary objects, became the standard frame of the subject in the 1950s, in the work of Tarski and Robinson. Substructures and closures generalize subgroups and subrings, and the term description of a closure is the general form of the description of a subgroup by words in the generators.

The Mathlib files are by these authors, read from their headers: `Semantics` (under `Mathlib.ModelTheory`) by Aaron Anderson, Jesse Michael Han and Floris van Doorn; `Bundled`, `FinitelyGenerated` and `Quotients` by Aaron Anderson; `Substructures` by Aaron Anderson and Gabin Kolly.

### Reference

<?reference?>
