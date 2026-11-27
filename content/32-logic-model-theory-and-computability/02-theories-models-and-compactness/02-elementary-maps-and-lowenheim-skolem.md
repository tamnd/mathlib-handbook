---
title: Elementary maps and Löwenheim-Skolem
kind: theory
modules:
  - Mathlib.ModelTheory.ElementaryMaps
  - Mathlib.ModelTheory.ElementarySubstructures
  - Mathlib.ModelTheory.DirectLimit
  - Mathlib.ModelTheory.PartialEquiv
  - Mathlib.ModelTheory.Types
  - Mathlib.ModelTheory.Topology.Types
explains:
  E3: [FirstOrder.Language.ElementaryEmbedding, FirstOrder.Language.Embedding.isElementary_of_exists, FirstOrder.Language.Substructure.IsElementary, FirstOrder.Language.ElementarySubstructure, FirstOrder.Language.elementaryDiagram, FirstOrder.Language.ElementaryEmbedding.ofModelsElementaryDiagram, FirstOrder.Language.DirectLimit, FirstOrder.Language.PartialEquiv, FirstOrder.Language.IsExtensionPair, FirstOrder.Language.equiv_between_cg, FirstOrder.Language.Theory.CompleteType, FirstOrder.Language.Theory.typeOf, FirstOrder.Language.Theory.exists_modelType_is_realized_in, CompleteType.isTopologicalBasis_range_typesWith]
  E2: [FirstOrder.Language.ElementaryEmbedding.map_formula, FirstOrder.Language.ElementaryEmbedding.map_boundedFormula, FirstOrder.Language.ElementaryEmbedding.map_sentence, FirstOrder.Language.ElementaryEmbedding.elementarilyEquivalent, FirstOrder.Language.ElementaryEmbedding.injective, FirstOrder.Language.ElementaryEmbedding.toEmbedding, FirstOrder.Language.ElementaryEmbedding.comp, FirstOrder.Language.ElementaryEmbedding.theory_model_iff, FirstOrder.Language.Embedding.toElementaryEmbedding, FirstOrder.Language.Equiv.toElementaryEmbedding, FirstOrder.Language.ElementarySubstructure.subtype, FirstOrder.Language.ElementarySubstructure.realize_sentence, FirstOrder.Language.ElementarySubstructure.elementarilyEquivalent, FirstOrder.Language.Substructure.isElementary_of_exists, FirstOrder.Language.Substructure.toElementarySubstructure, FirstOrder.Language.MeetsDefinable, FirstOrder.Language.MeetsDefinable.isElementary_closure, FirstOrder.Language.DirectLimit.of, FirstOrder.Language.DirectLimit.exists_of, FirstOrder.Language.DirectLimit.lift, FirstOrder.Language.DirectLimit.lift_unique, FirstOrder.Language.DirectLimit.cg, FirstOrder.Language.DirectedSystem.natLERec, FirstOrder.Language.DirectLimit.partialEquivLimit, FirstOrder.Language.PartialEquiv.symm, FirstOrder.Language.PartialEquiv.toEquivOfEqTop, FirstOrder.Language.Embedding.toPartialEquiv, FirstOrder.Language.FGEquiv, FirstOrder.Language.embedding_from_cg, FirstOrder.Language.Theory.typesWith, FirstOrder.Language.Theory.CompleteType.mem_or_not_mem, FirstOrder.Language.Theory.CompleteType.nonempty_iff, FirstOrder.Language.Theory.CompleteType.typesWith_inf, FirstOrder.Language.Theory.CompleteType.typesWith_not, FirstOrder.Language.Theory.CompleteType.mem_typeOf, FirstOrder.Language.Theory.realizedTypes, CompleteType.instTopologicalSpaceCompleteType, CompleteType.isClopen_typesWith, CompleteType.instTotallySeparatedSpaceCompleteType]
  E1: auto
families: []
requires: [V32.C01, V13.C05, V13.C04, V03.C08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Elementary maps and Löwenheim-Skolem

### Overview

An embedding preserves quantifier-free formulas, but it can change the truth of a formula with quantifiers. The inclusion of $(\{1, 2, 3, \dots\}, <)$ into $(\mathbb{N}, <)$ is an embedding, and the element $1$ has a predecessor in $\mathbb{N}$ but not in the smaller structure. An elementary embedding preserves all formulas with parameters. This section studies these maps and the results that build them: the Tarski-Vaught test, the downward and upward Löwenheim-Skolem theorems, and the Łoś-Vaught test for completeness. It then treats two constructions that glue maps together, direct limits and back-and-forth systems, and it ends with complete types, which describe the possible behaviour of a tuple, and their Stone space.

The cardinal arithmetic is that of Mathlib, with universe lifts in the formal statements. The text writes the statements without lifts.

### Definitions

**Definition (Elementary embedding).** A map $g : M \to N$ of $L$-structures is elementary if for each $n$, each formula $\varphi(x_0, \dots, x_{n-1})$ and each tuple $\bar a \in M^n$, $$N \models \varphi(g(\bar a)) \iff M \models \varphi(\bar a).$$ Mathlib writes `M ↪ₑ[L] N`.

An elementary map is injective, since it preserves the formula $x_0 = x_1$ and its negation. It preserves relations and functions, since it preserves the atomic formulas $R(\bar x)$ and $f(\bar x) = x_n$. So it is an embedding.

**Definition (Elementary substructure).** A substructure $S \subseteq M$ is elementary if its inclusion is an elementary embedding. Write $S \preceq M$.

**Definition (Elementary diagram).** The elementary diagram of $M$ is $\mathrm{Th}_{L[[M]]}(M)$, the complete theory of $M$ in the language with one constant for each element, interpreted by itself.

**Definition (Direct limit).** Let $(I, \le)$ be a directed preorder, $(G_i)_{i \in I}$ structures, and $f_{ij} : G_i \hookrightarrow G_j$ embeddings for $i \le j$, with $f_{ii} = \mathrm{id}$ and $f_{jk} \circ f_{ij} = f_{ik}$. The direct limit $\varinjlim G_i$ is the set of pairs $(i, x)$ with $x \in G_i$, modulo $(i, x) \sim (j, y)$ when $f_{ik}(x) = f_{jk}(y)$ for some $k \ge i, j$. A function symbol acts on a tuple of classes by moving all entries to a common $G_k$ and applying it there; a relation is defined in the same way. Each $G_i$ embeds into the limit.

**Definition (Partial equivalence and extension pair).** A partial equivalence $M \rightharpoonup N$ is an equivalence $p : A \to B$ between a substructure $A \subseteq M$ and a substructure $B \subseteq N$. The partial equivalences are ordered by extension. The pair $(M, N)$ is an extension pair if for each partial equivalence $p$ with finitely generated domain and each $m \in M$, there is a partial equivalence $q \ge p$, also with finitely generated domain, with $m$ in its domain.

**Definition (Complete type).** Let $T$ be an $L$-theory and $\alpha$ a type of variables. A complete type of $T$ in the variables $\alpha$ is a maximal $L[[\alpha]]$-theory $p$ that contains $T$. Its elements are the sentences of $L[[\alpha]]$, which are the formulas of $L$ in the free variables $\alpha$, with the variables read as constants. For a model $M$ and a tuple $v : \alpha \to M$, the type of $v$ is the set of formulas $\varphi(\bar x)$ with $M \models \varphi(v)$. For a sentence $\varphi$ of $L[[\alpha]]$, $[\varphi]$ is the set of types that contain $\varphi$. The type space $S_\alpha(T)$ has the topology generated by the sets $[\varphi]$.

### Theorems and proofs

**Theorem (Tarski-Vaught test).** Let $g : M \hookrightarrow N$ be an embedding. Suppose that for each formula $\varphi(\bar x, y)$, each $\bar a$ in $M$ and each $b \in N$ with $N \models \varphi(g(\bar a), b)$, there is $c \in M$ with $N \models \varphi(g(\bar a), g(c))$. Then $g$ is elementary.

*Proof.* Prove by induction on a bounded formula $\varphi$ with no free variables, at level $n$, that $N \models \varphi(g \circ \bar a) \Leftrightarrow M \models \varphi(\bar a)$ for each $\bar a \in M^n$. A formula in the free variables $\mathrm{Fin}\, n$ is first relabeled into such a bounded formula. For $\bot$, equations and relations, the claim holds because $g$ is an embedding: terms commute with $g$, $g$ is injective, and $g$ reflects relations. The case of $\Rightarrow$ follows from the two induction hypotheses. Let $\varphi = \forall y\, \psi(\bar x, y)$. If $N \models \forall y\, \psi(g \bar a, y)$, then for each $c \in M$, $N \models \psi(g \bar a, g c)$, so $M \models \psi(\bar a, c)$ by induction. Conversely, let $M \models \forall y\, \psi(\bar a, y)$, and suppose $N \models \neg \psi(g \bar a, b)$ for some $b \in N$. Apply the hypothesis to the formula $\neg \psi$: some $c \in M$ has $N \models \neg\psi(g \bar a, g c)$. By induction, $M \models \neg\psi(\bar a, c)$, a contradiction. $\square$

**Theorem (Downward Löwenheim-Skolem).** Let $M$ be an $L$-structure, $s \subseteq M$, and $\kappa$ a cardinal with $\aleph_0 \le \kappa$, $\#s \le \kappa$, $\#L \le \kappa$ and $\kappa \le \#M$. Then there is an elementary substructure $S \preceq M$ with $s \subseteq S$ and $\#S = \kappa$.

*Proof.* Since $\#s \le \kappa \le \#M$, choose $s' \subseteq M$ with $s \subseteq s'$ and $\#s' = \kappa$. Since $M$ is infinite, it is nonempty, so it carries the Skolem functions of Section 1. Let $S$ be the closure of $s'$ in the language $L \oplus L^{\mathrm{sk}}$. This language has at most $\max(\aleph_0, \#L) \le \kappa$ function symbols, so by the size of a closure (Chapter 1, Section 2), $\#S \le \max(\aleph_0, \kappa + \kappa) = \kappa$. Also $\#S \ge \#s' = \kappa$. The set $S$ is closed under the functions of $L$, so it is an $L$-substructure. It satisfies the Tarski-Vaught test: if $M \models \varphi(\bar a, b)$ with $\bar a$ in $S$, then $c = f_\varphi(\bar a)$ lies in $S$, and $M \models \varphi(\bar a, c)$ by the choice of $f_\varphi$. $\square$

**Proposition (Elementary diagram).** Let $N$ be an $L[[M]]$-structure that is a model of the elementary diagram of $M$. Then $m \mapsto c_m^N$ is an elementary embedding $M \to N$ of $L$-structures.

*Proof.* Let $\varphi(\bar x)$ be a formula of $L$ and $\bar a \in M^n$. Then $\varphi(c_{\bar a})$ is a sentence of $L[[M]]$. If $M \models \varphi(\bar a)$, this sentence is in the diagram, so $N \models \varphi(c^N_{\bar a})$. If $M \not\models \varphi(\bar a)$, then $\neg\varphi(c_{\bar a})$ is in the diagram, and $N \not\models \varphi(c^N_{\bar a})$. $\square$

**Theorem (Upward Löwenheim-Skolem).** Let $M$ be infinite and let $\kappa \ge \#M$ and $\kappa \ge \#L$. Then there is an elementary embedding $M \hookrightarrow N$ with $\#N = \kappa$.

*Proof.* The elementary diagram $D$ of $M$ has the infinite model $M$. By the theorem on large models (Section 1), $D$ has a model $N_0$ with $\#N_0 \ge \kappa$. The language $L[[M]]$ has cardinality $\#L + \#M \le \kappa$, and $\kappa \ge \#M \ge \aleph_0$. By downward Löwenheim-Skolem in $L[[M]]$, $N_0$ has an elementary substructure $N$ of cardinality $\kappa$. It is a model of $D$, since it is elementarily equivalent to $N_0$. The proposition gives $M \preceq N$. $\square$

Combining the two directions, an infinite structure $M$ is elementarily equivalent to a structure of each cardinality $\kappa \ge \max(\aleph_0, \#L)$.

**Theorem (Łoś-Vaught test).** Let $T$ be satisfiable with no finite models, and let $\kappa \ge \max(\aleph_0, \#L)$. If any two models of $T$ of cardinality $\kappa$ are equivalent, then $T$ is complete.

*Proof.* Let $\varphi$ be a sentence with $T \not\models \varphi$ and $T \not\models \neg\varphi$. Then $T \cup \{\neg\varphi\}$ and $T \cup \{\varphi\}$ have models $M_1, M_2$. They are infinite, so by the remark after upward Löwenheim-Skolem, there are $N_1 \equiv M_1$ and $N_2 \equiv M_2$ of cardinality $\kappa$. These are models of $T$, so $N_1 \cong N_2$. But $N_1 \models \neg\varphi$ and $N_2 \models \varphi$, which contradicts the preservation of sentences by equivalences. $\square$

**Theorem (Back-and-forth).** Let $M$ and $N$ be countably generated. Suppose that $(M, N)$ and $(N, M)$ are extension pairs. Then each partial equivalence $p$ with finitely generated domain extends to an equivalence $M \cong N$.

*Proof.* Let $(m_k)$ and $(n_k)$ enumerate countable generating sets of $M$ and $N$. Define $p_0 = p$. Given $p_{2k}$, use the extension pair $(M, N)$ to extend it to $p_{2k+1}$ with $m_k$ in the domain. Given $p_{2k+1}$, use the extension pair $(N, M)$ on its inverse, and get $p_{2k+2}$ with $n_k$ in the image. All domains stay finitely generated. The union of the chain $p_0 \le p_1 \le \cdots$ is a partial equivalence whose domain is a substructure that contains all $m_k$, so it is $M$. Its image contains all $n_k$, so it is $N$. $\square$

In Mathlib the union of the chain is a direct limit, `DirectLimit.partialEquivLimit`, and the chain comes from `Order.sequenceOfCofinals`.

**Theorem (The type space is a Stone space).** The sets $[\varphi]$ form a basis of clopen sets of $S_\alpha(T)$. The space is totally separated and compact.

*Proof.* A complete type $p$ is maximal, so it contains $\varphi$ or $\neg\varphi$ and not both. Hence $[\neg\varphi]$ is the complement of $[\varphi]$, and each $[\varphi]$ is clopen. Also $[\varphi] \cap [\psi] = [\varphi \sqcap \psi]$ and $[\top]$ is the whole space, so the sets $[\varphi]$ form a basis. If $p \ne q$, some $\varphi$ lies in $p$ and not in $q$, and the clopen set $[\varphi]$ separates them. For compactness, let $F$ be an ultrafilter on $S_\alpha(T)$, and let $p = \{\varphi : [\varphi] \in F\}$. Each sentence of $T$ is in $p$, since its set is the whole space. For a finite subset $\{\varphi_1, \dots, \varphi_k\}$ of $p$, the intersection $[\varphi_1] \cap \cdots \cap [\varphi_k]$ is in $F$, so it is nonempty, and a type in it is a satisfiable theory that contains these sentences. By compactness, $p$ is satisfiable. For each $\varphi$, either $[\varphi] \in F$ or its complement $[\neg\varphi] \in F$, so $p$ is maximal. Each basic neighbourhood $[\varphi]$ of $p$ is in $F$, so $F$ converges to $p$. $\square$

**Proposition (Realization of types).** Each complete type $p$ of $T$ in the variables $\alpha$ is the type of some tuple $v : \alpha \to M$ in some model $M$ of $T$.

*Proof.* The theory $p$ is satisfiable, so it has a model $M'$, an $L[[\alpha]]$-structure. Let $M$ be its reduct to $L$, and $v(a) = c_a^{M'}$. Then $M \models T$, since $T \subseteq p$. For each formula $\varphi$, $\varphi \in p$ implies $M \models \varphi(v)$. Since $p$ is maximal and the type of $v$ is consistent, the two sets are equal. $\square$

### Examples

**Example (The rationals in the reals).** The inclusion $(\mathbb{Q}, <) \subseteq (\mathbb{R}, <)$ is elementary. Apply the Tarski-Vaught test. Let $\bar a$ be rationals $a_1 < \cdots < a_k$ and $b \in \mathbb{R}$ with $\mathbb{R} \models \varphi(\bar a, b)$. If $b = a_i$, then $a_i$ is a rational witness. Otherwise $b$ lies in one of the open intervals $(-\infty, a_1)$, $(a_i, a_{i+1})$ or $(a_k, \infty)$, and there is a rational $q$ in the same interval. A map that is the identity outside this interval and piecewise linear inside, with $b \mapsto q$, is an order automorphism of $\mathbb{R}$ that fixes each $a_i$. Automorphisms preserve formulas, so $\mathbb{R} \models \varphi(\bar a, q)$.

**Counterexample (An embedding that is not elementary).** Let $M = \{1, 2, 3, \dots\}$ and $N = \mathbb{N}$, with $<$. The inclusion is an embedding, and $M \cong N$ by $n \mapsto n - 1$, so $M \equiv N$. The formula $\exists y\, (y < x)$ fails at $1$ in $M$ and holds at $1$ in $N$. So the inclusion is not elementary, although the two structures are elementarily equivalent.

**Example (Back-and-forth for dense orders).** Let $M, N$ be countable dense linear orders without endpoints. Let $p$ be a finite order-preserving bijection $a_1 < \cdots < a_k \mapsto b_1 < \cdots < b_k$, and $m \in M$. If $a_i < m < a_{i+1}$, density in $N$ gives $n$ with $b_i < n < b_{i+1}$. If $m$ is above all $a_i$, the absence of a top in $N$ gives $n > b_k$, and the case below is the same. The extension $p \cup \{m \mapsto n\}$ is again a partial equivalence. In this relational language a finitely generated substructure is finite, so $(M, N)$ and $(N, M)$ are extension pairs, and $M \cong N$. This is Cantor's theorem; Chapter 3 proves it for Mathlib's orders.

**Example (Types over the rationals).** Let $T$ be the elementary diagram of $(\mathbb{Q}, <)$, and consider types in one variable $x$. For each rational $q$, the formula $x = c_q$ gives a type realized in $\mathbb{Q}$. By the first example, $\mathbb{R}$ is a model of $T$, and the type of $\sqrt 2$ contains $c_q < x$ for $q < \sqrt 2$ and $x < c_q$ for $q > \sqrt 2$. No rational realizes it. Compactness also gives the type of an element above all rationals. Each such type is a point of the Stone space $S_1(T)$, and the realized types form a dense subset: a nonempty basic set $[\varphi(x)]$ has a model with a witness, and by elementarity a rational witness.

### The library around it

::: mathlib
`FirstOrder.Language.ElementaryEmbedding` · `Mathlib.ModelTheory.ElementaryMaps`

`M ↪ₑ[L] N` has the fields `toFun` and `map_formula'`, stated for formulas in the variables `Fin n`. `map_boundedFormula`, `map_formula` and `map_sentence` extend it, and `elementarilyEquivalent`, `theory_model_iff`, `injective`, `toEmbedding` and `comp` are the basic facts. `Equiv.toElementaryEmbedding` turns an equivalence into an elementary embedding. `elementaryDiagram L M` and `ElementaryEmbedding.ofModelsElementaryDiagram` are the proposition on diagrams.

<?decl FirstOrder.Language.ElementaryEmbedding?>
:::

::: mathlib
`FirstOrder.Language.Embedding.isElementary_of_exists` · `Mathlib.ModelTheory.ElementaryMaps`

The Tarski-Vaught test, with the hypothesis for `φ : L.BoundedFormula Empty (n + 1)` and the tuple `Fin.snoc (f ∘ x) a`. `Embedding.toElementaryEmbedding` bundles the result. For substructures, `Substructure.isElementary_of_exists` and `Substructure.toElementarySubstructure` are the same test, and `MeetsDefinable.isElementary_closure` says that the closure of a set that meets each nonempty definable set is elementary.

<?decl FirstOrder.Language.Embedding.isElementary_of_exists?>
:::

::: mathlib
`FirstOrder.Language.ElementarySubstructure` · `Mathlib.ModelTheory.ElementarySubstructures`

`L.ElementarySubstructure M` is a substructure with `Substructure.IsElementary`. `ElementarySubstructure.subtype`, `realize_sentence` and `elementarilyEquivalent` are the basic facts.

<?decl FirstOrder.Language.ElementarySubstructure?>
:::

::: mathlib
`FirstOrder.Language.exists_elementarySubstructure_card_eq` · `Mathlib.ModelTheory.Skolem`

Downward Löwenheim-Skolem, with the four cardinal hypotheses of the text, in the file of Skolem functions. Upward Löwenheim-Skolem is `exists_elementaryEmbedding_card_eq_of_ge` in `Satisfiability`, proved through `elementaryDiagram` as above; `exists_elementaryEmbedding_card_eq` combines the two directions. The Łoś-Vaught test is `Cardinal.Categorical.isComplete`, with `Cardinal.Categorical κ T` for $\kappa$-categoricity.

<?decl FirstOrder.Language.exists_elementarySubstructure_card_eq?>
:::

::: mathlib
`FirstOrder.Language.DirectLimit` · `Mathlib.ModelTheory.DirectLimit`

`DirectLimit G f` needs `[DirectedSystem G fun i j h => f i j h]` and `[IsDirectedOrder ι]`. `DirectLimit.of` is the embedding of a component, `exists_of` says each element comes from a component, and `lift` with `lift_unique` is the universal property. `DirectedSystem.natLERec` builds a system from a chain indexed by ℕ, and `DirectLimit.cg` shows that a countable limit of countably generated structures is countably generated. The index of this edition has no declaration for the union of an elementary chain.

<?decl FirstOrder.Language.DirectLimit?>
:::

::: mathlib
`FirstOrder.Language.equiv_between_cg` · `Mathlib.ModelTheory.PartialEquiv`

`M ≃ₚ[L] N` is `PartialEquiv`, with fields `dom`, `cod` and `toEquiv`, a partial order and `PartialEquiv.symm`. `L.FGEquiv M N` is the subtype of partial equivalences with finitely generated domain, and `IsExtensionPair` is the condition of the text. `embedding_from_cg` gives the forth half alone, an embedding of `M` into `N`; `equiv_between_cg` is the back-and-forth theorem. `Embedding.toPartialEquiv` and `PartialEquiv.toEquivOfEqTop` pass between total and partial maps.

<?decl FirstOrder.Language.equiv_between_cg?>
:::

::: mathlib
`FirstOrder.Language.Theory.CompleteType` · `Mathlib.ModelTheory.Types`

`T.CompleteType α` has the fields `toTheory`, `subset'` and `isMaximal'`. `T.typesWith φ` is the set $[\varphi]$, with `typesWith_inf` and `typesWith_not`. `CompleteType.mem_or_not_mem` and `nonempty_iff` (types exist if and only if `T` is satisfiable) are the basic facts. `T.typeOf v` is the type of a tuple, with `mem_typeOf`, `T.realizedTypes M α` is the set of types realized in `M`, and `exists_modelType_is_realized_in` is the proposition on realization.

<?decl FirstOrder.Language.Theory.CompleteType?>
:::

::: mathlib
`CompleteType.isTopologicalBasis_range_typesWith` · `Mathlib.ModelTheory.Topology.Types`

The topology is the instance `CompleteType.instTopologicalSpaceCompleteType`, generated by the range of `typesWith`, in the root namespace `CompleteType`. `isClopen_typesWith` and the instance `instTotallySeparatedSpaceCompleteType` are the first part of the theorem. The source file also proves `CompactSpace` and `BaireSpace` instances, but they are not public, and the index of this edition has no declaration for the compactness of the type space.

<?decl CompleteType.isTopologicalBasis_range_typesWith?>
:::

Common errors of a learner: The first error is to conclude $M \preceq N$ from $M \subseteq N$ and $M \equiv N$; the counterexample shows that this fails. The second error is to state the Tarski-Vaught test for formulas with free variables of $L$; the hypothesis in Mathlib is for bounded formulas over `Empty`, with the parameters as bound variables. The third error is to forget that complete types are theories of $L[[\alpha]]$, so a formula $\varphi(\bar x)$ enters a type as `Formula.equivSentence φ`. The fourth error is to look for the compactness of the type space as a named lemma; it is an instance that is not public in this edition.

### Exercises

1. (A) Show that the composite of two elementary embeddings is elementary, and that $S \preceq M$ implies $S \equiv M$. Hint: `ElementaryEmbedding.comp` and `elementarilyEquivalent`.
2. (A) Show that $(2\mathbb{Z}, +) \subseteq (\mathbb{Z}, +)$ is not elementary, although the two groups are isomorphic. Hint: the formula $\exists y\, (y + y = x)$ at $x = 2$.
3. (A) In the back-and-forth example, write the first three steps for $M = \mathbb{Q}$, $N = \mathbb{Q} \cap (0, 1)$ and the empty partial map, for given enumerations. Hint: the image of the first element can be $1/2$.
4. (B) Use the Łoś-Vaught test to prove that the theory of dense linear orders without endpoints is complete. Hint: $\kappa = \aleph_0$ and Cantor's theorem; the theory has no finite models.
5. (B) Show that the theory of infinite sets in the empty language is complete, and identify its type space in one variable over $\varnothing$. Hint: compare `Cardinal.empty_infinite_Theory_isComplete`; there is one type.
6. (B) Prove that a union of a chain $M_0 \preceq M_1 \preceq \cdots$ of elementary substructures is an elementary extension of each $M_k$. Hint: induction on formulas; a witness for an existential formula lies in some $M_j$.
7. (C) Let $L$ be countable and let $T$ be complete with infinite models. Show that if $S_n(T)$ is finite for each $n$, then each countable model of $T$ realizes all types. Hint: an isolated type contains a formula that generates it, and a finite Hausdorff space is discrete.

### Notes and history

Löwenheim proved in 1915 that a satisfiable first-order sentence has a countable model, and Skolem gave the proof by Skolem functions in 1920. Tarski and Vaught introduced elementary substructures and the test that bears their names in 1957, and the upward theorem for arbitrary cardinals is due to Tarski. Łoś and Vaught found the categoricity test independently in 1954. Cantor proved that countable dense linear orders without endpoints are isomorphic, and Fraïssé (1954) made the back-and-forth method a general tool of model theory. The topology on types follows Stone's duality for Boolean algebras.

The Mathlib files are by these authors, read from their headers: `ElementaryMaps`, `ElementarySubstructures` and `Types` (all under `Mathlib.ModelTheory`) by Aaron Anderson; `DirectLimit` by Aaron Anderson and Gabin Kolly; `PartialEquiv` by Aaron Anderson, Gabin Kolly and David Wärn; `Topology.Types` by Jonas van der Schaaf and Anish Rajeev. The header of `PartialEquiv` states that its proofs are adapted in part from Wärn's approach to countable dense linear orders.

### Reference

<?reference?>
