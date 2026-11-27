---
title: Definable sets, orders and graphs
kind: theory
modules:
  - Mathlib.ModelTheory.Definability
  - Mathlib.ModelTheory.Order
  - Mathlib.ModelTheory.Graph
explains:
  E3: [Set.Definable, Set.Definable₁, Set.Definable₂, FirstOrder.Language.DefinableSet, FirstOrder.Language.DefinableSet.instBooleanAlgebra, Set.Definable.image_comp, Set.definable_iff_finitely_definable, Set.DefinableFun, Set.TermDefinable, FirstOrder.Language.order, FirstOrder.Language.IsOrdered, FirstOrder.Language.OrderedStructure, FirstOrder.Language.linearOrderTheory, FirstOrder.Language.dlo, FirstOrder.Language.aleph0_categorical_dlo, FirstOrder.Language.dlo_isComplete, FirstOrder.Language.graph, FirstOrder.Language.Theory.simpleGraph]
  E2: [Set.Definable.union, Set.Definable.inter, Set.Definable.compl, Set.Definable.mono, Set.empty_definable_iff, Set.Definable.preimage_comp, Set.Definable.image_comp_equiv, Set.Definable.exists_of_finite, Set.Definable.forall_of_finite, Set.Definable.singleton, Set.Definable.diagonal, Set.DefinableMap, Set.DefinableFun.comp, Set.Definable.preimage_map, FirstOrder.Language.Term.definableFun_realize, Set.TermDefinable.definable_tupleGraph, Set.TermDefinable.trans, FirstOrder.Language.Term.le, FirstOrder.Language.Term.lt, FirstOrder.Language.Term.realize_le, FirstOrder.Language.Term.realize_lt, FirstOrder.Language.preorderTheory, FirstOrder.Language.partialOrderTheory, FirstOrder.Language.noTopOrderSentence, FirstOrder.Language.noBotOrderSentence, FirstOrder.Language.denselyOrderedSentence, FirstOrder.Language.orderStructure, FirstOrder.Language.leOfStructure, FirstOrder.Language.linearOrderOfModels, FirstOrder.Language.model_dlo, FirstOrder.Language.realize_denselyOrdered_iff, FirstOrder.Language.HomClass.monotone, FirstOrder.Language.HomClass.strictMono, FirstOrder.Language.dlo_isExtensionPair, FirstOrder.Language.dlo_age, FirstOrder.Language.isFraisseLimit_of_countable_nonempty_dlo, FirstOrder.Language.isFraisse_finite_linear_order, SimpleGraph.structure, FirstOrder.Language.simpleGraphOfStructure, FirstOrder.Language.Theory.simpleGraph_model_iff, FirstOrder.Language.Theory.simpleGraph_isSatisfiable]
  E1: auto
families: []
requires: [V03.C08, V04.C01, V30.C01, V32.C01, V32.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Definable sets, orders and graphs

### Overview

A formula with $n$ free variables cuts out a set of $n$-tuples in each structure: the tuples that satisfy it. These are the definable sets of the structure. A structure is tame when its definable sets are simple. In the ordered field $\mathbb{R}$, each definable subset of $\mathbb{R}$ is a finite union of points and intervals. In the field $\mathbb{C}$, each definable subset of $\mathbb{C}$ is finite or cofinite. In the ring $\mathbb{Z}$, each computably enumerable set of natural numbers is definable.

This section gives the Mathlib definition of definability with parameters, proves that the definable sets form a Boolean algebra closed under projection, and proves that an automorphism that fixes the parameters fixes each definable set. It then sets up the language of orders and the theory $\mathrm{DLO}$ of dense linear orders without endpoints, proves Cantor's theorem that two countable models of $\mathrm{DLO}$ are isomorphic, and deduces that $\mathrm{DLO}$ is complete. The last part treats the language of graphs, whose models are the simple graphs of Volume 30.

### Definitions

Fix a language $L$, an $L$-structure $M$ and a set $A \subseteq M$ of parameters. The language $L[[A]]$ is $L$ with a new constant symbol $c_a$ for each $a \in A$, interpreted in $M$ as $a$ (Chapter 1).

**Definition (Definable set).** Let $\alpha$ be a type. A set $S \subseteq M^{\alpha}$ is $A$-definable if there is a formula $\varphi$ of $L[[A]]$ with free variables in $\alpha$ such that $S = \{v \in M^{\alpha} : M \models \varphi[v]\}$. It is $\emptyset$-definable if this holds with $A = \emptyset$.

A tuple is a function $v \colon \alpha \to M$. Mathlib does not ask $\alpha$ to be finite. For subsets of $M$ and of $M \times M$ it uses the index types $\operatorname{Fin} 1$ and $\operatorname{Fin} 2$: a set $s \subseteq M$ is $A$-definable when $\{v : v_0 \in s\}$ is.

**Definition (The algebra of definable sets).** $\operatorname{Def}_A(M^{\alpha})$ is the type of $A$-definable subsets of $M^{\alpha}$, ordered by inclusion.

**Definition (Definable function).** A function $f \colon M^{\alpha} \to M$ is $A$-definable if its graph $\{(v, y) : f(v) = y\}$ is $A$-definable. A map $F \colon M^{\alpha} \to M^{\beta}$ is $A$-definable if each coordinate $v \mapsto F(v)_i$ is. A function $f$ is term-definable over $A$ if $f(v) = t^M[v]$ for a term $t$ of $L[[A]]$.

**Definition (Language of orders).** The language of orders has one binary relation symbol $\leq$ and no function symbols. An ordered language is a language with a chosen binary relation symbol $\leq$, and a structure for it is ordered if the symbol is interpreted as a given relation $\leq$ of $M$. The formula $t_1 < t_2$ abbreviates $t_1 \leq t_2 \wedge \neg (t_2 \leq t_1)$.

**Definition (Theories of orders).** The theory of preorders consists of reflexivity $\forall x\, x \leq x$ and transitivity. The theory of partial orders adds antisymmetry, and the theory of linear orders adds totality $\forall x \forall y\, (x \leq y \vee y \leq x)$. The theory $\mathrm{DLO}$ adds three sentences: $$\forall x \exists y\, \neg (y \leq x), \qquad \forall x \exists y\, \neg (x \leq y), \qquad \forall x \forall y\, (x < y \to \exists z\, (x < z \wedge z < y)).$$ They say that there is no top element, no bottom element, and that the order is dense.

**Definition (Language of graphs).** The language of graphs has one binary relation symbol $E$ and no function symbols. The theory of simple graphs is $\{\forall x\, \neg E(x, x),\ \forall x \forall y\, (E(x, y) \to E(y, x))\}$.

### Theorems and proofs

**Theorem (Boolean closure).** The $A$-definable subsets of $M^{\alpha}$ contain $\emptyset$ and $M^{\alpha}$ and are closed under finite unions, finite intersections, complements and differences. So $\operatorname{Def}_A(M^{\alpha})$ is a Boolean algebra, and the map to the power set preserves the operations.

*Proof.* The formula $\bot$ defines $\emptyset$ and $\top$ defines $M^{\alpha}$. If $\varphi$ defines $S$ and $\psi$ defines $T$, then $\varphi \vee \psi$ defines $S \cup T$, $\varphi \wedge \psi$ defines $S \cap T$ and $\neg \varphi$ defines the complement of $S$, by the clauses of realization. The difference is $S \cap T^{c}$, and induction gives finite unions and intersections. The axioms of a Boolean algebra hold because they hold in the power set and the operations are its operations. $\square$

**Theorem (Projection).** Let $\beta$ be finite and let $S \subseteq M^{\alpha \sqcup \beta}$ be $A$-definable. Then $\{v \in M^{\alpha} : \exists u \in M^{\beta},\ (v, u) \in S\}$ and $\{v : \forall u,\ (v, u) \in S\}$ are $A$-definable. More generally, for a map $f \colon \alpha \to \beta$ of finite types, the image of a definable $S \subseteq M^{\beta}$ under $g \mapsto g \circ f$ is definable.

*Proof.* Let $\varphi(x, y)$ define $S$, with $y = (y_1, \dots, y_k)$ indexed by $\beta$. The formula $\exists y_1 \cdots \exists y_k\, \varphi$ has free variables in $\alpha$, and $v$ satisfies it if and only if $(v, u) \in S$ for some $u$. The formula $\forall y_1 \cdots \forall y_k\, \varphi$ defines the second set. For the general case, factor $f$ as a bijection onto its range followed by the inclusion of the range. A bijection renames the variables of a formula, and the renamed formula defines the image. Restriction to the range forgets the other coordinates, which is the projection above. $\square$

**Theorem (Finitely many parameters).** A set is $A$-definable if and only if it is $A_0$-definable for a finite $A_0 \subseteq A$. If $A \subseteq B$, each $A$-definable set is $B$-definable.

*Proof.* A formula of $L[[A]]$ is a finite object, so it mentions finitely many constants $c_{a_1}, \dots, c_{a_m}$. It is then a formula of $L[[A_0]]$ with $A_0 = \{a_1, \dots, a_m\}$, and it defines the same set. Conversely, the inclusion $A_0 \subseteq A$ gives a map of languages $L[[A_0]] \to L[[A]]$ that keeps the interpretation of each symbol, and a formula and its image define the same set. The second statement is the same argument. $\square$

**Theorem (Invariance under automorphisms).** Let $\sigma$ be an automorphism of $M$ with $\sigma(a) = a$ for all $a \in A$. If $S \subseteq M^{\alpha}$ is $A$-definable, then $\sigma(S) = S$, with $\sigma$ acting on each coordinate.

*Proof.* Because $\sigma$ fixes each $a \in A$, it is an automorphism of $M$ as an $L[[A]]$-structure. By Chapter 1, an isomorphism preserves realization: $M \models \varphi[v]$ if and only if $M \models \varphi[\sigma \circ v]$. With $\varphi$ a formula for $S$, this gives $v \in S \iff \sigma \circ v \in S$. So $\sigma(S) \subseteq S$, and the same for $\sigma^{-1}$ gives $S \subseteq \sigma(S)$. $\square$

This theorem is the main tool to prove that a set is not definable. The index of this edition has no declaration for it in `Mathlib.ModelTheory.Definability`; its content is `StrongHomClass.realize_formula` in `Mathlib.ModelTheory.Semantics`.

**Theorem (Definable functions).** The realization of a term is an $\emptyset$-definable function. If $\alpha$ is finite, $g \colon M^{\beta} \to M^{\alpha}$ is an $A$-definable map and $f \colon M^{\alpha} \to M$ is $A$-definable, then $f \circ g$ is $A$-definable.

*Proof.* For a term $t$, the formula $t(x) = y$ defines the graph of $v \mapsto t^M[v]$. Next, $f(g(v)) = y$ holds if and only if $\exists z\, (\bigwedge_{i \in \alpha} z_i = g(v)_i \wedge f(z) = y)$. Each conjunct defines the graph of a definable function, so Boolean closure and projection apply. $\square$

**Proposition (Models of the theories of orders).** Let $M$ be a structure for an ordered language, with $a \leq b$ the interpretation of the symbol. Then $M$ is a model of the theory of preorders, partial orders or linear orders if and only if $\leq$ is a preorder, a partial order or a linear order. A linear order is a model of $\mathrm{DLO}$ if and only if it is dense and has no top and no bottom element.

*Proof.* Each sentence is the first-order form of one axiom, and the clauses of realization turn it back into the axiom: for example $M \models \forall x\, x \leq x$ if and only if $a \leq a$ for all $a$. In a linear order, the realization of $t_1 < t_2$ is $t_1 < t_2$, so the density sentence holds if and only if the order is dense. The sentence $\forall x \exists y\, \neg(y \leq x)$ says that each $a$ has a $b$ with $a < b$, which is the absence of a top element, and the bottom case is symmetric. $\square$

**Proposition (Homomorphisms are monotone).** Let $M$ and $N$ be ordered structures with preorders. Each homomorphism $h \colon M \to N$ is monotone. If $N$ is a partial order and $h$ is injective, then $h$ is strictly monotone.

*Proof.* A homomorphism preserves relations, so $a \leq b \Rightarrow h(a) \leq h(b)$. If $a < b$, then $h(a) \leq h(b)$ and $h(a) \neq h(b)$, so $h(a) < h(b)$. $\square$

**Lemma (Models of DLO are infinite).** Each nonempty model of $\mathrm{DLO}$ is infinite.

*Proof.* Choose $a_0 \in M$. As there is no top element, there is $a_1$ with $\neg(a_1 \leq a_0)$, so $a_0 < a_1$ by totality. Induction gives $a_0 < a_1 < a_2 < \cdots$, and a strictly increasing sequence is injective. $\square$

**Theorem (Cantor).** Two countable nonempty dense linear orders $P$ and $Q$ without endpoints are order isomorphic.

*Proof.* A finite partial isomorphism is an order isomorphism $p$ between a finite subset of $P$ and a finite subset of $Q$.

Step 1 (forth). Let $p$ be a finite partial isomorphism and $a \in P$. Then some finite partial isomorphism $p' \supseteq p$ has $a$ in its domain. If $a \in \operatorname{dom} p$, take $p' = p$. Otherwise let $x_1 < \cdots < x_n$ be the domain and $y_i = p(x_i)$, so $y_1 < \cdots < y_n$. If $n = 0$, choose any $b \in Q$. If $a < x_1$, choose $b < y_1$, which exists because $Q$ has no bottom element. If $x_n < a$, choose $b > y_n$, as $Q$ has no top element. Otherwise $x_i < a < x_{i+1}$ for a unique $i$, and density gives $b$ with $y_i < b < y_{i+1}$. In each case $b$ lies in the same position relative to the $y_i$ as $a$ relative to the $x_i$, so $p \cup \{(a, b)\}$ is a finite partial isomorphism.

Step 2 (back). The same argument for $p^{-1}$, with $P$ and $Q$ exchanged, puts a given $b \in Q$ into the range.

Step 3. Enumerate $P = \{a_0, a_1, \dots\}$ and $Q = \{b_0, b_1, \dots\}$, with repetitions allowed. Put $p_0 = \emptyset$, let $p_{2k+1} \supseteq p_{2k}$ have $a_k$ in its domain and let $p_{2k+2} \supseteq p_{2k+1}$ have $b_k$ in its range. The union $f$ of the chain is a function defined on all of $P$ and onto $Q$. It is strictly increasing, because two points of $P$ lie in the domain of a common $p_n$, so it is an isomorphism. $\square$

**Corollary (Completeness of DLO).** The theory $\mathrm{DLO}$ is $\aleph_0$-categorical and complete. In particular $(\mathbb{Q}, \leq)$ and $(\mathbb{R}, \leq)$ satisfy the same sentences.

*Proof.* Cantor's theorem gives $\aleph_0$-categoricity. The theory is satisfiable, since $\mathbb{Q}$ is a model, its models are infinite by the lemma, and the language is countable, so the Łoś-Vaught test of Chapter 2 applies. As $\mathbb{R} \models \mathrm{DLO}$, it satisfies the sentences of $\mathbb{Q}$. $\square$

**Proposition (Simple graphs as structures).** A structure for the language of graphs is a model of the theory of simple graphs if and only if $E$ is irreflexive and symmetric. So simple graphs on $V$ and models of the theory on $V$ correspond bijectively.

*Proof.* The two sentences unfold to irreflexivity and symmetry of $E^M$. A simple graph on $V$ is an irreflexive symmetric relation, and both constructions keep the relation. $\square$

### Examples

**Example (The order of the reals is definable in the field).** In $\mathbb{R}$ as a structure for the language of rings, $\exists y\, (x = y \cdot y)$ defines the set of nonnegative numbers, because a real number is a square if and only if it is nonnegative. So $x \leq z$ is $\emptyset$-definable by $\exists y\, (z = x + y \cdot y)$.

**Example (Definable subsets of the rationals).** In $(\mathbb{Q}, \leq)$, the only $\emptyset$-definable subsets of $\mathbb{Q}$ are $\emptyset$ and $\mathbb{Q}$: the translation $x \mapsto x + (b - a)$ is an automorphism that sends $a$ to $b$, so a definable set that contains one point contains all points. With $A = \{0\}$, the $A$-definable subsets are the $8$ unions of the pieces $(-\infty, 0)$, $\{0\}$ and $(0, \infty)$. For $a, b$ of the same sign, $x \mapsto (b/a) x$ is an automorphism that fixes $0$ and sends $a$ to $b$, so an $A$-definable set contains all of a piece or none of it.

**Example (A definable vertex in a path).** Let $P_3$ be the path with vertices $0, 1, 2$ and edges $\{0, 1\}$ and $\{1, 2\}$. The formula $\exists y \exists z\, (\neg (y = z) \wedge E(x, y) \wedge E(x, z))$ says that $x$ has two neighbours, and it defines $\{1\}$. The set $\{0\}$ is not $\emptyset$-definable, because the automorphism that exchanges $0$ and $2$ moves it.

**Counterexample (A point of the rationals).** The set $\{0\}$ is not $\emptyset$-definable in $(\mathbb{Q}, \leq)$, but it is $\{0\}$-definable by $x = c_0$. So the choice of parameters changes the definable sets.

### The library around it

::: mathlib
`Set.Definable` · `Mathlib.ModelTheory.Definability`

`A.Definable L s` for `A : Set M` and `s : Set (α → M)` says `∃ φ : L[[A]].Formula α, s = Set.ofPred φ.Realize`. The low dimensional versions are `A.Definable₁ L s` for `s : Set M` and `A.Definable₂ L s` for `s : Set (M × M)`. The closure lemmas are `Definable.union`, `Definable.inter`, `Definable.compl` and `Definable.sdiff`. `Definable.mono` enlarges the parameters, `definable_iff_finitely_definable` gives a finite `A0 : Finset M`, and `empty_definable_iff` removes the constants when `A = ∅`. `h.image_comp f` gives the image of `s : Set (β → M)` under `fun g => g ∘ f`, for `f : α → β` with `Finite α` and `Finite β`; the quantifier forms are `Definable.exists_of_finite` and `Definable.forall_of_finite`.

<?decl Set.Definable?>

<?decl Set.Definable.image_comp?>
:::

::: mathlib
`FirstOrder.Language.DefinableSet` · `Mathlib.ModelTheory.Definability`

`L.DefinableSet A α` is the subtype `{ s : Set (α → M) // A.Definable L s }`, with a `SetLike` instance and the instance `DefinableSet.instBooleanAlgebra`. The lemmas `mem_sup`, `mem_inf` and `mem_compl` compute the operations.

<?decl FirstOrder.Language.DefinableSet?>
:::

::: mathlib
`Set.DefinableFun` · `Mathlib.ModelTheory.Definability`

`A.DefinableFun L f` for `f : (α → M) → M` is `A.Definable L f.tupleGraph`, with the graph indexed by `Option α`, and `A.DefinableMap L F` asks it for each coordinate. The lemmas `Term.definableFun_realize`, `DefinableFun.comp` and `Definable.preimage_map` carry the attribute `fun_prop`, so the tactic `fun_prop` proves many definability goals. `A.TermDefinable L f` asks for a term of `L[[A]]`, with `TermDefinable.definable_tupleGraph` and `TermDefinable.trans`.

<?decl Set.DefinableFun?>
:::

::: mathlib
`FirstOrder.Language.order` · `Mathlib.ModelTheory.Order`

`Language.order` has the single relation `orderRel.le`. An ordered language is `[L.IsOrdered]` with the field `leSymb`, and `[L.OrderedStructure M]` says `RelMap leSymb x ↔ x 0 ≤ x 1`. The bounded formulas `t₁.le t₂` and `t₁.lt t₂` have `Term.realize_le` and `Term.realize_lt`. `orderStructure M` makes an ordered type a structure, as a definition and not an instance, and `leOfStructure` and `linearOrderOfModels` go back. `HomClass.monotone` and `HomClass.strictMono` are the proposition on homomorphisms.

<?decl FirstOrder.Language.order?>
:::

::: mathlib
`FirstOrder.Language.dlo` · `Mathlib.ModelTheory.Order`

`L.dlo` is `L.linearOrderTheory ∪ {L.noTopOrderSentence, L.noBotOrderSentence, L.denselyOrderedSentence}`, above `partialOrderTheory` and `preorderTheory`. The instance `model_dlo` gives `M ⊨ L.dlo` for a dense linear order without endpoints, and `realize_denselyOrdered_iff` goes back. The results are `aleph0_categorical_dlo : (ℵ₀).Categorical Language.order.dlo` and `dlo_isComplete`. Mathlib proves them through Fraïssé limits, with `dlo_isExtensionPair`, `dlo_age`, `isFraisse_finite_linear_order` and `isFraisseLimit_of_countable_nonempty_dlo`, which Section 2 explains. The order theoretic form of Cantor's theorem is `Order.iso_of_countable_dense`.

<?decl FirstOrder.Language.dlo?>
:::

::: mathlib
`FirstOrder.Language.Theory.simpleGraph` · `Mathlib.ModelTheory.Graph`

`Language.graph` has the single relation `adj`, and `Theory.simpleGraph` is `{adj.irreflexive, adj.symmetric}`, unfolded by `Theory.simpleGraph_model_iff`. `G.structure` is the structure of `G : SimpleGraph V`, and `simpleGraphOfStructure V` goes back. `Theory.simpleGraph_isSatisfiable` says that the theory has a model.

<?decl FirstOrder.Language.Theory.simpleGraph?>
:::

Common errors of a learner: The first error is to give `Set.Definable` a set of `M` instead of a set of tuples `α → M`; for a subset of `M` the predicate is `Definable₁`. The second error is to forget the parameters: the case without parameters is `(∅ : Set M).Definable L s`. The third error is to expect `Language.order.Structure ℚ` as an instance; use `letI := orderStructure ℚ`. The fourth error is to read the de Bruijn indices the wrong way: in `∀' ∃' ∼((&1).le &0)`, the variable `&0` belongs to the outer quantifier, so the sentence says $\forall x \exists y\, \neg(y \leq x)$.

### Exercises

1. (A) In $(\mathbb{Z}, +)$, with one binary function symbol, write formulas without parameters that define the set of even numbers and the set $\{0\}$. Hint: $\exists y\, (x = y + y)$, and $x + x = x$.
2. (A) Prove that each finite set $F \subseteq A$ and its complement are $A$-definable subsets of $M$. Hint: use $x = c_{a_1} \vee \cdots \vee x = c_{a_k}$ and Boolean closure.
3. (A) In the path $P_4$ with vertices $0, 1, 2, 3$ in a row, find all $\emptyset$-definable sets of vertices. Hint: the automorphism $i \mapsto 3 - i$ shows that each is a union of $\{0, 3\}$ and $\{1, 2\}$; write a formula for $\{1, 2\}$.
4. (B) Let $A \subseteq \mathbb{Q}$ be finite. Prove that each $A$-definable subset of $\mathbb{Q}$ is a finite union of points of $A$ and open intervals with endpoints in $A \cup \{-\infty, +\infty\}$. Hint: two points in the same open interval between consecutive points of $A$ are exchanged by a piecewise linear automorphism that fixes $A$.
5. (B) Prove that the theory of linear orders without endpoints is not complete. Hint: compare $\mathbb{Z}$ and $\mathbb{Q}$ with the density sentence.
6. (B) Show that the graph of addition is not $\emptyset$-definable in $(\mathbb{Q}, \leq)$. Hint: otherwise $\{x : x + x = x\} = \{0\}$ is $\emptyset$-definable by Boolean closure and projection.

### Notes and history

Tarski made precise the notions of truth in a structure and of a definable set, and he used them to study the definable sets of the real numbers. Cantor proved that each countable dense linear order without endpoints is isomorphic to the rationals. The proof in the text, which alternates between the two orders, is the back-and-forth method, and Section 2 turns it into the theory of Fraïssé limits. The completeness of $\mathrm{DLO}$ is the first example of the Łoś-Vaught test.

The Mathlib files are by these authors, read from their headers: `Definability`, `Order` and `Graph` (all under `Mathlib.ModelTheory`) by Aaron Anderson.

### Reference

<?reference?>
