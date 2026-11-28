---
title: Open sets, closed sets, closure and interior
kind: theory
modules:
  - Mathlib.Topology.Defs.Basic
  - Mathlib.Topology.Basic
  - Mathlib.Topology.Closure
  - Mathlib.Topology.Perfect
explains:
  E3: [TopologicalSpace, IsOpen, IsClosed, closure, interior]
  E2: [isOpen_univ, IsOpen.inter, isOpen_sUnion, isOpen_iUnion, isClosed_compl_iff, isClosed_sInter, IsClosed.union, closure_compl, interior_compl, subset_closure, interior_subset, IsClosed.closure_subset_iff, closure_union, Dense, dense_iff_inter_open, frontier, CofiniteTopology, CofiniteTopology.isOpen_iff, CofiniteTopology.isClosed_iff, TopologicalSpace.le_def]
  E1: auto
families: []
requires: [V01, V04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Open sets, closed sets, closure and interior

### Overview

Analysis on $\mathbb{R}$ uses the distance $|x - y|$ to say that a point is near a set, that a sequence converges, or that a function is continuous. Many of these notions do not need the distance itself. They need only to know which sets are open. A topology is this information: a family of subsets, the open sets, that is closed under finite intersections and arbitrary unions. With this small structure, the notions of closure, interior, convergence and continuity make sense on sets that carry no metric at all: spaces of functions with pointwise convergence, the spectrum of a ring, the space of ultrafilters.

This section gives the axioms, the closed sets, the interior and the closure of a set, and the first examples. The main results are the properties of the closed sets (finite unions, arbitrary intersections), the description of the closure as the set of points whose every open neighbourhood meets the set, and the duality $\overline{X \setminus A} = X \setminus A^\circ$. The examples include the discrete, the indiscrete and the cofinite topologies, and the closure of $\mathbb{Q}$ in $\mathbb{R}$.

### Definitions

**Definition (Topological space).** A topology on a set $X$ is a family $\mathcal{T}$ of subsets of $X$ with three properties.

1. $X \in \mathcal{T}$.
2. If $U, V \in \mathcal{T}$, then $U \cap V \in \mathcal{T}$.
3. If $\mathcal{S} \subseteq \mathcal{T}$ is any family, then $\bigcup \mathcal{S} \in \mathcal{T}$.

The elements of $\mathcal{T}$ are the open sets. A topological space is a set with a topology.

The empty family $\mathcal{S} = \emptyset$ has union $\emptyset$, so axiom 3 gives $\emptyset \in \mathcal{T}$. By induction, axiom 2 gives that a finite intersection $U_1 \cap \dots \cap U_n$ of open sets is open. An infinite intersection of open sets need not be open: in $\mathbb{R}$ the sets $(-1/n, 1/n)$ are open and their intersection is $\{0\}$, which is not open.

*Remarks.* Some texts write the axiom "$\emptyset$ is open" separately. It follows from axiom 3, and Mathlib does not list it. The axioms ask for arbitrary unions and only finite intersections. This asymmetry is the core of the notion. The open sets of $\mathbb{R}$ have exactly these properties, and the definition takes them as axioms.

::: mathlib
`TopologicalSpace` · `Mathlib.Topology.Defs.Basic`

A topology on a type `X` is a class with one field, the predicate `IsOpen : Set X → Prop`, and three axioms: `isOpen_univ`, `isOpen_inter` and `isOpen_sUnion`. A type has at most one topology at a time as an instance, so a statement about a space starts with `[TopologicalSpace X]`. A second topology on the same type is written with the notation `IsOpen[t] s`, or with a type synonym. The empty set is open by `isOpen_empty`, which Mathlib proves from `isOpen_sUnion`.

<?decl TopologicalSpace?>
:::

::: mathlib
`IsOpen` · `Mathlib.Topology.Defs.Basic`

The predicate "the set `s` is open" for the topology of the instance. It is a function `Set X → Prop`, so `IsOpen s` is a proposition and a proof of it is an object that a lemma can take.

<?decl IsOpen?>
:::

::: mathlib
`isOpen_univ` · `Mathlib.Topology.Defs.Basic`

The whole space is open. The three axioms appear in user form as `isOpen_univ`, `IsOpen.inter` and `isOpen_sUnion`. The form for an indexed family, `isOpen_iUnion`, is the one that a proof uses most often.

<?decl isOpen_univ?>
:::

::: mathlib
`IsOpen.inter` · `Mathlib.Topology.Defs.Basic`

The intersection of two open sets is open. The name is in the namespace `IsOpen`, so a proof `hU : IsOpen U` gives `hU.inter hV : IsOpen (U ∩ V)` by dot notation.

<?decl IsOpen.inter?>
:::

::: mathlib
`isOpen_sUnion` · `Mathlib.Topology.Defs.Basic`

The union `⋃₀ S` of a set of open sets is open. For a family `U : ι → Set X` use `isOpen_iUnion`.

<?decl isOpen_sUnion?>
:::

::: mathlib
`isOpen_iUnion` · `Mathlib.Topology.Basic`

The union `⋃ i, U i` of an indexed family of open sets is open. The index type `ι` is any type, of any size.

<?decl isOpen_iUnion?>
:::

**Definition (Closed set).** A subset $F$ of a topological space $X$ is closed if its complement $X \setminus F$ is open.

*Remarks.* "Closed" is not the opposite of "open". In $\mathbb{R}$ the set $[0, 1)$ is neither open nor closed, and $\mathbb{R}$ and $\emptyset$ are both open and closed. A set that is open and closed is called clopen. A space whose only clopen sets are $\emptyset$ and $X$ is connected, the subject of Chapter 6.

::: mathlib
`IsClosed` · `Mathlib.Topology.Defs.Basic`

`IsClosed s` is a structure with one field, `isOpen_compl : IsOpen sᶜ`. It is a structure, and not the bare definition `IsOpen sᶜ`, so that the unfolding is a deliberate step: a proof uses `isOpen_compl_iff` or `isClosed_compl_iff` to pass from one to the other. Mathlib marks it a class so that the instance search can find closedness of some sets, such as a singleton in a $T_1$ space (Chapter 4).

<?decl IsClosed?>
:::

::: mathlib
`isClosed_compl_iff` · `Mathlib.Topology.Basic`

The complement of `s` is closed if and only if `s` is open. The dual lemma `isOpen_compl_iff` says that `sᶜ` is open if and only if `s` is closed.

<?decl isClosed_compl_iff?>
:::

**Definition (Interior, closure, frontier).** Let $A$ be a subset of a topological space $X$.

- The interior $A^\circ$ is the union of all open sets contained in $A$.
- The closure $\overline{A}$ is the intersection of all closed sets that contain $A$.
- The frontier, or boundary, is $\partial A = \overline{A} \setminus A^\circ$.

A set $D$ is dense if $\overline{D} = X$.

*Remarks.* The interior is open, by axiom 3, and it is contained in $A$. So it is the largest open subset of $A$. The closure is closed, by the next theorem, and it contains $A$. So it is the smallest closed superset of $A$. These "largest" and "smallest" descriptions are the useful ones. A proof that $\overline{A} \subseteq F$ for a closed set $F$ only needs $A \subseteq F$.

::: mathlib
`interior` · `Mathlib.Topology.Defs.Basic`

The definition is `⋃₀ {t | IsOpen t ∧ t ⊆ s}`, the union of the open subsets. The basic lemmas are `isOpen_interior`, `interior_subset : interior s ⊆ s` and `interior_maximal`.

<?decl interior?>
:::

::: mathlib
`closure` · `Mathlib.Topology.Defs.Basic`

The definition is `⋂₀ {t | IsClosed t ∧ s ⊆ t}`. The lemmas `isClosed_closure`, `subset_closure` and `closure_minimal` give the three properties of the smallest closed superset.

<?decl closure?>
:::

::: mathlib
`subset_closure` · `Mathlib.Topology.Closure`

Each set is contained in its closure.

<?decl subset_closure?>
:::

::: mathlib
`interior_subset` · `Mathlib.Topology.Closure`

The interior of a set is contained in the set.

<?decl interior_subset?>
:::

::: mathlib
`frontier` · `Mathlib.Topology.Defs.Basic`

The frontier is defined as `closure s \ interior s`, as in the text.

<?decl frontier?>
:::

::: mathlib
`Dense` · `Mathlib.Topology.Defs.Basic`

`Dense s` is defined as `∀ x, x ∈ closure s`. The equivalent form `closure s = univ` is `dense_iff_closure_eq`. For a function, `DenseRange f` says that its range is dense.

<?decl Dense?>
:::

**Definition (Discrete, indiscrete and cofinite topologies).** Let $X$ be a set.

- The discrete topology has every subset open.
- The indiscrete topology has only $\emptyset$ and $X$ open.
- The cofinite topology has as open sets $\emptyset$ and the sets $U$ whose complement $X \setminus U$ is finite.

The cofinite topology is a topology. The set $X$ is open, since its complement is empty. If $U$ and $V$ are open and nonempty, then $X \setminus (U \cap V) = (X \setminus U) \cup (X \setminus V)$ is finite, so $U \cap V$ is open; if one of them is empty, the intersection is empty. For a union, if all the sets are empty the union is empty; otherwise some $U_i$ is nonempty and $X \setminus \bigcup U_j \subseteq X \setminus U_i$ is finite.

::: mathlib
`CofiniteTopology` · `Mathlib.Topology.Constructions`

`CofiniteTopology X` is a type synonym for `X` with the cofinite topology as its instance. A synonym is the standard way in Mathlib to put a second topology on a type: the type `X` keeps its own instance, and `CofiniteTopology X` has the new one. The maps `CofiniteTopology.of` and its inverse pass between the two types.

<?decl CofiniteTopology?>
:::

::: mathlib
`CofiniteTopology.isOpen_iff` · `Mathlib.Topology.Constructions`

A set is open in the cofinite topology if and only if it is empty or its complement is finite. Mathlib writes "empty or" as the implication `s.Nonempty → sᶜ.Finite`.

<?decl CofiniteTopology.isOpen_iff?>
:::

::: mathlib
`CofiniteTopology.isClosed_iff` · `Mathlib.Topology.Constructions`

The closed sets of the cofinite topology are the whole space and the finite sets.

<?decl CofiniteTopology.isClosed_iff?>
:::

**Definition (Finer and coarser).** Let $\mathcal{T}_1$ and $\mathcal{T}_2$ be topologies on $X$. The topology $\mathcal{T}_1$ is finer than $\mathcal{T}_2$, and $\mathcal{T}_2$ is coarser than $\mathcal{T}_1$, if $\mathcal{T}_2 \subseteq \mathcal{T}_1$: each $\mathcal{T}_2$-open set is $\mathcal{T}_1$-open.

The discrete topology is the finest topology and the indiscrete topology is the coarsest. On an infinite set the cofinite topology is strictly between them.

::: mathlib
`TopologicalSpace.le_def` · `Mathlib.Topology.Order`

The topologies on a type form a complete lattice, and Mathlib orders them so that `t ≤ s` means that `t` is finer than `s`: each `s`-open set is `t`-open. So `⊥` is the discrete topology and `⊤` is the indiscrete topology. This is the reverse of the inclusion of the families of open sets. The reason is the analogy with filters (Chapter 2): the neighbourhood filters of a finer topology are smaller, and `t ≤ s` holds if and only if `𝓝[t] x ≤ 𝓝[s] x` for each `x`. A learner who reads `≤` as "has fewer open sets" gets every lemma of `Mathlib.Topology.Order` backwards.

<?decl TopologicalSpace.le_def?>
:::

### Theorems and proofs

**Theorem (Properties of closed sets).** In a topological space $X$:

1. $\emptyset$ and $X$ are closed;
2. a finite union of closed sets is closed;
3. an arbitrary intersection of closed sets is closed.

*Proof.* The complement of $\emptyset$ is $X$ and the complement of $X$ is $\emptyset$, and both are open. This gives 1. For 2, let $F$ and $G$ be closed. By De Morgan, $X \setminus (F \cup G) = (X \setminus F) \cap (X \setminus G)$. This is an intersection of two open sets, so it is open, and $F \cup G$ is closed. Induction on the number of sets gives the finite case. For 3, let $(F_i)_{i \in I}$ be closed sets. By De Morgan, $X \setminus \bigcap_i F_i = \bigcup_i (X \setminus F_i)$, a union of open sets. It is open, so $\bigcap_i F_i$ is closed. $\square$

::: mathlib
`isClosed_sInter` · `Mathlib.Topology.Basic`

An intersection `⋂₀ S` of closed sets is closed. The indexed form is `isClosed_iInter`, and `isClosed_empty` and `isClosed_univ` give part 1.

<?decl isClosed_sInter?>
:::

::: mathlib
`IsClosed.union` · `Mathlib.Topology.Basic`

The union of two closed sets is closed. The finite indexed form is `isClosed_biUnion_finset`, and `Set.Finite.isClosed_biUnion` takes a finite set of indices.

<?decl IsClosed.union?>
:::

**Theorem (The closure is the smallest closed superset).** Let $A \subseteq X$. Then $\overline{A}$ is closed, $A \subseteq \overline{A}$, and $\overline{A} \subseteq F$ for each closed set $F \supseteq A$. In particular $A$ is closed if and only if $A = \overline{A}$.

*Proof.* The closure is an intersection of closed sets, so it is closed by part 3 of the last theorem. Each set in the intersection contains $A$, so $A \subseteq \overline{A}$. If $F$ is closed and contains $A$, then $F$ is one of the sets of the intersection, so $\overline{A} \subseteq F$. For the last claim: if $A$ is closed, take $F = A$ to get $\overline{A} \subseteq A$, so $A = \overline{A}$. If $A = \overline{A}$, then $A$ is closed because $\overline{A}$ is. $\square$

::: mathlib
`IsClosed.closure_subset_iff` · `Mathlib.Topology.Closure`

For a closed set `t`, the inclusion `closure s ⊆ t` holds if and only if `s ⊆ t`. This is the form of minimality that a proof uses: to bound a closure by a closed set, bound the set. The equality `closure s = s` for a closed set is `IsClosed.closure_eq`.

<?decl IsClosed.closure_subset_iff?>
:::

**Theorem (Duality of closure and interior).** For each $A \subseteq X$,
$$X \setminus \overline{A} = (X \setminus A)^\circ \quad\text{and}\quad \overline{X \setminus A} = X \setminus A^\circ.$$

*Proof.* Complementation $S \mapsto X \setminus S$ is a bijection from the closed sets that contain $A$ to the open sets that are contained in $X \setminus A$. It reverses inclusions. So it sends the intersection of the first family to the union of the second family: by De Morgan,
$$X \setminus \bigcap \{F \text{ closed} : A \subseteq F\} = \bigcup \{X \setminus F : F \text{ closed}, A \subseteq F\} = \bigcup \{U \text{ open} : U \subseteq X \setminus A\}.$$
The left side is $X \setminus \overline{A}$ and the right side is $(X \setminus A)^\circ$. This is the first formula. Apply the first formula to $X \setminus A$ in place of $A$: $X \setminus \overline{X \setminus A} = A^\circ$. Take complements to get the second formula. $\square$

::: mathlib
`interior_compl` · `Mathlib.Topology.Closure`

The interior of the complement is the complement of the closure: `interior sᶜ = (closure s)ᶜ`. Mathlib has the four forms `interior_compl`, `closure_compl`, `closure_eq_compl_interior_compl` and `interior_eq_compl_closure_compl`, so a proof can rewrite in either direction.

<?decl interior_compl?>
:::

::: mathlib
`closure_compl` · `Mathlib.Topology.Closure`

The closure of the complement is the complement of the interior.

<?decl closure_compl?>
:::

**Theorem (Points of the closure).** Let $A \subseteq X$ and $x \in X$. Then $x \in \overline{A}$ if and only if each open set $U$ with $x \in U$ meets $A$.

*Proof.* Assume $x \notin \overline{A}$. The set $U = X \setminus \overline{A}$ is open, it contains $x$, and it does not meet $A$ because $A \subseteq \overline{A}$. Conversely, assume that some open $U \ni x$ does not meet $A$. Then $A \subseteq X \setminus U$, and $X \setminus U$ is closed. So $\overline{A} \subseteq X \setminus U$ by minimality, and $x \notin \overline{A}$ because $x \in U$. The two contrapositives give the claim. $\square$

**Corollary (Dense sets).** A set $D$ is dense if and only if it meets each nonempty open set.

*Proof.* If $D$ is dense and $U$ is open and nonempty, pick $x \in U$. Then $x \in \overline{D}$, and $U$ is an open set that contains $x$, so $U$ meets $D$ by the theorem. Conversely, if $D$ meets each nonempty open set, let $x \in X$ and let $U$ be open with $x \in U$. Then $U$ is nonempty, so it meets $D$. By the theorem $x \in \overline{D}$. $\square$

::: mathlib
`dense_iff_inter_open` · `Mathlib.Topology.Closure`

A set is dense if and only if it meets each nonempty open set. The theorem on points of the closure has its Mathlib form in Chapter 2, in the language of neighbourhoods: `mem_closure_iff_nhds`.

<?decl dense_iff_inter_open?>
:::

**Theorem (Closure of a union).** For $A, B \subseteq X$, $\overline{A \cup B} = \overline{A} \cup \overline{B}$. The closure of an intersection satisfies only $\overline{A \cap B} \subseteq \overline{A} \cap \overline{B}$.

*Proof.* The set $\overline{A} \cup \overline{B}$ is closed, as a union of two closed sets, and it contains $A \cup B$. By minimality $\overline{A \cup B} \subseteq \overline{A} \cup \overline{B}$. Conversely, $A \subseteq A \cup B \subseteq \overline{A \cup B}$, and $\overline{A \cup B}$ is closed, so $\overline{A} \subseteq \overline{A \cup B}$ by minimality. In the same way $\overline{B} \subseteq \overline{A \cup B}$. This proves the equality. For the intersection, $A \cap B \subseteq A$ gives $\overline{A \cap B} \subseteq \overline{A}$, and in the same way for $B$. $\square$

The inclusion for intersections can be strict. In $\mathbb{R}$ take $A = \mathbb{Q}$ and $B = \mathbb{R} \setminus \mathbb{Q}$. Then $A \cap B = \emptyset$ has closure $\emptyset$, while $\overline{A} \cap \overline{B} = \mathbb{R}$, by the example below.

::: mathlib
`closure_union` · `Mathlib.Topology.Closure`

The closure of a union of two sets is the union of the closures. For an infinite family only the inclusion `⋃ i, closure (s i) ⊆ closure (⋃ i, s i)` holds, and it follows from `closure_mono`. The equality for a finite family is `closure_iUnion_of_finite`. The dual statement for the interior is `interior_inter`.

<?decl closure_union?>
:::

### Examples

**Example (Closures in $\mathbb{R}$).** Give $\mathbb{R}$ its usual topology: $U$ is open if for each $x \in U$ there is $\varepsilon > 0$ with $(x - \varepsilon, x + \varepsilon) \subseteq U$. Section 2 shows that this is a topology. Let $A = (0, 1]$. The set $[0, 1]$ is closed, because its complement $(-\infty, 0) \cup (1, \infty)$ is open. It contains $A$, so $\overline{A} \subseteq [0, 1]$. The point $0$ is in $\overline{A}$: an open set $U \ni 0$ contains an interval $(-\varepsilon, \varepsilon)$, and this interval contains $\min(\varepsilon/2, 1) \in A$. So $\overline{A} = [0, 1]$. The interior of $A$ is $(0, 1)$: the point $1$ is not interior, since each interval around $1$ contains points greater than $1$. So $\partial A = \{0, 1\}$.

**Example ($\mathbb{Q}$ is dense in $\mathbb{R}$).** Let $U \subseteq \mathbb{R}$ be open and nonempty. It contains an interval $(a, b)$ with $a < b$. Choose a natural number $n > 1/(b - a)$, by the Archimedean property. The multiples $k/n$ for $k \in \mathbb{Z}$ are spaced $1/n < b - a$ apart, so one of them is in $(a, b)$: take $k = \lfloor na \rfloor + 1$, so that $na < k \le na + 1 < nb$. So $U$ meets $\mathbb{Q}$, and $\mathbb{Q}$ is dense by the corollary. The same argument with $k/n + \sqrt{2}/n$ shows that $\mathbb{R} \setminus \mathbb{Q}$ is dense. The interior of $\mathbb{Q}$ is empty, since each interval contains an irrational number. So $\partial \mathbb{Q} = \mathbb{R}$.

**Example (The cofinite topology on $\mathbb{N}$).** Give $\mathbb{N}$ the cofinite topology. Let $A \subseteq \mathbb{N}$ be infinite. The closed sets are $\mathbb{N}$ and the finite sets. The only closed set that contains $A$ is $\mathbb{N}$, so $\overline{A} = \mathbb{N}$ and $A$ is dense. For a finite set $A$, $\overline{A} = A$. Two nonempty open sets $U$ and $V$ always meet: their complements are finite, so $U \cap V$ has finite complement and is infinite. This is the first sign that the cofinite topology is far from a metric topology: in $\mathbb{R}$, the open sets $(0, 1)$ and $(2, 3)$ are disjoint. Chapter 4 makes this precise: the cofinite topology on an infinite set is $T_1$ and not Hausdorff.

**Counterexample (An infinite union of closed sets).** The sets $F_n = [1/n, 1]$ for $n \ge 1$ are closed in $\mathbb{R}$. Their union is $(0, 1]$, which is not closed by the first example. So part 2 of the theorem on closed sets fails for infinite unions. Dually, the open sets $(-1/n, 1/n)$ have the intersection $\{0\}$, which is not open.

**Example (The Sierpiński space).** Let $X = \{0, 1\}$ with the open sets $\emptyset$, $\{1\}$ and $X$. This is a topology: the family is closed under intersections and unions, as a check of the finitely many cases shows. The closed sets are $X$, $\{0\}$ and $\emptyset$. The closure of $\{1\}$ is $X$, so the point $1$ is dense, while the closure of $\{0\}$ is $\{0\}$. A map $f : Y \to X$ is continuous (Section 3) if and only if $f^{-1}(\{1\})$ is open. So the continuous maps to $X$ correspond to the open subsets of $Y$. This makes the Sierpiński space the "classifier" of open sets.

### The library around it

The definitions of this section are in `Mathlib.Topology.Defs.Basic`, a file with few imports. The lemmas are in `Mathlib.Topology.Basic` and `Mathlib.Topology.Closure`. The names follow the pattern `isOpen_*` and `isClosed_*` for a statement that a set is open or closed (`isOpen_iUnion`, `isClosed_iInter`, `isClosed_empty`), and `IsOpen.*` and `IsClosed.*` for a lemma that takes a proof of openness as its first explicit argument (`IsOpen.inter`, `IsOpen.union`, `IsClosed.inter`, `IsClosed.preimage`). The closure and the interior have the monotonicity lemmas `closure_mono` and `interior_mono`, the idempotence lemmas `closure_closure` and `interior_interior`, and the lemmas `closure_empty`, `closure_univ`, `interior_univ`, `interior_empty`. The attribute `simp` is on the idempotence lemmas and on the lemmas for `∅` and `univ`.

A clopen set is `IsClopen s`, defined as `IsClosed s ∧ IsOpen s`; note the order of the two parts. The discrete topology is the class `DiscreteTopology X`, which says that the instance is `⊥`; `isOpen_discrete` then makes every set open.

The module `Mathlib.Topology.Perfect` treats sets with no isolated points. A set $C$ is preperfect if each point of $C$ is an accumulation point of $C$ (`Preperfect`, with the criterion `preperfect_iff_nhds`), and it is perfect if it is also closed (`Perfect`). A space is perfect if the whole space is preperfect (`PerfectSpace`). In a T1 space a set is preperfect if and only if its closure is perfect (`preperfect_iff_perfect_closure`). A nonempty perfect set in a T2.5 space splits into two disjoint nonempty perfect subsets (`Perfect.splitting`), which is the first step of the construction of a Cantor set inside it. In a second countable space each closed set is the union of a countable set and a perfect set (`exists_countable_union_perfect_of_isClosed`), so an uncountable closed set contains a nonempty perfect set (`exists_perfect_nonempty_of_isClosed_of_not_countable`). This is the Cantor-Bendixson theorem.

Common errors of a learner:

- The order of topologies is reversed: `⊥` is the discrete topology. Check the direction of each lemma about `≤` on topologies.
- `IsClosed s` is not by definition `IsOpen sᶜ`, and `rfl` does not prove one from the other. Use `isOpen_compl_iff` and `isClosed_compl_iff`.
- An infinite intersection of open sets is not open in general. A proof that the intersection of a sequence of open sets is open is wrong unless the topology is special (an Alexandrov topology).

The reference table at the end of the section lists the declarations of the three modules.

### Exercises

1. (A) List all topologies on the set $\{a, b\}$. Which of them are homeomorphic as spaces, in the sense of Section 3?
2. (A) Show that in the indiscrete topology on $X$, the closure of each nonempty set is $X$.
3. (A) Show that $\overline{\overline{A}} = \overline{A}$ and $(A^\circ)^\circ = A^\circ$.
4. (A) Show that $(A \cap B)^\circ = A^\circ \cap B^\circ$, and find sets in $\mathbb{R}$ with $(A \cup B)^\circ \ne A^\circ \cup B^\circ$.
5. (B) Show that $\partial A$ is closed, that $\partial A = \overline{A} \cap \overline{X \setminus A}$, and that $A$ is clopen if and only if $\partial A = \emptyset$.
6. (B) Show that the intersection of any family of topologies on $X$ is a topology. Deduce that for any family $\mathcal{S}$ of subsets of $X$ there is a coarsest topology that contains $\mathcal{S}$. Hint: intersect all the topologies that contain $\mathcal{S}$; the discrete topology is one of them.
7. (B) Show that the union of two topologies need not be a topology. Hint: on $\{a, b, c\}$ take the topologies generated by $\{a\}$ and by $\{b\}$.
8. (C) (Kuratowski) Start from a set $A \subseteq \mathbb{R}$ and apply closure and complement in any order. Show that at most $14$ distinct sets arise, and find a set $A$ for which $14$ sets arise. Hint: write $k$ for the closure and $c$ for the complement, and prove the identity $kckckck(A) = kck(A)$.

### Notes and history

Hausdorff gave the first axioms of a topological space in his *Grundzüge der Mengenlehre* (1914), with neighbourhoods as the primitive notion and with the separation axiom $T_2$ built in. Kuratowski (1922) gave the axioms with a closure operator, and the 14-set theorem of Exercise 8 is from his thesis. The axioms with open sets, in the form of this section, became standard with Bourbaki, *Topologie générale* I (1940), and with the text of Kelley (1955).

In Mathlib, the file `Mathlib/Topology/Basic.lean` goes back to the topology files of Lean 2 and Lean 3 by Johannes Hölzl and Mario Carneiro, with later work by Jeremy Avigad and Patrick Massot. The split of the definitions into the light file `Mathlib/Topology/Defs/Basic.lean` is a later refactor, done so that other parts of the library can state topological facts with few imports.

### Reference

<?reference?>
