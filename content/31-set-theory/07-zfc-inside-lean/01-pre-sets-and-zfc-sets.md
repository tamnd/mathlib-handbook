---
title: Pre-sets and ZFC sets
kind: theory
modules:
  - Mathlib.SetTheory.ZFC.PSet
  - Mathlib.SetTheory.ZFC.Basic
explains:
  E3: [PSet, PSet.Equiv, ZFSet, ZFSet.ext, ZFSet.Definable]
  E2: [PSet.mem_wf, PSet.Mem.ext, PSet.Equiv.euc, PSet.insert, PSet.powerset, PSet.sUnion, PSet.sep, PSet.ofNat, PSet.omega, PSet.embed, ZFSet.mk, ZFSet.eq, ZFSet.mem_wf, ZFSet.inductionOn, ZFSet.mem_insert_iff, ZFSet.mem_powerset, ZFSet.mem_sep, ZFSet.mem_sUnion, ZFSet.omega, ZFSet.omega_zero, ZFSet.omega_succ, ZFSet.regularity, ZFSet.image, ZFSet.mem_image, ZFSet.range, ZFSet.mem_range, Classical.allZFSetDefinable, ZFSet.pair, ZFSet.pair_injective, ZFSet.prod, ZFSet.IsFunc, ZFSet.funs, ZFSet.small_coe, ZFSet.Hereditarily]
  E1: auto
families: [PSet.mem_*, ZFSet.mem_*, ZFSet.coe_*]
requires: [V01.C01, V01.C02, V01.C03, V04.C01, V31.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Pre-sets and ZFC sets

### Overview

Zermelo-Fraenkel set theory has one kind of object, the set, and one primitive relation, membership. Lean has types and terms, and a term belongs to exactly one type. To study ZFC inside Lean, Mathlib builds a type whose terms behave like the sets of ZFC. The construction has two steps. A *pre-set* is a family of pre-sets indexed by a type: the pre-set $\langle \alpha, A \rangle$ has the members $A(a)$ for $a \in \alpha$. Two pre-sets are *extensionally equivalent* when each member of one is equivalent to some member of the other. A *ZFC set* is a pre-set up to this equivalence.

This section proves that extensional equivalence is an equivalence relation, that membership is well-founded, and that the axioms of ZFC hold in the type `ZFSet`: extensionality, the empty set, pairing, union, power set, separation, replacement, infinity, regularity and choice. The proofs are short, but each one shows how a construction of set theory becomes a construction on index types. Section 2 continues with ordinals, rank and the von Neumann hierarchy.

### Definitions

**Definition (Pre-set).** Fix a universe $u$. The pre-sets of level $u$ form the inductive type with one constructor: for each type $\alpha$ of level $u$ and each function $A : \alpha \to \mathrm{PSet}$, there is a pre-set $\langle \alpha, A \rangle$. The type $\alpha$ is the *index type* and $A$ is the *family of members*.

A pre-set is a well-founded tree whose nodes may branch over any type of level $u$. The empty pre-set is $\langle \emptyset, ! \rangle$, with the empty function. The pre-set $\langle \mathrm{Unit}, \_ \mapsto \emptyset \rangle$ has one member, the empty pre-set. The definition allows repetitions: $\langle \mathrm{Bool}, \_ \mapsto \emptyset \rangle$ lists the empty pre-set twice.

::: mathlib
`PSet` · `Mathlib.SetTheory.ZFC.PSet`

`PSet.{u} : Type (u + 1)` is a structure with the fields `Type : Type u` and `Func : Type → PSet`. Since the index type lives in `Type u`, the type of all pre-sets lives one universe higher. A pre-set is written `⟨α, A⟩` or `PSet.mk α A`, and its members are `x.Func i` for `i : x.Type`.

<?decl PSet?>
:::

**Definition (Extensional equivalence).** By recursion on pre-sets, $\langle \alpha, A \rangle \approx \langle \beta, B \rangle$ holds when for each $a \in \alpha$ there is $b \in \beta$ with $A(a) \approx B(b)$, and for each $b \in \beta$ there is $a \in \alpha$ with $A(a) \approx B(b)$. A pre-set $y$ is a *member* of $x = \langle \alpha, A \rangle$, written $y \in x$, if $y \approx A(a)$ for some $a$. It is a *subset*, $y \subseteq x$, if each member of $y$ is a member of $x$.

The equivalence forgets the index type and the repetitions. So $\langle \mathrm{Bool}, \_ \mapsto \emptyset \rangle \approx \langle \mathrm{Unit}, \_ \mapsto \emptyset \rangle$. Membership is defined up to equivalence on the left, so it is invariant under $\approx$ on both sides once the relation is known to be an equivalence.

::: mathlib
`PSet.Equiv` · `Mathlib.SetTheory.ZFC.PSet`

`PSet.Equiv x y` is defined by structural recursion, with the two conditions of the definition as a conjunction. The lemma `PSet.equiv_iff` unfolds it for arbitrary `x` and `y`. The instance `PSet.setoid` makes it a setoid, and `x ∈ y` is `∃ b, Equiv x (y.Func b)`.

<?decl PSet.Equiv?>
:::

**Definition (ZFC set).** The type of *ZFC sets* is the quotient of the pre-sets by extensional equivalence. For a pre-set $x$, its class is written $[x]$. A set $[x]$ is a member of $[y]$ when $x \in y$.

::: mathlib
`ZFSet` · `Mathlib.SetTheory.ZFC.Basic`

`ZFSet.{u} : Type (u + 1)` is `Quotient PSet.setoid.{u}`. The map `ZFSet.mk : PSet → ZFSet` sends a pre-set to its class, and `ZFSet.eq` says `mk x = mk y ↔ PSet.Equiv x y`. A `ZFSet` is a `SetLike` object with elements in `ZFSet`, so `x ∈ y`, `x ⊆ y` and the coercion `(x : Set ZFSet)` all have their usual meaning.

<?decl ZFSet?>
:::

**Definition (Definable function).** A function $f$ of $n$ arguments on ZFC sets is *definable* if it is the image of a function $g$ of $n$ arguments on pre-sets: $f([x_1], \dots, [x_n]) = [g(x_1, \dots, x_n)]$ for all pre-sets $x_i$.

The word is borrowed from logic, but the meaning here is weaker: no formula is involved. With the axiom of choice each function is definable, since one can take $g(x_1, \dots, x_n)$ to be a chosen representative of $f([x_1], \dots, [x_n])$.

::: mathlib
`ZFSet.Definable` · `Mathlib.SetTheory.ZFC.Basic`

`Definable n f` is a class with a field `out : (Fin n → PSet) → PSet` and the equation `mk_out`. The abbreviations `Definable₁` and `Definable₂` treat one and two arguments. The noncomputable definition `Classical.allZFSetDefinable` builds an instance for every function. The library uses explicit instances where it can, for example for `insert` and `pair`, because they compute.

<?decl ZFSet.Definable?>
:::

### Theorems and proofs

**Theorem (Extensional equivalence is an equivalence relation).** The relation $\approx$ on pre-sets is reflexive, symmetric and transitive.

*Proof.* The proof has three steps. Each step is an induction on the structure of pre-sets: a property holds for all pre-sets if it holds for $\langle \alpha, A \rangle$ whenever it holds for each $A(a)$.

Step 1, reflexivity. Let $x = \langle \alpha, A \rangle$ and assume $A(a) \approx A(a)$ for each $a$. For $a \in \alpha$ choose $b = a$, in both conditions. So $x \approx x$.

Step 2, a Euclidean law: if $x \approx y$ and $z \approx y$, then $x \approx z$. The induction is on $x$, for all $y$ and $z$. Let $x = \langle \alpha, A \rangle$, $y = \langle \beta, B \rangle$ and $z = \langle \gamma, C \rangle$. Let $a \in \alpha$. Since $x \approx y$, there is $b$ with $A(a) \approx B(b)$. Since $z \approx y$, there is $c$ with $C(c) \approx B(b)$. The induction hypothesis for $A(a)$ gives $A(a) \approx C(c)$. For the second condition, let $c \in \gamma$. Since $z \approx y$ there is $b$ with $C(c) \approx B(b)$, and since $x \approx y$ there is $a$ with $A(a) \approx B(b)$. The induction hypothesis gives $A(a) \approx C(c)$. So $x \approx z$.

Step 3. For symmetry, assume $x \approx y$. Step 1 gives $y \approx y$, and Step 2 applied to $y \approx y$ and $x \approx y$ gives $y \approx x$. For transitivity, assume $x \approx y$ and $y \approx z$. Symmetry gives $z \approx y$, and Step 2 gives $x \approx z$. $\square$

**Theorem (Extensionality).** Let $x$ and $y$ be pre-sets with the same members: $w \in x \Leftrightarrow w \in y$ for every pre-set $w$. Then $x \approx y$. Consequently two ZFC sets with the same elements are equal.

*Proof.* Let $x = \langle \alpha, A \rangle$ and $y = \langle \beta, B \rangle$. For $a \in \alpha$, $A(a) \in x$ by reflexivity, so $A(a) \in y$, which means $A(a) \approx B(b)$ for some $b$. For $b \in \beta$, $B(b) \in y$, so $B(b) \in x$, and $B(b) \approx A(a)$ for some $a$. By symmetry $A(a) \approx B(b)$. So $x \approx y$. For ZFC sets, choose representatives $x$ and $y$. Membership in $[x]$ is membership in $x$, so the hypothesis gives $x \approx y$ and hence $[x] = [y]$. $\square$

::: mathlib
`ZFSet.ext` · `Mathlib.SetTheory.ZFC.Basic`

The pre-set form is `PSet.Mem.ext`. On `ZFSet` the theorem is an `ext` lemma, so the tactic `ext z` reduces `x = y` to `z ∈ x ↔ z ∈ y`. The coercion to `Set ZFSet` is injective, which is the content of the `SetLike` instance.

<?decl ZFSet.ext?>
:::

**Theorem (Membership is well-founded).** The relation $\in$ on pre-sets is well-founded. So is the relation $\in$ on ZFC sets.

*Proof.* Recall from Volume 4, Chapter 1 that a relation is well-founded when each element is accessible: $x$ is accessible if all $y \in x$ are accessible, and the accessible elements are the least set closed under this rule. The plan is to prove, by induction on $x$, the stronger statement $P(x)$: every pre-set $y$ with $x \approx y$ is accessible. Then $x \approx x$ gives the theorem.

Let $x = \langle \alpha, A \rangle$ and assume $P(A(a))$ for each $a$. Let $y \approx x$. To show that $y$ is accessible, let $w \in y$. Then $w \approx y.\mathrm{Func}(j)$ for some index $j$ of $y$. Since $x \approx y$, there is $a$ with $A(a) \approx y.\mathrm{Func}(j)$. By transitivity and symmetry, $A(a) \approx w$, and $P(A(a))$ says that $w$ is accessible. So all members of $y$ are accessible, and $y$ is accessible.

On ZFC sets, membership is the relation that $\in$ on pre-sets induces on the quotient. A descending chain $[x_0] \ni [x_1] \ni \cdots$ gives pre-sets with $x_{n+1} \in x_n$, by the definition of membership on classes, and there is no such chain. Mathlib transfers the well-foundedness through the quotient with the general lemma for relations lifted to quotients. $\square$

The theorem gives *$\in$-induction*: if a property $p$ of ZFC sets satisfies "$p(y)$ for all $y \in x$ implies $p(x)$", then $p$ holds for all sets.

**Theorem (Regularity).** Each nonempty ZFC set $x$ has an element $y$ with $x \cap y = \emptyset$.

*Proof.* Assume that each $y \in x$ meets $x$. Prove by $\in$-induction that each set $z$ satisfies $z \notin x$. Let $z$ be a set and assume $w \notin x$ for each $w \in z$. If $z \in x$, then by assumption there is $w \in x \cap z$, and $w \in z$, $w \in x$ contradict the induction hypothesis. So $z \notin x$. Hence $x$ has no elements and $x = \emptyset$, against the hypothesis. $\square$

**Theorem (The constructions of ZFC).** For ZFC sets $x$ and $y$, a predicate $p$ and a function $f$ on ZFC sets, the following sets exist, with the stated elements.

1. Empty set: $\emptyset$, with no elements.
2. Insertion and pairs: $\{x\} \cup y$, with $z \in \{x\} \cup y \Leftrightarrow z = x \lor z \in y$. In particular the pair $\{x, y\}$.
3. Union: $\bigcup x$, with $z \in \bigcup x \Leftrightarrow \exists w \in x,\ z \in w$.
4. Power set: $\mathcal{P}(x)$, with $z \in \mathcal{P}(x) \Leftrightarrow z \subseteq x$.
5. Separation: $\{z \in x \mid p(z)\}$, with $z \in \{z \in x \mid p(z)\} \Leftrightarrow z \in x \land p(z)$.
6. Replacement: $f[x]$, with $z \in f[x] \Leftrightarrow \exists w \in x,\ f(w) = z$.
7. Infinity: a set $\omega$ with $\emptyset \in \omega$ and $n \in \omega \Rightarrow n \cup \{n\} \in \omega$.

*Proof.* Each set is first built on pre-sets, then shown to respect $\approx$. Let $x = \langle \alpha, A \rangle$ be a representative.

1. $\emptyset = \langle \mathrm{PEmpty}, ! \rangle$ has no index, so no members.
2. For a pre-set $v$, let $\mathrm{insert}(v, x) = \langle \mathrm{Option}\,\alpha, B \rangle$ with $B(\mathrm{none}) = v$ and $B(\mathrm{some}\,a) = A(a)$. Its members are the pre-sets equivalent to $v$ or to some $A(a)$. If $v \approx v'$ and $x \approx x'$, the indices match: $\mathrm{none}$ with $\mathrm{none}$, and $\mathrm{some}\,a$ with $\mathrm{some}\,a'$ for an $a'$ given by $x \approx x'$. So the construction passes to the quotient.
3. $\bigcup x = \langle \Sigma_{a \in \alpha} (A(a)).\mathrm{Type},\ (a, i) \mapsto (A(a)).\mathrm{Func}(i) \rangle$. Its members are the members of the members of $x$.
4. $\mathcal{P}(x) = \langle \mathcal{P}(\alpha),\ S \mapsto \langle S, A|_S \rangle \rangle$: one member for each subset $S$ of the index type. If $y \approx \langle S, A|_S \rangle$, each member of $y$ is equivalent to some $A(a)$, so $y \subseteq x$. Conversely, let $y = \langle \beta, B \rangle \subseteq x$. Put $S = \{a \in \alpha \mid \exists b,\ B(b) \approx A(a)\}$. Each $B(b)$ is a member of $x$, so it is equivalent to some $A(a)$ with $a \in S$. Each $a \in S$ has some $b$ with $B(b) \approx A(a)$. So $y \approx \langle S, A|_S \rangle$ and $y \in \mathcal{P}(x)$.
5. On pre-sets, $\{z \in x \mid q(z)\} = \langle \{a \mid q(A(a))\}, A|_{\ldots} \rangle$. For a ZFC predicate $p$, take $q(v) = p([v])$, which respects $\approx$.
6. Choose $g$ on pre-sets with $[g(v)] = f([v])$, by definability. Put $f[x] = [\langle \alpha, g \circ A \rangle]$. Its members are the $[g(A(a))] = f([A(a)])$.
7. Define the pre-sets $0 = \emptyset$ and $n + 1 = \mathrm{insert}(n, n)$, and $\omega = \langle \mathbb{N}, n \mapsto n \rangle$, with the index type lifted to level $u$. Then $\emptyset \in \omega$, and if $[v] \in [\omega]$, then $v \approx n$ for some $n$, so $\mathrm{insert}(v,v) \approx n + 1$ by part 2. $\square$

The axiom of choice for ZFC sets is in Section 2, because Mathlib states it with classes.

::: mathlib
`ZFSet.mem_powerset` · `Mathlib.SetTheory.ZFC.Basic`

Each construction has a membership lemma marked `simp`: `ZFSet.mem_insert_iff`, `ZFSet.mem_sUnion`, `ZFSet.mem_powerset`, `ZFSet.mem_sep`, `ZFSet.mem_image` and `ZFSet.mem_range`. The pre-set forms `PSet.powerset` and `PSet.sUnion` show the index types of the proof. The power set uses `Set x.Type`, all subsets of the index type, so the power set of `ZFSet` is full: it has every subset that Lean can name.

<?decl ZFSet.mem_powerset?>
:::

::: mathlib
`ZFSet.image` · `Mathlib.SetTheory.ZFC.Basic`

`ZFSet.image f x` needs `[Definable₁ f]`. With `Classical.allZFSetDefinable` every function `ZFSet → ZFSet` has such an instance. The form `ZFSet.range f` takes `f : α → ZFSet.{u}` for any type `α` with `Small.{u} α`, and `ZFSet.iUnion` is the union of the range. So replacement holds for all Lean functions, not only for those given by a formula. This is the second-order form of the axiom.

<?decl ZFSet.mem_image?>
:::

**Theorem (Kuratowski pairs).** Let $(x, y) = \{\{x\}, \{x, y\}\}$. Then $(x, y) = (x', y')$ implies $x = x'$ and $y = y'$.

*Proof.* Assume $\{\{x\}, \{x, y\}\} = \{\{x'\}, \{x', y'\}\}$. First, $\{x\}$ is an element of the right side, so $\{x\} = \{x'\}$ or $\{x\} = \{x', y'\}$. In both cases $x' \in \{x\}$, so $x = x'$.

Next, consider two cases. If $x = y$, the left side is $\{\{x\}\}$. Then $\{x', y'\} \in \{\{x\}\}$, so $\{x', y'\} = \{x\}$, and $y' = x = y$. If $x \neq y$, then $\{x, y\}$ is an element of the right side, so $\{x, y\} = \{x\}$ or $\{x, y\} = \{x, y'\}$, using $x' = x$. The first case gives $y = x$, which is excluded. So $\{x, y\} = \{x, y'\}$, and $y \in \{x, y'\}$ with $y \neq x$ gives $y = y'$. $\square$

With pairs, Mathlib defines the product $x \times y$ as a subset of $\mathcal{P}(\mathcal{P}(x \cup y))$ by separation, the predicate $\mathrm{IsFunc}(x, y, f)$, which says that $f \subseteq x \times y$ and each $z \in x$ has exactly one $w$ with $(z, w) \in f$, and the set $y^x$ of all such $f$.

### Examples

**Example (The natural numbers as pre-sets).** The pre-set $0$ is $\langle \mathrm{PEmpty}, ! \rangle$. Then $1 = \mathrm{insert}(0, 0) = \langle \mathrm{Option}\ \mathrm{PEmpty}, \mathrm{none} \mapsto 0 \rangle$, and $2 = \mathrm{insert}(1, 1)$ has the index type $\mathrm{Option}(\mathrm{Option}\ \mathrm{PEmpty})$, with $\mathrm{none} \mapsto 1$ and $\mathrm{some}\ \mathrm{none} \mapsto 0$. In general the index type of $n$ has $n$ elements, and the members of $n$ are $n-1, n-2, \dots, 0$. As ZFC sets, $[n] = \{0, 1, \dots, n-1\}$, the von Neumann natural numbers. For instance $[3] = \{\emptyset, \{\emptyset\}, \{\emptyset, \{\emptyset\}\}\}$.

**Example (Equal sets, different pre-sets).** Let $x = \langle \mathrm{Bool}, \_ \mapsto \emptyset \rangle$ and $y = \langle \mathrm{Unit}, \_ \mapsto \emptyset \rangle$. Every member of either one is equivalent to $\emptyset$, so $x \approx y$ and $[x] = [y] = \{\emptyset\}$. But $x \neq y$ as pre-sets: equality of the structures would give $\mathrm{Bool} = \mathrm{Unit}$ as types, and then a bijection between a type with two elements and a type with one element.

**Counterexample (Separation needs an invariant predicate).** On pre-sets, define $q(v)$: "the index type of $v$ has exactly two elements". Let $x = \langle \mathrm{Unit}, \_ \mapsto \langle \mathrm{Bool}, \_ \mapsto \emptyset \rangle \rangle$ and $x' = \langle \mathrm{Unit}, \_ \mapsto \langle \mathrm{Unit}, \_ \mapsto \emptyset \rangle \rangle$. By the previous example, $x \approx x'$. The separation $\{z \in x \mid q(z)\}$ has one member, while $\{z \in x' \mid q(z)\}$ is empty. So the two results are not equivalent, and $q$ does not give a separation on ZFC sets. This is why the pre-set lemma `PSet.mem_sep` has the hypothesis that the predicate respects $\approx$, and why the ZFC form takes a predicate on `ZFSet`.

**Example (A set of functions).** Let $x = \{\emptyset\}$ and $y = \{\emptyset, \{\emptyset\}\} = 2$. Then $x \times y = \{(\emptyset, \emptyset), (\emptyset, \{\emptyset\})\}$, and a function from $x$ to $y$ is a subset $f$ of $x \times y$ with exactly one pair for the single element $\emptyset$. So $y^x$ has the two elements $\{(\emptyset, \emptyset)\}$ and $\{(\emptyset, \{\emptyset\})\}$, as $|y|^{|x|} = 2^1 = 2$ predicts.

### The library around it

The file `Mathlib.SetTheory.ZFC.PSet` defines pre-sets with their membership, subsets, the constructions and the lemmas `PSet.Equiv.refl`, `PSet.Equiv.symm`, `PSet.Equiv.trans` and `PSet.Equiv.euc` of the first theorem. The file `Mathlib.SetTheory.ZFC.Basic` passes to the quotient. For each construction there is a pre-set definition, a `ZFSet` definition by `Quotient.map`, a membership lemma, and a `coe_` lemma that computes the coercion to `Set ZFSet`, for example `ZFSet.coe_sep`. The ordered pair `ZFSet.pair`, its injectivity `ZFSet.pair_injective`, the product `ZFSet.prod`, the predicate `ZFSet.IsFunc` and the set `ZFSet.funs` follow. The predicate `ZFSet.Hereditarily p x` says that $p$ holds for $x$ and, recursively, for all its elements. The instance `ZFSet.small_coe` says that the elements of a set form a small type, and `PSet.embed` is a pre-set of level $u+1$ whose members are the lifts of all pre-sets of level $u$: the universe of one level is a set at the next level.

Common errors of a learner:

- A pre-set equality `x = y` is almost never what is meant. Use `PSet.Equiv x y`, or pass to `ZFSet`.
- `ZFSet.sep p x` takes the predicate first, as `Set.sep` does not. The notation `{y ∈ x | p y}` is available through the `Sep` instance.
- The union of a set is the prefix `⋃₀`, scoped in the namespace `ZFSet`. Open the namespace to use it.
- The empty intersection `⋂₀ ∅` is `∅` by convention, a junk value. The lemma `ZFSet.mem_sInter` needs the hypothesis `x.Nonempty`.

See the reference table for the full list.

### Exercises

1. (A) Prove that $\langle \alpha, A \rangle \approx \emptyset$ if and only if $\alpha$ is empty.
2. (A) Show that $x \subseteq y$ and $y \subseteq x$ imply $x \approx y$ for pre-sets, and that the relation $\subseteq$ on pre-sets is a preorder but not a partial order.
3. (A) Compute the pre-set $\bigcup [3]$ and check that it is equivalent to $2$.
4. (B) Prove that no ZFC set $x$ satisfies $x \in x$, and that there are no $x, y$ with $x \in y \in x$. Hint: use well-foundedness.
5. (B) Prove that there is no ZFC set $v$ that contains every ZFC set. Hint: apply separation to $v$ with the predicate $z \notin z$.
6. (B) Show that the map $\mathbb{N} \to \mathrm{ZFSet}$, $n \mapsto [n]$, is injective. Hint: show by induction that $[n]$ has exactly $n$ elements.
7. (B) Let $f : \mathrm{ZFSet} \to \mathrm{ZFSet}$ be $f(z) = \{z\}$. Find a function $g$ on pre-sets that makes $f$ definable without the axiom of choice.
8. (C) Prove that $\mathcal{P}(x)$ is a set of the same level as $x$, while the collection of all pre-sets of level $u$ is a pre-set only at level $u + 1$. Explain how this matches the index types `Set x.Type : Type u` and `PSet.{u} : Type (u + 1)`.
9. (C) Define the transitive closure of a ZFC set $x$ as $\bigcup_{n} U^n(x)$, where $U(z) = \bigcup z$, using `ZFSet.range` over $\mathbb{N}$. Prove that it is the least transitive set that contains $x$ as a subset.

### Notes and history

Zermelo published his axioms in 1908, and Fraenkel and Skolem added replacement in 1922. The interpretation of sets as well-founded trees up to bisimulation is due to Aczel, who used it to interpret constructive set theory in Martin-Löf type theory in 1978. Mathlib's pre-sets are the same construction with the index types of a Lean universe. Werner compared the calculus of inductive constructions with ZFC in *Sets in types, types in sets* (1997), and Carneiro studied the case of Lean in his thesis *The Type Theory of Lean* (2019). Section 3 returns to their results. For the axioms themselves see Kunen, *Set Theory*, and Jech, *Set Theory*, Chapter 1.

### Reference

<?reference?>
