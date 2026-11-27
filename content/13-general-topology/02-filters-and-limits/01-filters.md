---
title: Filters
kind: theory
modules:
  - Mathlib.Order.Filter.Defs
  - Mathlib.Order.Filter.Basic
  - Mathlib.Order.Filter.AtTopBot.Defs
  - Mathlib.Order.Filter.Cofinite
  - Mathlib.Order.Filter.Bases.Basic
  - Mathlib.Order.Filter.Map
explains:
  E3: [Filter, Filter.principal, Filter.atTop, Filter.Eventually, Filter.NeBot, Filter.map, Filter.HasBasis]
  E2: [Filter.univ_mem, Filter.inter_mem, Filter.mem_of_superset, Filter.cofinite, Filter.mem_cofinite, Filter.Frequently, Filter.not_frequently, Filter.le_def, Filter.mem_principal, Filter.HasBasis.mem_iff, Filter.atTop_basis, Filter.Eventually.mono, Filter.Eventually.and, Filter.Eventually.of_forall, Filter.mem_atTop_sets, Nat.cofinite_eq_atTop, Filter.comap, Filter.mem_map, Filter.mem_comap, Filter.generate, Filter.mem_bot, Filter.principal_neBot_iff, Filter.instCompleteLatticeFilter]
  E1: auto
families: []
requires: [V04, V13.C01]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Filters

### Overview

The limit of a sequence $(a_n)$ is $L$ if for each $\varepsilon > 0$ there is an $N$ such that $|a_n - L| < \varepsilon$ for all $n \ge N$. Look at the part "there is an $N$ such that for all $n \ge N$". It says that the set $\{n : |a_n - L| < \varepsilon\}$ contains a tail $\{N, N+1, \dots\}$. The sets that contain a tail form a family with three properties. The whole set $\mathbb{N}$ is in it. A superset of a member is a member. The intersection of two members is a member, since the intersection of the tails from $N_1$ and $N_2$ is the tail from $\max(N_1, N_2)$. A family of sets with these three properties is a filter. The members of a filter are the "large" sets, and a property holds "eventually" when the set where it holds is large.

This section defines filters and the operations on them. The next section uses them to define limits.

### Definitions

**Definition (Filter).** A filter on a set $X$ is a family $F$ of subsets of $X$ such that

1. $X \in F$;
2. if $A \in F$ and $A \subseteq B$, then $B \in F$;
3. if $A, B \in F$, then $A \cap B \in F$.

The filter is proper if $\emptyset \notin F$.

*Remarks.* By 2, a filter contains $\emptyset$ if and only if it contains each subset of $X$. That filter is the improper filter. Many texts require a filter to be proper. Mathlib does not, and it writes `NeBot F` for properness. The reason is that the filters then form a complete lattice, and operations such as the infimum never leave the class of filters.

::: mathlib
`Filter` · `Mathlib.Order.Filter.Defs`

`Filter α` is a structure with a field `sets : Set (Set α)` and the three axioms `univ_sets`, `sets_of_superset` and `inter_sets`. Membership `s ∈ f` means `s ∈ f.sets`. The axioms are used through the lemmas `univ_mem`, `mem_of_superset` and `inter_mem`.

<?decl Filter?>
:::

::: mathlib
`Filter.univ_mem` · `Mathlib.Order.Filter.Defs`

The whole type is in each filter.

<?decl Filter.univ_mem?>
:::

::: mathlib
`Filter.mem_of_superset` · `Mathlib.Order.Filter.Defs`

A superset of a member is a member.

<?decl Filter.mem_of_superset?>
:::

::: mathlib
`Filter.inter_mem` · `Mathlib.Order.Filter.Defs`

The intersection of two members is a member. By induction, a finite intersection of members is a member. Infinite intersections are not.

<?decl Filter.inter_mem?>
:::

::: mathlib
`Filter.NeBot` · `Mathlib.Order.Filter.Defs`

`NeBot f` is the class that says `f ≠ ⊥`, that is, `∅ ∉ f`. It is a class so that instance search can find it, for example for `atTop` on `ℕ`.

<?decl Filter.NeBot?>
:::

**Definition (Eventually, frequently).** Let $F$ be a filter on $X$ and $P$ a property of points of $X$. The property $P$ holds eventually along $F$ if $\{x : P(x)\} \in F$. It holds frequently along $F$ if it is not the case that $\neg P$ holds eventually.

::: mathlib
`Filter.Eventually` · `Mathlib.Order.Filter.Defs`

`∀ᶠ x in f, p x` is notation for `Filter.Eventually p f`, that is, `{x | p x} ∈ f`. The notation reads as a quantifier, and the lemmas treat it as one: `Eventually.mono` weakens the property, `Eventually.and` combines two properties.

<?decl Filter.Eventually?>
:::

::: mathlib
`Filter.Eventually.and` · `Mathlib.Order.Filter.Basic`

If `p` and `q` hold eventually, then `p ∧ q` holds eventually. This is axiom 3. In an $\varepsilon$-$N$ proof it is the step "take $N = \max(N_1, N_2)$".

<?decl Filter.Eventually.and?>
:::

::: mathlib
`Filter.Eventually.mono` · `Mathlib.Order.Filter.Basic`

If `p` holds eventually and `p` implies `q` at each point, then `q` holds eventually. This is axiom 2.

<?decl Filter.Eventually.mono?>
:::

::: mathlib
`Filter.Eventually.of_forall` · `Mathlib.Order.Filter.Basic`

A property that holds everywhere holds eventually. This is axiom 1.

<?decl Filter.Eventually.of_forall?>
:::

::: mathlib
`Filter.Frequently` · `Mathlib.Order.Filter.Defs`

`∃ᶠ x in f, p x` is defined as `¬ ∀ᶠ x in f, ¬ p x`. Along `atTop` on `ℕ` it means "for infinitely many `n`".

<?decl Filter.Frequently?>
:::

::: mathlib
`Filter.not_frequently` · `Mathlib.Order.Filter.Basic`

The negation of "frequently `p`" is "eventually not `p`". With `Filter.not_eventually`, this lets `push_neg` move negations through the filter quantifiers.

<?decl Filter.not_frequently?>
:::

**Definition (Principal filter, tails, cofinite filter).**

- For $A \subseteq X$, the principal filter $\mathcal{P}(A)$ is the family of all supersets of $A$.
- For a preorder $X$, the filter $\mathrm{atTop}$ is generated by the sets $[a, \infty) = \{x : a \le x\}$. On $\mathbb{N}$ its members are the sets that contain a tail.
- The cofinite filter on $X$ is the family of sets with a finite complement.

::: mathlib
`Filter.principal` · `Mathlib.Order.Filter.Defs`

`𝓟 s` is the principal filter of `s`, and `mem_principal` says `t ∈ 𝓟 s ↔ s ⊆ t`. The notation `𝓟` needs `open Filter`.

<?decl Filter.principal?>
:::

::: mathlib
`Filter.mem_principal` · `Mathlib.Order.Filter.Defs`

Membership in a principal filter.

<?decl Filter.mem_principal?>
:::

::: mathlib
`Filter.principal_neBot_iff` · `Mathlib.Order.Filter.Basic`

`𝓟 s` is proper if and only if `s` is nonempty.

<?decl Filter.principal_neBot_iff?>
:::

::: mathlib
`Filter.atTop` · `Mathlib.Order.Filter.AtTopBot.Defs`

`atTop` is the infimum over `a` of `𝓟 (Ici a)`. On a directed nonempty order this is the family of sets that contain some `Ici a`, as `mem_atTop_sets` states. The dual filter is `atBot`.

<?decl Filter.atTop?>
:::

::: mathlib
`Filter.mem_atTop_sets` · `Mathlib.Order.Filter.AtTopBot.Basic`

A set is in `atTop` if and only if it contains all `b ≥ a` for some `a`. The form for properties is `eventually_atTop`.

<?decl Filter.mem_atTop_sets?>
:::

::: mathlib
`Filter.cofinite` · `Mathlib.Order.Filter.Cofinite`

The cofinite filter. It is proper exactly on an infinite type.

<?decl Filter.cofinite?>
:::

::: mathlib
`Filter.mem_cofinite` · `Mathlib.Order.Filter.Cofinite`

A set is in `cofinite` if and only if its complement is finite.

<?decl Filter.mem_cofinite?>
:::

**Definition (Order on filters).** For filters $F$ and $G$ on $X$, write $F \le G$ if $G \subseteq F$ as families of sets. Then $F$ is finer than $G$.

*Remarks.* The order is reversed, as for topologies. The intuition: $\mathcal{P}(A) \le \mathcal{P}(B)$ if and only if $A \subseteq B$, so the principal filters are ordered as their sets. A smaller filter is "concentrated on a smaller set". The least filter $\bot$ contains all sets, so $\bot = \mathcal{P}(\emptyset)$. The greatest filter $\top$ contains only $X$, so $\top = \mathcal{P}(X)$. The infimum of a family is the filter generated by the union of the families, and the supremum of a family is the intersection of the families.

::: mathlib
`Filter.le_def` · `Mathlib.Order.Filter.Defs`

`f ≤ g` if and only if each member of `g` is a member of `f`.

<?decl Filter.le_def?>
:::

::: mathlib
`Filter.instCompleteLatticeFilter` · `Mathlib.Order.Filter.Basic`

Filters on a type form a complete lattice (Volume 4). The infimum `f ⊓ g` has as members the sets `s ∩ t` with `s ∈ f` and `t ∈ g` (`mem_inf_iff`).

<?decl Filter.instCompleteLatticeFilter?>
:::

::: mathlib
`Filter.mem_bot` · `Mathlib.Order.Filter.Defs`

Each set is in `⊥`.

<?decl Filter.mem_bot?>
:::

::: mathlib
`Filter.generate` · `Mathlib.Order.Filter.Basic`

The filter generated by a family of sets: the least filter, in the order of families, that contains the family. Its members are the supersets of finite intersections of members of the family.

<?decl Filter.generate?>
:::

**Definition (Image and preimage of a filter).** Let $m : X \to Y$. For a filter $F$ on $X$, the image filter is $m_{*}F = \{B \subseteq Y : m^{-1}(B) \in F\}$. For a filter $G$ on $Y$, the preimage filter $m^{*}G$ is the filter on $X$ whose members are the sets that contain $m^{-1}(B)$ for some $B \in G$.

*Remarks.* The axioms hold for $m_{*}F$, since the preimage commutes with intersections and preserves inclusions. A sequence $a : \mathbb{N} \to X$ gives the filter $a_{*}\mathrm{atTop}$ on $X$, whose members are the sets that contain $a_n$ for all large $n$. This is the bridge from sequences to filters.

::: mathlib
`Filter.map` · `Mathlib.Order.Filter.Defs`

`map m f` is the image filter, and `mem_map` says `t ∈ map m f ↔ m ⁻¹' t ∈ f`. The membership is by definition, so `Iff.rfl` proves `mem_map`.

<?decl Filter.map?>
:::

::: mathlib
`Filter.mem_map` · `Mathlib.Order.Filter.Map`

Membership in an image filter.

<?decl Filter.mem_map?>
:::

::: mathlib
`Filter.comap` · `Mathlib.Order.Filter.Defs`

`comap m g` is the preimage filter.

<?decl Filter.comap?>
:::

::: mathlib
`Filter.mem_comap` · `Mathlib.Order.Filter.Map`

A set is in `comap m g` if and only if it contains the preimage of a member of `g`.

<?decl Filter.mem_comap?>
:::

**Definition (Basis of a filter).** A family $(s_i)_{i \in I}$ of sets, with a predicate $p$ on $I$, is a basis of a filter $F$ if, for each $A \subseteq X$, $A \in F$ if and only if $s_i \subseteq A$ for some $i$ with $p(i)$.

::: mathlib
`Filter.HasBasis` · `Mathlib.Order.Filter.Bases.Basic`

`f.HasBasis p s` says that the sets `s i` with `p i` form a basis of `f`. The index predicate lets one write, for example, the basis of balls `Metric.ball x ε` with `0 < ε`. Most filter proofs in Mathlib go through a basis: `HasBasis.mem_iff` turns membership into an existence statement.

<?decl Filter.HasBasis?>
:::

::: mathlib
`Filter.HasBasis.mem_iff` · `Mathlib.Order.Filter.Bases.Basic`

Membership through a basis.

<?decl Filter.HasBasis.mem_iff?>
:::

::: mathlib
`Filter.atTop_basis` · `Mathlib.Order.Filter.AtTopBot.Basic`

The intervals `Ici a` form a basis of `atTop` on a nonempty directed order.

<?decl Filter.atTop_basis?>
:::

### Theorems and proofs

**Theorem (Generated filter).** Let $\mathcal{S}$ be a family of subsets of $X$. The family $F$ of sets that contain a finite intersection $S_1 \cap \dots \cap S_n$ of members of $\mathcal{S}$, with $n \ge 0$, is a filter. It is the least filter that contains $\mathcal{S}$ as a family. It is proper if and only if each finite intersection of members of $\mathcal{S}$ is nonempty.

*Proof.* The empty intersection, $n = 0$, is $X$, so $X \in F$. A superset of a set that contains a finite intersection contains the same intersection. If $A \supseteq S_1 \cap \dots \cap S_n$ and $B \supseteq T_1 \cap \dots \cap T_m$, then $A \cap B$ contains the intersection of the $n + m$ sets. So $F$ is a filter. Each filter that contains $\mathcal{S}$ contains the finite intersections by axiom 3 and then their supersets by axiom 2, so it contains $F$. Finally, $\emptyset \in F$ if and only if some finite intersection is contained in $\emptyset$, that is, empty. $\square$

**Theorem (Cofinite and tails on the natural numbers).** On $\mathbb{N}$ the cofinite filter equals $\mathrm{atTop}$.

*Proof.* Let $A \in \mathrm{atTop}$. Then $A \supseteq \{N, N+1, \dots\}$ for some $N$, so $\mathbb{N} \setminus A \subseteq \{0, \dots, N-1\}$ is finite. Conversely, let $\mathbb{N} \setminus A$ be finite, and let $N$ be one more than its largest element, or $N = 0$ if it is empty. Then each $n \ge N$ is in $A$. $\square$

::: mathlib
`Nat.cofinite_eq_atTop` · `Mathlib.Order.Filter.Cofinite`

The theorem. On `ℤ` the two filters differ: `cofinite` on `ℤ` is `atBot ⊔ atTop`.

<?decl Nat.cofinite_eq_atTop?>
:::

**Theorem (Galois connection of map and comap).** For $m : X \to Y$, a filter $F$ on $X$ and a filter $G$ on $Y$: $m_{*}F \le G$ if and only if $F \le m^{*}G$.

*Proof.* Assume $m_{*}F \le G$, and let $A$ be a member of $m^{*}G$. Then $A \supseteq m^{-1}(B)$ for some $B \in G$. By assumption $B \in m_{*}F$, that is, $m^{-1}(B) \in F$, so $A \in F$. Conversely, assume $F \le m^{*}G$ and let $B \in G$. Then $m^{-1}(B) \in m^{*}G \subseteq F$, so $B \in m_{*}F$. $\square$

The next section uses this theorem: a limit statement can be written with `map` or with `comap`, and Mathlib has both forms.

### Examples

**Example (Eventually along atTop).** On $\mathbb{N}$, the statement $\forall^{f} n \in \mathrm{atTop},\ n^2 > 100$ holds, since $n^2 > 100$ for each $n \ge 11$. The statement "$n$ is even" holds frequently but not eventually along $\mathrm{atTop}$: the set of even numbers contains no tail, and neither does the set of odd numbers. So a filter can contain neither a set nor its complement. A filter that always contains one of the two is an ultrafilter, the subject of Section 3.

**Example (The filter of a sequence).** Let $a_n = (-1)^n$ in $\mathbb{R}$. The image filter $a_{*}\mathrm{atTop}$ contains a set $B$ if and only if $a_n \in B$ for all large $n$, that is, if and only if $\{-1, 1\} \subseteq B$. So $a_{*}\mathrm{atTop} = \mathcal{P}(\{-1, 1\})$. The image filter forgets the order of the terms and keeps only what happens in the long run.

**Example (A filter that is not principal).** The filter $\mathrm{atTop}$ on $\mathbb{N}$ is not principal. A principal filter $\mathcal{P}(A)$ contains $A$, its least member. If $\mathrm{atTop} = \mathcal{P}(A)$, then $A$ is contained in each tail, so $A = \emptyset$, and then $\emptyset \in \mathrm{atTop}$, which is false. On a finite set each filter is principal: it is $\mathcal{P}$ of the intersection of its members, which is a finite intersection.

### The library around it

The core definitions are in `Mathlib.Order.Filter.Defs`, the lattice structure and the lemmas on `Eventually` are in `Mathlib.Order.Filter.Basic`, `map` and `comap` are in `Mathlib.Order.Filter.Map`, and bases are in `Mathlib.Order.Filter.Bases.Basic`. The filters `atTop` and `atBot` have a large library in `Mathlib.Order.Filter.AtTopBot`.

A Mathlib proof about filters rarely touches the sets directly. It works with the quantifier `∀ᶠ` and the lemmas `Eventually.mono`, `Eventually.and`, `Eventually.of_forall` and `Eventually.exists`, the last for a proper filter. The tactic `filter_upwards [h₁, h₂] with x hx₁ hx₂` combines several eventual facts and leaves the pointwise goal. It is the formal form of "for $n \ge \max(N_1, N_2)$ both facts hold".

The relation "equal eventually", `f =ᶠ[l] g`, and "less eventually", `f ≤ᶠ[l] g`, are defined with `Eventually`. They state, for example, that two functions agree near a point.

The reference table at the end of the section lists the declarations of the modules.

### Exercises

1. (A) Show that the family of subsets of $\mathbb{R}$ that contain an interval $(-\varepsilon, \varepsilon)$ with $\varepsilon > 0$ is a proper filter. Show that it is not principal.
2. (A) Show that $\mathcal{P}(A) \sqcap \mathcal{P}(B) = \mathcal{P}(A \cap B)$ and $\mathcal{P}(A) \sqcup \mathcal{P}(B) = \mathcal{P}(A \cup B)$.
3. (A) Show that a property $P$ of natural numbers holds frequently along $\mathrm{atTop}$ if and only if $P(n)$ holds for infinitely many $n$.
4. (B) Show that the cofinite filter on $X$ is the infimum of the filters $\mathcal{P}(X \setminus \{x\})$, and that it is proper if and only if $X$ is infinite.
5. (B) Let $m : X \to Y$. Show that $m_{*}\mathcal{P}(A) = \mathcal{P}(m(A))$ and $m^{*}\mathcal{P}(B) = \mathcal{P}(m^{-1}(B))$.
6. (B) Show that $m_{*}F$ is proper if $F$ is proper, and give an example of a proper $G$ with $m^{*}G$ improper.
7. (C) Show that a filter $F$ has a countable basis if and only if there is a decreasing sequence $A_0 \supseteq A_1 \supseteq \dots$ of sets with $F = \{B : A_n \subseteq B \text{ for some } n\}$.

### Notes and history

Filters were introduced by Henri Cartan in 1937, in two notes in the *Comptes rendus*, to give a theory of convergence that works in all topological spaces. Bourbaki made them the basis of *Topologie générale* (1940). The older theory of nets, by Moore and Smith (1922), does the same work; a net gives a filter of its tails, and a filter gives a net indexed by its members. Mathlib chose filters because they are sets of sets, so they need no new index type, and because they form a complete lattice. The design of the filter library in Mathlib goes back to Johannes Hölzl, who used filters for limits in Isabelle/HOL before Lean.

### Reference

<?reference?>
