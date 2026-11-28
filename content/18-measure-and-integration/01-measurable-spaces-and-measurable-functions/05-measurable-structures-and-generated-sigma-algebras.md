---
title: Measurable structures and generated σ-algebras
kind: api
modules:
  - Mathlib.MeasureTheory.MeasurableSpace.Instances
  - Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated
  - Mathlib.MeasureTheory.MeasurableSpace.Prod
  - Mathlib.MeasureTheory.MeasurableSpace.Pi
  - Mathlib.MeasureTheory.MeasurableSpace.PreorderRestrict
  - Mathlib.MeasureTheory.MeasurableSpace.Invariants
  - Mathlib.MeasureTheory.MeasurableSpace.EventuallyMeasurable
  - Mathlib.MeasureTheory.MeasurableSpace.Card
  - Mathlib.MeasureTheory.MeasurableSpace.NCard
  - Mathlib.MeasureTheory.Order.Lattice
  - Mathlib.MeasureTheory.Order.Group.Lattice
explains:
  E2: [MeasureTheory.measurableSet_generateFrom_singleton_iff, Filter.principal_isMeasurablyGenerated_iff, generateFrom_prod_eq, MeasurableSpace.comp_eq_of_measurable_invariants, MeasurableSpace.cardinal_measurableSet_le, Measurable.eventuallyMeasurable_of_eventuallyEq]
  E1: auto
families: []
requires: [V03, V04, V13]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Measurable structures and generated σ-algebras

### Overview

The first three sections of this chapter define σ-algebras, the Borel σ-algebra, π-systems and measurable functions. A user of the library also needs many small facts around these definitions. Which σ-algebra does Lean put on $\mathbb{N}$ or on `Bool`? Which filters have a basis of measurable sets? Which families of sets generate the σ-algebra of a product? How large can a generated σ-algebra be? This section collects the modules that answer such questions.

The modules fall into four groups. The first group gives the instances on discrete types and the Boolean algebra of measurable sets. The second group treats filters with a measurable basis and the measurability of limits. The third group describes generators of product σ-algebras, the σ-algebra of the sets that a map leaves invariant, and the σ-algebra of the sets that are measurable up to a filter. The last group counts the measurable sets and proves that the lattice operations are measurable.

### The library around it

#### Instances on discrete types

The module `Mathlib.MeasureTheory.MeasurableSpace.Instances` gives a σ-algebra to the countable types of the library. The types `ℕ`, `ℤ`, `ℚ`, `ℕ∞`, `Fin n`, `ZMod n`, `Bool`, `Prop`, `Empty` and `PUnit` all receive the discrete σ-algebra, in which each set is measurable. The instances have the names `Nat.instMeasurableSpace`, `Int.instMeasurableSpace`, `Rat.instMeasurableSpace` and so on. Each type also receives an instance of `MeasurableSingletonClass`, for example `Nat.instMeasurableSingletonClass`, and the types with an explicit discrete structure receive `DiscreteMeasurableSpace`, for example `ENat.instDiscreteMeasurableSpace`. So a function out of `ℕ` is measurable with no proof, and `Subsingleton.measurableSingletonClass` covers every type with at most one point.

#### The σ-algebra of one set and the algebra of measurable sets

**Proposition (σ-algebra of one set).** For a set $s \subseteq X$, the σ-algebra $\sigma(\{s\})$ is $\{\emptyset, s, s^c, X\}$.

*Proof.* The four sets form a σ-algebra: the family is closed under complements, and a union of members is $\emptyset$, $s$, $s^c$ or $X$. Each σ-algebra that contains $s$ contains the four sets. $\square$

In Lean this is `MeasureTheory.measurableSet_generateFrom_singleton_iff`, in the form `MeasurableSet t ↔ t = ∅ ∨ t = s ∨ t = sᶜ ∨ t = Set.univ` for the σ-algebra `MeasurableSpace.generateFrom {s}`. The module `Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated` also describes this σ-algebra as a preimage: `MeasurableSpace.generateFrom_singleton` writes it as the comap of the discrete σ-algebra on `Prop` by the map $x \mapsto (x \in s)$, and `MeasurableSpace.generateFrom_singleton_le` states that it is below each σ-algebra in which $s$ is measurable.

The same module makes the subtype `Subtype MeasurableSet` of the measurable sets a Boolean algebra, `MeasurableSet.Subtype.instBooleanAlgebra`. The union, the intersection, the complement and the difference of two measurable sets are again terms of the subtype. The coercion lemmas `MeasurableSet.coe_union`, `MeasurableSet.coe_inter`, `MeasurableSet.coe_compl`, `MeasurableSet.coe_sdiff` and `MeasurableSet.coe_empty` say that the coercion to `Set α` commutes with these operations, and `MeasurableSet.sup_eq_union` and `MeasurableSet.inf_eq_inter` identify the lattice operations with the set operations.

#### Limits of sets and measurably generated filters

For a sequence of sets $s_n$, the sets $\limsup s_n = \bigcap_N \bigcup_{n \ge N} s_n$ and $\liminf s_n = \bigcup_N \bigcap_{n \ge N} s_n$ are countable combinations of the $s_n$. So they are measurable when each $s_n$ is measurable: `MeasurableSet.measurableSet_limsup` and `MeasurableSet.measurableSet_liminf`, with the bounded forms `MeasurableSet.measurableSet_blimsup` and `MeasurableSet.measurableSet_bliminf`. The lemma `MeasurableSet.iUnion_of_monotone` takes a monotone family indexed by a directed order whose filter `Filter.atTop` is countably generated, for example $\mathbb{R}$. Such a union is a countable union along a cofinal sequence, so it is measurable. The lemma `MeasurableSet.iInter_of_antitone` is the dual.

**Definition (measurably generated filter).** A filter $F$ on a measurable space is *measurably generated* if each $s \in F$ contains a measurable $t \in F$.

This is the class `Filter.IsMeasurablyGenerated`, with the field `Filter.IsMeasurablyGenerated.exists_measurable_subset`. The instances cover the filters of analysis. The bottom and top filters are measurably generated (`Filter.isMeasurablyGenerated_bot`, `Filter.isMeasurablyGenerated_top`), and so are `f ⊓ g` and `⨅ i, f i` when the factors are (`Filter.inf_isMeasurablyGenerated`, `Filter.iInf_isMeasurablyGenerated`). A principal filter is measurably generated exactly when its set is measurable.

**Proposition.** The principal filter $\mathcal{P}(s)$ is measurably generated if and only if $s$ is measurable.

*Proof.* If $s$ is measurable, each member of $\mathcal{P}(s)$ contains $s$, and $s$ is a measurable member. Conversely, $s$ is a member, so it contains a measurable member $t$. A member $t$ of $\mathcal{P}(s)$ satisfies $s \subseteq t$, so $t = s$. $\square$

This is `Filter.principal_isMeasurablyGenerated_iff`. The use of the class is `Filter.Eventually.exists_measurable_mem`: a property that holds eventually along $F$ holds on a measurable member of $F$. The main application is `measurableSet_tendsto`. For measurable $f_n : X \to Y$, indexed by a countable type with a countably generated filter $l$, and a filter $l'$ on $Y$ that is countably generated and measurably generated, the set $\{x : f_n(x) \to l'\}$ is measurable. The neighbourhood filters of a second countable Borel space satisfy the hypotheses.

#### Products and families

The product σ-algebra on $X \times Y$ is generated by the rectangles $A \times B$ with $A, B$ measurable, and these rectangles form a π-system: `generateFrom_prod` and `isPiSystem_prod` in `Mathlib.MeasureTheory.MeasurableSpace.Prod`. Smaller families of rectangles also generate it.

**Proposition.** Let $\mathcal{C}$ generate the σ-algebra of $X$ and $\mathcal{D}$ that of $Y$, and suppose that each family is countably spanning: $X$ is a countable union of members of $\mathcal{C}$, and $Y$ of members of $\mathcal{D}$. Then the rectangles $C \times D$ with $C \in \mathcal{C}$ and $D \in \mathcal{D}$ generate the product σ-algebra.

*Proof.* The rectangles are measurable, so the generated σ-algebra $\Sigma'$ is contained in the product. For the converse it is enough that $A \times Y$ and $X \times B$ are in $\Sigma'$ for each $A \in \mathcal{C}$ and $B \in \mathcal{D}$, since these sets generate the product. Write $Y = \bigcup_n D_n$ with $D_n \in \mathcal{D}$. Then $A \times Y = \bigcup_n A \times D_n \in \Sigma'$. The family of the $A$ with $A \times Y \in \Sigma'$ is a σ-algebra that contains $\mathcal{C}$, so it contains all measurable $A$. The same argument works for $X \times B$. $\square$

This is `generateFrom_prod_eq`, with the hypotheses `IsCountablySpanning C` and `IsCountablySpanning D`. The module `Mathlib.MeasureTheory.MeasurableSpace.Pi` has the analogue for a finite product $\prod_i X_i$: `generateFrom_pi_eq` and `generateFrom_pi`, with the π-system `isPiSystem_pi` of boxes $\prod_i A_i$ and `IsPiSystem.pi`. For an arbitrary index type, `MeasurableSpace.pi_eq_generateFrom_projections` writes the product σ-algebra as generated by the sets $\{x : x_i \in A\}$. The Prod module also proves that slices are embeddings: `measurableEmbedding_prodMk_left` states that $y \mapsto (x, y)$ is a measurable embedding when singletons are measurable, and `MeasurableEmbedding.prodMap` handles a product of embeddings. The lemmas `MeasurableSpace.comap_prodMk` and `MeasurableSpace.comap_prodMap` compute the σ-algebra that a pair of maps pulls back.

The module `Mathlib.MeasureTheory.MeasurableSpace.PreorderRestrict` treats families indexed by a preorder, as in the theory of stochastic processes. The restriction of $x = (x_a)_a$ to the indices $\le a$ is measurable (`Preorder.measurable_restrictLe`), and so are the restriction between two levels and the finite forms for a locally finite order (`Preorder.measurable_restrictLe₂`, `Preorder.measurable_frestrictLe`, `Preorder.measurable_frestrictLe₂`).

#### Invariant sets

For a map $f : X \to X$, the *invariant σ-algebra* consists of the measurable sets $s$ with $f^{-1}(s) = s$. It is `MeasurableSpace.invariants f`, and `MeasurableSpace.measurableSet_invariants` states the membership condition. It is below the original σ-algebra (`MeasurableSpace.invariants_le`), it is the whole σ-algebra for the identity (`MeasurableSpace.invariants_id`), and the invariants of $f$ are invariants of each iterate (`MeasurableSpace.le_invariants_iterate`). Ergodic theory uses it, and its key property is the following.

**Proposition.** Let $g : X \to Y$ be measurable for the invariant σ-algebra of $f$, and let the singletons of $Y$ be measurable. Then $g \circ f = g$.

*Proof.* Fix $x$ and put $y = g(x)$. The set $s = g^{-1}(\{y\})$ is in the invariant σ-algebra, so $f^{-1}(s) = s$. Since $x \in s$, also $x \in f^{-1}(s)$, that is $g(f(x)) = y = g(x)$. $\square$

This is `MeasurableSpace.comp_eq_of_measurable_invariants`. The lemma `MeasurableSpace.measurable_invariants_of_semiconj` transports measurability along a map $g$ with $g \circ f_a = f_b \circ g$.

#### Measurability modulo a filter

Let $l$ be a filter that is closed under countable intersections, the class `CountableInterFilter`. A set $s$ is *eventually measurable* for $l$ if $s$ agrees with a measurable set outside a set whose complement is in $l$. The sets of this kind form a σ-algebra, `eventuallyMeasurableSpace m l`, and `EventuallyMeasurableSet m l s` and `EventuallyMeasurable m l f` are the sets and the maps that are measurable for it. Two filters make this useful. For the filter `ae μ` the construction gives the null measurable sets of Chapter 2, and for the filter of residual sets of a topological space it gives the sets with the property of Baire. The basic lemmas are `le_eventuallyMeasurableSpace`, `MeasurableSet.eventuallyMeasurableSet`, `eventuallyMeasurableSet_of_mem_filter` and the congruence lemmas `EventuallyMeasurableSet.congr` and `EventuallyMeasurable.congr`.

**Proposition.** If $f$ is measurable and $g = f$ eventually along $l$, then $g$ is eventually measurable.

*Proof.* Let $N$ be a set with $N^c \in l$ outside of which $f = g$. For measurable $B$, the set $g^{-1}(B)$ agrees with $f^{-1}(B)$ outside $N$, and $f^{-1}(B)$ is measurable. So $g^{-1}(B)$ is eventually measurable. $\square$

This is `Measurable.eventuallyMeasurable_of_eventuallyEq`, and `Measurable.comp_eventuallyMeasurable` composes a measurable map after an eventually measurable one.

#### The size of a generated σ-algebra

The σ-algebra generated by a family $\mathcal{S}$ is the smallest σ-algebra that contains it. A definition from below needs a transfinite recursion. Put $\mathcal{S}_0 = \mathcal{S} \cup \{\emptyset\}$, and let $\mathcal{S}_i$ consist of $\mathcal{S}$, $\emptyset$, the complements of members of earlier stages and the countable unions of members of earlier stages. This is `MeasurableSpace.generateMeasurableRec` in `Mathlib.MeasureTheory.MeasurableSpace.Card`. The recursion stops at the first uncountable ordinal $\omega_1$: a countable family of sets of stages below $\omega_1$ lies in a stage below $\omega_1$, because a countable supremum of countable ordinals is countable. So `MeasurableSpace.generateMeasurable_eq_rec` gives the generated σ-algebra as the stage $\omega_1$.

**Theorem.** The σ-algebra generated by $\mathcal{S}$ has at most $\max(|\mathcal{S}|, 2)^{\aleph_0}$ members.

*Proof sketch.* Put $\kappa = \max(|\mathcal{S}|, 2)^{\aleph_0}$. By induction on $i < \omega_1$, each stage has at most $\kappa$ members: the stage $i$ is built from at most $|i| \cdot \kappa \le \kappa$ earlier sets, and the countable sequences of them number at most $\kappa^{\aleph_0} = \kappa$. The union of $\aleph_1 \le \kappa$ stages of size at most $\kappa$ has size at most $\kappa$. $\square$

This is `MeasurableSpace.cardinal_measurableSet_le` for the σ-algebra `MeasurableSpace.generateFrom s`, with the stage bound `MeasurableSpace.cardinal_generateMeasurableRec_le`. The corollary `MeasurableSpace.cardinal_measurableSet_le_continuum` says that a family of at most $\mathfrak{c}$ sets generates at most $\mathfrak{c}$ sets. The Borel σ-algebra of $\mathbb{R}$ is generated by the countably many intervals with rational ends, so it has at most $\mathfrak{c}$ members. The Cantor set has $2^{\mathfrak{c}}$ subsets, and each is Lebesgue null, so some Lebesgue measurable sets are not Borel. The small module `Mathlib.MeasureTheory.MeasurableSpace.NCard` proves `measurable_encard` and `measurable_ncard`: on a countable type, the cardinality of a set is a measurable function of the set.

#### Lattice operations

The module `Mathlib.MeasureTheory.Order.Lattice` follows the pattern of the algebraic classes such as `MeasurableMul₂`. The class `MeasurableSup M` says that $x \mapsto c \sqcup x$ and $x \mapsto x \sqcup c$ are measurable for each $c$, and `MeasurableSup₂ M` says that $(x, y) \mapsto x \sqcup y$ is measurable on $M \times M$. The classes `MeasurableInf` and `MeasurableInf₂` do the same for $\sqcap$. The lemmas have the names of the operation: `Measurable.sup`, `Measurable.inf`, `Measurable.sup_const`, `Measurable.const_sup`, `Measurable.inf_const`, `Measurable.const_inf`, and the same names under `AEMeasurable`. The forms `Measurable.sup` and `Measurable.inf` state the result for the function `f ⊔ g`, the forms `Measurable.fun_sup` and `Measurable.fun_inf` for the lambda `fun x ↦ f x ⊔ g x`. Finite suprema are measurable by `Finset.measurable_sup'` and `Finset.measurable_range_sup'`. The module `Mathlib.MeasureTheory.Order.Group.Lattice` combines these classes with the group structure: `measurable_abs`, `measurable_posPart` and `measurable_negPart`, with the composed forms `Measurable.abs`, `Measurable.posPart` and `Measurable.negPart` and the multiplicative twins `Measurable.mabs`, `Measurable.oneLePart` and `Measurable.leOnePart`. Chapter 5 uses $f = f^+ - f^-$ with these lemmas.

#### Common errors

1. A learner proves a set on `ℕ` measurable by hand. The instance `Nat.instMeasurableSpace` is the discrete σ-algebra, and `MeasurableSet.of_discrete` proves each such goal.
2. A learner applies `measurableSet_tendsto` with a filter that is not measurably generated, or with an uncountable index type. Both hypotheses matter: an uncountable family of measurable maps can converge on a set that is not measurable.
3. A learner drops `IsCountablySpanning` from `generateFrom_prod_eq`. With a generator of $X$ that does not cover $X$ by countably many sets, the rectangles can generate a strictly smaller σ-algebra.

### Exercises

1. (A) Describe the σ-algebra generated by two sets $s, t \subseteq X$ and give its number of members when the four sets $s \cap t$, $s \setminus t$, $t \setminus s$ and $(s \cup t)^c$ are nonempty.
2. (A) Show that the filter `Filter.atTop` on `ℕ` is measurably generated.
3. (B) Show that for measurable $f_n : X \to \mathbb{R}$ the set of the $x$ where $(f_n(x))$ converges in $\mathbb{R}$ is measurable. Hint: use `measurableSet_tendsto` after a choice of the limit, or the Cauchy criterion.
4. (B) Let $f : X \to X$ and let $g$ be measurable for the invariant σ-algebra of $f$. Show that $g \circ f^{n} = g$ for each $n$.
5. (B) Let $X = Y = \{0, 1\}$ with the discrete σ-algebra and $\mathcal{C} = \mathcal{D} = \{\{0\}\}$. Show that $\mathcal{C}$ and $\mathcal{D}$ generate the σ-algebras of the factors, but the rectangles $C \times D$ generate a σ-algebra with 4 members, not the 16 sets of the product.
6. (C) Show that the Borel σ-algebra of $\mathbb{R}$ has exactly $\mathfrak{c}$ members.

### Reference

<?reference?>
