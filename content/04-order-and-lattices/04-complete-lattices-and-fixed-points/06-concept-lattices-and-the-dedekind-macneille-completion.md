---
title: Concept lattices and the Dedekind-MacNeille completion
kind: api
modules:
  - Mathlib.Order.Concept
  - Mathlib.Order.Completion
explains:
  E2: [upperPolar, gc_upperPolar_lowerPolar, Order.isExtent_iff, Concept.extent_iSup, Concept.ofObject_le_ofAttribute_iff, DedekindCut, DedekindCut.principal_le_iff, DedekindCut.principalEmbedding_trans_factorEmbedding, DedekindCut.principalIso]
  E1: auto
families: []
requires: [V04.C01, V04.C02, V04.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Concept lattices and the Dedekind-MacNeille completion

### Overview

Let $r$ be a relation between a set of objects α and a set of attributes β. For a set $s$ of objects, the attributes that all objects of $s$ have form a set of attributes, and for a set $t$ of attributes, the objects that have all attributes of $t$ form a set of objects. A *concept* is a pair $(s, t)$ in which each of the two sets determines the other in this way. The concepts, ordered by inclusion of their sets of objects, form a complete lattice. This is the subject of formal concept analysis.

When $r$ is the order $\le$ of a partial order α, a concept is a pair $(A, B)$ in which $B$ is the set of the upper bounds of $A$ and $A$ is the set of the lower bounds of $B$. These pairs are the *Dedekind cuts*, and their lattice is the *Dedekind-MacNeille completion* of α: the smallest complete lattice into which α embeds. The cuts of $\mathbb{Q}$ give the real numbers together with $\pm\infty$. This section describes the two files. They use the upper and lower bounds of Chapter 1, the complete lattices of Section 1 and the Galois connections and closure operators of Chapter 6.

### The library around it

**Polars.** The file `Mathlib.Order.Concept` starts from a relation `r : α → β → Prop`. The *upper polar* of $s \subseteq \alpha$ is `upperPolar r s`, the set of $b$ with $r\,a\,b$ for each $a \in s$. The *lower polar* of $t \subseteq \beta$ is `lowerPolar r t`, the set of $a$ with $r\,a\,b$ for each $b \in t$. For the relation $\le$ they are the upper bounds and the lower bounds: `upperPolar_le` and `lowerPolar_le` hold by definition. The two polars reverse inclusion (`upperPolar_anti`, `lowerPolar_anti`), and they turn unions into intersections (`upperPolar_union`, `upperPolar_iUnion`). The basic fact is that they form a Galois connection between `Set α` and the order dual of `Set β`.

$$t \subseteq \operatorname{upperPolar} r\, s \iff s \subseteq \operatorname{lowerPolar} r\, t \qquad (\texttt{gc\_upperPolar\_lowerPolar}).$$

*Proof.* Both sides say that $r\,a\,b$ holds for each $a \in s$ and each $b \in t$. $\square$

The lemma `subset_upperPolar_iff_subset_lowerPolar` is this equivalence without the order dual. The general facts on Galois connections of Chapter 6 then give the rules `subset_lowerPolar_upperPolar` ($s$ is contained in the lower polar of its upper polar) and `upperPolar_lowerPolar_upperPolar` (three polars are one polar). The composite $s \mapsto \operatorname{lowerPolar} r\, (\operatorname{upperPolar} r\, s)$ is the closure operator `extentClosure r` on `Set α`, and `intentClosure r` is the closure operator on `Set β`.

**Extents and intents.** A set $s \subseteq \alpha$ is an *extent*, `Order.IsExtent r s`, if it is the lower polar of some set. A set $t \subseteq \beta$ is an *intent*, `Order.IsIntent r t`, if it is the upper polar of some set. The definition with a range gives the easy closure properties, and the other form is the fixed point property.

$$\operatorname{IsExtent} r\, s \iff \operatorname{lowerPolar} r\, (\operatorname{upperPolar} r\, s) = s \qquad (\texttt{Order.isExtent\_iff}).$$

*Proof.* If $s$ is the fixed point, then $s$ is a lower polar. If $s = \operatorname{lowerPolar} r\, t$, then the rule for three polars, in its dual form `lowerPolar_upperPolar_lowerPolar`, gives the equality. $\square$

Extents are closed under intersections: `Order.IsExtent.inter`, `Order.IsExtent.iInter` and `Order.IsExtent.iInter₂`, and `Order.IsExtent.univ` says that the whole set is an extent. The same holds for intents.

**Concepts.** The structure `Concept α β r` has two fields of data, `extent : Set α` and `intent : Set β`, and two proofs: the upper polar of the extent is the intent, and the lower polar of the intent is the extent. A concept is fixed by each of its two sets (`Concept.ext` and `Concept.ext'`), so `Concept.extent_injective` and `Concept.intent_injective` hold. The constructors `Concept.ofIsExtent` and `Concept.ofIsIntent` make a concept from an extent or an intent. The smallest concept whose extent contains a set $s$ is `Concept.ofObjects r s`, and `Concept.ofObject r a` is the concept of one object. The duals are `Concept.ofAttributes` and `Concept.ofAttribute`.

The order on concepts is the inclusion of the extents, and it is the reverse inclusion of the intents: `Concept.extent_subset_extent_iff` and `Concept.intent_subset_intent_iff`. The concept of an object is below the concept of an attribute exactly when the object has the attribute.

$$\operatorname{ofObject} r\, a \le \operatorname{ofAttribute} r\, b \iff r\,a\,b \qquad (\texttt{Concept.ofObject\_le\_ofAttribute\_iff}).$$

The concepts form a complete lattice. The infimum of a family has the intersection of the extents as its extent, and the supremum has the intersection of the intents as its intent.

$$\Big(\bigsqcup_i c_i\Big).\mathrm{extent} = \operatorname{lowerPolar} r \Big(\bigcap_i c_i.\mathrm{intent}\Big) \qquad (\texttt{Concept.extent\_iSup}).$$

*Proof.* An intersection of intents is an intent, so it is the intent of a concept $c$. A concept $d$ is above each $c_i$ exactly when the intent of $d$ is contained in each intent of $c_i$, that is in their intersection. Thus $c$ is the least upper bound, and its extent is the lower polar of its intent. $\square$

The lemmas `Concept.intent_iSup`, `Concept.extent_iInf` and `Concept.intent_iInf` give the other three components. The map `Concept.swap` exchanges the two sides, and `Concept.swapEquiv` is the order isomorphism from the dual of `Concept α β r` to `Concept β α (swap r)`. For special relations there are more facts: if $r$ is irreflexive, the extent and the intent of a concept on α are disjoint (`Concept.disjoint_extent_intent`), and for a strict total order they are complements (`Concept.isCompl_extent_intent`).

**Dedekind cuts.** The file `Mathlib.Order.Completion` defines `DedekindCut α` as an abbreviation for `Concept α α (· ≤ ·)`, for a preorder α. Thus the complete lattice structure comes from the concept lattice with no new proof. The two sets of a cut have the names `DedekindCut.left` and `DedekindCut.right`, and `DedekindCut.upperBounds_left` and `DedekindCut.lowerBounds_right` restate the two fields. The left set is a lower set, and the right set is an upper set.

The *principal cut* of $a$ is `DedekindCut.principal a`, with left set $\operatorname{Iic} a$ and right set $\operatorname{Ici} a$. It reflects the order (`DedekindCut.principal_le_principal`), and for a partial order it is the order embedding `DedekindCut.principalEmbedding`. A cut is above a principal cut exactly when its left set contains the point.

$$\operatorname{principal} a \le c \iff a \in c.\mathrm{left} \qquad (\texttt{DedekindCut.principal\_le\_iff}).$$

*Proof.* If $\operatorname{Iic} a \subseteq c.\mathrm{left}$, then $a \in c.\mathrm{left}$, because $a \le a$. Conversely, if $a \in c.\mathrm{left}$ and $y \le a$, then $y \in c.\mathrm{left}$, because the left set is a lower set. $\square$

Each cut is the supremum of the principal cuts of its left set, and the infimum of the principal cuts of its right set: `DedekindCut.biSup_principal_left` and `DedekindCut.biInf_principal_right`. So the principal cuts are dense in the completion in both directions.

**The universal property.** Let $f : \beta \hookrightarrow \alpha$ be an order embedding of a partial order β into a complete lattice α. The map `DedekindCut.factorEmbedding f` sends a cut $A$ to $\sup f(A.\mathrm{left})$, and it is an order embedding of `DedekindCut β` into α. It extends $f$ (`DedekindCut.factorEmbedding_principal`).

$$\operatorname{factorEmbedding} f \circ \operatorname{principalEmbedding} = f \qquad (\texttt{DedekindCut.principalEmbedding\_trans\_factorEmbedding}).$$

In Lean the composition is written with `RelEmbedding.trans`, in the order of application, so the principal embedding comes first in the name. In this sense the completion is the smallest complete lattice that contains β. The factor map is not unique: the map $A \mapsto \inf f(A.\mathrm{right})$ is also an embedding that extends $f$, and in general it is a different map.

If α is already a complete lattice, then the principal embedding is an isomorphism, `DedekindCut.principalIso`, with inverse $A \mapsto \sup A.\mathrm{left}$ (`DedekindCut.principalIso_symm_apply`). Together with the complete lattice of concepts, this is the fundamental theorem of concept lattices: each concept lattice is complete, and each complete lattice is a concept lattice. For a linear order α the completion is a complete linear order, and it is densely ordered when α is. The lemma `DedekindCut.lt_iff_exists` says that between two cuts $a < b$ of a linear order there is a principal cut $c$ with $a < c \le b$.

#### Common errors

1. Reading the order of concepts on the intents. The order is inclusion of the extents, so $c \le d$ is the reverse inclusion $d.\mathrm{intent} \subseteq c.\mathrm{intent}$. The lemma `Concept.intent_subset_intent_iff` states this with the sides exchanged.
2. Expecting `DedekindCut ℚ` to be $\mathbb{R}$. It contains also a least and a greatest cut, with left set $\emptyset$ and $\mathbb{Q}$, so it corresponds to $[-\infty, \infty]$.
3. Using `DedekindCut.principalEmbedding` on a preorder that is not a partial order. Then `DedekindCut.principal` is monotone but not injective, and the embedding needs `PartialOrder`.

### Exercises

1. (A) Show that `upperPolar r ∅` is the whole set, with `upperPolar_empty`.
2. (A) For the relation $\le$ on $\mathbb{N}$, find the extent and the intent of `Concept.ofObject (· ≤ ·) 3`.
3. (B) Prove that an intersection of two extents is an extent, from the definition of `Order.IsExtent` and `lowerPolar_union`.
4. (B) Let α be the four subsets of $\{0, 1\}$ ordered by inclusion with the top removed. Describe its Dedekind-MacNeille completion.
5. (B) Prove `DedekindCut.biSup_principal_left` from `DedekindCut.principal_le_iff` and `DedekindCut.upperBounds_left`.
6. (C) Let β have two elements $a, b$ with no relation between them, and embed β in the lattice $\bot < a, b < c < \top$. Find the cuts of β, and show that the maps $A \mapsto \sup f(A.\mathrm{left})$ and $A \mapsto \inf f(A.\mathrm{right})$ differ at the greatest cut.

### Reference

<?reference?>
