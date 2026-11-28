---
title: Frames, complete sublattices and complete lattice homomorphisms
kind: api
modules:
  - Mathlib.Order.CompleteBooleanAlgebra
  - Mathlib.Order.CompleteSublattice
  - Mathlib.Order.Hom.CompleteLattice
explains:
  E2: [inf_sSup_eq, iInf_iSup_eq, compl_iSup, Order.Frame.ofMinimalAxioms, CompleteSublattice.mk', CompleteLatticeHom.range, CompleteLatticeHom.setPreimage, map_iSup]
  E1: auto
families: []
requires: [V04.C02, V04.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Frames, complete sublattices and complete lattice homomorphisms

### Overview

A complete lattice need not be distributive, and a distributive complete lattice need not satisfy the infinite distributive laws. The open sets of a topological space satisfy $U \cap \bigcup_i V_i = \bigcup_i (U \cap V_i)$ for each family, but the dual law with an infinite intersection fails, because the intersection of infinitely many open sets is in general not open. A complete lattice in which $\sqcap$ distributes over each supremum is a *frame*. The dual notion is a *coframe*, and the filters on a type form a coframe.

This section describes three files. The first defines frames, coframes, the complete distributive and the completely distributive lattices, and the complete Boolean algebras. The second defines the complete sublattices of a complete lattice. The third defines the maps that preserve all suprema, all infima, or both. The files use the Heyting algebras and the bounded lattice homomorphisms of Chapter 3, and the complete lattices of Section 1.

### The library around it

**The distributive classes.** The file `Mathlib.Order.CompleteBooleanAlgebra` has six classes. They differ in the distributive law that they ask for.

| Class | Law |
|---|---|
| `Order.Frame` | $a \sqcap \bigsqcup_i f_i = \bigsqcup_i (a \sqcap f_i)$ |
| `Order.Coframe` | $a \sqcup \bigsqcap_i f_i = \bigsqcap_i (a \sqcup f_i)$ |
| `CompleteDistribLattice` | both of these laws |
| `CompletelyDistribLattice` | $\bigsqcap_a \bigsqcup_b f_{a,b} = \bigsqcup_g \bigsqcap_a f_{a, g(a)}$ |
| `CompleteBooleanAlgebra` | a complete lattice that is a Boolean algebra |
| `CompleteAtomicBooleanAlgebra` | a complete Boolean algebra that is completely distributive |

The class `Order.Frame` extends `CompleteLattice` and `HeytingAlgebra`, so a frame carries the operation $a \Rightarrow b$ as data. The infinite law is then a theorem, not an axiom.

$$a \sqcap \sup s = \bigsqcup_{b \in s} (a \sqcap b) \qquad (\texttt{inf\_sSup\_eq}).$$

*Proof.* In a Heyting algebra, $a \sqcap c \le b \iff c \le a \Rightarrow b$, so the map $c \mapsto a \sqcap c$ is the lower adjoint of a Galois connection (`gc_inf_himp`). A lower adjoint preserves each supremum (`GaloisConnection.l_sSup`, Chapter 6). $\square$

The forms for families are `inf_iSup_eq` and `iSup_inf_eq`, and the coframe forms are their duals. Other consequences in a frame are `iSup_disjoint_iff`, which says that $\bigsqcup_i f_i$ is disjoint from $a$ when each $f_i$ is, the product formula `sSup_inf_sSup`, and the formula `himp_eq_sSup` for the implication, $a \Rightarrow b = \sup\{w : w \sqcap a \le b\}$. Each frame is a distributive lattice by `Order.Frame.toDistribLattice`.

A complete distributive lattice is both a frame and a coframe. A completely distributive lattice satisfies the law of the table for each doubly indexed family, and the law gives the other ones. In each complete lattice one inequality holds, `le_iInf_iSup`, so the class asks only for the other one. The main lemma of the class is the equality.

$$\bigsqcap_a \bigsqcup_b f_{a,b} = \bigsqcup_{g} \bigsqcap_a f_{a, g(a)} \qquad (\texttt{iInf\_iSup\_eq}),$$

where $g$ runs over the choice functions $g : \forall a, \kappa(a)$. Each complete linear order is completely distributive, by `CompleteLinearOrder.toCompletelyDistribLattice`. The open sets of a space form a frame that is in general not completely distributive. The instances follow the inclusions between the classes: `CompleteBooleanAlgebra.toCompleteDistribLattice` and `CompleteAtomicBooleanAlgebra.toCompletelyDistribLattice`. Products, function types and order duals inherit each class.

**Complete Boolean algebras.** In a complete Boolean algebra the laws of De Morgan hold for each family.

$$\Big(\bigsqcup_i f_i\Big)^{c} = \bigsqcap_i f_i^{c} \qquad (\texttt{compl\_iSup}).$$

*Proof.* The complement is an order isomorphism from the algebra to its dual, because $a \le b \iff b^c \le a^c$. An order isomorphism sends each supremum to the corresponding supremum, and a supremum in the dual is an infimum. $\square$

The lemmas `compl_iInf`, `compl_sSup` and `compl_sInf` are the other forms, and `compl_sSup'` writes the result with the image of the set. The propositions form a complete atomic Boolean algebra by `Prop.instCompleteAtomicBooleanAlgebra`, and so do the subsets of a type, by `Set.instCompleteAtomicBooleanAlgebra`. A complete Boolean algebra is completely distributive only if it is atomic. Section 5 of Chapter 3 treats the atoms.

**Minimal axioms and transfer.** To prove that a complete lattice is a frame, it is enough to prove one inequality. The structure `Order.Frame.MinimalAxioms` has the single field $a \sqcap \sup s \le \bigsqcup_{b \in s} (a \sqcap b)$, and `Order.Frame.ofMinimalAxioms` builds the frame from it. It defines the missing operations by $a \Rightarrow b = \sup\{c : c \sqcap a \le b\}$ and $a^c = a \Rightarrow \bot$. The structures `Order.Coframe.MinimalAxioms`, `CompleteDistribLattice.MinimalAxioms` and `CompletelyDistribLattice.MinimalAxioms` play the same part for the other classes. The constructors `Function.Injective.frame`, `Function.Injective.completeBooleanAlgebra` and the others transfer a class along an injective map that preserves the operations, and the constructors in the `Equiv` namespace, such as `Equiv.frame`, transfer it along a bijection.

**Complete sublattices.** The file `Mathlib.Order.CompleteSublattice` defines `CompleteSublattice α`: a sublattice of a complete lattice α that is closed under each supremum and each infimum. Closure under the binary operations follows from the infinite conditions, and `CompleteSublattice.mk'` asks only for these.

*Proof of the claim.* For $x, y$ in the set, $x \sqcup y = \sup\{x, y\}$, and $\{x, y\}$ is a subset of the set, so $x \sqcup y$ is in the set. The infimum is dual. $\square$

The empty set is a subset, so $\bot = \sup \emptyset$ and $\top = \inf \emptyset$ are in each complete sublattice: `CompleteSublattice.bot_mem` and `CompleteSublattice.top_mem`. A complete sublattice $L$ is a complete lattice by `CompleteSublattice.instCompleteLattice`, with the operations of α: `CompleteSublattice.coe_sSup` holds by definition, and `CompleteSublattice.coe_iInf` is the indexed form for infima. This differs from the closure systems of Chapter 6, where the infimum is that of α but the supremum is not. The map `CompleteSublattice.subtype` is the inclusion as a complete lattice homomorphism. Complete sublattices push forward and pull back under a complete lattice homomorphism, by `CompleteSublattice.map` and `CompleteSublattice.comap`. The image of a homomorphism $f$ is the complete sublattice `CompleteLatticeHom.range`, and `CompleteLatticeHom.toOrderIsoRangeOfInjective` identifies α with the image when $f$ is injective. The lemma `CompleteSublattice.isComplemented_iff` says that $L$ is a complemented lattice exactly when each element of $L$ has a complement in α that is in $L$. The standard example is the set of submodules that a linear map sends into themselves.

**Homomorphisms.** The file `Mathlib.Order.Hom.CompleteLattice` defines four types of maps. Each has a companion class, so that a lemma stated for the class applies to each stronger type.

| Type | Class | Preserves |
|---|---|---|
| `sSupHom α β` | `sSupHomClass` | each `sSup` |
| `sInfHom α β` | `sInfHomClass` | each `sInf` |
| `FrameHom α β` | `FrameHomClass` | each `sSup`, $\sqcap$ and $\top$ |
| `CompleteLatticeHom α β` | `CompleteLatticeHomClass` | each `sSup` and each `sInf` |

The axioms are `sSupHomClass.map_sSup` and `sInfHomClass.map_sInf`, and the indexed forms follow.

$$f\Big(\bigsqcup_i g_i\Big) = \bigsqcup_i f(g_i) \qquad (\texttt{map\_iSup}).$$

*Proof.* By definition $\bigsqcup_i g_i = \sup (\operatorname{range} g)$, so $f(\bigsqcup_i g_i) = \sup f(\operatorname{range} g)$, and $f(\operatorname{range} g) = \operatorname{range}(f \circ g)$. $\square$

A map that preserves each supremum preserves $\bot = \sup \emptyset$ and the binary $\sqcup$, so `sSupHomClass.toSupBotHomClass` is an instance. In the same way `FrameHomClass.toBoundedLatticeHomClass` and the instances for `CompleteLatticeHom` connect these classes to the lattice homomorphisms of Chapter 3. Each order isomorphism is a complete lattice homomorphism, by `OrderIsoClass.toCompleteLatticeHomClass`. A frame homomorphism need not preserve the implication: `TopologicalSpace.Opens.frameHom`, the inclusion of the open sets into all sets, is an example. Each type has the identity, the composition and the extensionality lemma, and `CompleteLatticeHom.dual` and `sSupHom.dual` pass to the order duals.

The concrete maps come from sets. For $f : \alpha \to \beta$ the preimage is a complete lattice homomorphism `CompleteLatticeHom.setPreimage f`, from `Set β` to `Set α`, because the preimage preserves each union and each intersection. The image preserves only unions (`Set.image_sSup`), so `sSupHom.setImage f` is a `sSupHom`. A bijection gives an order isomorphism of the power sets, `Equiv.toOrderIsoSet`.

#### Common errors

1. Expecting the infinite distributive law in a `DistribLattice` with a `CompleteLattice` instance. The lemma `inf_iSup_eq` needs `Order.Frame`, which is a separate class. A distributive complete lattice need not be a frame.
2. Expecting a `FrameHom` to preserve $\Rightarrow$ or the complement. The class asks only for `sSup`, $\sqcap$ and $\top$. Use `HeytingHom` of Chapter 3 for maps that preserve the implication.
3. Building a `CompleteSublattice` with the structure constructor and proving closure under $\sqcup$ and $\sqcap$ by hand. Use `CompleteSublattice.mk'`, which needs only the closure under `sSup` and `sInf`.

### Exercises

1. (A) Prove `iSup_inf_eq` from `inf_iSup_eq` and the commutativity of $\sqcap$.
2. (A) Show that the preimage of a map preserves complements of sets, with `CompleteLatticeHom.setPreimage` and the lemmas of Chapter 3 on bounded lattice homomorphisms.
3. (B) Prove `compl_iInf` from `compl_iSup` and `compl_compl`.
4. (B) Let $L$ be the set of the subsets $s$ of $\mathbb{N}$ such that $s$ is finite or $s = \mathbb{N}$. Show that $L$ is closed under finite unions and finite intersections, but is not a complete sublattice of `Set ℕ`.
5. (B) In the frame of the open subsets of $\mathbb{R}$, the infimum of a family is the interior of its intersection. Let $V_n = (-1/n, 1/n)$ and $U = \mathbb{R} \setminus \{0\}$. Show that $U \sqcup \bigsqcap_n V_n \ne \bigsqcap_n (U \sqcup V_n)$, so that this frame is not a coframe.
6. (C) Prove that a complete Boolean algebra that is completely distributive is atomic: each element $a \ne \bot$ is above an atom.

### Reference

<?reference?>
