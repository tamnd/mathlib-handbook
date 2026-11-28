---
title: Boolean subalgebras, the Booleanisation and Birkhoff representation
kind: api
modules:
  - Mathlib.Order.BooleanSubalgebra
  - Mathlib.Order.Booleanisation
  - Mathlib.Order.Birkhoff
explains:
  E2: [BooleanSubalgebra.mem_bot, BooleanSubalgebra.mem_closure_iff_sup_sdiff, BooleanSubalgebra.gc_map_comap, Booleanisation.lift_le_comp, Booleanisation.liftLatticeHom_injective, LowerSet.supIrred_iff_of_finite, OrderIso.lowerSetSupIrred, exists_birkhoff_representation]
  E1: auto
families: []
requires: [V04.C01, V04.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Boolean subalgebras, the Booleanisation and Birkhoff representation

### Overview

The three files of this section build new Boolean algebras and distributive lattices from old ones, and they compare an abstract lattice with a lattice of sets. A Boolean subalgebra is a subset of a Boolean algebra that contains $\bot$ and is closed under $\sqcup$, $\sqcap$ and complement. The Booleanisation of a generalized Boolean algebra adds a complement to each element, and it shows that the lattice equations that do not mention the complement hold in each generalized Boolean algebra as soon as they hold in each Boolean algebra. Birkhoff representation says that a finite distributive lattice is the lattice of the lower sets of its sup-irreducible elements, so it is a lattice of sets with union and intersection.

The section uses the Boolean algebras and the generalized Boolean algebras of the earlier sections of this chapter, and the order embeddings and isomorphisms of Chapter 2. The maps between Boolean subalgebras are bundled homomorphisms `BoundedLatticeHom α β`, which preserve $\sqcup$, $\sqcap$, $\bot$ and $\top$, and the embeddings of the Booleanisation and of Birkhoff are bundled `LatticeHom`s.

### The library around it

**Boolean subalgebras.** The structure `BooleanSubalgebra α`, for a Boolean algebra $\alpha$, extends `Sublattice α` with two fields: the carrier contains $\bot$ and it is closed under complement. It is a `SetLike` structure, so a Boolean subalgebra $L$ coerces to a set, membership is written $a \in L$, and $L \le M$ means inclusion. The forgetful map is `BooleanSubalgebra.toSublattice`. The closure lemmas follow the usual pattern of names, the operation followed by *mem*: `BooleanSubalgebra.bot_mem`, `BooleanSubalgebra.top_mem`, `BooleanSubalgebra.sup_mem`, `BooleanSubalgebra.inf_mem`, `BooleanSubalgebra.compl_mem`, and the derived `BooleanSubalgebra.sdiff_mem` and `BooleanSubalgebra.himp_mem`, from $a \setminus b = a \sqcap b^c$ and $a \Rightarrow b = b \sqcup a^c$. The simp lemma `BooleanSubalgebra.compl_mem_iff` says $a^c \in L \iff a \in L$. In a complete Boolean algebra a Boolean subalgebra is closed under finite suprema and infima only: `BooleanSubalgebra.sSup_mem` and `BooleanSubalgebra.iSup_mem` have a finiteness hypothesis.

Each Boolean subalgebra is a Boolean algebra by the instance `BooleanSubalgebra.instBooleanAlgebraCoe`, and the operations are computed in $\alpha$: the simp lemmas `BooleanSubalgebra.val_sup`, `BooleanSubalgebra.val_compl` and their neighbours move a coercion through an operation. The inclusion into $\alpha$ is `BooleanSubalgebra.subtype`, and for $L \le M$ the inclusion of $L$ into $M$ is `BooleanSubalgebra.inclusion`. Both are bounded lattice homomorphisms.

The Boolean subalgebras of $\alpha$ form a complete lattice (`BooleanSubalgebra.instCompleteLattice`). The top is the whole algebra, with `BooleanSubalgebra.coe_top` and the isomorphism `BooleanSubalgebra.topEquiv`. The infimum of a family is the intersection (`BooleanSubalgebra.coe_iInf`). The bottom is the smallest possible one.

$$a \in \bot \iff a = \bot \lor a = \top \qquad (\texttt{BooleanSubalgebra.mem\_bot}).$$

*Proof.* Each Boolean subalgebra contains $\bot$ and $\top = \bot^c$. The set $\{\bot, \top\}$ is closed under the operations, because $\bot^c = \top$, $\top^c = \bot$, and the supremum and the infimum of two elements of $\{\bot, \top\}$ are again in it. So it is the least Boolean subalgebra. $\square$

A bounded lattice homomorphism $f : \alpha \to \beta$ of Boolean algebras gives the image `BooleanSubalgebra.map f` and the preimage `BooleanSubalgebra.comap f`, with membership lemmas `BooleanSubalgebra.mem_map` and `BooleanSubalgebra.mem_comap`. The preimage is a Boolean subalgebra because $f$ preserves complements: $f(a^c)$ is a complement of $f(a)$, and complements are unique in a distributive lattice. The two maps form a Galois connection.

$$\operatorname{map} f\, L \le M \iff L \le \operatorname{comap} f\, M \qquad (\texttt{BooleanSubalgebra.gc\_map\_comap}).$$

*Proof.* Both sides say that $f(a) \in M$ for each $a \in L$. $\square$

So the image preserves suprema and the preimage preserves infima, as Chapter 6 explains for each Galois connection: `BooleanSubalgebra.map_iSup` and `BooleanSubalgebra.comap_iInf` are the instances of this rule.

**The Boolean subalgebra generated by a set.** The closure `BooleanSubalgebra.closure s` is the infimum of the Boolean subalgebras that contain $s$. Its universal property is `BooleanSubalgebra.closure_le`: $\operatorname{closure} s \le L \iff s \subseteq L$. The induction principle `BooleanSubalgebra.closure_bot_sup_induction` proves a property of each element of the closure from the elements of $s$, from $\bot$, and from the closure under $\sqcup$ and complement. When $s$ already contains $\bot$ and is closed under complement, the closure is the sublattice generated by $s$ (`BooleanSubalgebra.closure_eq_latticeClosure`). When $s$ is a sublattice that contains $\bot$ and $\top$, the closure has an explicit form.

$$a \in \operatorname{closure} s \iff a = \bigsqcup_{(x, y) \in t} (x \setminus y) \text{ for a finite set } t \subseteq s \times s \qquad (\texttt{BooleanSubalgebra.mem\_closure\_iff\_sup\_sdiff}).$$

*Proof sketch.* Let $D$ be the set of the finite suprema of differences $x \setminus y$ with $x, y \in s$. Each element of $D$ is in the closure. Conversely, $D$ contains $s$, because $x = x \setminus \bot$, it contains $\bot$ as the empty supremum, and it is closed under $\sqcup$. For the complement, $(\bigsqcup_i (x_i \setminus y_i))^c = \bigsqcap_i (x_i^c \sqcup y_i)$, and $x_i^c = \top \setminus x_i$ and $y_i = y_i \setminus \bot$ are in $D$. Distributivity writes a finite infimum of finite suprema as a finite supremum of finite infima, and $(a \setminus b) \sqcap (c \setminus d) = (a \sqcap c) \setminus (b \sqcup d)$, with $a \sqcap c$ and $b \sqcup d$ in $s$ since $s$ is a sublattice. So $D$ is a Boolean subalgebra that contains $s$, and it contains the closure. $\square$

The companion `BooleanSubalgebra.closure_sdiff_sup_induction` turns this description into an induction principle.

**The Booleanisation.** A generalized Boolean algebra is a distributive lattice with $\bot$ and a relative complement $a \setminus b$, but with no top element; the finite subsets of an infinite set are the standard example. The type `Booleanisation α` is the disjoint union $\alpha \sqcup \alpha$. The first copy is the image of `Booleanisation.lift`, and the second copy, the image of `Booleanisation.comp`, holds the formal complements. The complement exchanges the copies (`Booleanisation.compl_lift`, `Booleanisation.compl_comp`). The order is defined by three rules and one exclusion.

| Lean name | Statement |
| --- | --- |
| `Booleanisation.lift_le_lift` | $\operatorname{lift} a \le \operatorname{lift} b \iff a \le b$ |
| `Booleanisation.comp_le_comp` | $\operatorname{comp} a \le \operatorname{comp} b \iff b \le a$ |
| `Booleanisation.lift_le_comp` | $\operatorname{lift} a \le \operatorname{comp} b \iff \operatorname{Disjoint} a\, b$ |
| `Booleanisation.not_comp_le_lift` | $\neg (\operatorname{comp} a \le \operatorname{lift} b)$ |
| `Booleanisation.lift_sup_comp` | $\operatorname{lift} a \sqcup \operatorname{comp} b = \operatorname{comp} (b \setminus a)$ |
| `Booleanisation.comp_sup_comp` | $\operatorname{comp} a \sqcup \operatorname{comp} b = \operatorname{comp} (a \sqcap b)$ |
| `Booleanisation.comp_bot` | $\operatorname{comp} \bot = \top$ |

Each rule copies a law of a Boolean algebra. For example `Booleanisation.lift_le_comp` copies the law $a \le b^c \iff a \sqcap b = \bot$, and `Booleanisation.comp_sup_comp` copies the law of De Morgan $a^c \sqcup b^c = (a \sqcap b)^c$. The exclusion `Booleanisation.not_comp_le_lift` reflects the fact that a complement $a^c$ is "large" and an element of $\alpha$ is "small". The lemmas are all simp lemmas, and the formulas for $\sqcup$, $\sqcap$, $\setminus$ and the complement hold by `rfl`, so `simp` computes in the Booleanisation after a case split on the two copies. With these rules `Booleanisation.instBooleanAlgebra` makes `Booleanisation α` a Boolean algebra. The map `Booleanisation.liftLatticeHom` is the inclusion of $\alpha$ as a lattice homomorphism.

$$\operatorname{lift} : \alpha \to \operatorname{Booleanisation} \alpha \text{ is injective} \qquad (\texttt{Booleanisation.liftLatticeHom\_injective}).$$

*Proof.* The map is the left inclusion of a disjoint union, and this map is injective. $\square$

The consequence is a transfer principle. Let $u = v$ be an equation in $\sqcup$, $\sqcap$, $\bot$ and $\setminus$ that holds in each Boolean algebra. Apply it in `Booleanisation α` to the images $\operatorname{lift} a_i$. The map lift preserves the operations, so the equation holds for the images of $u$ and $v$, and injectivity gives the equation in $\alpha$.

**Birkhoff representation.** An element $a$ of a join-semilattice is sup-irreducible (`SupIrred a`) when it is not minimal and $a = b \sqcup c$ implies $a = b$ or $a = c$. In the lattice of the lower sets of a partial order, each principal lower set $\operatorname{Iic} a$ is sup-irreducible (`LowerSet.supIrred_Iic`). For a finite order the converse holds.

$$\operatorname{SupIrred} s \iff \exists a,\ \operatorname{Iic} a = s \qquad (\texttt{LowerSet.supIrred\_iff\_of\_finite}).$$

*Proof.* A lower set $s$ of a finite order is the union of the sets $\operatorname{Iic} a$ for the maximal elements $a$ of $s$. If $s$ is sup-irreducible, then $s$ is not empty, since $\emptyset$ is the minimum. If $s$ has two distinct maximal elements $a$ and $b$, then $s$ is the union of $\operatorname{Iic} a$ and of the lower set generated by the other maximal elements, and neither part equals $s$, so $s$ is reducible. Hence $s$ has one maximal element $a$, and $s = \operatorname{Iic} a$. $\square$

So the map $a \mapsto \operatorname{Iic} a$ is an order embedding `OrderEmbedding.supIrredLowerSet` of $\alpha$ into the sup-irreducible lower sets, it is surjective for a finite order (`OrderEmbedding.supIrredLowerSet_surjective`), and `OrderIso.supIrredLowerSet` is the resulting isomorphism. This is the first half of the representation: a finite partial order is the order of the sup-irreducible elements of its lattice of lower sets. The dual statements for upper sets and inf-irreducible elements are `UpperSet.infIrred_iff_of_finite` and `OrderIso.infIrredUpperSet`. The second half goes from the lattice to the order.

$$\alpha \simeq_o \operatorname{LowerSet} \{a : \alpha \mid \operatorname{SupIrred} a\} \qquad (\texttt{OrderIso.lowerSetSupIrred}),$$

for a finite distributive lattice $\alpha$ with $\bot$.

*Proof sketch.* The map sends $a$ to the set of the sup-irreducible elements below $a$, which is a lower set. In the other direction a lower set $s$ goes to the supremum of its elements. Each element of a finite lattice is the supremum of the sup-irreducible elements below it, so the composite on $\alpha$ is the identity. For the other composite, the key fact is that in a distributive lattice a sup-irreducible element is sup-prime: if $p \le \bigsqcup_i b_i$, then $p = \bigsqcup_i (p \sqcap b_i)$, so $p = p \sqcap b_i$ for some $i$, that is $p \le b_i$. Hence a sup-irreducible element below the supremum of $s$ is below an element of $s$, and it is in $s$ because $s$ is a lower set. Both maps are monotone. $\square$

The embeddings `OrderEmbedding.birkhoffSet` and `OrderEmbedding.birkhoffFinset` compose this isomorphism with the inclusion of lower sets into all sets or finite sets, and they turn $\sqcup$ into union and $\sqcap$ into intersection (`OrderEmbedding.birkhoffSet_sup`, `OrderEmbedding.birkhoffSet_inf`). The bundled forms are `LatticeHom.birkhoffSet` and `LatticeHom.birkhoffFinset`, with `LatticeHom.birkhoffFinset_injective`. These definitions need `DecidablePred SupIrred` and a `Fintype` instance. The lemma `exists_birkhoff_representation` hides these hypotheses.

$$\alpha \text{ finite distributive} \implies \exists \beta \text{ finite},\ \exists f : \alpha \to \operatorname{Finset} \beta \text{ an injective lattice homomorphism}.$$

*Proof.* Take $\beta$ the type of the sup-irreducible elements and $f$ = `LatticeHom.birkhoffFinset`, after the choice of the classical decidability instances. $\square$

#### Common errors

1. A Boolean subalgebra of a complete Boolean algebra is closed under finite suprema only. The lemma `BooleanSubalgebra.sSup_mem` needs the hypothesis that the set is finite, and a Boolean subalgebra is in general not a complete sublattice.
2. The order on `Booleanisation α` is not the order on the sum type `α ⊕ α`. The instances are special to `Booleanisation`, and the simp lemmas apply only to terms written with `Booleanisation.lift` and `Booleanisation.comp`, not with the constructors of the sum type.
3. The Birkhoff embeddings contain decidability instances, and two forms of the same statement with different instances do not unify. Prefer `exists_birkhoff_representation` when only the existence of a representation matters.

### Exercises

1. (A) Prove that the finite and cofinite subsets of $\mathbb{N}$ form a Boolean subalgebra of `Set ℕ`, and that it is not closed under countable unions.
2. (A) Compute $\operatorname{comp} a \sqcap \operatorname{lift} b$ and $\operatorname{comp} a \setminus \operatorname{comp} b$ in `Booleanisation α`, and check each answer with a law of Boolean algebras.
3. (B) Prove that the preimage of a Boolean subalgebra under a bounded lattice homomorphism is closed under complement, with the uniqueness of complements in a distributive lattice.
4. (B) Find the sup-irreducible elements of the lattice of the divisors of $12$, and describe the isomorphism `OrderIso.lowerSetSupIrred` for it.
5. (B) Show that the lattice $M_3$ has three sup-irreducible elements, and that the map that sends $a$ to the set of the sup-irreducible elements below $a$ is injective and monotone but does not preserve $\sqcup$. Which hypothesis of the theorem fails?
6. (C) Prove that the Boolean subalgebra generated by a finite set of $n$ elements of a Boolean algebra has at most $2^{2^n}$ elements.

### Reference

<?reference?>
