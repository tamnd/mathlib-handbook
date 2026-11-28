---
title: Substructures of the opposite monoid
kind: api
modules:
  - Mathlib.Algebra.Group.Subsemigroup.MulOpposite
  - Mathlib.Algebra.Group.Submonoid.MulOpposite
  - Mathlib.Algebra.Group.Subgroup.MulOpposite
  - Mathlib.Algebra.Group.Subgroup.MulOppositeLemmas
explains:
  E2: [Subgroup.op, Subgroup.opEquiv, Subgroup.op_closure, Subgroup.normal_op, Subgroup.op_normalizer, Submonoid.mulEquivOpMop, Subgroup.smul_opposite_mul]
  E1: auto
families: []
requires: [V05.C01, V05.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Substructures of the opposite monoid

### Overview

The opposite monoid $M^{\mathrm{op}}$ has the same elements as $M$ and the reversed product $a \cdot_{\mathrm{op}} b = b a$. In Mathlib it is the type `MulOpposite M`, with the maps `MulOpposite.op` from $M$ to $M^{\mathrm{op}}$ and `MulOpposite.unop` back, and the rule `MulOpposite.op_mul` states $\mathrm{op}(x y) = \mathrm{op}(y)\,\mathrm{op}(x)$. A subset of $M$ is closed under the product of $M$ exactly when its image is closed under the reversed product. So each subsemigroup, submonoid or subgroup of $M$ has a twin in $M^{\mathrm{op}}$.

The four modules of this section build this twin and prove that it respects every operation on substructures. The correspondence is an order isomorphism, so it moves the closure, the meets and the joins, the bottom and the top. For subgroups it also keeps normality and the normalizer. A reader meets these results in two places. The first is the theory of right actions: the right multiplication of $G$ on itself is a left action of $G^{\mathrm{op}}$, and the library defines the left cosets of $H$ as the orbits of the subgroup $H^{\mathrm{op}}$. The second is the transfer of a result about left objects to right objects: a lemma for $M^{\mathrm{op}}$ gives the mirror lemma for $M$.

### The library around it

#### The construction and the order isomorphism

The definitions `Subsemigroup.op`, `Submonoid.op` and `Subgroup.op` send a substructure $S$ of $M$ to its preimage under `MulOpposite.unop`. So the carrier is $\{x \in M^{\mathrm{op}} \mid \mathrm{unop}(x) \in S\}$; this is `Subgroup.coe_op`, and the membership lemma `Subgroup.mem_op` states $x \in S^{\mathrm{op}}$ if and only if $\mathrm{unop}(x) \in S$. In the other direction, `Subsemigroup.unop`, `Submonoid.unop` and `Subgroup.unop` send a substructure of $M^{\mathrm{op}}$ back to $M$, with `Subgroup.mem_unop` and `Subgroup.coe_unop`. The two maps are inverse to each other by `Subgroup.op_unop` and `Subgroup.unop_op`, which hold by definition.

**Theorem.** The map $S \mapsto S^{\mathrm{op}}$ is an order isomorphism from the subgroups of $G$ to the subgroups of $G^{\mathrm{op}}$.

*Proof.* The set of $S^{\mathrm{op}}$ is closed under the product of $G^{\mathrm{op}}$: for $\mathrm{op}(a), \mathrm{op}(b)$ with $a, b \in S$, the product is $\mathrm{op}(b a)$, and $b a \in S$. It holds $1$ and inverses because $\mathrm{op}$ respects them. The map `Subgroup.unop` is an inverse with the same closure argument, and both maps keep inclusion because they are preimages. $\square$

The Lean name of the isomorphism is `Subgroup.opEquiv`, an order isomorphism from `Subgroup G` to `Subgroup (MulOpposite G)`, and `Submonoid.opEquiv` and `Subsemigroup.opEquiv` are the forms for the other two structures. Its order lemmas come in a fixed family with the same names in the three namespaces:

| Lean name | Statement |
|---|---|
| `Subgroup.op_le_op_iff` | $S_1^{\mathrm{op}} \le S_2^{\mathrm{op}} \iff S_1 \le S_2$ |
| `Subgroup.le_op_iff` | $S_1 \le S_2^{\mathrm{op}} \iff S_1^{\mathrm{unop}} \le S_2$ |
| `Subgroup.op_le_iff` | $S_1^{\mathrm{op}} \le S_2 \iff S_1 \le S_2^{\mathrm{unop}}$ |
| `Subgroup.op_inj` | $S_1^{\mathrm{op}} = S_2^{\mathrm{op}} \iff S_1 = S_2$ |
| `Subgroup.op_injective` | the map `Subgroup.op` is injective |
| `Subgroup.unop_le_unop_iff` | the same statement for the map back |

The forms `Subgroup.le_op_iff` and `Subgroup.op_le_iff` are adjunctions: they move op from one side of an inequality to the other as unop. They are the tool for proofs that start with a hypothesis in $M$ and a goal in $M^{\mathrm{op}}$.

#### Lattice operations and closures

An order isomorphism of complete lattices keeps all meets and joins. The library states each case as a simp lemma, so simp can push op through a lattice expression. For subgroups the names are `Subgroup.op_bot`, `Subgroup.op_top`, `Subgroup.op_inf`, `Subgroup.op_sup`, `Subgroup.op_sInf`, `Subgroup.op_sSup`, `Subgroup.op_iInf` and `Subgroup.op_iSup`. The namespaces `Submonoid` and `Subsemigroup` have the same family, and a mirror family exists for unop. For subgroups, the lattice lemmas are in `Mathlib.Algebra.Group.Subgroup.MulOppositeLemmas`, because that file imports the lattice of subgroups. The criteria `Subgroup.op_eq_bot` and `Subgroup.op_eq_top` state that $S^{\mathrm{op}}$ is trivial or full exactly when $S$ is.

**Theorem.** For a set $s \subseteq G$, $\langle s \rangle^{\mathrm{op}} = \langle \mathrm{unop}^{-1}(s) \rangle$ in $G^{\mathrm{op}}$.

*Proof.* The set $\mathrm{unop}^{-1}(s)$ is the image of $s$ under op. The map `Subgroup.op` is an order isomorphism, so it sends the smallest subgroup that contains $s$ to the smallest subgroup that contains the image of $s$. $\square$

This is `Subgroup.op_closure`. The inverse form is `Subgroup.unop_closure`, and `Submonoid.op_closure`, `Subsemigroup.op_closure` are the forms for the smaller structures. The forgetful maps commute with op: `Subgroup.op_toSubmonoid`, `Subgroup.op_toSubsemigroup`, `Submonoid.op_toSubsemigroup` and the unop forms. So a statement about the submonoid of a subgroup can move to the opposite side without a new proof.

#### The elements of the opposite substructure

A substructure $S$ and its opposite $S^{\mathrm{op}}$ have the same elements up to op. The equivalence of types `Subgroup.equivOp` sends $x \in S$ to $\mathrm{op}(x) \in S^{\mathrm{op}}$; `Submonoid.equivOp` and `Subsemigroup.equivOp` are the other forms. This equivalence does not respect the product, because the product of $S^{\mathrm{op}}$ is reversed. Two corrected forms exist.

**Theorem.** For a submonoid $S$ of $M$, the map $x \mapsto \mathrm{op}(\mathrm{op}(x))$ is a monoid isomorphism $S \cong (S^{\mathrm{op}})^{\mathrm{op}}$.

*Proof.* The map is a bijection, as a composite of the bijection `Subgroup.equivOp` and the bijection `MulOpposite.op`. For $x, y \in S$, the product $x y$ goes to $\mathrm{op}(x y)$ in $S^{\mathrm{op}}$, and this is $\mathrm{op}(y) \cdot \mathrm{op}(x)$ there. The second op reverses the order again, so the image of $x y$ is the product of the images of $x$ and $y$ in $(S^{\mathrm{op}})^{\mathrm{op}}$. $\square$

The Lean name is `Submonoid.mulEquivOpMop`, a monoid isomorphism from $S$ to the opposite of the subtype of $S^{\mathrm{op}}$, and `Subgroup.mulEquivOpMop` is the form for a subgroup. The other corrected form `Submonoid.mopMulEquivOp` is the isomorphism from the opposite of $S$ to $S^{\mathrm{op}}$: the opposite of the subtype is the subtype of the opposite. In a commutative monoid the product is not reversed, and `Submonoid.mulEquivOp` and `Subgroup.mulEquivOp` are monoid isomorphisms from $S$ to $S^{\mathrm{op}}$ without the extra op. The countability instances `Subgroup.instCountableSubtypeMulOppositeMemOp` and `Subgroup.instEncodableSubtypeMulOppositeMemOp` move along `Subgroup.equivOp`.

#### Normality and normalizers

**Theorem.** A subgroup $H$ of $G$ is normal if and only if $H^{\mathrm{op}}$ is normal in $G^{\mathrm{op}}$.

*Proof.* The conjugate of $\mathrm{op}(h)$ by $\mathrm{op}(g)$ in $G^{\mathrm{op}}$ is $\mathrm{op}(g)\,\mathrm{op}(h)\,\mathrm{op}(g)^{-1} = \mathrm{op}(g^{-1} h g)$. So $H^{\mathrm{op}}$ is stable under all conjugations exactly when $H$ is stable under all conjugations $h \mapsto g^{-1} h g$. As $g$ runs over $G$, so does $g^{-1}$. $\square$

The lemma is `Subgroup.normal_op`, and `Subgroup.normal_unop` is the mirror. The directions are `Subgroup.Normal.op`, `Subgroup.Normal.of_op`, `Subgroup.Normal.unop` and `Subgroup.Normal.of_unop`, and the instances `Subgroup.op.instNormal` and `Subgroup.unop.instNormal` let instance search find the normality of $H^{\mathrm{op}}$. The same computation shows that $g$ normalizes $H$ exactly when $\mathrm{op}(g)$ normalizes $H^{\mathrm{op}}$, which gives `Subgroup.op_normalizer`: $N_G(H)^{\mathrm{op}} = N_{G^{\mathrm{op}}}(H^{\mathrm{op}})$. The inverse form is `Subgroup.unop_normalizer`.

#### The right action of a subgroup

The opposite group $G^{\mathrm{op}}$ acts on $G$ by right multiplication: $\mathrm{op}(a) \cdot g = g a$. The module `Mathlib.Algebra.Group.Subgroup.MulOppositeLemmas` restricts this action to a subgroup with the instance `Subgroup.instSMul`, which gives a scalar action of the subtype of $H^{\mathrm{op}}$ on $G$. So for $h \in H^{\mathrm{op}}$ the element $h \cdot g$ is $g \, \mathrm{unop}(h)$. This right action commutes with left multiplication.

**Theorem.** For $x, g \in G$ and $h \in H^{\mathrm{op}}$, $h \cdot (g x) = g \,(h \cdot x)$.

*Proof.* Both sides equal $g x \,\mathrm{unop}(h)$, by the associativity of the product of $G$. $\square$

This is `Subgroup.smul_opposite_mul`. The library uses this action to define cosets. The relation `QuotientGroup.leftRel H` is the orbit relation of the action of $H^{\mathrm{op}}$ on $G$: two elements $a, b$ are related when $b = a h$ for some $h \in H$, that is, when $a H = b H$. So the left cosets of Chapter 4 are the orbits of a right action, and the results of Chapter 6 on orbits apply to them. A reader who needs the right cosets uses the action of $H$ itself, through `QuotientGroup.rightRel`.

#### Common errors

1. A learner expects `Subgroup.equivOp H` to be a group isomorphism. It is only an equivalence of types, because the product of $H^{\mathrm{op}}$ is reversed. Use `Subgroup.mulEquivOpMop`, or `Subgroup.mulEquivOp` in a commutative group.
2. A learner writes the membership $x \in H^{\mathrm{op}}$ for $x : G$. The subgroup $H^{\mathrm{op}}$ lives in `MulOpposite G`, so the element must be `MulOpposite.op x`; then `Subgroup.mem_op` reduces the goal to $x \in H$.
3. A learner looks for the lattice lemmas of `Subgroup.op` in `Mathlib.Algebra.Group.Subgroup.MulOpposite` and does not find them. For subgroups they are in `Mathlib.Algebra.Group.Subgroup.MulOppositeLemmas`, with the normality results.

### Exercises

1. (A) Prove `Subgroup.op_sup` from the fact that `Subgroup.opEquiv` is an order isomorphism.
2. (A) Let $M$ be a commutative monoid and $S$ a submonoid. Show that the map `Submonoid.mulEquivOp S` is a monoid isomorphism, and explain why the proof fails without commutativity.
3. (B) Use `Subgroup.normal_op` to deduce from the statement "the kernel of a homomorphism is normal" that the kernel of a homomorphism $G^{\mathrm{op}} \to K$ is normal, without a new computation.
4. (B) Prove that the orbits of the action of $H^{\mathrm{op}}$ on $G$ are the left cosets $g H$, and that the map $g \mapsto g^{-1}$ sends them to the right cosets $H g^{-1}$.
5. (C) Prove that $g \mapsto \mathrm{op}(g^{-1})$ is a group isomorphism $G \cong G^{\mathrm{op}}$, and that it sends each subgroup $H$ of $G$ onto $H^{\mathrm{op}}$.

### Reference

<?reference?>
