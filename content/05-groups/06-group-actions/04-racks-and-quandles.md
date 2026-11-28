---
title: Racks and quandles
kind: api
modules:
  - Mathlib.Algebra.Quandle
explains:
  E2: [Rack.ad_conj, Rack.self_act_act_eq, Rack.assoc_iff_id, UnitalShelf.assoc, Quandle.fix_inv, Rack.involutory_invAct_eq_act, Rack.toEnvelGroup.univ]
  E1: auto
families: []
requires: [V02, V05.C01, V05.C02, V05.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Racks and quandles

### Overview

Conjugation in a group satisfies an identity that does not use the product. Write $x \triangleright y = x y x^{-1}$. Then $x \triangleright (y \triangleright z) = (x \triangleright y) \triangleright (x \triangleright z)$, because conjugation by $x$ is an automorphism. A rack is a set with a binary operation $\triangleright$ that has this self-distributive law, and for which each map $y \mapsto x \triangleright y$ is a bijection. A quandle is a rack with $x \triangleright x = x$. These structures remember the conjugation of a group and forget the rest.

Quandles come from knot theory. The arcs of a knot diagram generate a quandle, and the three axioms of a quandle match the three Reidemeister moves. A colouring of a knot by the dihedral quandle of order $n$ is a Fox $n$-colouring. In algebra, racks give a second view of the action of a group on itself by conjugation of Section 1, and each rack has a universal group, the enveloping group, with a universal property like that of a free group.

The module `Mathlib.Algebra.Quandle` defines shelves, unital shelves, racks and quandles, their homomorphisms, the conjugation quandle of a group, the dihedral quandles, and the enveloping group. The construction of the enveloping group is a quotient of a type of formal words, as in Chapter 5.

### The library around it

#### The four classes

The module has four classes, each an extension of the one before.

1. `Shelf α` has an operation `Shelf.act : α → α → α` and the field `Shelf.self_distrib`: $x \triangleright (y \triangleright z) = (x \triangleright y) \triangleright (x \triangleright z)$.
2. `UnitalShelf α` adds an element $1$ with `UnitalShelf.one_act` and `UnitalShelf.act_one`: $1 \triangleright a = a$ and $a \triangleright 1 = a$.
3. `Rack α` extends `Shelf α` with an inverse operation `Rack.invAct` and the fields `Rack.left_inv` and `Rack.right_inv`: for each $x$, the map $y \mapsto x \triangleright^{-1} y$ is a two-sided inverse of $y \mapsto x \triangleright y$.
4. `Quandle α` extends `Rack α` with the field `Quandle.fix`: $x \triangleright x = x$.

The notation is scoped. After `open scoped Quandles`, the term `x ◃ y` is `Shelf.act x y`, the term `x ◃⁻¹ y` is `Rack.invAct x y`, and `S₁ →◃ S₂` is the type `ShelfHom S₁ S₂`. Both operations are right associative, so `x ◃ y ◃ z` is `x ◃ (y ◃ z)`. This matches the reading of $x \triangleright$ as a map that acts on the left.

A homomorphism of shelves is a map $f$ with $f(x \triangleright y) = f(x) \triangleright f(y)$. The structure `ShelfHom` holds such maps, and it is also the notion of homomorphism of racks and of quandles. It has a coercion to functions by `ShelfHom.instFunLike`, the rule `ShelfHom.map_act`, the identity `ShelfHom.id`, the composition `ShelfHom.comp` with `ShelfHom.comp_apply`, and extensionality `ShelfHom.ext`.

#### Unital shelves are monoids

A unit forces associativity. The lemma `UnitalShelf.act_idem` says $x \triangleright x = x$. Proof: $x \triangleright x = (x \triangleright 1) \triangleright (x \triangleright 1) = x \triangleright (1 \triangleright 1) = x \triangleright 1 = x$, by `UnitalShelf.act_one` and self-distributivity. The two lemmas `UnitalShelf.act_act_self_eq` and `UnitalShelf.act_self_act_eq` say $(x \triangleright y) \triangleright x = x \triangleright y$ and $x \triangleright (x \triangleright y) = x \triangleright y$. From them follows `UnitalShelf.assoc`:
$$(x \triangleright y) \triangleright z = x \triangleright (y \triangleright z).$$
Proof: by self-distributivity twice, $x \triangleright (y \triangleright z) = (x \triangleright y) \triangleright (x \triangleright z) = ((x \triangleright y) \triangleright x) \triangleright ((x \triangleright y) \triangleright z)$. The first lemma turns $(x \triangleright y) \triangleright x$ into $x \triangleright y$, and the second lemma turns $(x \triangleright y) \triangleright ((x \triangleright y) \triangleright z)$ into $(x \triangleright y) \triangleright z$. So a unital shelf is a monoid in which each element is idempotent and $xyx = xy$. Such monoids are graphic monoids. For this reason the library defines no unital racks: the lemma `Rack.assoc_iff_id` says that $x \triangleright (y \triangleright z) = (x \triangleright y) \triangleright z$ holds in a rack if and only if $x \triangleright z = z$. The proof is one line: rewrite the left side by self-distributivity to $(x \triangleright y) \triangleright (x \triangleright z)$, and cancel the bijection $(x \triangleright y) \triangleright$. So an associative rack has a trivial action.

#### The action as a permutation

For $x$ in a rack $R$, the map $y \mapsto x \triangleright y$ is a bijection. The library bundles it as `Rack.act' x : R ≃ R`, with `Rack.act'_apply` and `Rack.act'_symm_apply`. The cancellation rules `Rack.invAct_act_eq` and `Rack.act_invAct_eq` give $x \triangleright^{-1} (x \triangleright y) = y$ and $x \triangleright (x \triangleright^{-1} y) = y$, and `Rack.left_cancel` gives $x \triangleright y = x \triangleright y' \iff y = y'$. The inverse operation is self-distributive too, by `Rack.self_distrib_inv`.

The key identity is `Rack.ad_conj`:
$$\mathrm{act}'(x \triangleright y) = \mathrm{act}'(x) \circ \mathrm{act}'(y) \circ \mathrm{act}'(x)^{-1}$$
in the group `R ≃ R`. Evaluate both sides at $x \triangleright z$: the left side gives $(x \triangleright y) \triangleright (x \triangleright z)$ and the right side gives $x \triangleright (y \triangleright z)$, and these agree by self-distributivity. So self-distributivity says that $x \mapsto \mathrm{act}'(x)$ turns the rack operation into conjugation of permutations. This is `Rack.toConj R`, a rack homomorphism from $R$ to the conjugation quandle of `R ≃ R`.

A rack is close to a quandle. The lemma `Rack.self_act_act_eq` says $(x \triangleright x) \triangleright y = x \triangleright y$. Proof: put $y' = x \triangleright^{-1} y$, so that $y = x \triangleright y'$. Then $(x \triangleright x) \triangleright (x \triangleright y') = x \triangleright (x \triangleright y')$ by self-distributivity, and this is $x \triangleright y$. The lemmas `Rack.self_invAct_invAct_eq`, `Rack.self_act_invAct_eq` and `Rack.self_invAct_act_eq` are the variants with $\triangleright^{-1}$. The map $x \mapsto x \triangleright x$ is a bijection of $R$, `Rack.selfApplyEquiv R`, and `Rack.self_act_eq_iff_eq` says that it is injective. In a quandle this map is the identity, and `Quandle.fix_inv` says that $x \triangleright^{-1} x = x$ too: apply the bijection $x \triangleright$ to both sides and use `Quandle.fix`.

Two properties of racks are definitions. `Rack.IsInvolutory R` says that each map $y \mapsto x \triangleright y$ is an involution, and then `Rack.involutory_invAct_eq_act` gives $x \triangleright^{-1} y = x \triangleright y$, since the inverse of an involution is itself. `Rack.IsAbelian R` is the medial law $(x \triangleright y) \triangleright (z \triangleright w) = (x \triangleright z) \triangleright (y \triangleright w)$.

The opposite of a rack swaps the two operations. The instance `Rack.oppositeRack` puts a rack structure on the type synonym `Rᵐᵒᵖ` of Chapter 1, with `Rack.op_act_op_eq` stating $\mathrm{op}(x) \triangleright \mathrm{op}(y) = \mathrm{op}(x \triangleright^{-1} y)$ and `Rack.op_invAct_op_eq` the reverse rule. The instance `Quandle.oppositeQuandle` does the same for quandles.

#### Examples

The main example is `Quandle.Conj G`, a type synonym for a group $G$. The instance `Quandle.Conj.quandle` makes it a quandle with $x \triangleright y = x y x^{-1}$, and the simp lemma `Quandle.conj_act_eq_conj` unfolds the operation. The action of $x$ is the inner automorphism `MulAut.conj x`. The axiom $x \triangleright x = x x x^{-1} = x$ holds. A group homomorphism $f : G \to H$ gives the quandle homomorphism `Quandle.Conj.map f`, because $f(x y x^{-1}) = f(x) f(y) f(x)^{-1}$. The lemma `Quandle.conj_swap` says that $x \triangleright y = y$ if and only if $y \triangleright x = x$: both say that $x$ and $y$ commute.

The dihedral quandle `Quandle.Dihedral n` is a type synonym for `ZMod n`, with the operation `Quandle.dihedralAct n`: $a \triangleright b = 2a - b$. This is the reflection of $b$ in $a$ on a regular $n$-gon whose vertices are labelled by $\mathbb{Z}/n$. The lemma `Quandle.dihedralAct.inv` says that each map $b \mapsto 2a - b$ is an involution, so the inverse operation is the operation itself. Self-distributivity is a ring identity: $2a - (2b - c) = 2(2a - b) - (2a - c)$. The instance `Quandle.instDihedral` records the structure. The quandle is the set of reflections of the dihedral group of Chapter 1 under conjugation.

#### The enveloping group

Each rack homomorphism $R \to \mathrm{Conj}(G)$ to a group should come from a group. The enveloping group `Rack.EnvelGroup R` is the universal such group. In terms of a presentation it is the group with one generator $e_x$ for each $x \in R$ and the relations $e_x e_y e_x^{-1} = e_{x \triangleright y}$.

The construction does not use free groups. The inductive type `Rack.PreEnvelGroup R` holds formal expressions built from a unit `Rack.PreEnvelGroup.unit`, the generators `Rack.PreEnvelGroup.incl`, products `Rack.PreEnvelGroup.mul` and inverses `Rack.PreEnvelGroup.inv`. The type-valued relation `Rack.PreEnvelGroupRel'` lists the group laws, the congruence rules, and the rack relation `Rack.PreEnvelGroupRel'.act_incl`. Its propositional form `Rack.PreEnvelGroupRel` gives the setoid `Rack.PreEnvelGroup.setoid`, and `Rack.EnvelGroup R` is the quotient. The instance `Rack.instGroupEnvelGroup` makes it a group. The relation is type-valued so that the map out of the quotient can be defined by recursion on derivations.

The map `Rack.toEnvelGroup R : R →◃ Quandle.Conj (EnvelGroup R)` sends $x$ to the class of $e_x$. The universal property is an equivalence of types:

| Lean name | Statement |
|---|---|
| `Rack.toEnvelGroup.map` | `(R →◃ Quandle.Conj G) ≃ (EnvelGroup R →* G)` |
| `Rack.toEnvelGroup.univ` | the composite of `Conj.map (toEnvelGroup.map f)` and `toEnvelGroup R` is $f$ |
| `Rack.toEnvelGroup.univ_uniq` | a homomorphism $g$ with this property is `toEnvelGroup.map f` |
| `Rack.envelAction` | the homomorphism `EnvelGroup R →* R ≃ R` induced by `Rack.toConj R` |
| `Rack.envelAction_prop` | the class of $e_x$ acts on $y$ as $x \triangleright y$ |

The map `Rack.toEnvelGroup.map f` evaluates a formal expression in $G$ with `Rack.toEnvelGroup.mapAux f`, and `Rack.toEnvelGroup.mapAux.well_def` shows that related expressions have equal values. In the language of category theory, `Rack.EnvelGroup` is left adjoint to `Quandle.Conj`. The theorem `Rack.toEnvelGroup.univ` is the statement that each rack homomorphism to a conjugation quandle factors through the enveloping group. The enveloping group acts on the rack by `Rack.envelAction`, so each rack is a set with an action of its enveloping group, in the sense of Section 1.

#### Common errors

1. The notation `◃` is scoped. Without `open scoped Quandles` the term `x ◃ y` does not parse, and the goals show `Shelf.act x y`.
2. `Quandle.Conj G` is a type synonym of $G$. A term of type $G$ elaborates as a term of `Quandle.Conj G`, but the instance search on `G` finds the group structure and on `Quandle.Conj G` the quandle structure. State the type of the variables to choose the operation.
3. The operations are right associative. The term `x ◃ y ◃ z` is $x \triangleright (y \triangleright z)$, not $(x \triangleright y) \triangleright z$, and by `Rack.assoc_iff_id` the two are different in each rack with a nontrivial action.

### Exercises

1. (A) Check by hand that $a \triangleright b = 2a - b$ on $\mathbb{Z}/n$ is self-distributive and that $a \triangleright a = a$.
2. (A) Show that the dihedral quandle `Quandle.Dihedral 3` is the conjugation quandle of the three transpositions of $S_3$: give the bijection and check that it is a quandle homomorphism.
3. (B) Let $R$ be a rack. Show that $\mathrm{act}'(x \triangleright^{-1} y) = \mathrm{act}'(x)^{-1} \circ \mathrm{act}'(y) \circ \mathrm{act}'(x)$ in `R ≃ R`, with `Rack.ad_conj`.
4. (B) Prove that a quandle in which $x \triangleright y = y$ for all $x, y$ is involutory and abelian. Which groups $G$ have this property for `Quandle.Conj G`?
5. (B) Let $R$ be the trivial quandle on a set $X$, with $x \triangleright y = y$. Show that the enveloping group of $R$ is the free abelian group on $X$.
6. (C) Show that the enveloping group of the dihedral quandle `Quandle.Dihedral 3` is infinite, and find a surjection from it onto $S_3$.

### Reference

<?reference?>
