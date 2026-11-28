---
title: Free groups and reduced words
kind: api
modules:
  - Mathlib.GroupTheory.FreeGroup.Basic
  - Mathlib.GroupTheory.FreeGroup.Reduce
  - Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
  - Mathlib.GroupTheory.FreeGroup.Center
  - Mathlib.GroupTheory.FreeGroup.GeneratorEquiv
  - Mathlib.GroupTheory.FreeGroup.Orbit
explains:
  E2: [FreeGroup.lift, FreeGroup.Red.church_rosser, FreeGroup.reduce.min, FreeGroup.toWord_injective, FreeGroup.norm_mul_le, FreeGroup.centralizer_of, FreeGroup.isMulCommutative_iff_subsingleton, Equiv.ofFreeGroupEquiv]
  E1: auto
families: []
requires: [V01, V05.C01, V05.C02, V05.C03, V05.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Free groups and reduced words

### Overview

The free group on a type $\alpha$ is the group of words in the letters $a$ and $a^{-1}$ for $a \in \alpha$, where two words are equal when one comes from the other by insertion and deletion of pairs $a a^{-1}$ and $a^{-1} a$. It has the universal property of a free object: each map from $\alpha$ to a group $G$ extends to exactly one homomorphism $F(\alpha) \to G$. Section 1 of this chapter gives the free product of groups, and the free group on $\iota$ is the free product of $\iota$ copies of $\mathbb{Z}$. This section gives the direct construction of the free group and its library.

The six modules split the work as follows. `Mathlib.GroupTheory.FreeGroup.Basic` defines the free group as a quotient of lists by the reduction relation, proves the confluence of reduction, and gives the universal property. `Mathlib.GroupTheory.FreeGroup.Reduce` computes the reduced word of an element, so that equality in the free group becomes decidable, and defines the length of an element. `Mathlib.GroupTheory.FreeGroup.CyclicallyReduced` handles words whose first and last letters do not cancel, which is the tool for powers. `Mathlib.GroupTheory.FreeGroup.Center` computes centers and centralizers. `Mathlib.GroupTheory.FreeGroup.GeneratorEquiv` recovers the generating type from the group, and `Mathlib.GroupTheory.FreeGroup.Orbit` studies the sets of elements that start with a given letter, for ping-pong arguments with actions as in Chapter 6.

### The library around it

#### Words and reduction

A letter is a pair $(a, b)$ in `α × Bool`. The pair $(a, \mathrm{true})$ stands for $a$ and the pair $(a, \mathrm{false})$ stands for $a^{-1}$. A word is a list of letters. The one-step relation `FreeGroup.Red.Step L₁ L₂` says that $L_2$ comes from $L_1$ by the deletion of one adjacent pair $(a, b)(a, \lnot b)$. Its constructor `FreeGroup.Red.Step.not` states this for a pair in the middle of a word, and `FreeGroup.Red.Step.cons_not` for a pair at the front. The relation `FreeGroup.Red` is the reflexive transitive closure of the step relation, with `FreeGroup.Red.refl` and `FreeGroup.Red.trans`. A step removes two letters (`FreeGroup.Red.Step.length`), so a reduction makes a word shorter (`FreeGroup.Red.length_le`), and the result is a sublist of the start (`FreeGroup.Red.sublist`). Reduction is antisymmetric: `FreeGroup.Red.antisymm` says that $L_1 \to L_2$ and $L_2 \to L_1$ give $L_1 = L_2$.

**Confluence.** If $L_1$ reduces to $L_2$ and to $L_3$, then $L_2$ and $L_3$ reduce to a common word. This is `FreeGroup.Red.church_rosser`, with the conclusion `Relation.Join FreeGroup.Red L₂ L₃`.

*Proof sketch.* The key case is one step on each side. Two deletions in one word either remove the same pair, or remove disjoint pairs, or remove overlapping pairs $a a^{-1} a$. In the first case the results agree. In the second case each deletion can still be done after the other. In the third case the two results are equal, because deleting $a a^{-1}$ or $a^{-1} a$ from $a a^{-1} a$ leaves $a$ in both cases. This is the diamond lemma `FreeGroup.Red.Step.diamond`. An induction on the length of the two reductions then gives the full statement. $\square$

The type `FreeGroup α` is the quotient of words by the step relation, and `FreeGroup.mk` is the quotient map. By confluence, `FreeGroup.Red.exact` says that $\mathrm{mk}\,L_1 = \mathrm{mk}\,L_2$ exactly when $L_1$ and $L_2$ reduce to a common word. The group laws come from words: `FreeGroup.mul_mk` says that the product is concatenation, `FreeGroup.one_eq_mk` says that $1$ is the empty word, and `FreeGroup.inv_mk` says that the inverse reverses the word and flips each boolean. The function on words is `FreeGroup.invRev`, an involution (`FreeGroup.invRev_involutive`) that reverses concatenation (`FreeGroup.invRev_append`).

A word is reduced when no step applies to it. The predicate is `FreeGroup.IsReduced`, with `FreeGroup.isReduced_iff_not_step`. The lemma `FreeGroup.isReduced_cons_cons` checks it on the first two letters, and `FreeGroup.IsReduced.infix` says that a subword of a reduced word is reduced. A reduced word reduces only to itself (`FreeGroup.IsReduced.red_iff_eq`).

#### The universal property

The generator map is `FreeGroup.of`, with `FreeGroup.mk_eq_of` for its word $[(a, \mathrm{true})]$. It is injective (`FreeGroup.of_injective`).

**Universal property.** For a group $G$, the equivalence `FreeGroup.lift` sends a map $f : \alpha \to G$ to the homomorphism $F(\alpha) \to G$ with $\mathrm{of}\,a \mapsto f(a)$. Its inverse sends a homomorphism $g$ to $g \circ \mathrm{of}$ (`FreeGroup.lift_symm_apply`).

*Proof sketch.* On words, send the letter $(a, \mathrm{true})$ to $f(a)$ and $(a, \mathrm{false})$ to $f(a)^{-1}$, and take the product. This is `FreeGroup.Lift.aux`. A step deletes $f(a)f(a)^{-1}$ or $f(a)^{-1}f(a)$, so the product does not change (`FreeGroup.Red.Step.lift`), and the map goes down to the quotient. It is a homomorphism because the product of a concatenation is the product of the products. Uniqueness holds because the elements $\mathrm{of}\,a$ generate the group (`FreeGroup.closure_range_of`). $\square$

The computation rule is `FreeGroup.lift_apply_of`, and `FreeGroup.lift_mk` gives the value on a word. Uniqueness has two forms: `FreeGroup.lift_unique` for one homomorphism, and the extensionality lemma `FreeGroup.ext_hom`, which reduces an equality of homomorphisms out of `FreeGroup α` to their values on generators. The range of a lift is the subgroup generated by the image (`FreeGroup.range_lift_eq_closure`), so `FreeGroup.lift_surjective_iff_closure_range_eq_top` says that the lift is surjective exactly when the image of $f$ generates. Each subgroup is the range of a lift, by `FreeGroup.closure_eq_range`. The induction principle `FreeGroup.induction_on` proves a statement for all elements from the cases $1$, $\mathrm{of}\,a$, $(\mathrm{of}\,a)^{-1}$ and products.

The functor part is `FreeGroup.map`, with `FreeGroup.map.of` and `FreeGroup.map_eq_lift`. It keeps injectivity, surjectivity and bijectivity (`FreeGroup.map_injective`, `FreeGroup.map_surjective`, `FreeGroup.map_bijective`). An equivalence of types gives an isomorphism of free groups, `FreeGroup.freeGroupCongr`. The evaluation `FreeGroup.prod : FreeGroup G →* G` is the lift of the identity for a group $G$, and `FreeGroup.lift_eq_prod_map` factors each lift as $\mathrm{prod} \circ \mathrm{map}\,f$. The additive form is `FreeAddGroup`, and `FreeGroup.freeGroupEquivMultiplicative` connects the two.

Small cases have names. The free group on an empty type is trivial (`FreeGroup.instUniqueOfIsEmpty`). The free group on one generator is $\mathbb{Z}$: `FreeGroup.mulEquivIntOfUnique` is the isomorphism with `Multiplicative ℤ`, and `FreeGroup.freeGroupUnitEquivInt` is the bijection with $\mathbb{Z}$ for the one-point type.

#### Reduced words and the length

With decidable equality on $\alpha$, the function `FreeGroup.reduce` computes the reduced form of a word. It goes through the word from the right and deletes a letter that cancels with the head of the reduced rest. The lemmas `FreeGroup.reduce.red` and `FreeGroup.isReduced_iff_reduce_eq` say that the result is a reduction of the word and that it is reduced.

**Minimality.** If $\mathrm{reduce}\,L_1$ reduces to $L_2$, then $L_2 = \mathrm{reduce}\,L_1$. This is `FreeGroup.reduce.min`.

*Proof.* The word $\mathrm{reduce}\,L_1$ has no adjacent pair $(a, b)(a, \lnot b)$, so no step applies to it, and a reduction from it has length zero. $\square$

With confluence, minimality gives the normal form theorem. If $\mathrm{mk}\,L_1 = \mathrm{mk}\,L_2$, then both words reduce to a common word $L$, and $L$ reduces further to its reduced form, so $\mathrm{reduce}\,L_1 = \mathrm{reduce}\,L = \mathrm{reduce}\,L_2$. This is `FreeGroup.reduce.sound`, and `FreeGroup.reduce.exact` is the converse. The function `FreeGroup.toWord` sends an element to its reduced word, with `FreeGroup.toWord_mk`. It is injective (`FreeGroup.toWord_injective`), and `FreeGroup.mk_toWord` recovers the element. So the instance `FreeGroup.instDecidableEq` decides equality in the free group. The relation `FreeGroup.Red` is decidable too (`FreeGroup.Red.decidableRel`), because `FreeGroup.Red.enum` lists all reductions of a word among its sublists.

The table gives the reduced words of the basic elements.

| Lean name | Statement |
|---|---|
| `FreeGroup.toWord_one` | the word of $1$ is empty |
| `FreeGroup.toWord_of` | the word of $\mathrm{of}\,a$ is $[(a, \mathrm{true})]$ |
| `FreeGroup.toWord_inv` | the word of $x^{-1}$ is the inverted word of $x$ |
| `FreeGroup.toWord_mul` | the word of $xy$ is $\mathrm{reduce}(w(x) \mathbin{+\!\!+} w(y))$ |
| `FreeGroup.toWord_of_zpow` | the word of $(\mathrm{of}\,a)^n$ is $|n|$ copies of one letter |
| `FreeGroup.toWord_eq_nil_iff` | the word of $x$ is empty exactly when $x = 1$ |

The length of an element is the length of its reduced word, `FreeGroup.norm`. It is zero exactly at $1$ (`FreeGroup.norm_eq_zero`), it does not change under inversion (`FreeGroup.norm_inv_eq`), and `FreeGroup.norm_of_zpow` gives $\lVert (\mathrm{of}\,a)^n \rVert = |n|$.

**Subadditivity.** $\lVert xy \rVert \le \lVert x \rVert + \lVert y \rVert$. This is `FreeGroup.norm_mul_le`.

*Proof.* The word of $xy$ is the reduced form of the concatenation of the words of $x$ and $y$, and a reduction makes a word shorter. $\square$

The reduced words also give structure. A nonempty $\alpha$ gives a nontrivial group (`FreeGroup.instNontrivialOfNonempty`), and `FreeGroup.of_ne_one` says that no generator is $1$.

#### Cyclically reduced words and roots

A word is cyclically reduced when it is reduced and its last letter does not cancel with its first letter. The predicate is `FreeGroup.IsCyclicallyReduced`, with the criterion `FreeGroup.isCyclicallyReduced_iff`. A power of a cyclically reduced word needs no reduction: `FreeGroup.IsCyclicallyReduced.flatten_replicate` says that the $n$-fold concatenation is cyclically reduced.

Each reduced word $L$ has the form $c\,M\,c^{-1}$ with $M$ cyclically reduced. The function `FreeGroup.reduceCyclically` computes $M$, and `FreeGroup.reduceCyclically.conjugator` computes $c$. The lemma `FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically` states $L = c\,M\,c^{-1}$ as an equality of lists, and `FreeGroup.reduceCyclically.isCyclicallyReduced` states that $M$ is cyclically reduced. Then `FreeGroup.reduceCyclically.reduce_flatten_replicate` gives the reduced word of a power: for $n \ne 0$ it is $c\,M^n\,c^{-1}$. So the length of $x^n$ grows linearly in $n$, and the word of $x^n$ determines the word of $x$. This gives the instance `FreeGroup.instHasUniqueRoots`: in a free group, $x^n = y^n$ with $n \ne 0$ gives $x = y$.

#### Centers and centralizers

The module `Mathlib.GroupTheory.FreeGroup.Center` describes the elements that commute with a given element.

**The centralizer of a generator.** In `FreeGroup α`, the centralizer of $\mathrm{of}\,a$ is the cyclic subgroup that $\mathrm{of}\,a$ generates. This is `FreeGroup.centralizer_of`, and `FreeGroup.commute_of_iff` is the form for one element.

*Proof sketch.* Let $x$ commute with $\mathrm{of}\,a$. If the reduced word of $x$ has a letter $b$ with $b \ne a$, look at the first such letter in $(\mathrm{of}\,a)\,x$ and in $x\,(\mathrm{of}\,a)$. The lemmas `FreeGroup.idxOf_toWord_of_mul_eq` and `FreeGroup.idxOf_toWord_mul_of_eq` show that its position differs by one in the two words. So the words differ, and this contradicts the equality. So $x$ has only the letters $a^{\pm 1}$, and `FreeGroup.mem_zpowers_of_iff` says that $x$ is a power of $\mathrm{of}\,a$. $\square$

**Commutativity.** The free group on $\alpha$ is commutative exactly when $\alpha$ has at most one element. This is `FreeGroup.isMulCommutative_iff_subsingleton`, and `FreeGroup.isCyclic_iff_subsingleton` is the same for cyclicity.

*Proof.* If $\alpha$ has at most one element, the group is trivial or $\mathbb{Z}$. If $a \ne b$ in $\alpha$, then $\mathrm{of}\,b$ is not in the centralizer of $\mathrm{of}\,a$, by `FreeGroup.centralizer_of` and the reduced words. $\square$

So the center is trivial when $\alpha$ has two elements (`FreeGroup.center_eq_bot_of_nontrivial`). The same results hold for each group with a free basis, in the namespace `IsFreeGroup`: `IsFreeGroup.center_eq_bot_or_top`, `IsFreeGroup.isCyclic_centralizer` (the centralizer of $g \ne 1$ is cyclic), and `IsFreeGroup.commute_iff_exists_zpow` (two elements commute exactly when they are powers of one element). The lemma `IsFreeGroup.commute_trans` says that commutation is transitive on elements different from $1$. The predicate `IsFreeGroup` is the subject of Section 3.

#### The generating type and orbits

An isomorphism of free groups gives a bijection of the generating types: `Equiv.ofFreeGroupEquiv` turns $F(\alpha) \cong F(\beta)$ into $\alpha \simeq \beta$.

*Proof sketch.* An isomorphism of groups gives an isomorphism of their abelianizations, `MulEquiv.abelianizationCongr`. The abelianization of $F(\alpha)$ is the free commutative group `FreeCommGroup α`, and its additive form is a free $\mathbb{Z}$-module with basis $\alpha$ (`FreeAddCommGroup.basis`). So the isomorphism carries a basis indexed by $\alpha$ to a second basis of the free module on $\beta$. Over $\mathbb{Z}$ two bases of one module have index types in bijection, by `Module.Basis.indexEquiv`. $\square$

The same module has the forms for free commutative groups, `Equiv.ofFreeCommGroupEquiv` and `Equiv.ofFreeAddCommGroupEquiv`, and the basis `FreeAddCommGroup.basis` of the free abelian group. Chapter 11 treats these groups.

The module `Mathlib.GroupTheory.FreeGroup.Orbit` defines, for a letter $w$, the set `FreeGroup.startsWith w` of elements whose reduced word starts with $w$. These sets do not contain $1$ (`FreeGroup.startsWith.ne_one`), and two of them are disjoint exactly when the letters differ (`FreeGroup.startsWith.disjoint_iff_ne`). The lemma `FreeGroup.startsWith_mk_mul` says that left multiplication by $w$ sends each element that does not start with $w^{-1}$ into the set of $w$. For an action of `FreeGroup α` on a set $X$, the main result `FreeGroup.Orbit.duplicate` uses this fact: the image under $w^{-1}$ of the orbit of $x$ under the set of $w$ is the union of $\{x\}$ and the orbits of $x$ under the sets of all letters $v \ne w^{-1}$.

#### Common errors

1. A letter is a pair `(a, b)` with a boolean, and `(a, false)` is the inverse of the generator $a$. Two lists that are different can give the same element: `FreeGroup.mk [(a, true), (a, false)]` is `1`. Use `FreeGroup.toWord` to get the unique reduced word, and remember that it needs decidable equality on $\alpha$.
2. `FreeGroup.lift` is an equivalence, not a function. Write `FreeGroup.lift f` for the homomorphism, and `FreeGroup.lift.symm g` for the map on generators.
3. `FreeGroup.norm` is the length of the reduced word, not the word metric of a generating set of another group. The lemma `FreeGroup.norm_mk_le` gives only an upper bound for a word that is not reduced.

### Exercises

1. (A) Use `FreeGroup.toWord_mul` and `FreeGroup.toWord_of` to compute the reduced word of $(\mathrm{of}\,a)(\mathrm{of}\,b)(\mathrm{of}\,a)^{-1}$ for $a \ne b$, and deduce that this element is not $\mathrm{of}\,b$.
2. (A) Prove that `FreeGroup.map f` is injective when $f$ is injective, with a left inverse of $f$ on its range.
3. (B) Show that each element $x \ne 1$ of a free group has infinite order, with `FreeGroup.reduceCyclically.reduce_flatten_replicate`.
4. (B) Prove that $\lVert x^{-1} y x \rVert$ and $\lVert y \rVert$ have the same parity for all $x$ and $y$ in `FreeGroup α`.
5. (B) Show that the free group on two generators has trivial center, and that the centralizer of $(\mathrm{of}\,a)(\mathrm{of}\,b)$ is the cyclic group that it generates.
6. (C) Prove `FreeGroup.Red.church_rosser` from the diamond lemma `FreeGroup.Red.Step.diamond` by induction on the two reductions.

### Reference

<?reference?>
