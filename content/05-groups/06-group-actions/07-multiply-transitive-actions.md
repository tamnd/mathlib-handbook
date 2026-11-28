---
title: Multiply transitive actions and the theorems of Jordan
kind: api
modules:
  - Mathlib.GroupTheory.GroupAction.SubMulAction.OfStabilizer
  - Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup
  - Mathlib.GroupTheory.GroupAction.MultipleTransitivity
  - Mathlib.GroupTheory.GroupAction.MultiplePrimitivity
  - Mathlib.GroupTheory.GroupAction.Jordan
  - Mathlib.GroupTheory.GroupAction.SubMulAction.Combination
explains:
  E2: [MulAction.IsMultiplyPretransitive, SubMulAction.ofStabilizer.isMultiplyPretransitive, MulAction.isPreprimitive_of_is_two_pretransitive, MulAction.IsMultiplyPretransitive.index_of_fixingSubgroup_mul, Equiv.Perm.isMultiplyPretransitive, normalClosure_of_stabilizer_eq_top, Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem, Set.powersetCard.isPretransitive_of_isMultiplyPretransitive]
  E1: auto
families: []
requires: [V01, V05.C03, V05.C04, V05.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Multiply transitive actions and the theorems of Jordan

### Overview

An action of $G$ on $X$ is $n$-transitive when $G$ can send each list of $n$ distinct points to each other list of $n$ distinct points. The symmetric group $S_n$ is $n$-transitive on $\{1, \dots, n\}$, and the alternating group $A_n$ is $(n-2)$-transitive. Few other finite groups are $4$-transitive, so a high degree of transitivity is a strong condition. The main tool is induction on $n$: an action is $(n+1)$-transitive if and only if it is transitive and the stabilizer of a point is $n$-transitive on the other points.

These modules hold the sub-actions of a stabilizer and of a pointwise stabilizer on the complement, the class `MulAction.IsMultiplyPretransitive` and its primitive form `MulAction.IsMultiplyPreprimitive`, the theorems of Jordan on primitive groups that contain a transposition or a $3$-cycle, and the action on subsets of a fixed size. The previous section gives blocks and primitive actions. The fixing subgroup of a set and the alternating group come from other sections of the handbook.

### The library around it

#### Actions on the complement of a point or of a set

For a point $a$, the stabilizer $G_a$ maps the set $X \setminus \{a\}$ to itself. The module on stabilizers packages this as `SubMulAction.ofStabilizer G a`, a `SubMulAction` of `MulAction.stabilizer G a` on $X$. Its carrier is $\{a\}^c$ (`SubMulAction.ofStabilizer_carrier`), and `SubMulAction.mem_ofStabilizer_iff` gives $x \in$ `SubMulAction.ofStabilizer G a` if and only if $x \neq a$. For a finite type, `SubMulAction.nat_card_ofStabilizer_eq` gives the size $|X| - 1$. If $b = g \cdot a$, the map `SubMulAction.ofStabilizer.conjMap` is an equivariant bijection from the action of $G_a$ to the action of $G_b$, along the conjugation by $g$ (`SubMulAction.ofStabilizer.conjMap_bijective`). So the stabilizers of two points in the same orbit act in the same way. The map `SubMulAction.ofStabilizer.snoc` adds $a$ at the end of a list of distinct points of $X \setminus \{a\}$.

For a set $s$, the fixing subgroup `fixingSubgroup G s` fixes each point of $s$, and it maps the complement $s^c$ to itself. This gives `SubMulAction.ofFixingSubgroup G s`, with carrier $s^c$ (`SubMulAction.ofFixingSubgroup_carrier`, `SubMulAction.mem_ofFixingSubgroup_iff`). The fixing subgroup is contained in the stabilizer of the set (`MulAction.fixingSubgroup_le_stabilizer`). The module gives equivariant maps that compare these actions:

1. `SubMulAction.ofFixingSubgroup_of_singleton` identifies the action for $s = \{a\}$ with `SubMulAction.ofStabilizer G a`.
2. `SubMulAction.ofFixingSubgroup_insert_map` and `SubMulAction.fixingSubgroupInsertEquiv` identify the fixing subgroup of $\{a\} \cup s$ in $G$ with the fixing subgroup of $s$ in $G_a$, with their actions.
3. `SubMulAction.map_ofFixingSubgroupUnion` does the same for a union $s \cup t$, in two steps.
4. `SubMulAction.ofFixingSubgroup_of_inclusion` compares the actions for $t \subseteq s$.

Each map comes with a lemma that it is injective or bijective. These identifications let a proof fix the points of a set one at a time.

#### Multiple transitivity

The definition `MulAction.IsMultiplyPretransitive G X n` says that $G$ acts pretransitively on `Fin n ↪ X`, the injective maps from $\{0, \dots, n-1\}$ to $X$, with the action on the values. The lemma `MulAction.isMultiplyPretransitive_iff` unfolds this: for all $x, y$ in `Fin n ↪ X` there is $g$ with $g \cdot x = y$. The first cases are:

| Lean name | Statement |
| --- | --- |
| `MulAction.is_zero_pretransitive` | every action is $0$-transitive |
| `MulAction.is_one_pretransitive_iff` | $1$-transitive is the same as pretransitive |
| `MulAction.is_two_pretransitive_iff` | $2$-transitive means: for $a \neq b$ and $c \neq d$ there is $g$ with $g \cdot a = c$ and $g \cdot b = d$ |
| `MulAction.isPretransitive_of_is_two_pretransitive` | a $2$-transitive action is transitive |
| `MulAction.isMultiplyPretransitive_of_le` | an $n$-transitive action is $m$-transitive for $m \le n \le |X|$ |

The induction step is `SubMulAction.ofStabilizer.isMultiplyPretransitive`: for a transitive action, $G$ is $(n+1)$-transitive on $X$ if and only if $G_a$ is $n$-transitive on $X \setminus \{a\}$. Proof: a list of $n + 1$ distinct points can first be moved so that its last point is $a$, by transitivity. Then the lists that end with $a$ correspond, by `SubMulAction.ofStabilizer.snoc`, to lists of $n$ distinct points of $X \setminus \{a\}$, and an element that maps one such list to another and fixes $a$ is an element of $G_a$. The general form `SubMulAction.ofFixingSubgroup.isMultiplyPretransitive` says that if $G$ is $n$-transitive and $|s| + m = n$, then the fixing subgroup of $s$ is $m$-transitive on $s^c$.

A $2$-transitive action is primitive (`MulAction.isPreprimitive_of_is_two_pretransitive`). Proof: let $B$ be a block with two points $a \neq b$, and suppose that $c \notin B$. By $2$-transitivity there is $g$ with $g \cdot a = a$ and $g \cdot b = c$. Then $a \in g \cdot B \cap B$, so $g \cdot B = B$, and $c = g \cdot b \in B$. This is a contradiction, so $B = X$.

For a finite set $X$ and a set $s$ with $k$ elements, a $k$-transitive group has a fixing subgroup of index $|X|!/(|X| - k)!$. This is `MulAction.IsMultiplyPretransitive.index_of_fixingSubgroup_mul`, in the form $[G : G_{(s)}] \cdot (|X| - k)! = |X|!$, and `MulAction.IsMultiplyPretransitive.index_of_fixingSubgroup_eq` gives the index as $\binom{|X|}{k} \cdot k!$. Proof: by the orbit-stabilizer theorem for the action on `Fin k ↪ X`, the index of the stabilizer of a list is the number of lists of $k$ distinct points, and this stabilizer is the fixing subgroup of its set of values.

The main examples:

1. `Equiv.Perm.isMultiplyPretransitive`: the group `Equiv.Perm X` is $n$-transitive for every $n$. Proof: two injective maps from a finite type extend to a common permutation, which is `Equiv.Perm.exists_smul_eq_embedding`.
2. `alternatingGroup.isMultiplyPretransitive`: the alternating group is $(|X| - 2)$-transitive. Proof idea: if a permutation $\sigma$ maps a list of $|X| - 2$ points as required and is odd, then the transposition of the two points outside the target list, composed with $\sigma$, is even and maps the list in the same way.
3. `IsMultiplyPretransitive.alternatingGroup_le`: conversely, a subgroup of `Equiv.Perm X` that is $(|X| - 2)$-transitive contains the alternating group.
4. `alternatingGroup.isPreprimitive_of_three_le_card`: for $|X| \ge 3$, the alternating group acts primitively, and the instance `Equiv.Perm.instIsPreprimitive` gives the same for the full permutation group.

The lemma `normalClosure_of_stabilizer_eq_top` says that if $|X| > 2$ and $G$ is $2$-transitive, then the normal closure of a point stabilizer is $G$. Proof: the normal closure $N$ of $G_a$ contains all the stabilizers $G_x$, since they are conjugate. Take $g \in G$ and $b \neq a, g \cdot a$ (this uses $|X| > 2$). Then $G_b \le N$ acts transitively on $X \setminus \{b\}$, so some $h \in G_b$ has $h \cdot a = g \cdot a$. Then $h^{-1} g \in G_a$, so $g \in N$.

The module also gives the transfer of multiple transitivity along equivariant maps (`MulAction.IsPretransitive.of_embedding`, `Function.Injective.mulActionHom_embedding`, `MulActionHom.embMap`).

#### Multiple primitivity

The class `MulAction.IsMultiplyPreprimitive G X n` asks for $n$-transitivity and, for every set $s$ with $|s| + 1 = n$, primitivity of the fixing subgroup of $s$ on $s^c$. This is `MulAction.isMultiplyPreprimitive_iff`. So $1$-primitive is primitive (`MulAction.is_one_preprimitive_iff`). The induction step is `MulAction.isMultiplyPreprimitive_succ_iff_ofStabilizer`: for $n \ge 1$, $G$ is $(n+1)$-primitive on $X$ if and only if $G_a$ is $n$-primitive on $X \setminus \{a\}$. By `MulAction.isMultiplyPreprimitive_of_isMultiplyPretransitive_succ`, an $(n+1)$-transitive action is $n$-primitive, which generalizes the result that $2$-transitive implies primitive.

#### The theorems of Jordan

The module of Jordan proves criteria for a primitive group to be large. The technical results are `MulAction.IsPreprimitive.is_two_pretransitive` and `MulAction.IsPreprimitive.is_two_preprimitive`. Let $G$ be primitive on a finite set $X$, and let $s$ be a set with $n + 1$ points, with $n + 2 < |X|$. If the fixing subgroup of $s$ is transitive on $s^c$, then $G$ is $2$-transitive. If it is primitive on $s^c$, then $G$ is $2$-primitive. The theorem `MulAction.IsPreprimitive.isMultiplyPreprimitive` repeats the argument and gives $(n+2)$-primitivity from the primitivity of the fixing subgroup on $s^c$. These statements are given without proof here: the proofs use the blocks of the previous section and an induction on $|s|$.

The applications are about subgroups of `Equiv.Perm X` for finite $X$:

1. `Equiv.Perm.isPretransitive_of_isCycle_mem`: if $G$ contains a cycle $g$, then the fixing subgroup of the complement of the support of $g$ is transitive on the support.
2. `Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem`: a primitive subgroup that contains a transposition is the full permutation group. Proof sketch: the fixing subgroup of the complement of $\{a, b\}$ contains the transposition $(a\ b)$, so it is transitive on $\{a, b\}$. By Jordan, $G$ is $2$-transitive, so $G$ contains all the conjugates of $(a\ b)$, that is, all transpositions. The transpositions generate `Equiv.Perm X`.
3. `Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem`: a primitive subgroup that contains a $3$-cycle contains the alternating group. The proof is the same, with $3$-cycles in place of transpositions.
4. `Equiv.Perm.subgroup_eq_top_of_nontrivial`: if $|X| \le 2$, a nontrivial subgroup is the full group.

#### The action on subsets of a fixed size

The set `Set.powersetCard X n` is the set of finite subsets of $X$ with $n$ elements, as a set of `Finset X`. The module on combinations gives the action of $G$ on it, from the sub-action `Set.powersetCard.subMulAction`, with `Set.powersetCard.coe_smul` for the value of $g \cdot s$. The main maps are:

1. `Set.powersetCard.mulActionHom_singleton`: the equivariant bijection $x \mapsto \{x\}$ from $X$ to the subsets of size $1$ (`Set.powersetCard.mulActionHom_singleton_bijective`).
2. `Set.powersetCard.mulActionHom_compl`: the equivariant bijection $s \mapsto s^c$ from the subsets of size $n$ to the subsets of size $m$, for $m + n = |X|$ (`Set.powersetCard.mulActionHom_compl_bijective`).
3. `Set.powersetCard.mulActionHom_of_embedding`: the surjective equivariant map that sends a list of $n$ distinct points to its set of values (`Set.powersetCard.mulActionHom_of_embedding_surjective`).

The third map gives `Set.powersetCard.isPretransitive_of_isMultiplyPretransitive`: an $n$-transitive group is transitive on the subsets of size $n$. In particular `Set.powersetCard.isPretransitive` holds for `Equiv.Perm X`, and `Set.powersetCard.isPretransitive_alternatingGroup` holds for the alternating group when $|X| \ge 3$. For $0 < n < |X|$ and $|X| \neq 2n$, the actions of the permutation group and of the alternating group on the subsets of size $n$ are primitive (`Set.powersetCard.isPreprimitive_perm`, `Set.powersetCard.isPreprimitive_alternatingGroup`). The condition $|X| \neq 2n$ is necessary: for $|X| = 2n$, the pairs $\{s, s^c\}$ form a block system.

#### Common errors

1. `MulAction.IsMultiplyPretransitive G X n` is true for every $n > |X|$, because `Fin n ↪ X` is then empty. Lemmas that go down from $n$ to $m$, such as `MulAction.isMultiplyPretransitive_of_le`, need the hypothesis $n \le |X|$.
2. `SubMulAction.ofStabilizer G a` is a sub-action of the stabilizer, not of $G$. Its elements are points of $X$ with a proof that they differ from $a$, so a statement about them needs the coercion to $X$, as in `SubMulAction.mem_ofStabilizer_iff`.
3. The cardinality conditions in this section mix `Nat.card`, `ENat.card`, `Set.ncard` and `Set.encard`. For example `MulAction.isMultiplyPreprimitive_iff` uses `Set.encard`, while `MulAction.IsPreprimitive.is_two_pretransitive` uses `Set.ncard` and `Nat.card`. Check which one a lemma expects before a rewrite.

### Exercises

1. (A) Show that the action of the dihedral group of order $2n$ on the $n$ vertices of a regular polygon is $2$-transitive only for $n \le 3$.
2. (A) Use `MulAction.IsMultiplyPretransitive.index_of_fixingSubgroup_mul` to show that a $3$-transitive group on $6$ points has order divisible by $120$.
3. (B) Show that the action of $A_4$ on $\{1, 2, 3, 4\}$ is $2$-transitive but not $3$-transitive, and compute the stabilizer of a point and its action on the other three points.
4. (B) Let $G$ be $2$-transitive on a finite set $X$ and let $N \neq 1$ be a normal subgroup that acts faithfully. Show that $N$ is transitive on $X$.
5. (B) Show that the action of $S_4$ on the $2$-element subsets of $\{1, 2, 3, 4\}$ is transitive and not primitive, and find a block system.
6. (C) Let $p$ be a prime and let $G$ be a subgroup of $S_p$ that contains a $p$-cycle and a transposition. Show that $G = S_p$. Hint: $G$ is transitive of prime degree, so it is primitive.

### Reference

<?reference?>
