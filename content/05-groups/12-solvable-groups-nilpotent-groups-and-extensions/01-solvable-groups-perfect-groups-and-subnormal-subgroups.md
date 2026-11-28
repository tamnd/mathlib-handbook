---
title: Solvable groups, perfect groups and subnormal subgroups
kind: api
modules:
  - Mathlib.GroupTheory.Solvable
  - Mathlib.GroupTheory.IsPerfect
  - Mathlib.GroupTheory.IsSubnormal
explains:
  E2: [Subgroup.map_derivedSeries_eq, Group.isSolvable_of_isSolvable_injective, Group.isSolvable_iff_subgroup_quotient, Group.isSolvable_of_comm, Equiv.Perm.not_isSolvable_fin_5, Group.IsPerfect.not_isSolvable, Group.subsingleton_abelianization_iff_isPerfect, Subgroup.IsSubnormal.trans, Subgroup.IsSubnormal.normal_of_isSimpleGroup]
  E1: auto
families: []
requires: [V05.C03, V05.C05, V05.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Solvable groups, perfect groups and subnormal subgroups

### Overview

The commutator subgroup $[G, G]$ measures how far a group is from being commutative. Take the commutator subgroup again and again: $G^{(0)} = G$ and $G^{(n+1)} = [G^{(n)}, G^{(n)}]$. This is the derived series. A group is solvable when the derived series reaches the trivial subgroup. A group is perfect when the series does not move at all, that is, when $[G, G] = G$. The two notions are at opposite ends: a nontrivial perfect group is never solvable.

This section describes three modules. `Mathlib.GroupTheory.Solvable` defines the derived series and solvable groups, and proves that solvability passes to subgroups, quotients and extensions, and that the symmetric group on five or more points is not solvable. `Mathlib.GroupTheory.IsPerfect` defines perfect groups. `Mathlib.GroupTheory.IsSubnormal` defines subnormal subgroups, the subgroups that sit at the bottom of a finite chain of subgroups, each normal in the next.

The section uses the commutator subgroup $[H, K]$ and the abelianization from the section on commutators in Chapter 5, the quotient groups of the same chapter, and the symmetric groups of Chapter 7.

### The library around it

#### The derived series

The definition is `Subgroup.derivedSeries G n`, by recursion on $n$. The two equations `Subgroup.derivedSeries_zero` and `Subgroup.derivedSeries_succ` state $G^{(0)} = ⊤$ and $G^{(n+1)} = [G^{(n)}, G^{(n)}]$, and `Subgroup.derivedSeries_one` states $G^{(1)} = $ `commutator G`. Each term is normal (`Subgroup.derivedSeries_normal`) and even characteristic: the instance `Subgroup.derivedSeries_characteristic` gives `Subgroup.Characteristic`. The series decreases, by `Subgroup.derivedSeries_antitone`.

A homomorphism $f : G \to G'$ maps each term into the term with the same index: `Subgroup.map_derivedSeries_le_derivedSeries` states $f(G^{(n)}) \le G'^{(n)}$. When $f$ is surjective, equality holds.

**Proposition** (`Subgroup.map_derivedSeries_eq`). If $f : G \to G'$ is surjective, then $f(G^{(n)}) = G'^{(n)}$ for all $n$.

*Proof.* Induction on $n$. For $n = 0$, $f(G) = G'$ is the surjectivity. The image of a commutator subgroup is the commutator subgroup of the images (`Subgroup.map_commutator`), so $f(G^{(n+1)}) = [f(G^{(n)}), f(G^{(n)})] = [G'^{(n)}, G'^{(n)}] = G'^{(n+1)}$. $\square$

The library also has the inequality in the other direction for a surjection, `Subgroup.derivedSeries_le_map_derivedSeries`. All these names live in the namespace `Subgroup`. Short root names such as `derivedSeries` are deprecated aliases, so write the namespaced form.

#### Solvable groups

The class `Group.IsSolvable G` says that some term of the derived series is trivial. Its only field is `Group.IsSolvable.solvable`, and `Group.isSolvable_def` states the class as $\exists n, G^{(n)} = ⊥$. A trivial group is solvable (`Group.isSolvable_of_top_eq_bot`). A commutative group is solvable: `Group.isSolvable_of_comm` takes the hypothesis $\forall a\, b, ab = ba$, and its proof is one line, because then $[G, G] = ⊥$. Instances give solvability for a group with a `CommGroup` structure or an `IsMulCommutative` instance.

The class passes to the three standard constructions.

| Lean name | Statement |
|---|---|
| `Group.isSolvable_of_isSolvable_injective` | if $f : G \to G'$ is injective and $G'$ is solvable, then $G$ is solvable |
| `Group.isSolvable_of_surjective` | if $f : G \to G'$ is surjective and $G$ is solvable, then $G'$ is solvable |
| `Group.isSolvable_of_ker_le_range` | if $\ker g \le \operatorname{im} f$ for $f : G' \to G$, $g : G \to G''$ and $G'$, $G''$ are solvable, then $G$ is solvable |
| `Group.isSolvable_of_subgroup_quotient` | if $H$ is normal and $H$, $G/H$ are solvable, then $G$ is solvable |
| `Group.isSolvable_iff_subgroup_quotient` | for $H$ normal, $G$ is solvable if and only if $H$ and $G/H$ are solvable |
| `Group.isSolvable_commutator_iff` | $[G, G]$ is solvable if and only if $G$ is solvable |

Instances give the subgroup and quotient cases automatically: each subgroup of a solvable group is solvable, each quotient is solvable, and a product of two solvable groups is solvable.

**Proposition** (`Group.isSolvable_of_isSolvable_injective`). A group that embeds in a solvable group is solvable.

*Proof.* Let $f : G \to G'$ be injective, with $G'^{(n)} = ⊥$. Then $f(G^{(n)}) \le G'^{(n)} = ⊥$. Since $f$ is injective, $G^{(n)} = ⊥$. $\square$

The extension case `Group.isSolvable_of_ker_le_range` has a short proof too. Let $G'^{(m)} = ⊥$ and $G''^{(n)} = ⊥$. The image of $G^{(n)}$ in $G''$ is in $G''^{(n)} = ⊥$, so $G^{(n)} \le \ker g \le f(G')$. Then $G^{(n+m)} \le f(G'^{(m)}) = ⊥$, because the derived series of a subgroup is contained in the derived series of the bigger group. The quotient form is the special case where $f$ is the inclusion of $H$ and $g$ is the quotient map.

Two characterizations look at all subgroups at once. `Group.IsSolvable.commutator_lt_of_ne_bot` says that in a solvable group each nontrivial subgroup $H$ has $[H, H] < H$. Conversely, `Group.isSolvable_iff_commutator_lt` gives the equivalence when the subgroups satisfy `WellFoundedLT`, for example in a finite group. A nontrivial solvable group has a proper commutator subgroup, by `Group.IsSolvable.commutator_lt_top_of_nontrivial`. A simple group is solvable only when it is commutative: this is `IsSimpleGroup.comm_iff_isSolvable`.

#### Symmetric groups are not solvable

The criterion `Group.not_isSolvable_of_mem_derivedSeries` says: if some $g \ne 1$ lies in every term $G^{(n)}$, then $G$ is not solvable. The library applies it to $S_5$.

**Theorem** (`Equiv.Perm.not_isSolvable_fin_5`). The group `Equiv.Perm (Fin 5)` is not solvable.

*Proof sketch.* Let $x$ be the $3$-cycle $(0\,1\,2)$. A direct computation, checked by `decide`, finds permutations $y$ and $z$ with $x = z\,[x, y x y^{-1}]\,z^{-1}$. Now show $x \in G^{(n)}$ by induction on $n$. If $x \in G^{(n)}$, then also $y x y^{-1} \in G^{(n)}$, because the term is normal. So the commutator $[x, y x y^{-1}]$ is in $G^{(n+1)}$, and its conjugate $x$ is in $G^{(n+1)}$ too, because $G^{(n+1)}$ is normal. $\square$

The general form `Equiv.Perm.not_isSolvable` takes a type $X$ with `5 ≤ Cardinal.mk X`. Its proof embeds `Fin 5` in $X$, extends permutations by the identity with `Equiv.Perm.viaEmbeddingHom_injective`, and uses the injective case above. So a solvable group can not contain a copy of $S_5$.

#### Perfect groups

The class `Group.IsPerfect G` has the single field `Group.IsPerfect.commutator_eq_top`: `commutator G = ⊤`. The form `Group.isPerfect_def` is the same statement as an equivalence, and `Group.IsPerfect.mem_commutator` says that each element is in the commutator subgroup. For a subgroup $H$, `Subgroup.isPerfect_iff` turns the class on the coerced type into the equation $[H, H] = H$ in $G$.

**Proposition** (`Group.subsingleton_abelianization_iff_isPerfect`). A group is perfect if and only if its abelianization is trivial.

*Proof.* The abelianization is $G / [G, G]$. A quotient $G/N$ is trivial exactly when $N = G$. $\square$

The class is stable under images: `Group.IsPerfect.ofSurjective` for a surjection, `Group.IsPerfect.range` for the range of any homomorphism and `Group.IsPerfect.map` for the image of a perfect subgroup. Each term of the derived series of a perfect group is the whole group (`Group.IsPerfect.derivedSeries_eq_top`), and so is each term of the lower central series of a perfect subgroup (`Group.IsPerfect.lowerCentralSeries_eq_top`). This gives the negative results in one line each.

**Proposition** (`Group.IsPerfect.not_isSolvable`). A nontrivial perfect group is not solvable.

*Proof.* All terms of the derived series are $⊤$, and $⊤ \ne ⊥$ in a nontrivial group. $\square$

In the same way, a nontrivial perfect group is not nilpotent (`Group.IsPerfect.not_isNilpotent`) and not commutative (`Group.IsPerfect.not_isMulCommutative`), and a commutative perfect group is trivial (`Group.IsPerfect.subsingleton_of_isMulCommutative`). The module also proves the lemma of Grün: the center of $G / Z(G)$ is trivial when $G$ is perfect (`Group.IsPerfect.center_quotient_center_eq_bot`). Its consequence `Group.IsPerfect.upperCentralSeries_eq_center` says that the upper central series of a perfect group stops at the center. The proof of the lemma uses the three subgroups lemma for commutators, and this section does not repeat it.

#### Subnormal subgroups

The predicate `Subgroup.IsSubnormal H` is inductive, with two constructors. `Subgroup.IsSubnormal.top` says that $G$ is subnormal. `Subgroup.IsSubnormal.step` says: if $H \le K$, $K$ is subnormal and $H$ is normal in $K$, then $H$ is subnormal. Normality in $K$ is written `(H.subgroupOf K).Normal`, through the subgroup `Subgroup.subgroupOf` of the type $K$. So $H$ is subnormal exactly when a finite chain
$$H = H_0 \le H_1 \le \dots \le H_n = G$$
has each $H_i$ normal in $H_{i+1}$. The equivalence with chains is `Subgroup.IsSubnormal.isSubnormal_iff`, and `Subgroup.IsSubnormal.exists_chain` gives the chain from the predicate. A one step form is `Subgroup.IsSubnormal.iff_eq_top_or_exists`.

The first examples: a normal subgroup is subnormal (`Subgroup.Normal.isSubnormal`), and so is the trivial subgroup (`Subgroup.IsSubnormal.bot`) and each subsingleton subgroup (`Subgroup.IsSubnormal.of_subsingleton`). The predicate is closed under the usual operations.

| Lean name | Statement |
|---|---|
| `Subgroup.IsSubnormal.inf` | $H$, $K$ subnormal imply $H \cap K$ subnormal |
| `Subgroup.IsSubnormal.comap` | the preimage of a subnormal subgroup is subnormal |
| `Subgroup.IsSubnormal.map` | the image under a surjection is subnormal |
| `Subgroup.IsSubnormal.quotient` | the image in $G/K$ is subnormal |
| `Subgroup.IsSubnormal.subgroupOf` | $H \cap K$ is subnormal in $K$ |
| `Subgroup.IsSubnormal.smul` | the image under an automorphism action is subnormal |

**Proposition** (`Subgroup.IsSubnormal.trans`). If $H \le K$, $H$ is subnormal in $K$ and $K$ is subnormal in $G$, then $H$ is subnormal in $G$.

*Proof.* Join the two chains: a chain from $H$ to $K$ inside $K$, mapped into $G$, followed by the chain from $K$ to $G$. Each step stays normal, because normality of $A$ in $B$ only uses elements of $B$. $\square$

The form `Subgroup.IsSubnormal.trans'` takes $H$ as a subgroup of the type $K$ and maps it into $G$ with the inclusion of $K$. A proper subnormal subgroup lies in a proper normal subgroup: `Subgroup.IsSubnormal.exists_normal_and_le_and_lt_top_of_ne`, the first step of the chain from the top. This gives the next result at once.

**Proposition** (`Subgroup.IsSubnormal.normal_of_isSimpleGroup`). In a simple group, each subnormal subgroup is normal.

*Proof.* If $H = G$, it is normal. Otherwise $H \le K < G$ with $K$ normal. Simplicity gives $K = ⊥$, so $H = ⊥$, which is normal. $\square$

#### Common errors

1. The root names `derivedSeries`, `isSolvable_of_comm`, `IsSolvable` and similar are deprecated aliases. Use `Subgroup.derivedSeries`, `Group.isSolvable_of_comm` and `Group.IsSolvable`.
2. `Subgroup.IsSubnormal` is an inductive predicate. To prove it, apply a constructor or a closure lemma, not `Subgroup.Normal`. Normality inside $K$ is `(H.subgroupOf K).Normal`, a statement about a subgroup of the type $K$, not about $H$ in $G$.
3. `Group.isSolvable_iff_commutator_lt` needs `WellFoundedLT (Subgroup G)`. The infinite cyclic group $\mathbb{Z}$ does not satisfy it, so do not use this equivalence for an arbitrary infinite group.

### Exercises

1. (A) Compute the derived series of $S_3$ and of $S_4$, and show that both groups are solvable.
2. (A) Show that the product of two solvable groups is solvable from `Group.isSolvable_of_ker_le_range`, with the inclusion of the first factor and the projection to the second.
3. (B) Let $G$ be finite and solvable, and let $G \neq 1$. Show that $G$ has a normal subgroup $N$ with $G/N$ cyclic of prime order. Hint: use `Group.IsSolvable.commutator_lt_top_of_nontrivial`.
4. (B) Show that the alternating group $A_5$ is perfect. Deduce from `Group.IsPerfect.not_isSolvable` a second proof that $S_5$ is not solvable.
5. (B) In the dihedral group of order $8$, find a subgroup that is subnormal but not normal, and write a chain of length $2$ for it with `Subgroup.IsSubnormal.step`.
6. (C) Show that a finite group is solvable if and only if it has a chain $1 = H_0 \le H_1 \le \dots \le H_n = G$ with each $H_i$ normal in $H_{i+1}$ and each $H_{i+1}/H_i$ cyclic of prime order.

### Reference

<?reference?>
