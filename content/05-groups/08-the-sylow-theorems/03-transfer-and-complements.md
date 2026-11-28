---
title: Transfer, normal complements and Z-groups
kind: api
modules:
  - Mathlib.GroupTheory.Transfer
  - Mathlib.GroupTheory.Focal
  - Mathlib.GroupTheory.SchurZassenhaus
  - Mathlib.GroupTheory.SpecificGroups.ZGroup
  - Mathlib.GroupTheory.FixedPointFree
explains:
  E2: [MonoidHom.transfer, MonoidHom.transfer_eq_pow, MonoidHom.transferCenterPow_apply, MonoidHom.ker_transferSylow_isComplement', IsCyclic.normalizer_le_centralizer, Subgroup.commutator_inf_eq_focalSubgroup, Subgroup.exists_right_complement'_of_coprime, IsZGroup.of_squarefree, MonoidHom.FixedPointFree.commutatorMap_injective, MonoidHom.FixedPointFree.coe_eq_inv_of_involutive]
  E1: auto
families: []
requires: [V05.C04, V05.C05, V05.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Transfer, normal complements and Z-groups

### Overview

The Sylow theorems give subgroups of prime power order. A second question asks for quotients: when does a finite group $G$ have a normal subgroup $K$ with $G/K$ isomorphic to a Sylow $p$-subgroup $P$? Such a $K$ is a normal $p$-complement: $K \cap P = 1$ and $K P = G$. The main tool for this question is the transfer, a homomorphism from $G$ to an abelian quotient of a subgroup of finite index. It produces homomorphisms out of $G$ that cannot be seen from the multiplication table of the subgroup alone.

This section describes five modules. `Mathlib.GroupTheory.Transfer` defines the transfer and proves the normal complement theorem of Burnside. `Mathlib.GroupTheory.Focal` proves the focal subgroup theorem, which computes $P \cap [G, G]$. `Mathlib.GroupTheory.SchurZassenhaus` proves that a normal subgroup whose order is coprime to its index has a complement. `Mathlib.GroupTheory.SpecificGroups.ZGroup` studies the groups whose Sylow subgroups are all cyclic. `Mathlib.GroupTheory.FixedPointFree` studies automorphisms with no nontrivial fixed point.

The section uses the index and the transversals of Chapter 4, the quotients of Chapter 5, the actions of Chapter 6 and the Sylow theorems of the two sections before it. The notion of a complement, `Subgroup.IsComplement'`, comes from `Mathlib.GroupTheory.Complement`: `H.IsComplement' K` says that each element of $G$ is $h k$ for a unique pair $(h, k) \in H \times K$.

### The library around it

#### The transfer homomorphism

Let $H \le G$ have finite index $n$, let $A$ be a commutative group and let $\varphi : H \to A$ be a homomorphism. Choose a left transversal $T$, a set of representatives $t_q$ of the cosets $q \in G/H$. For $g \in G$, the set $g T$ is another transversal. For two transversals $S$ and $T$, define the difference
$$d(S, T) = \prod_{q \in G/H} \varphi(s_q^{-1} t_q) \in A,$$
where $s_q$ and $t_q$ are the representatives of $q$. Each factor makes sense because $s_q^{-1} t_q \in H$, and the product needs no order because $A$ is commutative. This is `Subgroup.leftTransversals.diff ϕ S T`. It satisfies the cocycle rules $d(R, S) \, d(S, T) = d(R, T)$ and $d(T, T) = 1$, by `Subgroup.leftTransversals.diff_mul_diff` and `Subgroup.leftTransversals.diff_self`, and it is invariant under left translation, by `Subgroup.leftTransversals.smul_diff_smul`.

The transfer is $V(g) = d(T, g T)$. It does not depend on $T$: for another transversal $S$, the cocycle rules and the invariance give $d(S, g S) = d(S, T) \, d(T, g T) \, d(g T, g S) = d(S, T) \, d(T, g T) \, d(T, S) = d(T, g T)$. It is a homomorphism: $d(T, g g' T) = d(T, g T) \, d(g T, g g' T) = d(T, g T) \, d(T, g' T)$. In Lean the transfer is `MonoidHom.transfer ϕ : G →* A`, for `[H.FiniteIndex]`, and `MonoidHom.transfer_def` states $V(g) = d(T, g T)$ for each transversal $T$.

To compute the transfer, the library chooses a transversal adapted to $g$. The cyclic group $\langle g \rangle$ acts on $G/H$, and each orbit is a cycle $q, g q, \dots, g^{k-1} q$. Taking the representatives $g_0, g g_0, \dots, g^{k-1} g_0$ for one cycle gives `Subgroup.transferTransversal`. With it, the transfer is a product over the orbits:
$$V(g) = \prod_{\text{orbits}} \varphi(g_0^{-1} g^{k} g_0),$$
where $k$ is the length of the orbit and $g_0$ a representative. This is `MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot`. The lengths add up to $n$. So if every conjugate $g_0^{-1} g^k g_0$ that lies in $H$ equals $g^k$, all factors are $\varphi(g^k)$ and $V(g) = \varphi(g^n)$. This is `MonoidHom.transfer_eq_pow`.

A first application takes $H = Z(G)$ and $\varphi$ the identity. A conjugate of a central element is the element itself, so the hypothesis of `MonoidHom.transfer_eq_pow` holds and the transfer is $g \mapsto g^{[G : Z(G)]}$. So if the center has finite index $n$, the map $g \mapsto g^n$ is a homomorphism $G \to Z(G)$. This is `MonoidHom.transferCenterPow G`, with the formula `MonoidHom.transferCenterPow_apply`.

#### The normal complement theorem of Burnside

Let $P$ be a Sylow $p$-subgroup of a finite group $G$ with $N_G(P) \le C_G(P)$. Then $P$ is commutative, since $P \le N_G(P)$, and the transfer of the identity of $P$ is a homomorphism $G \to P$. It is `MonoidHom.transferSylow P hP`. Elements of $P$ that are conjugate in $G$ are equal. Indeed, let $x \in P$ and $y = g^{-1} x g \in P$. Since $P$ is commutative, $P$ and $g^{-1} P g$ both lie in the centralizer $C_G(y)$, and they are Sylow subgroups of it. So $c^{-1} g^{-1} P g c = P$ for some $c \in C_G(y)$. Then $g c \in N_G(P) \le C_G(P)$, and $y = c^{-1} y c = (g c)^{-1} x (g c) = x$. So the hypothesis of `MonoidHom.transfer_eq_pow` holds on $P$, and the transfer is $x \mapsto x^{[G : P]}$ on $P$, by `MonoidHom.transferSylow_eq_pow`. The index $[G : P]$ is prime to $p$, so this power map is a bijection of $P$. Hence the transfer is onto $P$, its kernel $K$ meets $P$ trivially, and $|K| = [G : P]$.

**Theorem (Burnside).** If $N_G(P) \le C_G(P)$, then the kernel of the transfer is a normal complement of $P$.

This is `MonoidHom.ker_transferSylow_isComplement'`, with `MonoidHom.not_dvd_card_ker_transferSylow` for the order of the kernel. The hypothesis holds in a common case.

**Proposition.** Let $p$ be the smallest prime factor of $|G|$, and let a Sylow $p$-subgroup $P$ be cyclic. Then $N_G(P) \le C_G(P)$.

*Proof sketch.* By the N/C theorem of Chapter 3, $N_G(P)/C_G(P)$ embeds in $\operatorname{Aut}(P)$. Since $P$ is commutative, $P \le C_G(P)$, so the order of $N_G(P)/C_G(P)$ divides $[G : P]$ and is prime to $p$. The automorphism group of a cyclic group of order $p^a$ has order $p^{a-1}(p-1)$. So the order of $N_G(P)/C_G(P)$ divides $p - 1$. All prime factors of $|G|$ are at least $p$, so this order is $1$. $\square$

This is `IsCyclic.normalizer_le_centralizer`, and `IsCyclic.isComplement'` gives the normal complement. For example, a group of order $2m$ with $m$ odd has a cyclic Sylow $2$-subgroup of order $2$, so it has a normal subgroup of index $2$. In particular such a group is not simple when $m > 1$.

#### The focal subgroup theorem

For a subgroup $H$, the focal subgroup $H^*$ is the subgroup generated by the commutators $[x, u]$ with $x \in H$ and $[x, u] \in H$, for $u \in G$. It is `Subgroup.focalSubgroup H`, and `Subgroup.focalSubgroupOf H` is the same subgroup as a subgroup of $H$. It lies between the commutator subgroup of $H$ and $H \cap [G, G]$, by `Subgroup.commutator_le_focalSubgroup`, `Subgroup.focalSubgroup_le` and `Subgroup.focalSubgroup_le_commutator`. The quotient $H / H^*$ is commutative, by the instance `Subgroup.instIsMulCommutativeQuotientSubtypeMemFocalSubgroupOf`. So the transfer of the quotient map $H \to H/H^*$ is defined; it is `Subgroup.transferFocal H`, and on $H$ it is the power map $x \mapsto x^{[G : H]}$ modulo $H^*$, by `Subgroup.transferFocal_eq_pow`.

**Theorem (Focal subgroup theorem).** For a Sylow $p$-subgroup $P$ of a finite group $G$, $P \cap [G, G] = P^*$.

The Lean statement is `Subgroup.commutator_inf_eq_focalSubgroup`, with the commutator subgroup `commutator G`. The proof uses that the transfer to $P / P^*$ is onto, by `Subgroup.transferFocal_surjective`, and computes its kernel on $P$, by `Subgroup.ker_restrict_transferFocal_eq_focalSubgroupOf`. As a consequence, `Subgroup.transferFocal.quotientKerMulEquivQuotientFocalSubgroupOf` identifies $G / \ker V$ with $P / P^*$. The theorem says that the largest abelian $p$-quotient of $G$ is determined by the conjugation of elements of $P$ inside $G$.

#### The theorem of Schur and Zassenhaus

**Theorem (Schur-Zassenhaus).** Let $N$ be a normal subgroup of a finite group $G$ with $\gcd(|N|, [G : N]) = 1$. Then $N$ has a complement: a subgroup $K$ with $N \cap K = 1$ and $N K = G$.

The library has two forms, `Subgroup.exists_right_complement'_of_coprime` and `Subgroup.exists_left_complement'_of_coprime`, which differ in the order of the factors of `Subgroup.IsComplement'`. The statements use `Nat.card` and `Subgroup.index`, and they have no separate finiteness assumption.

*Proof sketch.* First let $N$ be commutative. Then $G$ acts on the set `Subgroup.QuotientDiff N` of left transversals of $N$ modulo the relation $d(S, T) = 1$, where $d$ is the difference of the transfer. The coprimality shows that already $N$ acts transitively, by `Subgroup.exists_smul_eq`, and the stabilizer of a point is a complement of $N$, by `Subgroup.isComplement'_stabilizer_of_coprime`. In general, take a counterexample $G$ of least order. A sequence of reductions shows that $N$ is a minimal normal subgroup, then a $p$-group, then commutative, which contradicts the first case. The steps are the lemmas `Subgroup.SchurZassenhausInduction.step7` and those before it. $\square$

Each finite group of order $m n$ with $\gcd(m, n) = 1$ and a normal subgroup of order $m$ is therefore a semidirect product of that subgroup by a subgroup of order $n$.

#### Z-groups

A Z-group is a group whose Sylow subgroups are all cyclic. The class is `IsZGroup G`, and `isZGroup_iff` unfolds it. A cyclic group is a Z-group, by the instance `IsZGroup.instOfIsCyclic`. A group of squarefree order is a Z-group, by `IsZGroup.of_squarefree`: each Sylow subgroup has prime order, so it is cyclic. The class passes to subgroups, by `IsZGroup.instSubtypeMemSubgroup`, and to quotients of a finite group, by `IsZGroup.instQuotientSubgroupOfFinite`. For maps, `IsZGroup.of_injective` and `IsZGroup.of_surjective` state the same.

The main results describe the structure of a finite Z-group $G$.

| Lean name | Statement |
|---|---|
| `IsZGroup.isCyclic_commutator` | $[G, G]$ is cyclic |
| `IsZGroup.isCyclic_abelianization` | $G / [G, G]$ is cyclic |
| `IsZGroup.coprime_commutator_index` | the order of $[G, G]$ is coprime to its index |
| `IsZGroup.instIsSolvableOfFinite` | $G$ is solvable |
| `IsZGroup.exponent_eq_card` | the exponent of $G$ equals its order |
| `IsZGroup.instIsCyclicOfFiniteOfIsNilpotent` | a nilpotent finite Z-group is cyclic |
| `isZGroup_iff_exists_mulEquiv` | $G$ is a Z-group if and only if it is a semidirect product of two cyclic groups of coprime orders |

The proofs use the Burnside theorem above at the smallest prime, by induction on the order, and the Schur-Zassenhaus theorem for the last row. The lemma `Sylow.le_center_or_le_commutator` is a key step: a normal cyclic Sylow subgroup lies in the center or in the commutator subgroup.

#### Fixed-point-free automorphisms

A map $\varphi : G \to G$ is fixed-point-free if $\varphi(g) = g$ only for $g = 1$. This is `MonoidHom.FixedPointFree φ`. The commutator map $g \mapsto g \varphi(g)^{-1}$ is `MonoidHom.commutatorMap φ`, written `g / φ g`.

**Proposition.** If $\varphi$ is a fixed-point-free endomorphism, the commutator map is injective, so it is a bijection when $G$ is finite.

*Proof.* Suppose $g \varphi(g)^{-1} = h \varphi(h)^{-1}$. Then $h^{-1} g = \varphi(h)^{-1} \varphi(g) = \varphi(h^{-1} g)$, so $h^{-1} g$ is a fixed point and $g = h$. $\square$

This is `MonoidHom.FixedPointFree.commutatorMap_injective`, and `MonoidHom.FixedPointFree.commutatorMap_surjective` is the finite case. Now let $\varphi$ also be an involution and $G$ finite. Each $x$ is $g \varphi(g)^{-1}$, so $\varphi(x) = \varphi(g) g^{-1} = x^{-1}$. So $\varphi$ is the inversion, by `MonoidHom.FixedPointFree.coe_eq_inv_of_involutive`. Inversion is then a homomorphism, so $G$ is commutative, by `MonoidHom.FixedPointFree.commute_all_of_involutive`, and `MonoidHom.FixedPointFree.commGroupOfInvolutive` builds the `CommGroup` structure. An element of order $2$ would be a fixed point of the inversion, so $|G|$ is odd, by `MonoidHom.FixedPointFree.odd_card_of_involutive`.

#### Common errors

1. `MonoidHom.transfer` needs the instance `[H.FiniteIndex]` and a commutative target. For a noncommutative $H$, first compose with a map to an abelian quotient, as `Subgroup.transferFocal` does.
2. `MonoidHom.transferSylow` takes the proof `hP : normalizer P ≤ centralizer P` as an argument. The lemma `IsCyclic.normalizer_le_centralizer` supplies it only for the smallest prime factor, stated as `(Nat.card G).minFac = p`.
3. The two Schur-Zassenhaus lemmas differ in the order of the arguments of `Subgroup.IsComplement'`. A goal of the form `∃ K, K.IsComplement' N` needs `Subgroup.exists_left_complement'_of_coprime`.

### Exercises

1. (A) Show that a group of order $30$ has a normal subgroup of index $2$.
2. (B) Show that every group of order $15$ is a Z-group, and deduce that it is cyclic.
3. (B) Let $[G : Z(G)] = n$ be finite. Show that $g \mapsto g^n$ is a homomorphism $G \to Z(G)$, and compute its image for $G = D_4$.
4. (B) Show that $N = \langle (1 2 3) \rangle$ in $S_3$ has a complement, and check that the complement is not normal.
5. (B) Show that a finite group with a fixed-point-free automorphism $\varphi$ with $\varphi^2 = \mathrm{id}$ is commutative of odd order.
6. (C) Let $G$ be a finite group whose Sylow $2$-subgroups are cyclic and nontrivial. Show that $G$ has a normal subgroup of index $|P|$, where $P$ is a Sylow $2$-subgroup.

### Reference

<?reference?>
