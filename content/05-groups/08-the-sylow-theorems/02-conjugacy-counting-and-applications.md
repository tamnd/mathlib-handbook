---
title: The second and third Sylow theorems and groups of small order
kind: theory
modules:
  - Mathlib.GroupTheory.Sylow
explains:
  E3: [card_sylow_modEq_one, Sylow.isPretransitive_of_finite]
  E2: [Sylow.card_dvd_index, Sylow.card_eq_index_normalizer, Sylow.smul_eq_iff_mem_normalizer, Sylow.unique_of_normal, Sylow.normal_of_subsingleton, Sylow.not_dvd_index, Sylow.card_coprime_index, Sylow.ext]
  E1: auto
families: []
requires: [V05.C06]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V05/C08/Examples.lean
  - MathlibHandbook/V05/C08/Exercises.lean
  - MathlibHandbook/V05/C08/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The second and third Sylow theorems and groups of small order

### Overview

The first Sylow theorem gives Sylow $p$-subgroups. The second says that they are all conjugate, and that each $p$-subgroup lies in one of them. The third counts them: their number $n_p$ divides the index $m$ of a Sylow subgroup, and $n_p \equiv 1 \pmod p$. These two conditions often force $n_p = 1$. Then the Sylow $p$-subgroup is normal, and the group is not simple.

The section proves the two theorems in full, with the fixed point congruence and orbit-stabilizer. Then it applies them: groups of order $pq$, groups of order $15$, $12$, $30$ and $56$.

### Definitions

Fix a prime $p$ and a finite group $G$ with $|G| = p^a m$, $p \nmid m$. The group $G$ acts on its subgroups by conjugation, $g \cdot H = g H g^{-1}$. The conjugate of a Sylow $p$-subgroup has the same order, so it is a Sylow $p$-subgroup, and $G$ acts on $\operatorname{Syl}_p(G)$. The stabilizer of $P$ is the normalizer $N_G(P)$.

::: mathlib
`Sylow.smul_eq_iff_mem_normalizer` · `Mathlib.GroupTheory.Sylow`

The action of `G` on `Sylow p G` is by conjugation, and `g • P = P ↔ g ∈ normalizer P`. The underlying subgroup of `g • P` is the pointwise conjugate, by `Sylow.pointwise_smul_def`.

<?decl Sylow.smul_eq_iff_mem_normalizer?>
:::

**Definition (Simple group).** A group $G \ne \{1\}$ is simple if its only normal subgroups are $\{1\}$ and $G$.

### Theorems and proofs

**Theorem (Sylow II).** Let $P \in \operatorname{Syl}_p(G)$ and let $Q \le G$ be a $p$-subgroup. Then $Q \le g P g^{-1}$ for some $g \in G$. In particular, any two Sylow $p$-subgroups are conjugate.

*Proof.* Let $Q$ act on the set $G/P$ of left cosets of $P$ by $q \cdot gP = qgP$. The set has $[G : P] = m$ elements, and $|Q|$ is a power of $p$. By the fixed point congruence, the number of fixed cosets is $\equiv m \not\equiv 0 \pmod p$. So there is a fixed coset $gP$. Then $qgP = gP$ for each $q \in Q$, so $g^{-1} q g \in P$, and $q \in g P g^{-1}$. So $Q \le g P g^{-1}$. If $Q$ is a Sylow $p$-subgroup too, then $|Q| = p^a = |g P g^{-1}|$, and $Q = g P g^{-1}$. $\square$

::: mathlib
`Sylow.isPretransitive_of_finite` · `Mathlib.GroupTheory.Sylow`

The second Sylow theorem as an instance: `MulAction.IsPretransitive G (Sylow p G)`, when `Sylow p G` is finite. So for two Sylow subgroups `P` and `Q` there is `g` with `g • P = Q`, by `MulAction.exists_smul_eq`. The part about an arbitrary `p`-subgroup is `IsPGroup.exists_le_sylow` with this instance.

<?decl Sylow.isPretransitive_of_finite?>
:::

**Corollary (Normal Sylow subgroups).** Let $P \in \operatorname{Syl}_p(G)$. Then $P \trianglelefteq G$ if and only if $n_p = 1$.

*Proof.* If $P$ is normal, each conjugate of $P$ is $P$, so by Sylow II $P$ is the only Sylow $p$-subgroup. If $n_p = 1$, each conjugate $g P g^{-1}$ is a Sylow $p$-subgroup, so it is $P$, and $P$ is normal. $\square$

::: mathlib
`Sylow.unique_of_normal` · `Mathlib.GroupTheory.Sylow`

The first direction: a normal Sylow subgroup gives `Unique (Sylow p G)`.

<?decl Sylow.unique_of_normal?>
:::

::: mathlib
`Sylow.normal_of_subsingleton` · `Mathlib.GroupTheory.Sylow`

The second direction: under `[Subsingleton (Sylow p G)]`, each `P : Sylow p G` is normal.

<?decl Sylow.normal_of_subsingleton?>
:::

**Theorem (Sylow III).** Let $P \in \operatorname{Syl}_p(G)$. Then $n_p = [G : N_G(P)]$. So $n_p$ divides $m$. Also $n_p \equiv 1 \pmod p$.

*Proof.* By Sylow II the action of $G$ on $\operatorname{Syl}_p(G)$ has one orbit. The stabilizer of $P$ is $N_G(P)$. By orbit-stabilizer, $n_p = [G : N_G(P)]$. Since $P \le N_G(P) \le G$, the tower law gives $m = [G : P] = [G : N_G(P)] \cdot [N_G(P) : P]$, so $n_p \mid m$.

For the congruence, restrict the action to $P$. The group $P$ has order $p^a$, so the fixed point congruence gives $n_p \equiv |F| \pmod p$, with $F$ the set of the $Q \in \operatorname{Syl}_p(G)$ such that $x Q x^{-1} = Q$ for each $x \in P$. The subgroup $P$ itself is in $F$. Let $Q \in F$. Then $P \le N_G(Q)$. So $P$ and $Q$ are subgroups of $N = N_G(Q)$ of order $p^a$. Since $|N|$ divides $|G|$, $p^a$ is the largest power of $p$ that divides $|N|$, and $P$ and $Q$ are Sylow $p$-subgroups of $N$. By Sylow II in $N$, $P = y Q y^{-1}$ for some $y \in N$. But $Q$ is normal in $N$, so $y Q y^{-1} = Q$, and $P = Q$. So $F = \{P\}$ and $n_p \equiv 1 \pmod p$. $\square$

::: mathlib
`card_sylow_modEq_one` · `Mathlib.GroupTheory.Sylow`

The congruence `Nat.card (Sylow p G) ≡ 1 [MOD p]`. It needs only `[Finite (Sylow p G)]`, not a finite group. The Mathlib proof is the proof above, with `IsPGroup.card_modEq_card_fixedPoints`.

<?decl card_sylow_modEq_one?>
:::

::: mathlib
`Sylow.card_eq_index_normalizer` · `Mathlib.GroupTheory.Sylow`

The equation `Nat.card (Sylow p G) = (normalizer P).index`.

<?decl Sylow.card_eq_index_normalizer?>
:::

::: mathlib
`Sylow.card_dvd_index` · `Mathlib.GroupTheory.Sylow`

The divisibility `Nat.card (Sylow p G) ∣ P.index`, that is, $n_p \mid m$.

<?decl Sylow.card_dvd_index?>
:::

**Proposition (The index of a Sylow subgroup).** For $P \in \operatorname{Syl}_p(G)$, $p \nmid [G : P]$, and $|P|$ is coprime to $[G : P]$.

*Proof.* The index is $m$, and $p \nmid m$ by the choice of $a$. A common prime factor of $p^a$ and $m$ is $p$. $\square$

::: mathlib
`Sylow.not_dvd_index` · `Mathlib.GroupTheory.Sylow`

The theorem `¬p ∣ P.index`, for a Sylow subgroup of finite index.

<?decl Sylow.not_dvd_index?>
:::

::: mathlib
`Sylow.card_coprime_index` · `Mathlib.GroupTheory.Sylow`

The theorem `(Nat.card P).Coprime P.index`, for `G` finite.

<?decl Sylow.card_coprime_index?>
:::

**Theorem (Groups of order $pq$).** Let $|G| = pq$ with primes $p < q$. Then the Sylow $q$-subgroup is normal, so $G$ is not simple. If also $p \nmid q - 1$, then $G$ is cyclic.

*Proof.* By Sylow III, $n_q \mid p$ and $n_q \equiv 1 \pmod q$. The divisors of $p$ are $1$ and $p$. Since $1 < p < q$, $p$ is its own remainder modulo $q$, so $p \not\equiv 1 \pmod q$. So $n_q = 1$, and the Sylow $q$-subgroup $Q$ is normal. Now let $p \nmid q - 1$. Then $n_p \mid q$ and $n_p \equiv 1 \pmod p$. The case $n_p = q$ would give $p \mid q - 1$, so $n_p = 1$, and the Sylow $p$-subgroup $P$ is normal too. The orders of $P$ and $Q$ are coprime, so $P \cap Q = \{1\}$ by Lagrange. Let $P = \langle x \rangle$ and $Q = \langle y \rangle$; groups of prime order are cyclic. The commutator $x y x^{-1} y^{-1}$ is in $Q$, as $x y x^{-1} \in Q$, and in $P$, as $y x^{-1} y^{-1} \in P$. So it is $1$, and $x$ and $y$ commute. Commuting elements of coprime orders $p$ and $q$ have a product of order $pq$. So $xy$ generates $G$. $\square$

**Theorem (No simple groups of order $30$ or $56$).** A group of order $30$ or $56$ has a normal Sylow subgroup.

*Proof.* Two distinct subgroups of prime order $r$ meet in $\{1\}$, by Lagrange. So $n_r$ subgroups of order $r$ give $n_r (r - 1)$ elements of order $r$.

Let $|G| = 30 = 2 \cdot 3 \cdot 5$. Then $n_5 \mid 6$ and $n_5 \equiv 1 \pmod 5$, so $n_5 \in \{1, 6\}$. Also $n_3 \mid 10$ and $n_3 \equiv 1 \pmod 3$, so $n_3 \in \{1, 10\}$. If $n_5 = 6$ and $n_3 = 10$, then $G$ has $6 \cdot 4 = 24$ elements of order $5$ and $10 \cdot 2 = 20$ elements of order $3$, and $44 > 30$. So $n_5 = 1$ or $n_3 = 1$.

Let $|G| = 56 = 2^3 \cdot 7$. Then $n_7 \mid 8$ and $n_7 \equiv 1 \pmod 7$, so $n_7 \in \{1, 8\}$. If $n_7 = 8$, there are $8 \cdot 6 = 48$ elements of order $7$. The other $8$ elements contain each Sylow $2$-subgroup, which has order $8$ and no element of order $7$. So there is exactly one Sylow $2$-subgroup, and it is normal. $\square$

### Examples

**Example (Sylow numbers of $S_4$).** Here $24 = 2^3 \cdot 3$. The last section found $n_3 = 4$ and $n_2 = 3$. Check: $4 \mid 8$, $4 \equiv 1 \pmod 3$, $3 \mid 3$, $3 \equiv 1 \pmod 2$. The normalizer of $\langle (1\,2\,3) \rangle$ has index $4$, so order $6$; it is the copy of $S_3$ on $\{1, 2, 3\}$. The normalizer of a Sylow $2$-subgroup has index $3$, so order $8$; the subgroup is its own normalizer.

**Example (Order $15$).** For $p = 3$, $q = 5$: $3 \nmid 4$, so each group of order $15$ is cyclic. The same holds for orders $33 = 3 \cdot 11$, $35 = 5 \cdot 7$ and $51 = 3 \cdot 17$.

**Counterexample (Order $6$).** For $p = 2$, $q = 3$, $p \mid q - 1$, and $S_3$ is not cyclic. Its Sylow $3$-subgroup $A_3$ is normal, as the theorem says, but $n_2 = 3$: the three subgroups $\langle (1\,2) \rangle$, $\langle (1\,3) \rangle$, $\langle (2\,3) \rangle$. The same happens for $D_q$ of order $2q$.

**Example (Order $12$).** Let $|G| = 12$. Then $n_3 \in \{1, 4\}$. If $n_3 = 4$, then $G$ has $8$ elements of order $3$, and the other $4$ elements form the unique Sylow $2$-subgroup, which is normal. So $n_3 = 1$ or $n_2 = 1$. The group $A_4$ has $n_3 = 4$ and $n_2 = 1$, with Sylow $2$-subgroup $V$. The group $\mathbb{Z}/12$ has $n_2 = n_3 = 1$. The dihedral group $D_6$ has $n_3 = 1$, with Sylow $3$-subgroup $\langle r^2 \rangle$, and $n_2 = 3$.

**Counterexample (Non-maximal $p$-subgroups).** The analogue of Sylow II fails for $p$-subgroups that are not maximal. In the Klein group $V$ the three subgroups of order $2$ are not conjugate, since $V$ is commutative and each conjugate of a subgroup is the subgroup itself.

**Counterexample (Counting does not always succeed).** Let $G = A_5$, of order $60 = 2^2 \cdot 3 \cdot 5$. The conditions allow $n_5 \in \{1, 6\}$, $n_3 \in \{1, 4, 10\}$, $n_2 \in \{1, 3, 5, 15\}$. In $A_5$ the values are $n_5 = 6$, $n_3 = 10$, $n_2 = 5$, and no Sylow subgroup is normal. Indeed $A_5$ is simple, so the Sylow theorems alone cannot show that every group of order $60$ has a normal subgroup.

**Example (Sylow II in Lean).**

<?lean MathlibHandbook/V05/C08/Examples.lean#conjugate?>

**Example (Sylow III in Lean).**

<?lean MathlibHandbook/V05/C08/Examples.lean#mod_one?>

### The library around it

The rest of `Mathlib.GroupTheory.Sylow` builds on these theorems. `Sylow.normalizer_normalizer` states that the normalizer of a Sylow subgroup is its own normalizer. The Frattini argument is `Sylow.normalizer_sup_eq_top`. The file `Mathlib.GroupTheory.SpecificGroups.Alternating.Simple` proves that $A_n$ is simple for $n \ge 5$, as `alternatingGroup.isSimpleGroup`. The theorem of Schur and Zassenhaus, in `Mathlib.GroupTheory.SchurZassenhaus`, gives a complement to a normal subgroup of coprime order.

::: mathlib
`Sylow.ext` · `Mathlib.GroupTheory.Sylow`

Extensionality: `(P : Subgroup G) = Q → P = Q`. Use it to turn an equation of subgroups into an equation in `Sylow p G`.

<?decl Sylow.ext?>
:::

Common errors of a learner:

- The conditions $n_p \mid m$ and $n_p \equiv 1 \pmod p$ are necessary, not sufficient. For $|G| = 12$ they allow $n_3 = 4$ and $n_2 = 3$, and each value occurs, but not both in one group, by the count of elements above.
- Two Sylow subgroups for different primes can meet only in $\{1\}$, but two Sylow subgroups for the same prime can meet in a large subgroup when $p^a$ is not prime. The count of elements works only for Sylow subgroups of prime order.
- `card_sylow_modEq_one` takes `p` and `G` as explicit arguments; `Sylow.card_dvd_index` takes a Sylow subgroup.

### Exercises

1. (A) Find $n_2$ and $n_5$ for $D_5$ and for $\mathbb{Z}/10$.
2. (A) Show that every group of order $35$ is cyclic.
3. (B) Show that a group of order $20$ has a normal Sylow $5$-subgroup.
4. (B) Show that a group of order $p^2 q$, with $p$ and $q$ distinct primes, is not simple. Hint: if $n_q = p^2$, count the elements of order $q$; the case $q \mid p + 1$ needs $p = 2$, $q = 3$.
5. (B) Let $P \in \operatorname{Syl}_p(G)$ and $P \le H \le G$. Show that $P \in \operatorname{Syl}_p(H)$ and that $n_p(H) \le n_p(G)$.
6. (C) Prove the Frattini argument: if $N \trianglelefteq G$ and $P \in \operatorname{Syl}_p(N)$, then $G = N_G(P) N$. Hint: for $g \in G$, $g P g^{-1}$ is a Sylow subgroup of $N$; apply Sylow II in $N$.
7. (C) Show that a simple group of order $60$ has $n_5 = 6$, and that it has a subgroup of index $6$.
8. (L) Prove that two Sylow subgroups with the same underlying subgroup are equal. The solution is `sylow_ext_example`.

### Notes and history

Sylow published the three theorems in 1872 in the Mathematische Annalen, for groups of permutations. His statement of the third theorem was $n_p \equiv 1 \pmod p$. Frobenius proved in 1895 a stronger congruence: the number of subgroups of order $p^k$ is $\equiv 1 \pmod p$ for each $p^k$ that divides $|G|$. The proof of Sylow III by the action of $P$ on $\operatorname{Syl}_p(G)$ is standard in modern texts.

The classification of the groups of small order uses these arguments again and again. Hölder determined the groups of order $pq$, $p^2 q$ and of square-free order in the 1890s. The simplicity of $A_5$, and the fact that it is the only simple group of order $60$ up to isomorphism, are the start of the theory of finite simple groups.

### Reference

<?reference?>
