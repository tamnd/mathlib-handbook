---
title: The theorem of Cauchy and the first Sylow theorem
kind: theory
modules:
  - Mathlib.GroupTheory.Sylow
explains:
  E3: [exists_prime_orderOf_dvd_card, Sylow.exists_subgroup_card_pow_prime]
  E2: [Sylow, Sylow.exists_subgroup_card_pow_succ, Sylow.card_quotient_normalizer_modEq_card_quotient, Sylow.card_eq_multiplicity, Sylow.ofCard, IsPGroup.exists_le_sylow, Subgroup.normalizer]
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

## The theorem of Cauchy and the first Sylow theorem

### Overview

The converse of the theorem of Lagrange is false: $A_4$ has order $12$ and no subgroup of order $6$. For prime powers the converse is true. The theorem of Cauchy gives an element of order $p$ for each prime $p$ that divides $|G|$. The first Sylow theorem gives a subgroup of order $p^n$ for each prime power $p^n$ that divides $|G|$. In particular, if $|G| = p^a m$ with $p \nmid m$, there is a subgroup of order $p^a$, a Sylow $p$-subgroup.

Both proofs use the fixed point congruence of the last chapter: a group of order $p^n$ that acts on a finite set $X$ has $|X| \equiv |X^P| \pmod p$. The next section proves the second and the third Sylow theorems and applies them to groups of small order.

### Definitions

Fix a prime $p$ and a finite group $G$. Write $|G| = p^a m$ with $p \nmid m$.

**Definition (Normalizer).** For a subgroup $H \le G$, the normalizer of $H$ is $N_G(H) = \{g \in G : g H g^{-1} = H\}$. It is the stabilizer of $H$ for the action of $G$ on its subgroups by conjugation, so it is a subgroup. It contains $H$, and $H$ is normal in $N_G(H)$. It is the largest subgroup of $G$ in which $H$ is normal, and $N_G(H) = G$ if and only if $H \trianglelefteq G$.

::: mathlib
`Subgroup.normalizer` · `Mathlib.Algebra.Group.Subgroup.Defs`

The normalizer of a set `S : Set G`, as a subgroup. For a subgroup `H` one writes `Subgroup.normalizer (H : Set G)`, or `H.normalizer` with the coercion. For a subgroup `H`, the membership lemma `Subgroup.mem_normalizer_iff` states `g ∈ normalizer H ↔ ∀ h, h ∈ H ↔ g * h * g⁻¹ ∈ H`.

<?decl Subgroup.normalizer?>
:::

**Definition (Sylow subgroup).** A $p$-subgroup of $G$ is a subgroup whose order is a power of $p$. A Sylow $p$-subgroup is a subgroup of order $p^a$, the largest power of $p$ that divides $|G|$. Write $\operatorname{Syl}_p(G)$ for the set of them and $n_p = |\operatorname{Syl}_p(G)|$.

::: mathlib
`Sylow` · `Mathlib.GroupTheory.Sylow`

The type `Sylow p G` of the Sylow `p`-subgroups. Mathlib uses a definition that also works for infinite groups: a term is a subgroup `P` with `IsPGroup p P`, and each `p`-subgroup that contains `P` is equal to `P`. So a Sylow subgroup is a maximal `p`-subgroup. A term coerces to `Subgroup G`. The definition does not assume that `p` is prime; the theorems do, with the instance `[Fact p.Prime]`.

<?decl Sylow?>
:::

The two definitions agree for finite groups. This is a corollary below.

### Theorems and proofs

**Theorem (Cauchy).** Let $G$ be finite and let $p$ be a prime that divides $|G|$. Then $G$ has an element of order $p$.

*Proof.* This proof is due to McKay. Let
$$X = \{(x_1, \ldots, x_p) \in G^p : x_1 x_2 \cdots x_p = 1\}.$$
The first $p - 1$ entries of a tuple in $X$ are arbitrary, and they fix the last entry as $x_p = (x_1 \cdots x_{p-1})^{-1}$. So $|X| = |G|^{p-1}$. Since $p \mid |G|$ and $p - 1 \ge 1$, $p$ divides $|X|$.

If $(x_1, \ldots, x_p) \in X$, then $(x_2, \ldots, x_p, x_1) \in X$, because
$$x_2 \cdots x_p x_1 = x_1^{-1} (x_1 x_2 \cdots x_p) x_1 = x_1^{-1} x_1 = 1.$$
So the rotation $\rho$ is a map $X \to X$. It is a bijection, and $\rho^p$ is the identity. So $k \cdot x = \rho^k(x)$ is an action of $\mathbb{Z}/p$ on $X$. The group $\mathbb{Z}/p$ has order $p$, so the fixed point congruence gives $|X| \equiv |X^{\mathbb{Z}/p}| \pmod p$.

A tuple is fixed by $\rho$ if and only if its entries are equal, so the fixed points are the tuples $(x, \ldots, x)$ with $x^p = 1$. Their number is $|\{x \in G : x^p = 1\}|$, and it is $\equiv |X| \equiv 0 \pmod p$. It is at least $1$, because $x = 1$ counts. So it is at least $p \ge 2$, and there is an $x \ne 1$ with $x^p = 1$. The order of $x$ divides $p$ and is not $1$, so it is $p$. $\square$

::: mathlib
`exists_prime_orderOf_dvd_card` · `Mathlib.GroupTheory.Perm.Cycle.Type`

The theorem of Cauchy: `p ∣ Fintype.card G → ∃ x : G, orderOf x = p`, with `[Fact p.Prime]`. It sits in the file of the cycle type, because the Mathlib proof is the proof of McKay, with the rotation as a permutation of the tuples. The version for `Nat.card` is `exists_prime_orderOf_dvd_card'`.

<?decl exists_prime_orderOf_dvd_card?>
:::

**Corollary (Finite $p$-groups).** A finite group $G$ has order a power of $p$ if and only if the order of each element is a power of $p$.

*Proof.* If $|G| = p^n$, each order divides $p^n$ by Lagrange, so it is a power of $p$. Conversely, if a prime $q \ne p$ divides $|G|$, then Cauchy gives an element of order $q$, which is not a power of $p$. $\square$

So the definition of `IsPGroup` by the orders of the elements agrees with the definition by the order of the group.

**Lemma (Normalizer congruence).** Let $H \le G$ be a subgroup of order $p^n$. Then
$$[N_G(H) : H] \equiv [G : H] \pmod p.$$

*Proof.* Let $H$ act on the set $G/H$ of left cosets by $h \cdot gH = hgH$. The set has $[G : H]$ elements, and $H$ has order $p^n$, so the fixed point congruence gives $[G:H] \equiv |(G/H)^H| \pmod p$. A coset $gH$ is fixed if and only if $hgH = gH$ for each $h \in H$. This holds if and only if $g^{-1} h g \in H$ for each $h \in H$, that is, $g^{-1} H g \subseteq H$. The two sets have the same finite size, so this is $g^{-1} H g = H$, which is $g^{-1} \in N_G(H)$, which is $g \in N_G(H)$. So the fixed cosets are the cosets $gH$ with $g \in N_G(H)$. These are the elements of $N_G(H)/H$, and there are $[N_G(H) : H]$ of them. $\square$

::: mathlib
`Sylow.card_quotient_normalizer_modEq_card_quotient` · `Mathlib.GroupTheory.Sylow`

The lemma for `Nat.card H = p ^ n`. The left side is the quotient of `normalizer H` by `H` seen as a subgroup of it, written with `Subgroup.comap` along the inclusion `subtype`.

<?decl Sylow.card_quotient_normalizer_modEq_card_quotient?>
:::

**Theorem (Sylow I, step).** Let $H \le G$ have order $p^n$ and let $p^{n+1}$ divide $|G|$. Then there is a subgroup $K$ with $H \le K$, $|K| = p^{n+1}$ and $H \trianglelefteq K$.

*Proof.* By Lagrange, $|G| = p^n [G : H]$. Since $p^{n+1} \mid |G|$, $p \mid [G : H]$. By the lemma, $p \mid [N_G(H) : H]$. The subgroup $H$ is normal in $N = N_G(H)$, so $N/H$ is a group of order $[N : H]$, and $p$ divides this order. By Cauchy, $N/H$ has a subgroup $C$ of order $p$. Let $\pi : N \to N/H$ be the quotient map and let $K = \pi^{-1}(C)$. By the correspondence theorem $K$ is a subgroup of $N$ that contains $H$, and $K/H = C$. So $|K| = |C| \cdot |H| = p \cdot p^n = p^{n+1}$. Since $K \le N$, $H$ is normal in $K$. $\square$

::: mathlib
`Sylow.exists_subgroup_card_pow_succ` · `Mathlib.GroupTheory.Sylow`

The step: `p ^ (n + 1) ∣ Nat.card G → Nat.card H = p ^ n → ∃ K, Nat.card K = p ^ (n + 1) ∧ H ≤ K`. The statement does not record that `H` is normal in `K`; the induction does not need it.

<?decl Sylow.exists_subgroup_card_pow_succ?>
:::

**Theorem (Sylow I).** If $p^n$ divides $|G|$, then $G$ has a subgroup of order $p^n$. Each subgroup of order $p^k$ with $k \le n$ lies in one of them. In particular $G$ has a Sylow $p$-subgroup.

*Proof.* Induction on $n$, from the trivial subgroup, of order $p^0$. If $H$ has order $p^k$ and $p^{k+1} \mid |G|$, the step gives $K \ge H$ of order $p^{k+1}$. Repeat until the order is $p^n$. $\square$

::: mathlib
`Sylow.exists_subgroup_card_pow_prime` · `Mathlib.GroupTheory.Sylow`

The theorem `p ^ n ∣ Nat.card G → ∃ K : Subgroup G, Nat.card K = p ^ n`.

<?decl Sylow.exists_subgroup_card_pow_prime?>
:::

**Corollary (The two definitions agree).** Let $P$ be a $p$-subgroup of $G$. Then $P$ is a maximal $p$-subgroup if and only if $|P| = p^a$. Each $p$-subgroup lies in a Sylow $p$-subgroup.

*Proof.* If $|P| = p^a$ and $Q \ge P$ is a $p$-subgroup, then $|Q|$ is a power of $p$ that divides $|G|$, so $|Q| \le p^a = |P|$ and $Q = P$. Conversely, let $P$ be maximal with $|P| = p^k$. If $k < a$, then $p^{k+1} \mid |G|$, and the step gives a larger $p$-subgroup. So $k = a$. The last claim is the theorem with $n = a$. $\square$

::: mathlib
`Sylow.card_eq_multiplicity` · `Mathlib.GroupTheory.Sylow`

For `P : Sylow p G` with `G` finite: `Nat.card P = p ^ (Nat.card G).factorization p`. The exponent `(Nat.card G).factorization p` is $a$.

<?decl Sylow.card_eq_multiplicity?>
:::

::: mathlib
`Sylow.ofCard` · `Mathlib.GroupTheory.Sylow`

The converse direction as a construction: a subgroup `H` with `Nat.card H = p ^ (Nat.card G).factorization p` gives a term of `Sylow p G`. This is the usual way to produce a Sylow subgroup from a count.

<?decl Sylow.ofCard?>
:::

::: mathlib
`IsPGroup.exists_le_sylow` · `Mathlib.GroupTheory.Sylow`

The theorem `IsPGroup p P → ∃ Q : Sylow p G, P ≤ Q`. It needs no finiteness: for an infinite group the proof uses Zorn's lemma. So `Sylow p G` is never empty; the instance is `Sylow.nonempty`.

<?decl IsPGroup.exists_le_sylow?>
:::

### Examples

**Example (Cauchy for $S_3$ and $p = 2$).** In the proof for $G = S_3$ and $p = 2$, $X = \{(x, x^{-1})\}$ has $6$ elements. The rotation sends $(x, x^{-1})$ to $(x^{-1}, x)$. The fixed points are the pairs with $x = x^{-1}$: the identity and the three transpositions, so $4 \equiv 6 \pmod 2$. For $p = 3$, $|X| = 36$, and the fixed points are $(x, x, x)$ with $x^3 = 1$: the identity and the two $3$-cycles, so $3 \equiv 36 \equiv 0 \pmod 3$.

**Example (Sylow subgroups of $S_4$).** Here $|S_4| = 24 = 2^3 \cdot 3$. A Sylow $3$-subgroup has order $3$; it is $\langle (a\,b\,c) \rangle$, and there are $8/2 = 4$ of them. A Sylow $2$-subgroup has order $8$. The dihedral group of the square with vertices $1, 2, 3, 4$ in this order is one of them:
$$D = \{e, (1\,2\,3\,4), (1\,3)(2\,4), (1\,4\,3\,2), (1\,3), (2\,4), (1\,2)(3\,4), (1\,4)(2\,3)\}.$$
The other two come from the orders $1, 3, 2, 4$ and $1, 2, 4, 3$ of the vertices. The chain $\{e\} < \langle (1\,3)(2\,4) \rangle < V < D$, with $V$ the Klein group, shows the step three times, each subgroup normal in the next.

**Example (A cyclic group).** In $\mathbb{Z}/12$ the subgroups of order $2$, $4$ and $3$ are $\langle 6 \rangle$, $\langle 3 \rangle$ and $\langle 4 \rangle$. For a cyclic group the theorem is weaker than the structure theorem for cyclic groups, which gives one subgroup of each order that divides $12$.

**Counterexample (Cauchy for a composite divisor).** The number $4$ divides $|V| = 4$ for the Klein group, but $V$ has no element of order $4$. The theorem of Cauchy needs a prime. The group $V$ is its own subgroup of order $4$, so Sylow I holds, but the subgroup is not cyclic.

**Counterexample (Orders that are not prime powers).** The group $A_4$ has order $12$ and no subgroup of order $6$, by the last chapter on cosets. So Sylow I does not extend to the divisors of $|G|$ that are not prime powers.

**Example (Cauchy in Lean).**

<?lean MathlibHandbook/V05/C08/Examples.lean#cauchy?>

**Example (Sylow I in Lean).**

<?lean MathlibHandbook/V05/C08/Examples.lean#exists_subgroup?>

**Example (The order of a Sylow subgroup in Lean).**

<?lean MathlibHandbook/V05/C08/Examples.lean#card_sylow?>

### The library around it

The file `Mathlib.GroupTheory.Sylow` builds the theory for arbitrary groups. The type `Sylow p G` exists for each group, and the finite statements carry `[Finite G]` or `[Finite (Sylow p G)]`. The orders are `Nat.card`, not `Fintype.card`, so the statements need no `Fintype` instance. The theorem of Cauchy is older in the library and still states `Fintype.card`. The file `Mathlib.GroupTheory.PGroup` has `IsPGroup` and the fixed point congruence `IsPGroup.card_modEq_card_fixedPoints`.

Common errors of a learner:

- The exponent $a$ is the exponent of $p$ in $|G|$, not the largest $n$ with $p^n \le |G|$. In Lean it is `(Nat.card G).factorization p`.
- A subgroup of order $p^n$ with $n < a$ is a $p$-subgroup, not a Sylow subgroup. The type `Sylow p G` holds only the maximal ones.
- For a prime $p$ that does not divide $|G|$, the Sylow $p$-subgroup is the trivial subgroup. It exists, and $n_p = 1$.
- An equation `(P : Subgroup G) = Q` between the underlying subgroups is not yet `P = Q` in `Sylow p G`; use `Sylow.ext`.

### Exercises

1. (A) Find all the Sylow $2$-subgroups and Sylow $3$-subgroups of $S_3$.
2. (A) Find a Sylow $2$-subgroup and a Sylow $5$-subgroup of $\mathbb{Z}/20$ and of $D_5$.
3. (B) Prove the theorem of Cauchy for an abelian group by induction on $|G|$. Hint: take $x \ne 1$; if $p \nmid \operatorname{ord}(x)$, pass to $G/\langle x \rangle$ and lift an element of order $p$.
4. (B) Let $|G| = p^a m$ and $P \in \operatorname{Syl}_p(G)$. Show that $p \nmid [N_G(P) : P]$. Hint: $[N_G(P) : P]$ divides $m$.
5. (B) Show that each subgroup of order $p^{a-1}$ is normal in some subgroup of order $p^a$.
6. (C) Show that a group of order $p^n$ has a normal subgroup of each order $p^k$, $0 \le k \le n$. Hint: use the center and induction.
7. (L) Prove that a group has a Sylow $p$-subgroup. The solution is `sylow_nonempty_example`.
8. (L) Prove that a group of even order has an element of order $2$. The solution is `cauchy_two_example`.

### Notes and history

Cauchy proved his theorem in 1845, for subgroups of symmetric groups, as part of his work on permutations. Ludwig Sylow proved the three theorems in 1872, also for groups of permutations. Frobenius gave a proof for abstract finite groups in 1887. The proof above of Cauchy's theorem is from a short note of James McKay in 1959. Wielandt gave in 1959 a different proof of Sylow I, by a count of the subsets of size $p^a$; the proof above, by the normalizer congruence, is the one of many later texts.

The Mathlib definition of `Sylow p G` as a maximal `p`-subgroup comes from the theory of infinite groups, where the order is not available. For finite groups the corollary above connects it to the textbook definition.

### Reference

<?reference?>
