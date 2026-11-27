---
title: The theorems of Cauchy and Sylow
kind: theory
modules:
  - Mathlib.GroupTheory.Sylow
explains:
  E3: [Sylow.exists_subgroup_card_pow_prime, card_sylow_modEq_one]
  E2: [Sylow, Sylow.card_eq_multiplicity, exists_prime_orderOf_dvd_card, Sylow.isPretransitive_of_finite]
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

## The theorems of Cauchy and Sylow

### Overview

The converse of the theorem of Lagrange is false, but it holds for prime powers. The theorem of Cauchy gives an element of order $p$ for each prime $p$ that divides $|G|$. The Sylow theorems go further. A finite group has a subgroup of order $p^k$ for each prime power $p^k$ that divides $|G|$. The subgroups of the largest such order, the Sylow $p$-subgroups, are conjugate to each other, and their number is $1$ modulo $p$. In Mathlib, `Sylow p G` is the type of the Sylow $p$-subgroups. This section shows the theorem of Cauchy and the three Sylow theorems.

### Definitions

**Definition ($p$-group).** For a prime $p$, a $p$-group is a group in which each element has an order that is a power of $p$. A finite $p$-group has order $p^k$. In Mathlib the predicate is `IsPGroup p G`.

**Definition (Sylow subgroup).** A Sylow $p$-subgroup of $G$ is a $p$-subgroup that no larger $p$-subgroup contains. In Mathlib it is a term of the structure `Sylow p G`, which coerces to `Subgroup G`.

### Theorems and proofs

**Theorem (Cauchy).** If $G$ is finite and a prime $p$ divides $|G|$, then $G$ has an element of order $p$.

*Proof.* Let $X$ be the set of the tuples $(x_1, \dots, x_p)$ in $G^p$ with $x_1 x_2 \cdots x_p = 1$. Then $|X| = |G|^{p-1}$, so $p$ divides $|X|$. The group $\mathbb{Z}/p$ acts on $X$ by rotation. Each orbit has size $1$ or $p$, by the orbit stabilizer theorem. The orbits of size $1$ are the tuples $(x, \dots, x)$ with $x^p = 1$. The tuple $(1, \dots, 1)$ is one of them, and $p$ divides the number of them. So there is $x \neq 1$ with $x^p = 1$. $\square$

**Theorem (First Sylow theorem).** If $p^n$ divides $|G|$, then $G$ has a subgroup of order $p^n$.

*Proof.* By induction on $n$. Let $H$ have order $p^{n-1}$. The normalizer $N$ of $H$ has $[N : H] \equiv [G : H] \pmod p$, by a count of the fixed points of the action of $H$ on $G / H$. So $p$ divides $|N / H|$. By the theorem of Cauchy, $N / H$ has a subgroup of order $p$. Its preimage in $N$ has order $p^n$. $\square$

**Theorem (Second Sylow theorem).** Any two Sylow $p$-subgroups $P$ and $Q$ of a finite group are conjugate.

*Proof.* $Q$ acts on $G / P$ by left multiplication. The number $[G : P]$ is prime to $p$, and each orbit of a $p$-group has a size that is a power of $p$. So there is a fixed point $gP$. Then $Q \le g P g^{-1}$, and the two have the same order. $\square$

**Theorem (Third Sylow theorem).** The number $n_p$ of Sylow $p$-subgroups is $1$ modulo $p$, and $n_p$ divides $[G : P]$.

*Proof.* $P$ acts on the Sylow $p$-subgroups by conjugation. The one fixed point is $P$, so $n_p \equiv 1 \pmod p$. By the second theorem, $G$ acts transitively, and the stabilizer of $P$ contains $P$. So $n_p$ divides $[G : P]$. $\square$

::: mathlib
`exists_prime_orderOf_dvd_card` · `Mathlib.GroupTheory.Perm.Cycle.Type`

The theorem of Cauchy. The prime is an instance `Fact p.Prime`. The proof in Mathlib uses the rotation of tuples above, so the lemma lives in the file of cycle types.

<?decl exists_prime_orderOf_dvd_card?>
:::

::: mathlib
`Sylow.exists_subgroup_card_pow_prime` · `Mathlib.GroupTheory.Sylow`

The first Sylow theorem for each prime power that divides `Nat.card G`. It needs `Finite G`.

<?decl Sylow.exists_subgroup_card_pow_prime?>
:::

::: mathlib
`Sylow` · `Mathlib.GroupTheory.Sylow`

The structure has the subgroup, the proof that it is a $p$-group, and the proof that it is maximal. It does not need a finite group. The lemma `Sylow.ext` says that two Sylow subgroups with the same subgroup are equal.

<?decl Sylow?>
:::

::: mathlib
`Sylow.card_eq_multiplicity` · `Mathlib.GroupTheory.Sylow`

A Sylow $p$-subgroup has the order $p^k$, where $k$ is the exponent of $p$ in the factorization of $|G|$.

<?decl Sylow.card_eq_multiplicity?>
:::

::: mathlib
`Sylow.isPretransitive_of_finite` · `Mathlib.GroupTheory.Sylow`

The second Sylow theorem, stated as an instance: the action of $G$ on `Sylow p G` by conjugation is transitive.

<?decl Sylow.isPretransitive_of_finite?>
:::

::: mathlib
`card_sylow_modEq_one` · `Mathlib.GroupTheory.Sylow`

The third Sylow theorem, $n_p \equiv 1 \pmod p$. The partner `Sylow.card_dvd_index` gives the divisibility.

<?decl card_sylow_modEq_one?>
:::

### Examples

**Example (The theorem of Cauchy).**

<?lean MathlibHandbook/V05/C08/Examples.lean#cauchy?>

**Example (Subgroups of prime power order).**

<?lean MathlibHandbook/V05/C08/Examples.lean#exists_subgroup?>

**Example (The order of a Sylow subgroup).**

<?lean MathlibHandbook/V05/C08/Examples.lean#card_sylow?>

**Example (Sylow subgroups are conjugate).** The instance search finds the proof.

<?lean MathlibHandbook/V05/C08/Examples.lean#conjugate?>

**Example (The number of Sylow subgroups).**

<?lean MathlibHandbook/V05/C08/Examples.lean#mod_one?>

### The library around it

The $p$-groups are in `Mathlib.GroupTheory.PGroup`, with the lemma `IsPGroup.card_modEq_card_fixedPoints` that the proofs above use. The normalizer of a subgroup is `Subgroup.normalizer`. The theorem of Cauchy in its additive form is `exists_prime_addOrderOf_dvd_card`. A finite group with only one Sylow $p$-subgroup has a normal Sylow subgroup, and the lemma `Sylow.normal_of_subsingleton` gives that. With these facts, the classification of groups of order $p q$ is a short exercise.

### Exercises

1. (A) Give the order of a Sylow $2$-subgroup of a group of order $24$.
2. (A) Explain why a Sylow $p$-subgroup is normal when $n_p = 1$.
3. (B) Show that a group of order $15$ is cyclic.
4. (B) Show that a group of order $12$ has a normal Sylow $2$-subgroup or a normal Sylow $3$-subgroup.
5. (L) Prove that each group has a Sylow $p$-subgroup. The solution is `sylow_nonempty_example`.
6. (L) Prove that two Sylow subgroups with the same subgroup are equal. The solution is `sylow_ext_example`.
7. (L) Prove that a finite group of even order has an element of order $2$. The solution is `cauchy_two_example`.

### Notes and history

Cauchy proved his theorem in 1845. Sylow published his three theorems in 1872, for groups of permutations. The proof of the theorem of Cauchy with tuples is due to McKay, in 1959. Mathlib proves the first Sylow theorem with the induction above. The step from $p^{n-1}$ to $p^n$ is `Sylow.exists_subgroup_card_pow_succ`.

### Reference

<?reference?>
