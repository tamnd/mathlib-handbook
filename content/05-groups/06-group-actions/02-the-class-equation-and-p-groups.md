---
title: The class equation, p-groups and counting orbits
kind: theory
modules:
  - Mathlib.GroupTheory.ClassEquation
  - Mathlib.GroupTheory.PGroup
explains:
  E3: [Group.card_center_add_sum_card_noncenter_eq_card, IsPGroup.card_modEq_card_fixedPoints]
  E2: [ConjAct, ConjAct.smul_def, ConjAct.stabilizer_eq_centralizer, IsConj, IsPGroup, IsPGroup.center_nontrivial, IsPGroup.commGroupOfCardEqPrimeSq, MulAction.fixedPoints, MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group]
  E1: auto
families: []
requires: [V05.C05]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V05/C06/Examples.lean
  - MathlibHandbook/V05/C06/Exercises.lean
  - MathlibHandbook/V05/C06/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The class equation, p-groups and counting orbits

### Overview

A group acts on itself by conjugation. The orbits of this action are the conjugacy classes, and the orbit-stabilizer theorem gives the size of each class. The sum of the sizes is the order of the group. This is the class equation. It separates the center, whose classes have one element, from the rest.

For a group whose order is a power of a prime $p$, each class outside the center has a size divisible by $p$. This simple remark has strong consequences: a nontrivial $p$-group has a nontrivial center, and a group of order $p^2$ is commutative. The same argument proves a congruence for any action of a $p$-group, which is the key step in the proofs of Cauchy's theorem and of the Sylow theorems in Chapter 8. The section ends with Burnside's lemma, which counts orbits.

### Definitions

**Definition (Conjugacy class).** Elements $x, y \in G$ are conjugate if $y = g x g^{-1}$ for some $g \in G$. The conjugacy class of $x$ is $\operatorname{cl}(x) = \{g x g^{-1} : g \in G\}$.

::: mathlib
`IsConj` · `Mathlib.Algebra.Group.Conj`

The relation `IsConj a b`: there is a unit `c` with `SemiconjBy c a b`, that is, `c * a = b * c`. In a group this is `∃ c, c * a * c⁻¹ = b`, by `isConj_iff`. The type of the classes is `ConjClasses G`.

<?decl IsConj?>
:::

**Definition (Centralizer).** The centralizer of $x$ is $C(x) = \{g \in G : g x = x g\}$. It is a subgroup, and $Z(G) = \bigcap_x C(x)$.

**Definition (Conjugation action).** The group $G$ acts on the set $G$ by $g \cdot x = g x g^{-1}$. The axioms hold by the theorem on conjugation of Chapter 2. The orbit of $x$ is $\operatorname{cl}(x)$ and the stabilizer of $x$ is $C(x)$.

::: mathlib
`ConjAct` · `Mathlib.GroupTheory.GroupAction.ConjAct`

The type synonym `ConjAct G` is a copy of `G` that acts on `G` by conjugation. A copy is needed because `G` already acts on itself by left multiplication, and one type can carry only one instance of `MulAction G G`. The maps `ConjAct.toConjAct` and `ConjAct.ofConjAct` pass between the two copies.

<?decl ConjAct?>
:::

::: mathlib
`ConjAct.smul_def` · `Mathlib.GroupTheory.GroupAction.ConjAct`

The action unfolded: `g • h = ofConjAct g * h * (ofConjAct g)⁻¹`.

<?decl ConjAct.smul_def?>
:::

::: mathlib
`ConjAct.stabilizer_eq_centralizer` · `Mathlib.GroupTheory.GroupAction.ConjAct`

The stabilizer of `g` under conjugation is the centralizer of `{g}`, written `Subgroup.centralizer`, up to the copy `toConjAct`.

<?decl ConjAct.stabilizer_eq_centralizer?>
:::

**Definition ($p$-group).** Let $p$ be a prime. A finite group is a $p$-group if its order is a power of $p$.

::: mathlib
`IsPGroup` · `Mathlib.GroupTheory.PGroup`

The predicate `IsPGroup p G` says that each element has order a power of `p`: `∀ g, ∃ k, g ^ p ^ k = 1`. This definition works for infinite groups. For a finite group it agrees with the definition above, by `IsPGroup.iff_card`; the proof of that lemma uses Cauchy's theorem of Chapter 8. The direction `IsPGroup.of_card` is easy.

<?decl IsPGroup?>
:::

**Definition (Fixed points).** For an action of $G$ on $X$, the fixed points are $X^G = \{x \in X : g \cdot x = x \text{ for each } g\}$, the points whose orbit has one element.

::: mathlib
`MulAction.fixedPoints` · `Mathlib.GroupTheory.GroupAction.Defs`

The set `fixedPoints G X`. The set of the points fixed by one element `g` is `MulAction.fixedBy X g`.

<?decl MulAction.fixedPoints?>
:::

### Theorems and proofs

**Theorem (Size of a class).** Let $G$ be finite and $x \in G$. Then $|\operatorname{cl}(x)| = [G : C(x)]$, which divides $|G|$. The class of $x$ is $\{x\}$ if and only if $x \in Z(G)$.

*Proof.* The first claim is the orbit-stabilizer theorem for the conjugation action, and the index divides $|G|$ by Lagrange's theorem. The class of $x$ is $\{x\}$ if and only if $g x g^{-1} = x$ for each $g$, that is, $g x = x g$ for each $g$, that is, $x \in Z(G)$. $\square$

**Theorem (Class equation).** Let $G$ be finite, and let $x_1, \ldots, x_k$ be one element from each conjugacy class with more than one element. Then
$$|G| = |Z(G)| + \sum_{i=1}^{k} [G : C(x_i)],$$
and each index $[G : C(x_i)]$ is a divisor of $|G|$ greater than $1$.

*Proof.* The classes partition $G$, because they are the orbits of an action. The classes with one element are the sets $\{z\}$ with $z \in Z(G)$, by the last theorem, and together they contain $|Z(G)|$ elements. The other classes are $\operatorname{cl}(x_1), \ldots, \operatorname{cl}(x_k)$, of sizes $[G : C(x_i)] > 1$. $\square$

::: mathlib
`Group.card_center_add_sum_card_noncenter_eq_card` · `Mathlib.GroupTheory.ClassEquation`

The class equation with `Fintype.card`: the order of the center plus the sum of the sizes of the classes in `ConjClasses.noncenter G` is the order of `G`. The form with `Nat.card` and `Finite` is `Group.nat_card_center_add_sum_card_noncenter_eq_card`.

<?decl Group.card_center_add_sum_card_noncenter_eq_card?>
:::

**Theorem (Fixed point congruence).** Let $P$ be a group of order $p^n$, with $p$ prime, that acts on a finite set $X$. Then $|X| \equiv |X^P| \pmod p$.

*Proof.* The orbits partition $X$. Each orbit has a size that divides $|P| = p^n$, by orbit-stabilizer, so the size is $1$ or a multiple of $p$. The orbits of size $1$ are the sets $\{x\}$ with $x \in X^P$. So $|X| = |X^P| + (\text{a sum of multiples of } p)$. $\square$

::: mathlib
`IsPGroup.card_modEq_card_fixedPoints` · `Mathlib.GroupTheory.PGroup`

The congruence `Nat.card X ≡ Nat.card (fixedPoints G X) [MOD p]`, for a $p$-group `G` and a finite `X`. The group need not be finite: it is enough that each element has order a power of `p`, since the orbits are finite.

<?decl IsPGroup.card_modEq_card_fixedPoints?>
:::

**Theorem (Center of a $p$-group).** Let $P$ be a group of order $p^n$ with $n \ge 1$. Then $Z(P) \ne \{1\}$, and $p$ divides $|Z(P)|$.

*Proof.* Apply the congruence to the conjugation action of $P$ on itself. The fixed points are the elements $x$ with $g x g^{-1} = x$ for each $g$, that is, the center. So $|Z(P)| \equiv |P| = p^n \equiv 0 \pmod p$. Since $1 \in Z(P)$, the number $|Z(P)|$ is positive, so it is at least $p$. $\square$

::: mathlib
`IsPGroup.center_nontrivial` · `Mathlib.GroupTheory.PGroup`

The theorem: a nontrivial finite $p$-group has a `Nontrivial` center. The form with the order of subgroups is `IsPGroup.bot_lt_center`.

<?decl IsPGroup.center_nontrivial?>
:::

**Theorem (Groups of order $p^2$).** A group of order $p^2$, with $p$ prime, is commutative.

*Proof.* Let $|G| = p^2$ and $Z = Z(G)$. By the last theorem $|Z|$ is $p$ or $p^2$. Assume $|Z| = p$. Then $G/Z$ has order $p$, so it is cyclic by Chapter 4, with a generator $g Z$. Each element of $G$ is in some coset $g^i Z$, so it has the form $g^i z$ with $z \in Z$. Let $a = g^i z$ and $b = g^j z'$. Since $z$ and $z'$ commute with each element,
$$a b = g^i g^j z z' = g^{i + j} z z' = g^j g^i z' z = b a.$$
So $G$ is commutative and $Z = G$, which contradicts $|Z| = p$. So $|Z| = p^2$ and $G = Z$ is commutative. $\square$

::: mathlib
`IsPGroup.commGroupOfCardEqPrimeSq` · `Mathlib.GroupTheory.PGroup`

The theorem as a structure: a `CommGroup` instance on a group with `Nat.card G = p ^ 2`. The statement as a property is `IsPGroup.isMulCommutative_of_card_eq_prime_sq`. An older lemma named `IsPGroup.commutative_of_card_eq_prime_sq` is deprecated.

<?decl IsPGroup.commGroupOfCardEqPrimeSq?>
:::

**Theorem (Burnside's lemma).** Let a finite group $G$ act on a finite set $X$, and let $\operatorname{Fix}(g) = \{x : g \cdot x = x\}$. The number of orbits is
$$\frac{1}{|G|} \sum_{g \in G} |\operatorname{Fix}(g)|.$$

*Proof.* Count the set $S = \{(g, x) \in G \times X : g \cdot x = x\}$ in two ways. By $g$: $|S| = \sum_g |\operatorname{Fix}(g)|$. By $x$: $|S| = \sum_x |G_x| = \sum_x |G| / |G x|$, by orbit-stabilizer. Group the points by orbits. For an orbit $O$, each $x \in O$ has $|G x| = |O|$, so the points of $O$ contribute $|O| \cdot |G|/|O| = |G|$. So $|S| = |G| \cdot (\text{number of orbits})$. $\square$

::: mathlib
`MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group` · `Mathlib.GroupTheory.GroupAction.Quotient`

Burnside's lemma without division: the sum of the sizes of the sets `fixedBy X g` is the number of orbits times the order of `G`.

<?decl MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group?>
:::

### Examples

**Example (Class equation of $S_3$).** The center of $S_3$ is $\{e\}$: a transposition does not commute with a $3$-cycle, and the two $3$-cycles do not commute with a transposition. The classes are $\{e\}$, the three transpositions and the two $3$-cycles, so $6 = 1 + 3 + 2$. For a transposition $t$, $C(t) = \{e, t\}$ has index $3$; for a $3$-cycle $c$, $C(c) = A_3$ has index $2$.

**Example (Class equation of $D_4$).** From $r s r^{-1} = s r^2$, $s r s^{-1} = r^3$ and $r (s r) r^{-1} = s r^3$, the classes of $D_4$ are
$$\{1\}, \ \{r^2\}, \ \{r, r^3\}, \ \{s, s r^2\}, \ \{s r, s r^3\}.$$
So $8 = 2 + 2 + 2 + 2$, with center $\{1, r^2\}$ of order $2$. This agrees with the theorem on $p$-groups for $p = 2$.

**Example (Necklaces).** Count the necklaces of $4$ beads in $2$ colours, where two necklaces are the same if a rotation maps one to the other. The group $\mathbb{Z}/4$ of rotations acts on the $2^4 = 16$ colourings. The rotation by $0$ fixes $16$. The rotations by $1$ and by $3$ fix only the $2$ constant colourings. The rotation by $2$ fixes the colourings with bead $1$ equal to bead $3$ and bead $2$ equal to bead $4$, which are $4$. Burnside's lemma gives $(16 + 2 + 4 + 2)/4 = 6$ necklaces: all white, all black, one black, three black, two adjacent black, and two opposite black.

**Counterexample (The theorems need prime powers).** The group $S_3$ has order $6$, not a prime power, and its center is trivial. So the theorem on the center fails for other orders. The group $D_4$ has order $8 = 2^3$ and is not commutative. So the theorem on order $p^2$ does not extend to $p^3$.

**Counterexample (No congruence for other orders).** Let $S_3$ act on itself by conjugation. Then $|X| = 6$ and the fixed points are the center, so $|X^G| = 1$. For $p = 2$ and for $p = 3$, $6 \equiv 0 \not\equiv 1 \pmod p$. The congruence needs orbit sizes that are powers of one prime, and here the orbits have sizes $1$, $2$ and $3$.

### The library around it

The center and the centralizer have their own files, `Mathlib.GroupTheory.Subgroup.Center` and `Mathlib.GroupTheory.Subgroup.Centralizer`. The theory of $p$-groups in `Mathlib.GroupTheory.PGroup` also has `IsPGroup.index` and `IsPGroup.card_orbit`, the facts that indices and orbit sizes in a $p$-group are powers of $p$, and `IsPGroup.to_subgroup` and `IsPGroup.map` for subgroups and images. The nilpotent groups, which generalize finite $p$-groups, are in `Mathlib.GroupTheory.Nilpotent`. The conjugacy classes of a symmetric group are described by cycle types in Chapter 7.

Common errors of a learner:

- The action of `G` on itself in Mathlib is left multiplication. A conjugation statement must use `ConjAct G`, or `MulAut.conj`.
- `IsPGroup p G` does not assume that `p` is prime. Most lemmas ask for `[Fact p.Prime]`.
- The class equation counts classes outside the center. Each such class has more than one element, so the sum has no term equal to $1$.

### Exercises

1. (A) Write the class equation of $\mathbb{Z}/2 \times S_3$.
2. (A) Show that a group of order $25$ is isomorphic to $\mathbb{Z}/25$ or to $\mathbb{Z}/5 \times \mathbb{Z}/5$.
3. (B) Show that a group of order $p^n$ has a normal subgroup of order $p^k$ for each $0 \le k \le n$. Hint: use induction, with a subgroup of order $p$ in the center.
4. (B) Show that no group of order $10$ has a center of order $2$ or $5$. Hint: the quotient by the center would be cyclic.
5. (B) Count the necklaces of $6$ beads in $3$ colours up to rotation.
6. (C) Let $N \trianglelefteq P$ with $N \ne \{1\}$ and $|P| = p^n$. Show that $N \cap Z(P) \ne \{1\}$. Hint: $P$ acts on $N$ by conjugation.

### Notes and history

The counting of conjugates goes back to Cauchy and to Sylow, and Frobenius used the class equation in 1887 in his new proof of the Sylow theorems. Sylow proved in 1872 that a group of order $p^n$ is solvable, by an argument close to the theorem on the center. The orbit counting lemma is often called the lemma of Burnside, who gave it in his book of 1897. It was known to Cauchy in 1845 and to Frobenius in 1887, so some authors call it the lemma that is not Burnside's. Pólya extended it in 1937 to count colourings with weights.

In Mathlib, the type synonym `ConjAct` follows a general pattern: a new type with the same elements carries a second instance. The same pattern gives `Multiplicative`, `Additive` and `MulOpposite`.

### Reference

<?reference?>
