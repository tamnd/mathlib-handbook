---
title: Group actions, orbits and stabilizers
kind: theory
modules:
  - Mathlib.Algebra.Group.Action.Defs
  - Mathlib.GroupTheory.GroupAction.Defs
  - Mathlib.GroupTheory.GroupAction.Quotient
explains:
  E3: [MulAction.card_orbit_mul_card_stabilizer_eq_card_group]
  E2: [MulAction, MulAction.orbit, MulAction.stabilizer, MulAction.mem_orbit_iff, MulAction.mem_stabilizer_iff, MulAction.orbitEquivQuotientStabilizer, MulAction.orbitRel, MulAction.toPermHom, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  E1: auto
families: []
requires: [V05.C04]
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

## Group actions, orbits and stabilizers

### Overview

Groups arise as groups of symmetries: the rotations of a cube, the permutations of a set, the invertible linear maps of a space. A group action makes this precise. It is a rule by which each element of a group $G$ moves the points of a set $X$. An action splits $X$ into orbits, and it gives each point a stabilizer, the subgroup of the elements that fix it. The orbit-stabilizer theorem relates the two: the size of an orbit is the index of the stabilizer.

This theorem is the main counting tool of finite group theory. The next section applies it to the action of $G$ on itself by conjugation, which gives the class equation. Chapter 8 applies it to actions on sets of subgroups and of cosets, which gives the Sylow theorems.

### Definitions

**Definition (Action).** An action of a group $G$ on a set $X$ is a map $G \times X \to X$, $(g, x) \mapsto g \cdot x$, with $1 \cdot x = x$ and $g \cdot (h \cdot x) = (g h) \cdot x$ for all $g, h \in G$ and $x \in X$.

::: mathlib
`MulAction` · `Mathlib.Algebra.Group.Action.Defs`

The class `MulAction G X` gives the notation `g • x`, with the axioms `one_smul` and `SemigroupAction.mul_smul`; `MulAction` extends `SemigroupAction`. The form `smul_smul : g • h • x = (g * h) • x` is the second axiom read from left to right. It needs only a monoid `G`. The additive form is `AddAction`, with the notation `g +ᵥ x`.

<?decl MulAction?>
:::

**Definition (Orbit and stabilizer).** Let $G$ act on $X$ and let $x \in X$. The orbit of $x$ is $G x = \{g \cdot x : g \in G\}$. The stabilizer of $x$ is $G_x = \{g \in G : g \cdot x = x\}$.

::: mathlib
`MulAction.orbit` · `Mathlib.GroupTheory.GroupAction.Defs`

The orbit as a set, `MulAction.orbit G x : Set X`. It is the range of the map `fun g => g • x`.

<?decl MulAction.orbit?>
:::

::: mathlib
`MulAction.mem_orbit_iff` · `Mathlib.GroupTheory.GroupAction.Defs`

The membership: `y ∈ orbit G x ↔ ∃ g, g • x = y`. The lemma `MulAction.mem_orbit_self` gives `x ∈ orbit G x`.

<?decl MulAction.mem_orbit_iff?>
:::

::: mathlib
`MulAction.stabilizer` · `Mathlib.GroupTheory.GroupAction.Defs`

The stabilizer as a `Subgroup G`, when `G` is a group. For a monoid there is `MulAction.stabilizerSubmonoid`.

<?decl MulAction.stabilizer?>
:::

::: mathlib
`MulAction.mem_stabilizer_iff` · `Mathlib.GroupTheory.GroupAction.Defs`

The membership: `g ∈ stabilizer G x ↔ g • x = x`. It is a `simp` lemma.

<?decl MulAction.mem_stabilizer_iff?>
:::

**Definition (Transitive and faithful).** The action is transitive if $X$ is one orbit. It is faithful if only $g = 1$ fixes each point. The kernel of the action is the set of the $g$ that fix each point.

In Mathlib these are the classes `MulAction.IsPretransitive` and `FaithfulSMul`. The prefix "pre" means that $X$ may be empty.

### Theorems and proofs

**Theorem (Actions are homomorphisms).** Let $G$ act on $X$. For $g \in G$, the map $\sigma_g : X \to X$, $x \mapsto g \cdot x$, is a bijection, and $g \mapsto \sigma_g$ is a homomorphism $G \to \operatorname{Sym}(X)$. Its kernel is the kernel of the action. Conversely, each homomorphism $\rho : G \to \operatorname{Sym}(X)$ gives an action $g \cdot x = \rho(g)(x)$.

*Proof.* The axioms give $\sigma_g \circ \sigma_{g^{-1}} = \sigma_{g g^{-1}} = \sigma_1 = \mathrm{id}$, and also $\sigma_{g^{-1}} \circ \sigma_g = \mathrm{id}$. So $\sigma_g$ is a bijection with inverse $\sigma_{g^{-1}}$. The second axiom says $\sigma_g \circ \sigma_h = \sigma_{g h}$, so $g \mapsto \sigma_g$ is a homomorphism. Its kernel is the set of the $g$ with $\sigma_g = \mathrm{id}$, which is the kernel of the action. For the converse, $\rho(1) = \mathrm{id}$ and $\rho(g) \circ \rho(h) = \rho(g h)$ are the two axioms. $\square$

::: mathlib
`MulAction.toPermHom` · `Mathlib.Algebra.Group.Action.End`

The homomorphism `G →* Equiv.Perm X` of the theorem. The single bijection $\sigma_g$ is `MulAction.toPerm g`. The action is faithful exactly when this map is injective, by `MulAction.toPerm_injective` in one direction.

<?decl MulAction.toPermHom?>
:::

**Theorem (Orbits partition the set).** The relation $x \sim y$ if $y \in G x$ is an equivalence relation on $X$. Its classes are the orbits. So two orbits are equal or disjoint.

*Proof.* Reflexive: $x = 1 \cdot x$. Symmetric: if $y = g \cdot x$, then $g^{-1} \cdot y = (g^{-1} g) \cdot x = x$. Transitive: if $y = g \cdot x$ and $z = h \cdot y$, then $z = (h g) \cdot x$. The class of $x$ is the set of the $y$ with $y \in G x$, which is $G x$. $\square$

::: mathlib
`MulAction.orbitRel` · `Mathlib.GroupTheory.GroupAction.Defs`

The relation as a `Setoid X`. The type of orbits is `MulAction.orbitRel.Quotient G X`. The equivalence `MulAction.selfEquivSigmaOrbits` writes `X` as the disjoint union of its orbits, which is the form used to count.

<?decl MulAction.orbitRel?>
:::

**Theorem (Stabilizers).** Each stabilizer $G_x$ is a subgroup of $G$. Points of the same orbit have conjugate stabilizers: $G_{g \cdot x} = g G_x g^{-1}$.

*Proof.* $1 \cdot x = x$. If $g \cdot x = x$ and $h \cdot x = x$, then $(g h) \cdot x = g \cdot (h \cdot x) = x$ and $g^{-1} \cdot x = g^{-1} \cdot (g \cdot x) = x$. For the second claim, let $k \in G_x$. Then $(g k g^{-1}) \cdot (g \cdot x) = g \cdot (k \cdot x) = g \cdot x$, so $g G_x g^{-1} \subseteq G_{g \cdot x}$. Apply this to the point $g \cdot x$ and the element $g^{-1}$: $g^{-1} G_{g \cdot x} g \subseteq G_x$, which gives the other inclusion. $\square$

::: mathlib
`MulAction.stabilizer_smul_eq_stabilizer_map_conj` · `Mathlib.GroupTheory.GroupAction.Basic`

The second claim: the stabilizer of `g • x` is the image of the stabilizer of `x` under `MulAut.conj g`.

<?decl MulAction.stabilizer_smul_eq_stabilizer_map_conj?>
:::

**Theorem (Orbit-stabilizer).** Let $G$ act on $X$ and let $x \in X$. The map $\Phi : G/G_x \to G x$, $\Phi(g G_x) = g \cdot x$, is a well defined bijection from the left cosets of $G_x$ to the orbit. So $|G x| = [G : G_x]$, and if $G$ is finite, then
$$|G x| \cdot |G_x| = |G|.$$

*Proof.* For $g, h \in G$:
$$g \cdot x = h \cdot x \iff (g^{-1} h) \cdot x = x \iff g^{-1} h \in G_x \iff g G_x = h G_x.$$
The first step applies $g^{-1}$ to both sides, or $g$ in the other direction. The last step is the theorem on cosets of Chapter 4. Read from right to left, the chain says that $\Phi$ is well defined. Read from left to right, it says that $\Phi$ is injective. It is onto, since each point of the orbit is some $g \cdot x = \Phi(g G_x)$. So $|G x|$ is the number of cosets, $[G : G_x]$. For finite $G$, Lagrange's theorem gives $[G : G_x] \cdot |G_x| = |G|$. $\square$

::: mathlib
`MulAction.orbitEquivQuotientStabilizer` · `Mathlib.GroupTheory.GroupAction.Quotient`

The bijection of the theorem, as an equivalence of types between `orbit G x` and `G ⧸ stabilizer G x`. The lemma `MulAction.index_stabilizer` gives the form with the index.

<?decl MulAction.orbitEquivQuotientStabilizer?>
:::

::: mathlib
`MulAction.card_orbit_mul_card_stabilizer_eq_card_group` · `Mathlib.GroupTheory.GroupAction.Quotient`

The counting form: `card (orbit G x) * card (stabilizer G x) = card G`, with `Fintype` instances for the three types.

<?decl MulAction.card_orbit_mul_card_stabilizer_eq_card_group?>
:::

**Corollary (Orbit sizes divide).** If $G$ is finite, the size of each orbit divides $|G|$. If $X$ is finite with orbits $G x_1, \ldots, G x_k$, then $|X| = \sum_{i=1}^{k} [G : G_{x_i}]$.

*Proof.* The first claim is the theorem with Lagrange's theorem. The second claim follows because the orbits partition $X$. $\square$

**Theorem (Cayley).** Each group $G$ is isomorphic to a subgroup of $\operatorname{Sym}(G)$. A group of order $n$ is isomorphic to a subgroup of $S_n$.

*Proof.* The group $G$ acts on itself by $g \cdot x = g x$: this is associativity and the unit axiom. The action is faithful, because $g \cdot 1 = g$, so only $g = 1$ fixes $1$. So the homomorphism $G \to \operatorname{Sym}(G)$ is injective, and $G$ is isomorphic to its range by the first isomorphism theorem. If $|G| = n$, a bijection $G \to \{1, \ldots, n\}$ identifies $\operatorname{Sym}(G)$ with $S_n$. $\square$

**Theorem (Action on cosets).** Let $H \le G$ have index $n$. Then $G$ acts on $G/H$ by $g \cdot (x H) = (g x) H$. This gives a homomorphism $\rho : G \to \operatorname{Sym}(G/H) \cong S_n$ with $\ker \rho \le H$.

*Proof.* The rule is well defined: if $x H = y H$, then $x^{-1} y \in H$, and $(g x)^{-1}(g y) = x^{-1} y \in H$. The axioms hold by associativity. If $g \in \ker \rho$, then $g H = H$, so $g \in H$. $\square$

### Examples

**Example (Symmetric groups and dihedral groups).** The group $S_n$ acts on $\{1, \ldots, n\}$ by $\sigma \cdot i = \sigma(i)$. The action is transitive. The stabilizer of $n$ is the group of the permutations of $\{1, \ldots, n-1\}$, a copy of $S_{n-1}$. The theorem gives $n \cdot (n-1)! = n!$. The group $D_n$ acts on the $n$ vertices of the regular $n$-gon, transitively. The stabilizer of a vertex is $\{1, t\}$, where $t$ is the reflection in the line through that vertex and the center. So $|D_n| = n \cdot 2 = 2 n$.

**Example (Rotations of the cube).** Let $G$ be the group of rotations of a cube. It acts on the $6$ faces, transitively. The stabilizer of the top face is the group of the $4$ rotations about the vertical axis. So $|G| = 6 \cdot 4 = 24$. With the $8$ vertices instead, the stabilizer of a vertex has the $3$ rotations about a long diagonal, and $8 \cdot 3 = 24$ again.

**Example (Conjugation and cosets).** The group $G$ acts on itself by conjugation, $g \cdot x = g x g^{-1}$. The axioms are $c_1 = \mathrm{id}$ and $c_g c_h = c_{g h}$ of Chapter 2. The orbits are the conjugacy classes and the stabilizer of $x$ is the centralizer of $x$; the next section studies them. The action of $S_3$ on the cosets of $H = \{e, (1\,2)\}$ has kernel $\{e\}$: the kernel is a normal subgroup inside $H$, and $H$ is not normal. So $S_3 \to \operatorname{Sym}(S_3/H) \cong S_3$ is an isomorphism.

**Counterexample (Right multiplication is not a left action).** The rule $g \cdot x = x g$ fails the second axiom when $G$ is not commutative: $g \cdot (h \cdot x) = x h g$, while $(g h) \cdot x = x g h$. In $S_3$, with $x = e$, $g = (1\,2)$ and $h = (1\,3)$, the two sides are $(1\,3)(1\,2) = (1\,2\,3)$ and $(1\,2)(1\,3) = (1\,3\,2)$. The rule $g \cdot x = x g^{-1}$ is a left action.

**Counterexample (Orbit-stabilizer with an infinite group).** The group $(\mathbb{Z}, +)$ acts on $\mathbb{Z}/5$ by $n \cdot x = x + n$. There is one orbit, of size $5$, and the stabilizer of each point is $5\mathbb{Z}$. The bijection $\mathbb{Z}/5\mathbb{Z} \to \mathbb{Z}/5$ holds, but the product formula has no meaning: $|G_x|$ and $|G|$ are infinite. Only the index form $|G x| = [G : G_x]$ survives.

**Example (An action in Lean).**

<?lean MathlibHandbook/V05/C06/Examples.lean#action?>

**Example (Orbits in Lean).**

<?lean MathlibHandbook/V05/C06/Examples.lean#orbit?>

**Example (Stabilizers in Lean).**

<?lean MathlibHandbook/V05/C06/Examples.lean#stabilizer?>

**Example (The orbit-stabilizer theorem in Lean).**

<?lean MathlibHandbook/V05/C06/Examples.lean#orbit_stabilizer?>

**Example (The regular action).**

<?lean MathlibHandbook/V05/C06/Examples.lean#regular?>

### The library around it

The instance `Monoid.toMulAction` makes each monoid act on itself by left multiplication, so `g • x = g * x` for `g x : G` by `smul_eq_mul`. The conjugation action uses the type `ConjAct G` of the next section, to avoid a clash with this instance. The action on cosets is the instance `MulAction.quotient`, and Cayley's theorem is `Equiv.Perm.subgroupOfMulAction`. Fixed points and the sets fixed by one element are `MulAction.fixedPoints` and `MulAction.fixedBy`.

Common errors of a learner:

- `g • x` and `g * x` are different terms even when `X = G`. Rewrite with `smul_eq_mul` to pass from one to the other.
- `MulAction.orbit G x` is a `Set X`. Its cardinality needs a `Fintype` instance on the subtype, or the use of `Nat.card`.
- The stabilizer depends on the action. When two actions of `G` on `X` are in scope, the instance search chooses one, and type synonyms such as `ConjAct G` select the other.

### Exercises

1. (A) Show that $\mathrm{GL}_2(\mathbb{R})$ acts on $\mathbb{R}^2$ and find the orbits.
2. (A) Find the orbits and the stabilizers of the action of $\langle (1\,2\,3) \rangle$ on $\{1, 2, 3, 4\}$.
3. (B) Use the action on the $12$ edges of a cube to recompute the order of its rotation group.
4. (B) Let $H \le G$ with $[G : H] = n$ and $|G|$ not a divisor of $n!$. Show that $G$ has a normal subgroup $N \ne \{1\}$ with $N \le H$. Hint: use the action on cosets.
5. (L) Prove that $x$ is in its orbit. The solution is `mem_orbit_self_example`.
6. (L) Prove that $g \cdot x$ is in the orbit of $x$. The solution is `smul_mem_orbit_example`.
7. (L) Prove that $1$ is in the stabilizer of $x$. The solution is `one_mem_stabilizer_example`.
8. (C) Let $G$ be finite and let $p$ be the least prime that divides $|G|$. Show that a subgroup of index $p$ is normal. Hint: the image of $G$ in $S_p$ has order dividing $p!$ and $|G|$.

### Notes and history

Cayley proved in 1854 that each group is a group of permutations, in the paper that defined abstract groups. Jordan used actions on sets in his Traité of 1870, and the orbit-stabilizer theorem appears there in the form of the counting of the values of functions under permutations. Frobenius made actions of groups a central tool in the 1880s. The word "orbit" comes from the study of transformation groups in geometry.

In Mathlib, `MulAction` is a class over the notation `•`. The same notation serves for scalar multiplication in modules, which are additive groups with an action of a ring, so the theory of this section applies to them without change.

### Reference

<?reference?>
