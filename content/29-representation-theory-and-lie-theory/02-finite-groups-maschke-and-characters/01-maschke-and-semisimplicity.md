---
title: Maschke's theorem and semisimplicity
kind: theory
modules:
  - Mathlib.RepresentationTheory.Maschke
  - Mathlib.RepresentationTheory.Semisimple
  - Mathlib.RepresentationTheory.Irreducible
  - Mathlib.RepresentationTheory.FinGroupCharZero
explains:
  E3: [LinearMap.equivariantProjection, LinearMap.equivariantProjection_condition, MonoidAlgebra.exists_leftInverse_of_injective, MonoidAlgebra.Submodule.exists_isCompl, Representation.IsSemisimpleRepresentation, Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule, Representation.IsIrreducible, Representation.irreducible_iff_isSimpleModule_asModule, Representation.IsIrreducible.bijective_or_eq_zero, Representation.IsIrreducible.finrank_intertwiningMap_self, Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative, FDRep.simple_iff_end_is_rank_one]
  E2: [LinearMap.conjugate, LinearMap.conjugate_i, LinearMap.sumOfConjugates, LinearMap.sumOfConjugatesEquivariant, LinearMap.equivariantProjection_apply, MonoidAlgebra.Submodule.instIsSemisimpleModule, MonoidAlgebra.Submodule.instIsSemisimpleRepresentation, MonoidAlgebra.Submodule.instIsSemisimpleRingAddMonoidAlgebra, Representation.isSemisimpleModule_iff_isSemisimpleRepresentation_ofModule, Representation.isSimpleModule_iff_irreducible_ofModule, Representation.IsIrreducible.injective_or_eq_zero, Representation.IsIrreducible.surjective_or_eq_zero, Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed, Representation.IsIrreducible.instSubsingletonIntertwiningMapOfIsEmptyEquiv, Rep.instInjective, Rep.instProjective, FDRep.instInjectiveOfNeZeroCastCard, FDRep.instProjectiveOfNeZeroCastCard]
  E1: auto
families: []
requires: [V29.C01, V07.C02, V07.C05, V25.C02, V26.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Maschke's theorem and semisimplicity

### Overview

A representation is often too large to study as a whole, so the first task is to cut it into pieces. A subrepresentation $U \subseteq V$ is a piece, and the question is whether $V$ splits as $U \oplus U'$ with $U'$ also a subrepresentation. For a finite group whose order is invertible in the field, the answer is always yes. This is the theorem of Maschke, and its proof is the averaging trick of Chapter 1: take any linear complement and average the projection over the group.

The consequences fill this section. Each finite dimensional representation is a direct sum of irreducible ones, the group algebra is a semisimple ring, and each object of `Rep k G` is projective and injective. The lemma of Schur then controls the maps between irreducible pieces: a nonzero map between irreducibles is an isomorphism, and over an algebraically closed field the endomorphisms of an irreducible representation are the scalars. Two examples show that the hypotheses are needed: the order must be invertible, and the field must be algebraically closed for the scalar form of Schur.

In this section $k$ is a field, $G$ a group and $V$, $W$ representations of $G$ over $k$. The hypothesis "the order of $G$ is invertible in $k$" means that $G$ is finite of order $n$ with $n \ne 0$ in $k$; in Mathlib it reads `[NeZero (Nat.card G : k)]`, which forces $G$ to be finite because `Nat.card` of an infinite type is $0$.

### Definitions

**Definition (Irreducible representation).** A representation $V$ is irreducible if $V \ne 0$ and the only subrepresentations are $0$ and $V$. Mathlib states this as `IsSimpleOrder (Subrepresentation ρ)`.

**Definition (Semisimple representation).** A representation $V$ is semisimple if each subrepresentation $U$ has a complement: a subrepresentation $U'$ with $U \cap U' = 0$ and $U + U' = V$. Mathlib states this as `ComplementedLattice (Subrepresentation ρ)`.

**Definition (Conjugate of a linear map).** For $k[G]$-modules $V$, $W$, a $k$-linear map $\pi \colon W \to V$ and $g \in G$, the conjugate is $\pi^g = g^{-1} \circ \pi \circ g \colon W \to V$, where $g$ denotes the action of $g$ on each module.

**Definition (Equivariant projection).** If $G$ has order $n$ invertible in $k$, the equivariant projection of $\pi$ is $P = \frac{1}{n} \sum_{g \in G} \pi^g$.

### Theorems and proofs

**Lemma (The averaged map is equivariant).** Let $G$ be finite. For each $k$-linear $\pi \colon W \to V$, the sum $S = \sum_{g} \pi^g$ is $k[G]$-linear. If $i \colon V \to W$ is $k[G]$-linear with $\pi \circ i = \mathrm{id}_V$, then $\pi^g \circ i = \mathrm{id}_V$ for each $g$, and if $n$ is invertible, the equivariant projection satisfies $P \circ i = \mathrm{id}_V$.

*Proof.* Fix $h \in G$ and $w \in W$. Then
$$S(hw) = \sum_g g^{-1} \pi(g h w) = \sum_{g'} h g'^{-1} \pi(g' w) = h S(w),$$
with the substitution $g' = gh$, so that $g^{-1} = h g'^{-1}$; the map $g \mapsto gh$ is a bijection of $G$. A $k$-linear map that commutes with each $h$ is $k[G]$-linear by Chapter 1. For the second claim, $\pi^g(i(v)) = g^{-1}\pi(g\,i(v)) = g^{-1}\pi(i(gv)) = g^{-1} g v = v$, since $i$ commutes with $g$. Summing over $G$ gives $S \circ i = n \cdot \mathrm{id}_V$, and so $P \circ i = \frac{1}{n} S \circ i = \mathrm{id}_V$. $\square$

**Theorem (Maschke).** Let $G$ be a finite group whose order $n$ is invertible in the field $k$. Each injective $k[G]$-linear map $i \colon V \to W$ has a $k[G]$-linear left inverse. In particular each $k[G]$-submodule of $W$ has a complementary $k[G]$-submodule, and each representation of $G$ over $k$ is semisimple.

*Proof.* Since $k$ is a field, the injective $k$-linear map $i$ has a $k$-linear left inverse $\pi$: extend a basis of $i(V)$ to a basis of $W$ and send the new basis vectors to $0$ (Volume 7, Chapter 2). The lemma turns $\pi$ into a $k[G]$-linear $P$ with $P \circ i = \mathrm{id}_V$. For a submodule $U \subseteq W$, apply this to the inclusion $i \colon U \to W$ to get $P$, and put $U' = \ker P$. Each $w$ is $iP(w) + (w - iP(w))$, with $P(w - iP(w)) = P(w) - P(w) = 0$, so $W = U + U'$; if $u \in U \cap U'$ then $u = P(i(u)) = 0$. So $U'$ is a complement, and it is a $k[G]$-submodule because $P$ is $k[G]$-linear. By Chapter 1, subrepresentations are $k[G]$-submodules, so each representation is semisimple. $\square$

**Proposition (Semisimple representations and modules).** A representation $\rho$ is semisimple, or irreducible, if and only if the $k[G]$-module $\rho.\mathrm{asModule}$ is semisimple, or simple.

*Proof.* Chapter 1 gives an order isomorphism between the lattice of subrepresentations of $\rho$ and the lattice of $k[G]$-submodules of the module. An order isomorphism preserves bottom, top, meet and join, so it preserves the property that each element has a complement, and the property that there are exactly two elements $0 \neq V$ and nothing between. $\square$

**Corollary (Decomposition into irreducibles).** If the order of $G$ is invertible in $k$, each finite dimensional representation $V$ is a direct sum $V_1 \oplus \dots \oplus V_r$ of irreducible subrepresentations.

*Proof.* Induct on $\dim V$. If $V = 0$, take $r = 0$. Otherwise choose a nonzero subrepresentation $V_1$ of least dimension; it is irreducible, since a proper nonzero subrepresentation of $V_1$ would have smaller dimension. By Maschke, $V = V_1 \oplus V'$ with $V'$ a subrepresentation of smaller dimension, and the induction hypothesis splits $V'$. $\square$

**Corollary (Projective and injective objects).** If the order of $G$ is invertible in $k$, the ring $k[G]$ is semisimple, and each object of $\mathbf{Rep}_k(G)$ and of $\mathbf{FDRep}_k(G)$ is projective and injective.

*Proof.* The module $k[G]$ over itself is semisimple by Maschke, so $k[G]$ is a semisimple ring. Over a semisimple ring, each short exact sequence of modules splits, because the kernel has a complement; so each module is projective and injective. The equivalence $\mathbf{Rep}_k(G) \simeq \mathrm{Mod}_{k[G]}$ of Chapter 1 preserves these properties. For $\mathbf{FDRep}$, the forgetful functor to $\mathbf{Rep}$ is fully faithful and preserves and reflects epimorphisms and monomorphisms, and a lifting problem in $\mathbf{FDRep}$ is solved by its solution in $\mathbf{Rep}$. $\square$

**Theorem (Lemma of Schur).** Let $f \colon V \to W$ be an intertwining map.

1. If $V$ is irreducible, then $f$ is injective or $f = 0$.
2. If $W$ is irreducible, then $f$ is surjective or $f = 0$.
3. If both are irreducible, then $f$ is bijective or $f = 0$. If $V$ and $W$ are not equivalent, then $\mathrm{Hom}_G(V, W) = 0$.
4. If $V$ is irreducible and finite dimensional and $k$ is algebraically closed, then $k \to \mathrm{End}_G(V)$, $c \mapsto c \cdot \mathrm{id}$, is bijective, so $\dim_k \mathrm{End}_G(V) = 1$.

*Proof.* The kernel of $f$ is a subrepresentation of $V$. If $V$ is irreducible it is $0$ or $V$, which gives $f$ injective or $f = 0$. The image of $f$ is a subrepresentation of $W$; if $W$ is irreducible it is $0$ or $W$, which gives the second claim. The third claim combines the first two, and a bijective intertwining map is an equivalence by Chapter 1. For the fourth claim, $c \mapsto c \cdot \mathrm{id}$ is injective because $V \ne 0$. Let $f \in \mathrm{End}_G(V)$. The characteristic polynomial of $f$ has a root $\lambda$ in the algebraically closed field $k$, so $f - \lambda\,\mathrm{id}$ is an intertwining map with nonzero kernel. By the first claim it is $0$, and $f = \lambda\,\mathrm{id}$. $\square$

**Corollary (Irreducibles of abelian groups).** Let $G$ be commutative, $k$ algebraically closed and $V$ a finite dimensional irreducible representation. Then $\dim V = 1$.

*Proof.* For $h \in G$, the map $\rho(h)$ is an intertwining map, because $\rho(h)\rho(g) = \rho(hg) = \rho(gh) = \rho(g)\rho(h)$. By Schur it is a scalar $c_h$. Then each line of $V$ is stable under each $\rho(h)$, so each line is a subrepresentation. Since $V \ne 0$ has a line and $V$ is irreducible, $V$ is that line. $\square$

**Theorem (Simplicity from endomorphisms).** Let $k$ be algebraically closed with the order of $G$ invertible in $k$, and let $V$ be a finite dimensional representation. Then $V$ is irreducible if and only if $\dim_k \mathrm{End}_G(V) = 1$.

*Proof.* If $V$ is irreducible, Schur gives dimension $1$. Conversely, suppose $\dim \mathrm{End}_G(V) = 1$. Then $V \ne 0$, since $\mathrm{End}_G(0) = 0$. If $V$ is not irreducible, it has a subrepresentation $U$ with $0 \ne U \ne V$, and by Maschke $V = U \oplus U'$ with $U' \ne 0$. The projection $p$ onto $U$ along $U'$ is an intertwining map, as both summands are stable. Then $\mathrm{id}$ and $p$ are linearly independent: $a \cdot \mathrm{id} + b p = 0$ applied to a nonzero vector of $U'$ gives $a = 0$, and then applied to a nonzero vector of $U$ gives $b = 0$. So $\dim \mathrm{End}_G(V) \ge 2$, a contradiction. $\square$

### Examples

**Example (The permutation representation of $S_3$).** Over $\mathbb{Q}$, Chapter 1 splits $\mathbb{Q}^3 = \mathbb{Q}(1,1,1) \oplus W$, with $W = \{x : x_1 + x_2 + x_3 = 0\}$. The representation $W$ is irreducible. A nonzero proper subrepresentation of $W$ is a line stable under $c = (1\,2\,3)$, so it is spanned by an eigenvector of $c$ with a rational eigenvalue. On $W$ the matrix of $c$ is $\begin{pmatrix} 0 & -1 \\ 1 & -1 \end{pmatrix}$, with characteristic polynomial $x^2 + x + 1$, which has no rational root. So $\mathbb{Q}^3$ is the sum of the trivial representation and the irreducible $W$. Wedderburn's theorem identifies the semisimple ring $\mathbb{Q}[S_3]$ with $\mathbb{Q} \times \mathbb{Q} \times M_2(\mathbb{Q})$, the factors belonging to the trivial, sign and $W$ representations; the dimensions agree, $1 + 1 + 4 = 6$. The index of this edition has no declaration for the formula $\sum_i (\dim V_i)^2 = |G|$, so this identification is not a Mathlib statement.

**Counterexample (The order divisible by the characteristic).** Let $p$ be a prime and let $G = \mathbb{Z}/p$ act on $\mathbb{F}_p^2$ by $m \mapsto \begin{pmatrix} 1 & m \\ 0 & 1 \end{pmatrix}$, which is well defined because $p = 0$ in $\mathbb{F}_p$. The line $\mathbb{F}_p e_1$ is a subrepresentation. Each line stable under the generator is spanned by an eigenvector, and the only eigenvectors are the multiples of $e_1$. So the line has no complement, the representation is not semisimple, and Maschke fails because $|G| = p$ is $0$ in $\mathbb{F}_p$.

**Counterexample (An infinite group).** The same matrices for $m \in \mathbb{Z}$ give a representation of $\mathbb{Z}$ on $\mathbb{Q}^2$ with the same invariant line and no complement. Here $\mathrm{char}\,\mathbb{Q} = 0$, and the failure comes from the infinite order of the group.

**Counterexample (Schur needs an algebraically closed field).** Let $\mathbb{Z}/3$ act on $\mathbb{Q}^2$ by the powers of $C = \begin{pmatrix} 0 & -1 \\ 1 & -1 \end{pmatrix}$, which satisfies $C^3 = 1$. It is irreducible, by the argument for $W$ above. The matrix $C$ commutes with the action, and $C$ is not a scalar. In fact $\mathrm{End}_G(\mathbb{Q}^2) = \mathbb{Q}[C] \cong \mathbb{Q}(\zeta_3)$, a field of dimension $2$ over $\mathbb{Q}$. So the fourth claim of Schur and the abelian corollary both fail over $\mathbb{Q}$. Over $\mathbb{C}$ the same representation splits into the two lines spanned by the eigenvectors of $C$ for $\zeta_3$ and $\zeta_3^2$.

### The library around it

::: mathlib
`LinearMap.equivariantProjection` · `Mathlib.RepresentationTheory.Maschke`

The file works with `k[G]`-modules `V`, `W` that are also `k`-modules through `IsScalarTower`. `LinearMap.conjugate π g` is $\pi^g$ and `conjugate_i` is the identity $\pi^g \circ i = \mathrm{id}$. `sumOfConjugates` is $S$ as a `k`-linear map and `sumOfConjugatesEquivariant` the same map as a `k[G]`-linear map. `equivariantProjection G π` scales it by the inverse of the order, with `equivariantProjection_apply`, and `equivariantProjection_condition (hcard : IsUnit (Nat.card G : k))` is the statement $P \circ i = \mathrm{id}$. Over a field with `[NeZero (Nat.card G : k)]`, `MonoidAlgebra.exists_leftInverse_of_injective` and `MonoidAlgebra.Submodule.exists_isCompl` are the two forms of Maschke. They give the instances `IsSemisimpleModule k[G] V`, `IsSemisimpleRepresentation ρ`, and `IsSemisimpleRing (AddMonoidAlgebra k G)` for additive groups. Wedderburn's theorem for the resulting semisimple ring is `IsSemisimpleRing.exists_algEquiv_pi_matrix_end_mulOpposite`, outside this module.

<?decl MonoidAlgebra.exists_leftInverse_of_injective?>
:::

::: mathlib
`Representation.IsSemisimpleRepresentation` · `Mathlib.RepresentationTheory.Semisimple`

`IsSemisimpleRepresentation ρ` abbreviates `ComplementedLattice (Subrepresentation ρ)`. The iff `isSemisimpleRepresentation_iff_isSemisimpleModule_asModule` moves to `ρ.asModule`, and `isSemisimpleModule_iff_isSemisimpleRepresentation_ofModule` goes the other way for a `k[G]`-module. The irreducible version in `Irreducible` is parallel: `IsIrreducible ρ` abbreviates `IsSimpleOrder (Subrepresentation ρ)`, with `irreducible_iff_isSimpleModule_asModule` and `isSimpleModule_iff_irreducible_ofModule`.

<?decl Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule?>
:::

::: mathlib
`Representation.IsIrreducible.bijective_or_eq_zero` · `Mathlib.RepresentationTheory.Irreducible`

For `f : IntertwiningMap ρ σ` with `[IsIrreducible ρ]`, `injective_or_eq_zero` gives the first part of Schur; `surjective_or_eq_zero` takes a map into an irreducible `ρ`; `bijective_or_eq_zero` needs both irreducible. An instance gives `Subsingleton (IntertwiningMap ρ σ)` when `Equiv ρ σ` is empty. Under `[FiniteDimensional k V] [IsAlgClosed k]`, `algebraMap_intertwiningMap_bijective_of_isAlgClosed` is the fourth part, `finrank_intertwiningMap_self` its dimension form, and `finrank_eq_one_of_isMulCommutative` the abelian corollary.

<?decl Representation.IsIrreducible.finrank_intertwiningMap_self?>
:::

::: mathlib
`FDRep.simple_iff_end_is_rank_one` · `Mathlib.RepresentationTheory.FinGroupCharZero`

With `[Field k] [Finite G] [NeZero (Nat.card G : k)]`, the instances `Rep.instInjective`, `Rep.instProjective`, `FDRep.instInjectiveOfNeZeroCastCard` and `FDRep.instProjectiveOfNeZeroCastCard` are the corollary on projective and injective objects. `simple_iff_end_is_rank_one` adds `[IsAlgClosed k]` and states `Simple V ↔ Module.finrank k (V ⟶ V) = 1` with `Simple` the categorical notion in `FDRep`. `simple_iff_char_is_norm_one` is the character form, treated in the next section.

<?decl FDRep.simple_iff_end_is_rank_one?>
:::

Common errors of a learner: The first error is to state Maschke with `[Fintype G]` alone; the order must be nonzero in `k`, and over $\mathbb{F}_p$ with $p$ dividing $|G|$ the statement is false. The second error is to use `Representation.IsIrreducible` and `FDRep`'s `Simple` as one notion; they are linked only through the equivalences of Chapter 1, so a lemma about one does not rewrite the other. The third error is to apply the scalar form of Schur over $\mathbb{Q}$ or $\mathbb{R}$; it needs `IsAlgClosed k`, and the counterexample above shows why.

### Exercises

1. (A) Show that each one dimensional representation is irreducible, and that the sign representation of $S_3$ is not equivalent to the trivial one.
2. (A) Decompose the regular representation of $\mathbb{Z}/2$ over $\mathbb{Q}$ into irreducibles. Hint: use $e_1 + e_s$ and $e_1 - e_s$.
3. (A) Find $\mathrm{End}_{S_3}(\mathbb{Q}^3)$ for the permutation representation, and use Schur to explain why it has dimension $2$. Hint: $\mathbb{Q}^3 = \mathbb{Q} \oplus W$ with the summands irreducible and not equivalent.
4. (B) Let $V = U_1 \oplus U_2$ with $U_1$, $U_2$ irreducible and not equivalent. Show that each subrepresentation of $V$ is $0$, $U_1$, $U_2$ or $V$. Hint: project a subrepresentation to each factor and apply Schur.
5. (B) Over $\mathbb{C}$, list the irreducible representations of $\mathbb{Z}/n$ and show that there are exactly $n$ of them up to equivalence. Hint: use the abelian corollary; the generator acts by an $n$-th root of unity.
6. (C) Show that in the counterexample over $\mathbb{F}_p$, the representation has exactly one subrepresentation of dimension $1$, and that it is not a direct sum of irreducibles.

### Notes and history

Maschke proved complete reducibility for finite groups in 1898. Schur proved the lemma that carries his name in 1905, in his reworking of the character theory of Frobenius. The failure of Maschke in characteristic dividing the order is the start of modular representation theory, which Brauer developed from the 1930s. Mathlib authors, read from the file headers: `RepresentationTheory.Maschke` by Kim Morrison; `RepresentationTheory.Semisimple` and `RepresentationTheory.Irreducible` by Stepan Nesterov; `RepresentationTheory.FinGroupCharZero` by Sophie Morel.

### Reference

<?reference?>
