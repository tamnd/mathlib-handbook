---
title: Topological rings and fields
kind: theory
modules:
  - Mathlib.Topology.Algebra.Ring.Basic
  - Mathlib.Topology.Algebra.Ring.Ideal
  - Mathlib.Topology.Algebra.Ring.Compact
  - Mathlib.Topology.Algebra.GroupWithZero
  - Mathlib.Topology.Algebra.Field
  - Mathlib.Topology.Algebra.Ring.Real
  - Mathlib.Topology.Instances.Rat
  - Mathlib.Topology.Instances.RatLemmas
  - Mathlib.Topology.Instances.Complex
  - Mathlib.Topology.Instances.Matrix
  - Mathlib.Topology.Algebra.Polynomial
  - Mathlib.Topology.Algebra.MvPolynomial
  - Mathlib.Topology.Instances.ZMod
  - Mathlib.Topology.Algebra.Group.Matrix
  - Mathlib.Topology.Algebra.Localization
  - Mathlib.Topology.Instances.TrivSqZeroExt
  - Mathlib.Topology.Algebra.Algebra.Rat
  - Mathlib.Topology.Algebra.IntermediateField
explains:
  E3: [IsTopologicalRing, ContinuousInv₀, IsTopologicalDivisionRing]
  E2: [IsTopologicalSemiring, IsSemitopologicalRing, IsTopologicalRing.of_addGroup_of_nhds_zero, RingTopology, Subring.topologicalClosure, Ideal.closure, Ideal.closure_eq_of_isClosed, topologicalRing_quotient, QuotientRing.isOpenMap_coe, DivisionRing.finite_of_compactSpace_of_t2Space, IsArtinianRing.finite_of_compactSpace_of_t2Space, Ideal.isOpen_of_isMaximal, Continuous.inv₀, Filter.Tendsto.div, Units.isEmbedding_val₀, Subfield.topologicalClosure, instIsTopologicalDivisionRingReal, Rat.isDenseEmbedding_coe_real, Rat.instTotallyDisconnectedSpace, Complex.subfield_eq_of_closed, Matrix.topologicalRing, Continuous.matrix_det, continuousAt_matrix_inv, Polynomial.continuous, Polynomial.continuous_aeval, MvPolynomial.continuous_eval, ZMod.instDiscreteTopology]
  E1: auto
families: []
requires: [V06, V13.C01, V13.C04, V13.C05, V14.C01]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Topological rings and fields

### Overview

A topological ring is a ring whose additive group is a topological group and whose multiplication is continuous. The results of Chapter 1 apply to its additive group, and this section adds what the multiplication gives. Closures of subrings and ideals are subrings and ideals, quotients are topological rings, and polynomial maps and the determinant are continuous. For fields, Mathlib asks that the inversion is continuous at each nonzero point. The main theorem states that a compact Hausdorff division ring is finite.

### Definitions

**Definition (Topological ring).** A topological ring is a ring $R$ with a topology such that $(x, y) \mapsto x + y$, $x \mapsto -x$ and $(x, y) \mapsto xy$ are continuous.

**Definition (Topological division ring).** A topological division ring is a division ring $K$ that is a topological ring and in which the map $x \mapsto x^{-1}$ is continuous at each $x \ne 0$. A topological field is a commutative topological division ring.

An equivalent form of the second definition asks that $K^\times = K \setminus \{0\}$, with the subspace topology, is a topological group.

::: mathlib
`IsTopologicalRing` · `Mathlib.Topology.Algebra.Ring.Basic`

A class for `[TopologicalSpace R] [NonUnitalNonAssocRing R]` that extends `IsTopologicalSemiring R` (that is, `ContinuousAdd` and `ContinuousMul`) and `ContinuousNeg R`. So the instance gives `IsTopologicalAddGroup R` too. The class needs no unit and no associativity, so it applies to Lie rings and to rings of operators with no unit. The weaker `IsSemitopologicalRing` asks only that multiplication is separately continuous. The criterion `IsTopologicalRing.of_addGroup_of_nhds_zero` reduces the continuity of multiplication to three limits at $0$: $xy \to 0$ as $(x, y) \to (0, 0)$, and $x_0 x \to 0$ and $x x_0 \to 0$ as $x \to 0$. The structure `RingTopology R` bundles a topology that makes `R` a topological ring.

<?decl IsTopologicalRing?>
:::

::: mathlib
`ContinuousInv₀` · `Mathlib.Topology.Algebra.GroupWithZero`

A class with one field: `∀ x ≠ 0, ContinuousAt Inv.inv x`. In Mathlib `(0 : K)⁻¹ = 0`, a junk value that makes the inversion a total function. The inversion is not continuous at $0$ in $\mathbb{R}$, so the class asks only for $x \ne 0$. The lemmas carry the matching hypothesis: `Continuous.inv₀` needs `∀ x, f x ≠ 0`, and `Filter.Tendsto.div` needs a nonzero limit of the denominator. The lemma `Units.isEmbedding_val₀` states that the units of a group with zero carry the subspace topology.

<?decl ContinuousInv₀?>
:::

::: mathlib
`IsTopologicalDivisionRing` · `Mathlib.Topology.Algebra.Field`

A class that extends `IsTopologicalRing K` and `ContinuousInv₀ K`. There is no separate class for fields: a topological field is a `Field` with this class. The real numbers have the instance `instIsTopologicalDivisionRingReal`.

<?decl IsTopologicalDivisionRing?>
:::

### Theorems and proofs

**Proposition (Closures).** Let $R$ be a topological ring. The closure of a subring is a subring, and the closure of a left ideal is a left ideal. If $K$ is a topological division ring, the closure of a subfield is a subfield.

*Proof.* By Chapter 1, Section 2, the closure $\overline{S}$ of an additive subgroup is an additive subgroup. Let $S$ be a subring. The multiplication $m$ is continuous and $m(S \times S) \subseteq S$, so $m(\overline{S} \times \overline{S}) = m(\overline{S \times S}) \subseteq \overline{S}$. Also $1 \in \overline{S}$. Let $I$ be a left ideal and $r \in R$. The map $x \mapsto rx$ is continuous and maps $I$ into $I$, so it maps $\overline{I}$ into $\overline{I}$. Let $F$ be a subfield of $K$ and $x \in \overline{F}$ with $x \ne 0$. The inversion is continuous at $x$ and maps $F \setminus \{0\}$ into $F$. Each neighbourhood of $x$ that misses $0$ meets $F \setminus \{0\}$, so $x$ is in the closure of $F \setminus \{0\}$ in $K \setminus \{0\}$, and $x^{-1} \in \overline{F}$. $\square$

In Mathlib these closures are `Subring.topologicalClosure`, `Ideal.closure` and `Subfield.topologicalClosure`. A closed ideal is its own closure, `Ideal.closure_eq_of_isClosed`.

**Proposition (Quotients).** Let $I$ be a two sided ideal of a topological ring $R$. The ring $R/I$ with the quotient topology is a topological ring, and the map $R \to R/I$ is open.

*Proof.* The additive part is the theorem on quotient groups of Chapter 1, Section 3. Let $\pi : R \to R/I$ and let $m'$ be the multiplication of $R/I$. Then $m' \circ (\pi \times \pi) = \pi \circ m$ is continuous. The map $\pi \times \pi$ is an open continuous surjection, so it is a quotient map, and $m'$ is continuous. $\square$

**Proposition (Polynomials).** Let $R$ be a commutative topological ring and $p \in R[x_1, \dots, x_n]$. The map $R^n \to R$, $a \mapsto p(a)$, is continuous.

*Proof.* The projections $a \mapsto a_i$ and the constant maps are continuous. Sums and products of continuous maps into $R$ are continuous, because they are composites of a continuous map into $R \times R$ with the addition or the multiplication. The map $a \mapsto p(a)$ is built from projections and constants by finitely many sums and products. $\square$

**Theorem (Matrices).** Let $K$ be a Hausdorff topological field and $n \ge 1$. The ring $M_n(K)$ with the product topology of $K^{n^2}$ is a topological ring, the determinant is continuous, $GL_n(K)$ is open in $M_n(K)$, and $A \mapsto A^{-1}$ is continuous on $GL_n(K)$.

*Proof.* Each entry of $A + B$, $-A$ and $AB$ is a polynomial in the entries of $A$ and $B$, and $\det A$ is a polynomial in the entries of $A$. So the four maps are continuous by the proposition on polynomials. The set $GL_n(K) = \det^{-1}(K \setminus \{0\})$ is open, since $\{0\}$ is closed when $K$ is Hausdorff. By Cramer's rule $A^{-1} = (\det A)^{-1} \operatorname{adj}(A)$. The entries of $\operatorname{adj}(A)$ are polynomials, and $A \mapsto (\det A)^{-1}$ is the composite of $\det$, which takes values in $K \setminus \{0\}$ on $GL_n(K)$, and the inversion, which is continuous there. $\square$

**Theorem (Compact division rings).** A compact Hausdorff topological division ring $K$ is finite.

*Proof.* The set $U = K \setminus \{1\}$ is open because $K$ is Hausdorff, and $0 \in U$. The multiplication $m$ maps $K \times \{0\}$ into $\{0\} \subseteq U$, so $K \times \{0\} \subseteq m^{-1}(U)$, an open set. Since $K$ is compact, the tube lemma (Volume 13, Chapter 5) gives an open neighbourhood $V$ of $0$ with $K \times V \subseteq m^{-1}(U)$, that is, $kv \ne 1$ for all $k \in K$ and $v \in V$. Let $v \in V$ with $v \ne 0$. Then $k = v^{-1}$ gives $kv = 1$, a contradiction. So $V = \{0\}$, and $\{0\}$ is open. By translation each point is open, and $K$ is discrete. A compact discrete space is finite, since the cover by the points has a finite subcover. $\square$

The proof does not use the continuity of the inversion. So the theorem holds for each division ring with a compact Hausdorff ring topology, and Mathlib states it with `IsTopologicalRing` only.

::: mathlib
`DivisionRing.finite_of_compactSpace_of_t2Space` · `Mathlib.Topology.Algebra.Field`

For `[DivisionRing K] [IsTopologicalRing K] [CompactSpace K] [T2Space K]`, the result `Finite K`. The module `Mathlib.Topology.Algebra.Ring.Compact` extends it: `IsArtinianRing.finite_of_compactSpace_of_t2Space` for artinian commutative rings, and `Ideal.isOpen_of_isMaximal`, which states that a maximal ideal of a compact Hausdorff noetherian ring is open.

<?decl DivisionRing.finite_of_compactSpace_of_t2Space?>
:::

### Examples

**Example (The real field).** $\mathbb{R}$ is a topological field. Addition and negation are continuous by Chapter 1. For multiplication, $xy - x_0y_0 = (x - x_0)y + x_0(y - y_0)$, so $|xy - x_0 y_0| \le |x - x_0|(|y_0| + 1) + |x_0||y - y_0|$ when $|y - y_0| \le 1$. For the inversion at $x_0 \ne 0$, let $|x - x_0| < |x_0|/2$. Then $|x| > |x_0|/2$ and $|x^{-1} - x_0^{-1}| = |x - x_0|/(|x||x_0|) < 2|x - x_0|/|x_0|^2$. The same estimates work for $\mathbb{C}$ and for each field with an absolute value, the subject of Chapter 8.

**Example (The $p$-adic topology on $\mathbb{Z}$).** Fix a prime $p$ and give $\mathbb{Z}$ the topology in which the sets $a + p^n\mathbb{Z}$ form a basis. The ideals $p^n\mathbb{Z}$ are open subgroups, so addition and negation are continuous. For multiplication, $(x + p^n a)(y + p^n b) - xy = p^n(ay + xb + p^n ab) \in p^n\mathbb{Z}$. So $\mathbb{Z}$ is a topological ring. It is Hausdorff, since $\bigcap_n p^n\mathbb{Z} = \{0\}$. In this topology $p^n \to 0$, and the sequence $s_n = (p^n - 1)/(p - 1)$ is Cauchy, since $s_m - s_n \in p^n\mathbb{Z}$ for $m \ge n$. If $s_n \to z \in \mathbb{Z}$, then $(p - 1)z = \lim (p^n - 1) = -1$, which is impossible for $p \ne 2$. So the ring is not complete. Its completion is the ring $\mathbb{Z}_p$ of Chapter 3. Each $\mathbb{Z}/p^n\mathbb{Z}$ is the quotient by an open ideal, and it is discrete, in accordance with `ZMod.instDiscreteTopology`.

**Counterexample (A ring topology on a field that is not a field topology).** Give $\mathbb{Q}$ the topology in which the sets $a + n!\mathbb{Z}$, for $a \in \mathbb{Q}$ and $n \ge 1$, form a basis. Use the criterion of `IsTopologicalRing.of_addGroup_of_nhds_zero`. The sets $n!\mathbb{Z}$ are subgroups, so $\mathbb{Q}$ is a topological group. Also $n!\mathbb{Z} \cdot n!\mathbb{Z} \subseteq n!\mathbb{Z}$. For $x_0 = a/b$ with $b \ge 1$ and $n \ge m + b$, the integer $n!/b$ is a multiple of $m!$, so $x_0 \cdot n!\mathbb{Z} \subseteq m!\mathbb{Z}$. So $\mathbb{Q}$ is a Hausdorff topological ring. The inversion is not continuous at $1$: $x_n = 1 + n! \to 1$, but $x_n^{-1} - 1 = -n!/(1 + n!)$ is not an integer, so it is not in $1!\mathbb{Z} = \mathbb{Z}$. So a field with a ring topology need not be a topological field, and the class `ContinuousInv₀` is a real extra condition.

**Remark (Common errors).** A learner often asks that the inversion of a topological field is continuous on all of $K$. With the junk value $0^{-1} = 0$ this fails in $\mathbb{R}$: $1/x$ has no limit at $0$. A second error is to forget the nonzero hypothesis when a proof uses `Continuous.inv₀` or `Filter.Tendsto.div`. A third error is to think that a ring with a Hausdorff ring topology is a topological field once it is a field. The counterexample on $\mathbb{Q}$ shows that this is false.

### The library around it

The classes are in `Mathlib.Topology.Algebra.Ring.Basic`, `Mathlib.Topology.Algebra.GroupWithZero` and `Mathlib.Topology.Algebra.Field`. Ideals and quotient rings are in `Mathlib.Topology.Algebra.Ring.Ideal`, polynomials in `Mathlib.Topology.Algebra.Polynomial` and `Mathlib.Topology.Algebra.MvPolynomial`, and matrices in `Mathlib.Topology.Instances.Matrix`, which gives `Matrix.topologicalRing` and `Continuous.matrix_det`. The inverse of a matrix is continuous at $A$ by `continuousAt_matrix_inv`, under the hypothesis that `Ring.inverse` is continuous at $\det A$. The field $\mathbb{Q}$ is dense in $\mathbb{R}$ (`Rat.isDenseEmbedding_coe_real`) and totally disconnected (`Rat.instTotallyDisconnectedSpace`), and a closed subfield of $\mathbb{C}$ is $\mathbb{R}$ or $\mathbb{C}$ (`Complex.subfield_eq_of_closed`).

Matrix groups are in `Mathlib.Topology.Algebra.Group.Matrix`. The general linear group $GL_n(R)$ is the group of units of the matrix ring, and the special linear group $SL_n(R)$ has the topology of a subspace of the matrices. For a topological commutative ring $R$, $SL_n(R)$ is a topological group (`Matrix.SpecialLinearGroup.isTopologicalGroup`) and the determinant $GL_n(R) \to R^\times$ is continuous (`Matrix.GeneralLinearGroup.continuous_det`). The inclusion $SL_n(R) \to GL_n(R)$ is an embedding (`Matrix.SpecialLinearGroup.isEmbedding_toGL`), and a closed embedding when $R$ is $T_0$ (`Matrix.SpecialLinearGroup.isClosedEmbedding_toGL`). A continuous ring hom $f : R \to S$ induces continuous maps of these groups (`Continuous.generalLinearGroup_map`, `Continuous.specialLinearGroup_map`). The same pattern holds for inducing maps and embeddings, with names such as `Topology.IsEmbedding.specialLinearGroup_map` and `Topology.IsClosedEmbedding.generalLinearGroup_map`. If $R$ is discrete, then $SL_n(R)$ is discrete (`Matrix.SpecialLinearGroup.instDiscreteTopology`), so $SL_2(\mathbb{Z})$ is a discrete group.

The module `Mathlib.Topology.Algebra.Localization` gives the localization $M^{-1}R$ of a topological commutative ring at a submonoid $M$ the finest ring topology that makes $R \to M^{-1}R$ continuous (`Localization.ringTopology`). With it, $M^{-1}R$ is a topological ring (`instIsTopologicalRingLocalization`).

The module `Mathlib.Topology.Instances.TrivSqZeroExt` treats the trivial square zero extension $R \oplus M$ of a ring $R$ by a bimodule $M$, with the product $(r, m)(r', m') = (rr', rm' + mr')$. Its topology and its uniformity are those of the product $R \times M$ (`TrivSqZeroExt.nhds_def`, `TrivSqZeroExt.uniformity_def`). So the projections and the inclusions are continuous (`TrivSqZeroExt.continuous_fst`, `TrivSqZeroExt.continuous_snd`, `TrivSqZeroExt.continuous_inl`, `TrivSqZeroExt.continuous_inr`), and over a commutative ring they are bundled as continuous linear maps (`TrivSqZeroExt.fstCLM`, `TrivSqZeroExt.sndCLM`, `TrivSqZeroExt.inlCLM`, `TrivSqZeroExt.inrCLM`). The extension is a topological semiring when $R$ is one, addition on $M$ is continuous and the two actions of $R$ on $M$ are continuous (`TrivSqZeroExt.topologicalSemiring`). Sums are computed in each component (`TrivSqZeroExt.hasSum_fst`, `TrivSqZeroExt.hasSum_snd`, `TrivSqZeroExt.hasSum_inl`, `TrivSqZeroExt.hasSum_inr`), and the extension of complete spaces is complete (`TrivSqZeroExt.instCompleteSpace`). The dual numbers $R[\varepsilon]$ with $\varepsilon^2 = 0$ are the case $M = R$.

Two small modules concern fields. In `Mathlib.Topology.Algebra.Algebra.Rat`, the multiplication by a fixed rational number is continuous on a division ring of characteristic zero with separately continuous multiplication (`DivisionRing.continuousConstSMul_rat`). In `Mathlib.Topology.Algebra.IntermediateField`, an intermediate field $K \le E \le L$ acts continuously on each space on which $L$ acts continuously (`IntermediateField.continuousSMul`).

### Exercises

1. (A) Show that each ring with the discrete topology is a topological ring, and that each field with the discrete topology is a topological field.
2. (A) Show that the map $\mathbb{R}^3 \to \mathbb{R}$, $(a, b, c) \mapsto b^2 - 4ac$, is continuous, and that the set of $(a, b, c)$ with $a \ne 0$ for which $ax^2 + bx + c$ has two distinct real roots is open.
3. (A) Let $R$ be a Hausdorff topological ring. Show that the set $\{x : x^2 = 0\}$ is closed.
4. (B) Show that the closure of an ideal in a commutative topological ring is an ideal, and that a maximal ideal is either closed or dense.
5. (B) Let $K$ be a topological field and $f, g : X \to K$ continuous with $g(x) \ne 0$ for all $x$. Show that $f/g$ is continuous.
6. (B) Show that $GL_n(\mathbb{R})$ is dense in $M_n(\mathbb{R})$. *Hint:* $\det(A + tI)$ is a nonzero polynomial in $t$.
7. (C) Let $R$ be a topological ring with unit group $R^\times$. Show that $R^\times$ is open if it contains a neighbourhood of $1$. Show that if also the inversion $R^\times \to R^\times$ is continuous at $1$ for the subspace topology, then it is continuous. *Hint:* $x = x_0(x_0^{-1}x)$ and $x^{-1} = (x_0^{-1}x)^{-1}x_0^{-1}$.

### Notes and history

The classification of locally compact fields is a classical theorem: a locally compact, non-discrete topological field is $\mathbb{R}$, $\mathbb{C}$, a finite extension of a $p$-adic field $\mathbb{Q}_p$, or a field $\mathbb{F}_q((t))$ of Laurent series. Weil's "Basic Number Theory" starts from this result.

### Reference

<?reference?>
