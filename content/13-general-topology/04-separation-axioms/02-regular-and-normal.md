---
title: Regular and normal spaces
kind: theory
modules:
  - Mathlib.Topology.Separation.Regular
  - Mathlib.Topology.Separation.SeparatedNhds
  - Mathlib.Topology.Separation.CompletelyRegular
  - Mathlib.Topology.Separation.GDelta
  - Mathlib.Topology.Separation.PerfectlyNormal
  - Mathlib.Topology.Separation.NotNormal
explains:
  E3: [RegularSpace, NormalSpace, SeparatedNhds]
  E2: [T3Space, T4Space, T5Space, regularSpace_iff, closed_nhds_basis, RegularSpace.of_exists_mem_nhds_isClosed_subset, instT3Space, T4Space.t3Space, instT4SpaceOfT1SpaceOfNormalSpace, NormalSpace.normal, normal_separation, NormalSpace.of_regularSpace_secondCountableTopology, Metric.infDist, Metric.continuous_infDist_pt, IsClosed.notMem_iff_infDist_pos, instNormalSpaceOfPseudoMetrizableSpace, instT4SpaceOfMetrizableSpace, CompletelyRegularSpace, T35Space]
  E1: auto
families: []
requires: [V13.C01, V13.C02, V13.C03]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Regular and normal spaces

### Overview

The Hausdorff axiom separates two points. The next two axioms separate a point from a closed set, and two closed sets from each other. A space is regular if each point and each closed set that misses it have disjoint open neighbourhoods. A space is normal if two disjoint closed sets have disjoint open neighbourhoods.

Normality is the axiom that gives continuous functions. Chapter 8 proves that in a normal space two disjoint closed sets are separated by a continuous function with values in $[0,1]$, and that continuous functions on closed sets extend. This section gives the definitions, the filter form of regularity, and the proof that each metric space is normal.

### Definitions

**Definition (Separated by neighbourhoods).** Two sets $A, B \subseteq X$ are separated by neighbourhoods if there are disjoint open sets $U \supseteq A$ and $V \supseteq B$.

::: mathlib
`SeparatedNhds` · `Mathlib.Topology.Separation.SeparatedNhds`

`SeparatedNhds s t` says that there are open `U ⊇ s` and `V ⊇ t` with `Disjoint U V`.

<?decl SeparatedNhds?>
:::

**Definition (Regular, normal, $T_3$, $T_4$).** A space $X$ is regular if for each closed $F$ and each $x \notin F$, the sets $\{x\}$ and $F$ are separated by neighbourhoods. It is normal if each two disjoint closed sets are separated by neighbourhoods. A $T_3$ space is a regular $T_0$ space. A $T_4$ space is a normal $T_1$ space.

*Remarks.* The literature is not uniform: some authors include $T_1$ in "regular" and "normal", others in "$T_3$" and "$T_4$". Mathlib follows the second convention. A normal space need not be regular: the Sierpiński space has no two disjoint nonempty closed sets, so it is normal, and it is not regular. With $T_1$, points are closed, and then $T_4 \Rightarrow T_3 \Rightarrow T_2$.

::: mathlib
`RegularSpace` · `Mathlib.Topology.Separation.Regular`

The class field `regular` states regularity in filter form: for closed `s` and `a ∉ s`, `Disjoint (𝓝ˢ s) (𝓝 a)`. Here `𝓝ˢ s` is the filter of neighbourhoods of the set `s`, the sets that contain an open set containing `s`. The lemma `regularSpace_iff` states this form.

<?decl RegularSpace?>
:::

::: mathlib
`regularSpace_iff` · `Mathlib.Topology.Separation.Regular`

Regularity as disjointness of the neighbourhood filter of a closed set and the neighbourhood filter of a point outside it.

<?decl regularSpace_iff?>
:::

::: mathlib
`T3Space` · `Mathlib.Topology.Separation.Regular`

A regular $T_0$ space. The instance `instT3Space` builds it from the two classes, and each $T_3$ space is $T_2$ by instance.

<?decl T3Space?>
:::

::: mathlib
`instT3Space` · `Mathlib.Topology.Separation.Regular`

`T0Space` and `RegularSpace` give `T3Space`.

<?decl instT3Space?>
:::

::: mathlib
`NormalSpace` · `Mathlib.Topology.Separation.Regular`

The class has the field `normal`: two disjoint closed sets satisfy `SeparatedNhds`. It does not include $T_1$.

<?decl NormalSpace?>
:::

::: mathlib
`NormalSpace.normal` · `Mathlib.Topology.Separation.Regular`

The field of the class. The lemma `normal_separation` is the same statement with implicit sets.

<?decl NormalSpace.normal?>
:::

::: mathlib
`normal_separation` · `Mathlib.Topology.Separation.Regular`

Disjoint closed sets in a normal space have disjoint open neighbourhoods.

<?decl normal_separation?>
:::

::: mathlib
`T4Space` · `Mathlib.Topology.Separation.Regular`

A normal $T_1$ space. It is built from the two classes by `instT4SpaceOfT1SpaceOfNormalSpace`, and it is $T_3$ by `T4Space.t3Space`.

<?decl T4Space?>
:::

::: mathlib
`instT4SpaceOfT1SpaceOfNormalSpace` · `Mathlib.Topology.Separation.Regular`

`T1Space` and `NormalSpace` give `T4Space`.

<?decl instT4SpaceOfT1SpaceOfNormalSpace?>
:::

::: mathlib
`T4Space.t3Space` · `Mathlib.Topology.Separation.Regular`

A $T_4$ space is $T_3$: a point is a closed set.

<?decl T4Space.t3Space?>
:::

### Theorems and proofs

**Theorem (Regularity by closed neighbourhoods).** A space $X$ is regular if and only if, for each $x$, the closed neighbourhoods of $x$ form a basis of $\mathcal{N}(x)$: each neighbourhood $N$ of $x$ contains a closed neighbourhood of $x$.

*Proof.* Assume $X$ is regular and let $N \in \mathcal{N}(x)$, with $x \in U \subseteq N$ and $U$ open. The set $F = X \setminus U$ is closed and misses $x$. Choose disjoint open sets $V \ni x$ and $W \supseteq F$. Then $V \subseteq X \setminus W$, which is closed, so $\overline{V} \subseteq X \setminus W \subseteq X \setminus F = U \subseteq N$. So $\overline{V}$ is a closed neighbourhood of $x$ inside $N$.

Conversely, let $F$ be closed and $x \notin F$. The set $X \setminus F$ is an open neighbourhood of $x$, so it contains a closed neighbourhood $C$ of $x$. Let $V$ be open with $x \in V \subseteq C$ and $W = X \setminus C$. Then $W$ is open, $W \supseteq F$ because $C \subseteq X \setminus F$, and $V \cap W = \emptyset$. $\square$

::: mathlib
`closed_nhds_basis` · `Mathlib.Topology.Separation.Regular`

In a regular space, the closed neighbourhoods of `x` form a basis of `𝓝 x`. The converse is `RegularSpace.of_exists_mem_nhds_isClosed_subset`.

<?decl closed_nhds_basis?>
:::

::: mathlib
`RegularSpace.of_exists_mem_nhds_isClosed_subset` · `Mathlib.Topology.Separation.Regular`

A space is regular if each neighbourhood of each point contains a closed neighbourhood.

<?decl RegularSpace.of_exists_mem_nhds_isClosed_subset?>
:::

The same argument, with a closed set in place of the point, gives the form of normality used in Chapter 8: $X$ is normal if and only if for each closed $F$ and each open $U \supseteq F$ there is an open $V$ with $F \subseteq V \subseteq \overline{V} \subseteq U$.

**Theorem (Metric spaces are normal).** Each pseudometric space is normal. Each metric space is $T_4$.

*Proof.* For a nonempty set $A$, let $d(x, A) = \inf_{a \in A} d(x, a)$. Two facts are needed.

(a) The map $x \mapsto d(x, A)$ is continuous. For each $a \in A$, $d(x, a) \le d(x, y) + d(y, a)$. Take the infimum over $a$: $d(x, A) \le d(x, y) + d(y, A)$. By symmetry $|d(x, A) - d(y, A)| \le d(x, y)$, so the map is Lipschitz with constant $1$.

(b) If $A$ is closed, then $d(x, A) = 0$ if and only if $x \in A$. If $x \in A$, the infimum is $0$. If $x \notin A$, some ball $B(x, r)$ with $r > 0$ misses $A$, because $X \setminus A$ is open. Then $d(x, a) \ge r$ for each $a \in A$, so $d(x, A) \ge r > 0$.

Let $A$ and $B$ be disjoint closed sets. If one of them is empty, take $U = \emptyset$ or $V = \emptyset$. Otherwise set
$$U = \{x : d(x, A) < d(x, B)\}, \qquad V = \{x : d(x, B) < d(x, A)\}.$$
They are open by (a), as preimages of open sets under the continuous map $x \mapsto d(x, A) - d(x, B)$. They are disjoint. For $x \in A$, $d(x, A) = 0$, and $d(x, B) > 0$ by (b), since $x \notin B$. So $A \subseteq U$, and in the same way $B \subseteq V$.

A metric space is $T_1$, since it is Hausdorff (Section 1). So it is $T_4$. $\square$

::: mathlib
`Metric.infDist` · `Mathlib.Topology.MetricSpace.HausdorffDistance`

`infDist x s` is the distance $d(x, A)$ of the proof. It is `0` for the empty set by convention.

<?decl Metric.infDist?>
:::

::: mathlib
`Metric.continuous_infDist_pt` · `Mathlib.Topology.MetricSpace.HausdorffDistance`

Fact (a) of the proof.

<?decl Metric.continuous_infDist_pt?>
:::

::: mathlib
`IsClosed.notMem_iff_infDist_pos` · `Mathlib.Topology.MetricSpace.HausdorffDistance`

Fact (b) of the proof, for a nonempty closed set.

<?decl IsClosed.notMem_iff_infDist_pos?>
:::

::: mathlib
`instNormalSpaceOfPseudoMetrizableSpace` · `Mathlib.Topology.GDelta.MetrizableSpace`

The theorem, for each pseudometrizable space, as an instance. Mathlib derives it from a stronger result: a pseudometrizable space is perfectly normal, since each closed set is a $G_\delta$ set.

<?decl instNormalSpaceOfPseudoMetrizableSpace?>
:::

::: mathlib
`instT4SpaceOfMetrizableSpace` · `Mathlib.Topology.GDelta.MetrizableSpace`

A metrizable space is $T_4$.

<?decl instT4SpaceOfMetrizableSpace?>
:::

**Theorem (Regular and second countable).** A regular second countable space is normal.

*Proof.* Let $A$ and $B$ be disjoint closed sets and $\mathcal{B}$ a countable basis. For each $a \in A$, regularity gives a basic set $W \ni a$ with $\overline{W} \cap B = \emptyset$. List these sets as $W_1, W_2, \dots$; they cover $A$. In the same way list basic sets $W'_1, W'_2, \dots$ that cover $B$ with $\overline{W'_n} \cap A = \emptyset$. Put
$$U_n = W_n \setminus \textstyle\bigcup_{k \le n} \overline{W'_k}, \qquad V_n = W'_n \setminus \textstyle\bigcup_{k \le n} \overline{W_k}.$$
Each is open. $U = \bigcup_n U_n$ contains $A$, since a point of $A$ is in some $W_n$ and in no $\overline{W'_k}$. In the same way $V = \bigcup_n V_n \supseteq B$. If $x \in U_n \cap V_m$ with $n \le m$, then $x \in W_n \subseteq \overline{W_n}$, so $x \notin V_m$, a contradiction; the case $m \le n$ is the same. So $U \cap V = \emptyset$. $\square$

::: mathlib
`NormalSpace.of_regularSpace_secondCountableTopology` · `Mathlib.Topology.Separation.Regular`

The theorem, as an instance. Mathlib proves it from the stronger statement for Lindelöf spaces, `NormalSpace.of_regularSpace_lindelofSpace`.

<?decl NormalSpace.of_regularSpace_secondCountableTopology?>
:::

### Examples

**Counterexample (A Hausdorff space that is not regular).** Let $K = \{1/n : n \ge 1\}$. On $\mathbb{R}$ take the topology generated by the open intervals and the sets $(a, b) \setminus K$. It is finer than the usual topology, so it is Hausdorff. The set $K$ is closed in it: $\mathbb{R} \setminus K = \bigcup_{a < b} (a, b) \setminus K$ is open. The point $0 \notin K$. Each open set $U \ni 0$ contains a basic set $(-\varepsilon, \varepsilon) \setminus K$. Each open set $W \supseteq K$ contains, around each $1/n$, a usual interval, since the only basic sets that contain a point of $K$ are intervals. Choose $1/n < \varepsilon$ and an interval $(1/n - \delta, 1/n + \delta) \subseteq W \cap (0, \varepsilon)$. It contains points not in $K$, which lie in $U$. So $U \cap W \ne \emptyset$, and the space is not regular.

**Example (Normal spaces from the theorems).** The spaces $\mathbb{R}^n$, each subspace of a metric space, and each space with a countable basis and closed neighbourhood bases are normal. The Sorgenfrey line of Chapter 1 is normal, though not metrizable; its square, the Sorgenfrey plane, is regular and not normal. So a product of two normal spaces need not be normal, and the theorem on second countable spaces cannot drop its hypothesis, since the Sorgenfrey plane is not second countable.

### The library around it

The classes are in `Mathlib.Topology.Separation.Regular`. Between $T_3$ and $T_4$ sits the completely regular axiom, `CompletelyRegularSpace`, in `Mathlib.Topology.Separation.CompletelyRegular`: each closed set and each point outside it are separated by a continuous function to $[0,1]$. With $T_0$ it gives `T35Space`, the Tychonoff spaces. Chapter 8 proves that $T_4$ implies $T_{3\frac{1}{2}}$. Above $T_4$ is `T5Space`, the completely normal spaces, in which each subspace is normal.

::: mathlib
`CompletelyRegularSpace` · `Mathlib.Topology.Separation.CompletelyRegular`

Points and closed sets are separated by continuous functions to the unit interval.

<?decl CompletelyRegularSpace?>
:::

::: mathlib
`T35Space` · `Mathlib.Topology.Separation.CompletelyRegular`

A completely regular $T_0$ space, also called a Tychonoff space.

<?decl T35Space?>
:::

::: mathlib
`T5Space` · `Mathlib.Topology.Separation.Regular`

A completely normal $T_1$ space: separated sets have disjoint neighbourhoods.

<?decl T5Space?>
:::

A normal space is perfectly normal if each closed set is a $G_\delta$ set, a countable intersection of open sets. This is `PerfectlyNormalSpace` in `Mathlib.Topology.Separation.GDelta`, and with T0 it gives `T6Space`. A perfectly normal space is completely normal (`PerfectlyNormalSpace.toCompletelyNormalSpace`), and in it each closed set is a $G_\delta$ set (`IsClosed.isGδ`). A space is perfectly normal if and only if each closed set is the zero set of a continuous function to $[0,1]$ (`perfectlyNormalSpace_iff_forall_isClosed_preimage_zero`). Each metric space is perfectly normal. In a first countable T1 space each point is a $G_\delta$ set (`IsGδ.singleton`). The module `Mathlib.Topology.Separation.NotNormal` gives the lemma of Jones: in a separable normal space a closed discrete subset has cardinality less than the continuum (`IsClosed.mk_lt_continuum`). So a separable space with a closed discrete subset of cardinality at least the continuum is not normal (`IsClosed.not_normal_of_continuum_le_mk`). The Sorgenfrey plane is the standard example.

The reference table at the end of the section lists the declarations of the modules.

### Exercises

1. (A) Show that a regular $T_0$ space is Hausdorff.
2. (A) Show that each subspace of a regular space is regular.
3. (A) Show that a closed subspace of a normal space is normal.
4. (B) Prove the form of normality stated after the first theorem: $X$ is normal if and only if each closed $F$ inside an open $U$ has an open $V$ with $F \subseteq V \subseteq \overline{V} \subseteq U$.
5. (B) Show that in a regular space each point has a basis of open sets $V$ with $\overline{V}$ inside any given neighbourhood, and deduce that a product of two regular spaces is regular.
6. (B) Show that the space of the counterexample has a closed set $K$ and a point $0$ that are not separated by neighbourhoods, and that the quotient of $\mathbb{R}$ by $K$ (collapse $K$ to a point) is not Hausdorff with the usual topology.
7. (C) Show that the Sorgenfrey line is normal.

### Notes and history

Regular spaces were introduced by Vietoris in 1921 and normal spaces by Tietze in 1923, with the axiom that bears the second name in the list of Alexandroff and Hopf. Urysohn (1925) proved that normality gives continuous separating functions, and Tychonoff (1930) defined the completely regular spaces as the subspaces of cubes $[0,1]^I$. The counterexample of the $K$-topology is in Steen and Seebach, *Counterexamples in topology*. That the Sorgenfrey plane is not normal follows from the Jones lemma (1937): a separable normal space has no closed discrete subspace of the size of the continuum.

### Reference

<?reference?>
