---
title: Topological vector bundles
kind: theory
modules:
  - Mathlib.Topology.VectorBundle.Basic
  - Mathlib.Topology.VectorBundle.Constructions
  - Mathlib.Topology.VectorBundle.Hom
  - Mathlib.Topology.VectorBundle.ContinuousAlternatingMap
  - Mathlib.Topology.VectorBundle.FiniteDimensional
  - Mathlib.Topology.VectorBundle.Riemannian
explains:
  E3: [VectorBundle, Bundle.Trivialization.coordChangeL, VectorBundleCore]
  E2: [Bundle.Trivialization.IsLinear, Bundle.Trivialization.linearEquivAt, Bundle.Trivialization.continuousLinearEquivAt, Bundle.Trivialization.continuousLinearEquivAt_apply, Bundle.Trivialization.continuousLinearMapAt, Bundle.Trivialization.symmL, VectorBundle.continuousLinearEquivAt, VectorBundle.continuousOn_coordChange', VectorBundle.trivialization_linear', Bundle.Trivialization.symm_coordChangeL, Bundle.zeroSection, Bundle.Trivialization.continuous_zeroSection, VectorBundle.completeSpace, VectorBundleCore.Fiber, VectorBundleCore.localTriv, VectorBundleCore.localTriv_apply, VectorBundleCore.localTriv_coordChange_eq, VectorBundleCore.coordChange_linear_comp, VectorBundleCore.fiberBundle, VectorBundleCore.vectorBundle, VectorBundleCore.toFiberBundleCore, trivialVectorBundleCore, VectorPrebundle, Bundle.Trivial.vectorBundle, VectorBundle.prod, VectorBundle.pullback, Bundle.Pretrivialization.continuousLinearMapCoordChange, Bundle.Pretrivialization.continuousOn_continuousLinearMapCoordChange, Bundle.ContinuousLinearMap.vectorPrebundle, Bundle.ContinuousLinearMap.vectorBundle, Bundle.Trivialization.continuousLinearMap, Bundle.ContinuousAlternatingMap.instVectorBundle, VectorBundle.finiteDimensional, VectorBundle.finrank_eq, Bundle.RiemannianMetric, Bundle.RiemannianBundle, Bundle.ContinuousRiemannianMetric, IsContinuousRiemannianBundle, Continuous.inner_bundle]
  E1: auto
families: []
requires: [V13.C01, V16.C01, V16.C02, V16.C03, V16.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Topological vector bundles

### Overview

A vector bundle is a fiber bundle whose fibers are vector spaces and whose trivializations are linear on each fiber. Over the intersection of two base sets, the change of trivializations is then a family of invertible linear maps of the model fiber $F$. Mathlib asks that it is continuous in the base point for the operator norm.

This section uses Section 1 and the operator norm of Volume 16, Chapter 2. It proves that each trivialization gives a continuous linear isomorphism from a fiber to $F$, that the zero section is continuous, and that a family of linear transition functions with the cocycle condition defines a vector bundle. It builds the bundle of continuous linear maps between two vector bundles. It ends with continuous Riemannian metrics.

### Definitions

Let $\Bbbk$ be a nontrivially normed field, $B$ a topological space, $F$ a normed space over $\Bbbk$, and $E : B \to \mathrm{Type}$ a family of $\Bbbk$-modules with a topology on each $E_b$. Let $E$ be a fiber bundle with fiber $F$, as in Section 1.

**Definition (Linear trivialization).** A trivialization $e$ of $E$ with base set $U$ is linear if for each $b \in U$ the map $e_b : E_b \to F$, $v \mapsto \mathrm{pr}_2(e(b, v))$, is $\Bbbk$-linear.

**Definition (Coordinate change).** Let $e, e'$ be linear trivializations with base sets $U, U'$. For $b \in U \cap U'$ the coordinate change is $g_{e e'}(b) = e'_b \circ e_b^{-1} : F \to F$. Mathlib extends it by the identity for $b \notin U \cap U'$.

**Definition (Vector bundle).** The fiber bundle $E$ is a vector bundle over $\Bbbk$ if every trivialization of its atlas is linear, and for any two trivializations $e, e'$ of the atlas the map $b \mapsto g_{e e'}(b) \in L(F, F)$ is continuous on $U \cap U'$ for the operator norm.

**Definition (Vector bundle core).** A vector bundle core with index type $\iota$ consists of open sets $U_i \subseteq B$, a choice $i(b)$ with $b \in U_{i(b)}$, and maps $g_{ij} : B \to L(F, F)$ such that $g_{ii}(b) = \mathrm{id}$ for $b \in U_i$, each $g_{ij}$ is continuous on $U_i \cap U_j$, and $g_{jk}(b) \circ g_{ij}(b) = g_{ik}(b)$ for $b \in U_i \cap U_j \cap U_k$.

**Definition (Zero section).** The zero section is the map $B \to \mathrm{Tot}(E)$, $b \mapsto (b, 0)$.

**Definition (Hom bundle).** Let $E_1, E_2$ be vector bundles over $B$ with fibers $F_1, F_2$. The bundle of continuous linear maps has fiber $L(E_{1,b}, E_{2,b})$ at $b$ and model fiber $L(F_1, F_2)$.

**Definition (Continuous Riemannian metric).** Let $\Bbbk = \mathbb{R}$. A Riemannian metric on $E$ is a family of inner products $g_b$ on the fibers $E_b$ that define the given topology of each fiber. It is continuous if $b \mapsto g_b$ is a continuous section of the bundle of bilinear forms $L(E_b, L(E_b, \mathbb{R}))$.

::: mathlib
`VectorBundle` · `Mathlib.Topology.VectorBundle.Basic`

`VectorBundle R F E` is a `Prop`-valued class on top of `FiberBundle F E`. Its two fields are `trivialization_linear'`, which asks `Bundle.Trivialization.IsLinear R e` for each trivialization of the atlas, and `continuousOn_coordChange'`. The coordinate change `Bundle.Trivialization.coordChangeL R e e' b` is a continuous linear equivalence `F ≃L[R] F`, the identity outside the two base sets. `VectorBundleCore R B F ι` is the structure of transition functions.

<?decl VectorBundle?>
<?decl Bundle.Trivialization.coordChangeL?>
<?decl VectorBundleCore?>
:::

### Theorems and proofs

Fix a vector bundle $E$ as above. For $b \in B$ let $\iota_b : E_b \to \mathrm{Tot}(E)$ be $v \mapsto (b, v)$. Section 1 shows that $\iota_b$ is an inducing map: a map $h$ into $E_b$ is continuous if and only if $\iota_b \circ h$ is continuous.

**Theorem (Trivializations on a fiber).** Let $e$ be a linear trivialization with base set $U$ and $b \in U$. Then $e_b : E_b \to F$ is a continuous linear isomorphism.

*Proof.* The map $e$ is a bijection from $\pi^{-1}(U)$ onto $U \times F$ with $\mathrm{pr}_1 \circ e = \pi$. So it maps the fiber $\pi^{-1}(b) = \iota_b(E_b)$ bijectively onto $\{b\} \times F$, and $e_b$ is a bijection. It is linear by hypothesis, so it is a linear isomorphism. Its continuity follows from $e_b = \mathrm{pr}_2 \circ e \circ \iota_b$, where $\iota_b$ takes values in the source of $e$. The inverse is $h(w) = e_b^{-1}(w)$ and $\iota_b(h(w)) = e^{-1}(b, w)$. The map $w \mapsto e^{-1}(b, w)$ is continuous, because $e^{-1}$ is continuous on $U \times F$. Since $\iota_b$ is inducing, $h$ is continuous. $\square$

**Corollary (Fibers).** Each fiber $E_b$ is isomorphic to $F$ as a topological vector space. If $F$ has finite dimension $n$, then $\dim E_b = n$.

*Proof.* Apply the theorem to the trivialization of the atlas at $b$. A linear isomorphism preserves dimension. $\square$

**Theorem (Coordinate changes).** For $b \in U \cap U'$, the coordinate change $g_{e e'}(b)$ is a continuous linear automorphism of $F$, with inverse $g_{e' e}(b)$. For three trivializations and $b$ in the three base sets, $g_{e' e''}(b) \circ g_{e e'}(b) = g_{e e''}(b)$.

*Proof.* The map $g_{e e'}(b) = e'_b \circ e_b^{-1}$ is a composite of continuous linear isomorphisms. Then $g_{e' e}(b) \circ g_{e e'}(b) = e_b \circ e'^{-1}_b \circ e'_b \circ e_b^{-1} = \mathrm{id}$, and the same computation gives the cocycle identity. $\square$

**Theorem (Zero section).** The zero section is continuous.

*Proof.* Fix $b_0$ and let $e$ be the trivialization of the atlas at $b_0$. For $b \in U$, $e(b, 0) = (b, e_b(0)) = (b, 0)$, because $e_b$ is linear. So on the open set $U$ the zero section equals $b \mapsto e^{-1}(b, 0)$, which is continuous. $\square$

**Theorem (Vector bundle from a core).** A vector bundle core defines a vector bundle with fibers $F$, whose atlas consists of the trivializations $e_i$ given by
$$e_i(b, v) = (b, g_{i(b)\, i}(b)\, v), \qquad b \in U_i,$$
and whose coordinate changes are $g_{e_i e_j}(b) = g_{ij}(b)$ on $U_i \cap U_j$.

*Proof.* Forget the linear structure. The maps $g_{ij}(b)$ define a fiber bundle core in the sense of Section 1: the identity and cocycle conditions are the same, and the map $(b, v) \mapsto g_{ij}(b) v$ is continuous on $(U_i \cap U_j) \times F$, because evaluation $L(F, F) \times F \to F$ is continuous. Section 1 gives the fiber bundle and the $e_i$. Each $e_i$ is linear on the fibers, because $g_{i(b) i}(b)$ is linear. For $b \in U_i \cap U_j$ and $w \in F$, write $k = i(b)$. Then $e_i^{-1}(b, w) = (b, g_{ik}(b) w)$, by the identity and cocycle conditions, and
$$g_{e_i e_j}(b)\, w = g_{kj}(b)\, g_{ik}(b)\, w = g_{ij}(b)\, w.$$
So $b \mapsto g_{e_i e_j}(b)$ equals $g_{ij}$ on $U_i \cap U_j$, which is continuous by hypothesis. $\square$

**Theorem (Hom bundle).** Let $E_1, E_2$ be vector bundles, with linear trivializations $e_1, e_1'$ of $E_1$ and $e_2, e_2'$ of $E_2$. On the intersection $W$ of the four base sets, the coordinate change of the Hom bundle is
$$\Phi(b) : T \mapsto g_{e_2 e_2'}(b) \circ T \circ g_{e_1' e_1}(b),$$
and $b \mapsto \Phi(b) \in L(L(F_1, F_2), L(F_1, F_2))$ is continuous on $W$.

*Proof.* The Hom trivialization from $e_1, e_2$ sends $T \in L(E_{1,b}, E_{2,b})$ to $e_{2,b} \circ T \circ e_{1,b}^{-1}$. A change to $e_1', e_2'$ conjugates by the coordinate changes, which gives the formula. For continuity, put $A = g_{e_2 e_2'}$ and $C = g_{e_1' e_1}$; both are continuous on $W$. For $b, b' \in W$ and $T$ with $\|T\| \le 1$,
$$\|A(b) T C(b) - A(b') T C(b')\| \le \|A(b) - A(b')\| \, \|C(b)\| + \|A(b')\| \, \|C(b) - C(b')\|.$$
The right side tends to $0$ as $b' \to b$, so $\|\Phi(b) - \Phi(b')\| \to 0$. $\square$

**Theorem (Finite dimension).** Let $F$ be finite dimensional and $e, e'$ linear trivializations of a fiber bundle. Then $b \mapsto g_{e e'}(b)$ is continuous on $U \cap U'$ for the operator norm.

*Proof.* Let $v_1, \dots, v_n$ be a basis of $F$. The map $A \mapsto \max_j \|A v_j\|$ is a norm on $L(F, F)$, and all norms on this finite dimensional space are equivalent (Volume 16, Chapter 3). So $\|A\| \le c \max_j \|A v_j\|$ for a constant $c$. Each $b \mapsto g_{e e'}(b) v_j = \mathrm{pr}_2(e'(e^{-1}(b, v_j)))$ is continuous on $U \cap U'$. Hence $\|g_{e e'}(b) - g_{e e'}(b_0)\| \le c \max_j \|g_{e e'}(b) v_j - g_{e e'}(b_0) v_j\| \to 0$. $\square$

In infinite dimension this fails. Pointwise continuity of $b \mapsto g(b) v$ does not give continuity for the operator norm, and Mathlib asks for the second.

### Examples

**Example (Trivial bundle).** The trivial bundle $B \times F$ has one trivialization, the identity. Its coordinate change is constant, so it is a vector bundle. A vector bundle core with all $g_{ij} = \mathrm{id}$ gives the same bundle.

**Example (Möbius line bundle).** The Möbius band of Section 1 has two trivializations over two arcs of $S^1$, and the coordinate changes are the constants $1$ and $-1$ on the two components of the intersection. These are linear and locally constant, so the Möbius band is a real vector bundle of rank $1$.

**Example (Whitney sum).** For two vector bundles $E_1, E_2$ over $B$, the fiberwise product $E_{1,b} \times E_{2,b}$ is a vector bundle with fiber $F_1 \times F_2$. Its coordinate change is $g_1(b) \times g_2(b)$, which is continuous in $b$.

**Example (Pullback).** For a continuous $f : B' \to B$, the coordinate changes of $f^* E$ are $g_{e e'} \circ f$, continuous on $f^{-1}(U \cap U')$.

**Example (Trivial Riemannian bundle).** Let $F$ be a real inner product space and $A : B \to L(F, F)$ continuous with $A(b)$ symmetric and $\langle A(b) v, v \rangle \ge m \|v\|^2$ for a constant $m > 0$. Then $g_b(v, w) = \langle A(b) v, w \rangle$ is a continuous Riemannian metric on $B \times F$. The bound $m \|v\|^2 \le g_b(v, v) \le \|A(b)\| \, \|v\|^2$ shows that $g_b$ defines the topology of $F$.

### The library around it

::: mathlib
`Bundle.Trivialization.continuousLinearEquivAt` · `Mathlib.Topology.VectorBundle.Basic`

`Bundle.Trivialization.continuousLinearEquivAt R e b hb : E b ≃L[R] F` is the first theorem above. `Bundle.Trivialization.continuousLinearMapAt` and `Bundle.Trivialization.symmL` are the two directions as maps defined for all `b`, with value `0` outside the base set. `VectorBundle.continuousLinearEquivAt R F E b` uses the trivialization of the atlas at `b`. `Bundle.Trivialization.continuous_zeroSection` is the zero section theorem.

<?decl Bundle.Trivialization.continuousLinearEquivAt?>
<?decl Bundle.Trivialization.continuous_zeroSection?>
<?decl VectorBundleCore.localTriv_coordChange_eq?>
<?decl VectorBundle.finrank_eq?>
:::

The core gives the bundle through the instances `VectorBundleCore.fiberBundle` and `VectorBundleCore.vectorBundle` on `Z.Fiber`, and `VectorBundleCore.localTriv_apply` is the formula for $e_i$. `VectorPrebundle` builds a vector bundle from linear pretrivializations, before any topology on the total space exists. The Hom bundle is built this way: `Bundle.ContinuousLinearMap.vectorPrebundle`, then the instance `Bundle.ContinuousLinearMap.vectorBundle`. It asks that each fiber of `E₂` is a topological additive group with continuous scalar multiplication. Its coordinate change `Bundle.Pretrivialization.continuousLinearMapCoordChange` is the map $\Phi$ above, and its continuity is `Bundle.Pretrivialization.continuousOn_continuousLinearMapCoordChange`. The bundle of continuous alternating maps has the instance `Bundle.ContinuousAlternatingMap.instVectorBundle`. The instances `Bundle.Trivial.vectorBundle`, `VectorBundle.prod` and `VectorBundle.pullback` are the trivial bundle, the Whitney sum and the pullback. `VectorBundle.finiteDimensional` and `VectorBundle.completeSpace` transfer finite dimension and completeness from $F$ to the fibers.

::: mathlib
`IsContinuousRiemannianBundle` · `Mathlib.Topology.VectorBundle.Riemannian`

`IsContinuousRiemannianBundle F E` assumes that each fiber already has an inner product. It says that there exists $g$ with $b \mapsto g_b$ continuous into the Hom bundle and $\langle v, w \rangle = g_b(v, w)$. `Bundle.RiemannianMetric E` is the data of the inner products, with a condition that they define the topology of the fibers. The class `Bundle.RiemannianBundle E` uses it to put an inner product space structure on each fiber without a second, different norm. `Bundle.ContinuousRiemannianMetric F E` is the continuous version. `Continuous.inner_bundle` says that the inner product of two continuous sections is continuous.

<?decl IsContinuousRiemannianBundle?>
<?decl Bundle.RiemannianMetric?>
<?decl Continuous.inner_bundle?>
:::

Common errors of a learner:

- Expecting `VectorBundle R F E` to give the atlas. The atlas is in `FiberBundle F E`; `VectorBundle` only adds two properties.
- Using `coordChangeL R e e' b` with `b` outside the base sets. It is then the identity, and no lemma about trivializations applies.
- Forgetting the operator norm condition in infinite dimension. A fiber bundle with linear trivializations is not always a vector bundle in the sense of Mathlib.

### Exercises

1. (A) Show that $e_b(v) = g_{e' e}(b)\,(e'_b(v))$ for $v \in E_b$ and $b \in U \cap U'$.
2. (A) Show that a vector bundle of rank $1$ over $B$ with a continuous section $s$ with $s(b) \neq 0$ for all $b$ is isomorphic to $B \times \Bbbk$. Deduce from Section 1 that the Möbius line bundle has no such section.
3. (B) Let $E$ be a vector bundle and $s, t$ continuous sections. Show that $s + t$ and $c\, s$ for $c \in \Bbbk$ are continuous. Hint: work in one trivialization and use the first theorem.
4. (B) Let $E$ be a real vector bundle with fiber $\mathbb{R}^n$ over a space $B$. Show that a Riemannian metric that is continuous in one trivialization near each point is continuous in every trivialization of the atlas.
5. (B) The dual bundle of $E$ is the Hom bundle from $E$ to $B \times \Bbbk$. Compute its coordinate changes in terms of those of $E$.
6. (C) Let $F$ be an infinite dimensional Banach space and $B = [0, 1]$. Construct a map $g : B \to L(F, F)$ with $g(b)$ invertible for all $b$, $b \mapsto g(b) v$ continuous for each $v$, and $g$ not continuous for the operator norm. Hint: take $F = \ell^2$ and let $g(b)$ act on the basis vector $e_n$ by a factor that depends on $b$ and $n$.

### Notes and history

The name Whitney sum refers to Hassler Whitney, who studied sphere bundles and their characteristic classes in the 1930s. The header of `Mathlib.Topology.VectorBundle.Basic` names Nicolò Cavalleri, Sébastien Gouëzel, Heather Macbeth, Patrick Massot and Floris van Doorn as authors. The header of `Mathlib.Topology.VectorBundle.Hom` names Heather Macbeth and Floris van Doorn, and that of `Mathlib.Topology.VectorBundle.Riemannian` names Sébastien Gouëzel.

### Reference

<?reference?>
