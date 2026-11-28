---
title: Topological modules and continuous linear maps
kind: theory
modules:
  - Mathlib.Topology.Algebra.Module.Basic
  - Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
  - Mathlib.Topology.Algebra.Module.Equiv.Basic
  - Mathlib.Topology.Algebra.Module.ClosedSubmodule
  - Mathlib.Topology.Algebra.Algebra
  - Mathlib.Topology.Algebra.Projectivization
  - Mathlib.Topology.Algebra.Monoid.FunOnFinite
explains:
  E3: [ContinuousLinearMap, ContinuousLinearEquiv, Submodule.topologicalClosure]
  E2: [ContinuousLinearMap.toLinearMap, ContinuousLinearMap.continuous, ContinuousLinearMap.comp, ContinuousLinearMap.isClosed_ker, ContinuousLinearMap.smulRight, ContinuousLinearEquiv.toHomeomorph, Submodule.isClosed_topologicalClosure, Submodule.le_topologicalClosure, Submodule.topologicalClosure_minimal, Submodule.dense_iff_topologicalClosure_eq_top, LinearMap.continuous_on_pi, Submodule.isOpenMap_mkQ, Submodule.continuous_mkQ, ContinuousSMul.of_nhds_zero, ClosedSubmodule, ClosedSubmodule.isClosed, Submodule.closure, ContinuousAlgHom, ContinuousAlgHom.continuous, Subalgebra.topologicalClosure, continuous_algebraMap, algebraMapCLM]
  E1: auto
families: []
requires: [V07, V13.C01, V13.C04, V14.C01]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Topological modules and continuous linear maps

### Overview

A topological vector space is a vector space over a topological field with a topology in which addition and scalar multiplication are continuous. This section defines topological modules over a topological ring, and the continuous linear maps between them. These maps form the type `M →L[R] N` of Mathlib. The section proves that closures of submodules are submodules, that a linear map is continuous if it is continuous at $0$, and that each linear map out of $R^n$ is continuous. It shows with two examples that a linear map on an infinite-dimensional space need not be continuous.

### Definitions

**Definition (Topological module).** Let $R$ be a topological ring and $M$ an $R$-module with a topology. $M$ is a topological module if $M$ is a topological additive group and the scalar multiplication $R \times M \to M$, $(r, x) \mapsto rx$, is continuous. When $R$ is a topological field, $M$ is a topological vector space.

**Definition (Continuous linear map).** Let $M, N$ be topological $R$-modules. A continuous linear map $f : M \to N$ is an $R$-linear map that is continuous. A continuous linear equivalence is a linear bijection $f$ such that $f$ and $f^{-1}$ are continuous.

In Mathlib, a topological module is not a class of its own. A statement takes the two parts as separate hypotheses: `[IsTopologicalAddGroup M] [ContinuousSMul R M]`. Many results need less. The closure of a submodule needs only `ContinuousConstSMul R M`, the continuity of each map $x \mapsto rx$.

::: mathlib
`ContinuousLinearMap` · `Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic`

A structure that extends the linear map type `M →ₛₗ[σ] M₂` with a field `cont`. The notation is `M →SL[σ] M₂` for a ring hom `σ : R →+* S`, and `M →L[R] M₂` for the linear case `σ = RingHom.id R`. The semilinear form exists for conjugate linear maps on complex spaces, which are linear for `σ = starRingEnd ℂ`. A continuous linear map coerces to a function and, through `ContinuousLinearMap.toLinearMap`, to a linear map. `ContinuousLinearMap.continuous` extracts the continuity, and `ContinuousLinearMap.comp` composes. Mathlib bundles the continuity because `M →L[R] M₂` is itself a module, and in later volumes a normed space with the operator norm.

<?decl ContinuousLinearMap?>
:::

::: mathlib
`ContinuousLinearEquiv` · `Mathlib.Topology.Algebra.Module.Equiv.Basic`

The type `M ≃L[R] M₂` of linear equivalences with both directions continuous. `ContinuousLinearEquiv.toHomeomorph` gives the underlying homeomorphism. A linear bijection that is continuous need not have a continuous inverse, so the structure asks for both.

<?decl ContinuousLinearEquiv?>
:::

### Theorems and proofs

**Proposition (Closure of a submodule).** Let $M$ be a module with a topology in which addition is continuous and each map $x \mapsto rx$ is continuous. Then the closure $\overline{N}$ of a submodule $N$ is a submodule. It is the smallest closed submodule that contains $N$.

*Proof.* The addition $a$ is continuous and $a(N \times N) \subseteq N$, so $a(\overline{N} \times \overline{N}) = a(\overline{N \times N}) \subseteq \overline{N}$. For $r \in R$ the map $x \mapsto rx$ is continuous and maps $N$ into $N$, so it maps $\overline{N}$ into $\overline{N}$. Also $0 \in N \subseteq \overline{N}$. A closed submodule that contains $N$ contains its closure. $\square$

::: mathlib
`Submodule.topologicalClosure` · `Mathlib.Topology.Algebra.Module.Basic`

`N.topologicalClosure : Submodule R M` under `[ContinuousConstSMul R M] [ContinuousAdd M]`, the exact hypotheses of the proposition. The lemmas `Submodule.isClosed_topologicalClosure`, `Submodule.le_topologicalClosure` and `Submodule.topologicalClosure_minimal` give the three properties, and `Submodule.dense_iff_topologicalClosure_eq_top` relates it to density. The module `Mathlib.Topology.Algebra.Module.ClosedSubmodule` has the bundled type `ClosedSubmodule R M` and the map `Submodule.closure` into it, with `ClosedSubmodule.isClosed`.

<?decl Submodule.topologicalClosure?>
:::

**Proposition (Continuity at zero).** Let $f : M \to N$ be a linear map between topological modules. If $f$ is continuous at $0$, then $f$ is continuous.

*Proof.* The map $f$ is a homomorphism of additive topological groups. Apply the proposition on continuity at the identity of Chapter 1, Section 2. $\square$

**Proposition (Maps out of $R^n$).** Let $R$ be a topological ring, $M$ a topological $R$-module and $f : R^n \to M$ a linear map. Then $f$ is continuous.

*Proof.* Let $e_1, \dots, e_n$ be the standard basis of $R^n$ and $m_i = f(e_i)$. For $x = (x_1, \dots, x_n)$, linearity gives $f(x) = \sum_i x_i m_i$. Each map $x \mapsto x_i m_i$ is the composite of the projection $x \mapsto x_i$, which is continuous, and of $r \mapsto r m_i$, which is continuous because scalar multiplication is. A finite sum of continuous maps into $M$ is continuous, because addition is. $\square$

This is `LinearMap.continuous_on_pi`, for an index type with `[Finite ι]`. The converse direction, from $M$ into $R^n$, is the hard part of Section 3: it needs a Hausdorff space and a complete field.

**Proposition (Kernels and quotients).** Let $f : M \to N$ be a continuous linear map and $N$ a $T_1$ space. Then $\ker f$ is closed. For a submodule $L \le M$, the quotient $M/L$ with the quotient topology is a topological module, the map $M \to M/L$ is continuous and open, and $M/L$ is Hausdorff if and only if $L$ is closed.

*Proof.* $\ker f = f^{-1}(\{0\})$, and $\{0\}$ is closed in a $T_1$ space. For the quotient, the additive part is the theorem on quotient groups of Chapter 1, Section 3, which also gives the openness and the separation. Let $\pi : M \to M/L$ and let $s'$ be the scalar multiplication of $M/L$. Then $s' \circ (\mathrm{id}_R \times \pi) = \pi \circ s$ is continuous, and $\mathrm{id}_R \times \pi$ is an open continuous surjection, so it is a quotient map. Therefore $s'$ is continuous. $\square$

The kernel lemma is `ContinuousLinearMap.isClosed_ker`, and the quotient lemmas are `Submodule.continuous_mkQ` and `Submodule.isOpenMap_mkQ`.

**Proposition (A criterion at zero).** Let $R$ be a topological ring and $M$ a topological additive group with an $R$-module structure. Suppose that $rx \to 0$ as $(r, x) \to (0, 0)$, that $rx_0 \to 0$ as $r \to 0$ for each $x_0$, and that $r_0 x \to 0$ as $x \to 0$ for each $r_0$. Then scalar multiplication is continuous.

*Proof.* Let $(r, x) \to (r_0, x_0)$ and write $r = r_0 + s$, $x = x_0 + y$ with $s \to 0$ and $y \to 0$. Then $rx - r_0x_0 = r_0 y + s x_0 + s y$. The three terms tend to $0$ by the three hypotheses, and addition is continuous. $\square$

In Mathlib this is `ContinuousSMul.of_nhds_zero`. It is the usual way to put a topological module structure on a space defined by a basis of neighbourhoods of $0$.

### Examples

**Example (Euclidean space).** $\mathbb{R}^n$ with the product topology is a topological vector space over $\mathbb{R}$: scalar multiplication $(t, x) \mapsto (tx_1, \dots, tx_n)$ has continuous components. By the proposition on maps out of $R^n$, each linear map $\mathbb{R}^n \to \mathbb{R}^m$ is continuous. So $\mathbb{R}^n \to_L \mathbb{R}^m$ is the set of all $m \times n$ matrices.

**Example (Evaluation on continuous functions).** Let $C[0,1]$ be the space of continuous real functions on $[0,1]$ with the norm $\|f\|_\infty = \sup |f|$. For $t \in [0,1]$ the map $\mathrm{ev}_t(f) = f(t)$ is linear, and $|\mathrm{ev}_t(f) - \mathrm{ev}_t(g)| \le \|f - g\|_\infty$, so it is continuous. The map $I(f) = \int_0^1 f$ is continuous too, with $|I(f)| \le \|f\|_\infty$. The kernel of $\mathrm{ev}_0$ is the closed hyperplane of functions that vanish at $0$.

**Counterexample (Differentiation).** Let $P \subseteq C[0,1]$ be the subspace of polynomials, and $D : P \to P$, $D(p) = p'$. $D$ is linear. Let $p_n(x) = x^n/n$. Then $\|p_n\|_\infty = 1/n \to 0$, but $D(p_n) = x^{n-1}$ has norm $1$. So $D(p_n) \not\to 0 = D(0)$, and $D$ is not continuous at $0$. The space $P$ is infinite-dimensional. Section 3 shows that in finite dimension each linear map between Hausdorff spaces over $\mathbb{R}$ is continuous.

**Counterexample (A discontinuous functional with dense kernel).** Let $c_{00}$ be the space of real sequences with finitely many nonzero terms, with the norm $\|x\|_\infty = \max |x_n|$. Let $\ell(x) = \sum_n n x_n$, a finite sum. Then $\ell(e_n/n) = 1$ while $\|e_n/n\|_\infty = 1/n \to 0$, so $\ell$ is not continuous. Its kernel is dense. For $x \in c_{00}$ the vectors $x - \ell(x) e_n/n$ lie in $\ker \ell$ and tend to $x$. So $\ker \ell$ is a submodule that is not closed, and its closure is the whole space. Section 3 proves that a linear functional on a topological vector space is continuous if and only if its kernel is closed.

**Example (Continuous algebra maps).** For a topological ring $A$ that is an algebra over a topological ring $R$ with continuous scalar multiplication, the map $R \to A$, $r \mapsto r \cdot 1$, is continuous linear (`algebraMapCLM`, `continuous_algebraMap`). A continuous algebra homomorphism is `ContinuousAlgHom`, written `A →A[R] B`. The evaluation $\mathrm{ev}_t : C[0,1] \to \mathbb{R}$ is one. The closure of a subalgebra is a subalgebra, `Subalgebra.topologicalClosure`. By the Weierstrass theorem, the closure of the subalgebra of polynomials in $C[0,1]$ is the whole space.

::: mathlib
`ContinuousAlgHom` · `Mathlib.Topology.Algebra.Algebra`

The structure `A →A[R] B`, an algebra hom `A →ₐ[R] B` with a field `cont`. It follows the pattern of `ContinuousLinearMap`. `ContinuousAlgHom.continuous` extracts the continuity.

<?decl ContinuousAlgHom?>
:::

**Remark (Common errors).** A learner often treats `f : M →L[R] N` as a linear map. It is a different type, and Lean inserts a coercion: `(f : M →ₗ[R] N)` is `f.toLinearMap`, and `⇑f` is the function. A second error is to expect that a continuous linear bijection has a continuous inverse. Over Banach spaces this holds by the open mapping theorem, but in general it fails: the identity from $(c_{00}, \|\cdot\|_1)$ to $(c_{00}, \|\cdot\|_\infty)$ is continuous, since $\|x\|_\infty \le \|x\|_1$, and its inverse is not, since $\|e_1 + \dots + e_n\|_1 = n$.

### The library around it

The module `Mathlib.Topology.Algebra.Module.Basic` holds the closures, the quotients and the criteria for continuity. The type `M →L[R] N` and its operations are in `Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic`, and equivalences in `Mathlib.Topology.Algebra.Module.Equiv.Basic`. The map `ContinuousLinearMap.smulRight c f` is $x \mapsto c(x) \cdot f$; with $c$ the identity of $R$ it gives the map $t \mapsto tf$ from $R$ to $M$. Algebras are in `Mathlib.Topology.Algebra.Algebra`.

The module `Mathlib.Topology.Algebra.Projectivization` gives the projective space $\mathbb{P}(V)$ of a topological vector space $V$ the quotient topology of the map $V \setminus \{0\} \to \mathbb{P}(V)$, $v \mapsto [v]$ (`Projectivization.mk'`). A map out of $\mathbb{P}(V)$ is continuous if and only if its composite with this map is continuous (`Projectivization.continuous_iff`). When each map $v \mapsto cv$ with $c$ a unit is continuous, the map $v \mapsto [v]$ is open, so it is an open quotient map (`Projectivization.isOpenQuotientMap_mk'`). The module `Mathlib.Topology.Algebra.Monoid.FunOnFinite` shows that for a map $f : X \to Y$ of finite types the map $M^X \to M^Y$ that sums over the fibres of $f$ is continuous (`FunOnFinite.continuous_map`, `FunOnFinite.continuous_linearMap`).

### Exercises

1. (A) Show that each linear functional $\mathbb{R}^n \to \mathbb{R}$ is $x \mapsto \sum_i a_i x_i$ and is continuous.
2. (A) Let $f, g : M \to N$ be continuous linear maps, with $N$ Hausdorff, that agree on a dense submodule. Show that $f = g$.
3. (A) Show that the composite of two continuous linear maps is a continuous linear map and that the set of continuous linear maps $M \to N$ is a submodule of the linear maps when $R$ is commutative.
4. (B) Let $M$ be a topological vector space over $\mathbb{R}$ and $H$ a hyperplane. Show that $H$ is either closed or dense. *Hint:* $\overline{H}$ is a subspace that contains $H$.
5. (B) Show that the map $C[0,1] \to C[0,1]$, $f \mapsto (x \mapsto \int_0^x f)$, is continuous linear, and find a bound for its norm.
6. (B) On $c_{00}$ with $\|\cdot\|_\infty$, show that $\ell(x) = \sum_n x_n$ is not continuous and that $\ell'(x) = \sum_n x_n/n^2$ is continuous.
7. (C) Let $\ell$ be a linear functional on a real topological vector space $M$ that is bounded on a neighbourhood $V$ of $0$: $|\ell| \le C$ on $V$. Show that $\ell$ is continuous. *Hint:* $|\ell| \le \varepsilon$ on $(\varepsilon/C) V$, and $(\varepsilon / C) V$ is a neighbourhood of $0$.

### Notes and history

Topological vector spaces in the general sense come from the work of Kolmogorov and von Neumann in the 1930s. Bourbaki's "Espaces vectoriels topologiques" fixed the modern treatment. The examples of discontinuous linear maps show why functional analysis restricts to continuous ones. The type `M →L[R] N` is the space of such maps, and later volumes give it a norm and the strong and weak topologies.

### Reference

<?reference?>
