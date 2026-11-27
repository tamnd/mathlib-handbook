---
title: Smooth partitions of unity
kind: theory
modules:
  - Mathlib.Geometry.Manifold.PartitionOfUnity
  - Mathlib.Geometry.Manifold.SmoothApprox
explains:
  E3: [SmoothPartitionOfUnity, SmoothPartitionOfUnity.exists_isSubordinate, SmoothBumpCovering, exists_contMDiffMap_forall_mem_convex_of_local]
  E2: [SmoothBumpCovering.IsSubordinate, SmoothBumpCovering.exists_isSubordinate, SmoothBumpCovering.toSmoothPartitionOfUnity, SmoothBumpCovering.toSmoothPartitionOfUnity_apply, SmoothBumpCovering.eventuallyEq_one, SmoothBumpCovering.locallyFinite, SmoothPartitionOfUnity.IsSubordinate, SmoothPartitionOfUnity.sum_eq_one, SmoothPartitionOfUnity.locallyFinite, SmoothPartitionOfUnity.nonneg, SmoothPartitionOfUnity.sum_le_one, SmoothPartitionOfUnity.contMDiff_sum, SmoothPartitionOfUnity.toPartitionOfUnity, SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source, SmoothPartitionOfUnity.finsum_smul_mem_convex, SmoothPartitionOfUnity.contMDiff_finsum_smul, BumpCovering.toSmoothPartitionOfUnity, exists_contMDiffMap_zero_one_of_isClosed, exists_contMDiff_zero_iff_one_iff_of_isClosed, IsOpen.exists_contMDiff_support_eq, exists_contMDiffMap_one_nhds_of_subset_interior, exists_contMDiffMap_forall_mem_convex_of_local_const, exists_contMDiffSection_forall_mem_convex_of_local, Metric.exists_contMDiffMap_forall_closedBall_subset, Continuous.exists_contMDiff_approx, Continuous.exists_contMDiff_approx_and_eqOn, Continuous.exists_contDiff_approx, Continuous.exists_contDiff_approx_and_eqOn]
  E1: auto
families: []
requires: [V23.C02, V23.C03, V23.C05, V13.C04, V13.C05, V13.C08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Smooth partitions of unity

### Overview

A smooth partition of unity is a family of smooth functions $\rho_i : M \to [0, 1]$ with $\sum_i \rho_i = 1$, such that each point has a neighbourhood where only finitely many $\rho_i$ are not zero. If $g_i$ is defined near the support of $\rho_i$, then $\sum_i \rho_i g_i$ is defined on all of $M$.

This section constructs them on a Hausdorff, $\sigma$-compact manifold modelled on a finite dimensional real space, from locally finite covers, smooth bump coverings and a product formula. It then proves smooth Urysohn functions, gluing into convex sets, and smooth approximation.

### Definitions

Let $M$ be a topological space.

**Definition (Locally finite family).** A family $(A_i)_{i \in \iota}$ of subsets of $M$ is locally finite if each $x \in M$ has a neighbourhood $W$ such that $W \cap A_i \neq \emptyset$ for only finitely many $i$.

**Definition (Paracompact space).** $M$ is paracompact if every open cover of $M$ has a locally finite open refinement.

**Definition ($\sigma$-compact space).** $M$ is $\sigma$-compact if it is a countable union of compact sets.

Now let $M$ be a manifold modelled on $I : H \to E$, with $E$ finite dimensional and real, and $s \subseteq M$.

**Definition (Smooth bump covering).** A smooth bump covering of $s$ is a family $(f_i)_{i \in \iota}$ of smooth bump functions of Section 1, with centers $c_i$, such that $c_i \in s$ for all $i$, the family $(\mathrm{supp}\, f_i)$ is locally finite, and for each $x \in s$ there is $i$ with $f_i = 1$ on a neighbourhood of $x$. It is subordinate to a map $U : M \to \mathcal{P}(M)$ if $\overline{\mathrm{supp}}\, f_i \subseteq U(c_i)$ for all $i$.

**Definition (Smooth partition of unity).** A smooth partition of unity on $s$ is a family $(\rho_i)_{i \in \iota}$ of $C^\infty$ functions $M \to \mathbb{R}$ such that $\rho_i \ge 0$, the family $(\mathrm{supp}\, \rho_i)$ is locally finite, $\sum_i \rho_i(x) \le 1$ for all $x$, and $\sum_i \rho_i(x) = 1$ for $x \in s$. It is subordinate to a family $(U_i)_{i \in \iota}$ if $\overline{\mathrm{supp}}\, \rho_i \subseteq U_i$ for all $i$.

::: mathlib
`SmoothPartitionOfUnity` · `Mathlib.Geometry.Manifold.PartitionOfUnity`

`SmoothPartitionOfUnity ι I M s` has the default `s := Set.univ`. Its functions have type `C^∞⟮I, M; 𝓘(ℝ), ℝ⟯`, and the sums are `finsum`. The `SmoothBumpCovering.IsSubordinate` takes a map `U : M → Set M` evaluated at the centers, while `SmoothPartitionOfUnity.IsSubordinate` takes a family `U : ι → Set M`.

<?decl SmoothPartitionOfUnity?>
<?decl SmoothBumpCovering?>
<?decl SmoothBumpCovering.IsSubordinate?>
<?decl SmoothPartitionOfUnity.IsSubordinate?>
:::

### Theorems and proofs

**Theorem (Locally finite refinement).** Let $M$ be locally compact and $\sigma$-compact, $s \subseteq M$ closed, and for each $x \in s$ let $\mathcal{B}(x)$ be a basis of neighbourhoods of $x$. Then there are points $c_k \in s$ and sets $B_k \in \mathcal{B}(c_k)$ such that $s \subseteq \bigcup_k B_k$ and $(B_k)$ is locally finite.

*Proof.* A locally compact $\sigma$-compact space has compact sets $\emptyset = K_0 \subseteq K_1 \subseteq \dots$ with $K_n \subseteq \mathrm{int}\, K_{n+1}$ and $\bigcup_n K_n = M$. Put $K_{-1} = \emptyset$. For $n \ge 0$ let $C_n = s \cap (K_{n+1} \setminus \mathrm{int}\, K_n)$ and $O_n = \mathrm{int}\, K_{n+2} \setminus K_{n-1}$. $C_n$ is compact. The open set $O_n$ contains $C_n$, because $K_{n+1} \subseteq \mathrm{int}\, K_{n+2}$ and $K_{n-1} \subseteq \mathrm{int}\, K_n$. For $x \in C_n$ choose $B_x \in \mathcal{B}(x)$ with $B_x \subseteq O_n$. Finitely many interiors of these sets cover $C_n$. Collect these sets for all $n$. They cover $s$: a point $x \in s$ lies in $C_n$ for the least $n$ with $x \in K_{n+1}$. For local finiteness, let $y \in M$ and $y \in K_m$. The neighbourhood $\mathrm{int}\, K_{m+1}$ of $y$ lies in $K_{n-1}$ for $n \ge m + 2$, so it is disjoint from $O_n$ and meets only the finitely many sets of the stages $n \le m + 1$. $\square$

**Theorem (Existence of bump coverings).** Let $M$ be Hausdorff and $\sigma$-compact, $s \subseteq M$ closed, and let $U(x)$ be a neighbourhood of $x$ for each $x \in s$. Then there is a smooth bump covering of $s$ subordinate to $U$.

*Proof.* $M$ is locally compact. By Section 1, the supports of the bump functions $f$ at $x$ with $\overline{\mathrm{supp}}\, f \subseteq U(x)$ form a basis of neighbourhoods of $x$. The refinement theorem gives such $f_k$ at points $c_k \in s$, with supports that cover $s$ and are locally finite. $M$ is paracompact (apply the refinement theorem to $s = M$, with $\mathcal{B}(x)$ the open neighbourhoods of $x$ inside a member of the cover), so it is normal. By the shrinking lemma for the open, point-finite cover by the supports, there are closed sets $V_k \subseteq \mathrm{supp}\, f_k$ that still cover $s$. By the shrinking of the outer radius in Section 1, there is $\rho_k \in (0, R_k)$ with $V_k \subseteq \mathrm{dom}\,\varphi_k \cap \hat\varphi_k^{-1}(B(\hat c_k, \rho_k))$. Replace the inner radius of $f_k$ by $\rho_k$. The support depends only on $R_k$, and the new $f_k$ is $1$ on this open set. Each $x \in s$ lies in some $V_k$, so $f_k = 1$ near $x$. $\square$

**Theorem (From bump coverings to partitions).** Let $(f_i)$ be a smooth bump covering of $s$ on a Hausdorff $C^\infty$ manifold, and fix a well-order $<$ on $\iota$. Put
$$\rho_i = f_i \prod_{j < i} (1 - f_j).$$
Then $(\rho_i)$ is a smooth partition of unity on $s$, and $\overline{\mathrm{supp}}\, \rho_i \subseteq \overline{\mathrm{supp}}\, f_i$.

*Proof.* Let $x \in M$ and let $W$ be an open neighbourhood of $x$ that meets $\mathrm{supp}\, f_j$ only for $j$ in a finite set $J$. On $W$ the factors with $j \notin J$ are $1$, so $\rho_i = f_i \prod_{j \in J, j < i}(1 - f_j)$ is a finite product of $C^\infty$ functions. So $\rho_i$ is $C^\infty$. Since $0 \le f_j \le 1$, $0 \le \rho_i \le f_i$, so $\mathrm{supp}\, \rho_i \subseteq \mathrm{supp}\, f_i$, and the family of supports is locally finite. Write $J = \{j_1 < \dots < j_m\}$. By induction on $p$,
$$\sum_{l \le p} \rho_{j_l} = 1 - \prod_{l \le p}(1 - f_{j_l}) \quad \text{on } W,$$
because $1 - P + f_{j_{p+1}} P = 1 - (1 - f_{j_{p+1}}) P$ for $P = \prod_{l \le p}(1 - f_{j_l})$. All other $\rho_i$ vanish on $W$. So $\sum_i \rho_i = 1 - \prod_{j \in J}(1 - f_j) \le 1$ on $W$. If $x \in s$, some $f_j$ equals $1$ near $x$, so the product is $0$ at $x$ and the sum is $1$. $\square$

**Theorem (Partition subordinate to an open cover).** Let $M$ be a Hausdorff, $\sigma$-compact $C^\infty$ manifold, $s$ closed, and $(U_i)_{i \in \iota}$ open sets with $s \subseteq \bigcup_i U_i$. Then there is a smooth partition of unity on $s$ indexed by $\iota$ and subordinate to $(U_i)$.

*Proof.* Choose $i(x)$ with $x \in U_{i(x)}$ for $x \in s$. The existence theorem with $U(x) = U_{i(x)}$ gives a bump covering $(f_k)_{k \in \kappa}$ with $\overline{\mathrm{supp}}\, f_k \subseteq U_{i(c_k)}$, and the last theorem gives a partition $(\rho_k)$. Put $\sigma_i = \sum_{k : i(c_k) = i} \rho_k$. Locally this sum is finite, so $(\sigma_i)$ is a smooth partition of unity on $s$. The closure of a locally finite union of sets is the union of their closures, so $\overline{\mathrm{supp}}\, \sigma_i \subseteq \bigcup_{i(c_k) = i} \overline{\mathrm{supp}}\, \rho_k \subseteq U_i$. $\square$

**Corollary (Smooth Urysohn lemma).** Let $M$ be as in the theorem and $s, t \subseteq M$ disjoint closed sets. Then there is a $C^\infty$ function $g : M \to [0, 1]$ with $g = 0$ on $s$ and $g = 1$ on $t$.

*Proof.* Let $(\rho_k)$ be the partition on $t$ of a bump covering of $t$ subordinate to $U(x) = M \setminus s$. Then $g = \sum_k \rho_k$ is $C^\infty$, with values in $[0, 1]$, and $g = 1$ on $t$. Each $\rho_k$ vanishes on $s$, because $\overline{\mathrm{supp}}\, \rho_k \subseteq M \setminus s$. So $g = 0$ on $s$. $\square$

**Theorem (Gluing into convex sets).** Let $M$ be a Hausdorff, $\sigma$-compact $C^\infty$ manifold, $F$ a real normed space, and $t(x) \subseteq F$ convex for each $x \in M$. Suppose that each $x$ has a neighbourhood $U_x$ and a $C^n$ map $g_x$ on $U_x$ with $g_x(y) \in t(y)$ for $y \in U_x$. Then there is a $C^n$ map $g : M \to F$ with $g(y) \in t(y)$ for all $y$.

*Proof.* The open sets $\mathrm{int}\, U_x$ cover $M$. Let $(\rho_x)_{x \in M}$ be a smooth partition of unity on $M$ subordinate to them, and put $g = \sum_x \rho_x g_x$, with $\rho_x g_x = 0$ outside $\mathrm{supp}\, \rho_x$. Each term is $C^n$: if $y \in \overline{\mathrm{supp}}\, \rho_x \subseteq \mathrm{int}\, U_x$, then $\rho_x$ and $g_x$ are $C^n$ near $y$; otherwise the term is $0$ near $y$. The sum is locally finite, so $g$ is $C^n$. At $y$, the coefficients $\rho_x(y)$ are nonnegative with sum $1$, and $\rho_x(y) \neq 0$ gives $y \in U_x$, so $g(y)$ is a convex combination of points of $t(y)$. $\square$

**Corollary (Smooth approximation).** Let $M$ be as in the theorem, $f : M \to F$ continuous and $\varepsilon : M \to (0, \infty)$ continuous. Then there is a $C^n$ map $g$ with $\|g(y) - f(y)\| < \varepsilon(y)$ for all $y$ and $\mathrm{supp}\, g \subseteq \mathrm{supp}\, f$.

*Proof.* Put $t(y) = B(f(y), \varepsilon(y))$ if $f(y) \neq 0$ and $t(y) = \{0\}$ if $f(y) = 0$. These sets are convex. If $f(x) \neq 0$, take the constant $f(x)$ on the set of $y$ with $f(y) \neq 0$ and $\|f(y) - f(x)\| < \varepsilon(y)$. If $f(x) = 0$, take $0$ on the set of $y$ with $\|f(y)\| < \varepsilon(y)$. Both sets are open, contain $x$, and the constant lies in $t(y)$ on them. The theorem gives $g$ with $g(y) \in t(y)$, so $\|g(y) - f(y)\| < \varepsilon(y)$, and $g(y) = 0$ when $f(y) = 0$. $\square$

### Examples

**Example (A partition on the line).** Let $\psi(t) = e^{-1/t}$ for $t > 0$ and $\psi(t) = 0$ for $t \le 0$, and $h(t) = \psi(t)/(\psi(t) + \psi(1 - t))$. The denominator is positive, so $h$ is $C^\infty$ with $h = 0$ on $(-\infty, 0]$ and $h = 1$ on $[1, \infty)$. Put $\rho_2(t) = h(3t - 1)$ and $\rho_1 = 1 - \rho_2$. Then $\overline{\mathrm{supp}}\, \rho_2 = [1/3, \infty) \subseteq (0, \infty)$ and $\overline{\mathrm{supp}}\, \rho_1 = (-\infty, 2/3] \subseteq (-\infty, 1)$. So $(\rho_1, \rho_2)$ is subordinate to $((-\infty, 1), (0, \infty))$.

**Example (Riemannian metrics).** On a Hausdorff, $\sigma$-compact $C^\infty$ manifold, take the bundle of bilinear forms on the tangent spaces, built from the Hom bundles of Chapter 5, and let $t(x)$ be the convex set of positive definite symmetric forms. On a chart domain, the pullback of the inner product of $\mathbb{R}^n$ is a smooth local section with values in $t$. The gluing theorem for sections glues them into a Riemannian metric. The index of this edition has no declaration for this existence theorem as one statement.

### The library around it

::: mathlib
`SmoothPartitionOfUnity.exists_isSubordinate` · `Mathlib.Geometry.Manifold.PartitionOfUnity`

The theorem asks for `FiniteDimensional ℝ E`, `IsManifold I ∞ M`, `T2Space M` and `SigmaCompactSpace M`. Mathlib does not group indices. It applies `BumpCovering.exists_isSubordinate_of_prop` with the property "is smooth", fed by the smooth Urysohn lemma. Bump coverings come from `SmoothBumpCovering.exists_isSubordinate`; the product formula is `SmoothBumpCovering.toSmoothPartitionOfUnity_apply`.

<?decl SmoothPartitionOfUnity.exists_isSubordinate?>
<?decl SmoothBumpCovering.exists_isSubordinate?>
<?decl SmoothBumpCovering.toSmoothPartitionOfUnity?>
<?decl SmoothBumpCovering.toSmoothPartitionOfUnity_apply?>
<?decl BumpCovering.exists_isSubordinate_of_prop?>
:::

::: mathlib
`exists_contMDiffMap_forall_mem_convex_of_local` · `Mathlib.Geometry.Manifold.PartitionOfUnity`

The local maps satisfy `ContMDiffOn I 𝓘(ℝ, F) n g U` with `U ∈ 𝓝 x`. The two steps of the proof are `SmoothPartitionOfUnity.finsum_smul_mem_convex` and `SmoothPartitionOfUnity.contMDiff_finsum_smul`. Variants: `exists_contMDiffMap_forall_mem_convex_of_local_const` and, for sections of a vector bundle, `exists_contMDiffSection_forall_mem_convex_of_local`.

<?decl exists_contMDiffMap_forall_mem_convex_of_local?>
<?decl SmoothPartitionOfUnity.finsum_smul_mem_convex?>
<?decl SmoothPartitionOfUnity.contMDiff_finsum_smul?>
<?decl exists_contMDiffSection_forall_mem_convex_of_local?>
<?decl Continuous.exists_contMDiff_approx?>
:::

The topological input lives in other modules: `refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set` (refinement), `exists_subset_iUnion_closed_subset` (shrinking), the instances `paracompact_of_locallyCompact_sigmaCompact` and `NormalSpace.of_paracompactSpace_r1Space`, and `Manifold.locallyCompact_of_finiteDimensional`. The smooth Urysohn lemma is `exists_contMDiffMap_zero_one_of_isClosed`, and `exists_contMDiff_zero_iff_one_iff_of_isClosed` makes $s$ and $t$ the exact zero and one sets. `Continuous.exists_contMDiff_approx_and_eqOn` keeps $g = f$ on a closed set near which $f$ is smooth. `Continuous.exists_contDiff_approx` is for normed spaces.

`IsOpen.exists_contMDiff_support_eq` realizes an open set as a support.

Common errors of a learner:

- Looking for `SmoothPartitionOfUnity.contMDiff`, which does not exist. Each `f i` is a bundled map with smoothness `(f i).contMDiff`.
- Passing a family `ι → Set M` to `SmoothBumpCovering.IsSubordinate`. It takes a map `M → Set M`, read at the centers.
- Using these theorems on a $C^n$ manifold, $n$ finite. They need `IsManifold I ∞ M`.

### Exercises

1. (A) Let $(\rho_i)$ be a smooth partition of unity on $M$. Show that for each $x$ there is $i$ with $\rho_i(x) > 0$.
2. (B) Let $K \subseteq U \subseteq M$ with $K$ compact and $U$ open, on a Hausdorff, $\sigma$-compact $C^\infty$ manifold. Use the smooth Urysohn lemma to find a smooth $g : M \to [0, 1]$ with $g = 1$ on $K$ and $\overline{\mathrm{supp}}\, g \subseteq U$. Hint: first find an open $V$ with $K \subseteq V \subseteq \overline{V} \subseteq U$.
3. (B) Show that every closed set $s$ of such a manifold is the zero set of a smooth function $M \to [0, \infty)$. Hint: apply `IsOpen.exists_contMDiff_support_eq` to $M \setminus s$.
4. (B) Show that a locally finite family of compact sets in a $\sigma$-compact space is countable after removing the empty sets. Hint: each compact set of the exhaustion meets finitely many of them.
5. (B) Let $f : M \to \mathbb{R}$ be continuous and positive. Show that there is a smooth $g$ with $f/2 < g < 2f$. Hint: approximate with $\varepsilon = f/2$.
6. (C) Show that the line with two origins has no smooth partition of unity subordinate to the cover by the two copies of $\mathbb{R}$. Hint: Exercise 6 of Section 1.

### Notes and history

Jean Dieudonné introduced paracompact spaces in 1944. A. H. Stone proved in 1948 that metric spaces are paracompact. The header of `Mathlib.Geometry.Manifold.PartitionOfUnity` names Yury Kudryashov as author, and the header of `Mathlib.Geometry.Manifold.SmoothApprox` names Anatole Dedecker and Patrick Massot.

### Reference

<?reference?>
