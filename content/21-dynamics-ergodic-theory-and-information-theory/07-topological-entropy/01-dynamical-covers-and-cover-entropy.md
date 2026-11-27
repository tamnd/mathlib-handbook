---
title: Dynamical entourages and cover entropy
kind: theory
modules:
  - Mathlib.Dynamics.TopologicalEntropy.DynamicalEntourage
  - Mathlib.Dynamics.TopologicalEntropy.CoverEntropy
explains:
  E3: [Dynamics.dynEntourage, Dynamics.IsDynCoverOf, Dynamics.coverMincard, Dynamics.coverEntropyEntourage, Dynamics.coverEntropy, Dynamics.coverMincard_mul_le_pow, Dynamics.coverEntropyInf_eq_coverEntropy]
  E2: [Dynamics.mem_dynEntourage, Dynamics.dynEntourage_mem_uniformity, Dynamics.dynEntourage_comp_subset, Function.Semiconj.preimage_dynEntourage, Dynamics.coverEntropyInfEntourage, Dynamics.coverEntropyInf, Dynamics.IsDynCoverOf.iterate_le_pow, Dynamics.coverMincard_le_pow, Dynamics.coverEntropyEntourage_le_log_coverMincard_div, Dynamics.coverEntropyEntourage_le_coverEntropyInfEntourage, Dynamics.exists_isDynCoverOf_of_isCompact_invariant, Dynamics.coverEntropyEntourage_finite_of_isCompact_invariant, Dynamics.coverEntropy_eq_iSup_basis, Dynamics.coverEntropy_empty, Dynamics.coverEntropy_nonneg, Dynamics.coverMincard_finite_iff]
  E1: auto
families: []
requires: [V13.C05, V13.C07, V21.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Dynamical entourages and cover entropy

### Overview

Topological entropy measures how fast the orbits of a map separate. Two points are close at the scale $U$ and the time $n$ if their first $n$ iterates stay $U$-close. The number of points that approximate all orbit segments of length $n$ grows at an exponential rate, the entropy at the scale $U$. The topological entropy is the supremum over all scales. Mathlib states this definition of Bowen and Dinaburg for a uniform space, with the entourages of Volume 13, Chapter 7, as scales. The minimal cover size is submultiplicative. So the limsup and the liminf give the same entropy on an invariant set, and the entropy at each scale is finite on a compact invariant set.

### Definitions

Here $X$ is a uniform space, $T : X \to X$, $F \subseteq X$, and $U, V$ are relations on $X$. The relation $U \circ V$ is the set of pairs $(a, c)$ with $(a, b) \in U$ and $(b, c) \in V$ for some $b$.

**Definition (Dynamical entourage).** For $n \in \mathbb{N}$, the *dynamical entourage* of $U$ at time $n$ is
$$D_n(U) = \{(x, y) \in X \times X : (T^k x, T^k y) \in U \text{ for } 0 \le k < n\}.$$
Thus $D_0(U) = X \times X$ and $D_1(U) = U$. If $U$ is reflexive or symmetric, so is $D_n(U)$. If $T$ is uniformly continuous and $U$ is an entourage, then $D_n(U)$ is an entourage, as a finite intersection of preimages of $U$ under the maps $T^k \times T^k$. Also $D_n(U) \circ D_n(V) \subseteq D_n(U \circ V)$.

::: mathlib
`Dynamics.dynEntourage` · `Mathlib.Dynamics.TopologicalEntropy.DynamicalEntourage`

`dynEntourage T U n` is `⋂ k < n, (map T T)^[k] ⁻¹' U` for `U : SetRel X X`. The lemma `mem_dynEntourage` unfolds it, `dynEntourage_mem_uniformity` needs `UniformContinuous T`, and `dynEntourage_comp_subset` is the inclusion for compositions. Section 2 uses `Function.Semiconj.preimage_dynEntourage`, the behaviour under a semiconjugacy.

<?decl Dynamics.dynEntourage?>
:::

**Definition (Dynamical cover).** A set $s \subseteq X$ is a *$(U, n)$-dynamical cover* of $F$ if for each $x \in F$ there is $y \in s$ with $(x, y) \in D_n(U)$. The set $s$ need not lie in $F$. The *minimal cover size* $N(F, U, n)$ is the least cardinality of a finite $(U, n)$-dynamical cover of $F$, and $\infty$ if there is none. Only the empty set has $N(F, U, n) = 0$. A larger $U$, a smaller $F$ or a smaller $n$ gives a smaller $N$.

**Definition (Cover entropy).** The *entropy of $T$ on $F$ at the scale $U$* is
$$h(T, F, U) = \limsup_{n \to \infty} \frac{1}{n} \log N(F, U, n) \in [-\infty, \infty],$$
with the natural logarithm, $\log 0 = -\infty$ and $\log \infty = \infty$. The variant $h_{\inf}(T, F, U)$ uses the liminf. The *topological entropy* of $T$ on $F$ is $h(T, F) = \sup_U h(T, F, U)$ over the entourages $U$, and $h_{\inf}(T, F) = \sup_U h_{\inf}(T, F, U)$.

A smaller $U$ gives a larger $h(T, F, U)$, so a basis of the uniformity gives the same supremum. For a metric space, the sets $U_\varepsilon = \{d < \varepsilon\}$ form a basis. If $F = \emptyset$, then $h(T, F) = -\infty$; otherwise $N \ge 1$ and $h(T, F) \ge 0$. The entropy in bits is $h(T, F)/\log 2$.

::: mathlib
`Dynamics.coverEntropy` · `Mathlib.Dynamics.TopologicalEntropy.CoverEntropy`

`IsDynCoverOf T F U n s` is `IsCover (dynEntourage T U n) F s`, and `coverMincard T F U n : ℕ∞` is the infimum of the cardinalities of the covers `s : Finset X` (`coverMincard_finite_iff`). `coverEntropyEntourage T F U` is `expGrowthSup fun n ↦ coverMincard T F U n`. Here `ExpGrowth.expGrowthSup` is the limsup of `log (u n) / n` in `EReal`, with the natural logarithm `ENNReal.log`. The limsup form is the default; `coverEntropyInfEntourage` and `coverEntropyInf` use the liminf. `coverEntropy T F` is `⨆ U ∈ 𝓤 X, coverEntropyEntourage T F U`. The remarks above are `coverEntropy_eq_iSup_basis`, `coverEntropy_empty` and `coverEntropy_nonneg`.

<?decl Dynamics.coverEntropy?>
:::

### Theorems and proofs

**Lemma (Iteration of a cover).** Let $T(F) \subseteq F$, $U$ symmetric, and $s$ a finite $(U, m)$-dynamical cover of $F$. For each $n$ there is a $(U \circ U, mn)$-dynamical cover $t$ of $F$ with $|t| \le |s|^n$.

*Proof.* For a word $w = (y_0, \ldots, y_{n-1}) \in s^n$, let $F_w$ be the set of $x \in F$ with $(T^{jm} x, y_j) \in D_m(U)$ for all $j < n$. The sets $F_w$ cover $F$, because invariance puts each $T^{jm} x$ in $F$. Pick $x_w \in F_w$ for each $w$ with $F_w \neq \emptyset$, and let $t$ be the set of these points. Then $|t| \le |s|^n$.

Let $x \in F_w$ and $k = jm + i$ with $j < n$ and $i < m$. Then $(T^{i} T^{jm} x, T^i y_j) \in U$ and $(T^i T^{jm} x_w, T^i y_j) \in U$. The symmetry of $U$ gives $(T^i y_j, T^k x_w) \in U$, so $(T^k x, T^k x_w) \in U \circ U$. Thus $(x, x_w) \in D_{mn}(U \circ U)$. $\square$

**Corollary.** If $T(F) \subseteq F$ and $U$ is symmetric, then $N(F, U \circ U, mn) \le N(F, U, m)^n$. $\square$ (Apply the lemma to a minimal cover.)

::: mathlib
`Dynamics.coverMincard_mul_le_pow` · `Mathlib.Dynamics.TopologicalEntropy.CoverEntropy`

With `MapsTo T F F` and `[U.IsSymm]`: `coverMincard T F (U.comp U) (m * n) ≤ coverMincard T F U m ^ n`. The lemma is `IsDynCoverOf.iterate_le_pow`, and the second bound is `coverMincard_le_pow`.

<?decl Dynamics.coverMincard_mul_le_pow?>
:::

**Theorem (Entropy and one time).** Let $T(F) \subseteq F$, let $U$ be symmetric and $m \ge 1$. Then $h(T, F, U \circ U) \le \frac{1}{m} \log N(F, U, m)$.

*Proof.* If $N(F, U, m) = \infty$, the right side is $\infty$. If $N(F, U, m) = 0$, then $F = \emptyset$ and the left side is $-\infty$. Otherwise $c = N(F, U, m)$ is a positive integer. As $N$ increases with the time and $k \le m(\lfloor k/m \rfloor + 1)$, the corollary gives
$$\frac{1}{k} \log N(F, U \circ U, k) \le \frac{\lfloor k/m \rfloor + 1}{k} \log c \le \frac{\log c}{m} + \frac{\log c}{k}.$$
Let $k \to \infty$. $\square$

**Theorem (Limsup and liminf agree).** If $T(F) \subseteq F$, then $h_{\inf}(T, F) = h(T, F)$.

*Proof.* A liminf is at most a limsup, so $h_{\inf}(T, F) \le h(T, F)$. For symmetric $V$, the previous theorem for all $m \ge 1$ gives $h(T, F, V \circ V) \le h_{\inf}(T, F, V)$. Let $U$ be an entourage. Volume 13, Chapter 7, gives a symmetric entourage $V$ with $V \circ V \subseteq U$, so
$$h(T, F, U) \le h(T, F, V \circ V) \le h_{\inf}(T, F, V) \le h_{\inf}(T, F).$$
Take the supremum over $U$. $\square$

::: mathlib
`Dynamics.coverEntropyInf_eq_coverEntropy` · `Mathlib.Dynamics.TopologicalEntropy.CoverEntropy`

`MapsTo T F F → coverEntropyInf T F = coverEntropy T F`. The two steps are `coverEntropyEntourage_le_log_coverMincard_div` and `coverEntropyEntourage_le_coverEntropyInfEntourage`.

<?decl Dynamics.coverEntropyInf_eq_coverEntropy?>
:::

**Theorem (Finiteness on a compact invariant set).** Let $F$ be compact with $T(F) \subseteq F$, and let $U$ be an entourage. Then $N(F, U, n) < \infty$ for each $n$, and $h(T, F, U) < \infty$.

*Proof.* Choose a symmetric entourage $V$ with $V \circ V \subseteq U$. For $y \in F$, the set $\{x : (x, y) \in V\}$ is a neighbourhood of $y$. By compactness, finitely many of them, for $y$ in a finite set $s$, cover $F$, so $s$ is a $(V, 1)$-dynamical cover. The lemma gives a $(U, n)$-dynamical cover with at most $|s|^n$ points, and $h(T, F, U) \le h(T, F, V \circ V) \le \log |s|$ by the previous theorem with $m = 1$. $\square$ The entropy $h(T, F)$ itself can be $\infty$ (Exercise 5).

::: mathlib
`Dynamics.coverEntropyEntourage_finite_of_isCompact_invariant` · `Mathlib.Dynamics.TopologicalEntropy.CoverEntropy`

With `IsCompact F`, `MapsTo T F F` and `U ∈ 𝓤 X`, it gives `coverEntropyEntourage T F U < ⊤`. The finite cover is `exists_isDynCoverOf_of_isCompact_invariant`.

<?decl Dynamics.coverEntropyEntourage_finite_of_isCompact_invariant?>
:::

### Examples

**Example (Isometries).** Let $T$ be an isometry of a compact metric space $X$. Then $D_n(U_\varepsilon) = U_\varepsilon$ for $n \ge 1$, so $N(X, U_\varepsilon, n)$ is constant and finite, and $h(T, X, U_\varepsilon) = 0$. The $U_\varepsilon$ form a basis, so $h(T, X) = 0$.

**Example (The doubling map).** Let $X = \mathbb{R}/\mathbb{Z}$ with $d(x, y)$ the distance from $x - y$ to $\mathbb{Z}$, and $T x = 2x$, so $d(Tx, Ty) \le 2 d(x, y)$. Then $h(T, X) = \log 2$.

For the upper bound, let $M \ge 1/\varepsilon$ be an integer. Each $x$ is within $1/(2^{n+1} M)$ of a point $y$ of the form $j / (2^n M)$, and for $k < n$
$$d(T^k x, T^k y) \le 2^{n-1} \cdot \frac{1}{2^{n+1} M} = \frac{1}{4M} < \varepsilon.$$
So these $2^n M$ points form a $(U_\varepsilon, n)$-dynamical cover and $h(T, X, U_\varepsilon) \le \limsup_n \frac{1}{n}(n \log 2 + \log M) = \log 2$.

For the lower bound, let $\varepsilon \le 1/4$ and $(x, y) \in D_n(U_\varepsilon)$. Let $a_k \in (-\varepsilon, \varepsilon)$ represent $T^k x - T^k y$ for $k < n$. Then $2 a_k - a_{k+1}$ is an integer of absolute value less than $3\varepsilon < 1$, so $a_{k+1} = 2 a_k$. Thus $a_{n-1} = 2^{n-1} a_0$ and $|a_0| < 2^{1-n}\varepsilon$. So $\{x : (x, y) \in D_n(U_\varepsilon)\}$ is in an arc of length $4\varepsilon 2^{-n}$, and by the Lebesgue measure $N(X, U_\varepsilon, n) \ge 2^n/(4\varepsilon)$ and $h(T, X, U_\varepsilon) \ge \log 2$.

### The library around it

The index of this edition has no declaration for the entropy of a concrete system, for the definition by open covers, or for the variational principle.

Common errors of a learner:

- The theorems on iteration need the instance `U.IsSymm`. The lemma `comp_symm_mem_uniformity_sets` gives a symmetric entourage.
- `coverEntropy T ∅` is `⊥`, not `0`. A lemma with value $0$ needs `F.Nonempty`.
- On a compact invariant set, `coverEntropy` can still be `⊤`.

### Exercises

1. (A) Let $T$ be the identity of a compact space. Show that $h(T, X) = 0$.
2. (A) Show that $h(T^k, F) \le k\, h(T, F)$ for $k \ge 1$. Hint: $D_{kn}(U)$ for $T$ lies in $D_n(U)$ for $T^k$.
3. (B) Let $T x = q x$ on $\mathbb{R}/\mathbb{Z}$, for an integer $q \ge 2$. Show that $h(T, X) = \log q$.
4. (B) Let $F \subseteq \mathbb{R}^d$ be bounded and $T$ Lipschitz with constant $L > 1$. Show that $h(T, F) \le d \log L$. Hint: a grid of mesh $\varepsilon L^{1-n}$ is a $(U_\varepsilon, n)$-dynamical cover of $F$.
5. (C) Let $T$ be the shift $(Tx)_i = x_{i+1}$ on $X = [0, 1]^{\mathbb{N}}$. For $U = \{(x, y) : |x_0 - y_0| < \varepsilon\}$, show that $N(X, U, n) \ge \lfloor 1/(2\varepsilon) \rfloor^n$. Conclude that $h(T, X) = \infty$, though $h(T, X, U) < \infty$ for each entourage $U$.

### Notes and history

Adler, Konheim and McAndrew defined topological entropy in 1965 with open covers of a compact space. Dinaburg in 1970 and Bowen in 1971 gave the definition by spanning and separated sets of a metric space. On a compact metric space the definitions agree. The variational principle, which compares it with the measure theoretic entropies, is due to Goodwyn, Dinaburg and Goodman.

### Reference

<?reference?>
