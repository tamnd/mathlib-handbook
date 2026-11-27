---
title: Dynamical nets, subsets and semiconjugacy
kind: theory
modules:
  - Mathlib.Dynamics.TopologicalEntropy.NetEntropy
  - Mathlib.Dynamics.TopologicalEntropy.Subset
  - Mathlib.Dynamics.TopologicalEntropy.Semiconj
explains:
  E3: [Dynamics.IsDynNetIn, Dynamics.netMaxcard, Dynamics.coverEntropy_eq_iSup_netEntropyEntourage, Dynamics.coverEntropy_closure, Dynamics.coverEntropy_union, Dynamics.coverEntropy_image_le_of_uniformContinuous]
  E2: [Dynamics.IsDynNetIn.card_le_card_of_isDynCoverOf, Dynamics.coverMincard_le_netMaxcard, Dynamics.netEntropyEntourage, Dynamics.coverEntropy_monotone, Dynamics.coverMincard_union_le, Dynamics.coverEntropy_iUnion_le, Dynamics.IsDynCoverOf.closure, Dynamics.IsDynCoverOf.image, Dynamics.coverMincard_image_le, Dynamics.coverEntropy_image_of_comap, Dynamics.coverEntropy_restrict, Dynamics.coverEntropySupBotHom]
  E1: auto
families: []
requires: [V13.C05, V13.C07, V21.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Dynamical nets, subsets and semiconjugacy

### Overview

Section 1 of this chapter defined the topological entropy $h(T, F)$ by minimal dynamical covers. This section uses its notation: $D_n(U)$, $N(F, U, n)$ and $h(T, F, U)$. It proves that the maximal size of a dynamical net gives the same entropy, and then the properties that make entropy a tool: it increases with the set, it takes the maximum on a finite union, it does not change under closure, and it does not increase under a uniformly continuous factor map. So it is an invariant of topological conjugacy on compact spaces. The full shift on $k$ symbols of Chapter 3 has entropy $\log k$.

### Definitions

As in Section 1, $X$ is a uniform space, $T : X \to X$, $F \subseteq X$, and the relation $D_n(U)$ is the dynamical entourage of $U$. For $x \in X$, write $B_n(x, U) = \{z : (x, z) \in D_n(U)\}$.

**Definition (Dynamical net).** A set $s$ is a *$(U, n)$-dynamical net* in $F$ if $s \subseteq F$ and the sets $B_n(x, U)$ for $x \in s$ are pairwise disjoint. The *maximal net size* $M(F, U, n)$ is the supremum of the cardinalities of the finite nets, in $\{0, 1, \ldots, \infty\}$. The *net entropy* at the scale $U$ is
$$h^{\mathrm{net}}(T, F, U) = \limsup_{n \to \infty} \frac{1}{n} \log M(F, U, n).$$

If $U$ is reflexive, distinct points $x, x'$ of a net satisfy $(x, x') \notin D_n(U)$, so a net is a separated set in the sense of Bowen. Exercise 4 is a converse.

::: mathlib
`Dynamics.IsDynNetIn` · `Mathlib.Dynamics.TopologicalEntropy.NetEntropy`

`IsDynNetIn T F U n s` is `s ⊆ F ∧ s.PairwiseDisjoint fun x ↦ (dynEntourage T U n).inv.ball x`. Here `(D.inv).ball x` is $B_n(x, U)$. Then `netMaxcard T F U n : ℕ∞` is the supremum of `s.card` over the nets `s : Finset X`, and `netEntropyEntourage T F U` is its `expGrowthSup`.

<?decl Dynamics.netMaxcard?>
:::

### Theorems and proofs

**Lemma (Nets and covers).** Let $s$ be a finite $(U, n)$-dynamical net in $F$ and $t$ a finite $(U, n)$-dynamical cover of $F$. Then $|s| \le |t|$. So $M(F, U, n) \le N(F, U, n)$.

*Proof.* For $x \in s \subseteq F$, choose $y(x) \in t$ with $(x, y(x)) \in D_n(U)$, that is $y(x) \in B_n(x, U)$. If $y(x) = y(x')$, the balls of $x$ and $x'$ meet, so $x = x'$. Thus $x \mapsto y(x)$ is injective. $\square$

**Lemma (A maximal net is a cover).** Let $U$ be reflexive and symmetric. Then $N(F, U \circ U, n) \le M(F, U, n)$.

*Proof.* Assume $M(F, U, n) < \infty$, and let $s$ be a net of maximal cardinality. Let $x \in F$. If $x \in s$, then $(x, x) \in D_n(U \circ U)$ by reflexivity. If $x \notin s$, then $s \cup \{x\}$ is not a net, so $B_n(x, U)$ meets $B_n(y, U)$ for some $y \in s$. Take $z$ in both. Then $(x, z) \in D_n(U)$ and, by symmetry, $(z, y) \in D_n(U)$, so $(x, y) \in D_n(U \circ U)$. Thus $s$ is a $(U \circ U, n)$-dynamical cover. $\square$

**Theorem (Nets give the entropy).** $h(T, F) = \sup_U h^{\mathrm{net}}(T, F, U)$, over the entourages $U$.

*Proof.* The first lemma gives $h^{\mathrm{net}}(T, F, U) \le h(T, F, U)$. Let $U$ be an entourage and $V$ a symmetric entourage with $V \circ V \subseteq U$; it is reflexive, as each entourage is. The second lemma gives $h(T, F, U) \le h(T, F, V \circ V) \le h^{\mathrm{net}}(T, F, V)$. $\square$

::: mathlib
`Dynamics.coverEntropy_eq_iSup_netEntropyEntourage` · `Mathlib.Dynamics.TopologicalEntropy.NetEntropy`

`coverEntropy T F = ⨆ U ∈ 𝓤 X, netEntropyEntourage T F U`. The two lemmas are `IsDynNetIn.card_le_card_of_isDynCoverOf` and `coverMincard_le_netMaxcard`, the second with `[U.IsRefl] [U.IsSymm]`.

<?decl Dynamics.coverEntropy_eq_iSup_netEntropyEntourage?>
:::

**Theorem (Finite unions).** If $F \subseteq G$, then $h(T, F) \le h(T, G)$. For all $F$ and $G$, $h(T, F \cup G) = \max(h(T, F), h(T, G))$.

*Proof.* A cover of $G$ covers $F$, which gives the first claim and the inequality $\ge$. The union of a cover of $F$ and a cover of $G$ covers $F \cup G$, so $N(F \cup G, U, n) \le 2 \max(N(F, U, n), N(G, U, n))$. Thus
$$\frac{1}{n} \log N(F \cup G, U, n) \le \frac{\log 2}{n} + \max\Big(\frac{1}{n}\log N(F, U, n), \frac{1}{n}\log N(G, U, n)\Big).$$
The limsup of a maximum is the maximum of the limsups, so $h(T, F \cup G, U) \le \max(h(T, F, U), h(T, G, U))$. Take the supremum over $U$. $\square$

For a countable union, only $\sup_i h(T, F_i) \le h(T, \bigcup_i F_i)$ holds (see the counterexample below).

::: mathlib
`Dynamics.coverEntropy_union` · `Mathlib.Dynamics.TopologicalEntropy.Subset`

`coverEntropy T (F ∪ G) = max (coverEntropy T F) (coverEntropy T G)`. The sum bound is `coverMincard_union_le`, and monotonicity is `coverEntropy_monotone`. Together they make `coverEntropySupBotHom T` a `SupBotHom (Set X) EReal`. The inequality for countable unions is `coverEntropy_iUnion_le`.

<?decl Dynamics.coverEntropy_union?>
:::

**Theorem (Closure).** If $T$ is continuous, then $h(T, \overline{F}) = h(T, F)$.

*Proof.* The inequality $\ge$ is monotonicity. Let $s$ be a $(U, n)$-dynamical cover of $F$, $V$ an entourage and $x \in \overline{F}$. The set $B_n(x, V)$ is the intersection of the sets $(T^k)^{-1}\{w : (T^k x, w) \in V\}$ for $k < n$, a neighbourhood of $x$ by continuity. So it meets $F$ at a point $z$. Choose $y \in s$ with $(z, y) \in D_n(U)$. Then $(x, y) \in D_n(V) \circ D_n(U) \subseteq D_n(V \circ U)$, so $s$ is a $(V \circ U, n)$-dynamical cover of $\overline{F}$. Thus $N(\overline{F}, V \circ U, n) \le N(F, U, n)$.

Let $W$ be an entourage, and choose an entourage $V$ with $V \circ V \subseteq W$. Then
$$h(T, \overline{F}, W) \le h(T, \overline{F}, V \circ V) \le h(T, F, V) \le h(T, F).$$
Take the supremum over $W$. $\square$

::: mathlib
`Dynamics.coverEntropy_closure` · `Mathlib.Dynamics.TopologicalEntropy.Subset`

`Continuous T → coverEntropy T (closure F) = coverEntropy T F`. The step on covers is `IsDynCoverOf.closure`: with `V ∈ 𝓤 X`, a cover for `U` of `F` is a cover for `V.comp U` of `closure F`.

<?decl Dynamics.coverEntropy_closure?>
:::

**Theorem (Factors).** Let $S : X \to X$ and $T : Y \to Y$ be maps and $\varphi : X \to Y$ a uniformly continuous map with $\varphi \circ S = T \circ \varphi$. Then $h(T, \varphi(F)) \le h(S, F)$.

*Proof.* Let $V$ be an entourage of $Y$ and $U = (\varphi \times \varphi)^{-1} V$, an entourage of $X$. From $T^k \varphi = \varphi S^k$, $(x, y) \in D_n^S(U)$ gives $(\varphi x, \varphi y) \in D_n^T(V)$. So the image of a $(U, n)$-dynamical cover of $F$ is a $(V, n)$-dynamical cover of $\varphi(F)$, and $N(\varphi(F), V, n) \le N(F, U, n)$. Thus $h(T, \varphi(F), V) \le h(S, F, U) \le h(S, F)$. Take the supremum over $V$. $\square$

**Corollary (Conjugacy invariance).** Let $X$ and $Y$ be compact, $\varphi : X \to Y$ a homeomorphism and $\varphi \circ S = T \circ \varphi$. Then $h(S, X) = h(T, Y)$.

*Proof.* By the theorem of Heine in Volume 13, Chapter 7, $\varphi$ and $\varphi^{-1}$ are uniformly continuous, and $\varphi^{-1} \circ T = S \circ \varphi^{-1}$. The theorem gives both inequalities. $\square$

::: mathlib
`Dynamics.coverEntropy_image_le_of_uniformContinuous` · `Mathlib.Dynamics.TopologicalEntropy.Semiconj`

`Function.Semiconj φ S T → UniformContinuous φ → ∀ F, coverEntropy T (φ '' F) ≤ coverEntropy S F`. The step on covers is `IsDynCoverOf.image`, and `coverMincard_image_le` bounds the cardinality with the pullback `Prod.map φ φ ⁻¹' V`. For the pullback uniformity on $X$, `coverEntropy_image_of_comap` gives equality. The lemma `coverEntropy_restrict` says that the entropy of the restriction of $T$ to an invariant set $F$ is $h(T, F)$. The index of this edition has no declaration for the corollary itself.

<?decl Dynamics.coverEntropy_image_le_of_uniformContinuous?>
:::

### Examples

**Example (The full shift).** Let $|A| = k$, $X = A^{\mathbb{Z}}$ with the product uniformity, and $(\sigma x)_i = x_{i+1}$, the shift of Chapter 3. The sets $U_r = \{(x, y) : x_i = y_i \text{ for } |i| \le r\}$ form a basis. Here $(x, y) \in D_n(U_r)$ if and only if $x_i = y_i$ for $-r \le i \le r + n - 1$, a window of $2r + n$ places. So $B_n(x, U_r)$ is the cylinder of the word of $x$ on this window. Choose one point for each of the $k^{2r+n}$ words. These points form a cover, and they form a net, because distinct cylinders are disjoint. With the first lemma, $N(X, U_r, n) = M(X, U_r, n) = k^{2r+n}$. So $h(\sigma, X, U_r) = \lim_n \frac{2r + n}{n}\log k = \log k$, and $h(\sigma, X) = \log k$. So full shifts on different numbers of symbols are not conjugate. The index of this edition has no declaration for this value.

**Counterexample (Countable unions).** Let $k \ge 2$ in the full shift, and let $P$ be the set of periodic points. It is countable and dense. Each singleton $\{x\}$ has entropy $0$, since $N(\{x\}, U, n) = 1$. But $\sigma$ is continuous, so the closure theorem gives $h(\sigma, P) = h(\sigma, X) = \log k$. Thus $h(\sigma, \bigcup_{x \in P} \{x\}) > \sup_{x \in P} h(\sigma, \{x\})$.

### The library around it

Mathlib proves each result for the limsup and for the liminf, with names such as `coverEntropyInf_closure`.

Common errors of a learner:

- In `IsDynNetIn` the disjoint sets are the forward balls `(dynEntourage T U n).inv.ball x`. This is a stronger condition than the separation $(x, x') \notin D_n(U)$.
- `coverEntropy_image_le_of_uniformContinuous` asks for uniform continuity of `φ`, not continuity. On a compact space, `CompactSpace.uniformContinuous_of_continuous` gives it.

### Exercises

1. (A) Show that a finite nonempty set $F$ has $h(T, F) = 0$.
2. (A) Let $T$ be uniformly continuous. Show that $h(T, T(F)) \le h(T, F)$.
3. (B) Let $X \subseteq \{0, 1\}^{\mathbb{Z}}$ be the golden mean shift, the set of sequences with no two consecutive $1$s. Show that $X$ is closed and invariant, and that $h(\sigma, X) = \log \frac{1 + \sqrt 5}{2}$. Hint: the number of allowed words of length $m$ is the Fibonacci number $F_{m+2}$.
4. (B) Let $U$ be symmetric, $s \subseteq F$, and $(x, x') \notin D_n(U \circ U)$ for distinct $x, x' \in s$. Show that $s$ is a $(U, n)$-dynamical net in $F$.
5. (B) Let $S$ and $T$ be maps of uniform spaces $X$ and $Y$ with nonempty $F \subseteq X$ and $G \subseteq Y$. Show that $h(S \times T, F \times G) \le h(S, F) + h(T, G)$. Hint: products of covers.
6. (B) A sliding block code is a map $\varphi : A^{\mathbb{Z}} \to B^{\mathbb{Z}}$ with $\varphi(x)_i = f(x_{i-r}, \ldots, x_{i+r})$. Show that $\varphi$ is uniformly continuous and commutes with the shifts. Deduce that if $\varphi$ is onto, then $|B| \le |A|$.

### Notes and history

Adler, Konheim and McAndrew introduced topological entropy in 1965 as an invariant of conjugacy. Bowen used spanning and separated sets of a metric space in 1971. The entropy of a shift of finite type is the logarithm of the spectral radius of its transition matrix. Exercise 3 is the case of the matrix with rows $(1, 1)$ and $(1, 0)$, whose spectral radius is the golden ratio.

### Reference

<?reference?>
