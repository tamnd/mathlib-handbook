---
title: Completions of groups, rings and fields
kind: theory
modules:
  - Mathlib.Topology.Algebra.GroupCompletion
  - Mathlib.Topology.Algebra.UniformRing
  - Mathlib.Topology.Algebra.UniformField
  - Mathlib.Topology.Algebra.LinearMapCompletion
  - Mathlib.Topology.Algebra.InfiniteSum.GroupCompletion
  - Mathlib.Topology.Algebra.UniformFaithfulSMul
explains:
  E3: [AddMonoidHom.extension, UniformSpace.Completion.ring, CompletableTopField]
  E2: [UniformSpace.Completion.addGroup, UniformSpace.Completion.instAddCommGroup, UniformSpace.Completion.isUniformAddGroup, UniformSpace.Completion.toCompl, UniformSpace.Completion.coe_add, UniformSpace.Completion.instModule, AddMonoidHom.completion, UniformSpace.Completion.commRing, UniformSpace.Completion.topologicalRing, UniformSpace.Completion.coe_mul, UniformSpace.Completion.coeRingHom, UniformSpace.Completion.extensionHom, UniformSpace.Completion.mapRingHom, IsDenseInducing.extendRingHom, UniformSpace.Completion.instField, UniformSpace.Completion.instIsTopologicalDivisionRing, UniformSpace.Completion.hatInv, UniformSpace.Completion.mul_hatInv_cancel, completableTopField_of_complete, Subfield.completableTopField, IsUniformInducing.completableTopField, ContinuousLinearMap.completion, ContinuousLinearMap.fromCompletion, Summable.toCompl_tsum]
  E1: auto
families: []
requires: [V13.C07, V14.C01, V14.C02]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Completions of groups, rings and fields

### Overview

Volume 13, Chapter 7, builds the completion $\hat X$ of a uniform space $X$: a complete Hausdorff uniform space with a uniformly continuous map $\iota : X \to \hat X$ of dense image, such that each uniformly continuous map from $X$ to a complete Hausdorff space extends uniquely through $\iota$. This section puts algebra on $\hat X$: groups complete to groups, rings to rings, and fields to fields only under an extra condition. The real and the $p$-adic numbers are the main examples.

### Definitions

Throughout, a commutative topological group or ring carries the uniform structure of Section 1, with entourages $\{(x, y) : y - x \in V\}$ for $V$ a neighbourhood of $0$.

**Definition (Completable field).** A Hausdorff topological field $K$ is completable if for each Cauchy filter $\mathcal{F}$ on $K$ that does not have $0$ as a cluster point, that is, with $\mathcal{N}(0) \wedge \mathcal{F} = \bot$, the image $\mathcal{F}^{-1}$ under $x \mapsto x^{-1}$ is a Cauchy filter.

::: mathlib
`CompletableTopField` · `Mathlib.Topology.Algebra.UniformField`

A class for `[Field K] [UniformSpace K]` that extends `T0Space K` with the field `nice : ∀ F, Cauchy F → 𝓝 0 ⊓ F = ⊥ → Cauchy (map (fun x => x⁻¹) F)`. With `[IsTopologicalDivisionRing K] [IsUniformAddGroup K]` it gives the instances `UniformSpace.Completion.instField` and `UniformSpace.Completion.instIsTopologicalDivisionRing`. Instances: `completableTopField_of_complete` and `Subfield.completableTopField`.

<?decl CompletableTopField?>
:::

### Theorems and proofs

**Theorem (Completion of a commutative group).** Let $G$ be a commutative topological group. There is a unique structure of a topological group on $\hat G$ for which $\iota$ is a homomorphism. With it, $\hat G$ is a complete Hausdorff commutative uniform group, $\iota(G)$ is dense, and $\ker \iota = \overline{\{0\}}$.

*Proof.* By Section 1, $d(x, y) = x - y$ is uniformly continuous on $G \times G$, whose completion is $\hat G \times \hat G$ (Volume 13, Chapter 7). So there is a unique uniformly continuous $\hat d$ on $\hat G \times \hat G$ with $\hat d(\iota x, \iota y) = \iota(x - y)$. Define $-b = \hat d(0, b)$ and $a + b = \hat d(a, -b)$. Each group axiom, such as $(a + b) + c = a + (b + c)$, equates two continuous maps $\hat G^k \to \hat G$ that agree on the dense set $\iota(G)^k$. Into a Hausdorff space such maps are equal. As $\hat d$ is uniformly continuous, $\hat G$ is a uniform group. Finally $\iota(x) = \iota(y)$ if and only if $(x, y)$ lies in each entourage, that is, $y - x \in \overline{\{0\}}$. $\square$

**Theorem (Extension of homomorphisms).** Let $f : G \to H$ be a continuous homomorphism of commutative topological groups, with $H$ complete and Hausdorff. There is a unique continuous homomorphism $\hat f : \hat G \to H$ with $\hat f \circ \iota = f$.

*Proof.* By Section 1, $f$ is uniformly continuous, so the extension theorem gives a unique continuous $\hat f$ with $\hat f \circ \iota = f$. The maps $(a, b) \mapsto \hat f(a + b)$ and $(a, b) \mapsto \hat f(a) + \hat f(b)$ are continuous and agree on $\iota(G) \times \iota(G)$. So they are equal. $\square$

::: mathlib
`AddMonoidHom.extension` · `Mathlib.Topology.Algebra.GroupCompletion`

For `f : α →+ β` with `Continuous f`, where `β` is a complete `T0Space` with `IsUniformAddGroup β`, the result `Completion α →+ β`. The functorial form `AddMonoidHom.completion` maps `Completion α →+ Completion β`. Related: `UniformSpace.Completion.addGroup`, `UniformSpace.Completion.instAddCommGroup`, `UniformSpace.Completion.isUniformAddGroup`, `UniformSpace.Completion.toCompl` and the module instance `UniformSpace.Completion.instModule`.

<?decl AddMonoidHom.extension?>
:::

The multiplication of a ring is not uniformly continuous in general. On $\mathbb{R}$, the pairs $(n, n + 1/n)$ are close, but $(n + 1/n)^2 - n^2 = 2 + 1/n^2$ is not small. So the extension theorem does not apply directly. The next lemma replaces uniform continuity.

**Lemma (Products of Cauchy filters).** Let $R$ be a commutative topological ring and $\mathcal{F}, \mathcal{G}$ Cauchy filters on $R$. Then the image of $\mathcal{F} \times \mathcal{G}$ under the multiplication is a Cauchy filter.

*Proof.* First, for a Cauchy filter $\mathcal{F}$ and a neighbourhood $V$ of $0$ there are $A \in \mathcal{F}$ and a neighbourhood $W$ of $0$ with $AW \subseteq V$. Choose $V'$ with $V' + V' \subseteq V$, and $W_0$ with $W_0 W_0 \subseteq V'$, by the continuity of multiplication at $(0, 0)$. Choose $A \in \mathcal{F}$ with $A - A \subseteq W_0$, and fix $a_0 \in A$. By continuity of $x \mapsto a_0 x$ there is $W_1$ with $a_0 W_1 \subseteq V'$. Let $W = W_0 \cap W_1$. For $a \in A$ and $w \in W$, $aw = a_0 w + (a - a_0)w \in V' + W_0W_0 \subseteq V$. Now let $U$ be a neighbourhood of $0$, and choose $V$ with $V + V \subseteq U$. Choose $A \in \mathcal{F}$ and $W$ with $AW \subseteq V$, and $B \in \mathcal{G}$ and $W'$ with $BW' \subseteq V$. Shrink $A$ and $B$ so that $A - A \subseteq W'$ and $B - B \subseteq W$. For $a, a' \in A$ and $b, b' \in B$,
$$ab - a'b' = a(b - b') + (a - a')b' \in AW + W'B \subseteq V + V \subseteq U.$$
So the set $AB$ of the image filter is small of order $U$. $\square$

**Lemma (Extension of Cauchy continuous maps).** Let $D \subseteq X$ be dense in a uniform space $X$, let $Y$ be complete and Hausdorff, and let $g : D \to Y$ map Cauchy filters to Cauchy filters. Then $g$ extends to a continuous map $\hat g : X \to Y$.

*Proof.* For $x \in X$ the trace $\mathcal{F}_x$ of $\mathcal{N}(x)$ on $D$ is a Cauchy filter, so $g(\mathcal{F}_x)$ is Cauchy and converges to one point $\hat g(x)$. For $x \in D$, each set of $\mathcal{F}_x$ contains $x$, so each set of $g(\mathcal{F}_x)$ contains $g(x)$. Then $g(x)$ is a cluster point of the Cauchy filter $g(\mathcal{F}_x)$, and a Cauchy filter converges to each of its cluster points. So $\hat g(x) = g(x)$, as $Y$ is Hausdorff. For continuity, let $C$ be a closed neighbourhood of $\hat g(x)$. Closed neighbourhoods form a basis in a uniform space. There is an open $N \ni x$ with $g(N \cap D) \subseteq C$. For $x' \in N$, the filter $\mathcal{F}_{x'}$ contains $N \cap D$, so $\hat g(x')$ is a limit of a filter on $C$, and $\hat g(x') \in C$. $\square$

**Theorem (Completion of a commutative ring).** Let $R$ be a commutative topological ring. The multiplication of $R$ extends to $\hat R$, and $\hat R$ is a complete Hausdorff commutative topological ring with $\iota$ a ring homomorphism.

*Proof.* By the two lemmas, the multiplication on the dense set $\iota(R) \times \iota(R)$ extends to a continuous map $\hat R \times \hat R \to \hat R$. The ring axioms are equations between continuous maps that hold on a dense set, so they hold in the Hausdorff space $\hat R$. $\square$

::: mathlib
`UniformSpace.Completion.ring` · `Mathlib.Topology.Algebra.UniformRing`

The instance `Ring (Completion α)` for `[Ring α] [UniformSpace α] [IsTopologicalRing α] [IsUniformAddGroup α]`. Commutativity is not needed; `UniformSpace.Completion.commRing` adds it. Related: `UniformSpace.Completion.topologicalRing`, `UniformSpace.Completion.coeRingHom`, `UniformSpace.Completion.extensionHom` (into a complete `T0Space` ring), `UniformSpace.Completion.mapRingHom`, `IsDenseInducing.extendRingHom`, and the bilinear extension `IsDenseInducing.extend_Z_bilin`.

<?decl UniformSpace.Completion.ring?>
:::

**Theorem (Completion of a field).** Let $K$ be a completable Hausdorff topological field. Then $\hat K$ is a topological field.

*Proof.* By the previous theorem, $\hat K$ is a commutative ring. Let $x \ne 0$ in $\hat K$, and let $\mathcal{F}$ be the pullback to $K$ of $\mathcal{N}(x)$; it is a Cauchy filter. As $\hat K$ is Hausdorff, some neighbourhoods of $x$ and $0$ are disjoint, so $\mathcal{N}(0) \wedge \mathcal{F} = \bot$. By hypothesis $\mathcal{F}^{-1}$ is Cauchy and converges to some $y$. The map $t \mapsto t \cdot t^{-1}$ is constant $1$ on $K^\times$, so by continuity of multiplication $xy = 1$. The continuity of the inverse on $\hat K \setminus \{0\}$ follows from the lemma on extensions, applied to the dense subset $\iota(K^\times)$. $\square$

In Mathlib the inverse on the completion is `UniformSpace.Completion.hatInv`, and `UniformSpace.Completion.mul_hatInv_cancel` states $x \cdot x^{-1} = 1$ for $x \ne 0$.

### Examples

**Example (The real numbers).** The field $\mathbb{Q}$ with $|\cdot|$ is completable. Let $\mathcal{F}$ be Cauchy with $\mathcal{N}(0) \wedge \mathcal{F} = \bot$. Then there are $\delta > 0$ and $A \in \mathcal{F}$ with $|a| \ge \delta$ on $A$. For $a, b \in A$, $|a^{-1} - b^{-1}| = |b - a|/|ab| \le |a - b|/\delta^2$. So $\mathcal{F}^{-1}$ is Cauchy. The completion of $\mathbb{Q}$ is $\mathbb{R}$ (Volume 13, Chapter 7), and by the theorem it is a topological field. See `Rat.denseRange_cast` and `Real.instCompleteSpace`.

**Example (The $p$-adic numbers).** Let $|x|_p = p^{-v_p(x)}$ on $\mathbb{Q}$, where $v_p$ is the exponent of $p$ in $x$. By Exercise 6, $\mathbb{Q}$ is completable for $|\cdot|_p$. The completion is the field $\mathbb{Q}_p$. In it, $s_n = 1 + p + \dots + p^{n-1}$ satisfies $(1 - p)s_n = 1 - p^n \to 1$, so $s_n \to (1 - p)^{-1}$. For $p = 3$, $\sum 3^n = -1/2$. The ring $\mathbb{Z}$ with the $p$-adic topology of Chapter 2 has the completion $\mathbb{Z}_p$. See `Padic.instCompleteSpace` and `Padic.denseRange_ratCast`.

**Counterexample (A completion with zero divisors).** Give $\mathbb{Q}$ the topology induced by the diagonal map $\delta : \mathbb{Q} \to \mathbb{R} \times \mathbb{Q}_3$. It is a Hausdorff field topology, since the operations are continuous in each factor. The image is dense: given $(r, \alpha)$ and $\varepsilon > 0$, choose $a \in \mathbb{Q}$ with $|a - \alpha|_3 < \varepsilon$ and $N$ with $3^{-N} < \varepsilon$. As $3^N \mathbb{Z}[1/2]$ is dense in $\mathbb{R}$, some $q = a + 3^N z$ with $z \in \mathbb{Z}[1/2]$ has $|q - r| < \varepsilon$, and $|q - \alpha|_3 < \varepsilon$. So the completion is $\mathbb{R} \times \mathbb{Q}_3$, with the zero divisors $(1, 0)(0, 1) = 0$. Here $x_n = 3^n/(3^n + 1)$ tends to $(1, 0)$, so its filter is Cauchy and avoids $0$, but $x_n^{-1} = 1 + 3^{-n}$ has $|x_n^{-1}|_3 = 3^n$ and is not Cauchy.

**Remark (Common errors).** The completion of a topological field need not be a field; `CompletableTopField` is the extra hypothesis. Multiplication on $\mathbb{R}$ is not uniformly continuous, so the extension theorem for uniformly continuous maps does not give the ring structure; the lemma on Cauchy filters is needed. In Lean, `(x : Completion α)` is injective in `x` only under `T0Space`, by `UniformSpace.Completion.coe_injective`; `UniformSpace.Completion.coe_add` and `UniformSpace.Completion.coe_mul` move the coercion through the operations.

### The library around it

From Volume 13 come `UniformSpace.Completion.denseRange_coe` and `UniformSpace.Completion.extension`. A continuous linear map has a completion, `ContinuousLinearMap.completion`, and a map into a complete space extends from the completion, `ContinuousLinearMap.fromCompletion`. For sums, `Summable.toCompl_tsum` states that the map into the completion commutes with the sum; in this edition it takes a summation filter `L`, the subject of Chapter 4. A uniform embedding of fields into a completable field makes the source completable, `IsUniformInducing.completableTopField`.

The module `Mathlib.Topology.Algebra.UniformFaithfulSMul` shows that the completion of a field $K$ that is a faithful $R$-algebra is again faithful over $R$, when the completion is nontrivial (`UniformSpace.Completion.faithfulSMul`).

### Exercises

1. (A) Show that the completion of a complete Hausdorff commutative group $G$ is $G$, with $\iota$ an isomorphism. *Hint:* the identity of $G$ has the universal property.
2. (A) Show that the completion of $\mathbb{Z}$ with the discrete topology is $\mathbb{Z}$. *Hint:* a Cauchy filter on a discrete group is eventually constant.
3. (A) In $\mathbb{Q}_5$, compute the limit of $1 + 5 + 25 + \dots + 5^{n-1}$ and check the result by multiplication. *Hint:* use $(1 - p)s_n = 1 - p^n$.
4. (B) Show that the multiplication of $\mathbb{R}$ is uniformly continuous on $[-M, M]^2$ for each $M$. *Hint:* $xy - x'y' = x(y - y') + (x - x')y'$.
5. (B) Let $G$ be a commutative topological group with $\overline{\{0\}} = N$. Show that $\hat G$ is also the completion of $G/N$, and that $G/N \to \hat G$ is injective. *Hint:* the uniform structure of $G$ is pulled back from $G/N$.
6. (B) Show that the field $\mathbb{Q}$ with the $p$-adic absolute value is completable, with the same estimate as for the real numbers. *Hint:* $|a|_p \ge \delta$ on a set of the filter.
7. (C) Show that $\mathbb{Z}[1/2]$ is dense in $\mathbb{R}$, that $3^N\mathbb{Z}[1/2]$ is dense for each $N$, and complete the proof of density in the counterexample with $3$ replaced by any prime $p$ and $2$ by any prime $\ell \ne p$. *Hint:* $2^{-k}\mathbb{Z}$ has gaps $2^{-k}$.

### Notes and history

Hensel introduced the $p$-adic numbers in the 1890s, and Kürschák in 1913 constructed the completion of a field with an absolute value. The density of $\mathbb{Q}$ in $\mathbb{R} \times \mathbb{Q}_p$ is a case of the approximation theorem for inequivalent absolute values, proved by Artin and Whaples.

### Reference

<?reference?>
