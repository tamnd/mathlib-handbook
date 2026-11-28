---
title: The completion of a uniform space
kind: theory
modules:
  - Mathlib.Topology.UniformSpace.Completion
  - Mathlib.Topology.UniformSpace.UniformEmbedding
  - Mathlib.Topology.UniformSpace.AbstractCompletion
  - Mathlib.Topology.UniformSpace.CompareReals
  - Mathlib.Topology.UniformSpace.CompleteSeparated
explains:
  E3: [UniformSpace.Completion, uniformly_extend_exists]
  E2: [CauchyFilter, UniformSpace.Completion.completeSpace, UniformSpace.Completion.denseRange_coe, UniformSpace.Completion.isUniformEmbedding_coe, UniformSpace.Completion.coe_injective, UniformSpace.Completion.extension, UniformSpace.Completion.extension_coe, UniformSpace.Completion.uniformContinuous_extension, UniformSpace.Completion.extension_unique, UniformSpace.Completion.map, IsUniformInducing, IsUniformEmbedding, uniformContinuous_uniformly_extend, uniformly_extend_spec, Continuous.ext_on]
  E1: auto
families: []
requires: [V13.C02, V13.C03, V13.C04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The completion of a uniform space

### Overview

Each uniform space $X$ sits densely in a complete Hausdorff uniform space $\hat X$, its completion. The completion of $\mathbb{Q}$ is $\mathbb{R}$, and the completion of $\mathbb{Q}$ with the $p$-adic metric is $\mathbb{Q}_p$. The completion has a universal property: each uniformly continuous map from $X$ to a complete Hausdorff space extends in exactly one way to a uniformly continuous map on $\hat X$. This section proves the extension theorem and sketches the construction with Cauchy filters.

### Definitions

**Definition (Uniform embedding).** A map $e : X \to Y$ of uniform spaces is uniformly inducing if the entourages of $X$ are exactly the preimages under $e \times e$ of the entourages of $Y$. It is a uniform embedding if it is also injective.

::: mathlib
`IsUniformInducing` · `Mathlib.Topology.UniformSpace.Defs`

The structure with the field `comap_uniformity`: `comap (fun x => (f x.1, f x.2)) (𝓤 β) = 𝓤 α`. `IsUniformEmbedding` adds injectivity. The inclusion of a subspace with the induced uniformity is the main example.

<?decl IsUniformInducing?>
:::

**Definition (Completion).** A completion of $X$ is a complete Hausdorff uniform space $\hat X$ with a uniformly continuous map $\iota : X \to \hat X$ of dense range, such that $\iota$ is uniformly inducing.

If $X$ is Hausdorff, then $\iota$ is a uniform embedding, and $X$ is identified with a dense subspace of $\hat X$.

::: mathlib
`UniformSpace.Completion` · `Mathlib.Topology.UniformSpace.Completion`

The completion, built as the space of minimal Cauchy filters `CauchyFilter α` modulo the relation of being inseparable. The coercion `↑a` sends `a` to the class of the filter of `𝓝 a`. The instance `UniformSpace.Completion.completeSpace` gives completeness, `UniformSpace.Completion.denseRange_coe` the dense range, and `UniformSpace.Completion.isUniformEmbedding_coe` the embedding for a `T0Space`.

<?decl UniformSpace.Completion?>
:::

### Theorems and proofs

**Theorem (Extension).** Let $e : A \to X$ be uniformly inducing with dense range, $Y$ complete and Hausdorff, and $f : A \to Y$ uniformly continuous. There is a unique continuous $g : X \to Y$ with $g \circ e = f$, and $g$ is uniformly continuous.

*Proof.* Uniqueness. Two continuous maps to a Hausdorff space that agree on a dense set agree everywhere: the set where they agree is closed, since it is the preimage of the closed diagonal of $Y \times Y$.

Existence. Fix $x \in X$. The filter $F_x = e^{-1}(\mathcal{N}(x))$ on $A$, with members the sets $e^{-1}(N)$ for $N \in \mathcal{N}(x)$, is proper, since $e$ has dense range and each $N$ meets $e(A)$. It is Cauchy. Let $V$ be an entourage of $A$. Since $e$ is uniformly inducing, $V \supseteq (e \times e)^{-1}(W)$ for an entourage $W$ of $X$. Choose a symmetric $W'$ with $W' \circ W' \subseteq W$. For $a, b \in e^{-1}(W'[x])$, $(e(a), e(b)) \in W$, so $(a, b) \in V$. So the member $e^{-1}(W'[x])$ of $F_x$ is $V$-small.

The image $f(F_x)$ is Cauchy, since $f$ is uniformly continuous. As $Y$ is complete, it converges, and the limit is unique since $Y$ is Hausdorff. Define $g(x)$ as this limit. For $x = e(a)$, $F_x \le \mathcal{N}(a)$ because $e$ is continuous, so $f(F_x) \le \mathcal{N}(f(a))$ and $g(e(a)) = f(a)$.

Uniform continuity. Let $W$ be a closed entourage of $Y$; these form a basis of $\mathcal{U}_Y$. Choose an entourage $V$ of $A$ with $(f(a), f(b)) \in W$ for $(a, b) \in V$, and an entourage $U$ of $X$ with $(e \times e)^{-1}(U) \subseteq V$. Choose an open symmetric $U'$ with $U' \circ U' \circ U' \subseteq U$. Let $(x, y) \in U'$. For $a \in e^{-1}(U'[x])$ and $b \in e^{-1}(U'[y])$, the pair $(e(a), e(b))$ lies in $U' \circ U' \circ U' \subseteq U$, so $(f(a), f(b)) \in W$. The set $f(e^{-1}(U'[x])) \times f(e^{-1}(U'[y]))$ belongs to the product filter $f(F_x) \times f(F_y)$, which converges to $(g(x), g(y))$. So $(g(x), g(y))$ lies in the closure of $W$, which is $W$. $\square$

::: mathlib
`uniformly_extend_exists` · `Mathlib.Topology.UniformSpace.UniformEmbedding`

The existence of the limit of `f` along `comap e (𝓝 a)`, the filter $F_x$ of the proof. The extension itself is `IsDenseInducing.extend`; `uniformly_extend_spec` gives its limit property and `uniformContinuous_uniformly_extend` its uniform continuity.

<?decl uniformly_extend_exists?>
:::

::: mathlib
`Continuous.ext_on` · `Mathlib.Topology.Separation.Hausdorff`

The uniqueness step: two continuous maps to a `T2Space` that agree on a dense set are equal.

<?decl Continuous.ext_on?>
:::

**Corollary (Universal property).** Let $Y$ be complete and Hausdorff, and $f : X \to Y$ uniformly continuous. There is exactly one uniformly continuous $\hat f : \hat X \to Y$ with $\hat f(\iota(x)) = f(x)$. Two completions of $X$ are isomorphic by a unique uniform isomorphism that commutes with the maps from $X$.

*Proof.* The first claim is the theorem with $e = \iota$. For two completions $(\hat X, \iota)$ and $(\tilde X, \kappa)$, extend $\kappa$ to $\hat\kappa : \hat X \to \tilde X$ and $\iota$ to $\hat\iota : \tilde X \to \hat X$. The map $\hat\iota \circ \hat\kappa$ is uniformly continuous and is the identity on $\iota(X)$, so by uniqueness it is the identity. The same holds in the other order. $\square$

::: mathlib
`UniformSpace.Completion.extension` · `Mathlib.Topology.UniformSpace.Completion`

The map $\hat f$. `UniformSpace.Completion.extension_coe` gives $\hat f(\iota(a)) = f(a)$, `UniformSpace.Completion.uniformContinuous_extension` its uniform continuity, and `UniformSpace.Completion.extension_unique` the uniqueness. The functor on maps is `UniformSpace.Completion.map`.

<?decl UniformSpace.Completion.extension?>
:::

**Theorem (Construction).** Each uniform space has a completion.

*Proof sketch.* Let $C$ be the set of minimal Cauchy filters on $X$. Each Cauchy filter $F$ contains a unique minimal one: the filter generated by the sets $V[A] = \{y : \exists a \in A, (a, y) \in V\}$ with $A \in F$ and $V$ an entourage. For an entourage $V$ let $\hat V = \{(F, G) : \exists A \in F \cap G, A \times A \subseteq V\}$. These sets generate a uniform structure on $C$. The map $x \mapsto \mathcal{N}(x)$ is uniformly inducing with dense range. The space $C$ is complete: a Cauchy filter $\Phi$ on $C$ gives the Cauchy filter on $X$ generated by the sets $\bigcup_{F \in S} A_F$, and $\Phi$ converges to its minimal part. Finally, the quotient of $C$ by the relation "inseparable" is Hausdorff and keeps the other properties. $\square$

Mathlib carries out this construction in `Mathlib.Topology.UniformSpace.Completion`. Afterwards, the universal property is the only interface that later files use. A reader does not need the minimal Cauchy filters to work with the completion: each statement about $\hat X$ follows from density, completeness and the extension theorem.

### Examples

**Example (The real numbers).** The inclusion $\mathbb{Q} \to \mathbb{R}$ is a uniform embedding with dense range, and $\mathbb{R}$ is complete and Hausdorff. So $\mathbb{R}$ is a completion of $\mathbb{Q}$, unique up to unique isomorphism. Mathlib defines $\mathbb{R}$ with Cauchy sequences of rationals in a separate construction, and the corollary shows that the result agrees with `UniformSpace.Completion ℚ`.

**Example ($p$-adic numbers).** For a prime $p$, let $|x|_p = p^{-k}$ when $x = p^k a/b$ with $p$ dividing neither $a$ nor $b$, and $|0|_p = 0$. Then $d(x, y) = |x - y|_p$ is a metric on $\mathbb{Q}$, with a uniform structure different from the usual one: $p^n \to 0$. Its completion is the field $\mathbb{Q}_p$ of $p$-adic numbers.

**Counterexample (Continuity is not enough).** The map $f : \mathbb{Q} \to \mathbb{R}$ with $f(q) = 0$ for $q^2 < 2$ and $f(q) = 1$ for $q^2 > 2$ is continuous on $\mathbb{Q}$, since $\sqrt{2}$ is not rational. It does not extend continuously to $\mathbb{R}$: at $\sqrt{2}$ both values $0$ and $1$ are limits. The map is not uniformly continuous, so the theorem does not apply.

### The library around it

The construction and the universal property are in `Mathlib.Topology.UniformSpace.Completion`. The general extension theorem for a uniformly inducing map with dense range is in `Mathlib.Topology.UniformSpace.UniformEmbedding`. Metric completions are in `Mathlib.Topology.MetricSpace.Completion`, and the volumes on topological algebra extend the group and ring operations to the completion with the same universal property.

The module `Mathlib.Topology.UniformSpace.AbstractCompletion` states the universal property without a fixed construction. A term of `AbstractCompletion α` is a package: a complete $T_0$ space `AbstractCompletion.space` with a uniformly inducing map `AbstractCompletion.coe` of dense range. The fields are `AbstractCompletion.complete`, `AbstractCompletion.separation`, `AbstractCompletion.isUniformInducing` and `AbstractCompletion.dense`. Each package has the extension `AbstractCompletion.extend`, with `AbstractCompletion.extend_coe` and `AbstractCompletion.uniformContinuous_extend`, the functorial map `AbstractCompletion.map`, and the two-variable forms `AbstractCompletion.extend₂` and `AbstractCompletion.map₂`. Two packages of the same space are uniformly equivalent, by `AbstractCompletion.compareEquiv`. The proof is the usual one: the maps `AbstractCompletion.compare` in the two directions extend the identity of $\alpha$, so their composites are the identity on a dense set, and so everywhere. A complete $T_0$ space is its own completion, `AbstractCompletion.ofComplete`, and `AbstractCompletion.prod` gives the completion of a product.

The module `Mathlib.Topology.UniformSpace.CompareReals` uses this to compare two constructions of the real numbers. The type `CompareReals.Bourbakiℝ` is the completion of the rationals as a uniform space, through the package `CompareReals.bourbakiPkg`. The package `rationalCauSeqPkg` presents $\mathbb{R}$, built from Cauchy sequences, as a completion of $\mathbb{Q}$. The uniform equivalence `CompareReals.compareEquiv` then identifies the two.

The module `Mathlib.Topology.UniformSpace.CompleteSeparated` holds three facts that need the $T_0$ axiom. A complete subset of a $T_0$ space is closed, `IsComplete.isClosed`. A uniform embedding of a complete space into a $T_0$ space is a closed embedding, `IsUniformEmbedding.isClosedEmbedding`. The lemma `IsDenseInducing.continuous_extend_of_cauchy` extends a map along a dense inducing map when the images of the Cauchy filters converge.

The reference table at the end of the section lists the declarations of the modules.

### Exercises

1. (A) Show that the completion of a complete Hausdorff space $X$ is $X$ itself, with $\iota$ the identity.
2. (A) Show that the completion of $(0, 1)$ with the usual metric is $[0, 1]$.
3. (A) Show that $\mathbb{N}$ with the discrete uniformity is its own completion.
4. (B) Show that if $X$ is totally bounded, then $\hat X$ is compact.
5. (B) Show that the completion of a metric space is a metric space, with the extension of the distance.
6. (B) Show that a uniformly continuous map $f : X \to Y$ induces a uniformly continuous map $\hat X \to \hat Y$, and that this is compatible with composition.
7. (C) Show that $\mathbb{Z}$ with the $p$-adic metric has the compact completion $\mathbb{Z}_p$.

### Notes and history

Méray (1869) and Cantor (1872) built $\mathbb{R}$ from Cauchy sequences of rationals. Hausdorff completed general metric spaces in 1914. Weil (1937) completed uniform spaces, and Bourbaki used minimal Cauchy filters in the form that Mathlib follows. Hensel introduced the $p$-adic numbers in 1897.

### Reference

<?reference?>
