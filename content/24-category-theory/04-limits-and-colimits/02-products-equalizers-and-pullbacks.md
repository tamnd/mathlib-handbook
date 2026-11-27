---
title: Products, equalizers and pullbacks
kind: theory
modules:
  - Mathlib.CategoryTheory.Limits.Shapes.Products
  - Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
  - Mathlib.CategoryTheory.Limits.Shapes.Equalizers
  - Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
  - Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
  - Mathlib.CategoryTheory.Limits.Types.Limits
  - Mathlib.CategoryTheory.Limits.Types.Pullbacks
  - Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
explains:
  E3: [CategoryTheory.Limits.piObj, CategoryTheory.Limits.prod, CategoryTheory.Limits.equalizer, CategoryTheory.Limits.pullback, CategoryTheory.Limits.has_limits_of_hasEqualizers_and_products]
  E2: [CategoryTheory.Limits.Fan, CategoryTheory.Limits.Pi.lift, CategoryTheory.Limits.HasProducts, CategoryTheory.Limits.prod.fst, CategoryTheory.Limits.prod.lift, CategoryTheory.Limits.BinaryFan, CategoryTheory.Limits.Fork, CategoryTheory.Limits.parallelPair, CategoryTheory.Limits.equalizer.ι, CategoryTheory.Limits.equalizer.lift, CategoryTheory.Limits.HasEqualizers, CategoryTheory.Limits.mono_of_isLimit_fork, CategoryTheory.Limits.cospan, CategoryTheory.Limits.PullbackCone, CategoryTheory.Limits.pullback.fst, CategoryTheory.Limits.pullback.lift, CategoryTheory.Limits.HasPullbacks, CategoryTheory.Limits.PullbackCone.mono_fst_of_is_pullback_of_mono, CategoryTheory.Limits.pullback.fst_of_mono, CategoryTheory.Limits.Types.pullbackIsoPullback, CategoryTheory.Limits.Types.limitCone, CategoryTheory.Limits.Types.limitEquivSections, CategoryTheory.Limits.limitConeOfEqualizerAndProduct, CategoryTheory.Limits.hasFiniteLimits_of_hasTerminal_and_pullbacks]
  E1: auto
families: []
requires: [V24.C01, V24.C02, V24.C03, V05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Products, equalizers and pullbacks

### Overview

Three shapes carry most of the theory of limits. A product is a limit of a family with no maps. An equalizer is a limit of two parallel maps. A pullback is a limit of two maps with a common target. This section computes them in sets and groups. It proves the two theorems that make these shapes the building blocks: a category with all products and all equalizers has all limits, and a category with a terminal object and all pullbacks has all finite limits.

### Definitions

**Definition (Product).** A limit of a family $(X_i)_{i \in I}$ of objects of $C$ is a *product* $\prod_i X_i$ with *projections* $p_i : \prod_i X_i \to X_i$. For each family $f_i : W \to X_i$ there is exactly one $\langle f_i \rangle : W \to \prod_i X_i$ with $p_i \circ \langle f_i \rangle = f_i$. For $I = \{1, 2\}$ one writes $X_1 \times X_2$ and $\langle f_1, f_2 \rangle$.

**Definition (Equalizer).** Let $f, g : X \to Y$. An *equalizer* of $f$ and $g$ is a morphism $e : E \to X$ with $f \circ e = g \circ e$ such that each $h : W \to X$ with $f \circ h = g \circ h$ factors as $h = e \circ \bar h$ for exactly one $\bar h : W \to E$.

A cone over $f, g : X \rightrightarrows Y$, a *fork*, has components $\pi_X$ and $\pi_Y = f \circ \pi_X = g \circ \pi_X$. So an equalizer is a limit of this diagram.

**Definition (Pullback).** Let $f : X \to Z$ and $g : Y \to Z$. A *pullback* of $f$ and $g$ is an object $P$ with $p_1 : P \to X$ and $p_2 : P \to Y$ such that $f \circ p_1 = g \circ p_2$, and such that for each pair $a : W \to X$, $b : W \to Y$ with $f \circ a = g \circ b$ there is exactly one $u : W \to P$ with $p_1 \circ u = a$ and $p_2 \circ u = b$. It is a limit of the *cospan* $X \to Z \leftarrow Y$.

**Definition (Finite limits).** A category is *finite* if it has finitely many objects and morphisms. $C$ *has finite limits* if every diagram of a finite shape has a limit.

::: mathlib
`CategoryTheory.Limits.piObj` · `Mathlib.CategoryTheory.Limits.Shapes.Products`

For `f : β → C`, a cone over `Discrete.functor f` is a `Fan f`, and `piObj f` is the chosen product under `HasProduct f`. The projections are `Pi.π f b` and the map into the product is `Pi.lift p`. Binary products have their own API: `prod X Y`, `prod.fst`, `prod.snd` and `prod.lift f g`, with the cone `BinaryFan X Y` over `pair X Y`.

<?decl CategoryTheory.Limits.piObj?>
<?decl CategoryTheory.Limits.prod?>
:::

::: mathlib
`CategoryTheory.Limits.equalizer` · `Mathlib.CategoryTheory.Limits.Shapes.Equalizers`

The diagram is `parallelPair f g`, a cone over it is a `Fork f g`, and `Fork.ofι ι w` builds a fork from `ι : P ⟶ X` and `w : ι ≫ f = ι ≫ g`. The chosen equalizer is `equalizer f g` with `equalizer.ι f g`, the equation `equalizer.condition f g`, and `equalizer.lift h w` for the factorization.

<?decl CategoryTheory.Limits.equalizer?>
:::

::: mathlib
`CategoryTheory.Limits.pullback` · `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`

The diagram is `cospan f g` and a cone over it is a `PullbackCone f g`. The chosen pullback is `pullback f g`, with `pullback.fst f g` and `pullback.snd f g`. The lemma `pullback.condition` reads `pullback.fst f g ≫ f = pullback.snd f g ≫ g`, and `pullback.lift h k w` is the map from a commuting square.

<?decl CategoryTheory.Limits.pullback?>
:::

### Theorems and proofs

**Theorem (Limits in sets).** Let $F : J \to \mathbf{Set}$ with $J$ small. Put
$$L = \Big\{ (x_j) \in \prod_{j} F(j) \;:\; F(u)(x_j) = x_k \text{ for all } u : j \to k \Big\},$$
the set of *compatible families*, and let $\pi_j : L \to F(j)$ be the coordinate maps. Then $(L, \pi)$ is a limit cone over $F$.

*Proof.* By the definition of $L$, $\pi$ is a cone. Let $(W, \sigma)$ be a cone. For $w \in W$, the family $(\sigma_j(w))_j$ is compatible, since $F(u)(\sigma_j(w)) = \sigma_k(w)$ by the cone condition. So $\bar\sigma(w) = (\sigma_j(w))_j$ defines $\bar\sigma : W \to L$ with $\pi_j \circ \bar\sigma = \sigma_j$. Any $h$ with $\pi_j \circ h = \sigma_j$ has the same coordinates as $\bar\sigma$, so $h = \bar\sigma$. $\square$

So the product is the cartesian product. The equalizer of $f, g : X \to Y$ is the subset $\{x \in X : f(x) = g(x)\}$. The pullback of $f : X \to Z$ and $g : Y \to Z$ is the fibre product $X \times_Z Y = \{(x, y) : f(x) = g(y)\}$.

**Proposition (Equalizers are monic).** An equalizer $e : E \to X$ of $f$ and $g$ is a monomorphism.

*Proof.* Let $a, b : W \to E$ with $e \circ a = e \circ b$. Put $h = e \circ a$. Then $f \circ h = g \circ h$, and both $a$ and $b$ are factorizations of $h$ through $e$. By uniqueness, $a = b$. $\square$

**Proposition (Pullbacks preserve monos).** Let $P$, with $p_1, p_2$, be a pullback of $f : X \to Z$ and $m : Y \to Z$. If $m$ is a monomorphism, then $p_1$ is a monomorphism.

*Proof.* Let $a, b : W \to P$ with $p_1 \circ a = p_1 \circ b$. Then $m \circ p_2 \circ a = f \circ p_1 \circ a = f \circ p_1 \circ b = m \circ p_2 \circ b$. Since $m$ is monic, $p_2 \circ a = p_2 \circ b$. So $a$ and $b$ have the same components, and by the proposition on maps into a limit in Section 1, $a = b$. $\square$

**Theorem (Limits from products and equalizers).** Suppose $C$ has all products indexed by sets and all equalizers. Then $C$ is complete. If $C$ has finite products and equalizers, it has finite limits.

*Proof.* Let $F : J \to C$ with $J$ small. Let $M$ be the set of all morphisms $u : j \to k$ of $J$, and write $s(u) = j$, $t(u) = k$. Form the products
$$P = \prod_{j \in \mathrm{Ob}\, J} F(j), \qquad Q = \prod_{u \in M} F(t(u)),$$
with projections $p_j$ and $q_u$. Define $s, t : P \to Q$ by
$$q_u \circ s = p_{t(u)}, \qquad q_u \circ t = F(u) \circ p_{s(u)}.$$
Let $e : L \to P$ be an equalizer of $s$ and $t$, and put $\pi_j = p_j \circ e$.

*It is a cone.* For $u : j \to k$, $F(u) \circ \pi_j = F(u) \circ p_j \circ e = q_u \circ t \circ e = q_u \circ s \circ e = p_k \circ e = \pi_k$.

*It is universal.* Let $(W, \sigma)$ be a cone. Let $\bar\sigma = \langle \sigma_j \rangle : W \to P$. For each $u : j \to k$, $q_u \circ s \circ \bar\sigma = p_k \circ \bar\sigma = \sigma_k$ and $q_u \circ t \circ \bar\sigma = F(u) \circ \sigma_j = \sigma_k$. Maps into $Q$ with the same components are equal, so $s \circ \bar\sigma = t \circ \bar\sigma$. Hence $\bar\sigma = e \circ v$ for a unique $v : W \to L$, and $\pi_j \circ v = p_j \circ \bar\sigma = \sigma_j$. If also $\pi_j \circ v' = \sigma_j$ for all $j$, then $p_j \circ e \circ v' = \sigma_j$, so $e \circ v' = \bar\sigma = e \circ v$. Since $e$ is monic, $v' = v$.

If $J$ is finite, then $P$ and $Q$ are finite products, so the same construction gives finite limits. $\square$

**Theorem (Finite limits from pullbacks).** If $C$ has a terminal object $1$ and all pullbacks, then $C$ has finite limits.

*Proof.* By the previous theorem, it suffices to build finite products and equalizers.

*Binary products.* Let $X \times Y$ be the pullback of $X \to 1 \leftarrow Y$. Any two maps $a : W \to X$, $b : W \to Y$ satisfy the condition of the square, since there is only one map $W \to 1$. So pairs $(a, b)$ factor uniquely, which is the definition of a product.

*Finite products.* The terminal object is the empty product, and $(\prod_{i < n} X_i) \times X_n$ is a product of $X_0, \dots, X_n$ by the two universal properties in turn.

*Equalizers.* Let $f, g : X \to Y$. Let $P$, with $a, b : P \to X$, be a pullback of $\langle 1_X, f \rangle$ and $\langle 1_X, g \rangle : X \to X \times Y$. The square gives $\langle a, f \circ a \rangle = \langle b, g \circ b \rangle$, so $a = b$ and $f \circ a = g \circ a$. Let $h : W \to X$ with $f \circ h = g \circ h$. Then $\langle 1_X, f \rangle \circ h = \langle 1_X, g \rangle \circ h$, so $(h, h)$ factors through $P$ by a unique $u$. A map $u'$ with $a \circ u' = h$ also has $b \circ u' = a \circ u' = h$, so $u' = u$. Hence $a$ is an equalizer of $f$ and $g$. $\square$

### Examples

**Example (A pullback of finite sets).** Let $X = \{1, 2, 3, 4\}$, $Y = \{a, b\}$ and $Z = \{0, 1\}$. Let $f : X \to Z$ send $n$ to its parity, so $f(1) = f(3) = 1$ and $f(2) = f(4) = 0$, and let $g(a) = 0$, $g(b) = 1$. The pullback is
$$X \times_Z Y = \{(2, a), (4, a), (1, b), (3, b)\},$$
a set with 4 of the 8 pairs. For $Y = \{*\}$ and $g(*) = z$, the pullback is the fibre $f^{-1}(z)$.

**Example (Groups).** In groups (Volume 5, Chapter 2), the product of $(G_i)$ is the direct product with the pointwise operation. The equalizer of $f, g : G \to H$ is the subgroup $\{x : f(x) = g(x)\}$; with $g$ trivial it is the kernel of $f$. The underlying set is the limit in sets; Section 4 explains why.

**Counterexample (Fields have no product of $\mathbb{Q}$ and $\mathbb{F}_2$).** A product $P$ of $\mathbb{Q}$ and $\mathbb{F}_2$ in fields has homomorphisms $P \to \mathbb{Q}$ and $P \to \mathbb{F}_2$. A homomorphism of fields preserves the characteristic, so $\operatorname{char} P$ is both $0$ and $2$. So the product does not exist.

**Counterexample (Finite sets lack infinite products).** Let $X_n = \{0, 1\}$ for $n \in \mathbb{N}$, in the category of finite sets. Suppose $P$, with $p_n$, is a product. Maps $\{*\} \to P$ correspond to cones with apex $\{*\}$, which are all the sequences in $\{0, 1\}^{\mathbb{N}}$. So $P$ has uncountably many points, which is impossible.

::: mathlib
`CategoryTheory.Limits.Types.limitEquivSections` · `Mathlib.CategoryTheory.Limits.Types.Limits`

The theorem on limits in sets is `Types.limitCone`, whose apex is the type `F.sections` of compatible families (made small when needed), with `Types.limitConeIsLimit`. The equivalence `Types.limitEquivSections : limit F ≃ F.sections` compares it with the chosen limit. For pullbacks, `Types.PullbackObj f g` is the subtype `{p : X × Y // f p.1 = g p.2}`, and `Types.pullbackIsoPullback f g` is the isomorphism with `pullback f g`. `GrpCat.binaryProductLimitCone` is the direct product of groups, and `TopCat.prod_topology` gives the product topology of spaces (Volume 13, Chapter 1) as an infimum of induced topologies.

<?decl CategoryTheory.Limits.Types.limitEquivSections?>
<?decl GrpCat.binaryProductLimitCone?>
<?decl TopCat.prod_topology?>
:::

### The library around it

The two theorems of this section are in `Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers`. `has_limits_of_hasEqualizers_and_products` gives `HasLimitsOfSize.{w, w} C` from `HasProducts.{w} C` and `HasEqualizers C`, with the cone `limitConeOfEqualizerAndProduct`. `hasFiniteLimits_of_hasTerminal_and_pullbacks` gives `HasFiniteLimits C`. The two results on monos are `mono_of_isLimit_fork` and `PullbackCone.mono_fst_of_is_pullback_of_mono`, with the instance `pullback.fst_of_mono`.

Common errors of a learner:

- The order of the arguments of `pullback.fst f g`: it is the projection to the source of `f`, the first map of the cospan.
- In `Types`, `limit F` is not by definition the set of compatible families. Use `Types.limitEquivSections`.

### Exercises

1. (A) Show that in a poset the product is the infimum, the equalizer of $x \le y$ with itself is $x$, and the pullback of $x \le z \ge y$ is $x \wedge y$.
2. (A) Compute the equalizer of $f, g : \mathbb{Z} \to \mathbb{Z}/6$ in abelian groups, with $f(n) = 2n$ and $g(n) = 5n$.
3. (B) (Pasting lemma.) In a commutative diagram of two squares side by side, suppose the right square is a pullback. Show that the left square is a pullback if and only if the outer rectangle is one.
4. (B) Show that $m : X \to Y$ is monic if and only if the square with $1_X, 1_X, m, m$ is a pullback.
5. (C) Let $C$ have binary products and pullbacks. Show that the equalizer of $f, g : X \to Y$ is the pullback of the diagonal $\langle 1_Y, 1_Y \rangle : Y \to Y \times Y$ along $\langle f, g \rangle : X \to Y \times Y$. Then give a category with pullbacks and equalizers but no terminal object.

### Notes and history

Products, kernels and fibre products were known in each field long before Eilenberg and Mac Lane (1945) gave the language that makes them one notion. The construction of all limits from products and equalizers is in Mac Lane's *Categories for the Working Mathematician* (1971).

### Reference

<?reference?>
