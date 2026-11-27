---
title: Quotient modules and the isomorphism theorems
kind: theory
modules:
  - Mathlib.LinearAlgebra.Quotient.Defs
  - Mathlib.LinearAlgebra.Quotient.Basic
  - Mathlib.LinearAlgebra.Isomorphisms
explains:
  E3: [LinearMap.quotKerEquivRange]
  E2: [Submodule.mkQ, Submodule.Quotient.eq, Submodule.liftQ, LinearMap.quotKerEquivOfSurjective, LinearMap.quotientInfEquivSupQuotient, Submodule.quotientQuotientEquivQuotient, Submodule.Quotient.module]
  E1: auto
families: []
requires: [V05, V04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Quotient modules and the isomorphism theorems

### Overview

A submodule $N$ of $M$ is a normal subgroup of the abelian group $M$, since each subgroup of an abelian group is normal. So the quotient group $M / N$ exists, as in Volume 5. The scalar action passes to the cosets, and $M / N$ is a module. The quotient forgets the directions in $N$: two vectors become equal when they differ by an element of $N$. Geometrically, the quotient of $\mathbb{R}^3$ by a line is the set of the lines parallel to it, and this set is a plane.

This section builds the quotient, proves its universal property, and proves the three isomorphism theorems. The first one, $M / \ker f \cong \operatorname{im} f$, is the source of the rank-nullity theorem of Chapter 2. The quotient also gives the right language for the structure theorem of Chapter 7, where a finitely generated abelian group is the quotient of $\mathbb{Z}^n$ by the relations between its generators.

### Definitions

**Definition (Quotient module).** Let $N$ be a submodule of an $R$-module $M$. For $x \in M$, the coset of $x$ is $\bar{x} = x + N = \{x + y : y \in N\}$. The quotient $M / N$ is the set of the cosets, with the operations
$$\bar{x} + \bar{y} = \overline{x + y}, \qquad r \cdot \bar{x} = \overline{r x}.$$
The quotient map is $\pi : M \to M / N$, $\pi(x) = \bar{x}$.

The operations are well defined. Let $\bar{x} = \bar{x}'$ and $\bar{y} = \bar{y}'$, so $x - x' \in N$ and $y - y' \in N$. Then $(x + y) - (x' + y') = (x - x') + (y - y') \in N$, and $r x - r x' = r (x - x') \in N$. So the classes of $x + y$ and of $r x$ do not depend on the choice of the representatives. The axioms of a module hold in $M / N$ because they hold in $M$ for the representatives.

::: mathlib
`Submodule.Quotient.module` · `Mathlib.LinearAlgebra.Quotient.Defs`

The instance `Module R (M ⧸ N)`. The type `M ⧸ N` (the symbol is `\quot`) is the quotient of `M` by the setoid of `N.quotientRel`, the relation `x - y ∈ N`. The coset of `x` is `Submodule.Quotient.mk x`, or the value `N.mkQ x` of the quotient map.

<?decl Submodule.Quotient.module?>
:::

::: mathlib
`Submodule.mkQ` · `Mathlib.LinearAlgebra.Quotient.Defs`

The quotient map `N.mkQ : M →ₗ[R] M ⧸ N` as a bundled linear map. The lemma `Submodule.mkQ_apply` says `N.mkQ x = Submodule.Quotient.mk x`, and `Submodule.range_mkQ` says that the map is surjective.

<?decl Submodule.mkQ?>
:::

### Theorems and proofs

**Theorem (Equality in the quotient).** For $x, y \in M$, $\bar{x} = \bar{y}$ in $M / N$ if and only if $x - y \in N$. In particular $\bar{x} = 0$ if and only if $x \in N$, and $\ker \pi = N$.

*Proof.* The first statement is the definition of the cosets of the subgroup $N$: $x + N = y + N$ if and only if $x - y \in N$. The second is the case $y = 0$. The third rewrites the second: $\pi(x) = 0$ if and only if $x \in N$. $\square$

::: mathlib
`Submodule.Quotient.eq` · `Mathlib.LinearAlgebra.Quotient.Defs`

The statement `Quotient.mk x = Quotient.mk y ↔ x - y ∈ p`. Rewrite with it to turn an equation in the quotient into a membership in `p`.

<?decl Submodule.Quotient.eq?>
:::

**Theorem (Universal property of the quotient).** Let $f : M \to P$ be a linear map with $N \subseteq \ker f$. Then there is exactly one linear map $\bar{f} : M / N \to P$ with $\bar{f} \circ \pi = f$, that is, $\bar{f}(\bar{x}) = f(x)$. The kernel of $\bar{f}$ is $(\ker f) / N$, the image of $\ker f$ in $M / N$.

*Proof.* Uniqueness: $\pi$ is surjective, so $\bar{f}$ is fixed by its values $\bar{f}(\bar{x}) = f(x)$. Existence: define $\bar{f}(\bar{x}) = f(x)$. This is well defined: if $\bar{x} = \bar{x}'$, then $x - x' \in N \subseteq \ker f$, so $f(x) - f(x') = f(x - x') = 0$. The map is linear: $\bar{f}(\bar{x} + \bar{y}) = \bar{f}(\overline{x + y}) = f(x + y) = f(x) + f(y)$, and the scalar law is the same. Last, $\bar{f}(\bar{x}) = 0$ if and only if $f(x) = 0$, so $\ker \bar{f} = \pi(\ker f)$. $\square$

::: mathlib
`Submodule.liftQ` · `Mathlib.LinearAlgebra.Quotient.Basic`

The induced map `p.liftQ f h : M ⧸ p →ₗ[R] P` from a proof `h : p ≤ ker f`. The equation `p.liftQ f h ∘ₗ p.mkQ = f` is `Submodule.liftQ_mkQ`, and the value on a coset is `Submodule.liftQ_apply`. To define a map out of a quotient in Mathlib, use `liftQ`, or use `Quotient.liftOn` on the underlying type.

<?decl Submodule.liftQ?>
:::

**Theorem (First isomorphism theorem).** Let $f : M \to P$ be linear. Then the map $\bar{f} : M / \ker f \to \operatorname{im} f$, $\bar{x} \mapsto f(x)$, is a linear equivalence. In particular, if $f$ is surjective, then $M / \ker f \cong P$.

*Proof.* Apply the universal property with $N = \ker f$ and the map $f$, seen as a map into $\operatorname{im} f$. This gives a linear map $\bar{f}$ with $\bar{f}(\bar{x}) = f(x)$. Its kernel is $\pi(\ker f) = 0$, so $\bar{f}$ is injective. It is surjective onto $\operatorname{im} f$: each element of the range is $f(x) = \bar{f}(\bar{x})$. A bijective linear map is a linear equivalence by Section 2. $\square$

::: mathlib
`LinearMap.quotKerEquivRange` · `Mathlib.LinearAlgebra.Isomorphisms`

The equivalence `(M ⧸ ker f) ≃ₗ[R] range f`. The target is the subtype `↥(range f)`, so a value is a pair of a vector of `P` and a proof that it lies in the range. The lemma `LinearMap.quotKerEquivRange_apply_mk` computes it on a coset. This is the main tool to compute a quotient: find a surjective map with the right kernel.

<?decl LinearMap.quotKerEquivRange?>
:::

::: mathlib
`LinearMap.quotKerEquivOfSurjective` · `Mathlib.LinearAlgebra.Isomorphisms`

The equivalence `(M ⧸ ker f) ≃ₗ[R] P` for a surjective `f`. It avoids the subtype of the range.

<?decl LinearMap.quotKerEquivOfSurjective?>
:::

**Theorem (Second isomorphism theorem).** Let $A$ and $B$ be submodules of $M$. Then $A / (A \cap B) \cong (A + B) / B$, by $a + (A \cap B) \mapsto a + B$.

*Proof.* Let $g : A \to (A + B) / B$ be the map $g(a) = a + B$. It is the restriction of the quotient map, so it is linear. It is surjective: an element of $(A + B)/B$ is the coset of $a + b$ with $a \in A$ and $b \in B$, and this coset equals $a + B = g(a)$, since $(a + b) - a = b \in B$. Its kernel is $\{a \in A : a \in B\} = A \cap B$. The first isomorphism theorem gives the claim. $\square$

::: mathlib
`LinearMap.quotientInfEquivSupQuotient` · `Mathlib.LinearAlgebra.Isomorphisms`

The second isomorphism theorem for submodules `p p'` of `M`. Both sides are quotients of submodules, so the statement uses `comap p.subtype` to see `p ⊓ p'` as a submodule of `↥p`, and the same for `(p ⊔ p')`. The type looks heavy, but the map is `a ↦ a + p'`.

<?decl LinearMap.quotientInfEquivSupQuotient?>
:::

**Theorem (Third isomorphism theorem).** Let $N \subseteq L$ be submodules of $M$. Then $L / N$ is a submodule of $M / N$, and $(M / N) / (L / N) \cong M / L$.

*Proof.* The image of $L$ under $\pi : M \to M/N$ is $L / N$, a submodule by Section 2. The quotient map $\pi_L : M \to M / L$ has kernel $L \supseteq N$. The universal property gives a map $h : M / N \to M / L$ with $h(x + N) = x + L$. It is surjective, because $\pi_L$ is. Its kernel is $\pi(\ker \pi_L) = \pi(L) = L / N$. The first isomorphism theorem applied to $h$ gives the claim. $\square$

::: mathlib
`Submodule.quotientQuotientEquivQuotient` · `Mathlib.LinearAlgebra.Isomorphisms`

The equivalence `((M ⧸ S) ⧸ map S.mkQ T) ≃ₗ[R] M ⧸ T` for `S ≤ T`. The submodule `T / S` of `M ⧸ S` is written `map S.mkQ T`, the image of `T`.

<?decl Submodule.quotientQuotientEquivQuotient?>
:::

**Theorem (Correspondence theorem).** The map $L \mapsto L / N$ is an order isomorphism from the submodules of $M$ that contain $N$ to the submodules of $M / N$. Its inverse sends a submodule $Q$ of $M/N$ to $\pi^{-1}(Q)$.

*Proof.* Both maps preserve inclusion. For $L \supseteq N$: $\pi^{-1}(\pi(L)) = L + N = L$, since $x \in \pi^{-1}(\pi(L))$ means $x - l \in N$ for some $l \in L$. For a submodule $Q$ of $M / N$: $\pi(\pi^{-1}(Q)) = Q$, since $\pi$ is surjective. Also $\pi^{-1}(Q) \supseteq \pi^{-1}(0) = N$. So the two maps are inverse bijections that preserve the order. $\square$

### Examples

**Example (A quotient of $\mathbb{R}^3$ by a line).** Let $L = \mathbb{R}(1, 1, 1)$ in $\mathbb{R}^3$. The map $f : \mathbb{R}^3 \to \mathbb{R}^2$, $f(x, y, z) = (x - z, y - z)$, is linear and surjective: $f(a, b, 0) = (a, b)$. Its kernel is $\{x = y = z\} = L$. The first isomorphism theorem gives $\mathbb{R}^3 / L \cong \mathbb{R}^2$. Two vectors have the same class if they differ by a multiple of $(1, 1, 1)$. For example, $(3, 5, 2)$ and $(1, 3, 0)$ have the same class, since their difference is $(2, 2, 2)$, and both go to $(1, 3)$.

**Example (A finite quotient of $\mathbb{Z}^2$).** Let $N = \{(a, b) \in \mathbb{Z}^2 : a \equiv b \pmod 3\}$. The map $f : \mathbb{Z}^2 \to \mathbb{Z}/3$, $f(a, b) = \overline{a - b}$, is $\mathbb{Z}$-linear and surjective, with kernel $N$. So $\mathbb{Z}^2 / N \cong \mathbb{Z}/3$. The submodule $N$ is spanned by $(1, 1)$ and $(3, 0)$: if $a \equiv b$, then $(a, b) = b(1, 1) + \frac{a - b}{3}(3, 0)$. This is a first case of the computation of Chapter 7, where $\mathbb{Z}^2 / \langle (1, 1), (3, 0) \rangle$ comes out as $\mathbb{Z}/1 \oplus \mathbb{Z}/3 = \mathbb{Z}/3$.

**Example (Polynomials modulo a polynomial).** Let $V = \mathbb{Q}[x]$ and $N = (x^2 + 1) \mathbb{Q}[x]$, the multiples of $x^2 + 1$. Division with remainder writes each $p$ as $p = q (x^2 + 1) + a + b x$ with unique $a, b \in \mathbb{Q}$. So the map $V \to \mathbb{Q}^2$ that sends $p$ to $(a, b)$ is linear and surjective, with kernel $N$. Thus $V / N \cong \mathbb{Q}^2$. The class of $x^3$ is the class of $-x$, since $x^3 = x (x^2 + 1) - x$. The quotient is also a ring, the field $\mathbb{Q}(i)$, but that structure is the subject of Volume 6.

**Counterexample (A quotient is not a submodule).** In $\mathbb{Z}$, the quotient $\mathbb{Z} / 2 \mathbb{Z}$ has two elements. It is not isomorphic to a submodule of $\mathbb{Z}$, since each nonzero submodule $n \mathbb{Z}$ is infinite. In a vector space, each quotient $V / W$ is isomorphic to a complement of $W$ in $V$, by Chapter 2. Over $\mathbb{Z}$ this fails, and this is one of the main differences between vector spaces and modules.

### The library around it

The quotient is in `Mathlib.LinearAlgebra.Quotient.Defs` and `Mathlib.LinearAlgebra.Quotient.Basic`. The isomorphism theorems are in `Mathlib.LinearAlgebra.Isomorphisms`. For quotients of a ring by an ideal, Mathlib uses the same symbol `R ⧸ I`, and the ring structure comes from `Ideal.Quotient` in the ring theory volumes. The two structures are compatible: the module structure of `R ⧸ I` over `R` is the one of this section.

The Mathlib form of the quotient uses `Quotient` of a `Setoid`. A coset is not a set of vectors in Mathlib. It is an element of a new type, and the map `Submodule.Quotient.mk` is the only way to make one. Lemmas on cosets are proved by `Quotient.inductionOn` or by the tactic `induction x using Submodule.Quotient.induction_on`: each element of `M ⧸ N` is `mk x` for some `x`.

### Exercises

1. (A) Show that $\mathbb{R}^3 / \{(x, y, 0)\} \cong \mathbb{R}$. Hint: use the map $(x, y, z) \mapsto z$.
2. (A) In $\mathbb{Z}^2 / \langle (2, 0), (0, 2) \rangle$, list the classes and identify the module. Hint: the map to $(\mathbb{Z}/2)^2$ that reduces each coordinate.
3. (A) Let $M = P_3$, the real polynomials of degree at most $3$, and $N = \{p : p(0) = p(1) = 0\}$. Find a linear map with kernel $N$ and show $M / N \cong \mathbb{R}^2$.
4. (B) Let $N \subseteq M$. Show that $M / N = 0$ if and only if $N = M$, and that $\pi$ is injective if and only if $N = 0$.
5. (B) Let $f : M \to P$ be surjective and $L \supseteq \ker f$ a submodule of $M$. Show that $M / L \cong P / f(L)$. Hint: compose $f$ with the quotient map of $P$.
6. (B) Prove that $\mathbb{Q}/\mathbb{Z}$ has, for each $n \ge 1$, exactly one submodule of order $n$. Hint: a submodule of order $n$ is killed by $n$, and the elements of $\mathbb{Q}/\mathbb{Z}$ killed by $n$ form a cyclic group of order $n$.
7. (C) Let $V = \mathbb{R}^{\mathbb{N}}$ be the space of the real sequences and $c_0$ the subspace of the sequences that tend to $0$. Show that the map $V \to V / c_0$ sends two sequences to the same class if and only if their difference tends to $0$, and that the limit gives a well defined linear map from (convergent sequences)$/c_0$ to $\mathbb{R}$ which is an isomorphism.

### Notes and history

The isomorphism theorems are due to Emmy Noether, in her papers of 1927 on abstract ideal theory, where she stated them for groups with operators. A module is an abelian group with operators from a ring, so her theorems contain the three theorems of this section. The language of quotient spaces in linear algebra became standard later, with the books of Bourbaki and of Halmos.

In Mathlib, the file `Mathlib.LinearAlgebra.Quotient.Basic` and the isomorphism theorems go back to Johannes Hölzl, Mario Carneiro and Kevin Buzzard, with later work by Yury Kudryashov. The choice to build `M ⧸ N` from a `Setoid` is shared with groups and rings, so the same notation and the same tactics work in all three cases.

### Reference

<?reference?>
