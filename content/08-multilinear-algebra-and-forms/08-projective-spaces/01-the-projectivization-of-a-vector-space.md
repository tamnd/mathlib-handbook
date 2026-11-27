---
title: The projectivization of a vector space
kind: theory
modules:
  - Mathlib.LinearAlgebra.Projectivization.Basic
  - Mathlib.LinearAlgebra.Projectivization.Independence
  - Mathlib.LinearAlgebra.Projectivization.Cardinality
explains:
  E3: [Projectivization, Projectivization.mk, Projectivization.card_of_finrank]
  E2: [Projectivization.rep, Projectivization.mk_rep, Projectivization.mk_eq_mk_iff, Projectivization.mk_eq_mk_iff', Projectivization.submodule, Projectivization.equivSubmodule, Projectivization.ind, Projectivization.lift, Projectivization.map, Projectivization.Independent, Projectivization.independent_iff, Projectivization.independent_pair_iff_ne, Projectivization.card, Projectivization.nonZeroEquivProjectivizationProdUnits, Projectivization.card_of_finrank_two]
  E1: auto
families: []
requires: [V07.C02, V05.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The projectivization of a vector space

### Overview

Projective geometry adds points at infinity to an affine space, so that two distinct lines in a plane always meet. Algebraically, a point of $\mathbb{P}(V)$ is a line through the origin of $V$, and $\mathbb{P}^n(K) = \mathbb{P}(K^{n+1})$ has homogeneous coordinates $[x_0 : \dots : x_n]$.

This section defines $\mathbb{P}(V)$ as a quotient, describes its points by representatives and by one-dimensional subspaces, and shows how injective linear maps act on it. It defines independent families of points. Then it counts the points over a finite field: $\mathbb{P}^n(\mathbb{F}_q)$ has
$$\frac{q^{n+1} - 1}{q - 1} = 1 + q + q^2 + \dots + q^n$$
points. The bases and dimensions of Volume 7, Chapter 2 and the orbits of a group action of Volume 5, Chapter 6 are used without comment.

### Definitions

Let $K$ be a division ring and $V$ a $K$-vector space. All results also hold for fields, which are the main case.

**Definition (Projectivization).** The projectivization $\mathbb{P}(V)$ is the set of orbits of the group $K^{\times}$ acting by scalar multiplication on $V \setminus \{0\}$. The orbit of $v \neq 0$ is written $[v]$. So $[v] = [w]$ if and only if $v = a w$ for some $a \in K^{\times}$. The projective space of dimension $n$ is $\mathbb{P}^n(K) = \mathbb{P}(K^{n+1})$, and its points are written $[x_0 : \dots : x_n]$.

For $v \neq 0$ and $a \neq 0$, $a v \neq 0$, so the action is well defined. The dimension of $\mathbb{P}(V)$ is $\dim V - 1$: a projective line comes from a plane, a projective plane from a space of dimension 3.

::: mathlib
`Projectivization` · `Mathlib.LinearAlgebra.Projectivization.Basic`

`Projectivization K V`, written `ℙ K V` in the scope `LinearAlgebra.Projectivization`, is the quotient of `{v : V // v ≠ 0}` by the orbit relation of `Kˣ`.

<?decl Projectivization?>
:::

::: mathlib
`Projectivization.mk` · `Mathlib.LinearAlgebra.Projectivization.Basic`

`mk K v hv` is $[v]$, with `hv : v ≠ 0`. By `mk_eq_mk_iff`, two points are equal if and only if `a • w = v` for a unit `a`; `mk_eq_mk_iff'` takes `a : K` instead.

<?decl Projectivization.mk?>
:::

<?decl Projectivization.mk_eq_mk_iff?>

<?decl Projectivization.mk_eq_mk_iff'?>

**Definition (Representative).** A representative of a point $P$ is a vector $v \neq 0$ with $[v] = P$. The one-dimensional subspace of $P = [v]$ is the line $K v$; it does not depend on the representative.

Each point has representatives, and any two differ by a unit. Choosing one representative for each point gives a map $\mathbb{P}(V) \to V \setminus \{0\}$, which depends on the choice.

::: mathlib
`Projectivization.rep` · `Mathlib.LinearAlgebra.Projectivization.Basic`

`P.rep` is chosen by the axiom of choice and is used only through `mk_rep : mk K P.rep _ = P`. `P.submodule` is the line $K v$.

<?decl Projectivization.rep?>
:::

<?decl Projectivization.mk_rep?>

<?decl Projectivization.submodule?>

**Definition (Induced map).** Let $f : V \to W$ be an injective linear map. The induced map $\mathbb{P}(f) : \mathbb{P}(V) \to \mathbb{P}(W)$ sends $[v]$ to $[f(v)]$.

The definition is sound. Since $f$ is injective, $v \neq 0$ gives $f(v) \neq 0$. If $[v] = [w]$, then $v = a w$, and $f(v) = a f(w)$, so $[f(v)] = [f(w)]$.

::: mathlib
`Projectivization.map` · `Mathlib.LinearAlgebra.Projectivization.Basic`

`map f hf` takes an injective semilinear map `f : V →ₛₗ[σ] W`, so field automorphisms also act; `map_mk` and `map_comp` give functoriality.

<?decl Projectivization.map?>
:::

**Definition (Independent points).** A family $(P_i)_{i \in I}$ of points of $\mathbb{P}(V)$ is independent if a family of representatives $(v_i)$ is linearly independent in $V$. Otherwise it is dependent.

The condition does not depend on the representatives, because multiplying each $v_i$ by a unit does not change linear independence. Three points of a projective plane are dependent exactly when they lie on one projective line.

::: mathlib
`Projectivization.Independent` · `Mathlib.LinearAlgebra.Projectivization.Independence`

An inductive predicate on families `f : ι → ℙ K V`; `independent_iff` translates it into `LinearIndependent K (rep ∘ f)`. The predicate `Projectivization.Dependent` is its negation, by `dependent_iff_not_independent`.

<?decl Projectivization.Independent?>
:::

<?decl Projectivization.independent_iff?>

### Theorems and proofs

**Proposition (Points and lines).** The map $[v] \mapsto K v$ is a bijection from $\mathbb{P}(V)$ to the set of one-dimensional subspaces of $V$.

*Proof.* The map is well defined: $K (a v) = K v$ for $a \in K^{\times}$. It is surjective, since each one-dimensional subspace is $K v$ for any nonzero $v$ in it. It is injective: if $K v = K w$, then $v \in K w$, so $v = a w$ with $a \neq 0$ because $v \neq 0$, and $[v] = [w]$. $\square$

<?decl Projectivization.equivSubmodule?>

**Proposition (Universal property).** Let $g$ be a function from $V \setminus \{0\}$ to a set $X$ with $g(a v) = g(v)$ for all $a \in K^{\times}$. Then there is a unique function $\bar g : \mathbb{P}(V) \to X$ with $\bar g([v]) = g(v)$. To prove a property of all points, it suffices to prove it for all points $[v]$ with $v \neq 0$.

*Proof.* This is the universal property of the quotient by an equivalence relation: $g$ is constant on the classes, so $\bar g$ is well defined, and it is unique because every point has the form $[v]$. The second claim holds because $[\,\cdot\,]$ is surjective. $\square$

<?decl Projectivization.lift?>

<?decl Projectivization.ind?>

**Proposition (Pairs of points).** Two points $P, Q$ of $\mathbb{P}(V)$ are independent if and only if $P \neq Q$.

*Proof.* Let $P = [v]$ and $Q = [w]$. If $P = Q$, then $v = a w$ and $v - a w = 0$ is a nontrivial relation. Conversely, suppose that $s v + t w = 0$ with $(s, t) \neq (0, 0)$. If $s = 0$, then $t w = 0$ with $t \neq 0$, so $w = 0$, which is impossible. So $s \neq 0$ and $v = -s^{-1} t w$; here $t \neq 0$, since $v \neq 0$. So $P = Q$. $\square$

<?decl Projectivization.independent_pair_iff_ne?>

**Theorem (Vectors and points).** The map $(P, a) \mapsto a \cdot \operatorname{rep}(P)$ is a bijection $\mathbb{P}(V) \times K^{\times} \to V \setminus \{0\}$. So if $V$ is finite, then $|V| - 1 = |\mathbb{P}(V)| \cdot (|K| - 1)$.

*Proof.* Injective: if $a \operatorname{rep}(P) = b \operatorname{rep}(Q)$, then $P = [a \operatorname{rep}(P)] = [b \operatorname{rep}(Q)] = Q$, so $(a - b) \operatorname{rep}(P) = 0$ and $a = b$ since $\operatorname{rep}(P) \neq 0$. Surjective: for $v \neq 0$, put $P = [v]$; then $[v] = [\operatorname{rep}(P)]$, so $v = a \operatorname{rep}(P)$ for some $a \in K^{\times}$. For the count, $|V \setminus \{0\}| = |V| - 1$ and $|K^{\times}| = |K| - 1$. $\square$

In the language of Volume 5, Chapter 6: $K^{\times}$ acts freely on $V \setminus \{0\}$, so every orbit has $|K^{\times}|$ elements, and the theorem is the orbit count.

::: mathlib
`Projectivization.nonZeroEquivProjectivizationProdUnits` · `Mathlib.LinearAlgebra.Projectivization.Cardinality`

The bijection `{v // v ≠ 0} ≃ ℙ k V × kˣ`. The count `Projectivization.card` is `Nat.card V - 1 = Nat.card (ℙ k V) * (Nat.card k - 1)`.

<?decl Projectivization.nonZeroEquivProjectivizationProdUnits?>
:::

<?decl Projectivization.card?>

**Corollary (Points over a finite field).** Let $K = \mathbb{F}_q$ be a finite field with $q$ elements and let $\dim V = n + 1$. Then
$$|\mathbb{P}(V)| = \frac{q^{n+1} - 1}{q - 1} = \sum_{i = 0}^{n} q^i.$$
In particular a projective line over $\mathbb{F}_q$ has $q + 1$ points and a projective plane has $q^2 + q + 1$ points.

*Proof.* A basis gives $V \cong K^{n+1}$ (Volume 7, Chapter 2), so $|V| = q^{n+1}$. By the theorem, $q^{n+1} - 1 = |\mathbb{P}(V)| (q - 1)$, and $q - 1 \geq 1$. The second form follows from $q^{n+1} - 1 = (q - 1)(1 + q + \dots + q^n)$. $\square$

::: mathlib
`Projectivization.card_of_finrank` · `Mathlib.LinearAlgebra.Projectivization.Cardinality`

For a finite field `k` and `finrank k V = n`, `Nat.card (ℙ k V) = ∑ i ∈ Finset.range n, Nat.card k ^ i`; here `n` is $\dim V$, so the sum runs to $n - 1$. `card_of_finrank_two` is the line, with `Nat.card k + 1` points.

<?decl Projectivization.card_of_finrank?>
:::

<?decl Projectivization.card_of_finrank_two?>

**Proposition (Affine decomposition).** The points $[x_0 : \dots : x_n]$ of $\mathbb{P}^n(K)$ with $x_0 \neq 0$ are in bijection with $K^n$ by $[x_0 : \dots : x_n] \mapsto (x_1 / x_0, \dots, x_n / x_0)$, and the points with $x_0 = 0$ form a copy of $\mathbb{P}^{n-1}(K)$.

*Proof.* For $x_0 \neq 0$, the point has the unique representative $(1, x_1/x_0, \dots, x_n/x_0)$ with first coordinate $1$: two such representatives differ by a unit $a$ with $a \cdot 1 = 1$. Conversely $(y_1, \dots, y_n) \mapsto [1 : y_1 : \dots : y_n]$ is the inverse map. The points with $x_0 = 0$ are the points of $\mathbb{P}(0 \times K^n)$, the image of $\mathbb{P}^{n-1}(K)$ under the injective map $y \mapsto (0, y)$. $\square$

With $K = \mathbb{F}_q$ this gives $|\mathbb{P}^n| = q^n + |\mathbb{P}^{n-1}|$, a second proof of the corollary by induction on $n$.

### Examples

**Example (The projective line over $\mathbb{F}_2$).** $\mathbb{P}^1(\mathbb{F}_2)$ has the $2^2 - 1 = 3$ nonzero vectors of $\mathbb{F}_2^2$ as its points, since $\mathbb{F}_2^{\times} = \{1\}$: the points are $[1 : 0]$, $[0 : 1]$ and $[1 : 1]$. The formula gives $(4 - 1)/(2 - 1) = 3$.

**Example (The Fano plane).** $\mathbb{P}^2(\mathbb{F}_2)$ has $(8 - 1)/(2 - 1) = 7$ points, the seven nonzero vectors of $\mathbb{F}_2^3$. Its lines are the planes of $\mathbb{F}_2^3$, and each contains $3$ points. Over $\mathbb{F}_3$ the projective plane has $(27 - 1)/2 = 13$ points: the $9$ points $[1 : y_1 : y_2]$ of the affine plane and the $4$ points of the line at infinity $x_0 = 0$.

**Counterexample (Maps that are not injective).** The projection $f : K^2 \to K$, $(x, y) \mapsto x$, is linear but sends the nonzero vector $(0, 1)$ to $0$. The formula $[v] \mapsto [f(v)]$ does not define a point for $[0 : 1]$, so a linear map induces a map of projective spaces only when it is injective; otherwise it is defined only outside the projectivized kernel.

**Counterexample (Three points).** In $\mathbb{P}^1(K)$ the points $[1 : 0]$, $[0 : 1]$ and $[1 : 1]$ are pairwise distinct, so every pair is independent, but the three are dependent, since $(1, 1) = (1, 0) + (0, 1)$. Pairwise independence does not imply independence.

### The library around it

The files are `Mathlib.LinearAlgebra.Projectivization.Basic`, `.Cardinality` and `.Independence`. Section 2 treats subspaces and the linear groups; projective varieties belong to the volumes on algebraic geometry.

### Exercises

1. (A) List the points of $\mathbb{P}^1(\mathbb{F}_3)$ and check that there are $4$. Hint: each point is $[1 : t]$ or $[0 : 1]$.
2. (A) Compute the number of points of $\mathbb{P}^3(\mathbb{F}_2)$ and of $\mathbb{P}^2(\mathbb{F}_4)$. Hint: use the corollary.
3. (A) Show that $[2 : 4 : 6] = [1 : 2 : 3]$ in $\mathbb{P}^2(\mathbb{Q})$, and that $[1 : 2] \neq [2 : 1]$. Hint: use the criterion `mk_eq_mk_iff'`.
4. (B) Count the number of $k$-dimensional subspaces of $\mathbb{F}_q^n$ for $k = 2$. Hint: count ordered pairs of independent vectors and divide by the number of bases of a plane.
5. (B) Show that $\mathbb{P}(f)$ is injective for each injective linear map $f$, and that $\mathbb{P}(f \circ g) = \mathbb{P}(f) \circ \mathbb{P}(g)$. Hint: compute on points $[v]$.
6. (C) Let $K$ be infinite and $\dim V \ge 2$. Show that $\mathbb{P}(V)$ is not the union of finitely many proper projective subspaces, that is, images of proper subspaces of $V$. Hint: a line of $\mathbb{P}(V)$ meets each proper subspace not containing it in at most one point.

### Notes and history

Points at infinity were used by Desargues in the seventeenth century, and homogeneous coordinates were introduced in the nineteenth century, by Möbius and by Plücker. The projective planes over finite fields are the first examples of finite geometries; the Fano plane is named after Gino Fano.

### Reference

<?reference?>
