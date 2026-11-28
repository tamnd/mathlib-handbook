---
title: Algebraic cycles and order of vanishing
kind: theory
modules:
  - Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
  - Mathlib.AlgebraicGeometry.OrderOfVanishing.Basic
  - Mathlib.AlgebraicGeometry.OrderOfVanishing.DVR
explains:
  E3: [AlgebraicGeometry.AlgebraicCycle, AlgebraicGeometry.AlgebraicCycle.map, AlgebraicGeometry.AlgebraicCycle.degree, AlgebraicGeometry.AlgebraicCycle.IsWeilDivisor, AlgebraicGeometry.Scheme.ordHom, AlgebraicGeometry.Scheme.ord, AlgebraicGeometry.Scheme.ord_mul, AlgebraicGeometry.Scheme.ord_add, AlgebraicGeometry.Scheme.ord_algebraMap_eq_of_eq_unit_mul_pow]
  E2: [AlgebraicGeometry.AlgebraicCycle.mapCoeff, AlgebraicGeometry.AlgebraicCycle.map_id, AlgebraicGeometry.AlgebraicCycle.degree_single, AlgebraicGeometry.AlgebraicCycle.degree_eq_map_of_unique, AlgebraicGeometry.AlgebraicCycle.weilDivisors, AlgebraicGeometry.AlgebraicCycle.isWeilDivisor_iff, AlgebraicGeometry.Scheme.ord_inv, AlgebraicGeometry.Scheme.ord_div, AlgebraicGeometry.Scheme.ord_pow, AlgebraicGeometry.Scheme.ord_zpow, AlgebraicGeometry.Scheme.ord_prod, AlgebraicGeometry.Scheme.ord_neg, AlgebraicGeometry.Scheme.ord_of_isUnit, AlgebraicGeometry.Scheme.ord_algebraMap_nonneg, AlgebraicGeometry.Scheme.ord_eq_zero_of_mem_basicOpen, AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one, AlgebraicGeometry.Scheme.le_ord_iff, AlgebraicGeometry.Scheme.coheight_eq_one_of_isDiscreteValuationRing, AlgebraicGeometry.Scheme.ord_algebraMap_irreducible, AlgebraicGeometry.Scheme.mem_maximalIdeal_iff_one_le_ord, AlgebraicGeometry.Scheme.exists_algebraMap_eq_iff_ord_nonneg, AlgebraicGeometry.Scheme.one_le_ord_iff_notMem_basicOpen]
  E1: auto
families: []
requires: [V09.C03, V10.C03, V10.C07, V28.C04, V28.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Algebraic cycles and order of vanishing

### Overview

An algebraic cycle on a scheme $X$ is a formal sum $\sum n_Z [Z]$ of integral closed subschemes with integer coefficients, finite on each quasi-compact open. A closed integral subscheme is determined by its generic point, so a cycle is a function from the points of $X$ to $\mathbb{Z}$ with locally finite support. Weil divisors are the cycles supported on points of codimension one. The basic source of divisors is a rational function $f$: at each codimension-one point $z$ it has an order of vanishing $\operatorname{ord}_z(f)$, positive at zeros and negative at poles.

This section defines cycles, their pushforward and the degree of zero-cycles, and the order of vanishing on a locally Noetherian integral scheme through the length of a quotient of the local ring. It proves that the order is a homomorphism on nonzero elements, computes it when the local ring is a discrete valuation ring, and proves the finiteness that makes the divisor of a function a cycle.

### Definitions

**Definition (Algebraic cycle).** Let $X$ be a scheme and $R$ a type with a zero. An *algebraic cycle* on $X$ with coefficients in $R$ is a function $c : X \to R$ whose support $\{x : c(x) \ne 0\}$ is locally finite: each point has an open neighbourhood that meets the support in a finite set.

A point $x$ stands for the closed subscheme $\overline{\{x\}}$ with its reduced structure. The cycles form an abelian group when $R$ does.

**Definition (Weil divisor).** A cycle $c$ is a *Weil divisor* when each point of its support has coheight $1$. On a scheme the coheight of $x$ is the Krull dimension of the local ring $\mathcal{O}_{X,x}$. So the support consists of points of codimension one.

**Definition (Residue degree).** Let $f : X \to Y$ be a morphism and $x \in X$. The *residue degree* of $f$ at $x$ is the dimension of $\kappa(x)$ as a vector space over $\kappa(f(x))$, with value $0$ when this dimension is infinite.

**Definition (Pushforward of cycles).** Let $f : X \to Y$ be quasi-compact and $w_X : X \to N$, $w_Y : Y \to N$ two weight functions. The *pushforward* $f_*c$ of a cycle $c$ has at $y \in Y$ the coefficient $\sum_{f(x) = y} m(x) c(x)$, where $m(x)$ is the residue degree of $f$ at $x$ when $w_X(x) = w_Y(f(x))$ and $0$ otherwise.

The weights are usually dimensions: a subvariety that drops dimension under $f$ has pushforward $0$.

**Definition (Degree of a zero-cycle).** Let $X$ be quasi-compact and $f : X \to Y$. The *degree* of a cycle $D$ with respect to $f$ is $\deg_f D = \sum_x m_f(x) D(x)$, with $m_f(x)$ the residue degree.

On a quasi-compact space a locally finite support is finite, so the sum is finite.

**Definition (Order of a ring element).** Let $A$ be a Noetherian local domain of dimension at most $1$. For $a \in A$ the *order* $\operatorname{ord}_A(a)$ is the length of the $A$-module $A/(a)$. For $a, b \ne 0$ the order of $a/b$ in the fraction field is $\operatorname{ord}_A(a) - \operatorname{ord}_A(b)$.

**Definition (Order of vanishing).** Let $X$ be integral and locally Noetherian, with function field $K(X)$. For $f \in K(X)$ and $z \in X$ of coheight $1$, $\operatorname{ord}_z(f)$ is the order of $f$ for the local ring $\mathcal{O}_{X,z}$, whose fraction field is $K(X)$. In Mathlib $\operatorname{ord}_z(f)$ has the junk value $0$ when $f = 0$ or when $z$ does not have coheight $1$.

### Theorems and proofs

**Lemma (Finite length).** Let $A$ be a Noetherian local domain of dimension $1$ and $a \ne 0$ in $A$. Then $A/(a)$ has finite length.

*Proof.* The primes of $A$ are $(0)$ and the maximal ideal $\mathfrak{m}$. A prime that contains $a$ is not $(0)$, so it is $\mathfrak{m}$. So $A/(a)$ is a Noetherian ring with one prime, so it has dimension $0$ and it is Artinian. An Artinian module over itself has finite length, and its $A$-submodules are its ideals, so its length as an $A$-module is finite. $\square$

**Theorem (Order is multiplicative).** For nonzero $a, b$ in $A$ as above, $\operatorname{ord}_A(ab) = \operatorname{ord}_A(a) + \operatorname{ord}_A(b)$. So $\operatorname{ord}_z(fg) = \operatorname{ord}_z(f) + \operatorname{ord}_z(g)$ for nonzero $f, g \in K(X)$.

*Proof.* Step 1. Consider $0 \to A/(b) \xrightarrow{\cdot a} A/(ab) \to A/(a) \to 0$, with the first map $r \mapsto ar$ and the second map the projection. The first map is well defined, since $a(b) \subseteq (ab)$. It is injective: if $ar = abs$ then $r = bs$, because $A$ is a domain. The image of the first map is $(a)/(ab)$, which is the kernel of the projection $A/(ab) \to A/(a)$.

Step 2. Length is additive on short exact sequences, so $\operatorname{ord}(ab) = \operatorname{ord}(b) + \operatorname{ord}(a)$.

Step 3. The order on the fraction field is well defined: if $a/b = c/d$ then $ad = bc$, and step 2 gives $\operatorname{ord} a + \operatorname{ord} d = \operatorname{ord} b + \operatorname{ord} c$. Additivity for fractions follows from step 2 applied to numerators and denominators. $\square$

**Corollary (Inverses and units).** For $f \ne 0$, $\operatorname{ord}_z(f^{-1}) = -\operatorname{ord}_z(f)$. A unit $u$ of $\mathcal{O}_{X,z}$ has order $0$, and an element of $\mathcal{O}_{X,z}$ has order at least $0$.

*Proof.* The theorem gives $\operatorname{ord}(f) + \operatorname{ord}(f^{-1}) = \operatorname{ord}(1) = 0$, since $A/(1) = 0$. For a unit $u$ one has $A/(u) = 0$. A length is at least $0$. $\square$

**Theorem (The DVR case).** Assume that $\mathcal{O}_{X,z}$ is a discrete valuation ring with uniformizer $\varpi$. Then $z$ has coheight $1$. For a unit $u$ and $n \ge 0$, $\operatorname{ord}_z(u\varpi^n) = n$. For $f, g \in K(X)$ with $f + g \ne 0$, $\operatorname{ord}_z(f + g) \ge \min(\operatorname{ord}_z f, \operatorname{ord}_z g)$.

*Proof.* A discrete valuation ring has dimension $1$, so the coheight of $z$ is $1$. In $A = \mathcal{O}_{X,z}$ the ideals that contain $\varpi^n$ are the $(\varpi^i)$ with $0 \le i \le n$. So $A/(\varpi^n)$ has the composition series $A/(\varpi^n) \supset (\varpi)/(\varpi^n) \supset \dots \supset (\varpi^n)/(\varpi^n) = 0$, whose factors $(\varpi^i)/(\varpi^{i+1}) \cong A/\mathfrak{m}$ are simple. So its length is $n$, and $\operatorname{ord}(u\varpi^n) = \operatorname{ord}(u) + n = n$.

For the inequality, let $f = 0$ first. The junk value gives $\operatorname{ord} f = 0$, and $\min(0, \operatorname{ord} g) \le \operatorname{ord} g = \operatorname{ord}(f + g)$. The case $g = 0$ is the same. Otherwise each nonzero element of $K(X)$ is $u\varpi^m$ with $m \in \mathbb{Z}$. Let $f = u\varpi^m$ and $g = v\varpi^n$ with $m \le n$. Then $f + g = \varpi^m(u + v\varpi^{n-m})$, and $u + v\varpi^{n-m}$ is a nonzero element of $A$, so its order is at least $0$. So $\operatorname{ord}(f + g) \ge m$. $\square$

In the DVR case $\operatorname{ord}_z(f) \ge 0$ holds exactly when $f \in \mathcal{O}_{X,z}$, and $\operatorname{ord}_z(f) \ge 1$ holds exactly when $f \in \mathfrak{m}_z$.

**Proposition (Finiteness of zeros and poles).** Let $X$ be a Noetherian integral scheme and $f \in K(X)$ nonzero. Then $\operatorname{ord}_z(f) \ne 0$ for only finitely many points $z$ of coheight $1$.

*Proof.* Step 1. Choose a nonempty affine open $\operatorname{Spec} A$ and write $f = a/b$ with $a, b \in A$ nonzero. On $U = D(ab)$ both $a$ and $b$ are units, so $f$ is a unit of $\Gamma(U, \mathcal{O}_X)$. For $z \in U$ the corollary gives $\operatorname{ord}_z(f) = 0$.

Step 2. The complement $X \setminus U$ is a proper closed subset of the Noetherian space $X$. It has finitely many irreducible components $Z_1, \dots, Z_r$, each with a generic point $\zeta_j$, and each $Z_j \ne X$.

Step 3. Let $z \notin U$ have coheight $1$. The closure of $z$ is irreducible and lies in $X \setminus U$, so it lies in some $Z_j$. So $\zeta_j$ is a generization of $z$. Coheight $1$ means that the only generizations of $z$ are $z$ and the generic point $\eta$ of $X$. Since $Z_j \ne X$, $\zeta_j \ne \eta$, so $\zeta_j = z$. So $z$ is one of the finitely many $\zeta_j$. $\square$

On a Noetherian integral scheme the function $z \mapsto \operatorname{ord}_z(f)$ is therefore a Weil divisor, the principal divisor of $f$. The index of this edition has no declaration for this principal divisor.

**Proposition (Degree as a pushforward).** Let $Y$ have one point and $f : X \to Y$ be quasi-compact. If the weights match at each $x$ with $D(x) \ne 0$ and nonzero residue degree, then $\deg_f D$ is the coefficient of $f_* D$ at the point of $Y$.

*Proof.* The preimage of the point is all of $X$, so the coefficient of $f_* D$ is $\sum_x m(x) D(x)$. For $x$ with $D(x) = 0$ or zero residue degree both summands vanish. For the other $x$ the weights match, so $m(x)$ is the residue degree. $\square$

### Examples

**Example (Orders on the integers).** Let $X = \operatorname{Spec} \mathbb{Z}$ and $f = 12/5$. At $(2)$ the local ring is $\mathbb{Z}_{(2)}$, and $12 = 3 \cdot 2^2$ with $3$ a unit, so $\operatorname{ord}_{(2)}(12) = 2$. A check: $\mathbb{Z}_{(2)}/(12) = \mathbb{Z}_{(2)}/(4) \cong \mathbb{Z}/4$, which has the composition series $\mathbb{Z}/4 \supset 2\mathbb{Z}/4 \supset 0$ of length $2$. At $(3)$ the order of $12$ is $1$, and at $(5)$ the order of $5$ is $1$. So $\operatorname{ord}_{(2)} f = 2$, $\operatorname{ord}_{(3)} f = 1$, $\operatorname{ord}_{(5)} f = -1$, and $\operatorname{ord}_{(p)} f = 0$ for the other primes. The principal divisor is $2[(2)] + [(3)] - [(5)]$.

**Example (A rational function on the line).** Let $k$ be a field of characteristic not $2$ and $f = x^2(x - 1)/(x + 1)$ on $\mathbb{A}^1_k$. The local rings at closed points are discrete valuation rings with uniformizers $x - c$. The points $0, 1, -1$ are distinct, so $\operatorname{ord}_0 f = 2$, $\operatorname{ord}_1 f = 1$ and $\operatorname{ord}_{-1} f = -1$. At other closed points the numerator and denominator are units. The generic point has coheight $0$, so the junk value $0$ applies there.

**Example (Degree zero on the projective line).** Let $f = x/y$ on $\mathbb{P}^1_k$. On $D(y)$ with coordinate $t = x/y$, $f = t$ has a simple zero at $[0 : 1]$. On $D(x)$ with coordinate $u = y/x$, $f = u^{-1}$ has a simple pole at $[1 : 0]$. Both points are $k$-rational, so their residue degrees over $\operatorname{Spec} k$ are $1$. The degree of $[0 : 1] - [1 : 0]$ is $1 - 1 = 0$.

**Example (A point of degree two).** On $\mathbb{A}^1_{\mathbb{R}}$ the point $z = (x^2 + 1)$ has residue field $\mathbb{R}[x]/(x^2 + 1) \cong \mathbb{C}$. Its residue degree over $\operatorname{Spec} \mathbb{R}$ is $2$. The function $x^2 + 1$ has order $1$ at $z$, since it generates the maximal ideal of the local ring, so its divisor $[z]$ has degree $2$. This equals the degree of the polynomial.

**Example (Pushforward along the squaring map).** Let $f : \mathbb{A}^1_{\mathbb{R}} \to \mathbb{A}^1_{\mathbb{R}}$ be given by $\mathbb{R}[y] \to \mathbb{R}[x]$, $y \mapsto x^2$, and take both weights equal to the coheight. The closed points $(x - 1)$ and $(x + 1)$ both map to $(y - 1)$ with residue degree $1$, so $f_*([(x - 1)] + [(x + 1)]) = 2[(y - 1)]$. The point $(x^2 + 1)$ maps to $(y + 1)$, since $y + 1 \mapsto x^2 + 1$. Its residue field $\mathbb{C}$ has degree $2$ over the residue field $\mathbb{R}$ of $(y + 1)$, so $f_*[(x^2 + 1)] = 2[(y + 1)]$. In both cases the coefficient $2$ is the degree of $f$.

### The library around it

::: mathlib
`AlgebraicGeometry.AlgebraicCycle` · `Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic`

`AlgebraicCycle X R` is an abbreviation for `Function.locallyFinsupp X R`, tagged Stacks 02QR. `AlgebraicCycle.IsWeilDivisor` asks the support to lie in `{x | coheight x = 1}`, and `AlgebraicCycle.weilDivisors` is the subgroup with `AlgebraicCycle.isWeilDivisor_iff`.

<?decl AlgebraicGeometry.AlgebraicCycle?>
:::

::: mathlib
`AlgebraicGeometry.AlgebraicCycle.map` · `Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic`

`AlgebraicCycle.map f wx wy c` needs `[QuasiCompact f]` and uses `AlgebraicCycle.mapCoeff`, which is `f.residueDegree x` when `wx x = wy (f.base x)` and `0` otherwise. `AlgebraicCycle.map_id` holds for equal weights. `AlgebraicCycle.degree f` needs `[CompactSpace X]`, and `AlgebraicCycle.degree_single` and `AlgebraicCycle.degree_eq_map_of_unique` are the computations above. The residue degree is `Scheme.Hom.residueDegree` in `ResidueField`.

<?decl AlgebraicGeometry.AlgebraicCycle.map?>
:::

::: mathlib
`AlgebraicGeometry.Scheme.ord` · `Mathlib.AlgebraicGeometry.OrderOfVanishing.Basic`

`Scheme.ordHom z hz` is `Ring.ordFrac` of the stalk, a monoid with zero hom to `ℤᵐ⁰`, and `Scheme.ord f z` converts it to `ℤ` with the junk values. The ring version `Ring.ord` is the length `Module.length R (R ⧸ span {x})`, tagged Stacks 02MD. The algebra lemmas are `Scheme.ord_mul`, `Scheme.ord_inv`, `Scheme.ord_div`, `Scheme.ord_pow`, `Scheme.ord_zpow` and `Scheme.ord_prod`, each with nonzero hypotheses. `Scheme.ord_eq_zero_of_mem_basicOpen` is step 1 of the finiteness proof.

<?decl AlgebraicGeometry.Scheme.ord?>
:::

::: mathlib
`AlgebraicGeometry.Scheme.ord_add` · `Mathlib.AlgebraicGeometry.OrderOfVanishing.DVR`

Under `[IsDiscreteValuationRing (X.presheaf.stalk x)]`, `Scheme.coheight_eq_one_of_isDiscreteValuationRing` gives coheight `1`, and `Scheme.ord_add` is the ultrametric inequality with the hypothesis `f + g ≠ 0`. `Scheme.ord_algebraMap_eq_of_eq_unit_mul_pow` and `Scheme.ord_algebraMap_irreducible` compute orders. `Scheme.exists_algebraMap_eq_iff_ord_nonneg` and `Scheme.mem_maximalIdeal_iff_one_le_ord` are the two membership criteria.

<?decl AlgebraicGeometry.Scheme.ord_add?>
:::

Common errors of a learner: `Scheme.ord` returns `0` at points of the wrong coheight and at `f = 0`, so a value `0` does not mean that `f` is a unit there. The coheight of a point is the dimension of its local ring, not of its closure. The pushforward depends on the weight functions, and with constant weights it does not drop the cycles that lose dimension. The ultrametric inequality needs a discrete valuation ring, so it is stated in the separate file `OrderOfVanishing.DVR`.

### Exercises

1. (A) Compute the principal divisor of $f = 18/49$ on $\operatorname{Spec} \mathbb{Z}$. *Hint:* Factor $18$ and $49$.
2. (A) Show that the order of $x^3 - x^2$ at the origin of $\mathbb{A}^1_k$ is $2$ by computing the length of $k[x]_{(x)}/(x^3 - x^2)$. *Hint:* $x - 1$ is a unit at the origin.
3. (B) Let $A = k[x, y]_{(x, y)}/(y^2 - x^3)$, the local ring of the cusp. Compute $\operatorname{ord}_A(x)$ and $\operatorname{ord}_A(y)$. *Hint:* $A/(x) \cong k[y]/(y^2)$ and $A/(y) \cong k[x]/(x^3)$.
4. (B) Show that the ultrametric inequality is an equality when $\operatorname{ord} f \ne \operatorname{ord} g$. *Hint:* Write $f + g = \varpi^m(u + v\varpi^{n-m})$ with $n > m$.
5. (B) On $\mathbb{A}^1_{\mathbb{R}}$, find the degree of the divisor of $(x^2 + 1)(x - 3)$ over $\operatorname{Spec} \mathbb{R}$. *Hint:* Use the residue degrees $2$ and $1$.
6. (C) Show that a principal divisor on $\mathbb{P}^1_k$ of a nonzero homogeneous fraction $g/h$ with $\deg g = \deg h$ has degree $0$ over $\operatorname{Spec} k$. *Hint:* Factor $g$ and $h$ into irreducibles and count each zero with its residue degree.

### Notes and history

Cycles and divisors go back to the classical theory of curves and surfaces. Weil divisors and the order of vanishing on Noetherian integral schemes are treated in Hartshorne, Chapter II, Section 6, and Fulton develops cycles, pushforward and rational equivalence in his book on intersection theory. The Mathlib sources follow the Stacks project.

The Mathlib Author of `AlgebraicCycle.Basic`, `OrderOfVanishing.Basic` and `OrderOfVanishing.DVR` is Raphael Douglas Giles.

### Reference

<?reference?>
