---
title: Star rings
kind: theory
modules:
  - Mathlib.Algebra.Star.Basic
  - Mathlib.Algebra.Star.SelfAdjoint
  - Mathlib.Algebra.Order.Star.Basic
explains:
  E3: [StarRing, IsSelfAdjoint, StarOrderedRing]
  E2: [StarMul, StarMul.star_mul, StarAddMonoid, InvolutiveStar, star_star, star_one, star_mul', star_inv₀, starRingEnd, starRingOfComm, TrivialStar, selfAdjoint, skewAdjoint, IsSelfAdjoint.star_mul_self, IsSelfAdjoint.add, IsSelfAdjoint.commute_iff, IsStarNormal, star_mul_self_nonneg, StarOrderedRing.le_iff]
  E1: auto
families: []
requires: [V06.C05, V06.C07]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Star rings

### Overview

Complex conjugation, the conjugate transpose of a complex matrix, and the conjugate of a quaternion share three properties. Each is additive, each undoes itself when applied twice, and each reverses the order of a product. A ring with such an operation is a star ring, and the operation is written $x \mapsto x^*$. Star rings are the algebraic frame of the spectral theorem and of operator algebras: the self-adjoint elements play the role of real numbers, and the elements $x^* x$ play the role of nonnegative numbers. This section defines star rings, proves the first rules, works out the main examples, and proves that the conjugate transpose reverses products. It defines self-adjoint and normal elements, and it ends with star-ordered rings, where the order comes from the elements $x^* x$. The analytic theory, with C*-algebras, is in Volume 16.

### Definitions

**Definition (Star ring).** A star ring is a ring $R$ with a map $* : R \to R$, $x \mapsto x^*$, such that for all $x, y \in R$:

1. $(x^*)^* = x$;
2. $(x + y)^* = x^* + y^*$;
3. $(x y)^* = y^* x^*$.

The map is an involution. Condition 3 says that it is an anti-homomorphism for the multiplication. On a commutative ring, condition 3 says that $*$ is multiplicative.

**Definition (Self-adjoint, skew-adjoint, normal).** Let $R$ be a star ring and $x \in R$. The element $x$ is self-adjoint if $x^* = x$, skew-adjoint if $x^* = -x$, and normal if $x x^* = x^* x$.

**Definition (Star-ordered ring).** A star-ordered ring is a star ring $R$ with a partial order such that $x \le y$ if and only if $y = x + p$ for some $p$ that is a finite sum of elements of the form $s^* s$.

In a star-ordered ring the nonnegative elements are exactly the finite sums of elements $s^* s$. The order is determined by the star.

::: mathlib
`StarRing` · `Mathlib.Algebra.Star.Basic`

`StarRing R` takes `[NonUnitalNonAssocSemiring R]`. It is built from smaller classes: `InvolutiveStar R` (condition 1, with the field `star_involutive`), `StarMul R` (condition 3, with the field `star_mul`), and the additivity of `StarAddMonoid R` (condition 2). The operation is `star x`, written `x⋆` in some files. Since the operation is data, `StarRing` is a class of data, not a `Prop`.

<?decl StarRing?>
:::

::: mathlib
`StarMul.star_mul` · `Mathlib.Algebra.Star.Basic`

The statement is `star (r * s) = star s * star r`. For a commutative monoid the lemma `star_mul'` gives `star (r * s) = star r * star s`. Other basic lemmas are `star_star`, `star_one`, `star_zero`, `star_neg` and, in a division ring, `star_inv₀ : star x⁻¹ = (star x)⁻¹`.

<?decl StarMul.star_mul?>
:::

### Theorems and proofs

**Proposition (First rules).** In a star ring $R$, $0^* = 0$, $1^* = 1$ and $(-x)^* = -x^*$. If $x$ is a unit, then $x^*$ is a unit and $(x^*)^{-1} = (x^{-1})^*$.

*Proof.* The map $*$ is additive, so it sends $0$ to $0$ and $-x$ to $-x^*$. For the unit, let $x \in R$. By conditions 3 and 1,
$$1^* x = 1^* (x^*)^* = (x^* \cdot 1)^* = (x^*)^* = x.$$
So $1^*$ is a left identity. Then $1^* = 1^* \cdot 1 = 1$, where the second step uses that $1^*$ is a left identity. For a unit $x$, apply $*$ to $x x^{-1} = 1$ and to $x^{-1} x = 1$. This gives $(x^{-1})^* x^* = 1$ and $x^* (x^{-1})^* = 1$. So $(x^{-1})^*$ is a two-sided inverse of $x^*$. $\square$

**Proposition (Stars on commutative rings).** Let $R$ be a commutative ring.

1. The identity map is a star on $R$.
2. A star on $R$ is a ring automorphism of $R$ of order at most $2$.
3. The identity map is a star on a ring $A$ if and only if $A$ is commutative.

*Proof.* (1) and (3): the identity satisfies conditions 1 and 2. Condition 3 for the identity reads $x y = y x$, which holds for all $x, y$ exactly when the ring is commutative. (2) By condition 3 and commutativity, $(x y)^* = y^* x^* = x^* y^*$. With the first rules and condition 2, the star is a ring homomorphism. It is its own inverse, so it is an automorphism, and applying it twice gives the identity. $\square$

::: mathlib
`starRingEnd` · `Mathlib.Algebra.Star.Basic`

For a commutative semiring `R` with `[StarRing R]`, `starRingEnd R : R →+* R` is the star as a ring homomorphism. On `ℂ` it is complex conjugation, written `conj` after `open ComplexConjugate`. The construction `starRingOfComm` gives each commutative semiring the trivial star, and the `Prop` class `TrivialStar R` says that `star x = x` for all `x`. The real numbers have the trivial star.

<?decl starRingEnd?>
:::

**Theorem (Conjugate transpose).** Let $R$ be a star ring and $n \ge 1$. For $A \in M_n(R)$ define $A^*$ by $(A^*)_{i j} = (A_{j i})^*$. Then $M_n(R)$ is a star ring.

*Proof.* Condition 1: $((A^*)^*)_{i j} = ((A^*)_{j i})^* = ((A_{i j})^*)^* = A_{i j}$. Condition 2 holds since the star of $R$ and the transpose are both additive. Condition 3: for matrices $A, B$,
$$((A B)^*)_{i j} = \big((A B)_{j i}\big)^* = \Big(\sum_k A_{j k} B_{k i}\Big)^* = \sum_k (B_{k i})^* (A_{j k})^*.$$
The last step uses that the star of $R$ is additive and reverses products. Now $(B_{k i})^* = (B^*)_{i k}$ and $(A_{j k})^* = (A^*)_{k j}$. So the sum is $\sum_k (B^*)_{i k} (A^*)_{k j} = (B^* A^*)_{i j}$. $\square$

The proof needs the reversal in $R$ and the reversal from the transpose. For $R = \mathbb{C}$ the star is the conjugate transpose of linear algebra. For $R = \mathbb{R}$, with the trivial star, it is the transpose. The theorem also needs the order of the factors in $(A_{j k} B_{k i})^* = (B_{k i})^* (A_{j k})^*$. Over a commutative ring the order does not matter, but over the quaternions it does.

::: mathlib
`Matrix.conjTranspose_mul` · `Mathlib.LinearAlgebra.Matrix.ConjTranspose`

The statement is `(M * N)ᴴ = Nᴴ * Mᴴ` for rectangular matrices over a star ring, where `Mᴴ` is `Matrix.conjTranspose M`. The star ring structure on square matrices uses this lemma, and `Matrix.star_eq_conjTranspose` states `star M = Mᴴ`. These lemmas are in Volume 7.

<?decl Matrix.conjTranspose_mul?>
:::

**Theorem (Quaternion conjugation).** On the real quaternions $\mathbb{H}$, the map $(a + b i + c j + d k)^* = a - b i - c j - d k$ is a star, and $q q^* = q^* q = a^2 + b^2 + c^2 + d^2$.

*Proof.* Conditions 1 and 2 are clear from the formula. Both sides of condition 3 are $\mathbb{R}$-bilinear in $(x, y)$, and the star is $\mathbb{R}$-linear. So it suffices to check condition 3 for $x, y \in \{1, i, j, k\}$. If $x = 1$ or $y = 1$, both sides agree by $1^* = 1$. Let $u, v \in \{i, j, k\}$, so $u^* = -u$ and $v^* = -v$. Then $v^* u^* = (-v)(-u) = v u$. If $u = v$, then $(u u)^* = (-1)^* = -1 = u u = v u$. If $u \ne v$, then $u v = \pm w$ for the third unit $w$, so $(u v)^* = \mp w = -u v$, and $v u = -u v$ by the multiplication table. In both cases $(u v)^* = v^* u^*$.

For the norm, write $q = a + p$ with $p = b i + c j + d k$. Then $q^* = a - p$ and $q q^* = a^2 - a p + p a - p^2 = a^2 - p^2$. The cross terms of $p^2$ cancel in pairs, since $i j = -j i$ and so on, and $p^2 = -(b^2 + c^2 + d^2)$. So $q q^* = a^2 + b^2 + c^2 + d^2$. The same computation gives $q^* q$. $\square$

::: mathlib
`Quaternion.self_mul_star` · `Mathlib.Algebra.Quaternion`

The statement is `a * star a = ↑(normSq a)` in `ℍ[R]`, where `Quaternion.normSq` is the sum of the four squares. The star ring instance on quaternions is in the same file. Chapter 3 uses this norm to show that `ℍ[ℝ]` is a division ring.

<?decl Quaternion.self_mul_star?>
:::

**Proposition (Self-adjoint elements).** Let $R$ be a star ring.

1. The self-adjoint elements form an additive subgroup that contains $1$.
2. For each $x \in R$, the elements $x + x^*$, $x^* x$ and $x x^*$ are self-adjoint.
3. If $x$ and $y$ are self-adjoint, then $x y$ is self-adjoint if and only if $x y = y x$.
4. If $2$ is a unit in $R$, each $x$ is uniquely the sum of a self-adjoint and a skew-adjoint element.

*Proof.* (1) If $x^* = x$ and $y^* = y$, then $(x - y)^* = x - y$, and $1^* = 1$. (2) $(x + x^*)^* = x^* + x$, and $(x^* x)^* = x^* (x^*)^* = x^* x$. The case $x x^*$ is the same. (3) $(x y)^* = y^* x^* = y x$, so $(x y)^* = x y$ if and only if $y x = x y$. (4) Write $h = (x + x^*)/2$ and $k = (x - x^*)/2$. Then $h^* = h$, $k^* = -k$ and $h + k = x$. The element $1/2$ is self-adjoint, since $2^* = 2$ and the star of an inverse is the inverse of the star. If $x = h' + k'$ is a second decomposition, then $h - h' = k' - k$ is both self-adjoint and skew-adjoint, so it equals its own negative, and $2(h - h') = 0$ gives $h = h'$. $\square$

In $\mathbb{C}$ this is the decomposition $z = \operatorname{Re} z + i \operatorname{Im} z$. In $M_n(\mathbb{C})$ it is the decomposition of a matrix into a Hermitian and a skew-Hermitian part.

::: mathlib
`IsSelfAdjoint` · `Mathlib.Algebra.Star.SelfAdjoint`

`IsSelfAdjoint x` is the `Prop` `star x = x`, defined for each type with `[Star R]`. Its lemmas follow the proposition: `IsSelfAdjoint.add`, `IsSelfAdjoint.star_mul_self : IsSelfAdjoint (star x * x)`, and `IsSelfAdjoint.commute_iff`, which states `Commute x y ↔ IsSelfAdjoint (x * y)` for self-adjoint `x` and `y`. The set of self-adjoint elements is the additive subgroup `selfAdjoint R`, and the skew-adjoint elements form `skewAdjoint R`.

<?decl IsSelfAdjoint?>
:::

::: mathlib
`IsStarNormal` · `Mathlib.Algebra.Star.SelfAdjoint`

`IsStarNormal x` is a `Prop` class with one field, `star_comm_self : Commute (star x) x`. It is a class so that instance search finds normality for self-adjoint elements and for elements built from them. The spectral theory of Volume 16 uses it.

<?decl IsStarNormal?>
:::

**Proposition (Nonnegativity of $s^* s$).** In a star-ordered ring, $s^* s \ge 0$ for each $s$. A sum of such elements is nonnegative, and every nonnegative element is self-adjoint.

*Proof.* Take $x = 0$ and $y = s^* s$ in the definition: $y = 0 + s^* s$ with $p = s^* s$, so $0 \le s^* s$. For a finite sum $p$ of such terms, $p = 0 + p$ gives $0 \le p$. If $0 \le y$, then $y = p$ is a finite sum of elements $s^* s$, each self-adjoint, so $y$ is self-adjoint by part 1 of the previous proposition. $\square$

::: mathlib
`StarOrderedRing` · `Mathlib.Algebra.Order.Star.Basic`

`StarOrderedRing R` is a `Prop` class over `[NonUnitalSemiring R] [PartialOrder R] [StarRing R]`. Its field is `StarOrderedRing.le_iff : x ≤ y ↔ ∃ p ∈ AddSubmonoid.closure (Set.range fun s ↦ star s * s), y = x + p`. The lemma `star_mul_self_nonneg : 0 ≤ star r * r` is the first claim of the proposition. Instances exist for `ℝ`, `ℂ` with its partial order, and the continuous functions with values in them.

<?decl StarOrderedRing?>
:::

### Examples

**Example (A matrix that is not normal).** Let $N = \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$ over $\mathbb{C}$. Then $N^* = \begin{pmatrix} 1 & 0 \\ 1 & 1 \end{pmatrix}$, and
$$N N^* = \begin{pmatrix} 2 & 1 \\ 1 & 1 \end{pmatrix}, \qquad N^* N = \begin{pmatrix} 1 & 1 \\ 1 & 2 \end{pmatrix}.$$
So $N$ is not normal. Both products are self-adjoint, as part 2 of the proposition says. The matrix $U = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}$ satisfies $U^* = -U$ and $U U^* = U^* U = I$. So $U$ is skew-adjoint and normal. The matrix $H = \begin{pmatrix} 2 & i \\ -i & 3 \end{pmatrix}$ is self-adjoint, since $(H^*)_{12} = \overline{H_{21}} = \overline{-i} = i$.

**Counterexample (Entrywise conjugation is not a star on matrices).** On $M_2(\mathbb{C})$ the map $A \mapsto \bar A$, conjugation of each entry with no transpose, is additive and involutive. It is multiplicative: $\overline{A B} = \bar A \bar B$. It is not a star. Take
$$A = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}, \quad B = \begin{pmatrix} 0 & 0 \\ 1 & 0 \end{pmatrix}, \quad A B = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}, \quad B A = \begin{pmatrix} 0 & 0 \\ 0 & 1 \end{pmatrix}.$$
All entries are real, so $\overline{A B} = A B$ and $\bar B \bar A = B A \ne A B$. Condition 3 fails. The same pair shows that the identity map on $M_2(\mathbb{R})$ is not a star, as part 3 of the proposition on commutative rings predicts.

**Example (The star order on $\mathbb{C}$).** With complex conjugation, $\bar s s = |s|^2$, a nonnegative real number. Every nonnegative real is of this form. So the star order on $\mathbb{C}$ is: $z \le w$ if and only if $w - z$ is a nonnegative real number. This is the partial order of Section 1 of Chapter 7. In it $i$ and $0$ are incomparable, since $i - 0$ and $0 - i$ are not real. The element $2 + 3 i \le 5 + 3 i$, since the difference is $3$.

### The library around it

Star rings in Mathlib start with the notation class `Star R` of Volume 5 and grow by mixins: `InvolutiveStar`, `StarMul`, `StarAddMonoid`, `StarRing`, and `StarModule R A` for a star algebra, where `star (r • x) = star r • star x`. The homomorphisms that preserve the star are `StarAlgHom`, written `A →⋆ₐ[R] B`, and the ring isomorphisms that preserve it are `StarRingEquiv`. The unitary elements, with `star u * u = 1 = u * star u`, form the submonoid `unitary R`. Volume 16 defines C*-algebras as complete normed star algebras with `‖star x * x‖ = ‖x‖ ^ 2`.

**Common errors of a learner.**

- Expecting `star (x * y) = star x * star y` in a noncommutative ring. That rule is `star_mul'`, and it needs commutativity. The general rule reverses the factors.
- Forgetting that the real numbers carry the trivial star. A lemma about `star` on `ℝ` reduces by `TrivialStar.star_trivial`.
- Assuming that the product of two self-adjoint elements is self-adjoint. It is only when they commute.
- Treating the star order as linear. On $\mathbb{C}$ and on matrices it is only partial.
- Confusing normal and self-adjoint. A self-adjoint element is normal, but $U$ in the example is normal and not self-adjoint.

### Exercises

1. (A) Show that $z \mapsto \bar z$ is a star on $\mathbb{C}$ and that its self-adjoint elements are the real numbers.
2. (A) Let $R$ be a star ring and $x$ self-adjoint. Show that $y^* x y$ is self-adjoint for each $y$.
3. (A) Compute $N^*$, $N N^*$ and $N^* N$ for $N = \begin{pmatrix} 1 & i \\ 0 & 2 \end{pmatrix}$, and decide whether $N$ is normal.
4. (B) Show that on $\mathbb{Z}[i]$ the conjugation is the only star other than the identity. Hint: a star is a ring automorphism, and it sends $i$ to a square root of $-1$.
5. (B) Show that a matrix in $M_n(\mathbb{C})$ with real entries is self-adjoint if and only if it is symmetric.
6. (B) Show that $x^* x = 0$ implies $x = 0$ in $M_n(\mathbb{C})$. Show that this fails in $\mathbb{C} \times \mathbb{C}$ with the star $(a, b)^* = (\bar b, \bar a)$. Hint: the trace of $x^* x$ is $\sum |x_{i j}|^2$; for the second part take $x = (1, 0)$.
7. (B) Show that every unitary element and every skew-adjoint element of a star ring is normal.
8. (C) In a star-ordered ring, show that $x \le y$ implies $z^* x z \le z^* y z$. Hint: $z^* (s^* s) z = (s z)^* (s z)$.
9. (C) Show that $\mathbb{R}$ with the trivial star and its usual order is star-ordered, using that every nonnegative real is a square.

### Notes and history

The conjugate transpose goes back to Hermite, who studied the forms now called Hermitian in 1855. The abstract notion of an involution on an algebra came from the theory of rings of operators. Gelfand and Naimark (1943) characterized the closed star algebras of operators on a Hilbert space by norm conditions, and Segal named them C*-algebras in 1947. In pure algebra, involutions of central simple algebras were classified by Albert in the 1930s in his work on Riemann matrices. In Mathlib, `StarOrderedRing` defines the order through the closure of the elements `star s * s`, so that the order is a consequence of the star and not an extra choice.

### Reference

<?reference?>
