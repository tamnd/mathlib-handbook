---
title: Number fields and rings of integers
kind: theory
modules:
  - Mathlib.NumberTheory.NumberField.Basic
  - Mathlib.NumberTheory.NumberField.Norm
  - Mathlib.NumberTheory.NumberField.Discriminant.Defs
  - Mathlib.NumberTheory.NumberField.Discriminant.Basic
explains:
  E3: [NumberField, NumberField.RingOfIntegers, NumberField.RingOfIntegers.norm, NumberField.discr]
  E2: [NumberField.RingOfIntegers.isIntegral_coe, NumberField.isAlgebraic, NumberField.RingOfIntegers.instIsDedekindDomain, NumberField.RingOfIntegers.rank, NumberField.RingOfIntegers.basis, NumberField.integralBasis, Rat.ringOfIntegersEquiv, NumberField.RingOfIntegers.coe_norm, NumberField.RingOfIntegers.isUnit_norm, NumberField.discr_eq_discr, NumberField.abs_discr_gt_two, NumberField.abs_discr_ge, NumberField.finite_of_discr_bdd, IsCyclotomicExtension.Rat.discr_prime]
  E1: auto
families: [NumberField.RingOfIntegers.*]
requires: [V06.C06, V07.C02, V12.C04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Number fields and rings of integers

### Overview

A number field is a field $K$ that is a finite extension of $\mathbb{Q}$. Its ring of integers $\mathcal{O}_K$ is the set of the elements of $K$ that are roots of a monic polynomial with integer coefficients. For $K = \mathbb{Q}$ it is $\mathbb{Z}$, and for $K = \mathbb{Q}(i)$ it is the ring $\mathbb{Z}[i]$ of Volume 6, Chapter 6. This section gives the definitions as Mathlib has them, computes $\mathcal{O}_K$ for every quadratic field, and introduces the norm and the discriminant. Section 2 uses both for the class group and the units.

### Definitions

**Definition (Number field).** A field $K$ is a number field if it has characteristic $0$ and is finite dimensional over $\mathbb{Q}$. Its degree is $[K : \mathbb{Q}] = \dim_{\mathbb{Q}}K$.

::: mathlib
`NumberField` · `Mathlib.NumberTheory.NumberField.Basic`

`class NumberField (K : Type*) [Field K] : Prop` with the fields `to_charZero : CharZero K` and `to_finiteDimensional : FiniteDimensional ℚ K`. Every number field is algebraic over `ℚ` (`NumberField.isAlgebraic`). Instances exist for `ℚ` and for the cyclotomic fields.

<?decl NumberField?>
:::

**Definition (Ring of integers).** $\mathcal{O}_K$ is the integral closure of $\mathbb{Z}$ in $K$: the set of $\alpha \in K$ with $f(\alpha) = 0$ for some monic $f \in \mathbb{Z}[X]$.

::: mathlib
`NumberField.RingOfIntegers` · `Mathlib.NumberTheory.NumberField.Basic`

`NumberField.RingOfIntegers K`, notation `𝓞 K`, is a type, not a subset of `K`. The map to `K` is `algebraMap (𝓞 K) K`, and `NumberField.RingOfIntegers.isIntegral_coe` says that its image is integral. For `ℚ`, `Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ`. Mathlib proves that `𝓞 K` is a Dedekind domain (`NumberField.RingOfIntegers.instIsDedekindDomain`) and a free `ℤ`-module of rank $[K : \mathbb{Q}]$ (`NumberField.RingOfIntegers.rank`), with a basis `NumberField.RingOfIntegers.basis` and its image `NumberField.integralBasis` in `K`.

<?decl NumberField.RingOfIntegers?>
:::

**Definition (Norm).** For $\alpha \in K$, the norm $N(\alpha) = N_{K/\mathbb{Q}}(\alpha)$ is the determinant of the $\mathbb{Q}$-linear map $x \mapsto \alpha x$ of $K$. It is multiplicative, and $N(\alpha) \in \mathbb{Z}$ for $\alpha \in \mathcal{O}_K$. For $K = \mathbb{Q}(\sqrt d)$, $N(x + y\sqrt d) = x^2 - dy^2$.

::: mathlib
`NumberField.RingOfIntegers.norm` · `Mathlib.NumberTheory.NumberField.Norm`

`RingOfIntegers.norm K : 𝓞 L →* 𝓞 K` for an extension `L / K`, with `coe_norm` relating it to `Algebra.norm K`. `NumberField.RingOfIntegers.isUnit_norm` says that `x` is a unit if and only if its norm is a unit.

<?decl NumberField.RingOfIntegers.norm?>
:::

**Definition (Discriminant).** Let $\omega_1, \dots, \omega_n$ be a $\mathbb{Z}$-basis of $\mathcal{O}_K$ and $\sigma_1, \dots, \sigma_n$ the embeddings $K \to \mathbb{C}$. The discriminant is $d_K = \det(\sigma_i(\omega_j))^2 = \det(\operatorname{Tr}(\omega_i\omega_j)) \in \mathbb{Z}$. It does not depend on the basis, since a change of basis multiplies the determinant by $\pm1$.

::: mathlib
`NumberField.discr` · `Mathlib.NumberTheory.NumberField.Discriminant.Defs`

`NumberField.discr K : ℤ` is `Algebra.discr ℤ` of the chosen basis, and `NumberField.discr_eq_discr` says that every basis of `𝓞 K` gives the same value.

<?decl NumberField.discr?>
:::

### Theorems and proofs

**Theorem (Integers of a quadratic field).** Let $d \ne 0, 1$ be a squarefree integer and $K = \mathbb{Q}(\sqrt d)$. Then
$$\mathcal{O}_K = \mathbb{Z}[\sqrt d] \ \text{ if } d \equiv 2, 3 \pmod 4, \qquad \mathcal{O}_K = \mathbb{Z}\left[\tfrac{1 + \sqrt d}{2}\right] \ \text{ if } d \equiv 1 \pmod 4,$$
and $d_K = 4d$ or $d_K = d$ in the two cases.

*Proof.* Let $\alpha = x + y\sqrt d$ with $x, y \in \mathbb{Q}$ and $y \ne 0$. Its minimal polynomial over $\mathbb{Q}$ is $X^2 - 2xX + (x^2 - dy^2)$. An element integral over $\mathbb{Z}$ has its minimal polynomial over $\mathbb{Q}$ in $\mathbb{Z}[X]$. This is a form of Gauss's lemma, cited here; Mathlib has it as `minpoly.isIntegrallyClosed_eq_field_fractions'`. So $\alpha \in \mathcal{O}_K$ if and only if $2x \in \mathbb{Z}$ and $x^2 - dy^2 \in \mathbb{Z}$. For $y = 0$ the condition is $x \in \mathbb{Z}$, which is the same condition with $b = 0$ below.

Write $a = 2x \in \mathbb{Z}$. Then $4(x^2 - dy^2) = a^2 - d(2y)^2 \in 4\mathbb{Z}$, so $d(2y)^2 \in \mathbb{Z}$. If $2y = u/v$ in lowest terms, $v^2 \mid du^2$ gives $v^2 \mid d$, and $v = 1$ since $d$ is squarefree. So $b = 2y \in \mathbb{Z}$, and the condition is $a^2 \equiv db^2 \pmod 4$.

The squares modulo $4$ are $0$ and $1$. If $d \equiv 2$ or $3 \pmod 4$, the only solutions are $a \equiv b \equiv 0 \pmod 2$: for $b$ odd, $db^2 \equiv d \in \{2, 3\}$ is not a square. So $x, y \in \mathbb{Z}$. If $d \equiv 1 \pmod 4$, the condition is $a \equiv b \pmod 2$, and $\alpha = \frac{a - b}{2} + b\cdot\frac{1 + \sqrt d}{2}$ with $\frac{a-b}{2} \in \mathbb{Z}$.

For the discriminant, the embeddings send $\sqrt d$ to $\pm\sqrt d$. With the basis $1, \sqrt d$, the matrix $\begin{pmatrix}1 & \sqrt d\\ 1 & -\sqrt d\end{pmatrix}$ has determinant $-2\sqrt d$, with square $4d$. With $1, \frac{1 + \sqrt d}{2}$, the determinant is $-\sqrt d$, with square $d$. $\square$

::: mathlib
`QuadraticAlgebra.Int.isIntegralClosure_iff` · `Mathlib.Algebra.QuadraticAlgebra.Int`

Mathlib works with `QuadraticAlgebra ℤ a b`, the ring $\mathbb{Z}[\omega]$ with $\omega^2 = a + b\omega$. The theorem says that $\mathbb{Z}[\omega]$ is the integral closure of $\mathbb{Z}$ in $\mathbb{Q}(\omega)$ if and only if its discriminant $b^2 + 4a$ is a fundamental discriminant. This is the theorem above in another form. The index of this edition has no declaration that identifies `𝓞 K` for a quadratic field `K` given as an abstract number field.

<?decl QuadraticAlgebra.Int.isIntegralClosure_iff?>
:::

**Proposition (Units and the norm).** An element $\alpha \in \mathcal{O}_K$ is a unit if and only if $N(\alpha) = \pm1$.

*Proof.* If $\alpha\beta = 1$ in $\mathcal{O}_K$, then $N(\alpha)N(\beta) = 1$ with both factors in $\mathbb{Z}$, so $N(\alpha) = \pm1$. Conversely, let $f(X) = X^m + c_{m-1}X^{m-1} + \cdots + c_0$ be the minimal polynomial of $\alpha$, with $c_i \in \mathbb{Z}$. Then $N(\alpha) = \pm c_0^{n/m}$, so $c_0 = \pm1$. From $f(\alpha) = 0$, $\alpha\cdot(\alpha^{m-1} + c_{m-1}\alpha^{m-2} + \cdots + c_1) = -c_0 = \mp1$, and the second factor is in $\mathcal{O}_K$. $\square$

::: mathlib
`NumberField.RingOfIntegers.isUnit_norm` · `Mathlib.NumberTheory.NumberField.Norm`

`IsUnit (norm K x) ↔ IsUnit x` for `x : 𝓞 F` and `F / K` finite. Over `ℚ`, the version with `|N x| = 1` is in Section 2.

<?decl NumberField.RingOfIntegers.isUnit_norm?>
:::

**Theorem (Minkowski and Hermite, cited).** If $[K : \mathbb{Q}] = n > 1$, then $|d_K| \ge \frac49\left(\frac{3\pi}{4}\right)^n > 2$; in particular $\mathbb{Q}$ has no unramified extension. For each $N$ there are only finitely many number fields in $\mathbb{C}$ with $|d_K| \le N$.

The proofs use Minkowski's theorem on convex bodies in the space $\mathbb{R}^{r_1} \times \mathbb{C}^{r_2}$. They are not given here.

::: mathlib
`NumberField.abs_discr_ge`, `NumberField.finite_of_discr_bdd` · `Mathlib.NumberTheory.NumberField.Discriminant.Basic`

`abs_discr_ge : 1 < finrank ℚ K → 4 / 9 * (3 * π / 4) ^ finrank ℚ K ≤ |discr K|`, with the corollary `abs_discr_gt_two`. The theorem of Hermite is `finite_of_discr_bdd`, stated for subfields of a field `A` of characteristic $0$.

<?decl NumberField.abs_discr_ge?>
<?decl NumberField.finite_of_discr_bdd?>
:::

### Examples

**Example (The Gaussian integers).** For $d = -1 \equiv 3 \pmod 4$, $\mathcal{O}_K = \mathbb{Z}[i]$ and $d_K = -4$. The norm $a^2 + b^2$ is the one of Volume 6, Chapter 6, and the units are the four elements of norm $1$: $\pm1, \pm i$.

**Example (The golden ratio).** For $d = 5 \equiv 1 \pmod 4$, $\mathcal{O}_K = \mathbb{Z}[\varphi]$ with $\varphi = \frac{1 + \sqrt5}{2}$, a root of $X^2 - X - 1$, and $d_K = 5$. The element $\varphi$ has norm $\frac{1 - 5}{4} = -1$, so it is a unit, with inverse $\varphi - 1$.

**Example (Eisenstein integers).** For $d = -3 \equiv 1 \pmod 4$, $\mathcal{O}_K = \mathbb{Z}[\omega]$ with $\omega = \frac{-1 + \sqrt{-3}}{2}$ a primitive cube root of unity, and $d_K = -3$. This ring is used in the proof of Fermat's last theorem for $n = 3$ (Chapter 4).

**Counterexample (A ring that is too small).** For $d = 5$, the ring $\mathbb{Z}[\sqrt5]$ is not integrally closed: $\varphi$ is integral but not in $\mathbb{Z}[\sqrt5]$. The ring $\mathbb{Z}[\sqrt5]$ has discriminant $20 = 2^2 \cdot 5$, and the index $[\mathbb{Z}[\varphi] : \mathbb{Z}[\sqrt5]] = 2$ is the square root of $20/5$.

### The library around it

The cyclotomic fields have their own files: `Mathlib.NumberTheory.NumberField.Cyclotomic.Basic` proves that $\mathcal{O}_K = \mathbb{Z}[\zeta_{p^k}]$ for $K = \mathbb{Q}(\zeta_{p^k})$, and computes the discriminant, for example `IsCyclotomicExtension.Rat.discr_prime`: $d_K = (-1)^{(p-1)/2}p^{p-2}$ for $K = \mathbb{Q}(\zeta_p)$. The general theory of Dedekind domains and of the ideal norm `Ideal.absNorm` is in `Mathlib.RingTheory`.

Common errors of a learner:

- `𝓞 K` is a separate type. To use an element `x : 𝓞 K` in `K`, write `(x : K)`, which is `algebraMap (𝓞 K) K x`.
- `NumberField.discr K` is an integer that depends on `K` only; `Algebra.discr ℤ b` depends on the family `b`, and is the discriminant of the field only when `b` is a basis of `𝓞 K`.
- `Algebra.norm ℚ` lands in `ℚ`, and `RingOfIntegers.norm ℚ` lands in `𝓞 ℚ`. Use `Rat.ringOfIntegersEquiv` to pass to `ℤ`.

### Exercises

1. (A) Find the ring of integers and the discriminant of $\mathbb{Q}(\sqrt{-5})$, $\mathbb{Q}(\sqrt{-7})$ and $\mathbb{Q}(\sqrt{12})$.
2. (A) Show that $1 + \sqrt2$ is a unit of $\mathbb{Z}[\sqrt2]$ and find its inverse.
3. (A) Show that $\frac{1 + \sqrt{-7}}{2}$ is integral, and find its minimal polynomial.
4. (B) Show that for $d < 0$ squarefree the units of $\mathcal{O}_K$, $K = \mathbb{Q}(\sqrt d)$, are $\pm1$, except for $d = -1$ (four units) and $d = -3$ (six units).
5. (B) Show that $\mathbb{Z}[\sqrt{-3}]$ is not a UFD: $4 = 2 \cdot 2 = (1 + \sqrt{-3})(1 - \sqrt{-3})$. Explain why this does not contradict unique factorization in $\mathbb{Z}[\omega]$.
6. (B) Show that $\mathcal{O}_K \cap \mathbb{Q} = \mathbb{Z}$ for every number field $K$.
7. (C) Let $K$ be a number field of degree $n$ and $\alpha \in \mathcal{O}_K$ with $K = \mathbb{Q}(\alpha)$. Show that $\operatorname{disc}(1, \alpha, \dots, \alpha^{n-1}) = [\mathcal{O}_K : \mathbb{Z}[\alpha]]^2\,d_K$.

### Notes and history

Gauss studied $\mathbb{Z}[i]$ and binary quadratic forms. Kummer worked with the cyclotomic integers in the 1840s and introduced ideal numbers to restore unique factorization. Dedekind gave the definition of the ring of integers and of ideals in his supplements to Dirichlet's lectures from 1871 on. Minkowski proved the lower bound for the discriminant in 1891, and Hermite proved the finiteness for bounded discriminant. A reference is Marcus, *Number Fields*, Chapters 2 and 5, and Neukirch, *Algebraic Number Theory*, Chapter I.

### Reference

<?reference?>
