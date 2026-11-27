---
title: Products and logarithms
kind: theory
modules:
  - Mathlib.Topology.Algebra.Support
explains:
  E3: [HasProd.norm, Multipliable.norm_tprod, HasProdUniformlyOn]
  E2: [Multipliable.norm, Topology.IsInducing.hasProd_iff, Topology.IsClosedEmbedding.map_tprod, Multipliable.hasFiniteMulSupport_of_discreteTopology, MultipliableUniformlyOn, HasProdLocallyUniformlyOn, MultipliableLocallyUniformlyOn, hasProdUniformlyOn_iff_tendstoUniformlyOn, HasProd.tprod_fiberwise]
  E1: auto
families: []
requires: [V13, V14.C04, V14.C05, V15]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Products and logarithms

### Overview

The exponential turns sums into products, $e^{a + b} = e^a e^b$, and the logarithm turns positive products into sums. Since both maps are continuous, they carry infinite sums to infinite products and back. This section uses them to prove the main convergence test for products: if $\sum a_i$ is summable in $\mathbb{R}$, then $\prod (1 + a_i)$ is multipliable. It then treats norms of products, products of functions that converge uniformly, and three classical products from the library: the Euler product of the zeta function, the product formula of the sine and the product of Wallis.

### Definitions

A *continuous monoid homomorphism* $\varphi : M \to N$ between commutative topological monoids is a continuous map with $\varphi(1) = 1$ and $\varphi(xy) = \varphi(x)\varphi(y)$. The exponential is a continuous homomorphism from the additive group $\mathbb{R}$ to the multiplicative monoid $\mathbb{R}$, with image the group $(0, \infty)$. The real logarithm is its inverse on $(0, \infty)$. On a normed commutative ring with $\|xy\| = \|x\| \|y\|$ and $\|1\| = 1$, such as $\mathbb{R}$, $\mathbb{C}$ and $\mathbb{Q}_p$, the norm is a continuous monoid homomorphism to $(\mathbb{R}, \cdot)$.

Let $f : I \to (X \to M)$ be a family of functions with values in a commutative monoid $M$ with a uniform structure, $g : X \to M$ and $s \subseteq X$. Then $f$ *has the product $g$ uniformly on $s$* when the finite products $\prod_{i \in F} f_i$ tend to $g$ uniformly on $s$ along $\mathrm{atTop}$.

::: mathlib
`HasProdUniformlyOn` · `Mathlib.Topology.Algebra.InfiniteSum.UniformOn`

The definition `HasProdUniformlyOn f g s`, the multiplicative twin of `HasSumUniformlyOn` of Section 5.2. The lemma `hasProdUniformlyOn_iff_tendstoUniformlyOn` unfolds it. The module also defines `MultipliableUniformlyOn` and the local forms `HasProdLocallyUniformlyOn` and `MultipliableLocallyUniformlyOn`.

<?decl HasProdUniformlyOn?>
:::

### Theorems and proofs

**Theorem (Images of products).** Let $\varphi : M \to N$ be a continuous monoid homomorphism and $f : I \to M$ with the product $a$. Then $\varphi \circ f$ has the product $\varphi(a)$. In particular, if $f : I \to \mathbb{R}$ has the sum $a$, then $e^{f}$ has the product $e^a$.

*Proof.* For a finite $F$, $\prod_{i \in F} \varphi(f_i) = \varphi(P_F)$ since $\varphi$ is a homomorphism. The net $P_F$ tends to $a$, and $\varphi$ is continuous, so $\varphi(P_F) \to \varphi(a)$. The exponential is a homomorphism from sums to products, and the same argument gives $\prod_{i \in F} e^{f_i} = e^{S_F} \to e^a$. $\square$

::: mathlib
`HasSum.rexp` · `Mathlib.Analysis.SpecialFunctions.Exp`

The statement `HasSum f a → HasProd (Real.exp ∘ f) (Real.exp a)`. For a homomorphism that is an embedding, `Topology.IsInducing.hasProd_iff` gives an equivalence, and `Topology.IsClosedEmbedding.map_tprod` commutes the homomorphism with `tprod` with no hypothesis of multipliability.

<?decl HasSum.rexp?>
:::

**Theorem (Products of positive reals).** Let $f : I \to \mathbb{R}$ with $f_i > 0$ for every $i$. If $i \mapsto \log f_i$ is summable, then $f$ is multipliable and $\prod' f = \exp(\sum' \log f_i) > 0$. Conversely, if $f$ has a product $p > 0$, then $\log f$ is summable with the sum $\log p$.

*Proof.* Since $f_i = \exp(\log f_i)$, the previous theorem applied to the family $\log f$ gives the first claim, and $\exp$ takes only positive values. For the converse, the finite products $P_F$ tend to $p > 0$, and $\log$ is continuous at $p$. Since $\log P_F = S_F(\log f)$ for every $F$, the finite sums of $\log f$ tend to $\log p$. $\square$

The converse needs $p > 0$. The product $\prod_{n \ge 2} (1 - 1/n)$ of Section 1 has the value $0$, and $\sum \log(1 - 1/n) = \lim_N \log(1/N)$ diverges to $-\infty$.

::: mathlib
`Real.rexp_tsum_eq_tprod` · `Mathlib.Analysis.SpecialFunctions.Log.Summable`

The statement takes `∀ i, 0 < f i` and `Summable fun i ↦ Real.log (f i)`, and concludes `Real.exp (∑' i, Real.log (f i)) = ∏' i, f i`. The multipliability is `Real.multipliable_of_summable_log`. The complex form `Complex.cexp_tsum_eq_tprod` takes `∀ i, f i ≠ 0` in place of positivity.

<?decl Real.rexp_tsum_eq_tprod?>
<?decl Real.multipliable_of_summable_log?>
<?decl Complex.cexp_tsum_eq_tprod?>
:::

**Theorem (The test of 1 + a).** Let $a : I \to \mathbb{R}$ be summable. Then $i \mapsto 1 + a_i$ is multipliable. If also $a_i \ne -1$ for every $i$, then $\prod' (1 + a_i) \ne 0$.

*Proof.* The terms tend to $0$ along the cofinite filter, so the set $E = \{i : |a_i| > 1/2\}$ is finite. On $[-1/2, 1/2]$ the inequality $|\log(1 + x)| \le 2|x|$ holds: $\log(1 + x) = \int_0^x \frac{dt}{1 + t}$, and $\frac{1}{1 + t} \le 2$ for $t \ge -1/2$. The family $|a|$ is summable by Section 5.2, so $|\log(1 + a_i)| \le 2 |a_i|$ for $i \notin E$ gives that $\log(1 + a)$ is summable on $I \setminus E$, by the comparison test of Section 5.1 and Section 5.2. By the previous theorem, the restriction of $1 + a$ to $I \setminus E$ has a product $q > 0$.

Now let $b = \prod_{i \in E} (1 + a_i)$, a finite product. For a finite $F \supseteq E$, $P_F = b \cdot P_{F \setminus E}$. As $F$ grows, $F \setminus E$ runs through the finite subsets of $I \setminus E$ along their filter $\mathrm{atTop}$, so $P_{F \setminus E} \to q$ and $P_F \to bq$ by continuity of multiplication. So $1 + a$ has the product $bq$. If no $a_i$ equals $-1$, then $b \ne 0$, and $bq \ne 0$. $\square$

::: mathlib
`Real.multipliable_one_add_of_summable` · `Mathlib.Analysis.SpecialFunctions.Log.Summable`

The statement `Summable f → Multipliable fun i ↦ 1 + f i`, with no other hypothesis. The step on logarithms is `Real.summable_log_one_add_of_summable`, and the complex form is `Complex.summable_log_one_add_of_summable`. The general expansion `multipliable_one_add_of_summable_prod` of Section 1 works in any commutative topological semiring.

<?decl Real.multipliable_one_add_of_summable?>
<?decl Real.summable_log_one_add_of_summable?>
:::

**Theorem (Norms of products).** Let $E$ be a seminormed commutative ring with $\|xy\| = \|x\| \|y\|$ and $\|1\| = 1$, and let $f : I \to E$ have the product $x$. Then $\|f\|$ has the product $\|x\|$, and $\|\prod' f\| = \prod' \|f_i\|$ when $f$ is multipliable.

*Proof.* Under the hypotheses the norm is a continuous monoid homomorphism from $(E, \cdot)$ to $(\mathbb{R}, \cdot)$. The theorem on images gives the first claim, and the formula follows by uniqueness of products in $\mathbb{R}$. $\square$

::: mathlib
`HasProd.norm` · `Mathlib.Topology.Algebra.InfiniteSum.Field`

The classes `SeminormedCommRing E`, `NormMulClass E` and `NormOneClass E`. The other forms are `Multipliable.norm` and `Multipliable.norm_tprod`. A complex product has the absolute value $\prod' |f_i|$ by this lemma.

<?decl HasProd.norm?>
<?decl Multipliable.norm_tprod?>
:::

**Theorem (Uniform products of continuous functions).** Let $X$ be a topological space, $M$ a commutative monoid with a uniform structure and continuous multiplication, and $f$ a family of continuous functions $X \to M$ with the product $g$ uniformly on $X$. Then $g$ is continuous.

*Proof.* Each finite product $\prod_{i \in F} f_i$ is continuous, and they tend to $g$ uniformly along a filter that is not trivial. A uniform limit of continuous functions is continuous, by Volume 13. $\square$

For holomorphic factors the library goes further: a product of holomorphic functions that converges locally uniformly can be differentiated through its logarithmic derivative, `logDeriv_tprod_eq_tsum` in `Mathlib.Analysis.Calculus.LogDerivUniformlyOn`.

### Examples

**Example (The Euler product).** For $s \in \mathbb{C}$ with $\operatorname{Re} s > 1$,
$$\zeta(s) = \sum_{n \ge 1} n^{-s} = \prod_{p \text{ prime}} \frac{1}{1 - p^{-s}} .$$
The proof expands each factor as a geometric series $\sum_e p^{-es}$ and uses unique factorization: the finite product over the primes in a finite set $F$ is the sum of $n^{-s}$ over the integers $n$ whose prime factors lie in $F$. The absolute summability of $\sum n^{-s}$ makes these sums tend to $\zeta(s)$.

::: mathlib
`riemannZeta_eulerProduct_hasProd` · `Mathlib.NumberTheory.EulerProduct.DirichletLSeries`

The statement `1 < s.re → HasProd (fun p : Nat.Primes ↦ (1 - (p : ℂ) ^ (-s))⁻¹) (riemannZeta s)`. The general form `EulerProduct.eulerProduct_hasProd` holds for any multiplicative function with summable norms in a complete normed commutative ring.

<?decl riemannZeta_eulerProduct_hasProd?>
<?decl EulerProduct.eulerProduct_hasProd?>
:::

**Example (The sine product and the product of Wallis).** For every real $x$,
$$\sin(\pi x) = \pi x \prod_{j \ge 1} \Bigl(1 - \frac{x^2}{j^2}\Bigr).$$
The family $x^2/j^2$ is summable, so the product is multipliable by the test of $1 + a$. At $x = 1/2$ the formula gives $\frac{2}{\pi} = \prod_{j \ge 1} \frac{(2j-1)(2j+1)}{(2j)^2}$, the product of Wallis.

::: mathlib
`Real.tendsto_euler_sin_prod` · `Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd`

The statement is the limit of the partial products, `Tendsto (fun n ↦ π * x * ∏ j ∈ Finset.range n, (1 - x ^ 2 / (j + 1) ^ 2)) atTop (𝓝 (sin (π * x)))`. The product of Wallis is `Real.tendsto_prod_pi_div_two` in `Mathlib.Analysis.Real.Pi.Wallis`, as the limit $\pi/2$ of the partial products of the reciprocal factors $\frac{(2i+2)^2}{(2i+1)(2i+3)}$.

<?decl Real.tendsto_euler_sin_prod?>
<?decl Real.tendsto_prod_pi_div_two?>
:::

**Example (A counterexample: conditional convergence is not enough).** Let $a_n = (-1)^n / \sqrt n$ for $n \ge 2$. The partial sums of $\sum a_n$ converge, by the alternating series test, but $a$ is not summable in Mathlib. The product $\prod (1 + a_n)$ diverges to $0$ in the classical sense. Indeed $\log(1 + x) = x - x^2/2 + r(x)$ with $|r(x)| \le |x|^3$ for $|x| \le 1/2$, and $a_n^2 = 1/n$. So the partial sums of $\log(1 + a_n)$ are a convergent sum, minus half the harmonic sum, plus a summable error, and they tend to $-\infty$. The test of $1 + a$ needs summability, which is absolute summability in $\mathbb{R}$.

**Remark (Common errors).** The test of $1 + a$ gives `Multipliable`, and in Mathlib this does not say that the product is nonzero. A factor $1 + a_i = 0$ gives the product $0$. A proof that divides by the product must also show $a_i \ne -1$ for all $i$, and use the positive form $\prod' f = \exp(\sum' \log f_i)$ when $f > 0$. A second error is to use the partial products of `Real.tendsto_euler_sin_prod` as a `tprod`: the statement is a limit along $\mathbb{N}$, and the unconditional product needs the test above as a separate step.

### The library around it

The links between products and logarithms live outside this volume, in `Mathlib.Analysis.SpecialFunctions.Log.Summable` for $\mathbb{R}$ and $\mathbb{C}$ and in `Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn` for uniform products of complex functions. Inside the volume, `Mathlib.Topology.Algebra.InfiniteSum.Field` gives the norm of a product, `Mathlib.Topology.Algebra.InfiniteSum.UniformOn` the uniform products, and `Mathlib.Topology.Algebra.InfiniteSum.Constructions` the regrouping of a product along the fibres of a map, `HasProd.tprod_fiberwise`. A multipliable family in a discrete group has only finitely many factors different from $1$ (`Multipliable.hasFiniteMulSupport_of_discreteTopology`). The module `Mathlib.Topology.Algebra.Support` defines the topological support `mulTSupport` of a function, the closure of the set where it differs from $1$, and the property `HasCompactMulSupport`. Its additive forms are `tsupport` and `HasCompactSupport`.

### Exercises

1. (A) Show that $\prod_{n \ge 1} (1 + 2^{-n})$ is multipliable and lies between $1$ and $e$.
2. (A) Let $f : I \to \mathbb{C}$ be multipliable. Show that $|\prod' f| = \prod' |f_i|$.
3. (A) Show that $\prod_{n \ge 1} e^{1/n^2} = e^{\pi^2/6}$.
4. (B) Show that $\prod_{n \ge 2} \bigl(1 + \frac{(-1)^n}{n}\bigr)$ has partial products that converge to a nonzero limit, and that the family $(-1)^n / n$ is not summable. Explain why the test of $1 + a$ does not apply, and decide whether the family $1 + (-1)^n/n$ is multipliable in Mathlib. *Hint:* pair the factors $n = 2k$ and $n = 2k + 1$.
5. (B) Show that for $0 < x < 1$ the product $\prod_{n \ge 1} (1 - x^n)$ is multipliable and positive.
6. (B) Derive the product of Wallis from the sine product at $x = 1/2$.
7. (C) Let $a : I \to \mathbb{C}$ be summable with $a_i \ne -1$ for every $i$. Show that $\prod' (1 + a_i) \ne 0$. *Hint:* follow the real proof with the complex logarithm on the disc $|z| \le 1/2$, and `Complex.cexp_tsum_eq_tprod`.

### Notes and history

Euler found the product formula for the sine and the product of the zeta function over the primes in the eighteenth century, and Wallis found his product for $\pi$ in the seventeenth. The criterion that $\prod (1 + a_n)$ converges absolutely when $\sum |a_n|$ converges is a standard part of the theory of entire functions, where Weierstrass used it to build functions with prescribed zeros. In Mathlib the criterion appears with the unconditional definition, in which absolute and unconditional convergence agree for real and complex families.

### Reference

<?reference?>
