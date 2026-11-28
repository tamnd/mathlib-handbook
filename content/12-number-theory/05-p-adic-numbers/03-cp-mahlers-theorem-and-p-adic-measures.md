---
title: The field C_p, Mahler's theorem and p-adic measures
kind: api
modules:
  - Mathlib.NumberTheory.Padics.ProperSpace
  - Mathlib.NumberTheory.Padics.LocalField
  - Mathlib.NumberTheory.LocalField.Basic
  - Mathlib.NumberTheory.Padics.ValuativeRel
  - Mathlib.NumberTheory.Padics.WithVal
  - Mathlib.NumberTheory.Padics.Complex
  - Mathlib.NumberTheory.Padics.MahlerBasis
  - Mathlib.NumberTheory.Padics.AddChar
  - Mathlib.NumberTheory.Padics.Measure.Basic
  - Mathlib.NumberTheory.Padics.Measure.Topology
  - Mathlib.NumberTheory.Padics.Measure.Monoid
  - Mathlib.NumberTheory.Padics.Measure.AmiceTransform
explains:
  E2: [PadicInt.compactSpace, Padic.instProperSpace, PadicComplex.isAlgClosed, mahler_natCast_eq, PadicInt.hasSum_mahler, PadicInt.ext_mahler, PadicInt.continuousAddCharEquiv, AbstractMeasure.dirac_mul_dirac, AbstractMeasure.coeff_amiceTransform]
  E1: auto
families: []
requires: [V12.C01, V13.C03, V14.C08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The field C_p, Mahler's theorem and p-adic measures

### Overview

Sections 1 and 2 built $\mathbb{Q}_p$ and $\mathbb{Z}_p$ and proved Hensel's lemma. This section goes on to the analysis over these fields. It has three parts. The first part gives the topology of $\mathbb{Z}_p$ and $\mathbb{Q}_p$ (compact and locally compact), connects $\mathbb{Q}_p$ with the general theory of valued fields, and builds the field $\mathbb{C}_p$, the completion of an algebraic closure of $\mathbb{Q}_p$. The second part proves Mahler's theorem: each continuous function $f : \mathbb{Z}_p \to \mathbb{Q}_p$ is a uniformly convergent series $\sum_n a_n\binom{x}{n}$ with $a_n \to 0$. The third part defines $p$-adic measures as continuous linear functionals on continuous functions, makes them into a ring by convolution, and identifies the measures on $\mathbb{Z}_p$ with the power series ring $\mathbb{Z}_p[[X]]$ by the Amice transform.

These are the first objects of $p$-adic analysis and of Iwasawa theory. The section needs the normed spaces of Volume 16 and the valued fields of Volume 14, Chapter 8.

### The library around it

#### Compactness and local fields

**Theorem.** $\mathbb{Z}_p$ is compact, and $\mathbb{Q}_p$ is a proper metric space: each closed ball is compact. In Lean these are the instances `PadicInt.compactSpace` and `Padic.instProperSpace`, with the lemma `PadicInt.totallyBounded_univ`.

*Proof.* Let $n \ge 0$. Each $x \in \mathbb{Z}_p$ is congruent modulo $p^n$ to an integer $a \in \{0, \dots, p^n - 1\}$ (Section 2), so $\|x - a\| \le p^{-n}$. So finitely many balls of radius $p^{-n}$ cover $\mathbb{Z}_p$, and $\mathbb{Z}_p$ is totally bounded. It is closed in the complete space $\mathbb{Q}_p$, so it is complete, and a complete totally bounded metric space is compact. The closed ball of radius $p^k$ about $c$ in $\mathbb{Q}_p$ is $c + p^{-k}\mathbb{Z}_p$, the image of $\mathbb{Z}_p$ by a continuous map, so it is compact. The radii between two powers of $p$ give the same balls, because the norm takes only the values $p^k$ and $0$. $\square$

With compactness, $\mathbb{Q}_p$ is a nonarchimedean local field: the instance `instIsNonarchimedeanLocalFieldPadic` gives `IsNonarchimedeanLocalField ℚ_[p]`, so the general theory of local fields applies to it.

That general theory starts in `Mathlib.NumberTheory.LocalField.Basic`. The class `IsNonarchimedeanLocalField K` asks for a field with a `ValuativeRel` whose topology is the valuative one, which is locally compact and not trivial. From these axioms the module derives the usual structure as instances: $K$ is complete, the valuation ring is compact and a discrete valuation ring with finite residue field, and it is complete for the topology of its maximal ideal. The value group is cyclic, and `IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt` is an order isomorphism of the value group with zero onto `WithZero (Multiplicative ℤ)`. Each closed ball $\{x \mid v(x) \le \gamma\}$ is compact by `IsNonarchimedeanLocalField.isCompact_closedBall`, which for `ℚ_[p]` gives back the proper space of the theorem above.

The module `Mathlib.NumberTheory.Padics.ValuativeRel` puts on `ℚ_[p]` the structure `ValuativeRel` of Volume 14, Chapter 8, by the instance `Padic.instValuativeRel`. The instances `Padic.instIsValuativeTopology`, `Padic.instIsRankLeOne` and `Padic.instIsNontrivial` say that the topology is the valuative one, of rank at most one and not trivial. The $\mathbb{Z}$-valued valuation `Padic.mulValuation` is compatible with it (`Padic.instCompatibleWithZeroMultiplicativeIntMulValuation`). For each compatible valuation `v`, `Padic.valuation_p_lt_one` says $v(p) < 1$ and `Padic.valuation_p_ne_zero` says $v(p) \ne 0$.

The module `Mathlib.NumberTheory.Padics.WithVal` compares two constructions of $\mathbb{Q}_p$. Section 1 built `ℚ_[p]` from Cauchy sequences for the $p$-adic norm. The general theory completes `WithVal (Rat.padicValuation p)`, the rationals with the $p$-adic valuation, as a uniform space. The ring isomorphism `Padic.withValRingEquiv` and the uniform isomorphism `Padic.withValUniformEquiv` identify the two completions, and `PadicInt.withValIntegersRingEquiv` and `PadicInt.withValIntegersUniformEquiv` identify the valuation ring of the completion with `ℤ_[p]`. The comparison of the two tests for integers is `Padic.norm_rat_le_one_iff_padicValuation_le_one`: for $x \in \mathbb{Q}$, $\|x\| \le 1$ if and only if `Rat.padicValuation p x ≤ 1`. The proof uses `Padic.isDenseInducing_cast_withVal`: the map from $\mathbb{Q}$ with the valuation to `ℚ_[p]` is a dense uniform embedding.

#### The field C_p

The algebraic closure `PadicAlgCl p` of $\mathbb{Q}_p$ is an abbreviation of `AlgebraicClosure ℚ_[p]`. Since $\mathbb{Q}_p$ is complete, its norm has exactly one extension to each finite extension, and so to the algebraic closure. Mathlib takes the spectral norm: `PadicAlgCl.spectralNorm_eq` says that the norm of `PadicAlgCl p` is `spectralNorm ℚ_[p] (PadicAlgCl p)`. The instances make it a `NontriviallyNormedField` and a `NormedAlgebra` over `ℚ_[p]`, with `PadicAlgCl.norm_extends` ($\|x\|$ is the same in $\mathbb{Q}_p$ and in the closure), `PadicAlgCl.isNonarchimedean` and `PadicAlgCl.valuation_p` ($v(p) = 1/p$).

The field `PadicAlgCl p` is not complete. Its completion is `PadicComplex p`, an abbreviation of `UniformSpace.Completion (PadicAlgCl p)`, with the notation `ℂ_[p]`. Its valuation ring is `PadicComplexInt p`, a `ValuationSubring ℂ_[p]` with the notation `𝓞_ℂ_[p]`, and `PadicComplexInt.integers` says that it is the ring of integers of the valuation.

**Theorem (cited).** $\mathbb{C}_p$ is algebraically closed (`PadicComplex.isAlgClosed`).

The proof uses Krasner's lemma: a root of a polynomial over $\mathbb{C}_p$ is the limit of roots of nearby polynomials over the algebraic closure, and a complete field whose dense subfield is algebraically closed is algebraically closed. The proof is not given here.

The norm of $\mathbb{C}_p$ extends the norm of the closure and of $\mathbb{Q}_p$: `PadicComplex.norm_extends`, `PadicComplex.norm_extends'`, and the forms for `‖·‖₊` named `PadicComplex.nnNorm_extends` and `PadicComplex.nnNorm_extends'`. The norm is the norm of the valuation (`PadicComplex.norm_eq_norm`), the field is ultrametric (`PadicComplex.isUltrametricDist`), and `PadicComplex.valuation_p` gives $v(p) = 1/p$.

#### Binomial functions and the Mahler basis

The ring `ℤ_[p]` is a binomial ring (`PadicInt.instBinomialRing`): for $x \in \mathbb{Z}_p$ the binomial coefficient $\binom{x}{k} = x(x - 1)\cdots(x - k + 1)/k!$ is in $\mathbb{Z}_p$, and it is `Ring.choose x k`. The function $x \mapsto \binom{x}{k}$ is continuous (`PadicInt.continuous_choose`), and so is $x \mapsto \binom{x + k - 1}{k}$ (`PadicInt.continuous_multichoose`). The bound behind both is `PadicInt.norm_ascPochhammer_le`: $|x(x + 1)\cdots(x + k - 1)| \le |k!|$ on $\mathbb{Z}_p$.

The $k$-th Mahler function is `mahler k : C(ℤ_[p], ℤ_[p])`, with `mahler_apply : mahler k x = Ring.choose x k`.

**Proposition.** $\mathrm{mahler}_k(n) = \binom{n}{k}$ for $n \in \mathbb{N}$, and the sup norm of $\mathrm{mahler}_k$ is $1$. These are `mahler_natCast_eq` and `PadicInt.norm_mahler_eq`.

*Proof.* For $n \in \mathbb{N}$, the product $n(n - 1)\cdots(n - k + 1)/k!$ is the integer $\binom{n}{k}$. Its norm is at most $1$, and $\mathbb{N}$ is dense in $\mathbb{Z}_p$, so the continuous function has norm at most $1$ on $\mathbb{Z}_p$. At $x = k$ the value is $\binom{k}{k} = 1$, so the norm is $1$. $\square$

The forward difference is $\Delta f(x) = f(x + 1) - f(x)$, which is `fwdDiff 1 f` from the theory of finite differences. Its powers satisfy $\Delta^n f(0) = \sum_{j=0}^n (-1)^{n-j}\binom{n}{j}f(j)$, and $\Delta\binom{x}{k} = \binom{x}{k-1}$.

**Theorem (Mahler).** Let $E$ be a complete ultrametric normed $\mathbb{Z}_p$-module and $f : \mathbb{Z}_p \to E$ continuous. Then $\Delta^n f(0) \to 0$, and
$$f(x) = \sum_{n \ge 0}\Delta^n f(0)\binom{x}{n},$$
with uniform convergence on $\mathbb{Z}_p$. Conversely, for each sequence $a_n \to 0$ in $E$, the series $\sum_n a_n\binom{x}{n}$ converges to a continuous function with $\Delta^n f(0) = a_n$.

In Lean, `PadicInt.mahlerTerm a n` is the function $x \mapsto \binom{x}{n}a$ in `C(ℤ_[p], E)`, and `PadicInt.mahlerSeries a` is the sum of these terms. The direct statement is `PadicInt.hasSum_mahler`, a `HasSum` in the Banach space `C(ℤ_[p], E)` with the sup norm, and `PadicInt.fwdDiff_tendsto_zero` says that the coefficients tend to $0$. The converse is `PadicInt.hasSum_mahlerSeries`, with `PadicInt.mahlerSeries_apply` for the values and `PadicInt.fwdDiff_mahlerSeries` for the coefficients. Together they give the linear isometry `PadicInt.mahlerEquiv E : C(ℤ_[p], E) ≃ₗᵢ[ℤ_[p]] ZeroAtInftyContinuousMap ℕ E`, which sends $f$ to the sequence $n \mapsto \Delta^n f(0)$ (`PadicInt.mahlerEquiv_apply`). The isometry says $\|f\|_\infty = \max_n |\Delta^n f(0)|$.

*About the proof.* Uniqueness of the coefficients follows from $\Delta\binom{x}{k} = \binom{x}{k-1}$, evaluated at $0$. The hard step is $\Delta^n f(0) \to 0$. The function $f$ is uniformly continuous, so $\|f(x) - f(y)\| \le \|f\|/p^s$ when $|x - y| \le p^{-t}$ for a suitable $t$. Then `PadicInt.fwdDiff_iter_le_of_forall_le` bounds $\|\Delta^{n + sp^t}f(0)\| \le \|f\|/p^s$ for all $n$. The proof uses that $\binom{p^t}{j}$ is divisible by $p$ for $0 < j < p^t$, so $\Delta^{p^t}$ is close to the difference $f(x + p^t) - f(x)$. The general bound `IsUltrametricDist.norm_fwdDiff_iter_apply_le` gives $\|\Delta^n f(m)\| \le \|f\|$. Once the coefficients tend to $0$, the series converges, and it agrees with $f$ on $\mathbb{N}$ by the Newton interpolation formula; by density it agrees on $\mathbb{Z}_p$.

**Corollary.** A continuous linear functional $\mu$ on $C(\mathbb{Z}_p, R)$ with $\mu(\mathrm{mahler}_n) = 0$ for all $n$ is zero (`PadicInt.ext_mahler`).

*Proof.* By Mahler's theorem the span of the functions $\mathrm{mahler}_n$ is dense (`PadicInt.dense_span_mahler`). The kernel of $\mu$ is closed and contains this span, so it is everything. $\square$

#### Continuous additive characters of Z_p

An additive character $\kappa : \mathbb{Z}_p \to R$ is a map with $\kappa(x + y) = \kappa(x)\kappa(y)$ and $\kappa(0) = 1$, the type `AddChar ℤ_[p] R`. For a complete ultrametric normed $\mathbb{Z}_p$-algebra $R$, the continuous ones are exactly the maps $x \mapsto (1 + r)^x$ with $r^n \to 0$.

**Theorem.** `PadicInt.continuousAddCharEquiv p R` is a bijection from the continuous additive characters to the elements $r$ of $R$ with $r^n \to 0$, and it sends $\kappa$ to $\kappa(1) - 1$ (`PadicInt.continuousAddCharEquiv_apply`). Its inverse sends $r$ to `PadicInt.addChar_of_value_at_one r hr`, the character with value $1 + r$ at $1$ (`PadicInt.addChar_of_value_at_one_def`).

*Proof.* Let $\kappa$ be continuous and $r = \kappa(1) - 1$. Then $\Delta\kappa(x) = \kappa(x + 1) - \kappa(x) = \kappa(x)r$, so $\Delta^n\kappa(0) = r^n$. By Mahler's theorem these coefficients tend to $0$; this is `AddChar.tendsto_eval_one_sub_pow`. Conversely, for $r^n \to 0$ the Mahler series $\sum_n r^n\binom{x}{n}$ is continuous, and on $m \in \mathbb{N}$ it is $(1 + r)^m$ by the binomial theorem. So it is additive on $\mathbb{N}$, and by density and continuity on $\mathbb{Z}_p$. A continuous character is determined by its values on the dense set $\mathbb{N}$, where $\kappa(m) = \kappa(1)^m$, so the two maps are inverse. $\square$

When the norm of $R$ is multiplicative, $r^n \to 0$ means $|r| < 1$, and `PadicInt.continuousAddCharEquiv_of_norm_mul` is the bijection with the open unit ball.

#### Abstract measures

For a topological space $X$, a topological ring $R$ and an $R$-module $E$, `AbstractMeasure X R E` is the type of continuous $R$-linear maps $C(X, R) \to E$. It is a type synonym of `C(X, R) →L[R] E`, and `AbstractMeasure.toCLMEquiv` is the identification. The synonym exists so that the type does not inherit the norm topology: the module `Mathlib.NumberTheory.Padics.Measure.Topology` defines the weak topology `AbstractMeasure.WeakTopology` and the strong topology `AbstractMeasure.StrongTopology` and makes neither of them an instance. The scoped notation `D(X, R)` stands for `AbstractMeasure X R R`. For $X = \mathbb{Z}_p$ and $R = \mathbb{Z}_p$, these are the $p$-adic measures on $\mathbb{Z}_p$.

A measure is applied to a function as a function is applied to a point, and `AbstractMeasure.ext` proves equality from equality on all functions. The constructions are these.

| Lean name | Statement |
|---|---|
| `AbstractMeasure.dirac` | the Dirac measure, with `AbstractMeasure.dirac_apply`: $\delta_x(f) = f(x)$ |
| `AbstractMeasure.map` | the image measure $(\phi_*\mu)(f) = \mu(f \circ \phi)$ for $\phi \in C(X, Y)$ |
| `AbstractMeasure.map_dirac` | $\phi_*\delta_x = \delta_{\phi(x)}$ |
| `AbstractMeasure.arrowCongrLeft` | the linear equivalence from a homeomorphism $X \simeq Y$ |
| `AbstractMeasure.contractFst` | $f \mapsto (y \mapsto \mu(x \mapsto f(x, y)))$ for $f \in C(X \times Y, R)$ |
| `AbstractMeasure.prodMk` | the product measure, integrating over $Y$ first |
| `AbstractMeasure.prodMk'` | the product measure, integrating over $X$ first |
| `AbstractMeasure.prodMk_eq_prodMk'` | the two agree for compact, Hausdorff, totally disconnected $X$ and $Y$ |

The last row is a Fubini theorem. Its hypotheses hold for $\mathbb{Z}_p$, where each continuous function on $\mathbb{Z}_p \times \mathbb{Z}_p$ is a uniform limit of finite sums $\sum g_i(x)h_i(y)$.

#### Convolution of measures

Let $G$ be a topological monoid. The module `Mathlib.NumberTheory.Padics.Measure.Monoid` defines `AbstractMeasure.convolveFunRight ν f` as the function $x \mapsto \nu(y \mapsto f(xy))$ (`AbstractMeasure.convolveFunRight_apply`) and the convolution $(\mu * \nu)(f) = \mu(x \mapsto \nu(y \mapsto f(xy)))$ (`AbstractMeasure.mul_apply`). For locally compact $G$ this makes `D(G, R)` a ring (`AbstractMeasure.instRing`) and an $R$-algebra, with unit $\delta_1$ (`AbstractMeasure.one_def`). For a commutative $G$ that is compact, Hausdorff and totally disconnected, the Fubini theorem gives commutativity (`AbstractMeasure.instCommRing`).

**Proposition.** $\delta_x * \delta_y = \delta_{xy}$ (`AbstractMeasure.dirac_mul_dirac`).

*Proof.* $(\delta_x * \delta_y)(f) = \delta_x(x' \mapsto \delta_y(y' \mapsto f(x'y'))) = \delta_x(x' \mapsto f(x'y)) = f(xy) = \delta_{xy}(f)$. $\square$

So $x \mapsto \delta_x$ is a monoid map `AbstractMeasure.diracHom`, and it extends to the algebra map `AbstractMeasure.monoidAlgebraHom : MonoidAlgebra R G →ₐ[R] D(G, R)` from the monoid algebra, with `AbstractMeasure.monoidAlgebraHom_single`. For $G = \mathbb{Z}_p$ the measures form a completion of the group algebra of $\mathbb{Z}$, the Iwasawa algebra.

#### The Amice transform

The Amice transform sends a measure $\mu$ on $\mathbb{Z}_p$ to the power series
$$\mathcal{A}_\mu(X) = \sum_{n \ge 0}\mu\!\left(\binom{x}{n}\right)X^n,$$
which is formally $\int (1 + X)^x\,d\mu(x)$. In Lean, `AbstractMeasure.amiceTransform` is the $R$-linear map from `AbstractMeasure ℤ_[p] R R` to `PowerSeries R`, and `AbstractMeasure.coeff_amiceTransform` says that its $n$-th coefficient is $\mu(\mathrm{mahler}_n)$.

**Proposition.** The Amice transform is injective, and over $\mathbb{Z}_p$ it is a linear equivalence $D(\mathbb{Z}_p, \mathbb{Z}_p) \cong \mathbb{Z}_p[[X]]$. These are `AbstractMeasure.injective_amiceTransform` and `AbstractMeasure.amiceTransformEquiv`.

*Proof.* If $\mathcal{A}_\mu = 0$, then $\mu(\mathrm{mahler}_n) = 0$ for all $n$, and $\mu = 0$ by `AbstractMeasure.ext_mahler`, the form of `PadicInt.ext_mahler` for measures. For surjectivity, let $F = \sum b_nX^n$ with $b_n \in \mathbb{Z}_p$. Put $\mu(f) = \sum_n a_n(f)b_n$, where $a_n(f) = \Delta^n f(0)$ are the Mahler coefficients of $f$. The series converges because $a_n(f) \to 0$ and $|b_n| \le 1$, and $|\mu(f)| \le \|f\|$ by the isometry of Mahler's theorem, so $\mu$ is continuous. On $f = \mathrm{mahler}_n$ the coefficients are $a_m = 1$ for $m = n$ and $0$ otherwise, so $\mu(\mathrm{mahler}_n) = b_n$. $\square$

The inverse is `AbstractMeasure.invTransform`, with `AbstractMeasure.invTransform_apply` for the formula of the proof and `AbstractMeasure.amiceTransform_invTransform`. For example, the Dirac measure $\delta_a$ has the coefficients $\binom{a}{n}$, so $\mathcal{A}_{\delta_a} = (1 + X)^a$.

The ring structure needs the multiplicative form, because the convolution of `D(G, R)` uses the multiplication of $G$. On `Multiplicative ℤ_[p]` the functions `AbstractMeasure.mulMahler n` are the Mahler functions, and `AbstractMeasure.mulMahler_mul` is the Vandermonde identity $\binom{x + y}{n} = \sum_{i + j = n}\binom{x}{i}\binom{y}{j}$. It says that the transform turns convolution into the product of power series: `AbstractMeasure.amiceTransformₐ` is an algebra map, with `AbstractMeasure.coeff_amiceTransformₐ`, and `AbstractMeasure.amiceTransformEquivₐ` is the algebra isomorphism of `AbstractMeasure (Multiplicative ℤ_[p]) ℤ_[p] ℤ_[p]` with `PowerSeries ℤ_[p]`. With $\delta_a * \delta_b = \delta_{a + b}$, the example above becomes $(1 + X)^a(1 + X)^b = (1 + X)^{a + b}$.

#### Common errors

1. `ℂ_[p]` is the completion of `PadicAlgCl p`, and a coercion goes from `PadicAlgCl p` to `ℂ_[p]`. An element of `ℚ_[p]` reaches `ℂ_[p]` in two steps, which is why the lemmas with a prime, such as `PadicComplex.norm_extends'`, contain `algebraMap ℚ_[p] (PadicAlgCl p)`.
2. `mahler n` is a continuous function to `ℤ_[p]`. To use it in `C(ℤ_[p], R)` for an algebra `R`, the statements write `mahler n • 1`, as in `PadicInt.ext_mahler` and `AbstractMeasure.coeff_amiceTransform`.
3. `AbstractMeasure X R E` has no topology instance. A statement about convergence of measures must choose `AbstractMeasure.WeakTopology` or `AbstractMeasure.StrongTopology` explicitly.

### Exercises

1. (A) Find the Mahler expansions of $x^2$ and $x^3$ on $\mathbb{Z}_p$, by computing $\Delta^n f(0)$.
2. (A) Show that $\|\binom{x}{n}\| = 1$ for each $n$, and that the unit ball of $\mathbb{Z}_p$ is not covered by fewer than $p^n$ balls of radius $p^{-n}$.
3. (B) Show that the characteristic function of $a + p\mathbb{Z}_p$ is continuous, and show that its Mahler coefficients tend to $0$ with a direct computation for $p = 2$.
4. (B) Compute the Amice transform of the measure $\mu(f) = f(1) - f(0)$, and of the convolution $\mu * \mu$.
5. (B) Let $r \in \mathbb{C}_p$ with $|r| < 1$. Show that the character $x \mapsto (1 + r)^x$ of `PadicInt.continuousAddCharEquiv_of_norm_mul` has finite order if and only if $1 + r$ is a root of unity of $p$-power order.
6. (C) Show that $\mathbb{C}_p$ is not locally compact, by showing that its residue field is infinite.

### Reference

<?reference?>
