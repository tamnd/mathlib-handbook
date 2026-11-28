---
title: Products and sequences with Lp norms
kind: api
modules:
  - Mathlib.Analysis.Normed.Lp.ProdLp
  - Mathlib.Analysis.Normed.Lp.Finsupp
  - Mathlib.Analysis.Normed.Lp.LpEquiv
  - Mathlib.Analysis.Normed.Lp.MeasurableSpace
  - Mathlib.Analysis.Normed.Lp.SmoothApprox
  - Mathlib.Analysis.Normed.Lp.lpHolder
explains:
  E2: [WithLp.prod_norm_eq_add, WithLp.prod_norm_eq_sup, WithLp.prod_lipschitzWith_toLp, lpPiLpₗᵢ, Memℓp.holder, lp.norm_dualPairing]
  E1: auto
families: []
requires: [V13, V15]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Products and sequences with Lp norms

### Overview

The section on normed fields and normed spaces introduced the type synonym `WithLp p V` and the space `PiLp p β` of finite families with the $\ell^p$ norm. The section on series introduced the space `lp E p` of sequences with finite $\ell^p$ norm. This section treats the files that complete these two constructions. The first file puts the $\ell^p$ norm on a product of two spaces. Other files give the $\ell^p$ distance on finitely supported functions, compare `lp` with `PiLp` and with bounded continuous functions, and give the inequality of Hölder for `lp`.

Two smaller files connect the construction with measure theory. One file gives `WithLp p X` the measurable structure of `X`. The other proves that smooth functions with compact support are dense in the space $L^p$ of a finite dimensional real space. The reader needs this section to use the $\ell^1$ or $\ell^2$ norm on $E \times F$, and to move between the different models of $\ell^p$.

### The library around it

**The $\ell^p$ norm on a product.** The product `E × F` has the sup norm $\max(\|x\|, \|y\|)$ as its instance. The file `Mathlib.Analysis.Normed.Lp.ProdLp` puts on the type synonym `WithLp p (E × F)` the norm
$$\|(x, y)\|_p = (\|x\|^p + \|y\|^p)^{1/p}$$
for $0 < p < \infty$, the sup norm for $p = \infty$, and the number of nonzero coordinates for $p = 0$. The projections are `WithLp.fst` and `WithLp.snd`, and the lemmas `WithLp.toLp_fst` and `WithLp.ofLp_fst` move them across `WithLp.toLp` and `WithLp.ofLp`. The table gives the formulas for the norm.

| Lean name | Statement |
|---|---|
| `WithLp.prod_norm_eq_add` | $\|f\| = (\|f_1\|^p + \|f_2\|^p)^{1/p}$ for $0 < p < \infty$ |
| `WithLp.prod_norm_eq_sup` | $\|f\| = \max(\|f_1\|, \|f_2\|)$ for $p = \infty$ |
| `WithLp.prod_norm_eq_card` | $\|f\|$ is the number of nonzero coordinates for $p = 0$ |
| `WithLp.prod_norm_eq_of_L1` | $\|x\| = \|x_1\| + \|x_2\|$ |
| `WithLp.prod_norm_eq_of_L2` | $\|x\| = \sqrt{\|x_1\|^2 + \|x_2\|^2}$ |
| `WithLp.prod_norm_sq_eq_of_L2` | $\|x\|^2 = \|x_1\|^2 + \|x_2\|^2$ |
| `WithLp.norm_fst_le` | $\|x_1\| \le \|x\|$ for $1 \le p$ |

Each norm lemma has the forms for the distance, the extended distance and the norm in $\mathbb{R}_{\ge 0}$, for example `WithLp.prod_dist_eq_of_L2`, `WithLp.prod_edist_eq_card` and `WithLp.prod_nnNorm_eq_add`. The triangle inequality holds only for $1 \le p$, so the instances `WithLp.instProdNormedAddCommGroup` and `WithLp.instProdNormedSpace` have the hypothesis `[Fact (1 ≤ p)]`. Completeness, `WithLp.instProdCompleteSpace`, needs no such hypothesis, because it comes from the uniform structure.

The file builds the instances with care. The uniform structure and the bornology of `WithLp p (E × F)` must be equal by definition to those of `E × F`. The map `WithLp.uniformEquivProd` is then a uniform equivalence, and `WithLp.prodContinuousLinearEquiv` is a continuous linear equivalence. The key estimate is the equivalence of the two norms: $\|x\|_\infty \le \|x\|_p \le 2^{1/p} \|x\|_\infty$. In Lean, `WithLp.prod_lipschitzWith_toLp` says that `WithLp.toLp p` is Lipschitz with constant $2^{1/p}$, and `WithLp.prod_antilipschitzWith_toLp` says that it is antilipschitz with constant $1$. Proof sketch of the upper bound: each term $\|x_i\|^p$ is at most $\|x\|_\infty^p$, so the sum is at most $2 \|x\|_\infty^p$, and the root of order $p$ gives the factor $2^{1/p}$.

The bundled maps follow the pattern of `Equiv.prodComm` and its relatives. `LinearIsometryEquiv.withLpProdComm` swaps the factors, `LinearIsometryEquiv.withLpProdAssoc` moves the brackets, `LinearIsometryEquiv.withLpProdCongr` and `LinearIsometry.withLpProdMap` act on each factor, and `LinearIsometryEquiv.withLpProdUnique` removes a factor with one element. `WithLp.fstL` and `WithLp.sndL` are the projections as continuous linear maps. The idempotents `WithLp.idemFst` and `WithLp.idemSnd` are the projections onto the two factors as endomorphisms. `WithLp.prod_norm_eq_idemFst_sup_idemSnd` and `WithLp.prod_norm_eq_add_idemFst` write the norm with these idempotents, a form that the theory of L-projections uses.

Sometimes the reader wants the $\ell^p$ norm on `E × F` itself, not on the synonym. The abbreviations `WithLp.seminormedAddCommGroupToProd` and `WithLp.normedAddCommGroupToProd` pull the norm back to `E × F`. They are not instances, so a proof must install them with `letI`.

**Finitely supported functions.** The file `Mathlib.Analysis.Normed.Lp.Finsupp` gives `WithLp p (ι →₀ X)` an extended metric for $1 \le p$, with $p$ in $\mathbb{R}_{\ge 0}$. The formula is `Finsupp.edist_def`: the distance of $f$ and $g$ is $(\sum_i d(f_i, g_i)^p)^{1/p}$, a finite sum over the union of the supports. `Finsupp.dist_def` and `Finsupp.nnDist_def` give the same formula for the real and the nonnegative distance. The file uses `Finsupp.zipWith` to make the function $i \mapsto d(f_i, g_i)$. The instance `Finsupp.instMetricSpaceWithLpOfNNReal` makes it a metric space when $X$ is one.

**Equivalences of models.** The file `Mathlib.Analysis.Normed.Lp.LpEquiv` compares the models. On a finite index type, every family is in $\ell^p$, so `lp E p` and `PiLp p E` have the same elements and the same norm. `Equiv.lpPiLp` and `AddEquiv.lpPiLp` give the bijection. `lpPiLpₗᵢ` gives the linear isometric equivalence, and `equiv_lpPiLp_norm` says that it keeps the norm. The lemma `lpPiLpₗᵢ_symm_single` sends `PiLp.single p i a` to `lp.single p i a`. On a discrete topological space $\alpha$, a bounded function is the same as a bounded continuous function. Then `lp (fun _ ↦ E) ∞` is the same as `α →ᵇ E`: the maps are `AddEquiv.lpBCF`, `lpBCFₗᵢ`, `RingEquiv.lpBCF` and `AlgEquiv.lpBCF`. The lemmas `coe_lpBCFₗᵢ` and `coe_lpBCFₗᵢ_symm` say that the maps do not change the underlying functions.

**The inequality of Hölder.** The file `Mathlib.Analysis.Normed.Lp.lpHolder` proves the inequality for sequences in a general form. Let $p, q, r$ in $[0, \infty]$ satisfy $1/p + 1/q = 1/r$; the class `ENNReal.HolderTriple` records this. Let $B_i : E_i \to F_i \to G_i$ be continuous bilinear maps with $\|B_i\| \le K$ for all $i$. If $e \in \ell^p$ and $f \in \ell^q$, then $(B_i(e_i, f_i))_i \in \ell^r$. This is `Memℓp.holder`. The proof treats the cases $p = 0$, $p = \infty$, $q = 0$ and $q = \infty$ apart, with `Memℓp.bilin_of_zero_left`, `Memℓp.bilin_of_top_left` and their right forms. The main case uses the bound `Memℓp.holder_gen_bound` on finite sums, which comes from the inequality of Hölder for finite sums.

The bundled forms are `lp.holder`, the pointwise map, `lp.holderₗ`, the bilinear map, and `lp.holderL`, the continuous bilinear map, with norm at most $K$ by `lp.norm_holderL_le`. For conjugate exponents (the class `ENNReal.HolderConjugate`) and a complete target space $H$, `lp.dualPairing` is the pairing
$$\langle e, f \rangle = \sum_i B_i(e_i, f_i),$$
and `lp.norm_dualPairing` says that its norm is at most $K$. The proof is a composition: the map `lp.holderL` with $r = 1$ has norm at most $K$, and the sum `lp.tsumCLM` on $\ell^1$ has norm at most $1$ by `lp.norm_tsumCLM_le`. The same file gives `lp.mapCLM`, the action of a bounded family of continuous linear maps $T_i : E_i \to F_i$ on $\ell^p$, with `lp.norm_mapCLM_le`.

**Measurability.** The file `Mathlib.Analysis.Normed.Lp.MeasurableSpace` gives `WithLp p X` the measurable structure of `X` (`WithLp.measurableSpace`). The maps are measurable (`WithLp.measurable_toLp`, `WithLp.measurable_ofLp`), and `MeasurableEquiv.toLp` is the measurable equivalence. The instances `WithLp.borelSpace` and `PiLp.borelSpace` say that the Borel structure is the right one, with a hypothesis of second countability.

**Smooth approximation.** The file `Mathlib.Analysis.Normed.Lp.SmoothApprox` proves a density result. Let $E$ be a finite dimensional real normed space with a measure that is finite on compact sets. For $1 \le p < \infty$, a function in $L^p$ is at distance at most $\varepsilon$ from a smooth function with compact support. This is `MeasureTheory.MemLp.exist_eLpNorm_sub_le`. The bundled form `MeasureTheory.Lp.dense_hasCompactSupport_contDiff` says that such functions make a dense set of `MeasureTheory.Lp F p μ`. The proof approximates first by a continuous function with compact support, then smooths it with `HasCompactSupport.exist_eLpNorm_sub_le_of_continuous`, and adds the two errors of size $\varepsilon/2$.

#### Common errors

1. Using `E × F` for the $\ell^2$ product. The instance on `E × F` gives the sup norm. The Euclidean norm on a product is on `WithLp 2 (E × F)`, and an element is made with `WithLp.toLp 2 (x, y)`.
2. Forgetting `[Fact (1 ≤ p)]`. The norm on `WithLp p (E × F)` is defined for all $p$, but the normed group instance needs this fact. Write `haveI : Fact (1 ≤ p) := ⟨hp⟩` when $p$ is a variable.
3. Giving the wrong exponent to `Memℓp.holder`. The third exponent is found by the class `ENNReal.HolderTriple`, so for $p = q = 2$ the result is in $\ell^1$, not in $\ell^2$.

### Exercises

1. (A) Use `WithLp.prod_norm_eq_of_L1` to compute the norm of `WithLp.toLp 1 ((3 : ℝ), (-4 : ℝ))`.
2. (A) Prove that $\|x_2\| \le \|x\|$ for $x$ in `WithLp p (E × F)` and $1 \le p$, and find the lemma of the library that states it.
3. (B) Show that `WithLp.toLp 2` from `ℝ × ℝ` is not an isometry, and find a vector where the factor $\sqrt{2}$ of `WithLp.prod_lipschitzWith_toLp` is attained.
4. (B) Use `lpPiLpₗᵢ` to show that `lp (fun _ : Fin n ↦ ℝ) 2` is complete without the general completeness theorem for `lp`.
5. (B) Deduce the inequality of Cauchy and Schwarz for real sequences in $\ell^2$ from `Memℓp.holder` and `lp.norm_dualPairing`, with $B_i$ the multiplication of $\mathbb{R}$.
6. (C) Show that the set of smooth functions with compact support is dense in `MeasureTheory.Lp ℝ 1 MeasureTheory.volume` on `ℝ`, and explain why the hypothesis $p \ne \infty$ of `MeasureTheory.Lp.dense_hasCompactSupport_contDiff` is necessary.

### Reference

<?reference?>
