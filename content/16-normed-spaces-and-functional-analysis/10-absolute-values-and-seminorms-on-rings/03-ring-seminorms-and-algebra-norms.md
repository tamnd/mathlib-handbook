---
title: Ring seminorms and algebra norms
kind: api
modules:
  - Mathlib.Analysis.Normed.Unbundled.RingSeminorm
  - Mathlib.Analysis.Normed.Unbundled.AlgebraNorm
  - Mathlib.Analysis.Normed.Unbundled.SeminormFromBounded
  - Mathlib.Analysis.Normed.Unbundled.SeminormFromConst
  - Mathlib.Analysis.Normed.Unbundled.SmoothingSeminorm
  - Mathlib.Analysis.Normed.Unbundled.IsPowMulFaithful
  - Mathlib.Analysis.Normed.Unbundled.IsPowMulTrivial
explains:
  E2: [RingSeminorm, RingNorm, MulRingNorm, RingNorm.toNormedRing, MulRingNorm.mulRingNormEquivAbsoluteValue, AlgebraNorm, MulAlgebraNorm, seminormFromBounded, seminormFromConst, smoothingSeminorm]
  E1: auto
families: []
requires: [V06, V11, V13, V16.C01, V16.C08, V16.C09]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Ring seminorms and algebra norms

### Overview

A normed ring has one norm, given by an instance. For the study of extensions of a valued field, it is necessary to compare many norms on one ring at the same time: the norms that a basis gives, the norms that the automorphisms of a field move, and the limits of sequences of such norms. Mathlib therefore has bundled seminorms on rings. A ring seminorm on $R$ is a function $f : R \to \mathbb{R}$ with $f(0) = 0$, $f(-x) = f(x)$, $f(x + y) \le f(x) + f(y)$ and $f(x y) \le f(x) f(y)$. It is a norm when $f(x) = 0$ only for $x = 0$, and it is multiplicative when $f(x y) = f(x) f(y)$. An algebra norm on an algebra $S$ over a normed ring $R$ also satisfies $f(r x) = \|r\| f(x)$.

Three constructions improve a function step by step. From a function that is only bounded for products, $f(x y) \le c f(x) f(y)$, a supremum gives a ring seminorm. From a ring seminorm, the limit of $f(x^n)^{1/n}$ gives a seminorm that is power multiplicative, which means $f(x^n) = f(x)^n$. From a power multiplicative seminorm and an element $c$, a limit gives a seminorm for which $c$ is multiplicative. Section 4 uses these steps to build the spectral norm on an algebraic extension.

### The library around it

The module `Mathlib.Analysis.Normed.Unbundled.RingSeminorm` defines the four structures `RingSeminorm R`, `RingNorm R`, `MulRingSeminorm R` and `MulRingNorm R`. Each extends the seminorm on groups of Chapter 8: `RingSeminorm.toAddGroupSeminorm` forgets the product, and `RingNorm.toRingSeminorm` and `MulRingNorm.toMulRingSeminorm` forget the condition on the kernel. The instances `RingSeminorm.ringSeminormClass`, `RingNorm.ringNormClass` and `MulRingNorm.mulRingNormClass` give the classes of the volume on rings, so a general lemma such as `map_pow_le_pow` applies: it states $f(a^n) \le f(a)^n$ for $n \ne 0$. The lemma `RingSeminorm.ne_zero_iff` states that a seminorm is nonzero if and only if it is nonzero at some point, and `RingSeminorm.seminorm_one_eq_one_iff_ne_zero` states that $f(1) = 1$ for each nonzero seminorm with $f(1) \le 1$.

The links to the normed classes go in both directions. The definitions `normRingSeminorm R` and `normRingNorm R` turn the norm of a normed ring into a bundled seminorm or norm, and `NormedField.toMulRingNorm R` does the same for a normed field. In the other direction, `RingSeminorm.toSeminormedRing` and `RingNorm.toNormedRing` make a ring with a bundled seminorm a seminormed ring or a normed ring. They are abbreviations and not instances, for the reason of Section 1: a ring can carry many seminorms. On a field, `RingSeminorm.toRingNorm` states that each nonzero ring seminorm is a norm, since a unit $x$ with $f(x) = 0$ forces $f(1) = 0$.

A multiplicative norm with real values is the same as an absolute value. The equivalence `MulRingNorm.mulRingNormEquivAbsoluteValue` identifies `MulRingNorm R` with `AbsoluteValue R ℝ` on a nontrivial ring, by `MulRingNorm.toAbsoluteValue` and `MulRingNorm.ofAbsoluteValue`. The documentation of the module asks to use `AbsoluteValue` when possible, so that results are not stated twice. The instance `MulRingNorm.instOne` gives the trivial norm, with value $1$ at each nonzero element, by `MulRingNorm.apply_one`.

The module `Mathlib.Analysis.Normed.Unbundled.AlgebraNorm` defines `AlgebraNorm R S` and `MulAlgebraNorm R S` for an algebra $S$ over a seminormed commutative ring $R$. The class `AlgebraNormClass` combines `SeminormClass` with `RingNormClass`, and `AlgebraNormClass.map_smul_eq_mul` states $f(r x) = \|r\| f(x)$. The lemma `AlgebraNorm.extends_norm` states that an algebra norm with $f(1) = 1$ extends the norm of $R$, and `MulAlgebraNorm.extends_norm` needs no condition. The definition `NormedAlgebra.toMulAlgebraNorm K L` gives the norm of a normed algebra of fields as a multiplicative algebra norm. The lemma `MulRingNorm.isPowMul` states that each multiplicative norm is power multiplicative, for the predicate `IsPowMul` that this chapter uses in each statement. The definition `AlgebraNorm.restriction` restricts an algebra norm to a smaller ring of scalars.

The module `Mathlib.Analysis.Normed.Unbundled.SeminormFromBounded` starts from a function $f$ with $f \ge 0$ and $f(x y) \le c f(x) f(y)$. The function `seminormFromBounded'` sends $x$ to the supremum of $f(x y) / f(y)$. With subadditivity, `seminormFromBounded` is a ring seminorm, and `normFromBounded` is a ring norm when $f$ has a trivial kernel. The lemma `seminormFromBounded_le` states that the new value is at most $c f(x)$, and `seminormFromBounded_ge` gives a bound below. The lemma `seminormFromBounded_ker` states that the kernel does not change, and `seminormFromBounded_isNonarchimedean` states that the ultrametric property is kept. Section 4 applies the construction to the norm of a basis, which is bounded for products but not submultiplicative.

The module `Mathlib.Analysis.Normed.Unbundled.SmoothingSeminorm` defines `smoothingFun μ x` as the infimum of $\mu(x^n)^{1/n}$ over $n \ge 1$, the same limit as the Gelfand radius of Chapter 9. The lemma `tendsto_smoothingFun_of_map_one_le_one` states that the sequence `smoothingSeminormSeq μ x` converges to this value when $\mu(1) \le 1$. The lemma `smoothingFun_le_self` states that the value is at most $\mu(x)$, and `isPowMul_smoothingFun` states that it is power multiplicative. For an ultrametric $\mu$, `isNonarchimedean_smoothingFun` states that the result is ultrametric, and `smoothingSeminorm μ hμ1 hna` bundles it as a ring seminorm. The subadditivity uses the ultrametric property through `RingSeminorm.exists_index_pow_le`, which bounds $\mu((x + y)^n)$ by a single term of the binomial expansion.

The module `Mathlib.Analysis.Normed.Unbundled.SeminormFromConst` takes a power multiplicative ring seminorm $f$ and an element $c$ with $f(c) \ne 0$. The definition `seminormFromConst c f` is the limit of $f(x c^n) / f(c)^n$, by `tendsto_seminormFromConst`, and the sequence `seminormFromConst_seq` is antitone. The lemma `seminormFromConst_const_mul` states that $c$ is multiplicative for the new seminorm, `seminormFromConst_isPowMul` states that it is still power multiplicative, and `seminormFromConst_le_seminorm` states that it is at most $f$. On a field, `normFromConst` gives a ring norm, and `algNormFromConst` gives an algebra norm.

Two short modules give consequences of power multiplicativity. The lemma `contraction_of_isPowMul` states that a bounded ring homomorphism into a ring with a power multiplicative norm is a contraction: $\|f(x)\| \le \|x\|$. The proof applies the bound $C$ to $x^n$, takes the $n$-th root and lets $C^{1/n} \to 1$. The lemma `AlgebraNorm.le_one_of_norm_le_one` states that, over a ring with a bounded norm, a power multiplicative algebra norm is at most $1$ on each integral element. So over a field with the trivial norm, each such norm on an algebraic extension is trivial.

#### Common errors

1. Making `RingNorm.toNormedRing` a global instance. It competes with the norm that the ring already has. Use it as a local instance, or keep the norm bundled and work with the function.
2. Stating new results for `MulRingNorm R`. Mathlib prefers `AbsoluteValue R ℝ`. Use `MulRingNorm.mulRingNormEquivAbsoluteValue` to pass to absolute values.
3. Forgetting the hypothesis $\mu(1) \le 1$ of `smoothingSeminorm` and of `tendsto_smoothingFun_of_map_one_le_one`. Without it the sequence $\mu(x^n)^{1/n}$ can fail to converge to its infimum.

### Exercises

1. (A) Show that the trivial ring norm, with value $1$ at each nonzero element, is a `MulRingNorm` on a field, and compare with `MulRingNorm.apply_one`.
2. (A) Use `map_pow_le_pow` to show that $f(x^n)^{1/n} \le f(x)$ for each ring seminorm $f$ and each $n \ge 1$.
3. (B) For a multiplicative $\mu$ with $\mu(1) \le 1$, show with `smoothingFun_apply_of_map_mul_eq_mul` that the smoothing does not change $\mu$.
4. (B) On $\mathbb{Q}^2$ with the product of coordinates, define $f(a, b) = 2 \max(|a|, |b|)$. Show that $f$ is submultiplicative but not power multiplicative, and compute `smoothingFun` of $f$.
5. (B) Use `contraction_of_isPowMul` to show that a bounded ring homomorphism between two normed fields is a contraction.
6. (C) Prove `AlgebraNorm.le_one_of_norm_le_one` for an element $x$ with $x^2 = a x + b$, where $\|a\|, \|b\| \le M$, by a bound on $f(x^n)$.

### Reference

<?reference?>
