---
title: Unitization and square zero extensions
kind: api
modules:
  - Mathlib.Analysis.Normed.Algebra.Unitization
  - Mathlib.Analysis.Normed.Algebra.UnitizationL1
  - Mathlib.Analysis.Normed.Algebra.TrivSqZeroExt
  - Mathlib.Analysis.Normed.Algebra.DualNumber
explains:
  E2: [Unitization.splitMul, Unitization.instNormedRing, Unitization.norm_eq_sup, Unitization.isometry_inr, Unitization.instCompleteSpace, WithLp.unitization_norm_def, WithLp.unitizationAlgEquiv, TrivSqZeroExt.instL1NormedRing, TrivSqZeroExt.snd_exp, DualNumber.exp_smul_eps]
  E1: auto
families: []
requires: [V06, V07, V16.C01, V16.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Unitization and square zero extensions

### Overview

Many Banach algebras of analysis have no unit: the continuous functions on $\mathbb{R}$ that tend to $0$ at infinity, the integrable functions with convolution, and the compact operators on an infinite dimensional space. The unitization of an algebra $A$ over $\mathbb{K}$ is the algebra $\mathbb{K} \times A$ with the product $(k, a)(l, b) = (k l, k b + l a + a b)$. Its unit is $(1, 0)$, and $A$ sits inside it as the ideal of pairs $(0, a)$. The spectrum of an element of $A$ is defined through the unitization, so the theory of section 3 applies to algebras without a unit.

The unitization needs a norm. Two choices are natural. The $\ell^1$ norm $\|(k, a)\| = \|k\| + \|a\|$ always works. When the norm of $A$ is regular, which means that $\|a\| = \sup_{\|b\| \le 1} \|a b\|$, a second norm comes from the action of $(k, a)$ on $A$ by left multiplication. Mathlib uses the second norm as the default, since it is a $C^*$ norm for a $C^*$ algebra. The square zero extension $R \oplus M$ of a ring by a bimodule, with $m m' = 0$, uses the $\ell^1$ norm. Its exponential has the closed form $\exp(r + m) = \exp(r) + \exp(r) m$ when $r$ commutes with $m$, and the dual numbers $\mathbb{R}[\varepsilon]$ with $\varepsilon^2 = 0$ are a special case.

### The library around it

The type `Unitization 𝕜 A` and the maps `Unitization.inl` from $\mathbb{K}$ and `Unitization.inr` from $A$ are algebraic, and they are in the volume on rings. The module `Mathlib.Analysis.Normed.Algebra.Unitization` adds the norm. The map `Unitization.splitMul 𝕜 A` is an algebra homomorphism from the unitization to $\mathbb{K} \times (A \to_L A)$. It sends $(k, a)$ to the pair of $k$ and the operator $b \mapsto k b + a b$. The norm of the unitization is the norm of this pair, by `Unitization.norm_def`, and `Unitization.norm_eq_sup` gives the explicit form $\max(\|k\|, \|k \cdot 1 + L_a\|)$, with $L_a$ the operator of left multiplication by $a$.

The construction needs the class `RegularNormedAlgebra 𝕜 A`, which states that `ContinuousLinearMap.mul 𝕜 A` is an isometry. Then `Unitization.splitMul_injective` states that the map is injective, so the pullback is a norm. The instances `Unitization.instNormedRing` and `Unitization.instNormedAlgebra` give the normed algebra, `Unitization.instNormOneClass` states that $\|1\| = 1$, and `Unitization.instCompleteSpace` states that the unitization of a Banach algebra is complete. The lemma `Unitization.norm_inr` states that $\|(0, a)\| = \|a\|$, so `Unitization.isometry_inr` makes $A$ an isometric part of its unitization. The topology is the product topology, by design, so the lemmas on continuity of the two parts, such as `Unitization.continuous_fst`, need no norm. The maps `Unitization.lipschitzWith_addEquiv` and `Unitization.antilipschitzWith_addEquiv` state that the identity to $\mathbb{K} \times A$ is Lipschitz in both directions with constant $2$, and `Unitization.uniformEquivProd` gives the uniform equivalence.

Two instances supply the regularity in the main cases. The instance `NormedAlgebra.instRegularNormedAlgebra` states that a unital normed algebra with $\|1\| = 1$ has a regular norm, since $\|a\| = \|a \cdot 1\|$. Such an algebra has a unit already, so the unitization is of interest mainly for algebras without one. The instance `CStarRing.instRegularNormedAlgebra` states that the norm of a $C^*$ algebra is regular, from the identity $\|a^* a\| = \|a\|^2$. Chapter 12 builds on this: `Unitization.instCStarRing` states that the unitization of a $C^*$ algebra with the norm of this section is again a $C^*$ algebra, and the functional calculus for algebras without a unit passes through it. The algebraic lemmas on the unitization, such as `Unitization.inr_star` and the extension `Unitization.lift` of a homomorphism without a unit, then apply to the normed algebra without change, since the norm is added on the same type.

The module `Mathlib.Analysis.Normed.Algebra.UnitizationL1` gives the $\ell^1$ norm on the type synonym `WithLp 1 (Unitization 𝕜 A)`. It needs no regularity. The lemma `WithLp.unitization_norm_def` states that $\|x\| = \|k\| + \|a\|$, and the instances `WithLp.instUnitizationNormedRing` and `WithLp.instUnitizationNormedAlgebra` make it a normed algebra. The equivalence `WithLp.unitizationAlgEquiv` is the identity, as an algebra isomorphism between the two types. The instance `WithLp.instNormOneClassOfNatENNRealUnitization` states that $\|1\| = 1$ also for this norm. Of all norms on the unitization with $\|1\| = 1$ that extend the norm of $A$, the $\ell^1$ norm is the largest and the norm of `Unitization.splitMul` is the smallest. The $\ell^1$ form gives a short proof that the quasispectrum of an element of a Banach algebra without a unit is compact, which is `quasispectrum.isCompact`. The lemma `Unitization.spectralRadius_inr` of section 3 compares the spectral radius in $A$ and in the unitization.

The module `Mathlib.Analysis.Normed.Algebra.TrivSqZeroExt` puts the $\ell^1$ norm on `TrivSqZeroExt R M`. Mathlib registers it as an instance, without a type synonym. The instances are `TrivSqZeroExt.instL1SeminormedRing`, `TrivSqZeroExt.instL1NormedRing` and `TrivSqZeroExt.instL1NormedAlgebra`, and `TrivSqZeroExt.norm_def` states $\|x\| = \|x_1\| + \|x_2\|$. The lemmas `TrivSqZeroExt.norm_inl` and `TrivSqZeroExt.norm_inr` give the norms of the two parts. With these instances the exponential of section 4 is defined, and the module computes it. The lemma `TrivSqZeroExt.fst_exp` states that the first part of $\exp(x)$ is $\exp(x_1)$. The lemma `TrivSqZeroExt.snd_exp` states that the second part is $\exp(x_1) \cdot x_2$, and `TrivSqZeroExt.exp_def` combines the two. These forms hold when the left and right actions of $R$ on $M$ agree. For a general bimodule, `TrivSqZeroExt.exp_def_of_smul_comm` asks this only for $x_1$ and $x_2$. The lemma `TrivSqZeroExt.exp_inl` states that the exponential of a pure element $r$ is $\exp(r)$ in the first part, and `TrivSqZeroExt.exp_inr` states that the exponential of a pure element $m$ is $1 + m$.

The dual numbers `DualNumber R` are the square zero extension of $R$ by itself, with the element `DualNumber.eps` that squares to $0$. The module `Mathlib.Analysis.Normed.Algebra.DualNumber` holds two lemmas. The lemma `DualNumber.exp_eps` states $\exp(\varepsilon) = 1 + \varepsilon$, and `DualNumber.exp_smul_eps` states $\exp(r \varepsilon) = 1 + r \varepsilon$. The dual numbers are the algebra behind automatic differentiation: $f(x + \varepsilon) = f(x) + f'(x) \varepsilon$ for a polynomial $f$, and the lemma for $\exp$ is the same rule for $f = \exp$ at $x = 0$.

#### Common errors

1. Expecting `Unitization 𝕜 A` to have a norm for each normed algebra $A$. The default norm needs `RegularNormedAlgebra 𝕜 A`. Without it, use `WithLp 1 (Unitization 𝕜 A)` and pass with `WithLp.unitizationAlgEquiv`.
2. Expecting the norm of the unitization to be $\|k\| + \|a\|$. The default norm is $\max(\|k\|, \|k \cdot 1 + L_a\|)$, by `Unitization.norm_eq_sup`. The $\ell^1$ norm is only on the type synonym.
3. Using `TrivSqZeroExt.snd_exp` for a bimodule with different left and right actions. The lemma needs the two actions to agree. Use `TrivSqZeroExt.exp_def_of_smul_comm` with a proof for the element.

### Exercises

1. (A) Use `Unitization.norm_inr` to show that the inclusion of $A$ into its unitization preserves distances.
2. (A) Compute $\exp(2 + 3 \varepsilon)$ in the real dual numbers with `TrivSqZeroExt.exp_def`.
3. (B) Show with `WithLp.unitization_norm_def` that $\|(k, a)(l, b)\| \le \|(k, a)\| \|(l, b)\|$ for the $\ell^1$ norm, from the formula for the product.
4. (B) For $A = \mathbb{C}$ with its usual norm, compute the norm of `Unitization.splitMul` at $(k, a)$ and compare it with $|k| + |a|$.
5. (B) Show that $(0, a)$ is never a unit in the unitization when $A \ne 0$, so $0$ is in the spectrum of $(0, a)$.
6. (C) Prove `DualNumber.exp_smul_eps` from `TrivSqZeroExt.snd_exp` and `TrivSqZeroExt.fst_exp`.

### Reference

<?reference?>
