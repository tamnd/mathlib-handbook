---
title: Continuous multilinear and alternating maps
kind: api
modules:
  - Mathlib.Analysis.Normed.Module.Multilinear.Basic
  - Mathlib.Analysis.Normed.Module.Multilinear.Curry
  - Mathlib.Analysis.Normed.Module.Alternating.Basic
  - Mathlib.Analysis.Normed.Module.Alternating.Curry
  - Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin
  - Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
  - Mathlib.Analysis.Normed.Module.PiTensorProduct.InjectiveSeminorm
explains:
  E2: [ContinuousMultilinearMap.le_opNorm, ContinuousMultilinearMap.opNorm_le_bound, MultilinearMap.mkContinuous_norm_le, ContinuousMultilinearMap.norm_image_sub_le, ContinuousMultilinearMap.norm_mkPiAlgebra, continuousMultilinearCurryLeftEquiv, ContinuousAlternatingMap.norm_toContinuousMultilinearMap, ContinuousAlternatingMap.norm_alternatizeUncurryFin_le, PiTensorProduct.liftIsometry, PiTensorProduct.projectiveSeminorm_tprod_le]
  E1: auto
families: []
requires: [V08, V13, V16.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Continuous multilinear and alternating maps

### Overview

A multilinear map $f(m_1, \dots, m_n)$ is linear in each variable when the other variables stay fixed. In a normed setting the useful maps are the continuous ones. A multilinear map on a finite product of normed spaces is continuous if and only if there is a constant $C$ with $\|f(m)\| \le C \prod_i \|m_i\|$. The smallest such $C$ is the operator norm of $f$. With this norm, the continuous multilinear maps form a normed space, and the space is complete when the target is complete. These spaces hold the higher derivatives of the differential calculus of volume 17, and the terms of power series.

Mathlib uses the type `ContinuousMultilinearMap 𝕜 E G` for a family `E : ι → Type*` of normed spaces indexed by a finite type `ι`. The notation `G [×n]→L[𝕜] G'` is the case where all $n$ factors are equal. The alternating maps, which change sign when two variables change places, have the type `E [⋀^ι]→L[𝕜] F`. This section gives the operator norm of both types, the curry equivalences, and the projective norm on a tensor product of normed spaces.

### The library around it

The operator norm of a continuous multilinear map is an infimum, as for linear maps. The two basic facts are `ContinuousMultilinearMap.le_opNorm`, which gives $\|f(m)\| \le \|f\| \prod_i \|m_i\|$, and `ContinuousMultilinearMap.opNorm_le_bound`, which gives $\|f\| \le M$ from $0 \le M$ and the bound $\|f(m)\| \le M \prod_i \|m_i\|$ for all $m$. Use these two lemmas for most estimates. The lemma `ContinuousMultilinearMap.opNorm_le_iff` puts them together, and `ContinuousMultilinearMap.isLeast_opNorm` states that the norm is the least bound. The definition `ContinuousMultilinearMap.norm_def` unfolds the norm, but a proof seldom needs it.

To build a continuous multilinear map, start with a `MultilinearMap` and a bound. The constructor `MultilinearMap.mkContinuous` takes a constant $C$ and a proof of $\|f(m)\| \le C \prod_i \|m_i\|$. The lemma `MultilinearMap.mkContinuous_norm_le` then gives the norm bound $\|f\| \le C$ when $0 \le C$. The lemma `MultilinearMap.continuous_of_bound` gives only the continuity, and `MultilinearMap.exists_bound_of_continuous` gives the opposite direction.

The space of continuous multilinear maps into a complete space is complete. Mathlib gives the instance `ContinuousMultilinearMap.instCompleteSpace` in the topological library, so the normed theory does not repeat it. The proof is the same as for linear maps: a Cauchy sequence of maps converges at each point, and the limit satisfies the same bound. The space of maps is a normed space over the field, and the evaluation $(f, m) \mapsto f(m)$ is continuous. A sequence of maps that converges in norm thus converges uniformly on each bounded set.

A multilinear map is not Lipschitz on the full space. The lemma `ContinuousMultilinearMap.norm_image_sub_le` gives the estimate $\|f(m_1) - f(m_2)\| \le \|f\| \cdot n \cdot \max(\|m_1\|, \|m_2\|)^{n-1} \|m_1 - m_2\|$, where $n$ is the number of variables. The primed form `ContinuousMultilinearMap.norm_image_sub_le'` gives a sharper sum over the variables. These lemmas make $f$ Lipschitz on each ball, and they are the start of the proof that $f$ is smooth.

Composition with linear maps follows the rules for linear maps. The lemma `ContinuousLinearMap.norm_compContinuousMultilinearMap_le` gives $\|g \circ f\| \le \|g\| \|f\|$ for a linear map $g$ after a multilinear map $f$. The lemma `ContinuousMultilinearMap.norm_compContinuousLinearMap_le` gives $\|f \circ (g_i)_i\| \le \|f\| \prod_i \|g_i\|$ for linear maps $g_i$ in each variable. The product map $(m_i)_i \mapsto \prod_i m_i$ in a normed algebra is `ContinuousMultilinearMap.mkPiAlgebra`. The lemma `ContinuousMultilinearMap.norm_mkPiAlgebra` states that its norm is $1$ in a normed algebra with $\|1\| = 1$. The map $(t_i)_i \mapsto (\prod_i t_i) z$ on $\mathbb{K}^n$ is `ContinuousMultilinearMap.mkPiRing`, and `ContinuousMultilinearMap.norm_mkPiRing` states that its norm is $\|z\|$. The lemma `ContinuousMultilinearMap.norm_restr` controls the map that `ContinuousMultilinearMap.restr` makes when it fixes some of the variables to one vector.

A multilinear map of $n + 1$ variables is the same as a linear map into the multilinear maps of $n$ variables. Mathlib makes this identification an isometry. The equivalence `continuousMultilinearCurryLeftEquiv` takes out the first variable, and `continuousMultilinearCurryRightEquiv` takes out the last. Both are linear isometric equivalences, so the norm stays the same, as the lemmas `ContinuousMultilinearMap.curryLeft_norm` and `ContinuousLinearMap.uncurryLeft_norm` state. The equivalences `continuousMultilinearCurryFin0` and `continuousMultilinearCurryFin1` identify the maps of $0$ variables with the constants and the maps of $1$ variable with the linear maps. The equivalence `ContinuousMultilinearMap.curryFinFinset` splits the variables along a finite set and its complement. The iterated derivative uses these equivalences at each step.

The alternating maps have the same API with the prefix `ContinuousAlternatingMap`. The norm is the norm of the underlying multilinear map, and `ContinuousAlternatingMap.norm_toContinuousMultilinearMap` states this equality. So `ContinuousAlternatingMap.le_opNorm`, `ContinuousAlternatingMap.opNorm_le_bound` and `ContinuousAlternatingMap.norm_image_sub_le` are copies of the multilinear lemmas. The map `ContinuousAlternatingMap.curryLeft` takes out the first variable of an alternating map of $n + 1$ variables, and `ContinuousAlternatingMap.norm_curryLeft` states that it keeps the norm. The lemma `ContinuousAlternatingMap.curryLeft_same` states that the result is $0$ when the same vector goes in twice.

The opposite construction is `ContinuousAlternatingMap.alternatizeUncurryFin`. It takes a linear map $f$ from $E$ into the alternating maps of $n$ variables, and gives the alternating map $v \mapsto \sum_i (-1)^i f(v_i)(v_0, \dots, \widehat{v_i}, \dots, v_n)$ of $n + 1$ variables. The lemma `ContinuousAlternatingMap.alternatizeUncurryFin_apply` gives this formula. The estimate `ContinuousAlternatingMap.norm_alternatizeUncurryFin_le` bounds the norm by $(n + 1) \|f\|$. The composite with `ContinuousAlternatingMap.curryLeft` is $(n + 1)$ times the identity, as `ContinuousAlternatingMap.alternatizeUncurryFin_curryLeft` states. This construction is the exterior derivative of a differential form in coordinates.

The last two modules give a norm to the tensor product $\bigotimes_i E_i$ of a finite family of normed spaces. The projective seminorm of $x$ is the infimum of $\sum_j |a_j| \prod_i \|m_{j,i}\|$ over all ways to write $x = \sum_j a_j \bigotimes_i m_{j,i}$. Mathlib gives this seminorm as `PiTensorProduct.projectiveSeminorm`, and makes it the norm of the type with the instance `PiTensorProduct.instSeminormedAddCommGroup`. The lemma `PiTensorProduct.projectiveSeminorm_tprod_le` gives $\|\bigotimes_i m_i\| \le \prod_i \|m_i\|$. The universal property is the isometry `PiTensorProduct.liftIsometry` between the continuous multilinear maps on $\prod_i E_i$ and the continuous linear maps on $\bigotimes_i E_i$. The map `PiTensorProduct.mapL` is the tensor product of a family of continuous linear maps, with the estimate `PiTensorProduct.opNorm_mapL`. The module on the injective seminorm now gives only `PiTensorProduct.toDualContinuousMultilinearMap`, the evaluation of a tensor on continuous multilinear maps. The lemma `PiTensorProduct.toDualContinuousMultilinearMap_le_projectiveSeminorm` bounds its norm by the projective seminorm. The old injective seminorm of that module is deprecated, so do not use it.

#### Common errors

1. Forgetting that the norm needs a finite index type. The operator norm and its lemmas need `[Fintype ι]`. For the notation `G [×n]→L[𝕜] G'`, the index type is `Fin n`, so this condition is automatic.
2. Using `ContinuousLinearMap` lemmas for a multilinear map. The lemmas have the prefix `ContinuousMultilinearMap` or `ContinuousAlternatingMap`. A multilinear map is not linear on the product, so `ContinuousLinearMap.le_opNorm` does not apply to it.
3. Expecting the projective seminorm to be a norm with no other work. Mathlib gives only a seminorm instance on `⨂[𝕜] i, E i`. Do not expect a `NormedAddCommGroup` instance.

### Exercises

1. (A) Show that $(x, y) \mapsto xy$ on $\mathbb{R}$ is a continuous multilinear map of norm $1$ with `ContinuousMultilinearMap.mkPiAlgebra` and `ContinuousMultilinearMap.norm_mkPiAlgebra`.
2. (A) Prove $\|f(m)\| \le \|f\| \cdot r^n$ when $\|m_i\| \le r$ for all $i$, from `ContinuousMultilinearMap.le_opNorm`.
3. (B) Prove `ContinuousMultilinearMap.norm_image_sub_le` for $n = 2$ with a direct telescoping argument.
4. (B) Show that `continuousMultilinearCurryLeftEquiv` keeps the norm: prove both inequalities with `ContinuousMultilinearMap.opNorm_le_bound`.
5. (B) Show that `ContinuousAlternatingMap.alternatizeUncurryFin` of `ContinuousAlternatingMap.curryLeft` of $f$ is $(n + 1) f$ for $n = 1$, with the formula of `ContinuousAlternatingMap.alternatizeUncurryFin_apply`.
6. (C) Prove `PiTensorProduct.projectiveSeminorm_tprod_le`, and use `PiTensorProduct.liftIsometry` to show that equality holds when each $E_i$ is $\mathbb{R}$.

### Reference

<?reference?>
