---
title: Normed group homomorphisms and their category
kind: api
modules:
  - Mathlib.Analysis.Normed.Group.Hom
  - Mathlib.Analysis.Normed.Group.HomCompletion
  - Mathlib.Analysis.Normed.Group.ControlledClosure
  - Mathlib.Analysis.Normed.Group.SemiNormedGrp
  - Mathlib.Analysis.Normed.Group.SemiNormedGrp.Completion
  - Mathlib.Analysis.Normed.Group.SemiNormedGrp.Kernels
explains:
  E2: [NormedAddGroupHom.opNorm_le_bound, NormedAddGroupHom.norm_comp_le, NormedAddGroupHom.isClosed_ker, NormedAddGroupHom.norm_completion, NormedAddGroupHom.ker_completion, controlled_closure_of_complete, SemiNormedGrp.explicitCokernelDesc_norm_le, SemiNormedGrp.iso_isometry_of_normNoninc]
  E1: auto
families: []
requires: [V05, V13, V16.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Normed group homomorphisms and their category

### Overview

The sections before this one study continuous linear maps between normed spaces. Some constructions have no scalars. A seminormed abelian group, such as a group of chains with an $\ell^1$ norm, has a norm but no field acts on it. The right maps are the bounded group homomorphisms: the additive maps $f$ with $\|f(x)\| \le C \|x\|$ for a constant $C$. Mathlib calls them normed group homomorphisms, with the type `NormedAddGroupHom V W`.

This section treats the theory of these maps. It gives the operator norm, kernels, ranges and equalizers, the extension of a map to the completions, and a lemma on preimages with controlled norm. It then treats the categories `SemiNormedGrp` and `SemiNormedGrp₁` of seminormed groups, with all bounded maps and with the maps of norm at most $1$, and their completions and cokernels. The theory follows the theory of the operator norm of the previous section, without scalars. The categories are a basis for homological algebra of normed groups.

### The library around it

**The type of bounded homomorphisms.** The file `Mathlib.Analysis.Normed.Group.Hom` defines the structure `NormedAddGroupHom V₁ V₂`. Its fields are a function, additivity, and the existence of a bound $C$. The constructors are `AddMonoidHom.mkNormedAddGroupHom`, which takes an additive map and an explicit bound, and `NormedAddGroupHom.ofLipschitz`, which takes an additive Lipschitz map. The lemma `exists_pos_bound_of_bound` makes a bound positive, and `NormedAddGroupHom.bound` gives a positive bound for each map. A bounded homomorphism is Lipschitz, so it is continuous and uniformly continuous (`NormedAddGroupHom.continuous`, `NormedAddGroupHom.uniformContinuous`). The coercion to functions comes from the instance `NormedAddGroupHom.funLike`, and the instances `NormedAddGroupHom.toAddMonoidHomClass` and `NormedAddGroupHom.instContinuousMapClass` make the general lemmas on additive and continuous maps apply.

**The operator norm.** The norm of $f$ is the infimum of the bounds:
$$\|f\| = \inf \{ c \ge 0 : \|f(x)\| \le c \|x\| \text{ for all } x \}.$$
The definition is `NormedAddGroupHom.opNorm`. The API is the same as the API of `ContinuousLinearMap`, with the prefix `NormedAddGroupHom`. The table gives the main lemmas.

| Lean name | Statement |
|---|---|
| `NormedAddGroupHom.le_opNorm` | $\|f(x)\| \le \|f\| \|x\|$ |
| `NormedAddGroupHom.opNorm_le_bound` | if $\|f(x)\| \le M \|x\|$ for all $x$ and $0 \le M$, then $\|f\| \le M$ |
| `NormedAddGroupHom.opNorm_add_le` | $\|f + g\| \le \|f\| + \|g\|$ |
| `NormedAddGroupHom.norm_comp_le` | $\|g \circ f\| \le \|g\| \|f\|$ |
| `NormedAddGroupHom.opNorm_zero_iff` | $\|f\| = 0 \iff f = 0$, for normed groups |
| `NormedAddGroupHom.norm_id` | $\|\mathrm{id}\| = 1$ when the topology is not trivial |

Proof sketch of `NormedAddGroupHom.norm_comp_le`: for each $x$, $\|g(f(x))\| \le \|g\| \|f(x)\| \le \|g\| \|f\| \|x\|$, so $\|g\| \|f\|$ is a bound, and `NormedAddGroupHom.opNorm_le_bound` concludes. With this norm, the homomorphisms form a seminormed group (`NormedAddGroupHom.toSeminormedAddCommGroup`), and a normed group when the domain and the target are normed (`NormedAddGroupHom.toNormedAddCommGroup`). A map with $\|f\| \le 1$ is called norm nonincreasing. The predicate is `NormedAddGroupHom.NormNoninc`, and `NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one` gives the equivalence with $\|f\| \le 1$. An isometry is norm nonincreasing (`NormedAddGroupHom.normNoninc_of_isometry`).

**Kernels, ranges and equalizers.** The kernel `NormedAddGroupHom.ker` and the range `NormedAddGroupHom.range` are additive subgroups, with `NormedAddGroupHom.mem_ker` and `NormedAddGroupHom.mem_range`. The kernel is closed, `NormedAddGroupHom.isClosed_ker`, because it is the preimage of the closed set $\{0\}$ by a continuous map. The range need not be closed. The inclusion of a subgroup is `NormedAddGroupHom.incl`, and `NormedAddGroupHom.ker.lift` factors a map through the kernel. The equalizer of two maps $f$ and $g$ is the subgroup where they agree, `NormedAddGroupHom.equalizer`, with the inclusion `NormedAddGroupHom.Equalizer.ι` and the factorization `NormedAddGroupHom.Equalizer.lift`. The lemmas `NormedAddGroupHom.Equalizer.norm_lift_le` and `NormedAddGroupHom.Equalizer.lift_normNoninc` say that the factorization does not increase the norm.

The predicate `NormedAddGroupHom.SurjectiveOnWith f K C` says that each $h \in K$ has a preimage $g$ with $\|g\| \le C \|h\|$. It is a quantitative form of surjectivity. The theorem of the open mapping chapter gives such a constant for a surjective continuous linear map between Banach spaces.

**Completions.** The file `Mathlib.Analysis.Normed.Group.HomCompletion` extends a bounded homomorphism $f : G \to H$ to the completions. The map `NormedAddCommGroup.toCompl` is the inclusion of $G$ into `UniformSpace.Completion G`. It keeps the norm (`NormedAddCommGroup.norm_toCompl`) and has dense range (`NormedAddCommGroup.denseRange_toCompl`). The extension is `NormedAddGroupHom.completion`, and `NormedAddGroupHom.completion_coe` says that it agrees with $f$ on $G$. The completion is a functor: `NormedAddGroupHom.completion_id` and `NormedAddGroupHom.completion_comp`. It is also additive, `NormedAddGroupHom.completion_add`, and it keeps the norm, `NormedAddGroupHom.norm_completion`. Proof sketch: the bound $\|\hat f(y)\| \le \|f\| \|y\|$ holds on the dense set $G$, and both sides are continuous, so it holds on the completion. The converse inequality comes from the restriction to $G$.

The kernel of the completion is subtle. It always contains the closure of the image of the kernel of $f$ (`NormedAddGroupHom.ker_le_ker_completion`). Equality holds when $f$ is surjective onto its range with a controlled constant. This is `NormedAddGroupHom.ker_completion`: under `f.SurjectiveOnWith f.range C`, the kernel of $\hat f$ is the closure of the image of $\ker f$.

**Controlled closure.** The file `Mathlib.Analysis.Normed.Group.ControlledClosure` extends a controlled surjectivity from a subgroup to its closure. Let $G$ be complete, and let each $h \in K$ have a preimage $g$ with $\|g\| \le C \|h\|$. Then each $h$ in the closure of $K$ has a preimage with $\|g\| \le (C + \varepsilon) \|h\|$, for each $\varepsilon > 0$. This is `controlled_closure_of_complete`. The proof is the argument of the open mapping theorem. Write $h$ as a sum $\sum_n h_n$ of elements of $K$ with $\|h_n\|$ small for $n \ge 1$, take controlled preimages $g_n$, and sum them in the complete group $G$. The form `controlled_closure_range_of_complete` treats the image of a third group by an isometry.

**The categories.** The file `Mathlib.Analysis.Normed.Group.SemiNormedGrp` defines the category `SemiNormedGrp` of seminormed abelian groups with bounded homomorphisms, and the category `SemiNormedGrp₁` with norm nonincreasing homomorphisms. The pattern is the pattern of the other concrete categories of Mathlib. An object is a bundled type with its structure, the morphisms are wrapped in a structure `SemiNormedGrp.Hom`, the function `SemiNormedGrp.Hom.hom` unwraps a morphism, and `SemiNormedGrp.ofHom` wraps a normed group homomorphism. The simp lemmas `SemiNormedGrp.hom_comp`, `SemiNormedGrp.hom_id` and `SemiNormedGrp.hom_ofHom` move between the two levels. For `SemiNormedGrp₁` the wrapper is `SemiNormedGrp₁.mkHom`, which takes a proof of `NormedAddGroupHom.NormNoninc`. Both categories have a zero object (`SemiNormedGrp.hasZeroObject`) and zero morphisms.

An isomorphism of `SemiNormedGrp` is a bounded map with a bounded inverse, so it need not keep the norm. The lemma `SemiNormedGrp.iso_isometry_of_normNoninc` says that an isomorphism is an isometry when both the map and its inverse are norm nonincreasing. Proof: $\|x\| = \|f^{-1}(f(x))\| \le \|f(x)\| \le \|x\|$. In `SemiNormedGrp₁` this holds for each isomorphism, `SemiNormedGrp₁.iso_isometry`, and `SemiNormedGrp₁.mkIso` turns an isomorphism of `SemiNormedGrp` with two norm nonincreasing maps into an isomorphism of `SemiNormedGrp₁`.

**Completion as a functor.** The file `Mathlib.Analysis.Normed.Group.SemiNormedGrp.Completion` makes completion a functor, `SemiNormedGrp.completion`. Its object is `UniformSpace.Completion V` (`SemiNormedGrp.completion_obj_carrier`), and its action on morphisms is `NormedAddGroupHom.completion` (`SemiNormedGrp.completion_map`). The inclusion `SemiNormedGrp.completion.incl` keeps the norm, and `SemiNormedGrp.completion.lift` extends a morphism into a complete group, with `SemiNormedGrp.completion.lift_comp_incl`. The instance `SemiNormedGrp.instPreadditive` makes the category preadditive, and the functor is additive (`SemiNormedGrp.instAdditiveCompletion`).

**Kernels and cokernels.** The file `Mathlib.Analysis.Normed.Group.SemiNormedGrp.Kernels` proves that both categories have cokernels (`SemiNormedGrp.instHasCokernels`, `SemiNormedGrp₁.instHasCokernels`) and that `SemiNormedGrp` has equalizers (`SemiNormedGrp.instHasEqualizers`). The cokernel of $f : X \to Y$ is the quotient $Y / f(X)$ with the quotient seminorm. The quotient is by the range, not by its closure, so the quotient is only seminormed. The general cokernel of category theory is defined by a universal property, so the file also gives an explicit model: `SemiNormedGrp.explicitCokernel`, with the projection `SemiNormedGrp.explicitCokernelπ` and the factorization `SemiNormedGrp.explicitCokernelDesc`. The projection is surjective and a quotient map (`SemiNormedGrp.explicitCokernelπ_surjective`, `SemiNormedGrp.isQuotient_explicitCokernelπ`). The factorization of $g$ has norm at most $\|g\|$ (`SemiNormedGrp.explicitCokernelDesc_norm_le`), because the quotient norm is an infimum over the fibre. The isomorphism with the abstract cokernel is `SemiNormedGrp.explicitCokernelIso`.

#### Common errors

1. Using `ContinuousLinearMap` lemmas for a `NormedAddGroupHom`. The two types are different, and the lemmas have the prefix `NormedAddGroupHom`. A continuous linear map gives a bounded homomorphism, but Lean does not insert the conversion.
2. Expecting an isomorphism of `SemiNormedGrp` to be an isometry. It is only a bounded map with a bounded inverse. Use `SemiNormedGrp.iso_isometry_of_normNoninc`, or work in `SemiNormedGrp₁`.
3. Expecting the cokernel to be a normed group. The range of $f$ need not be closed, so the quotient $Y / f(X)$ is only seminormed, and elements of the closure of the range have norm $0$.

### Exercises

1. (A) Prove `NormedAddGroupHom.norm_comp_le` from `NormedAddGroupHom.le_opNorm` and `NormedAddGroupHom.opNorm_le_bound`.
2. (A) Show that the map $\mathbb{Z} \to \mathbb{R}$, $n \mapsto n$, is a norm nonincreasing homomorphism, and build it with `AddMonoidHom.mkNormedAddGroupHom`.
3. (B) Give a bounded homomorphism with a range that is not closed, and compute the norm of a nonzero element of the closure of the range in the cokernel.
4. (B) Prove that the norm of the completion of $f$ is equal to the norm of $f$, as in `NormedAddGroupHom.norm_completion`.
5. (B) Show that each isomorphism of `SemiNormedGrp₁` is an isometry, and explain why the same proof fails in `SemiNormedGrp`.
6. (C) Prove `controlled_closure_of_complete`: write an element of the closure as a fast convergent series of elements of $K$, and sum the preimages.

### Reference

<?reference?>
