---
title: WithAbs and completions at an absolute value
kind: api
modules:
  - Mathlib.Analysis.Normed.Ring.WithAbs
  - Mathlib.Analysis.Normed.Field.WithAbs
explains:
  E2: [WithAbs, WithAbs.toAbs, WithAbs.equiv, WithAbs.norm_toAbs_eq, WithAbs.normedField, AbsoluteValue.under, AbsoluteValue.LiesOver, AbsoluteValue.Completion, AbsoluteValue.Completion.isometryEquiv, AbsoluteValue.degree_mul_degree]
  E1: auto
families: []
requires: [V06, V11, V13, V14, V16.C01, V16.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## WithAbs and completions at an absolute value

### Overview

A field such as $\mathbb{Q}$ has many absolute values: the usual one and one for each prime $p$. Each gives a norm, a topology and a completion, $\mathbb{R}$ or $\mathbb{Q}_p$. In Lean a type has at most one instance of `NormedField`, so the norms cannot all be instances on $\mathbb{Q}$. The solution of Mathlib is a type synonym. For an absolute value $v$ on a ring $R$, the type `WithAbs v` is a copy of $R$ with the same ring structure and with the norm $v$. Two absolute values give two different types, each with its own norm, and each lemma of the earlier chapters applies to each of them.

The completion of a field $K$ at $v$ is the completion of `WithAbs v` as a uniform space. Mathlib wraps it in a structure, `AbsoluteValue.Completion v`, which is a complete normed field. For an extension $L / K$ with an absolute value $w$ on $L$ that restricts to $v$, the completion at $w$ is an algebra over the completion at $v$. Its dimension is the local degree of $w$ over $v$, and the local degrees multiply in a tower. The number theory volume uses these completions to study the places of a number field.

### The library around it

The type `WithAbs v` is a structure with one field. The constructor `WithAbs.toAbs v` sends $x \in R$ to its copy, and `WithAbs.ofAbs` sends it back. The lemmas `WithAbs.ofAbs_toAbs` and `WithAbs.toAbs_ofAbs` state that the two maps are inverse, and lemmas such as `WithAbs.toAbs_add`, `WithAbs.toAbs_mul` and `WithAbs.ofAbs_pow` state that they preserve the operations. The equivalence `WithAbs.equiv v` bundles them as a ring isomorphism from `WithAbs v` to $R$. The type has instances such as `WithAbs.instRing` and `WithAbs.instCommRing` from the ring $R$, and the instance `WithAbs.normedRing` adds the norm when the values of $v$ are real. The lemmas `WithAbs.norm_toAbs_eq` and `WithAbs.norm_eq_apply_ofAbs` state that the norm is $v$.

The synonym carries the module and algebra structure. For an algebra $T$ over $R$, the instances `WithAbs.algebraLeft` and `WithAbs.instAlgebra` give $T$ as an algebra over `WithAbs v` and `WithAbs v` as an algebra over $R$. The equivalences `WithAbs.linearEquiv` and `WithAbs.algEquiv` identify the synonym with the original type. For a ring homomorphism $f : R \to R'$ and absolute values $v$ and $w$, the map `WithAbs.map v w f` is $f$ between the two synonyms, and `WithAbs.congr` is the form for an isomorphism. The module for fields adds `WithAbs.instField` and the instance `WithAbs.normedField`. The instances `WithAbs.instFiniteDimensional` and `WithAbs.instIsSeparable` pass finite dimension and separability from $K$ to `WithAbs v`, so the results of field theory apply.

An absolute value $w$ on $L$ restricts to $K$ along the map of an algebra. The restriction is `AbsoluteValue.under K w`, and `AbsoluteValue.under_apply` states that its value at $x$ is $w$ at the image of $x$. The class `AbsoluteValue.LiesOver w v` states that $w$ restricts to $v$, by `AbsoluteValue.liesOver_iff`, and the instance `AbsoluteValue.instLiesOverUnder` states that each $w$ lies over its restriction. The lemma `AbsoluteValue.LiesOver.trans` gives the transitivity in a tower. When $w$ lies over $v$, the theorem `WithAbs.isometry_map` states that the map of the algebra is an isometry between the synonyms.

The module for fields defines the completion. The structure `AbsoluteValue.Completion v` has an instance `AbsoluteValue.Completion.instNormedField`, and `AbsoluteValue.Completion.instCompleteSpace` states that it is complete. The map `AbsoluteValue.Completion.coe` sends `WithAbs v` into the completion, and `AbsoluteValue.Completion.norm_coe` states that it preserves the norm. The lemma `AbsoluteValue.Completion.denseRange_coe` states that its range is dense, and `AbsoluteValue.Completion.induction_on` gives the principle of proof by density. The equivalences `AbsoluteValue.Completion.equiv` and `AbsoluteValue.Completion.isometryEquiv` identify the structure with the completion `UniformSpace.Completion (WithAbs v)` of Volume 13. The structure exists so that the completion has one type, without a nested synonym.

For an extension with $w$ over $v$, the map `AbsoluteValue.Completion.map v w` is the extension of the map of the algebra to the completions, and `AbsoluteValue.Completion.isometry_map` states that it is an isometry. The definition `AbsoluteValue.Completion.algebraOfLiesOver` turns it into an algebra structure. The local degree `AbsoluteValue.degree K w` is the dimension of the completion at $w$ over the completion at the restriction of $w$, by `AbsoluteValue.degree_eq`. The theorem `AbsoluteValue.degree_mul_degree` states that the local degrees multiply in a tower $J \subseteq K \subseteq L$. The theorem `AbsoluteValue.Completion.locallyCompactSpace` states that the completion is locally compact when $v$ comes from an isometric embedding into a locally compact field, for example into $\mathbb{R}$ or $\mathbb{C}$.

A few lemmas make the bookkeeping easy. The lemmas `WithAbs.toAbs_bijective` and `WithAbs.ofAbs_bijective` state that the two maps between $R$ and `WithAbs v` are bijective, so a statement about all elements of one type gives a statement about all elements of the other. The lemmas `WithAbs.map_id` and `WithAbs.map_comp` state that `WithAbs.map` sends the identity to the identity and a composite to a composite. For restrictions, `AbsoluteValue.under_under` states that the restriction of a restriction is the restriction along the composite map, and `AbsoluteValue.LiesOver.under_eq` states that the restriction of $w$ is $v$ when $w$ lies over $v$. On the side of the completions, `AbsoluteValue.Completion.map_coe` states that the map of the completions agrees with the map of the synonyms on the image of `WithAbs v`, and `AbsoluteValue.Completion.map_comp_map` states that the maps compose in a tower. The instance `WithAbs.instUniformContinuousConstSMulReal` states that, for a field $T$ that is an algebra over a ring $R$, multiplication by a scalar of $R$ on `WithAbs w` is uniformly continuous. With it, the instance `AbsoluteValue.Completion.instAlgebra` makes the completion an algebra over $R$, for example over $K$ itself. The theorem `AbsoluteValue.Completion.algebraMap_eq_of_liesOver` states that each algebra structure of the completion at $w$ over the completion at $v$ that is continuous and compatible with $K$ has the map of the completions as its algebra map, so the structure is unique.

One more lemma links the norm and the algebra. The lemma `WithAbs.tendsto_one_div_one_add_pow_nhds_one` states that $1 / (1 + a^n) \to 1$ in `WithAbs v` when $v(a) < 1$. It is a step in the proof of the weak approximation theorem of Volume 14, which builds an element that is close to $1$ for one absolute value and close to $0$ for others.

#### Common errors

1. Writing `(x : WithAbs v)` for an element `x : K`. The synonym is a structure, so there is no coercion of this kind. Write `WithAbs.toAbs v x`, and use `WithAbs.ofAbs` to go back.
2. Expecting a lemma about `WithAbs v` to apply to $K$ with its own norm. The two types have different norms, and the equivalence `WithAbs.equiv v` is only a ring isomorphism, not an isometry.
3. Defining the completion of $K$ at $v$ as `UniformSpace.Completion (WithAbs v)` and then looking for the lemmas of this section. They are stated for `AbsoluteValue.Completion v`. Pass between the two with `AbsoluteValue.Completion.isometryEquiv`.

### Exercises

1. (A) For the $p$-adic absolute value $v$ on $\mathbb{Q}$, compute the norm of `WithAbs.toAbs v (p ^ 2)` with `WithAbs.norm_toAbs_eq`.
2. (A) Show that `WithAbs.equiv v` sends $1$ to $1$ and is bijective.
3. (B) Show that the trivial absolute value on a field gives a discrete topology on `WithAbs v`.
4. (B) Use `WithAbs.tendsto_one_div_one_add_pow_nhds_one` to show that $1 / (1 + 3^n) \to 1$ in $\mathbb{Q}$ with the $3$-adic absolute value. Explain why the same sequence tends to $0$ for the usual absolute value.
5. (B) For $K = \mathbb{Q}$ and $L = \mathbb{Q}(i)$ with an absolute value $w$ that extends the usual one, show that the local degree $\operatorname{degree}(w)$ is $2$.
6. (C) Prove `AbsoluteValue.LiesOver.trans` from `AbsoluteValue.liesOver_iff` and the definition of `AbsoluteValue.under`.

### Reference

<?reference?>
