---
title: The separation quotient of a topological group
kind: api
modules:
  - Mathlib.Topology.Algebra.SeparationQuotient.Basic
  - Mathlib.Topology.Algebra.SeparationQuotient.FiniteDimensional
  - Mathlib.Topology.Algebra.SeparationQuotient.Hom
  - Mathlib.Topology.Algebra.SeparationQuotient.Section
explains:
  E2: [SeparationQuotient.instIsTopologicalGroup, SeparationQuotient.instIsUniformGroup, SeparationQuotient.mkCLM, SeparationQuotient.liftCLM, SeparationQuotient.liftContinuousMonoidHom, SeparationQuotient.outCLM, SeparationQuotient.mkCLM_comp_outCLM, SeparationQuotient.postcomp_mkCLM_surjective, SeparationQuotient.isEmbedding_outCLM]
  E1: auto
families: []
requires: [V07, V13.C01, V13.C04, V14.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The separation quotient of a topological group

### Overview

Two points $x$ and $y$ of a topological space are *inseparable* if they have the same neighbourhoods. The separation quotient `SeparationQuotient X` identifies inseparable points, and it is the largest $T_0$ quotient of $X$. Volume 13 describes it as a topological space. In a topological group, $x$ and $y$ are inseparable if and only if $x y^{-1}$ lies in the closure of $\{1\}$, so the separation quotient is the quotient by the closed normal subgroup $\overline{\{1\}}$. It is a Hausdorff group.

This section describes the algebra on the separation quotient. The group, ring, module and algebra structures go down to the quotient, the quotient map is a continuous homomorphism, and continuous maps that respect inseparability factor through it. For a vector space over a field, the quotient map has a continuous linear section. This lets a proof reduce a statement about a non-Hausdorff space to a statement about a Hausdorff one, as the proof of completeness of spaces of multilinear maps does.

### The library around it

#### Algebraic structures on the quotient

Each continuous algebraic operation respects inseparability, because a continuous map sends inseparable points to inseparable points. So each operation goes down to the quotient, and the module `Mathlib.Topology.Algebra.SeparationQuotient.Basic` gives the instances. The quotient map `SeparationQuotient.mk` is then a homomorphism, and the simp lemmas state this for each operation.

| Lean name | Statement |
|---|---|
| `SeparationQuotient.mk_mul` | $[x y] = [x] [y]$ |
| `SeparationQuotient.mk_add` | $[x + y] = [x] + [y]$ |
| `SeparationQuotient.mk_inv` | $[x^{-1}] = [x]^{-1}$ |
| `SeparationQuotient.mk_smul` | $[c \cdot x] = c \cdot [x]$ |
| `SeparationQuotient.mk_pow` | $[x^n] = [x]^n$ |
| `SeparationQuotient.mk_natCast` | $[n] = n$ for a natural number $n$ |
| `SeparationQuotient.mk_algebraMap` | $[\iota(r)] = \iota(r)$ for the algebra map $\iota$ |

The structures come from `Function.Surjective.group` and its relatives: a surjective map that respects the operations carries the laws to its image. So the separation quotient of a group is a group (`SeparationQuotient.instGroup`), of a commutative ring a commutative ring (`SeparationQuotient.instCommRing`), of a module a module (`SeparationQuotient.instModule`), and of an algebra an algebra (`SeparationQuotient.instAlgebra`). Each instance needs the matching continuity: `ContinuousMul` for a monoid, `IsTopologicalGroup` for a group, `IsTopologicalRing` for a ring and `ContinuousConstSMul` for a scalar action.

The topological classes also go down. The instances `SeparationQuotient.instIsTopologicalGroup`, `SeparationQuotient.instIsTopologicalRing` and `SeparationQuotient.instContinuousSMul` say that the quotient is again a topological group, ring and module. For a uniform group, `SeparationQuotient.instIsUniformGroup` says that the quotient is a uniform group. The proofs use that the quotient map is open and inducing.

#### The quotient map as a homomorphism

The library bundles the quotient map in several ways.

1. `SeparationQuotient.mkMonoidHom` and `SeparationQuotient.mkAddMonoidHom` are the quotient map as a monoid homomorphism.
2. `SeparationQuotient.mkRingHom` is the quotient map as a ring homomorphism.
3. `SeparationQuotient.mkCLM R M` is the quotient map as a continuous linear map `M →L[R] SeparationQuotient M`.

The universal property goes the other way. A continuous map $f$ that takes equal values at inseparable points factors through the quotient, by `SeparationQuotient.lift`. The module gives the bundled forms.

| Lean name | Statement |
|---|---|
| `SeparationQuotient.liftCLM` | a continuous semilinear map with $f x = f y$ for inseparable $x, y$ factors through the quotient |
| `SeparationQuotient.liftCLM_mk` | the factored map at $[x]$ is $f(x)$ |
| `SeparationQuotient.liftContinuousMonoidHom` | the same for continuous monoid homomorphisms of commutative monoids |
| `SeparationQuotient.liftContinuousAddMonoidHom` | the additive form |
| `SeparationQuotient.liftContinuousCommMonoidHom_mk` | the factored homomorphism at $[x]$ is $f(x)$ |

When the target is a $T_0$ space, each continuous map respects inseparability, so the hypothesis holds at once. In practice the hypothesis comes from `Inseparable.map`: a continuous map sends inseparable points to inseparable points, and inseparable points of a $T_0$ space are equal.

#### A continuous linear section

Let $E$ be a topological vector space over a division ring $K$. The quotient map $E \to E/{\sim}$ is a surjective linear map, so linear algebra gives a linear right inverse. The right inverse is continuous for free: the topology of $E$ is induced from the quotient, so a map $g$ into $E$ is continuous if and only if $\mathrm{mk} \circ g$ is continuous, and $\mathrm{mk} \circ g$ is the identity. The lemma `SeparationQuotient.exists_out_continuousLinearMap` gives the section, and `SeparationQuotient.outCLM K E` chooses one.

| Lean name | Statement |
|---|---|
| `SeparationQuotient.mkCLM_comp_outCLM` | the quotient map after the section is the identity |
| `SeparationQuotient.mk_outCLM` | $[\mathrm{out}(x)] = x$ |
| `SeparationQuotient.isEmbedding_outCLM` | the section is a topological embedding |
| `SeparationQuotient.outCLM_isUniformEmbedding` | for a uniform group, it is a uniform embedding |
| `SeparationQuotient.outCLM_injective` | the section is injective |
| `SeparationQuotient.postcomp_mkCLM_surjective` | each continuous linear map $F \to E/{\sim}$ lifts to a map $F \to E$ |

The section identifies $E$ with the product of the closure $\overline{\{0\}}$ and the Hausdorff space $E/{\sim}$, as a topological vector space. The closure of $\{0\}$ has the indiscrete topology, so it does not affect limits or continuity, only the uniqueness of limits.

The module `Mathlib.Topology.Algebra.SeparationQuotient.FiniteDimensional` has one result: the quotient of a finite module is a finite module (`SeparationQuotient.instModuleFinite`), because the quotient map is surjective and linear.

#### Use in proofs

A typical proof that uses the separation quotient has three steps. Assume first that the space is Hausdorff and prove the result there. Then pass from $E$ to $E/{\sim}$ with `SeparationQuotient.mkCLM`, which keeps the uniform structure up to a uniform inducing map. Then go back with the lift or the section. The tactic *wlog* fits this pattern: the proof of `ContinuousMultilinearMap.completeSpace` begins with *wlog hF : T2Space F* and uses the separation quotient of $F$ in the other case.

The pattern also works for statements about limits. A filter converges to $x$ in $E$ if and only if its image converges to $[x]$ in the quotient, because the topology of $E$ is induced from the quotient. So a statement about convergence, completeness or summability in $E$ is the same statement in $E/{\sim}$, and there limits are unique. The lemma `SeparationQuotient.isInducing_mk` records this property of the quotient map.

#### Common errors

1. `SeparationQuotient.liftCLM` asks for $f x = f y$ for each pair of inseparable points, not for the kernel condition $f(\overline{\{0\}}) = 0$. The two conditions are equivalent for a linear map, but the library takes the first form.
2. `SeparationQuotient.outCLM` needs a division ring of scalars. For a module over a general ring, the quotient map need not have a linear section.
3. The separation quotient is not the completion. A complete space need not be Hausdorff, and the completion `UniformSpace.Completion` of a space is Hausdorff and complete.

### Exercises

1. (A) Prove that a topological group $G$ is Hausdorff if and only if the quotient map to its separation quotient is injective.
2. (A) Use `SeparationQuotient.mk_mul` and `SeparationQuotient.mk_inv` to show that the quotient map is a group homomorphism.
3. (B) Show that two points of a topological group are inseparable if and only if their quotient $x y^{-1}$ lies in the closure of $\{1\}$.
4. (B) Give a continuous linear functional on $\mathbb{R}^2$ with the topology induced by $(x, y) \mapsto x$, and factor it through the separation quotient with `SeparationQuotient.liftCLM`.
5. (C) Prove that a topological vector space $E$ over $\mathbb{R}$ is isomorphic, as a topological vector space, to the product of the closure of $\{0\}$ and its separation quotient, with `SeparationQuotient.outCLM`.

### Reference

<?reference?>
