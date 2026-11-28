---
title: Locally constant functions and discrete quotients
kind: api
modules:
  - Mathlib.Topology.LocallyConstant.Basic
  - Mathlib.Topology.LocallyConstant.Algebra
  - Mathlib.Topology.DiscreteQuotient
  - Mathlib.Topology.FiberPartition
  - Mathlib.Topology.ExtremallyDisconnected
explains:
  E2: [IsLocallyConstant.iff_isOpen_fiber, IsLocallyConstant.apply_eq_of_isPreconnected, IsLocallyConstant.range_finite, LocallyConstant.equivClopens, LocallyConstant.lift_comp_proj, DiscreteQuotient.instFiniteQuotientOfCompactSpace, DiscreteQuotient.exists_of_compat, CompactT2.projective_iff_extremallyDisconnected]
  E1: auto
families: []
requires: [V01, V04, V13.C01, V13.C02, V13.C04, V13.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Locally constant functions and discrete quotients

### Overview

A function is locally constant if each point has a neighbourhood on which the function is constant. On a connected space such a function is constant; this is a restatement of connectedness that Section 1 uses for the intermediate value theorem. On a space with many clopen sets, such as the Cantor set or the $p$-adic integers, the locally constant functions are many, and they carry the topology: a clopen set is the same thing as a locally constant function with values in $\{0, 1\}$.

This section describes the library of locally constant functions: the predicate `IsLocallyConstant`, the bundled type `LocallyConstant X Y` and its algebraic structure. It then describes the discrete quotients of a space, the quotients by equivalence relations with open classes. In a compact space each discrete quotient is finite, and the space maps onto the limit of its discrete quotients. This is the start of the theory of profinite spaces. The section ends with extremally disconnected spaces, which are the projective objects among compact Hausdorff spaces. It needs connectedness from Section 1, the separation axioms of Chapter 4 and compactness of Chapter 5.

### The library around it

#### The predicate

The predicate `IsLocallyConstant f` for $f : X \to Y$ says that the preimage of each subset of $Y$ is open. No topology on $Y$ is needed. The theorem `IsLocallyConstant.tfae` collects the usual forms: each point has a neighbourhood on which $f$ is constant (`IsLocallyConstant.iff_eventually_eq`), $f$ is eventually constant at each point, each set $\{x' : f(x') = f(x)\}$ is open, and each fibre $f^{-1}(y)$ is open. The last form is `IsLocallyConstant.iff_isOpen_fiber`. Its proof is one line: a preimage $f^{-1}(s)$ is the union of the fibres $f^{-1}(y)$ for $y \in s$, and a union of open sets is open. Since the complement of a fibre is a union of fibres, each fibre is clopen (`IsLocallyConstant.isClopen_fiber`).

A locally constant function is continuous for each topology on $Y$ (`IsLocallyConstant.continuous`). When $Y$ is discrete the converse holds (`IsLocallyConstant.iff_continuous`). Each function on a discrete space is locally constant (`IsLocallyConstant.of_discrete`).

The two main results connect the predicate with connectedness and with compactness.

- `IsLocallyConstant.apply_eq_of_isPreconnected`: $f$ is constant on each preconnected set. For $x \in s$, the fibre $f^{-1}(f(x))$ is clopen, so it splits $s$ into two relatively open parts, and preconnectedness says that it contains all of $s$. The forms `IsLocallyConstant.iff_is_const` and `IsLocallyConstant.exists_eq_const` are the statements for a preconnected space.
- `IsLocallyConstant.range_finite`: on a compact space, $f$ takes finitely many values. The fibres form an open cover by disjoint sets, so a finite subcover is the whole cover.

In a locally connected space the converse of the first result holds: a function that is constant on each connected component is locally constant (`IsLocallyConstant.of_constant_on_connected_components`).

The predicate is closed under the operations that act on values. If $f$ is locally constant, so is $g \circ f$ for each $g$ (`IsLocallyConstant.comp`), and if $f$ and $g$ are locally constant, so is $x \mapsto h(f(x), g(x))$ (`IsLocallyConstant.comp₂`), since each point has a common neighbourhood. The lemmas `IsLocallyConstant.add`, `IsLocallyConstant.mul`, `IsLocallyConstant.inv` and their companions are the special cases. Composition with a continuous map on the right is `IsLocallyConstant.comp_continuous`.

#### The bundled type

The type `LocallyConstant X Y` is the structure of a function and a proof that it is locally constant. It has a coercion to functions (`LocallyConstant.instFunLike`), so `LocallyConstant.ext` and `LocallyConstant.coe_injective` reduce equality to pointwise equality. When $Y$ has a topology, `LocallyConstant.toContinuousMap` gives the continuous map, with the coercion lemma `LocallyConstant.coe_continuousMap`. The constructors and operations follow one pattern.

| Lean name | Statement |
|---|---|
| `LocallyConstant.const X y` | the constant function with value $y$ |
| `LocallyConstant.map g f` | $g \circ f$, for any $g : Y \to Z$ |
| `LocallyConstant.comap f g` | $g \circ f$, for a continuous $f : X \to Y$ |
| `LocallyConstant.desc` | $f$ from a locally constant $g \circ f$ with $g$ injective |
| `LocallyConstant.ofIsClopen` | the indicator of a clopen set, with values in `Fin 2` |
| `LocallyConstant.indicator` | $f$ on a clopen $U$ and $0$ outside |
| `LocallyConstant.piecewise` | glue functions on two closed sets that cover $X$ |
| `LocallyConstant.flip`, `LocallyConstant.unflip` | swap the arguments of a function of two variables |
| `LocallyConstant.congrLeft` | a homeomorphism $X \simeq Y$ gives an equivalence of function types |

The function `LocallyConstant.ofIsClopen` and the fibre of $0$ give a bijection between locally constant functions with values in `Fin 2` and clopen sets. This is `LocallyConstant.equivClopens`, an equivalence with `TopologicalSpace.Clopens X`. Its inverse sends $f$ to $f^{-1}(0)$, which is clopen by `IsLocallyConstant.isClopen_fiber`, and `LocallyConstant.locallyConstant_eq_of_fiber_zero_eq` says that this fibre determines $f$.

The module `Mathlib.Topology.LocallyConstant.Algebra` puts the algebraic structure of $Y$ on `LocallyConstant X Y`, pointwise. If $Y$ is a monoid, a group, a ring or an $R$-algebra, then so is `LocallyConstant X Y`, by instances such as `LocallyConstant.instCommRing` and `LocallyConstant.instAlgebra`. The simp lemmas `LocallyConstant.coe_mul`, `LocallyConstant.coe_add` and the like push the coercion inside, and `LocallyConstant.mul_apply` evaluates. The maps of the previous table come in bundled forms with a suffix for the kind of morphism: `LocallyConstant.comapRingHom`, `LocallyConstant.comapₗ`, `LocallyConstant.comapₐ`, `LocallyConstant.mapRingHom`, `LocallyConstant.evalRingHom`, `LocallyConstant.constRingHom`, `LocallyConstant.coeFnRingHom` and `LocallyConstant.congrLeftRingEquiv`. The pattern is `MonoidHom`, `AddMonoidHom`, `RingHom`, `ₗ` for linear maps and `ₐ` for algebra maps. The function `LocallyConstant.charFn Y hU` is the characteristic function of a clopen set $U$, with values $0$ and $1$ in $Y$, and `LocallyConstant.charFn_inj` says that it determines $U$. The lemma `LocallyConstant.ker_comapₗ` says that pullback along a continuous surjection is injective.

#### Discrete quotients

A *discrete quotient* of $X$ is an equivalence relation on $X$ whose classes are open. The structure `DiscreteQuotient X` extends `Setoid X` with the field `DiscreteQuotient.isOpen_setOfPred_rel`. The quotient type has the quotient topology, and it is discrete (`DiscreteQuotient.instDiscreteTopologyQuotient`). The projection `DiscreteQuotient.proj` is continuous, surjective, a quotient map and locally constant (`DiscreteQuotient.proj_isLocallyConstant`). The classes are clopen: the complement of a class is the union of the other classes.

Discrete quotients and locally constant functions are two views of the same thing. Each locally constant $f$ has the discrete quotient `LocallyConstant.discreteQuotient f`, whose classes are the fibres, and $f$ factors through it: `LocallyConstant.lift f` is the induced function on the quotient, and `LocallyConstant.lift_comp_proj` says $\mathrm{lift}(f) \circ \mathrm{proj} = f$. Conversely, the projection of a discrete quotient is locally constant. A clopen set $A$ gives the discrete quotient `DiscreteQuotient.ofIsClopen` with the two classes $A$ and $A^c$.

The discrete quotients form a partial order: $A \le B$ when the relation of $A$ implies the relation of $B$, so $A$ is finer. There is a top element, with one class (`DiscreteQuotient.instOrderTop`), and the order is a meet semilattice (`DiscreteQuotient.instSemilatticeInf`). A bottom element exists when the space is locally connected (`DiscreteQuotient.instOrderBotOfLocallyConnectedSpace`), and then its classes are the connected components. For $A \le B$ the map `DiscreteQuotient.ofLE` goes from the quotient by $A$ to the quotient by $B$, with `DiscreteQuotient.ofLE_proj`. A continuous map $f : X \to Y$ pulls a discrete quotient back (`DiscreteQuotient.comap`), and when $A$ is finer than the pullback of $B$ (`DiscreteQuotient.LEComap f A B`) the map `DiscreteQuotient.map` is induced on the quotients, with `DiscreteQuotient.map_proj`.

On a compact space each discrete quotient is finite (`DiscreteQuotient.instFiniteQuotientOfCompactSpace`): the classes are an open cover by disjoint sets. The main theorem of the module is `DiscreteQuotient.exists_of_compat`. Let $X$ be compact, and choose for each discrete quotient $Q$ a class $c_Q$, such that $\mathrm{ofLE}(c_A) = c_B$ whenever $A \le B$. Then there is a point $x$ with $\mathrm{proj}_Q(x) = c_Q$ for each $Q$. In other words, the map from $X$ to the inverse limit of its finite discrete quotients is surjective. The proof is the finite intersection property: the classes $c_Q$ are closed, and finitely many of them meet, because a common refinement of $Q_1, \dots, Q_n$ has a class inside all of them. The module also gives the finite set of clopen classes `DiscreteQuotient.finsetClopens`, and `DiscreteQuotient.equivFinsetClopens` identifies a discrete quotient of a compact space with its finite partition into clopen sets.

The small module `Mathlib.Topology.FiberPartition` treats the fibres of a function $f : S \to Y$ as the subspaces of $S$ indexed by `Function.Fiber f`. The map `TopologicalSpace.Fiber.sigmaIsoHom f` is the continuous map from the disjoint union of the fibres to $S$, and `TopologicalSpace.Fiber.sigmaIsoHom_inj` and `TopologicalSpace.Fiber.sigmaIsoHom_surj` say that it is a bijection. For a locally constant function on a compact space there are finitely many fibres (`TopologicalSpace.Fiber.instFiniteFiberCoeLocallyConstant`). The category theory of profinite spaces uses this decomposition.

#### Extremally disconnected spaces

A space is *extremally disconnected* if the closure of each open set is open. The class is `ExtremallyDisconnected X`, with the field `ExtremallyDisconnected.open_closure`. An equivalent form is that disjoint open sets have disjoint closures (`ExtremallyDisconnected.disjoint_closure_of_disjoint_isOpen`). A Hausdorff extremally disconnected space is totally separated (`instTotallySeparatedSpaceOfExtremallyDisconnectedOfT2Space`), because the closure of an open set is a clopen set. A preirreducible space is extremally disconnected (`instExtremallyDisconnectedOfPreirreducibleSpace`), since there the closure of a nonempty open set is the whole space. The class passes along homeomorphisms (`extremallyDisconnected_of_homeo`) and to disjoint unions.

A compact Hausdorff space $X$ is *projective* if each continuous map $X \to Z$ lifts along each continuous surjection $Y \to Z$ of compact Hausdorff spaces. The predicate is `CompactT2.Projective X`. The theorem `CompactT2.projective_iff_extremallyDisconnected`, says that a compact Hausdorff space is projective if and only if it is extremally disconnected. The two directions are `CompactT2.ExtremallyDisconnected.projective` and `CompactT2.Projective.extremallyDisconnected`. The proof of the hard direction uses `exists_compact_surjective_zorn_subset`: a continuous surjection from a compact space onto a $T_1$ space restricts to a compact subspace of the source that still maps onto the target and is minimal for this property. Over an extremally disconnected target such a minimal map is a homeomorphism (`ExtremallyDisconnected.homeoCompactToT2`). The Stone-Čech compactification of a discrete space is projective (`StoneCech.projective`).

#### Common errors

1. `IsLocallyConstant f` is not the same as continuity when $Y$ is not discrete. A continuous function into $\mathbb{R}$ is locally constant only on special spaces, so a proof that goes from continuity to local constancy needs `IsLocallyConstant.iff_continuous` and a `DiscreteTopology` instance.
2. The order on `DiscreteQuotient X` goes from fine to coarse: $A \le B$ means that $A$ is finer than $B$. The top element is the quotient with one class, not the identity relation.
3. `LocallyConstant.comap` takes a bundled continuous map `C(X, Y)`, not a bare function. Write `LocallyConstant.comap ⟨f, hf⟩ g`, or use the bundled map if it exists.

### Exercises

1. (A) Prove that a locally constant function on $[0, 1]$ is constant, with `IsLocallyConstant.apply_eq_of_isPreconnected`.
2. (A) Show that a function $f : X \to Y$ is locally constant if and only if each fibre is clopen.
3. (B) Prove that a locally constant function on a compact space takes finitely many values, and use it to show that a compact discrete space is finite.
4. (B) Describe the discrete quotients of the Cantor set $\{0,1\}^{\mathbb{N}}$ given by the first $n$ coordinates, and show that each discrete quotient is coarser than one of them.
5. (B) Show that the locally constant functions $X \to \mathbb{Z}$ form a ring, and that it has no idempotents other than $0$ and $1$ when $X$ is connected.
6. (C) Prove that an extremally disconnected Hausdorff space has no nontrivial convergent sequences: a sequence of distinct points cannot converge.

### Reference

<?reference?>
