---
title: Partial equivalences
kind: api
modules:
  - Mathlib.Logic.Equiv.PartialEquiv
  - Mathlib.Basic.PEquiv
  - Mathlib.Data.PEquiv
explains:
  E2: [PartialEquiv.trans_source, PartialEquiv.image_source_eq_target, PartialEquiv.self_trans_symm, PartialEquiv.trans_symm_eq_symm_trans_symm, PEquiv.trans_eq_some, PEquiv.self_trans_symm, PEquiv.single_trans_single]
  E1: auto
families: []
requires: [V01.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Partial equivalences

### Overview

An equivalence `α ≃ β` is a bijection between two whole types. Many constructions need a bijection between a subset $s \subseteq \alpha$ and a subset $t \subseteq \beta$. A chart of a manifold is a bijection between an open set of the manifold and an open set of $\mathbb{R}^n$. A permutation matrix with some zero rows is a bijection between some rows and some columns. Mathlib has two structures for these objects, and this section treats both.

1. A *partial equivalence* `PartialEquiv α β` stores two total functions $f : \alpha \to \beta$ and $g : \beta \to \alpha$ and two sets, the *source* $s$ and the *target* $t$. On $s$ and $t$ the functions are inverse bijections. Outside these sets the values of $f$ and $g$ are junk values with no meaning. This is the form that topology and geometry use.
2. A *partial equivalence with options* `α ≃. β` (the structure `PEquiv`) stores two functions $\alpha \to \mathrm{Option}\ \beta$ and $\beta \to \mathrm{Option}\ \alpha$. The value `none` marks a point where the map is undefined. There are no junk values, and the domain is part of the function. This is the form that combinatorics and matrices use.

Both structures generalize `Equiv` from the earlier sections of this chapter. Both have an identity, an inverse and a composition, and both use the sets and images of Chapter 2.

### The library around it

#### The structure `PartialEquiv`

The module `Mathlib.Logic.Equiv.PartialEquiv` defines `PartialEquiv α β` with the fields `toFun`, `invFun`, `source`, `target` and four proofs:

1. `map_source'`: $x \in s \Rightarrow f(x) \in t$;
2. `map_target'`: $y \in t \Rightarrow g(y) \in s$;
3. `left_inv'`: $x \in s \Rightarrow g(f(x)) = x$;
4. `right_inv'`: $y \in t \Rightarrow f(g(y)) = y$.

A partial equivalence `e` acts as a function by a coercion, and the inverse is `e.symm`, with source and target exchanged (`PartialEquiv.symm_source`). The simp normal form is `e x` and `e.symm y`, never `e.toFun x` or `e.invFun y`. The lemmas without a prime, `PartialEquiv.map_source`, `PartialEquiv.left_inv` and the others, state the four fields in this normal form. In the language of the sets of Chapter 2, the fields say that `e` maps $s$ to $t$ (`PartialEquiv.mapsTo`), that `e.symm` is a left inverse on $s$ (`PartialEquiv.leftInvOn`), and together that `e` is a bijection from $s$ to $t$ (`PartialEquiv.bijOn`).

**Theorem.** For a partial equivalence $e$ with source $s$ and target $t$, the image $e(s)$ is $t$.

*Proof.* The field `map_source'` gives $e(s) \subseteq t$. For $y \in t$, the point $x = e^{-1}(y)$ is in $s$ by `map_target'`, and $e(x) = y$ by `right_inv'`. So $t \subseteq e(s)$. $\square$

This is `PartialEquiv.image_source_eq_target`. The library has many variants of it for subsets of the source and of the target: `PartialEquiv.image_source_inter_eq`, `PartialEquiv.symm_image_target_eq_source`, `PartialEquiv.source_inter_preimage_inv_preimage` and others. They let a proof move a set across $e$ while it stays inside the source.

**Extensionality.** Two partial equivalences are equal when their functions, their inverse functions and their sources agree (`PartialEquiv.ext`). The functions must agree at all points, also outside the source, because the junk values are part of the data. This is too strong for most uses. The weaker relation is `PartialEquiv.EqOnSource`: $e \approx e'$ when the sources are equal and the functions agree on the source. It is an equivalence relation, the instance `PartialEquiv.eqOnSourceSetoid`, with the notation `e ≈ e'`. Then `PartialEquiv.EqOnSource.target_eq` and `PartialEquiv.EqOnSource.symm'` show that the target and the inverse agree as well.

#### Constructions

The library builds partial equivalences in several ways.

| Lean name | Source | Target |
|---|---|---|
| `PartialEquiv.refl α` | all of $\alpha$ | all of $\alpha$ |
| `PartialEquiv.ofSet s` | $s$, with the identity | $s$ |
| `Equiv.toPartialEquiv e` | all of $\alpha$ | all of $\beta$ |
| `PartialEquiv.single a b` | $\{a\}$ | $\{b\}$ |
| `Set.BijOn.toPartialEquiv f s t h` | $s$ | $t$ |
| `Set.InjOn.toPartialEquiv f s h` | $s$ | $f(s)$ |
| `e.restr s` | $e.\mathrm{source} \cap s$ | $e.\mathrm{target} \cap e^{-1}(s)$ |
| `e.prod e'` | $s \times s'$ | $t \times t'$ |
| `PartialEquiv.pi e` | $\prod_i s_i$ | $\prod_i t_i$ |
| `e.toEquiv` | an equivalence `↑e.source ≃ ↑e.target` | |

The two constructions from `Set.BijOn` and `Set.InjOn` need `Nonempty α`. The inverse function must have a value at every point of $\beta$, also outside the target, and a nonempty type gives a junk value there. The inverse is `Function.invFunOn`, which uses choice.

A pair of sets $(s', t')$ is an *image pair* for $e$ when $x \in s'$ is equivalent to $e(x) \in t'$ for every $x$ in the source. This is `PartialEquiv.IsImage e s' t'`. The relation is stable under complement, intersection, union and difference (`PartialEquiv.IsImage.compl`, `PartialEquiv.IsImage.inter`, `PartialEquiv.IsImage.union`, `PartialEquiv.IsImage.diff`), and under inverse (`PartialEquiv.IsImage.symm_iff`). An image pair gives a restriction `PartialEquiv.IsImage.restr` with source $s \cap s'$ and target $t \cap t'$. Two partial equivalences with the same image pair can be glued by `PartialEquiv.piecewise`: the result follows $e$ on $s'$ and $e'$ outside $s'$. When the sources and the targets are disjoint, `PartialEquiv.disjointUnion` glues them with no image pair.

#### Composition

The composite `e.trans e'` of `e : PartialEquiv α β` and `e' : PartialEquiv β γ` has the function $e' \circ e$ (`PartialEquiv.trans_apply`). Its source is the largest set where the composite makes sense.

**Theorem.** The source of `e.trans e'` is $e.\mathrm{source} \cap e^{-1}(e'.\mathrm{source})$, and its target is $e'.\mathrm{target} \cap e'^{-1}(e.\mathrm{target})$.

*Proof sketch.* A point $x$ has a meaningful image under $e' \circ e$ when $x$ is in the source of $e$ and $e(x)$ is in the source of $e'$. On this set, $e$ is a bijection onto $e.\mathrm{target} \cap e'.\mathrm{source}$, and $e'$ is a bijection from this set onto the stated target. The definition builds the composite as `PartialEquiv.trans'` of the two restrictions to $e.\mathrm{target} \cap e'.\mathrm{source}$. The formula for the target is the formula for the source applied to the inverse. $\square$

The two formulas are `PartialEquiv.trans_source` and `PartialEquiv.trans_target`. The primed forms `PartialEquiv.trans_source'` and `PartialEquiv.trans_source''` write the source with $e.\mathrm{target} \cap e'.\mathrm{source}$. The inverse of a composite is the composite of the inverses in the reverse order (`PartialEquiv.trans_symm_eq_symm_trans_symm`). Composition is associative (`PartialEquiv.trans_assoc`), and `PartialEquiv.refl` is a unit on both sides (`PartialEquiv.refl_trans`, `PartialEquiv.trans_refl`).

An inverse is only an inverse up to `≈`. The composite $e \cdot e^{-1}$ is the identity on the source, not on all of $\alpha$.

**Theorem.** `e.trans e.symm ≈ PartialEquiv.ofSet e.source`.

*Proof.* By the theorem on composition, the source of $e \cdot e^{-1}$ is $s \cap e^{-1}(t)$. This is $s$, because $e$ maps $s$ into $t$. The source of `ofSet s` is $s$ as well. For $x \in s$, the composite sends $x$ to $e^{-1}(e(x)) = x$, and `ofSet s` sends $x$ to $x$. $\square$

This is `PartialEquiv.self_trans_symm`, and `PartialEquiv.symm_trans_self` is the same for the target. So the partial equivalences form a groupoid only up to the relation `≈`, and `PartialEquiv.EqOnSource.trans'` states that composition respects `≈`. Other useful identities are `PartialEquiv.trans_ofSet`, which states that composition with `ofSet s` is the restriction to $e^{-1}(s)$, and `PartialEquiv.restr_trans`. The composition with an equivalence on one side has the special forms `PartialEquiv.transEquiv` and `Equiv.transPartialEquiv`, with simpler formulas for source and target.

The tactic `mfld_set_tac` proves equalities and inclusions of sources and targets. It unfolds the definitions with the simp set `mfld_simps` and then argues element by element. The lemmas of the module carry the attribute `mfld_simps`, so the same simp set computes most sources and targets.

#### The structure `PEquiv`

The module `Mathlib.Basic.PEquiv` defines `PEquiv α β`, with the notation `α ≃. β`. The fields are `toFun : α → Option β`, `invFun : β → Option α` and one law: $g(b) = \mathrm{some}\ a$ if and only if $f(a) = \mathrm{some}\ b$. So the graph of $f$ and the graph of $g$ are the same set of pairs, read in the two directions. The membership form of the law is `PEquiv.mem_iff_mem : a ∈ f.symm b ↔ b ∈ f a`, where `b ∈ o` for an option means $o = \mathrm{some}\ b$. A `PEquiv` acts as a function `α → Option β`, and two of them are equal when they agree at every point (`PEquiv.ext`). Here no junk value exists, so the plain extensionality is the right one.

The basic constructions are `PEquiv.refl`, `PEquiv.symm`, `PEquiv.trans`, `Equiv.toPEquiv`, `PEquiv.ofSet s` (the identity on $s$ and undefined outside, for a decidable $s$), and `PEquiv.single a b`, which sends $a$ to $b$ and is undefined elsewhere. The composite `f.trans g` sends $a$ to `(f a).bind g`.

**Theorem.** `(f.trans g) a = some c` if and only if there is $b$ with $f(a) = \mathrm{some}\ b$ and $g(b) = \mathrm{some}\ c$.

*Proof.* The value $f(a)$ is `none` or `some b`. In the first case the bind is `none`, and no $b$ exists. In the second case the bind is $g(b)$, and the witness is this $b$. $\square$

This is `PEquiv.trans_eq_some`, and `PEquiv.mem_trans` is the form with `∈`. The algebra is the same as for `PartialEquiv`, with equalities in place of `≈`: `PEquiv.trans_assoc`, `PEquiv.refl_trans`, `PEquiv.trans_refl`, `PEquiv.symm_symm` and `PEquiv.symm_trans_rev`. The composite with the inverse is the identity on the domain: `PEquiv.self_trans_symm` states `f.trans f.symm = PEquiv.ofSet {a | (f a).isSome}`. The proof is a case split on $f(a)$: if $f(a) = \mathrm{some}\ b$, then $f^{-1}(b) = \mathrm{some}\ a$ by the law; if $f(a) = \mathrm{none}$, then the composite and `PEquiv.ofSet` are both undefined at $a$. So `f.trans f.symm = PEquiv.refl α` holds exactly when $f$ is defined everywhere (`PEquiv.trans_symm_eq_iff_forall_isSome`).

The elements `PEquiv.single` compose as matrix units do. The composite of `single a b` and `single b c` is `single a c` (`PEquiv.single_trans_single`), and the composite of `single a b₁` and `single b₂ c` with $b_1 \neq b_2$ is `⊥` (`PEquiv.single_trans_single_of_ne`). Here `⊥` is the partial equivalence that is undefined everywhere (`PEquiv.bot_apply`). The type `α ≃. β` has a partial order, the inclusion of graphs (`PEquiv.le_def`), with `⊥` as its least element. With decidable equality on both sides it is a meet semilattice, the instance `PEquiv.instSemilatticeInfOfDecidableEq`. The function `PEquiv.toMatrix`, in the module `Mathlib.Data.Matrix.PEquiv`, turns a partial equivalence into a matrix of zeros and ones, and the rules for `PEquiv.single` become the rules for the product of matrix units.

The module `Mathlib.Data.PEquiv` is a deprecated module that only imports `Mathlib.Basic.PEquiv`, and it has no declarations of its own.

#### Common errors

1. A learner proves `e.trans e.symm = PartialEquiv.refl α` for a partial equivalence. The statement is false when the source is not all of $\alpha$. The true statement is `PartialEquiv.self_trans_symm`, with `≈` and `ofSet e.source`.
2. A learner applies `PartialEquiv.ext` and must then prove an equality of junk values outside the source. Use `PartialEquiv.EqOnSource` when only the values on the source matter.
3. A learner writes `e.toFun x` in a statement, and simp lemmas do not apply. The simp normal form is `e x`, and `PartialEquiv.coe_mk` turns a structure literal into this form.

### Exercises

1. (A) Compute the source and the target of `(PartialEquiv.single a b).trans (PartialEquiv.single b c)` and of `(PartialEquiv.single a b).trans (PartialEquiv.single b' c)` for $b \neq b'$.
2. (A) Prove that `PEquiv.single a b` composed with its inverse is `PEquiv.ofSet {a}`, from `PEquiv.self_trans_symm`.
3. (B) Prove `PartialEquiv.trans_symm_eq_symm_trans_symm` from the formulas for the source and the target of a composite.
4. (B) Let $e$ be the partial equivalence $x \mapsto x^2$ from $(0, \infty)$ to $(0, \infty)$, with the inverse $y \mapsto \sqrt{y}$. Compute the source of `e.trans e` and of `e.restr (Set.Ioo 0 1)`.
5. (B) Prove that a `PEquiv` that is defined at every point is injective, as `PEquiv.injective_of_forall_isSome` states.
6. (C) Prove that `e.trans e.symm = PartialEquiv.refl α` holds, as an equality and not only up to `≈`, if and only if the source of $e$ is all of $\alpha$.

### Reference

<?reference?>
