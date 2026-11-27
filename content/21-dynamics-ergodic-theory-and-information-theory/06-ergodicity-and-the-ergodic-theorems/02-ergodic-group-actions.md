---
title: Ergodic group actions
kind: theory
modules:
  - Mathlib.Dynamics.Ergodic.Action.Basic
  - Mathlib.Dynamics.Ergodic.Action.OfMinimal
  - Mathlib.Dynamics.Ergodic.Action.Regular
explains:
  E3: [ErgodicSMul, MeasureTheory.ergodicSMul_iterateMulAct, MeasureTheory.aeconst_of_forall_smul_ae_eq, aeconst_of_dense_aestabilizer_smul, ergodic_smul_of_denseRange_zpow, ergodic_mul_left_iff_denseRange_zpow, MonoidHom.ergodic_of_dense_iUnion_preimage_one]
  E2: [ErgodicVAdd, ergodicSMul_iff, ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq, MeasureTheory.aeconst_of_forall_preimage_smul_ae_eq, MulAction.aeconst_of_aestabilizer_eq_top, ErgodicSMul.of_aestabilizer, aeconst_of_dense_setOfPred_preimage_smul_ae, aeconst_of_dense_setOfPred_preimage_smul_eq, ergodic_smul_of_denseRange_pow, ErgodicSMul.trans_isMinimal, DenseRange.zpow_of_ergodic_mul_left, ergodic_mul_left_of_denseRange_zpow, ergodic_mul_left_of_denseRange_pow, ergodic_add_left_iff_denseRange_zsmul, MonoidHom.preErgodic_of_dense_iUnion_preimage_one, AddMonoidHom.ergodic_of_dense_iUnion_preimage_zero, instErgodicSMulOfIsMulLeftInvariant, instErgodicSMulMulOppositeOfIsMulRightInvariant]
  E1: auto
families: []
requires: [V05, V14, V18, V21.C03, V21.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Ergodic group actions

### Overview

An action of any monoid is ergodic if every set that all the elements keep fixed up to a null set is trivial. The main tool of the library says that a set almost invariant under a dense set of elements is almost invariant under all of them. From it come the ergodicity of a translation $x \mapsto gx$ of a compact group with dense powers, and of surjective endomorphisms with a dense union of kernels.

### Definitions

Let a monoid $M$ act on a measurable space $X$ with a measure $\mu$, and write $g \cdot x$ for the action.

**Definition (Ergodic action).** The action is *ergodic* if $\mu$ is invariant under each map $x \mapsto g \cdot x$, and every measurable set $s$ with $(g \cdot)^{-1}(s) = s$ almost everywhere for all $g \in M$ is null or conull.

::: mathlib
`ErgodicSMul` · `Mathlib.Dynamics.Ergodic.Action.Basic`

`ErgodicSMul G α μ` is a class that extends `SMulInvariantMeasure G α μ` with the field `aeconst_of_forall_preimage_smul_ae_eq : MeasurableSet s → (∀ g, (g • ·) ⁻¹' s =ᵐ[μ] s) → EventuallyEmptyOrUniv s (ae μ)`. The additive class is `ErgodicVAdd`; `ergodicSMul_iff` unfolds it.

<?decl ErgodicSMul?>
:::

For a group $G$, the *almost everywhere stabilizer* of $s$ is the subgroup $\{g : g s = s \text{ a.e.}\}$.

### Theorems and proofs

**Proposition (Maps as actions).** Let $f$ be measurable and let $\mathbb{N}$ act by $n \cdot x = f^n(x)$. The action is ergodic if and only if $f$ is ergodic.

*Proof.* The measure is invariant under all $f^n$ if and only if it is invariant under $f$. If $f^{-1}(s) = s$ a.e., then $f^{-n}(s) = s$ a.e. by induction, since measure preserving preimages keep a.e. equality. $\square$

**Lemma (Closed stabilizer).** Let $X$ be a metric space with a finite Borel measure $\mu$, inner regular for compact sets, and let a topological space $M$ act on $X$ by a continuous map $(g, x) \mapsto g \cdot x$ such that each $x \mapsto g \cdot x$ preserves $\mu$. For measurable $s$, the set $S = \{g : (g\cdot)^{-1}(s) = s \text{ a.e.}\}$ is closed.

*Proof.* Write $\|u\| = \int |u|\,d\mu$ and $u_g(x) = u(g \cdot x)$. Then $\|u_g\| = \|u\|$, and $\|(1_s)_g - 1_s\| = \mu((g\cdot)^{-1}(s) \triangle s)$.

Let $\delta > 0$. Take compact $K \subseteq s$ with $\mu(s \setminus K) < \delta$. The sets $K_r = \{x : d(x, K) < r\}$ decrease to the closed set $K$, so $\mu(K_r \setminus K) < \delta$ for small $r$. With $\varphi(x) = \max(0, 1 - d(x, K)/r)$, which is continuous, equal to $1$ on $K$ and $0$ off $K_r$, $\|1_s - \varphi\| < 2\delta$.

Take compact $L$ with $\mu(X \setminus L) < \delta$. The function $(h, x) \mapsto \varphi(h \cdot x)$ is continuous, so each $x \in L$ has open sets $W_x \ni g$ and $N_x \ni x$ with $|\varphi(h \cdot y) - \varphi(g \cdot y)| < \delta$ for $h \in W_x$, $y \in N_x$. Finitely many $N_x$ cover $L$. Let $W$ be the intersection of the matching $W_x$. For $h \in W$, $\|\varphi_h - \varphi_g\| \le \delta\mu(X) + \mu(X \setminus L) \le \delta(\mu(X) + 1)$.

Let $g$ be in the closure of $S$ and take $h \in W \cap S$. Then $(1_s)_h = 1_s$ a.e., and
$$\|(1_s)_g - 1_s\| \le \|(1_s - \varphi)_g\| + \|\varphi_g - \varphi_h\| + \|(\varphi - 1_s)_h\| \le 4\delta + \delta(\mu(X) + 1).$$
As $\delta$ is arbitrary, $g \in S$. $\square$

**Corollary (Dense stabilizer).** If also the action is ergodic and $S$ is dense, then $s$ is null or conull, because $S = M$.

**Theorem (Dense powers).** Under the same hypotheses, let $M$ be a monoid and $g \in M$ with $\{g^n : n \in \mathbb{N}\}$ dense. Then $x \mapsto g \cdot x$ is ergodic.

*Proof.* Let $s$ be measurable with $(g\cdot)^{-1}(s) = s$ a.e. Since $g^{n+1} \cdot x = g \cdot (g^n \cdot x)$, induction gives $(g^n\cdot)^{-1}(s) = s$ a.e. for all $n$. So $S$ contains the dense set of powers, and the corollary applies. $\square$

**Theorem (Translations).** Let $G$ be a second countable Hausdorff topological group, so that $G$ is metrizable, and $\mu$ a nonzero finite left invariant Borel measure, inner regular for compact sets. Then $x \mapsto gx$ is ergodic if and only if the subgroup $\langle g \rangle$ is dense.

*Proof.* Every nonempty open $U$ has $\mu(U) > 0$: for compact $K$ with $\mu(K) > 0$, finitely many translates $hU$ cover $K$.

Suppose $\langle g \rangle$ is dense. The action of $G$ on itself by left multiplication is ergodic: let $s$ satisfy $hs = s$ a.e. for all $h$, and set $C = \{(h, y) : y \in s,\ hy \notin s\}$. Each section $C_h = s \setminus h^{-1}s$ is null, so $C$ is null for $\mu \otimes \mu$. By Fubini, for a.e. $y \in s$ the section $\{h : hy \notin s\} = (G \setminus s)y^{-1}$ is null. Right translation by $y^{-1}$ is quasi measure preserving for a left invariant measure, so if $\mu(s) > 0$ then $\mu(G \setminus s) = 0$. Now let $gs = s$ a.e. Since $g^{-1}$ also preserves $\mu$, $g^n s = s$ a.e. for all $n \in \mathbb{Z}$, so the a.e. stabilizer of $s$ is dense, and the corollary makes $s$ trivial.

Conversely, suppose that $H = \overline{\langle g \rangle} \ne G$. Take $x \notin H$. Since $G \setminus H$ is open, there is a symmetric open $W \ni 1$ with $xW \cap H = \emptyset$, and an open $V \ni 1$ with $VV^{-1} \subseteq W$. The open sets $HV$ and $HxV$ are disjoint: $h_1v_1 = h_2xv_2$ gives $x = h_2^{-1}h_1v_1v_2^{-1} \in HW$, so $xW \cap H \ne \emptyset$. Both are open and nonempty, and $gHV = HV$, so $HV$ is invariant and not trivial. $\square$

**Theorem (Endomorphisms).** Let $G$ be a compact second countable Hausdorff group with Haar probability $\mu$, and $f$ a continuous surjective endomorphism such that $\bigcup_n \ker f^n$ is dense. Then $f$ is ergodic.

*Proof.* The measure $f_*\mu$ is left invariant: $f^{-1}(f(h)A) = hf^{-1}(A)$ and $f$ is onto. By uniqueness of Haar measure (Volume 18), $f_*\mu = \mu$. Let $f^{-1}(s) = s$ a.e. and $k \in \ker f^n$. Then $f^n(kx) = f^n(x)$, so $kf^{-n}(s) = f^{-n}(s)$. With $s = f^{-n}(s)$ a.e. and the invariance of $\mu$ under $x \mapsto kx$, $ks = s$ a.e. The a.e. stabilizer of $s$ contains the dense set $\bigcup_n \ker f^n$, so the corollary for the action of $G$ on itself makes $s$ trivial. $\square$

### Examples

**Example (Rotations).** On $\mathbb{T} = \mathbb{R}/\mathbb{Z}$, the multiples of an irrational $a$ are dense, so the theorem on translations proves again, without Fourier series, that $x \mapsto x + a$ is ergodic.

**Example (Odometer).** On the $p$-adic integers $\mathbb{Z}_p$ with Haar probability, the integers are dense, so $x \mapsto x + 1$ is ergodic.

**Example (Multiplication).** On $\mathbb{T}$, the kernel of $x \mapsto n^k x$ is the set of multiples of $n^{-k}$. For $|n| \ge 2$ the union is dense, so $x \mapsto nx$ is ergodic.

### The library around it

::: mathlib
`MeasureTheory.ergodicSMul_iterateMulAct` · `Mathlib.Dynamics.Ergodic.Action.Basic`

`Measurable f → (ErgodicSMul (IterateMulAct f) α μ ↔ Ergodic f μ)`. Here `IterateMulAct f` is a copy of `ℕ` that acts by iterates.

<?decl MeasureTheory.ergodicSMul_iterateMulAct?>
<?decl IterateMulAct?>
:::

::: mathlib
`MeasureTheory.aeconst_of_forall_smul_ae_eq` · `Mathlib.Dynamics.Ergodic.Action.Basic`

For a group, `NullMeasurableSet s μ → (∀ g, g • s =ᵐ[μ] s) → EventuallyEmptyOrUniv s (ae μ)`. The form with preimages is `aeconst_of_forall_preimage_smul_ae_eq`; the forms with the stabilizer are `MulAction.aeconst_of_aestabilizer_eq_top` and `ErgodicSMul.of_aestabilizer`.

<?decl MeasureTheory.aeconst_of_forall_smul_ae_eq?>
<?decl MulAction.aestabilizer?>
:::

::: mathlib
`aeconst_of_dense_aestabilizer_smul` · `Mathlib.Dynamics.Ergodic.Action.OfMinimal`

With `[ContinuousInv G] [R1Space X] [BorelSpace X] [ContinuousSMul G X] [IsFiniteMeasure μ] [μ.InnerRegular] [ErgodicSMul G X μ]`, `NullMeasurableSet s μ → Dense (MulAction.aestabilizer G μ s : Set G) → EventuallyEmptyOrUniv s (ae μ)`. For a topological space `M` with `SMul M X`, `aeconst_of_dense_setOfPred_preimage_smul_ae` asks that `{g | (g • ·) ⁻¹' s =ᵐ[μ] s}` be dense, and `aeconst_of_dense_setOfPred_preimage_smul_eq` uses exact equality.

<?decl aeconst_of_dense_aestabilizer_smul?>
:::

::: mathlib
`ergodic_smul_of_denseRange_zpow` · `Mathlib.Dynamics.Ergodic.Action.OfMinimal`

`DenseRange (g ^ · : ℤ → G) → ∀ μ [IsFiniteMeasure μ] [μ.InnerRegular] [ErgodicSMul G X μ], Ergodic (g • ·) μ`. The monoid version with natural powers is `ergodic_smul_of_denseRange_pow`. With `MulAction.IsMinimal M N`, `ErgodicSMul.trans_isMinimal` passes ergodicity from `N` to `M`.

<?decl ergodic_smul_of_denseRange_zpow?>
<?decl MulAction.IsMinimal?>
:::

::: mathlib
`ergodic_mul_left_iff_denseRange_zpow` · `Mathlib.Dynamics.Ergodic.Action.OfMinimal`

With `[IsTopologicalGroup G] [SecondCountableTopology G] [BorelSpace G] [IsFiniteMeasure μ] [μ.InnerRegular] [μ.IsMulLeftInvariant] [NeZero μ]`, `Ergodic (g * ·) μ ↔ DenseRange (g ^ · : ℤ → G)`. The halves are `DenseRange.zpow_of_ergodic_mul_left`, under `[μ.IsOpenPosMeasure]`, and `ergodic_mul_left_of_denseRange_zpow` or `ergodic_mul_left_of_denseRange_pow`. The additive form is `ergodic_add_left_iff_denseRange_zsmul`. The regular action is ergodic by `instErgodicSMulOfIsMulLeftInvariant` for `SFinite` left invariant measures, and `instErgodicSMulMulOppositeOfIsMulRightInvariant` treats right multiplication.

<?decl ergodic_mul_left_iff_denseRange_zpow?>
<?decl MeasureTheory.quasiMeasurePreserving_mul_right?>
:::

::: mathlib
`MonoidHom.ergodic_of_dense_iUnion_preimage_one` · `Mathlib.Dynamics.Ergodic.Action.OfMinimal`

With `[CompactSpace G] [μ.IsHaarMeasure]` on a second countable group, `(f : G →* G) → Dense (⋃ n, f^[n] ⁻¹' 1) → Continuous f → Surjective f → Ergodic f μ`. The version `MonoidHom.preErgodic_of_dense_iUnion_preimage_one` asks for `QuasiMeasurePreserving f μ μ` and a finite inner regular left invariant measure, and gives `PreErgodic`. The additive form is `AddMonoidHom.ergodic_of_dense_iUnion_preimage_zero`.

<?decl MonoidHom.ergodic_of_dense_iUnion_preimage_one?>
:::

Common errors of a learner:

- `ErgodicSMul` includes the invariance of the measure.
- The condition in `ergodic_mul_left_iff_denseRange_zpow` uses integer powers. In a compact group the closures of the natural and of the integer powers are equal (Exercise 6), but the library states the two cases in separate lemmas.
- The theorems on dense sets need a finite inner regular measure, so they do not apply to Lebesgue measure on $\mathbb{R}$.

### Exercises

1. (A) Show that the action of $\mathbb{Z}$ on $\mathbb{T}$ by $n \cdot x = x + na$ is ergodic if and only if $a$ is irrational.
2. (A) Show that an action of a group is ergodic if the action of a subgroup is ergodic, and that the converse is false.
3. (B) Show that $x \mapsto x + (a, b)$ on $\mathbb{T}^2$ is ergodic if and only if $1, a, b$ are linearly independent over $\mathbb{Q}$. Hint: use Fourier series.
4. (B) Show that $x \mapsto 2x$ on the compact group $\mathbb{Z}_3^\times$ is ergodic for Haar probability, and that it is not ergodic on $\mathbb{Z}_3$. Hint: show that the powers of $4$ are dense in $1 + 3\mathbb{Z}_3$ and use $2 \equiv -1 \bmod 3$; on $\mathbb{Z}_3$, look at the set $\{x : |x|_3 = 1\}$.
5. (A) Show that the iterates of the automorphism $(x, y) \mapsto (x + y, x)$ of $\mathbb{T}^2$ have trivial kernels, so that the theorem on endomorphisms does not apply to it.
6. (C) Show that in a compact group with Haar probability, $\overline{\langle g \rangle}$ equals the closure of $\{g^n : n \ge 0\}$. Hint: the closure of the natural powers is a closed subsemigroup of a compact group; show that it contains $1$ and $g^{-1}$.

### Notes and history

The odometer is a standard example of an ergodic map with discrete spectrum. The index of this edition has no declaration for the ergodicity of hyperbolic automorphisms of $\mathbb{T}^2$, such as the map of Exercise 5.

### Reference

<?reference?>
