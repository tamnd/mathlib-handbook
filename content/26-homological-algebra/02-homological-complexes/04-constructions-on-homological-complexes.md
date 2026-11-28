---
title: Constructions on homological complexes
kind: api
modules:
  - Mathlib.Algebra.Homology.HomologicalComplexBiprod
  - Mathlib.Algebra.Homology.HomologicalComplexKernels
  - Mathlib.Algebra.Homology.HomologicalComplexLimitsEventuallyConstant
  - Mathlib.Algebra.Homology.Functor
  - Mathlib.Algebra.Homology.Linear
  - Mathlib.Algebra.Homology.FullSubcategory
  - Mathlib.Algebra.Homology.ConcreteCategory
  - Mathlib.Algebra.Homology.CommSq
  - Mathlib.Algebra.Homology.Square
  - Mathlib.Algebra.Homology.Double
  - Mathlib.Algebra.Homology.AlternatingConst
  - Mathlib.Algebra.Homology.HasNoLoop
  - Mathlib.Algebra.Homology.EulerCharacteristic
explains:
  E2: [HomologicalComplex.biprodXIso, HomologicalComplex.hasKernel_of_hasKernel_f, HomologicalComplex.quasiIso_iff_evaluation, HomologicalComplex.double, HomologicalComplex.evalCompCoyonedaCorepresentableByDoubleId, ChainComplex.alternatingConstHomotopyEquiv, ComplexShape.HasNoLoop, HomologicalComplex.eulerChar]
  E1: auto
families: []
requires: [V24.C08, V25.C02, V26.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Constructions on homological complexes

### Overview

Section 1 defines complexes of a given shape and Section 2 their homology. This section collects the constructions that a user meets next: biproducts and kernels of complexes, complexes of functors, linear structure, complexes with values in a full subcategory, and two small families of examples. The examples are the complex that lies in two degrees and the periodic complex built from two endomorphisms with zero composites. The section ends with the complex shapes that have no loops and with the Euler characteristic.

Most of these modules are short. They follow one principle: a construction on complexes is done degreewise, and a statement about complexes reduces to a statement in each degree. So the main lemmas say that an operation commutes with the evaluation functor `HomologicalComplex.eval C c i`, which sends a complex $K$ to its object $K_i$.

### The library around it

#### Biproducts, kernels and limits

Let $C$ be preadditive and let $K$ and $L$ be complexes of shape $c$ such that each $K_i \oplus L_i$ exists. Then the biproduct $K \oplus L$ exists (`HomologicalComplex.instHasBinaryBiproduct`), and the evaluation functors preserve it (`HomologicalComplex.instPreservesBinaryBiproductEval`). The isomorphism `HomologicalComplex.biprodXIso K L i` identifies $(K \oplus L)_i$ with $K_i \oplus L_i$. The differential is the diagonal matrix $\begin{pmatrix} d_K & 0 \\ 0 & d_L \end{pmatrix}$. The simp lemmas `HomologicalComplex.biprod_inl_fst_f`, `HomologicalComplex.biprod_inr_snd_f` and `HomologicalComplex.biprod_lift_fst_f` give the components of the structure maps in each degree. To prove that two maps out of $(K \oplus L)_i$ are equal, `HomologicalComplex.biprodX_ext_from` reduces to the two inclusions.

Kernels follow the same pattern. If $f : K \to L$ has a kernel in each degree, then $f$ has a kernel (`HomologicalComplex.hasKernel_of_hasKernel_f`), and the evaluation functors preserve it (`HomologicalComplex.eval_preservesLimit_of_hasKernel_f`). The dual results are `HomologicalComplex.hasCokernel_of_hasCokernel_f` and `HomologicalComplex.eval_preservesColimit_of_hasCokernel_f`. The kernel is the complex $(\ker f_i)_i$, and the differential is induced by the universal property of each kernel.

The module `Mathlib.Algebra.Homology.HomologicalComplexLimitsEventuallyConstant` treats limits over a cofiltered category $J$. Let $F : J \to \mathrm{HomologicalComplex}(C, c)$ be such that, in each degree $q$, the diagram $j \mapsto F(j)_q$ is eventually constant. Then for a limit cone $c_F$ and a suitable $j$, the map $(c_F)_q \to F(j)_q$ is an isomorphism (`HomologicalComplex.isIso_π_f_of_isLimit_of_isEventuallyConstantTo`). If this holds in the three degrees around $q$, the map of complexes is a quasi-isomorphism in degree $q$ (`HomologicalComplex.quasiIsoAt_π_of_isLimit_of_isEventuallyConstantTo`). This is the case of a tower of complexes that stabilizes in each degree.

#### Complexes of functors

Let $T$ be a category. A complex of functors $T \to V$ is the same as a functor from $T$ to complexes in $V$. The functor `HomologicalComplex.asFunctor` sends the first to the second, and `HomologicalComplex.complexOfFunctorsToFunctorToComplex` is the same operation as a functor. Its object at $t$ is the complex $(K_i(t))_i$, as `HomologicalComplex.asFunctor_obj_X` states.

Homology commutes with evaluation at $t$, so quasi-isomorphisms are tested pointwise. The lemma `HomologicalComplex.quasiIso_iff_evaluation` says that a map $f$ of complexes of functors is a quasi-isomorphism if and only if its evaluation at each $t$ is one. The lemma `HomologicalComplex.quasiIsoAt_iff_evaluation` is the form in one degree, and `CategoryTheory.ShortComplex.quasiIso_iff_evaluation` the form for short complexes.

#### Linear structure and full subcategories

If $C$ is linear over a ring $R$, the morphisms of complexes form an $R$-module, with the scalar acting in each degree (`HomologicalComplex.instModuleHom`). The instance `HomologicalComplex.instLinear` makes the category of complexes $R$-linear, and `CategoryTheory.Functor.mapHomologicalComplex_linear` says that a linear functor $F$ induces a linear functor on complexes.

Let $P$ be a property of objects of $V$ and let $K$ be a complex with each $K_n$ in $P$. Then $K$ is also a complex in the full subcategory of $P$. The definition `HomologicalComplex.liftObjectProperty` builds this complex, and `HomologicalComplex.liftFunctorObjectProperty` does the same for a functor. This is how a complex of projective objects becomes a complex in the subcategory of projective objects.

#### Elements in a concrete category

The module `Mathlib.Algebra.Homology.ConcreteCategory` extends the element calculus of Chapter 1 to complexes. For modules, an element $x \in K_i$ with $d(x) = 0$ defines a cycle `HomologicalComplex.cyclesMk`, and `HomologicalComplex.i_cyclesMk` says that it maps back to $x$. The lemma `CategoryTheory.ShortComplex.ShortExact.δ_apply'` computes the connecting map of the long exact sequence of Section 3 on elements: for a short exact sequence $0 \to K \to L \to M \to 0$ and a cycle $z \in M_i$, lift $z$ to $y \in L_i$, apply the differential, and take the unique preimage of $d(y)$ in $K_{i'}$.

#### Squares as short complexes

A commutative square in a preadditive category
$$\begin{array}{ccc} X_1 & \xrightarrow{f} & X_2 \\ \downarrow{\scriptstyle g} & & \downarrow{\scriptstyle h} \\ X_3 & \xrightarrow{k} & X_4 \end{array}$$
gives the short complex $X_1 \to X_2 \oplus X_3 \to X_4$, with the maps $(f, -g)$ and $h + k$. The module `Mathlib.Algebra.Homology.CommSq` defines it as `CategoryTheory.CommSq.shortComplex`, The variant `CategoryTheory.CommSq.shortComplex'` uses the maps $(f, g)$ and $h - k$, the form that suits pullbacks. It proves the classical fact: the square is a pushout if and only if $X_4$ is the cokernel of $X_1 \to X_2 \oplus X_3$ (`CategoryTheory.CommSq.isColimitEquivIsColimitCokernelCofork`), and it is a pullback if and only if $X_1$ is the kernel of $X_2 \oplus X_3 \to X_4$ (`CategoryTheory.CommSq.isLimitEquivIsLimitKernelFork`). The lemmas `CategoryTheory.IsPushout.epi_shortComplex_g` and `CategoryTheory.IsPullback.mono_shortComplex'_f` record the two halves of exactness. The module `Mathlib.Algebra.Homology.Square` gives the same results for the structure `CategoryTheory.Square`, as `CategoryTheory.Square.isPullbackEquivIsLimitKernelFork` and `CategoryTheory.Square.isPushoutEquivIsColimitCokernelCofork`.

#### The complex in two degrees

Let $i_0 \ne i_1$ with $c.\mathrm{Rel}\, i_0\, i_1$, and let $f : X_0 \to X_1$. The complex `HomologicalComplex.double f hi₀₁` has $X_0$ in degree $i_0$, $X_1$ in degree $i_1$, and $0$ elsewhere, with $f$ as the only differential. The isomorphisms `HomologicalComplex.doubleXIso₀` and `HomologicalComplex.doubleXIso₁` identify its two objects, and `HomologicalComplex.isZero_double_X` says that the other objects are zero. A map from the double complex to $K$ is a pair $\varphi_0 : X_0 \to K_{i_0}$, $\varphi_1 : X_1 \to K_{i_1}$ that commutes with $f$ and with $d$, where $d \varphi_1 = 0$: this is `HomologicalComplex.mkHomFromDouble`.

**Proposition.** For each object $X$, the complex `HomologicalComplex.double (𝟙 X) hi₀₁` corepresents the functor $K \mapsto \operatorname{Hom}(X, K_{i_0})$.

*Proof.* A map from the double complex to $K$ is a pair $(\varphi_0, \varphi_1)$ with $\varphi_1 = d \varphi_0$ by the first condition. The second condition $d \varphi_1 = d d \varphi_0 = 0$ holds for free. So the map is determined by $\varphi_0$, and every $\varphi_0$ occurs. $\square$

In Lean this is `HomologicalComplex.evalCompCoyonedaCorepresentableByDoubleId`. So the evaluation functor at $i_0$ is corepresentable (`HomologicalComplex.evalCompCoyonedaCorepresentable`).

#### The alternating constant complex

Let $\varphi, \psi : A \to A$ with $\varphi \psi = 0$ and $\psi \varphi = 0$. The periodic complex
$$\cdots \to A \xrightarrow{\varphi} A \xrightarrow{\psi} A \xrightarrow{\varphi} A \to 0$$
is `HomologicalComplex.alternatingConst`, for any shape on $\mathbb{N}$ whose relation joins indices of different parity. Its differential is $\varphi$ or $\psi$ by the parity of the source (`HomologicalComplex.alternatingConst_d`). The isomorphisms `HomologicalComplex.alternatingConstHomologyIsoEven` and `HomologicalComplex.alternatingConstHomologyIsoOdd` compute its homology in an interior degree as $\ker \psi / \operatorname{im} \varphi$ or $\ker \varphi / \operatorname{im} \psi$. This complex computes the homology of cyclic groups in Chapter 8.

The special case $\varphi = 1$, $\psi = 0$ is the functor `ChainComplex.alternatingConst`. Its homology is $X$ in degree $0$ (`ChainComplex.alternatingConstHomologyZero`) and $0$ in the other degrees (`ChainComplex.alternatingConst_exactAt`). The stronger statement `ChainComplex.alternatingConstHomotopyEquiv` gives a homotopy equivalence with the single complex on $X$ in degree $0$. The isomorphism `AlgebraicTopology.alternatingFaceMapComplexConst` identifies this complex with the alternating face map complex of a constant simplicial object.

#### Shapes with no loop and the Euler characteristic

A complex shape has no loop when no index is related to itself; this is the class `ComplexShape.HasNoLoop`, with `ComplexShape.not_rel_self`. The shapes `ComplexShape.up` and `ComplexShape.down` on $\mathbb{N}$ and $\mathbb{Z}$ have no loop (`ComplexShape.instHasNoLoopIntUp` and the three similar instances). The lemma `ComplexShape.exists_distinct_next_or` gives the consequence that the next index of $j$ is either distinct from $j$ or does not exist. Several constructions, such as the double complex, need two distinct related indices.

The module `Mathlib.Algebra.Homology.EulerCharacteristic` defines Euler characteristics for complexes of modules. The class `ComplexShape.EulerCharSigns` gives a sign $\chi(i) \in \{\pm 1\}$ for each index with $\chi(j) = -\chi(i)$ when $c.\mathrm{Rel}\, i\, j$ (`ComplexShape.EulerCharSigns.χ_next`). The four standard shapes have instances, such as `ComplexShape.eulerCharSignsDownNat` with sign $(-1)^n$. Then
$$\chi(K) = \sum_i \chi(i) \dim K_i, \qquad \chi_H(K) = \sum_i \chi(i) \dim H_i(K)$$
are `HomologicalComplex.eulerChar` and `HomologicalComplex.homologyEulerChar`. The definitions use `finsum` and `Module.finrank`, so they give $0$ for infinite support and for modules that are not free of finite rank. The lemmas `HomologicalComplex.eulerChar_eq_sum_finSet_of_finrankSupport_subset` and `HomologicalComplex.homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset` turn the `finsum` into a finite sum over a given finite set of indices. The graded forms are `GradedObject.eulerChar` and `GradedObject.finrankSupport`.

#### Common errors

1. `HomologicalComplex.double` needs a proof of `c.Rel i₀ i₁`, and many of its lemmas also need `i₀ ≠ i₁`. For a shape with a loop the construction still exists, but its objects are not the expected ones.
2. `HomologicalComplex.eulerChar` returns a junk value $0$ when infinitely many $K_i$ have nonzero rank. A proof that the Euler characteristic is a finite sum must supply a finite set of indices that contains the support.
3. In `HomologicalComplex.alternatingConst`, the hypothesis `hOdd` is `φ ≫ ψ = 0`, which is $\psi \circ \varphi = 0$, and `hEven` is `ψ ≫ φ = 0`. Both are needed, and a proof that swaps them gets a goal in the wrong order.

### Exercises

1. (A) Compute the homology of `HomologicalComplex.double f hi₀₁` for $f : \mathbb{Z} \xrightarrow{n} \mathbb{Z}$, in the two degrees $i_0$ and $i_1$.
2. (A) Show that the biproduct of two exact complexes is exact, by `HomologicalComplex.biprodXIso` and the additivity of homology.
3. (B) For $A = \mathbb{Z}[x]/(x^2)$ as a module over itself and $\varphi = \psi = x$, compute the homology of the alternating constant complex in each degree.
4. (B) Prove that a commutative square of abelian groups is a pullback if and only if the sequence $0 \to X_1 \to X_2 \oplus X_3 \to X_4$ is exact.
5. (B) Let $0 \to V_0 \to V_1 \to V_2 \to 0$ be a complex of finite dimensional vector spaces in degrees 0 to 2. Prove that $\chi(K) = \chi_H(K)$.
6. (C) Prove that evaluation at $i_0$ preserves all limits, from the fact that it is corepresentable.

### Reference

<?reference?>
