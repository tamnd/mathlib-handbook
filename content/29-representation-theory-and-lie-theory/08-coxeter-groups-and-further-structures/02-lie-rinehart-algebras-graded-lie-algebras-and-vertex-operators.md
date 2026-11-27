---
title: Lie-Rinehart algebras, graded Lie algebras and vertex operators
kind: theory
modules:
  - Mathlib.Algebra.Lie.Cochain
  - Mathlib.Algebra.Lie.Graded
  - Mathlib.Algebra.Lie.Loop
  - Mathlib.Algebra.LieRinehartAlgebra.Defs
  - Mathlib.Algebra.LieRinehartAlgebra.Subalgebra
  - Mathlib.Algebra.LieRinehartAlgebra.StrictIdeal
  - Mathlib.Algebra.LieRinehartAlgebra.Quotient
  - Mathlib.Algebra.Vertex.HVertexOperator
  - Mathlib.Algebra.Vertex.VertexOperator
  - Mathlib.Algebra.Lie.TransferInstance
explains:
  E3: [LieRinehartRing, LieRinehartAlgebra, LieRinehartAlgebra.Hom, LieRinehartAlgebra.anchor, StrictLieRinehartIdeal, LieRinehartAlgebra.Hom.ker, LieRinehartAlgebra.mk', LieModule.Cohomology.twoCochain, LieModule.Cohomology.d₁₂, LieModule.Cohomology.d₂₃, LieModule.Cohomology.d₂₃_comp_d₁₂, LieModule.Cohomology.twoCocycle, GradedLieAlgebra, LieDerivation.ofGrading, LieAlgebra.loopAlgebra, LieAlgebra.LoopAlgebra.residuePairing, LieAlgebra.LoopAlgebra.twoCocycleOfBilinear, HVertexOperator, HVertexOperator.comp, VertexOperator, VertexOperator.ncoeff]
  E2: [LieRinehartAlgebra.anchor_apply, LieRinehartAlgebra.Hom.comp, LieRinehartSubalgebra, LieRinehartSubalgebra.toLieSubalgebra, LieRinehartSubalgebra.map, LieRinehartAlgebra.Hom.range, LieRinehartAlgebra.isotropic, LieRinehartAlgebra.toLieIdeal, LieRinehartAlgebra.comap, LieRinehartAlgebra.Hom.mem_ker, LieRinehartAlgebra.mkQ, LieRinehartAlgebra.surjective_mk', LieRinehartAlgebra.ker_mk', LieModule.Cohomology.oneCochain, LieModule.Cohomology.mem_twoCochain_iff, LieModule.Cohomology.mem_twoCocycle_iff, LieModule.Cohomology.mem_twoCocycle_iff_of_trivial, SetLike.GradedBracket, DirectSum.decomposeLieEquiv, DirectSum.decompose_bracket, LieDerivation.ofGrading_apply_apply, LieAlgebra.loopAlgebraEquivLaurent, LieAlgebra.LoopAlgebra.toFinsupp, LieAlgebra.LoopAlgebra.twoCochainOfBilinear, HVertexOperator.coeff, HVertexOperator.of_coeff, HVertexOperator.coeff_comp, VertexOperator.ncoeff_apply, VertexOperator.coeff_eq_ncoeff, VertexOperator.ncoeff_eq_zero_of_lt_order, VertexOperator.of_coeff, AddEquiv.lieRing, AddEquiv.bracket_def, LinearEquiv.lieAlgebra, LinearEquiv.lieEquiv]
  E1: auto
families: []
requires: [V07.C01, V08.C02, V08.C05, V29.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Lie-Rinehart algebras, graded Lie algebras and vertex operators

### Overview

This section collects four structures that extend the theory of Lie algebras. A Lie-Rinehart algebra is a Lie algebra $L$ that is also a module over a commutative algebra $A$ and acts on $A$ by derivations; vector fields on a manifold are the standard example. The loop algebra $L[t, t^{-1}]$ carries a 2-cocycle made from an invariant form, and this cocycle defines the central extension that leads to the affine Kac-Moody algebras. A vertex operator is a formal series of operators with a lower bound on the poles for each vector; vertex operators are the material of vertex algebras.

Each part of the library is new and short. The section gives the axioms, proves the facts that make the definitions consistent, and marks where the index of this edition stops. The low degree cochains of Lie algebra cohomology appear because the loop algebra cocycle needs them.

### Definitions

Fix a commutative ring $R$. All Lie algebras are over $R$.

**Definition (Lie-Rinehart algebra).** Let $A$ be a commutative $R$-algebra and $L$ a Lie algebra over $R$ that is also an $A$-module, with compatible scalar actions. Suppose that $L$ acts on $A$ by a Lie module structure, written $\lbrack x, a\rbrack$. Then $(A, L)$ is a *Lie-Rinehart algebra* if for all $x, y \in L$ and $a, b \in A$:

1. $\lbrack a x, b\rbrack = a \lbrack x, b\rbrack$, so the action on $A$ is $A$-linear in $x$;
2. $\lbrack x, ab\rbrack = a \lbrack x, b\rbrack + \lbrack x, a\rbrack b$, so each $x$ acts by a derivation;
3. $\lbrack x, a y\rbrack = a \lbrack x, y\rbrack + \lbrack x, a\rbrack y$, the Leibniz rule for the bracket of $L$.

The map $\rho : L \to \operatorname{Der}_R(A)$, $\rho(x)(a) = \lbrack x, a\rbrack$, is the *anchor*.

**Definition (morphism).** Let $\sigma : A_1 \to A_2$ be a homomorphism of $R$-algebras. A *morphism over* $\sigma$ from $(A_1, L_1)$ to $(A_2, L_2)$ is a Lie algebra homomorphism $f : L_1 \to L_2$ with $f(a x) = \sigma(a) f(x)$ and $\sigma(\lbrack x, a\rbrack) = \lbrack f(x), \sigma(a)\rbrack$.

**Definition (strict ideal).** A *strict ideal* of a Lie-Rinehart algebra is an $A$-submodule $I \subseteq L$ with $\lbrack I, L\rbrack \subseteq I$ that is *isotropic*: $\lbrack i, a\rbrack = 0$ for all $i \in I$ and $a \in A$. A *Lie-Rinehart subalgebra* is an $A$-submodule closed under the bracket.

**Definition (graded Lie algebra).** Let $\iota$ be an additive monoid and $(\mathcal{L}_i)_{i \in \iota}$ a family of $R$-submodules of $L$ such that $L = \bigoplus_i \mathcal{L}_i$ as an internal direct sum. The family is a *grading* if $\lbrack \mathcal{L}_i, \mathcal{L}_j\rbrack \subseteq \mathcal{L}_{i+j}$ for all $i, j$.

**Definition (Lie algebra cochains in low degree).** Let $M$ be an $L$-module. A 1-cochain is a linear map $f : L \to M$. A 2-cochain is a bilinear map $c : L \times L \to M$ with $c(x, x) = 0$ for all $x$; then $c(y, x) = -c(x, y)$. The differentials are
$$(d_{12} f)(x, y) = x f(y) - y f(x) - f(\lbrack x, y\rbrack),$$
$$(d_{23} c)(x, y, z) = x c(y, z) - y c(x, z) + z c(x, y) - c(\lbrack x, y\rbrack, z) + c(\lbrack x, z\rbrack, y) - c(\lbrack y, z\rbrack, x).$$
A *2-cocycle* is a 2-cochain $c$ with $d_{23} c = 0$.

**Definition (loop algebra and residue pairing).** Let $A$ be an additive group. The *loop algebra* is $L\lbrack A\rbrack = R\lbrack A\rbrack \otimes_R L$, where $R\lbrack A\rbrack$ is the group algebra with basis $t^a$; the bracket is $\lbrack t^a \otimes x, t^b \otimes y\rbrack = t^{a+b} \otimes \lbrack x, y\rbrack$. For $A = \mathbb{Z}$ it is $L \otimes R\lbrack t, t^{-1}\rbrack$. For a bilinear form $\Phi$ on $L$ the *residue pairing* is
$$\psi(t^m \otimes x, t^n \otimes y) = n\, \delta_{m+n, 0}\, \Phi(x, y),$$
where $n \in A$ acts on $R$ through a given scalar action. For $A = \mathbb{Z}$ this is $\operatorname{Res}_{t=0} \Phi(f, dg)$.

**Definition (vertex operator).** Let $\Gamma$ be a partially ordered set and $V$, $W$ modules over a commutative ring $R$. A *heterogeneous vertex operator* is an $R$-linear map $A : V \to W((z^\Gamma))$ into Hahn series, $A(v) = \sum_{n \in \Gamma} A_n(v) z^n$, so that each $A_n : V \to W$ is linear and each support $\{n : A_n(v) \neq 0\}$ is partially well ordered. A *vertex operator* on $V$ is the case $\Gamma = \mathbb{Z}$ and $W = V$. Then $A_n(v) = 0$ for $n$ below a bound that depends on $v$. The *normalized coefficients* are $A_{(n)} = A_{-n-1}$, so that $A(z) = \sum_n A_{(n)} z^{-n-1}$.

### Theorems and proofs

**Proposition (the anchor).** For a Lie-Rinehart algebra $(A, L)$ the anchor $\rho : L \to \operatorname{Der}_R(A)$ is an $A$-linear homomorphism of Lie algebras, and it is a morphism of Lie-Rinehart algebras over the identity of $A$.

*Proof.* By rule 2, $\rho(x)$ is a derivation, and by rule 1, $\rho(a x) = a \rho(x)$. The module axiom $\lbrack \lbrack x, y\rbrack, a\rbrack = \lbrack x, \lbrack y, a\rbrack\rbrack - \lbrack y, \lbrack x, a\rbrack\rbrack$ says that $\rho(\lbrack x, y\rbrack) = \rho(x) \rho(y) - \rho(y) \rho(x)$, the commutator of derivations. The condition on brackets with $A$ is the definition of $\rho$. $\square$

**Proposition (kernels and quotients).** Let $f : L_1 \to L_2$ be a morphism over the identity of $A$. Then $\ker f$ is a strict ideal. Let $I$ be a strict ideal of $L$. Then $L/I$ is a Lie-Rinehart algebra over $A$ with $\lbrack \bar{x}, a\rbrack = \lbrack x, a\rbrack$, the projection $L \to L/I$ is a surjective morphism, and its kernel is $I$.

*Proof.* The kernel is an $A$-submodule because $f(a x) = a f(x)$, and an ideal because $f$ is a Lie homomorphism. For $i \in \ker f$, $\lbrack i, a\rbrack = \lbrack f(i), a\rbrack = 0$, so the kernel is isotropic. Since $I$ is an ideal and an $A$-submodule, $L/I$ is a Lie algebra and an $A$-module. The action on $A$ is well defined because $\lbrack x + i, a\rbrack = \lbrack x, a\rbrack$ for $i \in I$; only here is isotropy used. The three rules hold for representatives, hence in $L/I$, and the projection has the stated properties. $\square$

**Theorem ($d^2 = 0$).** For every 1-cochain $f$, $d_{23}(d_{12} f) = 0$. Hence $d_{12} f$ is a 2-cocycle.

*Proof.* First, $d_{12} f$ is a 2-cochain, since $(d_{12} f)(x, x) = x f(x) - x f(x) - f(0) = 0$. Put $c = d_{12} f$ and expand the six terms of $(d_{23} c)(x, y, z)$. Each of $x f(\lbrack y, z\rbrack)$, $y f(\lbrack x, z\rbrack)$ and $z f(\lbrack x, y\rbrack)$ occurs twice with opposite signs, once from the first three terms and once from the last three. The terms with two actions collect into three groups:
$$x y f(z) - y x f(z) - \lbrack x, y\rbrack f(z), \quad z x f(y) - x z f(y) + \lbrack x, z\rbrack f(y), \quad y z f(x) - z y f(x) - \lbrack y, z\rbrack f(x),$$
and each group is $0$ because $M$ is an $L$-module. What remains is
$$f(\lbrack \lbrack x, y\rbrack, z\rbrack) - f(\lbrack \lbrack x, z\rbrack, y\rbrack) + f(\lbrack \lbrack y, z\rbrack, x\rbrack) = f\bigl(\lbrack \lbrack x, y\rbrack, z\rbrack + \lbrack \lbrack z, x\rbrack, y\rbrack + \lbrack \lbrack y, z\rbrack, x\rbrack\bigr) = 0$$
by the Jacobi identity. $\square$

For a trivial module $M$ the actions vanish, and $c$ is a 2-cocycle if and only if
$$c(x, \lbrack y, z\rbrack) = c(\lbrack x, y\rbrack, z) + c(y, \lbrack x, z\rbrack). \tag{1}$$

**Proposition (derivations from a grading).** Let $(\mathcal{L}_i)$ be a grading of $L$ and $\varphi : \iota \to R$ an additive homomorphism. The linear map $D$ with $D(a) = \varphi(i) a$ for $a \in \mathcal{L}_i$ is a derivation of $L$.

*Proof.* The decomposition extends $D$ uniquely to $L$. Both sides of $D \lbrack a, b\rbrack = \lbrack D a, b\rbrack + \lbrack a, D b\rbrack$ are bilinear, so it is sufficient to take $a \in \mathcal{L}_i$ and $b \in \mathcal{L}_j$. Then $\lbrack a, b\rbrack \in \mathcal{L}_{i+j}$ and $D \lbrack a, b\rbrack = \varphi(i + j) \lbrack a, b\rbrack = \varphi(i) \lbrack a, b\rbrack + \varphi(j) \lbrack a, b\rbrack$. $\square$

**Theorem (the loop cocycle).** Let $A$ be a commutative ring with an algebra map $A \to R$. Suppose that $\Phi$ is symmetric and invariant, $\Phi(\lbrack x, y\rbrack, z) = -\Phi(y, \lbrack x, z\rbrack)$, and that $n r = 0$ implies $r = 0$ in $R$ for every natural number $n \neq 0$. Then the residue pairing $\psi$ is a 2-cocycle of $L\lbrack A\rbrack$ with values in the trivial module $R$.

*Proof.* Let $u = \sum_a t^a \otimes u_a$. Then $\psi(u, u) = \sum_a a\, \Phi(u_{-a}, u_a)$. For $a \neq -a$ the terms for $a$ and $-a$ cancel by symmetry. For $a = -a$ the term $r = a \Phi(u_a, u_a)$ satisfies $2r = 0$, so $r = 0$. For (1) take $t^a \otimes x$, $t^b \otimes y$, $t^c \otimes z$; all terms vanish unless $a + b + c = 0$. Put $P = \Phi(x, \lbrack y, z\rbrack)$. Invariance gives $\Phi(\lbrack x, y\rbrack, z) = -\Phi(\lbrack y, x\rbrack, z) = P$ and $\Phi(y, \lbrack x, z\rbrack) = -P$. The three terms of (1) are $(b + c) P$, $c P$ and $-(a + c) P$, and $(b + c) P = c P - (a + c) P$ because $a + b + c = 0$. $\square$

**Proposition (composition of vertex operators).** Let $A : V \to W((z^\Gamma))$ and $B : U \to V((z^{\Gamma'}))$ be heterogeneous vertex operators. The coefficients $C_{(g', g)} = A_g \circ B_{g'}$ define a heterogeneous vertex operator $C : U \to W((z^{\Gamma' \times_{\mathrm{lex}} \Gamma}))$.

*Proof.* Fix $u$ and put $S = \{(g', g) : A_g(B_{g'}(u)) \neq 0\}$. The projection of $S$ to $\Gamma'$ lies in the support of $B(u)$, and each fibre lies in the support of $A(B_{g'}(u))$; both are partially well ordered. Take a sequence $(g'_k, g_k)$ in $S$ and pass to a subsequence with $g'_k$ nondecreasing, which exists in a partially well ordered set. If some $g'_k < g'_l$ with $k < l$, then $(g'_k, g_k) < (g'_l, g_l)$ in the lexicographic order. If not, all $g'_k$ are equal, the $g_k$ lie in one fibre, and some $g_k \le g_l$ with $k < l$. So $S$ is partially well ordered. $\square$

### Examples

**Example (derivations of a polynomial ring).** Let $k$ be a field of characteristic $0$, $A = k\lbrack x\rbrack$ and $L = \operatorname{Der}_k(A) = A\, \partial$, with $\partial = d/dx$. The bracket is $\lbrack f \partial, g \partial\rbrack = (f g' - g f') \partial$, the action on $A$ is $\lbrack f \partial, a\rbrack = f a'$, and the anchor is the identity. An isotropic element $f \partial$ satisfies $f \cdot 1 = \lbrack f \partial, x\rbrack = 0$, so the only strict ideal is $0$.

**Example (the grading of $\mathfrak{sl}_2$).** In $\mathfrak{sl}_2$ with basis $e, h, f$ put $\mathcal{L}_1 = k e$, $\mathcal{L}_0 = k h$, $\mathcal{L}_{-1} = k f$ and $\mathcal{L}_i = 0$ otherwise. The relations $\lbrack h, e\rbrack = 2e$, $\lbrack h, f\rbrack = -2f$, $\lbrack e, f\rbrack = h$ show that this is a $\mathbb{Z}$-grading. With $\varphi(i) = 2i$ the derivation of the proposition sends $e \mapsto 2e$, $h \mapsto 0$, $f \mapsto -2f$, and so it is $\operatorname{ad} h$.

**Example (the affine cocycle of $\mathfrak{sl}_2$).** Take $L = \mathfrak{sl}_2(\mathbb{Q})$, $A = \mathbb{Z}$ and $\Phi(x, y) = \operatorname{tr}(x y)$. Then $\psi(t \otimes e, t^{-1} \otimes f) = (-1) \operatorname{tr}(e f) = -1$ and $\psi(t^{-1} \otimes f, t \otimes e) = 1$. The central extension $\hat{L} = L\lbrack t, t^{-1}\rbrack \oplus \mathbb{Q} K$ has the bracket $\lbrack t^m \otimes x, t^n \otimes y\rbrack = t^{m+n} \otimes \lbrack x, y\rbrack + n\, \delta_{m+n,0} \operatorname{tr}(x y) K$. This is $\hat{\mathfrak{sl}}_2$ without its degree derivation.

**Example (two vertex operators on $k\lbrack x\rbrack$).** Let $V = k\lbrack x\rbrack$. Define $A$ by $A_n = $ multiplication by $x^n$ for $n \ge 0$ and $A_n = 0$ for $n < 0$. Then $A(z) = \sum_{n \ge 0} x^n z^n$ is a vertex operator, and the support of $A(v)$ is $\mathbb{N}$ for $v \neq 0$. Its normalized coefficients are $A_{(n)} = x^{-n-1}$ for $n \le -1$ and $0$ for $n \ge 0$. Define $B$ by $B_n = \partial^n$ for $n \ge 0$ and $B_n = 0$ for $n < 0$. For $v$ of degree $d$ the support of $B(v)$ is in $\{0, \dots, d\}$, although $B$ has infinitely many nonzero coefficients. The series $C$ with $C_{-n} = $ multiplication by $x^n$ for $n \ge 0$ and $C_n = 0$ for $n > 0$ is not a vertex operator, since the support of $C(1)$ is not bounded below.

### The library around it

::: mathlib
`LieRinehartAlgebra` · `Mathlib.Algebra.LieRinehartAlgebra.Defs`

`LieRinehartRing A L` holds rules 1 to 3 for a `LieRing L` that is an `A`-module and acts on `A`, with the fields `lie_smul_eq_mul'`, `leibniz_mul_right'` and `leibniz_smul_right'`. `LieRinehartAlgebra R A L` is a `Prop` class on top of it with the scalar tower and `LieModule R L A`. There are instances on `Derivation R A A`. `LieRinehartAlgebra.Hom σ` with the notation `L₁ →ₗ⁅σ⁆ L₂` is the morphism over `σ`, and `Hom.comp` composes. `anchor R A L` is the anchor, with `anchor_apply`.

<?decl LieRinehartAlgebra?>
:::

::: mathlib
`StrictLieRinehartIdeal` · `Mathlib.Algebra.LieRinehartAlgebra.StrictIdeal`

`StrictLieRinehartIdeal A L` is the strict ideal, a structure over `Submodule A L`. `isotropic` is its last axiom, `toLieIdeal` forgets isotropy, and `comap` pulls back along a morphism. `Hom.ker` with `Hom.mem_ker` is the kernel of the proposition. In the module `Quotient`, `mkQ` gives the quotient and `mk' s R` the projection, with `surjective_mk'` and `ker_mk'`. `LieRinehartSubalgebra` with `toLieSubalgebra`, `map` and `Hom.range` covers subalgebras.

<?decl StrictLieRinehartIdeal?>
:::

::: mathlib
`LieModule.Cohomology.d₂₃_comp_d₁₂` · `Mathlib.Algebra.Lie.Cochain`

`oneCochain R L M` is `L →ₗ[R] M`, and `twoCochain R L M` is the submodule of bilinear maps with `mem_twoCochain_iff`. `d₁₂` and `d₂₃` are the differentials, and `d₂₃_comp_d₁₂` is the theorem. `twoCocycle` is the kernel of `d₂₃`, with `mem_twoCocycle_iff` and `mem_twoCocycle_iff_of_trivial`, which is (1). `LieAlgebra.Extension.ofTwoCocycle` in another module builds the extension.

<?decl LieModule.Cohomology.d₂₃_comp_d₁₂?>
<?decl LieAlgebra.Extension.ofTwoCocycle?>
:::

::: mathlib
`LieDerivation.ofGrading` · `Mathlib.Algebra.Lie.Graded`

`SetLike.GradedBracket` asks for `bracket_mem`, and `GradedLieAlgebra ℒ` combines it with `DirectSum.Decomposition ℒ`. `DirectSum.decomposeLieEquiv` is the Lie isomorphism $L \cong \bigoplus_i \mathcal{L}_i$, with `decompose_bracket`. `LieDerivation.ofGrading ℒ φ` is the derivation of the proposition, with `ofGrading_apply_apply`.

<?decl LieDerivation.ofGrading?>
:::

::: mathlib
`LieAlgebra.LoopAlgebra.twoCocycleOfBilinear` · `Mathlib.Algebra.Lie.Loop`

`loopAlgebra R A L` is `AddMonoidAlgebra R A ⊗[R] L`, `loopAlgebraEquivLaurent` identifies the case `A = ℤ` with Laurent polynomials, and `toFinsupp` gives the coefficients as `A →₀ L`. `residuePairing R A L Φ` is $\psi$. `twoCochainOfBilinear` needs `Φ.IsSymm`, `[HasUniqueDiv R]` and `[Algebra A R]`, and `twoCocycleOfBilinear` adds `Φ.lieInvariant L`. The values are in `TrivialLieModule R (loopAlgebra R A L) R`.

<?decl LieAlgebra.LoopAlgebra.twoCocycleOfBilinear?>
<?decl LinearMap.BilinForm.lieInvariant?>
:::

::: mathlib
`HVertexOperator.comp` · `Mathlib.Algebra.Vertex.HVertexOperator`

`HVertexOperator Γ R V W` is the abbreviation `V →ₗ[R] HahnModule Γ R W`. `coeff` gives $A_n$, `of_coeff` builds an operator from coefficients, and `comp` is the composition, indexed by `Γ' ×ₗ Γ`, with `coeff_comp`. In `VertexOperator`, `VertexOperator R V` is the case `Γ = ℤ`, `ncoeff A n` is `coeff A (-n - 1)` with the notation `A[[n]]`, and `of_coeff` takes a bounded below support condition.

<?decl HVertexOperator.comp?>
<?decl VertexOperator.ncoeff?>
:::

::: mathlib
`AddEquiv.lieRing` · `Mathlib.Algebra.Lie.TransferInstance`

`AddEquiv.lieRing e` transports a Lie ring structure along an additive equivalence, with `bracket_def` $\lbrack x, y\rbrack = e^{-1} \lbrack e x, e y\rbrack$. `LinearEquiv.lieAlgebra` and `LinearEquiv.lieEquiv` do the same for Lie algebras.

<?decl AddEquiv.lieRing?>
:::

Common errors of a learner: The anchor is the instance `LieRingModule L A`, so `⁅x, a⁆` is the anchor applied to `a`. `Hom.ker` and the quotient are for morphisms over `.id R A` only. A Lie ideal that is an `A`-submodule is not a strict ideal until isotropy is proved. Cochains stop at degree 3, and the index of this edition has no declaration for the cohomology groups $H^n(L, M)$; the module `Extension` has `LieEquiv.ofCoboundary` for cocycles that differ by $d_{12} f$. The trivial module is `TrivialLieModule R L R`. Gradings are internal. For `VertexOperator`, `coeff A n` and `ncoeff A n` differ by the shift $n \mapsto -n-1$, and in `comp A B` the first coordinate of the index belongs to the inner operator `B`. The index of this edition has no declaration for vertex algebras, the Jacobi identity of vertex operators or locality.

### Exercises

1. (A) Show that $\operatorname{Der}_R(A)$ is a Lie-Rinehart algebra with the identity as anchor. Hint: show first that the commutator of two derivations is a derivation.
2. (A) Let $(A, L)$ be a Lie-Rinehart algebra and $I$ a strict ideal. Prove that the anchor of $L$ vanishes on $I$, so that it factors through $L/I$. Hint: compare isotropy with the definition of the anchor.
3. (B) Prove $\lbrack a x, y\rbrack = a \lbrack x, y\rbrack - \lbrack y, a\rbrack x$ in a Lie-Rinehart algebra. Hint: apply rule 3 to $\lbrack y, a x\rbrack$ and use antisymmetry.
4. (B) Let $c = d_{12} f$ with values in a trivial module. Show that $c(x, y) = -f(\lbrack x, y\rbrack)$ and verify (1) for $c$ directly. Hint: (1) becomes $f$ of the Jacobi identity.
5. (B) For $L = \mathfrak{sl}_2(\mathbb{Q})$ with the trace form, compute $\psi(t^2 \otimes h, t^{-2} \otimes h)$ and $\psi(t \otimes e, t \otimes f)$. Hint: $\operatorname{tr}(h^2) = 2$ and the second index condition fails.
6. (B) Let $R = \mathbb{Q}$, $A = \mathbb{Z}$ and $\Phi \neq 0$. Show that $\psi$ is not of the form $d_{12} f$. Hint: $(d_{12} f)(t^m \otimes x, t^{-m} \otimes y) = -f(t^0 \otimes \lbrack x, y\rbrack)$ does not depend on $m$; compare $m = 1$ and $m = 2$.

### Notes and history

Lie-Rinehart algebras go back to Herz in 1953 and Palais in 1961. Rinehart studied them in 1963 in his work on differential forms on commutative algebras and proved a Poincaré-Birkhoff-Witt theorem for them; Huebschmann gave them their current name. The cohomology of Lie algebras is due to Chevalley and Eilenberg in 1948. Central extensions of loop algebras appeared with the Lie algebras of Kac and of Moody in 1967 and 1968. Vertex operators came from string theory; Borcherds defined vertex algebras in 1986; Frenkel, Lepowsky and Meurman used them in 1988 to construct the moonshine module.

The Mathlib files are by Sven Holtrop and Leonid Ryvkin (`LieRinehartAlgebra.Defs`), Leonid Ryvkin (`Subalgebra` and `TransferInstance`), Yaël Dillies and Leonid Ryvkin (`StrictIdeal` and `Quotient`), and Scott Carnahan (`Cochain`, `Graded`, `Loop`, `HVertexOperator` and `VertexOperator`).

### Reference

<?reference?>
