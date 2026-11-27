---
title: Kleisli categories and monadicity
kind: theory
modules:
  - Mathlib.CategoryTheory.Monad.Kleisli
  - Mathlib.CategoryTheory.Monad.Monadicity
  - Mathlib.CategoryTheory.Monad.Coequalizer
  - Mathlib.CategoryTheory.Monad.Limits
explains:
  E3: [CategoryTheory.Kleisli, CategoryTheory.Kleisli.Adjunction.adj, CategoryTheory.Monad.monadicOfCreatesGSplitCoequalizers, CategoryTheory.Monad.forgetCreatesLimits, CategoryTheory.Monad.beckAlgebraCoequalizer]
  E2: [CategoryTheory.Kleisli.Adjunction.toKleisli, CategoryTheory.Kleisli.Adjunction.fromKleisli, CategoryTheory.Kleisli.Adjunction.toKleisliCompFromKleisliIsoSelf, CategoryTheory.Monad.createsGSplitCoequalizersOfMonadic, CategoryTheory.Monad.monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms, CategoryTheory.Monad.beckSplitCoequalizer, CategoryTheory.Monad.beckCoequalizer, CategoryTheory.monadicCreatesLimits]
  E1: auto
families: []
requires: [V05, V13, V24.C04, V24.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Kleisli categories and monadicity

### Overview

This section builds the Kleisli adjunction of a monad $T$ on $C$ and shows that the two are the smallest and the largest adjunctions with monad $T$. Then Beck's theorem says, in terms of coequalizers, when the comparison functor $K : D \to C^T$ of a right adjoint is an equivalence. As in Section 1, the text writes $g \circ f$ for Mathlib's `f ≫ g`.

### Definitions

**Definition (Kleisli category).** Let $(T, \eta, \mu)$ be a monad on $C$. The *Kleisli category* $C_T$ has the objects of $C$ and $\mathrm{Hom}_{C_T}(X, Y) = \mathrm{Hom}_C(X, TY)$. The identity of $X$ is $\eta_X$, and the composite of $f : X \to TY$ and $g : Y \to TZ$ is $g \circ_T f = \mu_Z \circ Tg \circ f$.

The functor $F_T : C \to C_T$ is the identity on objects, with $F_T f = \eta_Y \circ f$. The functor $G_T : C_T \to C$ sends $Y$ to $TY$ and $f : X \to TY$ to $\mu_Y \circ Tf$.

::: mathlib
`CategoryTheory.Kleisli` · `Mathlib.CategoryTheory.Monad.Kleisli`

`Kleisli T` is a type synonym for `C`, with a category instance whose morphisms `X ⟶ Y` are the maps `X ⟶ T.obj Y` of `C`. The functors are `Kleisli.Adjunction.toKleisli T`, which is $F_T$, and `Kleisli.Adjunction.fromKleisli T`, which is $G_T$. By `toKleisliCompFromKleisliIsoSelf` their composite is `T`.

<?decl CategoryTheory.Kleisli?>
:::

**Definition (Monadic functor).** A functor $G : D \to C$ is *monadic* if it has a left adjoint $F$ and the comparison functor $K : D \to C^T$ of $T = GF$ is an equivalence.

**Definition (Split coequalizer).** A diagram $f, g : A \to B$ and $e : B \to Q$ is a *split coequalizer* if there are $s : Q \to B$ and $t : B \to A$ with
$$e \circ f = e \circ g, \qquad e \circ s = \mathrm{id}_Q, \qquad g \circ t = \mathrm{id}_B, \qquad f \circ t = s \circ e.$$
For a functor $G : D \to C$, a pair $f, g : A \to B$ in $D$ is *$G$-split* if $Gf, Gg$ have a split coequalizer in $C$. *Creation* of their coequalizers is as in Chapter 4: each split coequalizer $e$ of $Gf, Gg$ lifts uniquely to a map $\bar e$ with $G\bar e = e$, and $\bar e$ is a coequalizer.

### Theorems and proofs

**Proposition (Kleisli adjunction).** $C_T$ is a category, $F_T$ and $G_T$ are functors, $F_T \dashv G_T$, and the monad of this adjunction is $T$.

*Proof.* For $f : X \to TY$, $\eta_Y \circ_T f = \mu_Y \circ T\eta_Y \circ f = f$ and $f \circ_T \eta_X = \mu_Y \circ Tf \circ \eta_X = \mu_Y \circ \eta_{TY} \circ f = f$. For $h : Z \to TW$, the naturality of $\mu$ gives $\mu_{TW} \circ TTh = Th \circ \mu_Z$, so
$$(h \circ_T g) \circ_T f = \mu_W \circ T\mu_W \circ TTh \circ Tg \circ f = \mu_W \circ \mu_{TW} \circ TTh \circ Tg \circ f = \mu_W \circ Th \circ \mu_Z \circ Tg \circ f = h \circ_T (g \circ_T f).$$
The bijection $\mathrm{Hom}_{C_T}(F_T X, Y) = \mathrm{Hom}_C(X, G_T Y)$ is the identity, natural since $f \circ_T F_T h = f \circ h$ and $k \circ_T f = G_T(k) \circ f$. Then $G_T F_T f = \mu_Y \circ T\eta_Y \circ Tf = Tf$, the unit is $\eta$, the counit at $Y$ is $\mathrm{id}_{TY}$, and the multiplication is $G_T(\mathrm{id}_{TX}) = \mu_X$. $\square$

**Theorem (Kleisli is initial, Eilenberg-Moore is terminal).** Let $F \dashv G$, with $F : C \to D$, have the monad $T$. Then there is a unique functor $L : C_T \to D$ with $L F_T = F$ and $G L = G_T$, and a unique functor $K : D \to C^T$ with $K F = F^T$ and $G^T K = G$.

*Proof.* $K$ exists by Section 1. For uniqueness, $G^T K = G$ forces $KB = (GB, h_B)$ and $Kf = Gf$, and $KF = F^T$ forces $h_{FX} = \mu_X$. Then $K\varepsilon_B = G\varepsilon_B$ is a morphism of algebras $(TGB, \mu_{GB}) \to (GB, h_B)$, so $G\varepsilon_B \circ \mu_{GB} = h_B \circ TG\varepsilon_B$. Compose on the right with $T\eta_{GB}$: a unit law and a triangle identity give $G\varepsilon_B = h_B$.

For $L$, $L F_T = F$ forces $LX = FX$. For $f : X \to TY$, the map $Lf : FX \to FY$ has $G(Lf) = G_T f = \mu_Y \circ Tf$. Its transpose under $F \dashv G$ is $G(Lf) \circ \eta_X = \mu_Y \circ Tf \circ \eta_X = \mu_Y \circ \eta_{TY} \circ f = f$. So $Lf$ is the transpose $\varepsilon_{FY} \circ Ff$ of $f$, which proves uniqueness. For existence, put $Lf = \varepsilon_{FY} \circ Ff$. A triangle identity gives $L\eta_X = \mathrm{id}$. For $g : Y \to TZ$, the naturality of $\varepsilon$ at $Fg$ and at $\varepsilon_{FZ}$ turns $Lg \circ Lf$ into $\varepsilon_{FZ} \circ FG\varepsilon_{FZ} \circ FTg \circ Ff = L(g \circ_T f)$. The equations $GL = G_T$ and $LF_T = F$ are direct. $\square$

::: mathlib
`CategoryTheory.Kleisli.Adjunction.adj` · `Mathlib.CategoryTheory.Monad.Kleisli`

`Kleisli.Adjunction.adj T : toKleisli T ⊣ fromKleisli T` is the Kleisli adjunction. The index of this edition has no declaration for the category of adjunctions with a given monad, so the theorem above is not stated as initiality in Mathlib.

<?decl CategoryTheory.Kleisli.Adjunction.adj?>
:::

**Proposition (The forgetful functor creates limits).** Let $T$ be a monad on $C$ and $D : J \to C^T$ a diagram with $Dj = (A_j, a_j)$. Let $(P, p_j)$ be a limit of $G^T D$ in $C$. Then there is a unique $a : TP \to P$ that makes each $p_j$ a morphism of algebras, $(P, a)$ is an algebra, and $((P, a), p_j)$ is a limit of $D$.

*Proof.* For $u : j \to k$ in $J$, $Du \circ a_j \circ Tp_j = a_k \circ T(Du) \circ Tp_j = a_k \circ Tp_k$, so the maps $a_j \circ Tp_j$ form a cone on $G^T D$ with vertex $TP$. So there is a unique $a$ with $p_j \circ a = a_j \circ Tp_j$, that is, with each $p_j$ a morphism of algebras. Now $p_j \circ a \circ \eta_P = a_j \circ Tp_j \circ \eta_P = a_j \circ \eta_{A_j} \circ p_j = p_j$, so $a \circ \eta_P = \mathrm{id}$. Also
$$p_j \circ a \circ Ta = a_j \circ T(a_j \circ Tp_j) = a_j \circ \mu_{A_j} \circ TTp_j = a_j \circ Tp_j \circ \mu_P = p_j \circ a \circ \mu_P,$$
so $a \circ Ta = a \circ \mu_P$. A cone $q_j : (B, b) \to Dj$ gives a unique $q : B \to P$ with $p_j \circ q = q_j$, a morphism of algebras because $p_j \circ q \circ b = a_j \circ Tq_j = p_j \circ a \circ Tq$. $\square$

So $C^T$ has every limit that $C$ has.

**Lemma (Split coequalizers are absolute).** A split coequalizer $e$ of $f, g$ is a coequalizer, and every functor sends it to a split coequalizer.

*Proof.* If $h \circ f = h \circ g$, then $h = h \circ g \circ t = h \circ f \circ t = h \circ s \circ e$, so $h$ factors through $e$. Uniquely, as $e \circ s = \mathrm{id}$ makes $e$ epi. Functors preserve the four equations. $\square$

**Lemma (Beck's coequalizer).** For an algebra $(A, a)$, the map $a : TA \to A$ is a split coequalizer of $Ta, \mu_A : TTA \to TA$ in $C$, with $s = \eta_A$ and $t = \eta_{TA}$. Also $a : (TA, \mu_A) \to (A, a)$ is a coequalizer of $Ta, \mu_A$ in $C^T$.

*Proof.* The equations are $a \circ Ta = a \circ \mu_A$, $a \circ \eta_A = \mathrm{id}$, $\mu_A \circ \eta_{TA} = \mathrm{id}$, and $Ta \circ \eta_{TA} = \eta_A \circ a$ by the naturality of $\eta$. For the second claim, let $h : (TA, \mu_A) \to (B, b)$ be a morphism of algebras with $h \circ Ta = h \circ \mu_A$. Its factorization in $C$ is $k = h \circ \eta_A$. It is a morphism of algebras: $b \circ Tk = b \circ Th \circ T\eta_A = h \circ \mu_A \circ T\eta_A = h = k \circ a$. $\square$

**Theorem (Beck's monadicity theorem).** Let $G : D \to C$ have a left adjoint $F$. Then $G$ is monadic if and only if $G$ creates coequalizers of $G$-split pairs.

*Proof.* The main steps. Only if: it is enough to treat $G^T$. Let $f, g : (A, a) \to (B, b)$ be morphisms of algebras with a split coequalizer $e : B \to Q$ in $C$. By the lemma, $Te$ is a coequalizer of $Tf, Tg$, and $TTe$ is epi. Since $e \circ b \circ Tf = e \circ f \circ a = e \circ b \circ Tg$, there is a unique $q$ with $q \circ Te = e \circ b$, that is, a unique structure that makes $e$ a morphism of algebras. The laws for $q$ follow from those of $b$, as $e$ and $TTe$ are epi. If $h = k \circ e$ is a morphism of algebras to $(Z, z)$, then $k \circ q \circ Te = z \circ Tk \circ Te$, so $k$ is one.

If: the pair $Fa, \varepsilon_{FA} : FTA \to FA$ is $G$-split, since $G$ sends it to $Ta, \mu_A$. Let $M(A, a)$ be its created coequalizer. A map $M(A, a) \to B$ is a map $FA \to B$ that coequalizes the pair, and by transposition a morphism of algebras $(A, a) \to KB$. So $M \dashv K$. The unit is an isomorphism, since $G$ sends $FA \to M(A, a)$ to a coequalizer of $Ta, \mu_A$, which is $a$. For the counit, $G$ sends the fork $\varepsilon_B$ of $FG\varepsilon_B, \varepsilon_{FGB}$ to Beck's split coequalizer of $KB$, so $\varepsilon_B$ is a coequalizer and $MKB \to B$ is an isomorphism. $\square$

::: mathlib
`CategoryTheory.Monad.monadicOfCreatesGSplitCoequalizers` · `Mathlib.CategoryTheory.Monad.Monadicity`

From `adj : F ⊣ G` and the class `Monad.CreatesColimitOfIsSplitPair G`, this definition builds `MonadicRightAdjoint G`, which bundles the adjunction and the equivalence $K$. The converse is `Monad.createsGSplitCoequalizersOfMonadic`. The variant `Monad.monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms` asks that $D$ has and $G$ preserves reflexive coequalizers and that $G$ reflects isomorphisms. The instance `Monad.forgetCreatesLimits` is the proposition on limits, and `monadicCreatesLimits` transfers it to any monadic functor. Split coequalizers are `IsSplitCoequalizer f g π`, with `rightSection` for $s$ and `leftSection` for $t$, and `G.IsSplitPair f g` says that a pair is `G`-split. Beck's coequalizer is `Monad.beckSplitCoequalizer`, stated as `IsSplitCoequalizer (T.map X.a) (T.μ.app X.A) X.a`,, and `Monad.beckAlgebraCoequalizer` is the coequalizer in `T.Algebra`.

<?decl CategoryTheory.Monad.monadicOfCreatesGSplitCoequalizers?>

<?decl CategoryTheory.Monad.forgetCreatesLimits?>
:::

### Examples

**Example (Groups are monadic over sets).** Let $G : \mathbf{Grp} \to \mathbf{Set}$ be the forgetful functor, with the free group as left adjoint (Chapter 5). Let $f, g : H \to K$ be homomorphisms, and $e : K \to Q$ a split coequalizer of sets with $s, t$. The image $R = \{(f(x), g(x))\}$ of $(f, g)$ is a subgroup of $K \times K$, and $(f(t k), g(t k)) = (s e k, k) \in R$. Since $R$ is a subgroup, $(s e k_1 \cdot s e k_2, k_1 k_2) \in R$, and $e \circ f = e \circ g$ gives $e(k_1 k_2) = e(s e k_1 \cdot s e k_2)$. Define $q_1 q_2 = e(s q_1 \cdot s q_2)$ on $Q$. Then $e(k_1 k_2) = e(k_1) e(k_2)$. As $e$ is surjective, the axioms pass from $K$ to $Q$, and the law is unique. If a homomorphism $\varphi$ has $\varphi f = \varphi g$, the unique map $\psi$ with $\psi \circ e = \varphi$ is a homomorphism, as $\psi(e k \cdot e k') = \varphi(k k') = \psi(e k)\psi(e k')$. So $G$ creates the coequalizer, and Beck's theorem gives $\mathbf{Grp} \simeq \mathbf{Set}^T$. The index of this edition has no declaration that this forgetful functor is monadic.

**Counterexample (Topological spaces).** The forgetful functor $U : \mathbf{Top} \to \mathbf{Set}$ has the discrete topology as left adjoint, so $T$ is the identity monad. An algebra has $a = a \circ \eta_A = \mathrm{id}$, so $K = U$ up to isomorphism. But the identity map from a discrete two-point space to an indiscrete one is a continuous bijection, not a homeomorphism (Volume 13). So $U$ does not reflect isomorphisms, while monadic functors do.

**Remark.** The algebras of the ultrafilter monad on sets are the compact Hausdorff spaces: the structure map sends an ultrafilter to its limit. This is a theorem of Manes.

### The library around it

::: mathlib
`Compactum` · `Mathlib.Topology.Category.Compactum`

`Compactum` is `Monad.Algebra (ofTypeMonad Ultrafilter)`, from the Lean monad `Ultrafilter.monad`. The instance `compactumToCompHaus.isEquivalence` says that `compactumToCompHaus` is an equivalence with compact Hausdorff spaces, which is the remark.
:::

### Exercises

1. (A) Describe the Kleisli category of the maybe monad $X \sqcup \{\ast\}$ on $\mathbf{Set}$ as sets with partial functions.
2. (A) Show that the Kleisli category of the power set monad is the category of sets with relations, and that $\circ_T$ is the composition of relations.
3. (A) Show that $G_T$ is faithful for every monad. Hint: compose with $\eta_X$.
4. (B) Show that the inclusion of a reflective subcategory is monadic.
5. (C) Let $\mathbf{Field}$ be the category of fields. Show that the forgetful functor $\mathbf{Field} \to \mathbf{Set}$ has no left adjoint, so it is not monadic. Hint: a left adjoint would give an initial field.

### Notes and history

The Kleisli construction is in Kleisli's paper of 1965, and the algebras in Eilenberg and Moore's paper of the same year. Beck proved the monadicity theorem in his thesis; it is in Chapter VI of Mac Lane's *Categories for the Working Mathematician* (1971).

### Reference

<?reference?>
