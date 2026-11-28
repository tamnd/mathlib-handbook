---
title: Group schemes
kind: theory
modules:
  - Mathlib.AlgebraicGeometry.Group.Abelian
  - Mathlib.AlgebraicGeometry.Group.Affine
  - Mathlib.AlgebraicGeometry.Group.Smooth
explains:
  E3: [AlgebraicGeometry.algSpec, AlgebraicGeometry.hopfSpec, AlgebraicGeometry.essImage_hopfSpec, AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral, AlgebraicGeometry.smooth_of_grpObj]
  E2: [AlgebraicGeometry.algΓ, AlgebraicGeometry.algΓAlgSpecAdjunction, AlgebraicGeometry.algSpec.fullyFaithful, AlgebraicGeometry.braidedAlgSpec, AlgebraicGeometry.bialgSpec, AlgebraicGeometry.hopfSpec.fullyFaithful, AlgebraicGeometry.essImage_algSpec, AlgebraicGeometry.essImage_bialgSpec, AlgebraicGeometry.specOverSpec, AlgebraicGeometry.instGrpObjSpecAsOverSpec, AlgebraicGeometry.instCommGrpObjSpecAsOverSpec, AlgebraicGeometry.Spec.mapMulEquiv, AlgebraicGeometry.pullbackSpecIso', AlgebraicGeometry.isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed, AlgebraicGeometry.instIsClosedImmersionLeftSchemeOneOverSpecOf]
  E1: auto
families: []
requires: [V11.C03, V24.C05, V24.C07, V26.C07, V28.C04, V28.C05, V28.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Group schemes

### Overview

A group scheme over $S$ is an $S$-scheme $G$ with a multiplication $G \times_S G \to G$, a unit $S \to G$ and an inverse $G \to G$ that satisfy the group axioms as equations of morphisms. Equivalently, for each $S$-scheme $T$ the set $G(T)$ of $S$-morphisms $T \to G$ is a group, naturally in $T$. The multiplicative group $\mathbb{G}_m$ with $\mathbb{G}_m(T) = \Gamma(T, \mathcal{O}_T)^\times$ and the additive group $\mathbb{G}_a$ with $\mathbb{G}_a(T) = \Gamma(T, \mathcal{O}_T)$ are the first examples, and elliptic curves are the first proper examples.

Mathlib defines a group scheme as a group object in the cartesian monoidal category of schemes over $S$. This section proves that affine group schemes over $\operatorname{Spec} R$ are the spectra of commutative Hopf algebras over $R$, that a proper geometrically integral group scheme over a field is commutative, and that a geometrically reduced group scheme locally of finite type over a field is smooth.

### Definitions

**Definition (Group scheme).** Let $S$ be a scheme. The category of $S$-schemes has finite products, given by $S$ and fiber products over $S$. A *group scheme over $S$* is a group object $G$ in this category: an $S$-scheme with $S$-morphisms $\mu : G \times_S G \to G$, $\eta : S \to G$ and $\iota : G \to G$ such that the associativity, unit and inverse diagrams commute. It is *commutative* when $\mu$ composed with the swap of the factors is $\mu$.

A *monoid scheme* has $\mu$ and $\eta$ only. By the Yoneda lemma a group object structure on $G$ is the same as a group structure on each $G(T)$, natural in $T$.

**Definition (Hopf algebra).** Let $R$ be a commutative ring. A *commutative Hopf algebra* over $R$ is a commutative $R$-algebra $A$ with algebra maps $\Delta : A \to A \otimes_R A$, $\varepsilon : A \to R$ and a map $S : A \to A$ satisfying the coassociativity, counit and antipode identities. It is *cocommutative* when $\Delta$ composed with the swap is $\Delta$.

**Definition (The functors $\operatorname{Spec}$ and $\Gamma$ over a base).** Let $R$ be a commutative ring. The functor $\operatorname{Spec}$ sends a commutative $R$-algebra $A$ to $\operatorname{Spec} A$ with its structure map to $\operatorname{Spec} R$. The functor $\Gamma$ sends an $S$-scheme $X \to \operatorname{Spec} R$ to the $R$-algebra $\Gamma(X, \mathcal{O}_X)$.

**Definition (Geometric properties).** A scheme $X$ over a field $K$ is *geometrically integral* when $X \times_K \operatorname{Spec} L$ is integral for each field extension $L/K$. It is *geometrically reduced* when each such base change is reduced.

### Theorems and proofs

**Theorem (Spec and $\Gamma$ are adjoint).** The functor $\Gamma$ from $\operatorname{Spec} R$-schemes to the opposite of $R$-algebras is left adjoint to $\operatorname{Spec}$. The functor $\operatorname{Spec}$ is fully faithful, and its essential image is the class of affine $\operatorname{Spec} R$-schemes.

*Proof.* Step 1. For a scheme $X$ and a ring $A$, morphisms $X \to \operatorname{Spec} A$ correspond to ring maps $A \to \Gamma(X, \mathcal{O}_X)$. This is the adjunction between $\Gamma$ and $\operatorname{Spec}$ on all schemes.

Step 2. Under this bijection, a morphism $X \to \operatorname{Spec} A$ commutes with the maps to $\operatorname{Spec} R$ exactly when the ring map $A \to \Gamma(X, \mathcal{O}_X)$ commutes with the maps from $R$. So the bijection restricts to $R$-algebra maps and $S$-morphisms.

Step 3. For $X = \operatorname{Spec} B$ one has $\Gamma(X, \mathcal{O}_X) = B$, so $\operatorname{Spec}$ is fully faithful. An $S$-scheme is in the essential image exactly when it is isomorphic to some $\operatorname{Spec} B$, which means that it is affine. $\square$

**Theorem (Affine group schemes and Hopf algebras).** The functor $A \mapsto \operatorname{Spec} A$ gives an equivalence between the opposite of the category of commutative Hopf algebras over $R$ and the category of affine group schemes over $\operatorname{Spec} R$. Cocommutative Hopf algebras correspond to commutative group schemes.

*Proof.* Step 1. The functor $\operatorname{Spec}$ preserves finite products, viewed as a functor from the opposite of $R$-algebras. The product in that opposite category is the tensor product, and $\operatorname{Spec}(A \otimes_R B) \cong \operatorname{Spec} A \times_{\operatorname{Spec} R} \operatorname{Spec} B$. The terminal object $R$ goes to $\operatorname{Spec} R$.

Step 2. A fully faithful functor that preserves finite products induces a fully faithful functor on group objects. Group objects in the opposite of $R$-algebras are cogroup objects in $R$-algebras: an algebra $A$ with maps $\Delta : A \to A \otimes_R A$, $\varepsilon : A \to R$ and $S : A \to A$ that satisfy the dual axioms. These are the commutative Hopf algebras over $R$.

Step 3. Let $G$ be an affine group scheme. Then $G \cong \operatorname{Spec} A$ with $A = \Gamma(G, \mathcal{O}_G)$, and $G \times_S G$ is affine with ring $A \otimes_R A$. By full faithfulness the maps $\mu$, $\eta$ and $\iota$ come from unique maps $\Delta$, $\varepsilon$ and $S$, and the axioms transfer. So the functor is essentially surjective onto affine group schemes.

Step 4. The swap of $G \times_S G$ corresponds to the swap of $A \otimes_R A$, so $\mu$ commutes with the swap exactly when $\Delta$ does. $\square$

**Corollary (Points of an affine group scheme).** For a Hopf algebra $A$ and an $R$-algebra $T$, the group $G(\operatorname{Spec} T)$ of $G = \operatorname{Spec} A$ is the set of $R$-algebra maps $A \to T$ with the convolution product $(\varphi * \psi)(a) = \sum \varphi(a_{(1)}) \psi(a_{(2)})$, where $\Delta(a) = \sum a_{(1)} \otimes a_{(2)}$.

*Proof.* A point $\operatorname{Spec} T \to G$ is an algebra map $\varphi : A \to T$. The product of two points is the composite $\operatorname{Spec} T \to G \times_S G \to G$. On rings this is $A \xrightarrow{\Delta} A \otimes_R A \xrightarrow{\varphi \otimes \psi} T \otimes_R T \to T$, the last map being multiplication. That composite is the convolution. $\square$

**Lemma (Rigidity).** Let $k$ be an algebraically closed field. Let $X$ be a proper integral $k$-scheme, $Y$ and $Z$ integral separated $k$-schemes of finite type, and $X \times_k Y$ integral. Let $f : X \times_k Y \to Z$ with $f(X \times \{y_0\}) = \{z_0\}$ for a closed point $y_0$. Then for each closed point $x_0$ of $X$ one has $f = f \circ (x_0, p_2)$, so $f(x, y) = f(x_0, y)$.

*Proof.* Step 1. Choose an affine open $V \ni z_0$ and let $F = Z \setminus V$. The set $f^{-1}(F)$ is closed, and its image $p_2(f^{-1}(F))$ in $Y$ is closed because $X$ is proper. It does not contain $y_0$, since $f(X \times \{y_0\}) = \{z_0\} \subseteq V$. So $W = Y \setminus p_2(f^{-1}(F))$ is an open neighbourhood of $y_0$.

Step 2. Let $y \in W$ be closed. Then $f$ maps $X \times \{y\} \cong X$ into the affine $V$. A morphism from a proper integral $k$-scheme to an affine scheme factors through $\operatorname{Spec} \Gamma(X, \mathcal{O}_X)$, and $\Gamma(X, \mathcal{O}_X)$ is a finite field extension of $k$, so it equals $k$. So $f(X \times \{y\})$ is one closed point.

Step 3. So $f$ and $g = f \circ (x_0, p_2)$ agree on the closed points of the open set $X \times W$, which are the pairs of closed points since $k$ is algebraically closed. The equalizer of $f$ and $g$ is a closed subscheme, since $Z$ is separated. It contains all closed points of $X \times W$, which are dense because $X \times W$ is of finite type over $k$. Since $X \times W$ is reduced, $f$ and $g$ agree on $X \times W$. The open $X \times W$ is dense in the integral scheme $X \times_k Y$, so $f = g$ by the uniqueness theorem for maps from reduced schemes to separated schemes. $\square$

**Theorem (Proper group schemes are commutative).** Let $K$ be a field and $G$ a group scheme over $K$ that is proper and geometrically integral. Then $G$ is commutative.

*Proof.* Step 1. Assume first that $K$ is algebraically closed. Let $\gamma : G \times G \to G$ be the commutator $\gamma(x, y) = x y x^{-1} y^{-1}$, defined as a composite of $\mu$, $\iota$ and the diagonals. The product $G \times_K G$ is integral, because $G$ is geometrically integral. For the unit $e$ one has $\gamma(x, e) = e$ for each $x$, so $\gamma(G \times \{e\}) = \{e\}$.

Step 2. Apply the rigidity lemma with $X = Y = Z = G$, $y_0 = e$ and $x_0 = e$. Then $\gamma(x, y) = \gamma(e, y) = e$ for each $x, y$. So $\gamma$ is the constant map to $e$, which means $\mu = \mu \circ \text{swap}$.

Step 3. For general $K$ let $\bar{K}$ be an algebraic closure and $G_{\bar{K}}$ the base change. It is a proper integral group scheme over $\bar{K}$, and $G_{\bar{K}} \times G_{\bar{K}}$ is integral since $G$ is geometrically integral. By step 2 the morphisms $\mu$ and $\mu \circ \text{swap}$ agree after base change to $\bar{K}$. The map $\operatorname{Spec} \bar{K} \to \operatorname{Spec} K$ is faithfully flat and quasi-compact, so $G \times_K G \times_K \bar{K} \to G \times_K G$ is an fpqc cover. Representable functors are fpqc sheaves, so two morphisms that agree on an fpqc cover are equal. So $\mu = \mu \circ \text{swap}$. $\square$

Mathlib proves the algebraically closed case by a different route: it uses Zariski's main theorem to find an open $U \ni e$ over which $\gamma$ factors through a finite scheme, then shows that $\gamma$ is constant on each $\{x\} \times G$ by irreducibility.

**Theorem (Reduced group schemes are smooth).** Let $K$ be a field and $G$ a group scheme locally of finite type over $K$ that is geometrically reduced. Then $G \to \operatorname{Spec} K$ is smooth.

*Proof.* Step 1. Assume first that $K$ is algebraically closed, so $G$ is reduced. The field $K$ is perfect, so the smooth locus $G^{\mathrm{sm}}$ of $G \to \operatorname{Spec} K$ is a dense open. $G$ is nonempty, since it has the unit point. So $G^{\mathrm{sm}}$ has a closed point $y$, because $G$ is locally of finite type over a field and so a Jacobson scheme.

Step 2. Suppose $G^{\mathrm{sm}} \ne G$. Its complement is a nonempty closed set, so it contains a closed point $x$, again by the Jacobson property. The closed points $x$ and $y$ are $K$-points, since $K$ is algebraically closed. Right multiplication by $x^{-1}$ followed by right multiplication by $y$ is an automorphism $\alpha$ of $G$ over $K$ with $\alpha(x) = y$.

Step 3. An automorphism over $K$ maps the smooth locus to itself, because smoothness at a point is preserved by isomorphisms over $K$. So $x = \alpha^{-1}(y) \in G^{\mathrm{sm}}$, which contradicts the choice of $x$. So $G^{\mathrm{sm}} = G$.

Step 4. For general $K$ the base change $G_{\bar{K}}$ is a reduced group scheme locally of finite type over $\bar{K}$, so it is smooth by step 3. Smoothness descends along the surjective flat quasi-compact morphism $\operatorname{Spec} \bar{K} \to \operatorname{Spec} K$. $\square$

### Examples

**Example (The additive group).** Let $A = R[t]$ with $\Delta(t) = t \otimes 1 + 1 \otimes t$, $\varepsilon(t) = 0$ and $S(t) = -t$. Check of the antipode identity: $m \circ (S \otimes \mathrm{id}) \circ \Delta$ sends $t$ to $-t + t = 0 = \varepsilon(t)$. An $R$-algebra map $\varphi : R[t] \to T$ is the element $\varphi(t) \in T$. The convolution gives $(\varphi * \psi)(t) = \varphi(t) \cdot 1 + 1 \cdot \psi(t)$. So $\mathbb{G}_a(\operatorname{Spec} T) = (T, +)$.

**Example (The multiplicative group).** Let $A = R[t, t^{-1}]$ with $\Delta(t) = t \otimes t$, $\varepsilon(t) = 1$ and $S(t) = t^{-1}$. A point is a unit $u = \varphi(t)$ of $T$, and $(\varphi * \psi)(t) = \varphi(t)\psi(t)$. So $\mathbb{G}_m(\operatorname{Spec} T) = T^\times$. The coproduct is cocommutative, so $\mathbb{G}_m$ is commutative. $\mathbb{G}_m$ is affine of dimension $1$, so it is not proper, and the theorem on proper group schemes does not apply to it.

**Example (Roots of unity).** For $n \ge 1$ the ideal $(t^n - 1)$ of $R[t, t^{-1}]$ is a Hopf ideal: $\Delta(t^n - 1) = t^n \otimes t^n - 1 \otimes 1 = (t^n - 1) \otimes t^n + 1 \otimes (t^n - 1)$, $\varepsilon(t^n - 1) = 0$ and $S(t^n - 1) = t^{-n} - 1 = -t^{-n}(t^n - 1)$. The quotient defines $\mu_n = \operatorname{Spec} R[t]/(t^n - 1)$ with $\mu_n(\operatorname{Spec} T) = \{u \in T : u^n = 1\}$.

**Counterexample (A group scheme that is not smooth).** Let $k$ be a field of characteristic $p > 0$. In $k[t]$ one has $t^p - 1 = (t - 1)^p$, so $\mu_p = \operatorname{Spec} k[t]/((t - 1)^p)$. The element $t - 1$ is nilpotent and nonzero, so $\mu_p$ is not reduced and not geometrically reduced. A smooth scheme over a field is reduced, so $\mu_p$ is not smooth. The hypothesis of the smoothness theorem cannot be dropped.

**Example (A non-commutative affine group).** $\mathrm{GL}_2 = \operatorname{Spec} R[x_{11}, x_{12}, x_{21}, x_{22}, 1/\det]$ with $\Delta(x_{ij}) = \sum_l x_{il} \otimes x_{lj}$ has $\mathrm{GL}_2(\operatorname{Spec} T)$ the group of invertible $2 \times 2$ matrices over $T$. It is not commutative for $T = R \neq 0$, since the matrices $\begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$ and $\begin{pmatrix} 1 & 0 \\ 1 & 1 \end{pmatrix}$ do not commute. It is affine and not proper. An elliptic curve is proper and geometrically integral, so its group law is commutative.

### The library around it

::: mathlib
`AlgebraicGeometry.algSpec` · `Mathlib.AlgebraicGeometry.Group.Affine`

`algSpec R : (CommAlgCat R)ᵒᵖ ⥤ Over (Spec R)` and `algΓ R` form the adjunction `algΓAlgSpecAdjunction`. `algSpec.fullyFaithful` and `essImage_algSpec`, which says `IsAffine G.left`, are the first theorem. The instance `braidedAlgSpec` makes `algSpec` braided monoidal, which is step 1 of the second theorem.

<?decl AlgebraicGeometry.algSpec?>
:::

::: mathlib
`AlgebraicGeometry.hopfSpec` · `Mathlib.AlgebraicGeometry.Group.Affine`

`hopfSpec R : (CommHopfAlgCat R)ᵒᵖ ⥤ Grp (Over <| Spec R)` is `algSpec` on group objects, with `hopfSpec.fullyFaithful` and `essImage_hopfSpec`. The monoid version is `bialgSpec`. For a Hopf algebra `A`, the instances `instGrpObjSpecAsOverSpec` and, under `IsCocomm R A`, `instCommGrpObjSpecAsOverSpec` put the structure on `(Spec A).asOver (Spec R)`, where `specOverSpec` gives the structure map. Conversely an affine group scheme gets a `HopfAlgebra R Γ(G, ⊤)` instance. `Spec.mapMulEquiv` is the corollary on points, and `pullbackSpecIso'` is the tensor product formula.

<?decl AlgebraicGeometry.hopfSpec?>
:::

::: mathlib
`AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral` · `Mathlib.AlgebraicGeometry.Group.Abelian`

For `G : Over (Spec (.of K))` with `[IsProper G.hom] [GeometricallyIntegral G.hom] [GrpObj G]` the conclusion is `IsCommMonObj G`, tagged Stacks 0BFD. The algebraically closed case is `isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed`, with integrality of `(G ⊗ G).left` as a hypothesis. An instance in the file says that the unit `η[G].left` is a closed immersion.

<?decl AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral?>
:::

::: mathlib
`AlgebraicGeometry.smooth_of_grpObj` · `Mathlib.AlgebraicGeometry.Group.Smooth`

For `f : G ⟶ Spec (.of K)` with `[LocallyOfFiniteType f]`, `[GrpObj (Over.mk f)]` and `[GeometricallyReduced f]` the conclusion is `Smooth f`. The algebraically closed case is a private lemma that uses the dense smooth locus over a perfect field and right multiplication, and the general case descends along `AlgebraicClosure K`.

<?decl AlgebraicGeometry.smooth_of_grpObj?>
:::

Common errors of a learner: a group scheme in Mathlib is a `GrpObj` instance on an object of `Over S`, not a scheme with a group structure on its points. The space of $G \times_S G$ is not the product of the spaces, so the commutator cannot be studied point by point without care. The coproduct of $\mathbb{G}_a$ is $t \otimes 1 + 1 \otimes t$, not $t \otimes t$. The index of this edition has no declarations named for $\mathbb{G}_a$ or $\mathbb{G}_m$; they arise through `hopfSpec` from Hopf algebra structures on polynomial and Laurent polynomial rings.

### Exercises

1. (A) Check the counit identity $(\varepsilon \otimes \mathrm{id}) \circ \Delta = \mathrm{id}$ for $\mathbb{G}_m$ on the element $t^3$. *Hint:* $\Delta(t^3) = t^3 \otimes t^3$.
2. (A) Compute $\mu_4(\operatorname{Spec} \mathbb{C})$ and $\mu_4(\operatorname{Spec} \mathbb{R})$. *Hint:* Solve $u^4 = 1$.
3. (B) Show that $\alpha_p = \operatorname{Spec} k[t]/(t^p)$ with $\Delta(t) = t \otimes 1 + 1 \otimes t$ is a group scheme in characteristic $p$, and that it is not smooth. *Hint:* Expand $(t \otimes 1 + 1 \otimes t)^p$.
4. (B) Show that the determinant $\mathrm{GL}_2 \to \mathbb{G}_m$ is a morphism of group schemes. *Hint:* Check that the ring map $t \mapsto \det$ respects $\Delta$ on $t$.
5. (C) Let $G$ be a group scheme over $K$ and $x$ a $K$-point. Show that right multiplication by $x$ is an isomorphism of $K$-schemes. *Hint:* Right multiplication by $\iota \circ x$ is an inverse.
6. (C) Show that a commutative Hopf algebra $A$ over a field gives a group scheme $\operatorname{Spec} A$ whose unit is a closed immersion. *Hint:* $\varepsilon : A \to k$ is surjective.

### Notes and history

Group schemes were developed by Grothendieck and his school, and SGA 3 is the standard reference for group schemes over a base. The rigidity lemma and the commutativity of abelian varieties are in Mumford's book on abelian varieties. The Mathlib sources follow the Stacks project for the commutativity theorem.

The Mathlib Authors of `Group.Affine` are Yaël Dillies, Christian Merten, Michał Mrugała and Andrew Yang. The Mathlib Authors of `Group.Abelian` are Andrew Yang and Christian Merten. The Mathlib Author of `Group.Smooth` is Andrew Yang.

### Reference

<?reference?>
