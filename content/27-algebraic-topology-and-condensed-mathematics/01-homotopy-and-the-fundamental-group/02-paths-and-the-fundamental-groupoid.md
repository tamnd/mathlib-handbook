---
title: Paths and the fundamental groupoid
kind: theory
modules:
  - Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
  - Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
  - Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
  - Mathlib.AlgebraicTopology.FundamentalGroupoid.PUnit
  - Mathlib.AlgebraicTopology.FundamentalGroupoid.Product
  - Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
  - Mathlib.Topology.Homotopy.Path
  - Mathlib.Topology.Homotopy.TopCat.Basic
  - Mathlib.Topology.Homotopy.TopCat.Path
  - Mathlib.Topology.Homotopy.TopCat.ToSSet
  - Mathlib.Topology.Homotopy.TopCat.ZerothHomotopy
explains:
  E3: [Path.Homotopy, Path.Homotopic, Path.Homotopic.Quotient, FundamentalGroupoid, FundamentalGroup, FundamentalGroupoid.map, FundamentalGroupoidFunctor.homotopicMapsNatIso, SimplyConnectedSpace]
  E2: [Path.Homotopy.hcomp, Path.Homotopy.reparam, ContinuousMap.Homotopy.evalAt, Path.Homotopic.Quotient.trans, Path.Homotopic.Quotient.symm, Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm, Path.Homotopy.reflTransSymm, Path.Homotopy.transRefl, Path.Homotopy.transAssoc, FundamentalGroupoid.fundamentalGroupoidFunctor, FundamentalGroup.mul_def, FundamentalGroup.map, FundamentalGroup.fundamentalGroupMulEquivOfPath, Path.Homotopic.map_trans_evalAt, FundamentalGroupoidFunctor.equivOfHomotopyEquiv, FundamentalGroupoidFunctor.prodIso, FundamentalGroupoid.punitEquivDiscretePUnit, simply_connected_iff_paths_homotopic, simply_connected_iff_loops_nullhomotopic, SimplyConnectedSpace.ofContractible, ContinuousMap.HomotopyEquiv.simplyConnectedSpace, IsSimplyConnected, TopCat.Homotopy, TopCat.Path, TopCat.Homotopy.toSSet, TopCat.zerothHomotopyEquiv]
  E1: auto
families: []
requires: [V05.C01, V13.C01, V13.C06, V24.C01, V24.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Paths and the fundamental groupoid

### Overview

A path in a space $X$ is a continuous map from the unit interval $I$ to $X$. Two paths with the same end points are homotopic when one can be deformed into the other with the end points fixed. The homotopy classes of paths form a category: the objects are the points of $X$, the morphisms from $x$ to $y$ are the classes of paths from $x$ to $y$, and composition runs one path and then the next. Each morphism has an inverse, the reversed path, so the category is a groupoid. This is the *fundamental groupoid* $\Pi_1(X)$. The automorphism group of a point $x$ is the *fundamental group* $\pi_1(X, x)$.

This section builds the fundamental groupoid, proves the groupoid laws, and shows that a continuous map induces a functor. It proves homotopy invariance: homotopic maps induce naturally isomorphic functors, and a homotopy equivalence induces an equivalence of groupoids. It computes the groupoid of a product and of a point, and it studies simply connected spaces. It ends with the forms of these objects on the category `TopCat`.

### Definitions

**Definition (Path, path homotopy).** A *path* from $x$ to $y$ in $X$ is a continuous map $\gamma : I \to X$ with $\gamma(0) = x$ and $\gamma(1) = y$. A *path homotopy* from $\gamma_0$ to $\gamma_1$, two paths from $x$ to $y$, is a homotopy $H : I \times I \to X$ from $\gamma_0$ to $\gamma_1$ relative to $\{0, 1\}$. So $H(s, 0) = x$ and $H(s, 1) = y$ for all $s$. Write $\gamma_0 \simeq \gamma_1$ when one exists, and $[\gamma]$ for the class of $\gamma$.

By the previous section, path homotopy is an equivalence relation on the paths from $x$ to $y$.

**Definition (Operations on paths).** For a path $\alpha$ from $x$ to $y$ and a path $\beta$ from $y$ to $z$, the *composite* $\alpha \cdot \beta$ is the path with $(\alpha \cdot \beta)(t) = \alpha(2t)$ for $t \le 1/2$ and $\beta(2t - 1)$ for $t \ge 1/2$. It is continuous by the pasting lemma. The *reverse* is $\bar\alpha(t) = \alpha(1 - t)$, and the *constant path* $c_x$ has $c_x(t) = x$. A continuous map $f : X \to Y$ sends $\alpha$ to the path $f \circ \alpha$.

**Definition (Fundamental groupoid, fundamental group).** The fundamental groupoid $\Pi_1(X)$ is the category whose objects are the points of $X$, with $\operatorname{Hom}(x, y)$ the set of classes $[\alpha]$ of paths from $x$ to $y$, identity $[c_x]$, and composition that sends $[\alpha]$ and $[\beta]$ to $[\alpha \cdot \beta]$. The fundamental group $\pi_1(X, x)$ is the group $\operatorname{Aut}(x)$ of $\Pi_1(X)$.

**Definition (Simply connected space).** A space $X$ is *simply connected* when $\Pi_1(X)$ is equivalent to the category with one object and one morphism. Equivalently, $X$ is nonempty and between any two points there is exactly one homotopy class of paths.

### Theorems and proofs

**Lemma (Composition respects homotopy).** If $\alpha \simeq \alpha'$ and $\beta \simeq \beta'$ are path homotopies, then $\alpha \cdot \beta \simeq \alpha' \cdot \beta'$, $\bar\alpha \simeq \bar\alpha'$ and $f \circ \alpha \simeq f \circ \alpha'$.

*Proof.* Let $F$ and $G$ be the homotopies. Define $H(s, t) = F(s, 2t)$ for $t \le 1/2$ and $G(s, 2t - 1)$ for $t \ge 1/2$. At $t = 1/2$ both give $y$, since $F$ and $G$ fix the end points. The pasting lemma gives continuity, and $H$ fixes $x$ and $z$. For the reverse use $F(s, 1 - t)$, and for the image use $f \circ F$. $\square$

**Lemma (Reparametrisation).** Let $\varphi : I \to I$ be continuous with $\varphi(0) = 0$ and $\varphi(1) = 1$. Then $\gamma \circ \varphi \simeq \gamma$ for each path $\gamma$.

*Proof.* Define $H(s, t) = \gamma((1 - s)\varphi(t) + s t)$. The convex combination of $\varphi(t)$ and $t$ lies in $I$, so $H$ is defined and continuous. At $s = 0$ it is $\gamma \circ \varphi$, at $s = 1$ it is $\gamma$. For $t = 0$ the argument is $0$, and for $t = 1$ it is $1$, so the end points stay fixed. $\square$

**Theorem (Groupoid laws).** For paths $\alpha : x \to y$, $\beta : y \to z$ and $\delta : z \to w$:
1. $(\alpha \cdot \beta) \cdot \delta \simeq \alpha \cdot (\beta \cdot \delta)$;
2. $c_x \cdot \alpha \simeq \alpha \simeq \alpha \cdot c_y$;
3. $\alpha \cdot \bar\alpha \simeq c_x$ and $\bar\alpha \cdot \alpha \simeq c_y$.

So $\Pi_1(X)$ is a groupoid, with $[\alpha]^{-1} = [\bar\alpha]$, and $\pi_1(X, x)$ is a group.

*Proof.* For (1), the path $(\alpha \cdot \beta) \cdot \delta$ runs $\alpha$ on $[0, 1/4]$, $\beta$ on $[1/4, 1/2]$ and $\delta$ on $[1/2, 1]$. So it equals $(\alpha \cdot (\beta \cdot \delta)) \circ \varphi$, where $\varphi(t) = 2t$ on $[0, 1/4]$, $\varphi(t) = t + 1/4$ on $[1/4, 1/2]$ and $\varphi(t) = (t + 1)/2$ on $[1/2, 1]$. Check the corners: $\varphi(1/4) = 1/2$ from both formulas, and $\varphi(1/2) = 3/4$ from both. Then on $[0,1/4]$ the composite is $\alpha(2 \cdot 2t) = \alpha(4t)$, as required. The reparametrisation lemma gives (1). For (2), $\alpha \cdot c_y = \alpha \circ \psi$ with $\psi(t) = \min(1, 2t)$, and $c_x \cdot \alpha = \alpha \circ \chi$ with $\chi(t) = \max(0, 2t - 1)$. For (3), define $H(s, t) = \alpha(2ts)$ for $t \le 1/2$ and $H(s, t) = \alpha((2 - 2t)s)$ for $t \ge 1/2$. Both formulas give $\alpha(s)$ at $t = 1/2$. At $s = 0$ the map is constant at $x$, and at $s = 1$ it is $\alpha \cdot \bar\alpha$. For each $s$, $H(s, 0) = H(s, 1) = \alpha(0) = x$. So $c_x \simeq \alpha \cdot \bar\alpha$. The second claim of (3) is the first one for $\bar\alpha$, since the reverse of $\bar\alpha$ is $\alpha$. $\square$

**Proposition (Change of base point).** A path $\alpha$ from $x$ to $y$ gives a group isomorphism $\pi_1(X, x) \to \pi_1(X, y)$, $[\gamma] \mapsto [\bar\alpha \cdot \gamma \cdot \alpha]$. So in a path connected space all the fundamental groups are isomorphic.

*Proof.* In any groupoid, an isomorphism $a : x \to y$ gives the conjugation $g \mapsto a^{-1} g a$ from $\operatorname{Aut}(x)$ to $\operatorname{Aut}(y)$. It is a homomorphism, since $a^{-1} g a \, a^{-1} h a = a^{-1} g h a$, and conjugation by $a^{-1}$ is its inverse. $\square$

**Proposition (Functoriality).** A continuous map $f : X \to Y$ gives a functor $f_* : \Pi_1(X) \to \Pi_1(Y)$ with $f_*(x) = f(x)$ and $f_*[\alpha] = [f \circ \alpha]$. It satisfies $(g \circ f)_* = g_* \circ f_*$ and $(\mathrm{id})_* = \mathrm{id}$. It restricts to a group homomorphism $\pi_1(X, x) \to \pi_1(Y, f(x))$.

*Proof.* The lemma on composition shows that $f_*$ is well defined. The equations $f \circ (\alpha \cdot \beta) = (f \circ \alpha) \cdot (f \circ \beta)$ and $f \circ c_x = c_{f(x)}$ hold pointwise. The last two claims hold pointwise as well. $\square$

**Theorem (Homotopy invariance).** Let $H$ be a homotopy from $f$ to $g : X \to Y$, and for $x \in X$ let $h_x$ be the path $s \mapsto H(s, x)$ from $f(x)$ to $g(x)$. For each path $\gamma$ from $x$ to $y$,
$$(f \circ \gamma) \cdot h_y \simeq h_x \cdot (g \circ \gamma).$$
So the classes $[h_x]$ form a natural isomorphism $f_* \cong g_*$.

*Proof.* Define $K : I \times I \to Y$ by $K(s, t) = H(s, \gamma(t))$. Let $\lambda$ and $\mu$ be two edge paths in $I \times I$ from $(0,0)$ to $(1,1)$. In coordinates $(s, t)$, $\lambda$ is $(0, 0) \to (0, 1) \to (1, 1)$, which under $K$ gives $(f \circ \gamma) \cdot h_y$; and $\mu$ is $(0, 0) \to (1, 0) \to (1, 1)$, which under $K$ gives $h_x \cdot (g \circ \gamma)$. The square $I \times I$ is convex, so the straight-line homotopy $(1 - r)\lambda + r\mu$ is a path homotopy from $\lambda$ to $\mu$ inside it. Composing with $K$ gives the claimed homotopy. The equation is the naturality square of $[h]$, and each $[h_x]$ is invertible. $\square$

**Corollary (Homotopy equivalences).** A homotopy equivalence $f : X \to Y$ induces an equivalence of categories $\Pi_1(X) \simeq \Pi_1(Y)$ and isomorphisms $\pi_1(X, x) \cong \pi_1(Y, f(x))$.

*Proof.* Let $g$ be a homotopy inverse. By the theorem, $g_* f_* = (g f)_* \cong \mathrm{id}_* = \mathrm{id}$ and $f_* g_* \cong \mathrm{id}$, so $f_*$ is an equivalence. An equivalence of categories is fully faithful, so it gives bijections $\operatorname{Aut}(x) \to \operatorname{Aut}(f(x))$, and these are homomorphisms by functoriality. $\square$

**Proposition (Products and the point).** For spaces $X$ and $Y$, $\Pi_1(X \times Y) \cong \Pi_1(X) \times \Pi_1(Y)$, and so $\pi_1(X \times Y, (x, y)) \cong \pi_1(X, x) \times \pi_1(Y, y)$. The groupoid of a one-point space has one object and one morphism.

*Proof.* A path in $X \times Y$ is a pair of paths, and a path homotopy in $X \times Y$ is a pair of path homotopies, because a map into a product is continuous exactly when both coordinates are. Composition and reversal act coordinate by coordinate. For a point, there is exactly one path, the constant one. $\square$

**Theorem (Simply connected spaces).** For a space $X$ the following are equivalent:
1. $X$ is simply connected;
2. $X$ is path connected and any two paths with the same end points are homotopic;
3. $X$ is path connected and every loop is homotopic to a constant loop.

A contractible space is simply connected.

*Proof.* (1) and (2) say the same thing: $\Pi_1(X)$ is equivalent to the trivial groupoid exactly when it is nonempty and each Hom set has one element. (2) gives (3) at once. For (3) implies (2), let $\alpha$ and $\beta$ be paths from $x$ to $y$. The loop $\alpha \cdot \bar\beta$ is homotopic to $c_x$, so $\alpha \simeq \alpha \cdot \bar\beta \cdot \beta \simeq c_x \cdot \beta \simeq \beta$ by the groupoid laws. A contractible space is homotopy equivalent to a point. By the corollary its groupoid is equivalent to the groupoid of a point, which is trivial. $\square$

### Examples

**Example (A loop in the plane).** Let $\gamma(t) = (\cos 2\pi t, \sin 2\pi t)$, a loop at $(1, 0)$ in $\mathbb{R}^2$. The map $H(s, t) = (1 - s)\gamma(t) + s(1, 0)$ is a path homotopy from $\gamma$ to the constant loop. Check the end points: $\gamma(0) = \gamma(1) = (1, 0)$, so $H(s, 0) = H(s, 1) = (1, 0)$ for all $s$. So $[\gamma]$ is trivial in $\pi_1(\mathbb{R}^2, (1, 0))$. The same argument works in every convex set, so every convex set is simply connected.

**Counterexample (The punctured plane).** In $\mathbb{R}^2 \setminus \{0\}$ the formula above fails. At $s = 1/2$ and $t = 1/2$ it gives $\frac12(-1, 0) + \frac12(1, 0) = (0, 0)$, which is not in the space. The failure of one formula does not prove that $\gamma$ is not nullhomotopic. Chapter 2 proves it, by the computation $\pi_1(S^1) \cong \mathbb{Z}$ and the homotopy equivalence $\mathbb{R}^2 \setminus \{0\} \simeq S^1$.

**Example (A reparametrisation).** Let $\gamma$ be a path and $\varphi(t) = t^2$. The homotopy of the lemma is $H(s, t) = \gamma((1 - s)t^2 + st)$. At $t = 1/2$ and $s = 1/2$ the argument is $\frac12 \cdot \frac14 + \frac12 \cdot \frac12 = \frac38$, a point of $I$. So $\gamma \circ \varphi$ and $\gamma$ define the same morphism of $\Pi_1(X)$.

**Example (The torus).** By the product formula, $\pi_1(S^1 \times S^1) \cong \pi_1(S^1) \times \pi_1(S^1)$, which is $\mathbb{Z}^2$ after Chapter 2.

### The library around it

::: mathlib
`Path.Homotopy` · `Mathlib.Topology.Homotopy.Path`

`Path.Homotopy p₀ p₁` is `ContinuousMap.HomotopyRel p₀.toContinuousMap p₁.toContinuousMap {0, 1}`. The relation `Path.Homotopic` is its nonemptiness. `Path.Homotopy.hcomp` composes two homotopies as in the first lemma, and `Path.Homotopy.reparam` is the reparametrisation lemma. For a homotopy `H` of maps, `ContinuousMap.Homotopy.evalAt H x` is the path $h_x$.

<?decl Path.Homotopy?>
:::

::: mathlib
`Path.Homotopic.Quotient` · `Mathlib.Topology.Homotopy.Path`

`Path.Homotopic.Quotient x y` is the type of classes of paths from `x` to `y`. It has `Quotient.trans`, `Quotient.symm`, `Quotient.refl` and `Quotient.map`. The groupoid laws are `Quotient.trans_assoc`, `Quotient.refl_trans`, `Quotient.trans_refl`, `Quotient.trans_symm` and `Quotient.symm_trans`, in the module of the fundamental groupoid. Their proofs use the homotopies `Path.Homotopy.transAssoc`, `Path.Homotopy.transRefl` and `Path.Homotopy.reflTransSymm`; the last one is the formula of part (3).

<?decl Path.Homotopic.Quotient?>
:::

::: mathlib
`FundamentalGroupoid` · `Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic`

`FundamentalGroupoid X` is a structure with one field `as : X`, a wrapper around `X`. Its `Groupoid` instance has the quotients as morphisms, and composition `p ≫ q` runs `p` first. `FundamentalGroupoid.map f` is the functor $f_*$, and `FundamentalGroupoid.fundamentalGroupoidFunctor : TopCat ⥤ Grpd` has the scoped notation `π`, with `πₓ` and `πₘ` for objects and maps.

<?decl FundamentalGroupoid?>
:::

::: mathlib
`FundamentalGroup` · `Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup`

`FundamentalGroup X x` is the automorphism group `Aut` of `x` in the groupoid. By `FundamentalGroup.mul_def`, `p * q` is the class of the path that runs `q` first and `p` second, the convention of composition of functions. `FundamentalGroup.map f x` is the induced homomorphism, and `fundamentalGroupMulEquivOfPath` is the change of base point.

<?decl FundamentalGroup?>
:::

::: mathlib
`FundamentalGroupoidFunctor.homotopicMapsNatIso` · `Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps`

For `H : ContinuousMap.Homotopy f g`, this is the natural transformation with components `⟦H.evalAt x⟧`; an instance shows that it is an isomorphism. The square of the proof is `Path.Homotopic.map_trans_evalAt`. `FundamentalGroupoidFunctor.equivOfHomotopyEquiv` is the corollary on homotopy equivalences.

<?decl FundamentalGroupoidFunctor.homotopicMapsNatIso?>
:::

The product formula is `FundamentalGroupoidFunctor.prodIso`, an isomorphism in `Grpd` from `πₓ A × πₓ B` to `πₓ (A × B)`, with `piIso` for arbitrary products. The groupoid of a point is `FundamentalGroupoid.punitEquivDiscretePUnit`.

::: mathlib
`SimplyConnectedSpace` · `Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected`

The class asks for `Nonempty (FundamentalGroupoid X ≌ Discrete Unit)`. The three conditions of the theorem are `simply_connected_iff_unique_homotopic`, `simply_connected_iff_paths_homotopic` and `simply_connected_iff_loops_nullhomotopic`. The instance `SimplyConnectedSpace.ofContractible` gives the last claim, and `ContinuousMap.HomotopyEquiv.simplyConnectedSpace` transports the class. For a subset, `IsSimplyConnected s` means that the subtype is simply connected.

<?decl SimplyConnectedSpace?>
:::

The `TopCat` files restate the notions for the bundled category of spaces. `TopCat.Homotopy f g` is a homotopy between two morphisms of `TopCat`, and `TopCat.Path` is a morphism from the interval with prescribed end points. `TopCat.Homotopy.toSSet` sends a homotopy to a homotopy of maps of singular simplicial sets, `TopCat.toSSet`, and `TopCat.zerothHomotopyEquiv` identifies the path components `ZerothHomotopy X` with the set $\pi_0$ of the singular simplicial set. Chapter 5 uses the singular simplicial set.

```lean
example {X : Type*} [TopologicalSpace X] [SimplyConnectedSpace X]
    {x y : X} (p q : Path x y) : p.Homotopic q :=
  SimplyConnectedSpace.paths_homotopic p q
```

Common errors of a learner: Multiplication in `FundamentalGroup` runs the right factor first, while `Path.trans p q` runs `p` first. A point `x : X` is not an object of the groupoid; it must be wrapped as `⟨x⟩`. `Path.Homotopic` is a relation on paths with fixed end points, while `ContinuousMap.Homotopic` does not fix them. Simply connected spaces are nonempty by definition.

### Exercises

1. (A) Write a path homotopy between the loop $\gamma(t) = (\cos 2\pi t, \sin 2\pi t)$ in the closed unit disk and the constant loop, and check that it stays in the disk. *Hint:* Use the convex combination with $(1, 0)$.
2. (A) Show that $\bar{\bar\alpha} = \alpha$ and $\overline{\alpha \cdot \beta} = \bar\beta \cdot \bar\alpha$ as paths. *Hint:* Compare the formulas on $[0, 1/2]$ and $[1/2, 1]$.
3. (B) Show that two paths $\alpha$ and $\beta$ from $x$ to $y$ give the same change of base point isomorphism if and only if $[\alpha \cdot \bar\beta]$ lies in the centre of $\pi_1(X, x)$. *Hint:* Compute the two conjugations and compare them.
4. (B) Show that a retraction $r : X \to A$ with inclusion $i$ makes $i_* : \pi_1(A, a) \to \pi_1(X, a)$ injective. *Hint:* Use $r_* \circ i_* = \mathrm{id}$.
5. (B) Let $f : X \to Y$ be nullhomotopic. Show that $f_* : \pi_1(X, x) \to \pi_1(Y, f(x))$ is trivial. *Hint:* Use homotopy invariance: $f_*$ is a conjugate of the map induced by a constant map.
6. (C) Show that if $X$ is simply connected and $Y$ is simply connected, then $X \times Y$ is simply connected, without the product formula for groupoids. *Hint:* Build the homotopy of two paths coordinate by coordinate.
7. (C) Show that $\pi_1(X, x)$ is abelian when $X$ is a topological group. *Hint:* For loops $\alpha$, $\beta$ at $1$, compare $\alpha \cdot \beta$ and $\beta \cdot \alpha$ with the pointwise product $t \mapsto \alpha(t)\beta(t)$.

### Notes and history

Poincaré introduced the fundamental group in 1895 in his work on analysis situs. Mathlib takes the groupoid as the primary object and defines the group from it, so that no base point is fixed in advance.

The Mathlib Author of `Topology.Homotopy.Path` and `FundamentalGroupoid.Basic` is Shing Tak Lam. The Mathlib Author of `FundamentalGroupoid.FundamentalGroup` is Mark Lavrentyev. The Mathlib Authors of `FundamentalGroupoid.InducedMaps` are Praneeth Kolichala and Yury Kudryashov. The Mathlib Author of `FundamentalGroupoid.PUnit`, `FundamentalGroupoid.Product` and `FundamentalGroupoid.SimplyConnected` is Praneeth Kolichala. The Mathlib Author of the four `Topology.Homotopy.TopCat` files is Joël Riou.

### Reference

<?reference?>
