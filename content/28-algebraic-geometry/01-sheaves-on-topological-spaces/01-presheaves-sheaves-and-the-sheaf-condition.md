---
title: Presheaves, sheaves and the sheaf condition
kind: theory
modules:
  - Mathlib.Topology.Sheaves.Abelian
  - Mathlib.Topology.Sheaves.AddCommGrpCat
  - Mathlib.Topology.Sheaves.Alexandrov
  - Mathlib.Topology.Sheaves.CommRingCat
  - Mathlib.Topology.Sheaves.Forget
  - Mathlib.Topology.Sheaves.Functors
  - Mathlib.Topology.Sheaves.KPresheaf
  - Mathlib.Topology.Sheaves.KSheaf
  - Mathlib.Topology.Sheaves.Limits
  - Mathlib.Topology.Sheaves.LocalPredicate
  - Mathlib.Topology.Sheaves.MayerVietoris
  - Mathlib.Topology.Sheaves.Module
  - Mathlib.Topology.Sheaves.Over
  - Mathlib.Topology.Sheaves.PUnit
  - Mathlib.Topology.Sheaves.Presheaf
  - Mathlib.Topology.Sheaves.PresheafOfFunctions
  - Mathlib.Topology.Sheaves.Sheaf
  - Mathlib.Topology.Sheaves.SheafCondition.EqualizerProducts
  - Mathlib.Topology.Sheaves.SheafCondition.OpensLeCover
  - Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections
  - Mathlib.Topology.Sheaves.SheafCondition.Sites
  - Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
  - Mathlib.Topology.Sheaves.SheafOfFunctions
explains:
  E3: [TopCat.Presheaf, TopCat.Presheaf.IsSheaf, TopCat.Sheaf, TopCat.Presheaf.IsSheafEqualizerProducts, TopCat.Presheaf.isSheaf_iff_isSheafEqualizerProducts, TopCat.Presheaf.isSheaf_iff_isSheafPairwiseIntersections, TopCat.Presheaf.isSheaf_iff_isSheafOpensLeCover, TopCat.Presheaf.IsSheafUniqueGluing, TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing, TopCat.Sheaf.existsUnique_gluing, TopCat.Presheaf.toTypes_isSheaf, TopCat.LocalPredicate, TopCat.subsheafToTypes, TopCat.sheafToTop, TopCat.Presheaf.pushforward, TopCat.Presheaf.pullback, TopCat.Sheaf.pushforward, TopCat.Sheaf.pullbackPushforwardAdjunction, TopCat.Presheaf.isSheaf_iff_isSheaf_comp, TopCat.isSheaf_of_isLimit]
  E2: [TopCat.presheafToTypes, TopCat.presheafToTop, TopCat.PrelocalPredicate, TopCat.continuousLocal, TopCat.Sheaf.forget, TopCat.Presheaf.IsSheafPairwiseIntersections, TopCat.Presheaf.IsSheafOpensLeCover, TopCat.Presheaf.IsCompatible, TopCat.Presheaf.IsGluing, TopCat.Presheaf.SheafConditionEqualizerProducts.res, TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes, TopCat.Presheaf.SheafConditionEqualizerProducts.rightRes, TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens, TopCat.Presheaf.SheafConditionEqualizerProducts.piInters, TopCat.presheafToTopCommRing, TopCat.Sheaf.objSupIsoProdEqLocus, Opens.mayerVietorisSquare, Alexandrov.principalsKanExtension, Alexandrov.isSheaf_principalsKanExtension, TopCat.KPresheaf, TopCat.KPresheaf.IsKSheaf, TopCat.KSheaf, TopCat.Presheaf.isSheaf_on_punit_iff_isTerminal, TopCat.Presheaf.isSheaf_iff_isTerminal_of_indiscrete, TopCat.Sheaf.exact_iff_stalkFunctor_map_exact, TopCat.Sheaf.sections_exact_of_left_exact, TopologicalSpace.Opens.sheafOfModulesEquivOver, TopologicalSpace.Opens.overEquivalence, TopCat.Presheaf.isSheaf_of_isOpenEmbedding, TopCat.Sheaf.isIso_iff_isIso_basis, TopCat.limit_isSheaf, TopCat.Presheaf.pullbackPushforwardAdjunction, TopCat.Presheaf.isSheaf_unit]
  E1: auto
families: []
requires: [V13.C01, V24.C04, V24.C05, V25.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Presheaves, sheaves and the sheaf condition

### Overview

Many properties of functions are local: a function is continuous when it is continuous near each point. A sheaf records such data. It gives a set of sections over each open set, restriction maps to smaller open sets, and two rules: sections that agree locally are equal, and sections that agree on overlaps glue to one section. Schemes are spaces with a sheaf of rings, so the language of sheaves comes first in this volume.

This section defines presheaves with values in a category, states the sheaf condition in its equivalent forms and proves the equivalences that a reader uses most. It builds sheaves of functions from local predicates, studies limits of sheaves and the pushforward and pullback functors, and ends with the Mayer-Vietoris square, sheaves on Alexandrov spaces and K-sheaves on compact sets.

### Definitions

Let $X$ be a topological space and $\mathcal{O}(X)$ its partially ordered set of open sets, seen as a category with one arrow $V \to U$ when $V \subseteq U$.

**Definition (Presheaf).** A *presheaf* on $X$ with values in a category $C$ is a functor $F : \mathcal{O}(X)^{\mathrm{op}} \to C$. The object $F(U)$ is the object of *sections* over $U$. For $V \subseteq U$ the arrow $\rho_{UV} = F(V \subseteq U) : F(U) \to F(V)$ is the *restriction*. For concrete $C$ write $s|_V$ for $\rho_{UV}(s)$. A morphism of presheaves is a natural transformation.

**Definition (Compatible family, gluing).** Let $F$ be a presheaf of sets, $(U_i)_{i \in I}$ a family of open sets and $U = \bigcup_i U_i$. A family $s_i \in F(U_i)$ is *compatible* when $s_i|_{U_i \cap U_j} = s_j|_{U_i \cap U_j}$ for all $i, j$. A *gluing* of the family is a section $s \in F(U)$ with $s|_{U_i} = s_i$ for each $i$.

**Definition (Sheaf of sets).** A presheaf of sets $F$ is a *sheaf* when every compatible family has exactly one gluing.

For a general category $C$ the elements of $F(U)$ are not available, and the definition uses limits.

**Definition (Equalizer form of the sheaf condition).** Let $C$ have products. For a family $(U_i)$ with union $U$, consider the three arrows
$$F(U) \xrightarrow{\ e\ } \prod_i F(U_i) \underset{q}{\overset{p}{\rightrightarrows}} \prod_{i,j} F(U_i \cap U_j),$$
where $e$ has components $\rho_{U U_i}$, the component $(i, j)$ of $p$ is $\rho_{U_i, U_i \cap U_j} \circ \mathrm{pr}_i$, and that of $q$ is $\rho_{U_j, U_i \cap U_j} \circ \mathrm{pr}_j$. The presheaf satisfies the *equalizer condition* when, for each family, $e$ is an equalizer of $p$ and $q$.

**Definition (Sheaf, official form).** The opens of $X$ carry a Grothendieck topology: a sieve $S$ on $U$ covers $U$ when each point of $U$ lies in some $V \in S$. A presheaf $F$ with values in $C$ is a *sheaf* when, for each object $A$ of $C$, the presheaf of sets $U \mapsto \mathrm{Hom}_C(A, F(U))$ is a sheaf for this topology. A morphism of sheaves is a morphism of the underlying presheaves.

**Definition (Prelocal and local predicate).** Let $T$ assign a type $T_x$ to each point $x \in X$. A *prelocal predicate* $P$ is a property of functions $f : \prod_{x \in U} T_x$ for each open $U$, stable under restriction. It is *local* when it also satisfies: if each $x \in U$ has an open $V \ni x$, $V \subseteq U$, with $P(f|_V)$, then $P(f)$.

**Definition (Pushforward and pullback).** Let $f : X \to Y$ be continuous and $f^{-1} : \mathcal{O}(Y) \to \mathcal{O}(X)$ the preimage functor. The *pushforward* of a presheaf $F$ on $X$ is $f_*F = F \circ (f^{-1})^{\mathrm{op}}$, so $(f_*F)(V) = F(f^{-1}V)$. The *pullback* $f^{-1}G$ of a presheaf $G$ on $Y$ is the left Kan extension of $G$ along $(f^{-1})^{\mathrm{op}}$; when $C$ has colimits,
$$(f^{-1}G)(U) = \operatorname{colim}_{V \supseteq f(U)} G(V).$$
For sheaves the pullback is the sheafification of this presheaf.

### Theorems and proofs

**Proposition (Sections over the empty set).** If $F$ is a sheaf with values in $C$, then $F(\emptyset)$ is a terminal object of $C$.

*Proof.* The empty sieve covers $\emptyset$, since $\emptyset$ has no point. For a sheaf of sets $G$, the empty family over this sieve has exactly one gluing, so $G(\emptyset)$ has exactly one element. With $G = \mathrm{Hom}_C(A, F(-))$, each set $\mathrm{Hom}_C(A, F(\emptyset))$ has exactly one element, so $F(\emptyset)$ is terminal. $\square$

**Theorem (Equivalence of the forms for sets).** For a presheaf of sets $F$ these are equivalent: (a) every compatible family has exactly one gluing; (b) the equalizer condition holds; (c) $F$ is a sheaf in the official form.

*Proof.* (a) $\Leftrightarrow$ (b). In the category of sets, the equalizer of $p$ and $q$ is the subset $E$ of families $(s_i)$ with $p(s) = q(s)$. By the definition of $p$ and $q$, this equation says $s_i|_{U_i \cap U_j} = s_j|_{U_i \cap U_j}$ for all $i, j$, so $E$ is the set of compatible families. The map $e$ sends $s$ to $(s|_{U_i})$, and $e$ is an equalizer exactly when $e$ is a bijection onto $E$. Surjectivity onto $E$ is the existence of a gluing, and injectivity is its uniqueness.

(a) $\Rightarrow$ (c). For a set $A$, the presheaf $\mathrm{Hom}(A, F(-)) = F(-)^A$ is a product of copies of $F$, and a product of sheaves of sets is a sheaf, since a family glues in each coordinate. So it suffices to treat a one point set $A$, where $\mathrm{Hom}(A, F(-)) = F$. Let $S$ be a covering sieve on $U$ and $(t_V)_{V \in S}$ a family with $t_V|_W = t_W$ for $W \subseteq V$ in $S$. Since $S$ covers, $\bigcup_{V \in S} V = U$. A sieve is closed under shrinking, so $V \cap V' \in S$ and $t_V|_{V \cap V'} = t_{V \cap V'} = t_{V'}|_{V \cap V'}$: the family is compatible in the sense of (a). By (a) it has one gluing $t$. A second $t'$ with $t'|_V = t_V$ for all $V \in S$ is also a gluing, so $t' = t$.

(c) $\Rightarrow$ (a). Let $(s_i)$ be compatible with union $U$. Let $S$ be the sieve of opens $W$ contained in some $U_i$; it covers $U$. For $W \subseteq U_i$ put $t_W = s_i|_W$. This does not depend on $i$: if also $W \subseteq U_j$, then $W \subseteq U_i \cap U_j$ and compatibility gives $s_i|_W = s_j|_W$. The family $(t_W)$ is compatible on $S$, so (c) gives exactly one $t$ with $t|_W = t_W$ for all $W \in S$. In particular $t|_{U_i} = s_i$. A second gluing $t'$ satisfies $t'|_W = (t'|_{U_i})|_W = s_i|_W = t_W$, so $t' = t$. $\square$

**Theorem (Change of target).** Let $G : C \to D$ be a functor that reflects isomorphisms and preserves limits, and let $C$ have all limits. Then a presheaf $F$ with values in $C$ is a sheaf if and only if $G \circ F$ is a sheaf.

*Proof.* By the form with the diagram of the $U_i$ and the $U_i \cap U_j$, $F$ is a sheaf when each comparison map $c : F(U) \to L$ to the limit $L$ of this diagram is an isomorphism. Since $G$ preserves limits, $G(c)$ is the comparison map for $G \circ F$. Since $G$ reflects isomorphisms, $c$ is an isomorphism if and only if $G(c)$ is one. $\square$

**Theorem (Functions form a sheaf).** Let $T_x$ be a type for each $x \in X$, and $F(U) = \prod_{x \in U} T_x$ with restriction of functions. Then $F$ is a sheaf. If $P$ is a local predicate, then $F_P(U) = \{f \in F(U) : P(f)\}$ is a subsheaf.

*Proof.* Let $f_i \in F(U_i)$ be compatible. For $x \in U$ choose $i$ with $x \in U_i$ and set $f(x) = f_i(x)$. If also $x \in U_j$, then $f_i(x) = f_j(x)$ by compatibility at $x \in U_i \cap U_j$, so $f$ is well defined, and $f|_{U_i} = f_i$. Two gluings agree at each $x$, so they are equal. For $F_P$: restriction preserves $P$, so $F_P$ is a subpresheaf. If the $f_i$ satisfy $P$, their gluing $f$ satisfies $P(f|_{U_i})$ for each $i$, and every $x \in U$ lies in some $U_i$. Since $P$ is local, $P(f)$ holds. Uniqueness follows from uniqueness in $F$. $\square$

**Corollary (Continuous functions).** For a topological space $T$, the presheaf $U \mapsto C(U, T)$ is a sheaf.

*Proof.* Take $T_x = T$ and $P(f)$: $f$ is continuous. Continuity is preserved by restriction, and a function that is continuous on each member of an open cover is continuous: for an open $O \subseteq T$, $f^{-1}(O) = \bigcup_i f|_{U_i}^{-1}(O)$ is a union of open sets. So $P$ is local. $\square$

**Theorem (Pushforward of a sheaf).** If $F$ is a sheaf on $X$ and $f : X \to Y$ is continuous, then $f_*F$ is a sheaf on $Y$.

*Proof.* By the official form and the equivalence above for each $\mathrm{Hom}(A, -)$, it suffices to treat a sheaf of sets. Let $(V_i)$ be open in $Y$ with union $V$, and $s_i \in (f_*F)(V_i) = F(f^{-1}V_i)$ compatible. Preimage preserves unions and intersections: $\bigcup_i f^{-1}V_i = f^{-1}V$ and $f^{-1}V_i \cap f^{-1}V_j = f^{-1}(V_i \cap V_j)$. So $(s_i)$ is a compatible family of $F$ for the cover $(f^{-1}V_i)$ of $f^{-1}V$. It has exactly one gluing in $F(f^{-1}V) = (f_*F)(V)$. $\square$

**Theorem (Pullback and pushforward are adjoint).** Let $C$ have colimits. For presheaves $G$ on $Y$ and $F$ on $X$ there is a bijection, natural in $G$ and $F$,
$$\mathrm{Hom}(f^{-1}G, F) \cong \mathrm{Hom}(G, f_*F).$$

*Proof.* Write $\phi = (f^{-1})^{\mathrm{op}}$. Then $f_*F = F \circ \phi$ and $f^{-1}G = \mathrm{Lan}_\phi G$. The universal property of the left Kan extension is a natural bijection $\mathrm{Hom}(\mathrm{Lan}_\phi G, F) \cong \mathrm{Hom}(G, F \circ \phi)$, which sends $\alpha$ to the unit $G \to (\mathrm{Lan}_\phi G) \circ \phi$ followed by $\alpha \circ \phi$. $\square$

For sheaves, compose this adjunction with the adjunction between sheafification and the inclusion of sheaves.

**Theorem (Limits of sheaves).** Let $C$ have limits of shape $J$, and let $D : J \to \mathrm{PSh}(X, C)$ be a diagram of sheaves. Then the limit presheaf $(\lim D)(U) = \lim_j D_j(U)$ is a sheaf, and it is a limit in the category of sheaves.

*Proof.* It suffices to check that $\mathrm{Hom}(A, \lim_j D_j(-)) = \lim_j \mathrm{Hom}(A, D_j(-))$ is a sheaf of sets. A compatible family of this presheaf has $j$-th components that glue to a unique $t_j$. For $u : j \to k$, both $D(u) \circ t_j$ and $t_k$ glue the same family, so they are equal and $(t_j)$ is the unique gluing in the limit. Sheaves form a full subcategory, so this cone is also a limit of sheaves. $\square$

### Examples

**Example (Continuous functions on the line).** Let $X = \mathbb{R}$, $U_1 = (-\infty, 1)$ and $U_2 = (0, \infty)$, so $U_1 \cap U_2 = (0, 1)$. The sections $s_1(x) = |x|$ on $U_1$ and $s_2(x) = x$ on $U_2$ agree on $(0, 1)$, because $|x| = x$ for $x > 0$. Their gluing is $s(x) = |x|$ on $\mathbb{R}$. Not every section over a smaller set extends: $1/x$ is continuous on $(0, 1)$ but has no continuous extension to $U_1$, since it is unbounded near $0$.

**Counterexample (The constant presheaf).** Let $X = \{a, b\}$ with the discrete topology and $F(U) = \mathbb{Z}$ for every open $U$, with identity restrictions. This presheaf is not a sheaf, because $F(\emptyset) = \mathbb{Z}$ is not a one point set. Change the value at the empty set to $F(\emptyset) = \{\ast\}$. The new presheaf still fails: the sections $1$ on $\{a\}$ and $2$ on $\{b\}$ are compatible, since $\{a\} \cap \{b\} = \emptyset$, but a gluing $s \in F(X) = \mathbb{Z}$ needs $s = 1$ and $s = 2$. The repair is the sheaf $\underline{\mathbb{Z}}$ of locally constant functions to $\mathbb{Z}$. The family $(1, 2)$ glues to the function with value $1$ at $a$ and $2$ at $b$, and $\underline{\mathbb{Z}}(X) = \mathbb{Z}^2$.

**Example (A sheaf on a point).** On a one point space $X$, every cover of $X$ contains $X$. So a presheaf is a sheaf exactly when $F(\emptyset)$ is terminal, and $F(X)$ is free. Sheaves on a point form a category equivalent to $C$.

**Example (An Alexandrov space).** Let $X = \{0, 1\}$ with the order $0 \le 1$ and the upper sets as open sets: $\emptyset$, $\{1\}$, $X$. This is the Sierpinski space. A functor $D$ from the poset $X$ to $C$ is an arrow $D(0) \to D(1)$. The right Kan extension along $x \mapsto \{y : x \le y\}$ gives $F(X) = D(0)$, $F(\{1\}) = D(1)$, $F(\emptyset)$ terminal, and the restriction $F(X) \to F(\{1\})$ is the given arrow. The open $X$ has no cover by smaller open sets, so the sheaf condition imposes nothing more, and every sheaf on $X$ has this form.

### The library around it

::: mathlib
`TopCat.Presheaf` · `Mathlib.Topology.Sheaves.Presheaf`

`TopCat.Presheaf C X` is `(Opens X)ᵒᵖ ⥤ C`. Sections are `F.obj (op U)` and restrictions are `F.map i.op` for `i : V ⟶ U`.

<?decl TopCat.Presheaf?>
:::

::: mathlib
`TopCat.Presheaf.IsSheaf` · `Mathlib.Topology.Sheaves.Sheaf`

`F.IsSheaf` is `Presheaf.IsSheaf (Opens.grothendieckTopology X) F`, the general sheaf condition of `CategoryTheory.Presheaf.IsSheaf` for the site of opens. `TopCat.Sheaf C X` is the full subcategory of sheaves, with `F.obj` the presheaf of a sheaf `F`, and `TopCat.Sheaf.forget` is the fully faithful inclusion.

<?decl TopCat.Presheaf.IsSheaf?>
:::

::: mathlib
`TopCat.Presheaf.isSheaf_iff_isSheafEqualizerProducts` · `Mathlib.Topology.Sheaves.SheafCondition.EqualizerProducts`

With products in `C`, the sheaf condition is equivalent to `IsSheafEqualizerProducts`: for each family `U : ι → Opens X`, the fork built from `res`, `leftRes` and `rightRes` between `piOpens` and `piInters` is a limit.

<?decl TopCat.Presheaf.isSheaf_iff_isSheafEqualizerProducts?>
:::

::: mathlib
`TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing` · `Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing`

For a concrete category whose forgetful functor reflects isomorphisms and preserves limits, the sheaf condition is equivalent to `IsSheafUniqueGluing`, with `IsCompatible` and `IsGluing` as in the definitions above. A sheaf `F` gives `TopCat.Sheaf.existsUnique_gluing`, the gluing over `iSup U`.

<?decl TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing?>
:::

::: mathlib
`TopCat.subsheafToTypes` · `Mathlib.Topology.Sheaves.LocalPredicate`

A `TopCat.LocalPredicate T` gives the subsheaf `subsheafToTypes P` of `presheafToTypes X T`, whose sheaf property is `TopCat.Presheaf.toTypes_isSheaf`. With `continuousLocal`, the sheaf `TopCat.sheafToTop T` is the sheaf of continuous functions to `T`.

<?decl TopCat.subsheafToTypes?>
:::

::: mathlib
`TopCat.Sheaf.pullbackPushforwardAdjunction` · `Mathlib.Topology.Sheaves.Functors`

For `f : X ⟶ Y` this is `pullback A f ⊣ pushforward A f` on sheaves. The presheaf version `TopCat.Presheaf.pullbackPushforwardAdjunction` uses `TopCat.Presheaf.pullback`, the left Kan extension `CategoryTheory.Functor.lan` along `(Opens.map f).op`.

<?decl TopCat.Sheaf.pullbackPushforwardAdjunction?>
:::

::: mathlib
`TopCat.Sheaf.objSupIsoProdEqLocus` · `Mathlib.Topology.Sheaves.CommRingCat`

For a sheaf of commutative rings, `F(U ⊔ V)` is isomorphic to the subring of `F(U) × F(V)` where the two restrictions to `U ⊓ V` agree. The square itself is `Opens.mayerVietorisSquare U V` in `Mathlib.Topology.Sheaves.MayerVietoris`.

<?decl TopCat.Sheaf.objSupIsoProdEqLocus?>
:::

::: mathlib
`TopCat.KPresheaf.IsKSheaf` · `Mathlib.Topology.Sheaves.KSheaf`

A `TopCat.KPresheaf` on a Hausdorff space is a functor on compact sets. It is a K-sheaf when `F(∅)` is terminal, the square for `K₁ ∪ K₂` and `K₁ ∩ K₂` is a pullback, and `F(K)` is the colimit of `F(L)` over the compact `L` with `K` in the interior of `L`. The index of this edition has no declaration for the equivalence between K-sheaves and sheaves.

<?decl TopCat.KPresheaf.IsKSheaf?>
:::

::: mathlib
`TopCat.Sheaf.sections_exact_of_left_exact` · `Mathlib.Topology.Sheaves.AddCommGrpCat`

For sheaves of abelian groups, an exact sequence $0 \to F \to G \to H$ gives an exact sequence of sections on each open. `TopCat.Sheaf.exact_iff_stalkFunctor_map_exact` in `Mathlib.Topology.Sheaves.Abelian` tests exactness of sheaves on stalks.

<?decl TopCat.Sheaf.sections_exact_of_left_exact?>
:::

Common errors of a learner: the sheaf condition of the official form quantifies over all objects `A` of `C`, so a proof for a ring valued presheaf usually goes through `isSheaf_iff_isSheafUniqueGluing` or `isSheaf_iff_isSheaf_comp` and does not unfold the definition. A morphism `f : F ⟶ G` of sheaves is a wrapper, and its natural transformation is `f.hom`. The pullback of presheaves needs colimits in `C`, and the pullback of sheaves needs sheafification on top of it.

### Exercises

1. (A) Show that on a discrete space $X$ a sheaf of sets is determined by its values on the points, and $F(U) \cong \prod_{x \in U} F(\{x\})$. *Hint:* Cover $U$ by its points; their pairwise intersections are empty or a point.
2. (A) Let $F$ be the presheaf of bounded continuous functions on $\mathbb{R}$. Show that it is not a sheaf. *Hint:* Glue the functions $x$ on the intervals $(n - 1, n + 1)$.
3. (A) Show that a sheaf of sets $F$ on $X$ satisfies: if $s, t \in F(U)$ and $s|_{U_i} = t|_{U_i}$ for a cover $(U_i)$ of $U$, then $s = t$. *Hint:* Both are gluings of one family.
4. (B) Let $y \in Y$ and let $i : \{y\} \to Y$ be the inclusion. Compute $i^{-1}G$ for a presheaf of abelian groups $G$ on $Y$. *Hint:* The colimit runs over the open neighbourhoods of $y$.
5. (B) Show that holomorphy of a function on an open set of $\mathbb{C}$ is a local predicate, so that holomorphic functions form a sheaf of rings. Show that "constant" is a prelocal predicate that is not local. *Hint:* For the second part use a disconnected open set.
6. (C) Let $\phi : F \to G$ be a morphism of sheaves of abelian groups. Show that the kernel presheaf $U \mapsto \ker \phi_U$ is a sheaf, and that the image presheaf $U \mapsto \operatorname{im} \phi_U$ need not be one. *Hint:* The kernel is a limit. For the image, take $\exp$ from holomorphic functions to nowhere zero holomorphic functions on $\mathbb{C} \setminus \{0\}$ and the section $z$.

### Notes and history

Leray introduced sheaves in 1946, in his work on the cohomology of spaces and maps. Serre used sheaves of rings on varieties in FAC in 1955, and Grothendieck built the theory of schemes on them in EGA, from 1960 to 1967, with the general notion of a site in SGA. Hartshorne (1977) defines a sheaf by the locality and gluing axioms, and the Stacks project uses the equalizer form.

The Mathlib Authors of `Topology.Sheaves.Presheaf` are Kim Morrison, Mario Carneiro, Reid Barton and Andrew Yang. The Mathlib Author of `Topology.Sheaves.Sheaf`, `Topology.Sheaves.Forget`, `Topology.Sheaves.Limits`, `Topology.Sheaves.PresheafOfFunctions`, `Topology.Sheaves.SheafCondition.EqualizerProducts`, `Topology.Sheaves.SheafCondition.OpensLeCover` and `Topology.Sheaves.SheafCondition.PairwiseIntersections` is Kim Morrison. The Mathlib Authors of `Topology.Sheaves.LocalPredicate` are Johan Commelin, Kim Morrison and Adam Topaz, and those of `Topology.Sheaves.SheafOfFunctions` are Johan Commelin and Kim Morrison. The Mathlib Author of `Topology.Sheaves.SheafCondition.UniqueGluing` and `Topology.Sheaves.SheafCondition.Sites` is Justus Springer. The Mathlib Authors of `Topology.Sheaves.Functors` are Junyan Xu and Andrew Yang, and those of `Topology.Sheaves.CommRingCat` are Kim Morrison and Andrew Yang. The Mathlib Author of `Topology.Sheaves.PUnit` is Jujian Zhang. The Mathlib Authors of `Topology.Sheaves.Alexandrov` are Justin Curry and Adam Topaz. The Mathlib Author of `Topology.Sheaves.MayerVietoris` and `Topology.Sheaves.Over` is Joël Riou, that of `Topology.Sheaves.Module` is Andrew Yang, that of `Topology.Sheaves.Abelian` and `Topology.Sheaves.AddCommGrpCat` is Brian Nugent, and that of `Topology.Sheaves.KPresheaf` and `Topology.Sheaves.KSheaf` is Yannis Monbru Carcelero.

### Reference

<?reference?>
