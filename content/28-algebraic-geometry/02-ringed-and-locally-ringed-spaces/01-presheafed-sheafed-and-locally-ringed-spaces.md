---
title: Presheafed, sheafed and locally ringed spaces
kind: theory
modules:
  - Mathlib.Geometry.RingedSpace.Basic
  - Mathlib.Geometry.RingedSpace.LocallyRingedSpace
  - Mathlib.Geometry.RingedSpace.LocallyRingedSpace.ResidueField
  - Mathlib.Geometry.RingedSpace.PresheafedSpace
  - Mathlib.Geometry.RingedSpace.SheafedSpace
  - Mathlib.Geometry.RingedSpace.Stalks
explains:
  E3: [AlgebraicGeometry.PresheafedSpace, AlgebraicGeometry.PresheafedSpace.Hom, AlgebraicGeometry.SheafedSpace, AlgebraicGeometry.RingedSpace, AlgebraicGeometry.LocallyRingedSpace, AlgebraicGeometry.LocallyRingedSpace.Hom, AlgebraicGeometry.PresheafedSpace.Hom.stalkMap, AlgebraicGeometry.LocallyRingedSpace.residueField, AlgebraicGeometry.RingedSpace.basicOpen, AlgebraicGeometry.PresheafedSpace.restrict, AlgebraicGeometry.LocallyRingedSpace.restrict]
  E2: [AlgebraicGeometry.PresheafedSpace.comp, AlgebraicGeometry.PresheafedSpace.forget, AlgebraicGeometry.PresheafedSpace.isoOfComponents, AlgebraicGeometry.PresheafedSpace.ofRestrict, AlgebraicGeometry.PresheafedSpace.restrictTopIso, AlgebraicGeometry.PresheafedSpace.Γ, AlgebraicGeometry.PresheafedSpace.restrictStalkIso, AlgebraicGeometry.PresheafedSpace.stalkMap.comp, AlgebraicGeometry.PresheafedSpace.stalkMap.id, AlgebraicGeometry.PresheafedSpace.stalkMap_germ, AlgebraicGeometry.SheafedSpace.forgetToPresheafedSpace, AlgebraicGeometry.SheafedSpace.fullyFaithfulForgetToPresheafedSpace, AlgebraicGeometry.SheafedSpace.sheaf, AlgebraicGeometry.SheafedSpace.restrict, AlgebraicGeometry.RingedSpace.isUnit_res_of_isUnit_germ, AlgebraicGeometry.RingedSpace.isUnit_of_isUnit_germ, AlgebraicGeometry.RingedSpace.mem_basicOpen, AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen, AlgebraicGeometry.RingedSpace.basicOpen_mul, AlgebraicGeometry.RingedSpace.zeroLocus, AlgebraicGeometry.RingedSpace.exists_res_eq_zero_of_germ_eq_zero, AlgebraicGeometry.LocallyRingedSpace.Hom.stalkMap, AlgebraicGeometry.LocallyRingedSpace.forgetToSheafedSpace, AlgebraicGeometry.LocallyRingedSpace.homOfSheafedSpaceHomOfIsIso, AlgebraicGeometry.LocallyRingedSpace.isoOfSheafedSpaceIso, AlgebraicGeometry.LocallyRingedSpace.empty, AlgebraicGeometry.LocallyRingedSpace.emptyIsInitial, AlgebraicGeometry.LocallyRingedSpace.basicOpen_zero, AlgebraicGeometry.LocallyRingedSpace.ofRestrict, AlgebraicGeometry.LocallyRingedSpace.residue, AlgebraicGeometry.LocallyRingedSpace.residue_surjective, AlgebraicGeometry.LocallyRingedSpace.evaluation, AlgebraicGeometry.LocallyRingedSpace.Γevaluation, AlgebraicGeometry.LocallyRingedSpace.evaluation_eq_zero_iff_notMem_basicOpen, AlgebraicGeometry.LocallyRingedSpace.residueFieldMap, AlgebraicGeometry.LocallyRingedSpace.residue_comp_residueFieldMap_eq_stalkMap_comp_residue]
  E1: auto
families: []
requires: [V10.C02, V24.C04, V28.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Presheafed, sheafed and locally ringed spaces

### Overview

A smooth manifold, a complex manifold and a scheme share one structure: a topological space with a sheaf of rings of functions. On a manifold the functions near a point form a local ring, whose maximal ideal is the set of functions that vanish at the point. Schemes keep this local structure, but their sections are not functions on the points: a section of $\operatorname{Spec} \mathbb{Z}$ is an integer, and its value at $(p)$ is a residue class modulo $p$. The value of a section at a point lies in the residue field of the local ring there.

This section defines presheafed spaces, sheafed spaces and ringed spaces with their morphisms, and the stalk maps of a morphism. It defines locally ringed spaces, where the stalks are local rings and the stalk maps are local homomorphisms. It studies the basic open set of a section, the residue field at a point with the evaluation of sections, and the restriction of a space to an open subset.

### Definitions

Let $C$ be a category with colimits. For a continuous map $f : X \to Y$ and a presheaf $F$ on $X$, recall $(f_*F)(V) = F(f^{-1}V)$.

**Definition (Presheafed space).** A *presheafed space* over $C$ is a pair $(X, \mathcal{O}_X)$ of a topological space $X$ and a presheaf $\mathcal{O}_X$ on $X$ with values in $C$. A *morphism* $(X, \mathcal{O}_X) \to (Y, \mathcal{O}_Y)$ is a pair $(f, f^\#)$ of a continuous map $f : X \to Y$ and a morphism of presheaves $f^\# : \mathcal{O}_Y \to f_*\mathcal{O}_X$ on $Y$.

The map of sheaves goes from $Y$ to $X$, against $f$: functions on $Y$ pull back to functions on $X$. A component of $f^\#$ is a map $\mathcal{O}_Y(V) \to \mathcal{O}_X(f^{-1}V)$.

**Definition (Composition).** For $(f, f^\#) : X \to Y$ and $(g, g^\#) : Y \to Z$, the composite is $(g \circ f, h)$ with
$$h_W : \mathcal{O}_Z(W) \xrightarrow{g^\#_W} \mathcal{O}_Y(g^{-1}W) \xrightarrow{f^\#_{g^{-1}W}} \mathcal{O}_X(f^{-1}g^{-1}W).$$
The identity is $(\mathrm{id}_X, \mathrm{id})$.

**Definition (Sheafed space and ringed space).** A *sheafed space* is a presheafed space whose presheaf is a sheaf. Its morphisms are the morphisms of presheafed spaces. A *ringed space* is a sheafed space over the category of commutative rings.

**Definition (Stalk map).** Let $(f, f^\#) : X \to Y$ be a morphism and $x \in X$. The *stalk map* $f_x : \mathcal{O}_{Y, f(x)} \to \mathcal{O}_{X, x}$ is the composite of the stalk of $f^\#$ at $f(x)$ with the map $(f_*\mathcal{O}_X)_{f(x)} \to \mathcal{O}_{X,x}$ of the previous chapter. On germs, $f_x(s_{f(x)}) = (f^\#_V s)_x$ for $s \in \mathcal{O}_Y(V)$, $f(x) \in V$.

**Definition (Locally ringed space).** A *locally ringed space* is a ringed space whose stalks $\mathcal{O}_{X,x}$ are local rings. A *morphism* of locally ringed spaces is a morphism of ringed spaces such that every stalk map $f_x$ is a local homomorphism: $f_x(\mathfrak{m}_{f(x)}) \subseteq \mathfrak{m}_x$, or equivalently $f_x^{-1}(\mathfrak{m}_x) = \mathfrak{m}_{f(x)}$.

**Definition (Residue field and evaluation).** The *residue field* at $x$ is $\kappa(x) = \mathcal{O}_{X,x}/\mathfrak{m}_x$. For a section $s \in \mathcal{O}_X(U)$ with $x \in U$, the *value* $s(x) \in \kappa(x)$ is the image of the germ $s_x$.

**Definition (Basic open set).** For a ringed space $X$ and $s \in \mathcal{O}_X(U)$, the *basic open set* is $X_s = \{x \in U : s_x \text{ is a unit in } \mathcal{O}_{X,x}\}$. The *zero locus* of a set $S$ of sections is $\bigcap_{s \in S} (X \setminus X_s)$.

**Definition (Restriction to an open set).** Let $j : U \to X$ be an open embedding. The *restriction* $X|_U$ is the space $U$ with the presheaf $V \mapsto \mathcal{O}_X(j(V))$. The morphism $X|_U \to X$ is $j$ with the restrictions $\mathcal{O}_X(W) \to \mathcal{O}_X(j(j^{-1}W)) = \mathcal{O}_X(W \cap j(U))$ as components.

### Theorems and proofs

**Proposition (Category of presheafed spaces).** Presheafed spaces over $C$ and their morphisms form a category.

*Proof.* The composite of the definition is a morphism of presheaves $\mathcal{O}_Z \to (g \circ f)_*\mathcal{O}_X$, since $(g \circ f)^{-1} W = f^{-1}g^{-1}W$ and each of the two arrows is natural in $W$. For the unit laws, $(\mathrm{id}_X)_*$ is the identity functor and the identity morphism contributes identity components. For associativity, let $k : Z \to T$ be a third morphism. Both bracketings have, at an open $W \subseteq T$, the component $f^\#_{g^{-1}k^{-1}W} \circ g^\#_{k^{-1}W} \circ k^\#_W$, and continuous maps compose associatively. $\square$

The map $(X, \mathcal{O}_X) \mapsto X$ is a functor to topological spaces. A morphism is an isomorphism if and only if $f$ is a homeomorphism and $f^\#$ is an isomorphism of presheaves: the inverse is $(f^{-1}, (f^{-1})_*(f^\#)^{-1})$, up to the identification $(f^{-1})_*f_* = \mathrm{id}$.

**Proposition (Stalk maps compose).** For $X \xrightarrow{f} Y \xrightarrow{g} Z$ and $x \in X$, $(g \circ f)_x = f_x \circ g_{f(x)}$, and $(\mathrm{id})_x = \mathrm{id}$.

*Proof.* Every element of $\mathcal{O}_{Z, g(f(x))}$ is the image of a germ under a colimit map, so it suffices to compare both sides on germs $s_{g(f(x))}$ with $s \in \mathcal{O}_Z(W)$. The formula on germs gives $g_{f(x)}(s_{g(f(x))}) = (g^\#_W s)_{f(x)}$ and then $f_x((g^\#_W s)_{f(x)}) = (f^\#_{g^{-1}W} g^\#_W s)_x$. This is the germ of the composite component applied to $s$, which is $(g \circ f)_x(s_{g(f(x))})$. For the identity both sides send $s_x$ to $s_x$. $\square$

**Theorem (Units near a point).** Let $X$ be a ringed space, $s \in \mathcal{O}_X(U)$ and $x \in U$ with $s_x$ a unit. Then $s|_V$ is a unit on an open $V \ni x$. So $X_s$ is open, and $s|_{X_s}$ is a unit of $\mathcal{O}_X(X_s)$.

*Proof.* Let $u \in \mathcal{O}_{X,x}$ with $s_x u = 1$. By the lemma on germs $u = t_x$ for $t \in \mathcal{O}_X(W)$, and $(s|_{U \cap W} \, t|_{U \cap W})_x = 1_x$. Equal germs agree on a smaller open set, so $s|_V t|_V = 1$ on an open $V \ni x$. Then every point of $V$ lies in $X_s$, since germs of units are units. So $X_s$ is open. For the last claim, cover $X_s$ by such $V_x$ with inverses $t^x \in \mathcal{O}_X(V_x)$ of $s|_{V_x}$. On $V_x \cap V_y$ both $t^x$ and $t^y$ are inverses of the restriction of $s$, and inverses in a commutative ring are unique, so the family is compatible. Its gluing $t$ satisfies $(s t)|_{V_x} = 1$ for all $x$, so $s t = 1$ by the sheaf property. $\square$

**Proposition (Basic open sets).** For sections $s, t \in \mathcal{O}_X(U)$, $X_{st} = X_s \cap X_t$. If $X$ is locally ringed, $X_0 = \emptyset$.

*Proof.* In a commutative ring a product is a unit if and only if both factors are units, and $(st)_x = s_x t_x$. A local ring is nonzero, so $0$ is not a unit in any stalk. $\square$

**Theorem (Values and basic open sets).** In a locally ringed space, $s(x) = 0$ in $\kappa(x)$ if and only if $x \notin X_s$.

*Proof.* In a local ring $R$ with maximal ideal $\mathfrak{m}$, an element is a unit if and only if it is not in $\mathfrak{m}$: a nonunit generates a proper ideal, which lies in the unique maximal ideal, and an element of $\mathfrak{m}$ is not a unit since $\mathfrak{m}$ is proper. So $s_x \notin \mathfrak{m}_x$ if and only if $s_x$ is a unit. The value $s(x)$ is zero if and only if $s_x \in \mathfrak{m}_x$. $\square$

**Theorem (Residue field maps).** Let $f : X \to Y$ be a morphism of locally ringed spaces and $x \in X$. Then $f_x$ induces a field homomorphism $\kappa(f(x)) \to \kappa(x)$, and $f^\#(s)(x)$ is the image of $s(f(x))$ for each section $s$ of $\mathcal{O}_Y$ near $f(x)$.

*Proof.* Since $f_x$ is local, $f_x(\mathfrak{m}_{f(x)}) \subseteq \mathfrak{m}_x$, so the composite $\mathcal{O}_{Y, f(x)} \to \mathcal{O}_{X,x} \to \kappa(x)$ kills $\mathfrak{m}_{f(x)}$ and factors through $\kappa(f(x))$. For the formula, $f^\#(s)(x)$ is the class of $(f^\# s)_x = f_x(s_{f(x)})$, which is the image of the class of $s_{f(x)}$. $\square$

**Theorem (Isomorphisms of locally ringed spaces).** The forgetful functor from locally ringed spaces to ringed spaces is faithful. An isomorphism of ringed spaces between locally ringed spaces is an isomorphism of locally ringed spaces.

*Proof.* Faithfulness holds because a morphism of locally ringed spaces is a morphism of ringed spaces with a property. Let $f$ be an isomorphism of ringed spaces with inverse $g$. By the composition rule for stalk maps, $f_x$ is a ring isomorphism with inverse $g_{f(x)}$. A ring isomorphism between local rings maps the nonunits onto the nonunits, so it is local. The same holds for $g$, so $f$ and $g$ are morphisms of locally ringed spaces, inverse to each other. $\square$

**Proposition (Restriction keeps stalks).** For an open embedding $j : U \to X$ and $x \in U$, the stalk map of $X|_U \to X$ at $x$ is an isomorphism $\mathcal{O}_{X, j(x)} \cong \mathcal{O}_{X|_U, x}$. So the restriction of a locally ringed space is locally ringed, and $X|_U \to X$ is a morphism of locally ringed spaces.

*Proof.* The open neighbourhoods $j(V)$ of $j(x)$ with $V \ni x$ open in $U$ are cofinal among the neighbourhoods of $j(x)$, since $j(U)$ is open and $W \cap j(U) = j(j^{-1}W)$. On them the two colimits have the same terms $\mathcal{O}_X(j(V))$, so the stalk map is an isomorphism. An isomorphism of local rings is local. $\square$

### Examples

**Example (Continuous functions).** Let $X = \mathbb{R}^n$ and $\mathcal{O}_X(U)$ the ring of continuous real functions on $U$. The stalk at $x$ is local with maximal ideal $\mathfrak{m}_x$ the germs vanishing at $x$: a germ with $f(x) \neq 0$ is nonzero near $x$ and has the inverse $1/f$ there. The map $\mathcal{O}_{X,x} \to \mathbb{R}$, $f_x \mapsto f(x)$, is surjective with kernel $\mathfrak{m}_x$, so $\kappa(x) = \mathbb{R}$ and the value $s(x)$ is the usual value. The basic open set $X_s$ is $\{x : s(x) \neq 0\}$. A continuous map $\phi : X \to Y$ gives the morphism with $\phi^\#(s) = s \circ \phi$. Its stalk map sends $\mathfrak{m}_{\phi(x)}$ into $\mathfrak{m}_x$, since $s(\phi(x)) = 0$ gives $(s \circ \phi)(x) = 0$.

**Example (Residue fields of Spec $\mathbb{Z}$).** Chapter 3 shows that $\operatorname{Spec} \mathbb{Z}$ is a locally ringed space with $\mathcal{O}(\operatorname{Spec} \mathbb{Z}) = \mathbb{Z}$, stalk $\mathbb{Z}_{(p)}$ at $(p)$ and stalk $\mathbb{Q}$ at $(0)$. The residue fields are $\mathbb{Z}_{(p)}/p\mathbb{Z}_{(p)} \cong \mathbb{F}_p$ and $\mathbb{Q}$. The global section $6$ has the value $6 \bmod 5 = 1$ at $(5)$, the value $0$ at $(2)$ and $(3)$, and the value $6$ at $(0)$. So $X_6 = \operatorname{Spec} \mathbb{Z} \setminus \{(2), (3)\}$, in line with the theorem on values: $6$ is a unit in $\mathbb{Z}_{(p)}$ exactly for $p \neq 2, 3$.

**Counterexample (A ringed space that is not locally ringed).** Let $X$ be a point with $\mathcal{O}_X(X) = \mathbb{Z}$. The stalk is $\mathbb{Z}$, which has the maximal ideals $(2)$ and $(3)$, so it is not local. A point with the ring $k \times k$ also fails, since $(1, 0)$ and $(0, 1)$ are nonunits with a unit sum.

**Counterexample (A morphism that is not local).** Let $X$ and $Y$ be points with $\mathcal{O}_Y = \mathbb{Z}_{(p)}$ and $\mathcal{O}_X = \mathbb{Q}$. The inclusion $\mathbb{Z}_{(p)} \to \mathbb{Q}$ defines a morphism of ringed spaces $X \to Y$. It is not a morphism of locally ringed spaces: $p \in \mathfrak{m}_Y$ maps to a unit of $\mathbb{Q}$. The local morphisms $X \to Y$ correspond to the local homomorphisms $\mathbb{Z}_{(p)} \to \mathbb{Q}$, and there are none, since such a map sends $p$ to $p \neq 0$.

**Example (The empty space).** The empty space with its unique sheaf is a locally ringed space, since it has no stalk. It is initial: from it, every morphism has the empty map as base and the unique maps to $\mathcal{O}(\emptyset)$, the zero ring, as sheaf components.

### The library around it

::: mathlib
`AlgebraicGeometry.PresheafedSpace.Hom` · `Mathlib.Geometry.RingedSpace.PresheafedSpace`

A morphism has fields `base : X ⟶ Y` in `TopCat` and `c : Y.presheaf ⟶ base _* X.presheaf`. Composition is `PresheafedSpace.comp`, and `isoOfComponents` builds an isomorphism from a homeomorphism and an isomorphism of presheaves.

<?decl AlgebraicGeometry.PresheafedSpace.Hom?>
:::

::: mathlib
`AlgebraicGeometry.SheafedSpace` · `Mathlib.Geometry.RingedSpace.SheafedSpace`

`SheafedSpace C` extends `PresheafedSpace C` with `IsSheaf`. Its category is induced from presheafed spaces, so a morphism `f` has the presheafed morphism `f.hom`; `forgetToPresheafedSpace` is fully faithful. `AlgebraicGeometry.RingedSpace` is `SheafedSpace CommRingCat`.

<?decl AlgebraicGeometry.SheafedSpace?>
:::

::: mathlib
`AlgebraicGeometry.PresheafedSpace.Hom.stalkMap` · `Mathlib.Geometry.RingedSpace.Stalks`

`α.stalkMap x : Y.presheaf.stalk (α.base x) ⟶ X.presheaf.stalk x`, with the rules `stalkMap.id`, `stalkMap.comp` and `stalkMap_germ`. For locally ringed spaces it is `LocallyRingedSpace.Hom.stalkMap`.

<?decl AlgebraicGeometry.PresheafedSpace.Hom.stalkMap?>
:::

::: mathlib
`AlgebraicGeometry.LocallyRingedSpace.Hom` · `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`

A morphism extends a presheafed morphism with `prop : ∀ x, IsLocalHom (stalkMap x).hom`. `forgetToSheafedSpace` is faithful and reflects isomorphisms, and `isoOfSheafedSpaceIso` turns an isomorphism of sheafed spaces into one of locally ringed spaces.

<?decl AlgebraicGeometry.LocallyRingedSpace.Hom?>
:::

::: mathlib
`AlgebraicGeometry.RingedSpace.basicOpen` · `Mathlib.Geometry.RingedSpace.Basic`

`X.basicOpen f` is the set of `x ∈ U` where the germ of `f` is a unit. The lemmas `isUnit_res_of_isUnit_germ`, `isUnit_of_isUnit_germ` and `isUnit_res_basicOpen` are the theorem on units above.

<?decl AlgebraicGeometry.RingedSpace.basicOpen?>
:::

::: mathlib
`AlgebraicGeometry.LocallyRingedSpace.residueField` · `Mathlib.Geometry.RingedSpace.LocallyRingedSpace.ResidueField`

`X.residueField x` is `IsLocalRing.ResidueField` of the stalk, with a `Field` instance. `evaluation` is the germ followed by `residue`, `evaluation_eq_zero_iff_notMem_basicOpen` is the theorem on values, and `residueFieldMap f x : Y.residueField (f.base x) ⟶ X.residueField x` is the map of residue fields. The scheme version is `AlgebraicGeometry.Scheme.residueField`.

<?decl AlgebraicGeometry.LocallyRingedSpace.residueField?>
:::

::: mathlib
`AlgebraicGeometry.PresheafedSpace.restrict` · `Mathlib.Geometry.RingedSpace.PresheafedSpace`

`X.restrict h` takes `h : IsOpenEmbedding f` and has the presheaf `h.functor.op ⋙ X.presheaf`. The morphism back is `ofRestrict`, and `restrictStalkIso` is the isomorphism of stalks.

<?decl AlgebraicGeometry.PresheafedSpace.restrict?>
:::

Common errors of a learner: the sheaf map `c` of a morphism goes from `Y.presheaf` to the pushforward of `X.presheaf`, not in the direction of the map of spaces. A morphism of sheafed spaces is a wrapper, and its data is in `f.hom.base` and `f.hom.c`. A morphism of ringed spaces between locally ringed spaces need not be local. The value of a section at a point lies in a field that depends on the point, so a section of a scheme is not a function to one fixed ring.

### Exercises

1. (A) Let $X$ be a point with the ring $k[x]/(x^2)$. Show that $X$ is locally ringed, and compute $\kappa$ and the basic open set of the section $x$. *Hint:* The ring is local with maximal ideal $(x)$.
2. (A) Show that in a locally ringed space $X_1 = U$ for $1 \in \mathcal{O}_X(U)$, and $X_{s^n} = X_s$ for $n \ge 1$. *Hint:* Use $X_{st} = X_s \cap X_t$.
3. (B) Let $X$ be locally ringed and $s \in \mathcal{O}_X(X)$. Show that the zero locus of $\{s\}$ is closed and equals the set of $x$ with $s(x) = 0$. *Hint:* Use the theorem on values.
4. (B) Let $\phi : M \to N$ be a smooth map of manifolds. Show that $\phi^\#(s) = s \circ \phi$ defines a morphism of locally ringed spaces with smooth functions as structure sheaves. *Hint:* Check that the stalk maps send germs vanishing at $\phi(x)$ to germs vanishing at $x$.
5. (B) Let $f : X \to Y$ be a morphism of locally ringed spaces and $s \in \mathcal{O}_Y(V)$. Show that $f^{-1}(Y_s) = X_{f^\#(s)}$. *Hint:* A local homomorphism reflects units.
6. (C) Let $R$ be a local ring and $K$ a field. Show that the morphisms of locally ringed spaces from the point with ring $K$ to the point with ring $R$ correspond to the field homomorphisms $R/\mathfrak{m} \to K$. *Hint:* A local homomorphism to a field has the maximal ideal as kernel.
7. (C) Show that a morphism of ringed spaces $X \to Y$ between locally ringed spaces is local if and only if, for every open $V$ and every $s \in \mathcal{O}_Y(V)$, $f^{-1}(Y_s) = X_{f^\#(s)}$. *Hint:* For the converse, take $s$ with $s_{f(x)} \in \mathfrak{m}_{f(x)}$.

### Notes and history

Ringed spaces enter algebraic geometry with Serre in FAC (1955), where a variety is a space with a sheaf of rings of functions. Grothendieck made locally ringed spaces the basis of the theory of schemes in EGA, from 1960 to 1967, and Hartshorne (1977) defines a scheme as a locally ringed space locally isomorphic to the spectrum of a ring. The Mathlib definitions follow this route. Buzzard, Commelin and Massot defined schemes in Lean in 2020 in the same way.

The Mathlib Author of `Geometry.RingedSpace.PresheafedSpace`, `Geometry.RingedSpace.SheafedSpace` and `Geometry.RingedSpace.Stalks` is Kim Morrison. The Mathlib Authors of `Geometry.RingedSpace.Basic` are Justus Springer and Andrew Yang. The Mathlib Author of `Geometry.RingedSpace.LocallyRingedSpace` is Johan Commelin, and that of `Geometry.RingedSpace.LocallyRingedSpace.ResidueField` is Christian Merten.

### Reference

<?reference?>
