---
title: The étale and pro-étale sites
kind: theory
modules:
  - Mathlib.AlgebraicGeometry.Sites.AffineEtale
  - Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
  - Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
  - Mathlib.AlgebraicGeometry.Sites.Etale
  - Mathlib.AlgebraicGeometry.Sites.EtalePoint
  - Mathlib.AlgebraicGeometry.Sites.Proetale
explains:
  E3: [AlgebraicGeometry.Scheme.etaleTopology, AlgebraicGeometry.Scheme.smallEtaleTopology, AlgebraicGeometry.Scheme.ofArrows_mem_smallEtaleTopology_iff, AlgebraicGeometry.Scheme.exists_fac_of_etale_of_isSepClosed, AlgebraicGeometry.Scheme.pointSmallEtale, AlgebraicGeometry.Scheme.isConservative_pointSmallEtale, AlgebraicGeometry.Scheme.proetaleTopology, AlgebraicGeometry.isSheaf_fpqcTopology_continuousMapPresheaf, AlgebraicGeometry.Scheme.ellAdicSheaf, AlgebraicGeometry.Scheme.EllAdicCohomology]
  E2: [AlgebraicGeometry.Scheme.etalePrecoverage, AlgebraicGeometry.Scheme.zariskiTopology_le_etaleTopology, AlgebraicGeometry.Scheme.smallEtalePretopology, AlgebraicGeometry.Scheme.geometricFiber, AlgebraicGeometry.Scheme.AffineEtale, AlgebraicGeometry.Scheme.AffineEtale.topology, AlgebraicGeometry.Scheme.AffineEtale.sheafEquiv, AlgebraicGeometry.Scheme.AffineEtale.instEssentiallySmall, AlgebraicGeometry.Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology, AlgebraicGeometry.Scheme.pointSmallEtaleFiberObjToPreimage_surjective, AlgebraicGeometry.Scheme.isConservativeFamilyOfPoints_pointSmallEtale', AlgebraicGeometry.Scheme.instHasEnoughPointsEtaleSmallEtaleTopology, AlgebraicGeometry.Scheme.proetalePrecoverage, AlgebraicGeometry.Scheme.etaleTopology_le_proetaleTopology, AlgebraicGeometry.Scheme.proetaleTopology_le_fpqcTopology, AlgebraicGeometry.Scheme.instSubcanonicalProetaleTopology, AlgebraicGeometry.Scheme.ProEt, AlgebraicGeometry.Scheme.ProEt.topology, AlgebraicGeometry.Scheme.ProEt.topology_eq_top_of_isEmpty, AlgebraicGeometry.continuousMapPresheaf, AlgebraicGeometry.isSheaf_zariskiTopology_continuousMapPresheaf, AlgebraicGeometry.continuousMapPresheafEquivOfTotallyDisconnectedSpace, AlgebraicGeometry.continuousMapPresheafAb, AlgebraicGeometry.isSheaf_fpqcTopology_continuousMapPresheafAb, AlgebraicGeometry.Scheme.isZero_ellAdicSheaf_of_isEmpty]
  E1: auto
families: []
requires: [V10.C08, V11.C03, V11.C04, V12.C05, V13.C06, V25.C06, V26.C04, V28.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The étale and pro-étale sites

### Overview

The Zariski topology is too coarse for cohomology with finite or $\ell$-adic coefficients. On an irreducible scheme every two nonempty opens meet, so a constant Zariski sheaf has no higher cohomology. The étale topology adds the étale morphisms as covers. Its points are the geometric points $\operatorname{Spec} \Omega \to X$ with $\Omega$ separably closed, and the étale fundamental group and étale cohomology live on it. The pro-étale topology of Bhatt and Scholze enlarges it further to weakly étale covers, so that $\ell$-adic coefficients are a sheaf and not only an inverse system of sheaves.

This section defines the big and small étale sites and the affine étale site, proves that geometric points lift along étale morphisms and that these points detect covers, defines the pro-étale topology, proves that sheaves of continuous maps are fpqc sheaves, and defines $\ell$-adic cohomology in Mathlib.

### Definitions

**Definition (Étale topology).** The *étale topology* on schemes is the $P$-topology of the previous section for $P$ the class of étale morphisms. A family $\{U_i \to X\}$ covers when each map is étale and the images cover $X$.

**Definition (Small étale site).** Let $X$ be a scheme. The *small étale site* of $X$ has as objects the étale morphisms $U \to X$ and as morphisms the maps over $X$. A family over $X$ covers when the family of underlying morphisms is jointly surjective.

A morphism between two étale $X$-schemes is étale, so a jointly surjective family in the small site is an étale cover of schemes.

**Definition (Affine étale site).** The *affine étale site* of $S$ has as objects the pairs of a ring $R$ and an étale morphism $\operatorname{Spec} R \to S$. Its topology is induced from the small étale site along the functor that sends $(R, \operatorname{Spec} R \to S)$ to $\operatorname{Spec} R \to S$.

**Definition (Geometric point).** A *geometric point* of $S$ is a morphism $\bar{s} : \operatorname{Spec} \Omega \to S$ with $\Omega$ a separably closed field. Its *fiber functor* on the small étale site sends $U \to S$ to the set of $S$-morphisms $\operatorname{Spec} \Omega \to U$.

**Definition (Weakly étale morphism).** A morphism $f : X \to Y$ is *weakly étale* when $f$ is flat and its diagonal $X \to X \times_Y X$ is flat. The *pro-étale topology* has as covers the jointly surjective quasi-compact families of weakly étale morphisms.

**Definition (Sheaf of continuous maps).** Let $T$ be a topological space. The presheaf $C(-, T)$ sends a scheme $U$ to the set of continuous maps $|U| \to T$ on the underlying space, with restriction by composition.

**Definition ($\ell$-adic cohomology).** Let $\ell$ be a prime and $X$ a scheme. The *$\ell$-adic sheaf* of $X$ is the sheaf $U \mapsto C(U, \mathbb{Z}_\ell)$ of abelian groups on the pro-étale site of $X$. Its *$\ell$-adic cohomology* in degree $n$ is the sheaf cohomology $H^n$, defined as $\operatorname{Ext}^n$ from the constant sheaf $\mathbb{Z}$.

### Theorems and proofs

**Theorem (Order of the topologies).** The Zariski topology is contained in the étale topology, the étale topology in the pro-étale topology, and the pro-étale topology in the fpqc topology.

*Proof.* Step 1. An open immersion is étale, so Zariski covers are étale covers.

Step 2. An étale morphism $f : X \to Y$ is flat. Its diagonal is an open immersion, because $f$ is unramified, so the diagonal is flat. So $f$ is weakly étale. An étale morphism is flat and locally of finite presentation, so an étale cover is an fppf cover, and the comparison theorem of the previous section makes it quasi-compact. So étale covers are pro-étale covers.

Step 3. A weakly étale morphism is flat, and the pro-étale covers carry the same quasi-compactness condition as fpqc covers. $\square$

Since the fpqc topology is subcanonical, so are the étale and pro-étale topologies.

**Theorem (Lifting geometric points).** Let $f : X \to S$ be étale, $\Omega$ a separably closed field and $\bar{s} : \operatorname{Spec} \Omega \to S$. Let $x \in X$ with $f(x)$ equal to the image $s$ of $\bar{s}$. Then there is $l : \operatorname{Spec} \Omega \to X$ with $f \circ l = \bar{s}$ whose image is $x$.

*Proof.* Step 1. The morphism $\bar{s}$ factors through $\operatorname{Spec} \kappa(s)$ and gives a field map $\kappa(s) \to \Omega$.

Step 2. Because $f$ is étale, the fiber $X_s$ is étale over $\kappa(s)$, so it is a disjoint union of spectra of finite separable extensions. So $\kappa(x)$ is a finite separable extension of $\kappa(s)$.

Step 3. By the primitive element theorem $\kappa(x) = \kappa(s)(\alpha)$, and the minimal polynomial $g$ of $\alpha$ is separable. Its image in $\Omega[t]$ is separable, so it has a root $\beta$ in the separably closed field $\Omega$. The map $\alpha \mapsto \beta$ gives a $\kappa(s)$-embedding $\kappa(x) \to \Omega$.

Step 4. Let $l$ be the composite $\operatorname{Spec} \Omega \to \operatorname{Spec} \kappa(x) \to X$. Its image is $x$. The composite $f \circ l$ is $\operatorname{Spec} \Omega \to \operatorname{Spec} \kappa(s) \to S$ with the field map of step 1, which is $\bar{s}$. $\square$

**Corollary (Fibers map onto preimages).** For a geometric point $\bar{s}$ over $s \in S$ and an étale $U \to S$, the map from the fiber $\operatorname{Hom}_S(\operatorname{Spec} \Omega, U)$ to the preimage of $s$ in $U$, sending $l$ to its image point, is surjective.

*Proof.* This is the theorem applied to each point of the preimage. $\square$

**Theorem (Geometric points detect covers).** Let $\{\bar{s}_j\}$ be geometric points of $S$ whose images cover $S$. A family $\{g_i : U_i \to U\}$ in the small étale site covers if and only if for each $j$ and each $l \in \operatorname{Hom}_S(\operatorname{Spec} \Omega_j, U)$ some $i$ and some $l'$ with $g_i \circ l' = l$ exist.

*Proof.* Assume the family covers and let $l$ be given, with image $u \in U$. Choose $i$ and $u' \in U_i$ with $g_i(u') = u$. The morphism $g_i$ is étale, so the lifting theorem, applied to $g_i$, the geometric point $l$ of $U$ and $u'$, gives $l'$ with $g_i \circ l' = l$.

Conversely assume the lifting condition and let $u \in U$ lie over $s \in S$. Choose $j$ with $s$ in the image of $\bar{s}_j$. By the corollary there is $l$ in the fiber of $U$ with image $u$. Choose $i$ and $l'$ with $g_i \circ l' = l$. Then the image of $l'$ is a point of $U_i$ that maps to $u$. So the images of the $g_i$ cover $U$, and the family covers. $\square$

For each $s \in S$ the separable closure of $\kappa(s)$ gives a geometric point over $s$, so the small étale site has enough points.

**Theorem (Continuous maps form an fpqc sheaf).** For each topological space $T$ the presheaf $C(-, T)$ is a sheaf for the fpqc topology.

*Proof.* Step 1. Continuous maps glue along open covers, so $C(-, T)$ is a Zariski sheaf. By the fpqc sheaf criterion of the previous section it suffices to treat a faithfully flat morphism $f : V \to U$ of affine schemes.

Step 2. Let $g : |V| \to T$ be continuous with $g \circ p_1 = g \circ p_2$ on $V \times_U V$. Let $v, v' \in V$ with $f(v) = f(v')$. By the base-change lemma of the previous section there is $z \in V \times_U V$ with $p_1(z) = v$ and $p_2(z) = v'$. So $g(v) = g(v')$, and $g = h \circ f$ for a unique map of sets $h : |U| \to T$, since $f$ is surjective.

Step 3. A faithfully flat quasi-compact morphism is a quotient map of the underlying spaces. So $h$ is continuous. This gives the existence and uniqueness of the glued section. $\square$

**Proposition (Totally disconnected coefficients).** If $T$ is totally disconnected, then $C(U, T)$ is in bijection with $C(\pi_0(U), T)$, where $\pi_0(U)$ is the space of connected components of $|U|$ with the quotient topology.

*Proof.* A continuous map $g : |U| \to T$ sends each connected component to a connected subset of $T$, which is a point. So $g$ is constant on components and factors through the quotient map $|U| \to \pi_0(U)$. The factored map is continuous by the definition of the quotient topology, and it is unique because the quotient map is surjective. $\square$

With $T = \mathbb{Z}_\ell$, which is totally disconnected, this applies to the $\ell$-adic sheaf. On the empty scheme every sieve covers, so every sheaf is zero there and $\ell$-adic cohomology of the empty scheme is zero.

### Examples

**Example (The squaring cover).** Let $k$ be a field of characteristic not $2$, and let $\varphi : k[x, x^{-1}] \to k[t, t^{-1}]$ send $x$ to $t^2$. The target is free over the source with basis $1, t$, so $\varphi$ is flat and of finite presentation. The module of relative differentials is generated by $dt$ with the relation $d(t^2) = 2t\,dt = 0$, and $2t$ is a unit, so it is zero and $\varphi$ is étale. The map is finite and injective, so it is surjective on spectra. So $\operatorname{Spec} k[t, t^{-1}] \to \operatorname{Spec} k[x, x^{-1}]$ is an étale cover. It is not a Zariski cover: over $x = 1$ lie the two points $t = 1$ and $t = -1$. In characteristic $2$ the relation is $d(t^2) = 0$, the module of differentials is $k[t, t^{-1}]\,dt \neq 0$, and the map is not étale.

**Example (A Galois cover).** The map $\operatorname{Spec} \mathbb{C} \to \operatorname{Spec} \mathbb{R}$ is an étale cover. The fiber product is $\operatorname{Spec} (\mathbb{C} \otimes_{\mathbb{R}} \mathbb{C})$. Since $\mathbb{C} = \mathbb{R}[x]/(x^2 + 1)$, one gets $\mathbb{C} \otimes_{\mathbb{R}} \mathbb{C} = \mathbb{C}[x]/((x - i)(x + i)) \cong \mathbb{C} \times \mathbb{C}$ by the Chinese remainder theorem. The two factors correspond to the identity and complex conjugation. So for an étale sheaf $F$ the sheaf condition reads $F(\mathbb{R}) = F(\mathbb{C})^{\operatorname{Gal}(\mathbb{C}/\mathbb{R})}$.

**Example (Fibers at geometric points).** Let $U = \operatorname{Spec} \mathbb{Z}[1/2][i] \to \operatorname{Spec} \mathbb{Z}[1/2]$, which is étale since $x^2 + 1$ has derivative $2x$ and $x$ is a unit modulo $x^2 + 1$. Take the geometric point $\operatorname{Spec} \overline{\mathbb{F}}_5$ over $(5)$. The fiber is the set of ring maps $\mathbb{Z}[1/2][i] \to \overline{\mathbb{F}}_5$, so the set of roots of $x^2 + 1$ in $\overline{\mathbb{F}}_5$, which is $\{2, 3\}$ since $2^2 = 4 = -1$ and $3^2 = 9 = -1$ modulo $5$. The preimage of $(5)$ also has two points. Over $(3)$ the polynomial $x^2 + 1$ is irreducible over $\mathbb{F}_3$, so the preimage is one point with residue field $\mathbb{F}_9$, while the fiber at $\operatorname{Spec} \overline{\mathbb{F}}_3$ still has two elements. So the surjection of the corollary need not be injective.

**Example (Continuous maps on two points).** Let $U = \operatorname{Spec} k[x]/(x(x - 1))$. By the Chinese remainder theorem the ring is $k \times k$, so $|U|$ is two closed points with the discrete topology. For $T = \mathbb{Z}/2$ with the discrete topology, $C(U, T) = (\mathbb{Z}/2)^2$, with four elements.

### The library around it

::: mathlib
`AlgebraicGeometry.Scheme.etaleTopology` · `Mathlib.AlgebraicGeometry.Sites.Etale`

`Scheme.etaleTopology` is the topology of `@Etale`, with `Scheme.etalePrecoverage` and `Scheme.zariskiTopology_le_etaleTopology`. `Scheme.geometricFiber Ω` is a point of this big site with fiber functor `coyoneda.obj (Spec Ω)`. The small site `Scheme.smallEtaleTopology X` lives on `X.Etale`, and `Scheme.ofArrows_mem_smallEtaleTopology_iff` says that a family covers if and only if `⋃ i, Set.range (f i).left = .univ`.

<?decl AlgebraicGeometry.Scheme.etaleTopology?>
:::

::: mathlib
`AlgebraicGeometry.Scheme.AffineEtale` · `Mathlib.AlgebraicGeometry.Sites.AffineEtale`

`Scheme.AffineEtale S` is a costructured arrow category over `Spec` and `S`, with `AffineEtale.topology` and the equivalence `AffineEtale.sheafEquiv` with sheaves on the small site. The instance `AffineEtale.instEssentiallySmall` makes sheafification available, and `Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology` says that abelian étale sheaves form a Grothendieck abelian category.

<?decl AlgebraicGeometry.Scheme.AffineEtale?>
:::

::: mathlib
`AlgebraicGeometry.Scheme.exists_fac_of_etale_of_isSepClosed` · `Mathlib.AlgebraicGeometry.Sites.EtalePoint`

This is the lifting theorem. `Scheme.pointSmallEtale` is the point of the small site with fiber `Hom_S(Spec Ω, -)`, and `Scheme.pointSmallEtaleFiberObjToPreimage_surjective` is the corollary. `Scheme.isConservative_pointSmallEtale` is the detection theorem under the hypothesis that the images cover, and `Scheme.isConservativeFamilyOfPoints_pointSmallEtale'` uses separable closures of residue fields. The instance `Scheme.instHasEnoughPointsEtaleSmallEtaleTopology` follows.

<?decl AlgebraicGeometry.Scheme.exists_fac_of_etale_of_isSepClosed?>
:::

::: mathlib
`AlgebraicGeometry.Scheme.proetaleTopology` · `Mathlib.AlgebraicGeometry.Sites.Proetale`

`Scheme.proetalePrecoverage` is `propQCPrecoverage @WeaklyEtale`. The comparisons are `Scheme.etaleTopology_le_proetaleTopology` and `Scheme.proetaleTopology_le_fpqcTopology`, and `Scheme.instSubcanonicalProetaleTopology` follows. The pro-étale site of `S` is `Scheme.ProEt S`, the weakly étale `S`-schemes, with `ProEt.topology`. The lemma `ProEt.topology_eq_top_of_isEmpty` treats the empty scheme.

<?decl AlgebraicGeometry.Scheme.proetaleTopology?>
:::

::: mathlib
`AlgebraicGeometry.isSheaf_fpqcTopology_continuousMapPresheaf` · `Mathlib.AlgebraicGeometry.Sites.ConstantSheaf`

`continuousMapPresheaf T` is the presheaf of continuous maps. The lemmas `isSheaf_zariskiTopology_continuousMapPresheaf` and `isSheaf_fpqcTopology_continuousMapPresheaf` are steps 1 to 3 of the theorem, and the proof uses `Flat.isQuotientMap_of_surjective`. `continuousMapPresheafEquivOfTotallyDisconnectedSpace` is the proposition on components. The version `continuousMapPresheafAb` for a topological abelian group has `isSheaf_fpqcTopology_continuousMapPresheafAb`. A docstring TODO in this file still asks for the fpqc statement, but the lemma is present.

<?decl AlgebraicGeometry.isSheaf_fpqcTopology_continuousMapPresheaf?>
:::

::: mathlib
`AlgebraicGeometry.Scheme.EllAdicCohomology` · `Mathlib.AlgebraicGeometry.Sites.ElladicCohomology`

`Scheme.ellAdicSheaf ℓ` is `continuousMapPresheafAb ℤ_[ℓ]` pushed to `ProEt.topology X`; the source cites the paper of Bhatt and Scholze. `Scheme.EllAdicCohomology ℓ n` is `Sheaf.H` of this sheaf after a universe lift, so it lives in `Type (u + 1)`. `Scheme.isZero_ellAdicSheaf_of_isEmpty` is the computation for the empty scheme.

<?decl AlgebraicGeometry.Scheme.EllAdicCohomology?>
:::

Common errors of a learner: the fiber of a geometric point is a set of morphisms, not a set of points, and its map to the preimage need not be injective. `Scheme.etaleTopology` is on all schemes, while `Scheme.smallEtaleTopology X` is on `X.Etale`. The $\ell$-adic sheaf is a pro-étale sheaf, so $\ell$-adic cohomology is not the inverse limit of étale cohomology with coefficients $\mathbb{Z}/\ell^n$ by definition. The index of this edition has no declaration for the comparison of the two.

### Exercises

1. (A) Show that $\operatorname{Spec} \mathbb{Q}(\sqrt{2}) \to \operatorname{Spec} \mathbb{Q}$ is an étale cover and compute the fiber at the geometric point $\operatorname{Spec} \overline{\mathbb{Q}}$. *Hint:* Count the roots of $x^2 - 2$ in $\overline{\mathbb{Q}}$.
2. (A) Let $T$ be discrete and $U$ connected. Show that $C(U, T) = T$. *Hint:* A continuous map from a connected space to a discrete space is constant.
3. (B) Let $n \ge 1$ and $k$ a field whose characteristic does not divide $n$. Show that $x \mapsto x^n$ on $\operatorname{Spec} k[x, x^{-1}]$ is an étale cover. *Hint:* Follow the squaring example with basis $1, t, \dots, t^{n-1}$.
4. (B) Show that $\operatorname{Spec} \mathbb{Z}[i] \to \operatorname{Spec} \mathbb{Z}$ is not étale. *Hint:* Compute the fiber over $(2)$ and look for nilpotents.
5. (C) Show that the lifting theorem fails for $\Omega$ not separably closed. *Hint:* Use $\Omega = \mathbb{R}$, $S = \operatorname{Spec} \mathbb{R}$ and $X = \operatorname{Spec} \mathbb{C}$.
6. (C) Let $X = \operatorname{Spec} \prod_{n \in \mathbb{N}} \mathbb{F}_2$. Show that $|X|$ is totally disconnected and has infinitely many points. Deduce that $C(X, \mathbb{Z}/2)$ is not $\mathbb{Z}/2$. *Hint:* The idempotents $e_n$ give clopen sets $D(e_n)$.

### Notes and history

Grothendieck introduced the étale topology, and SGA 4 develops étale cohomology with SGA 5 for $\ell$-adic coefficients. Weakly étale morphisms and the pro-étale topology are due to Bhatt and Scholze, in their paper on the pro-étale topology for schemes, which the Mathlib sources cite for the $\ell$-adic sheaf.

The Mathlib Author of `Sites.Etale` and `Sites.ConstantSheaf` is Christian Merten. The Mathlib Authors of `Sites.AffineEtale` and `Sites.EtalePoint` are Christian Merten and Joël Riou. The Mathlib Authors of `Sites.Proetale` and `Sites.ElladicCohomology` are Jiedong Jiang and Christian Merten.

### Reference

<?reference?>
