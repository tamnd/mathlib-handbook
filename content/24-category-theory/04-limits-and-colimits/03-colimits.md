---
title: Colimits
kind: theory
modules:
  - Mathlib.CategoryTheory.Limits.Cones
  - Mathlib.CategoryTheory.Limits.IsLimit
  - Mathlib.CategoryTheory.Limits.HasLimits
  - Mathlib.CategoryTheory.Limits.Types.Colimits
  - Mathlib.CategoryTheory.Filtered.Basic
  - Mathlib.CategoryTheory.Limits.Types.Filtered
explains:
  E3: [CategoryTheory.Limits.Cocone, CategoryTheory.Limits.IsColimit, CategoryTheory.Limits.colimit, CategoryTheory.IsFiltered, CategoryTheory.Limits.Types.FilteredColimit.colimit_eq_iff]
  E2: [CategoryTheory.Limits.Cocone.ι, CategoryTheory.Limits.Cocone.op, CategoryTheory.Limits.IsColimit.desc, CategoryTheory.Limits.IsColimit.fac, CategoryTheory.Limits.IsColimit.uniq, CategoryTheory.Limits.isLimitEquivIsColimitOp, CategoryTheory.Limits.HasColimit, CategoryTheory.Limits.HasColimitsOfShape, CategoryTheory.Limits.HasColimits, CategoryTheory.Limits.colimit.ι, CategoryTheory.Limits.colimit.desc, CategoryTheory.Limits.colimit.ι_desc, CategoryTheory.Limits.IsInitial, CategoryTheory.Limits.sigmaObj, CategoryTheory.Limits.coprod, CategoryTheory.Limits.coprod.inl, CategoryTheory.Limits.coprod.desc, CategoryTheory.Limits.Cofork, CategoryTheory.Limits.coequalizer, CategoryTheory.Limits.coequalizer.π, CategoryTheory.Limits.pushout, CategoryTheory.Limits.PushoutCocone, CategoryTheory.Limits.Types.colimit_eq, CategoryTheory.Limits.Types.jointly_surjective, CategoryTheory.Functor.ColimitType, CategoryTheory.IsFilteredOrEmpty, CategoryTheory.IsFiltered.max, CategoryTheory.IsFiltered.coeq, CategoryTheory.isFiltered_of_semilatticeSup_nonempty]
  E1: auto
families: []
requires: [V24.C01, V24.C02, V24.C03, V05, V08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Colimits

### Overview

A colimit is a limit in the opposite category. Where a limit is the best object with maps *to* a diagram, a colimit is the best object with maps *from* it. Disjoint unions, free products of groups, tensor products of commutative rings and quotient spaces are colimits. Duality gives the general theory from Sections 1 and 2, but the computations are harder: a limit in sets is a subset of a product, but a colimit in sets is a quotient of a disjoint union, and the equivalence relation must be generated. For filtered diagrams the relation has a simple form, and this is the main theorem of the section.

### Definitions

**Definition (Cocone).** A *cocone* under $F : J \to C$ is an object $X$ with morphisms $\iota_j : F(j) \to X$ such that $\iota_k \circ F(u) = \iota_j$ for each $u : j \to k$. Equivalently, it is a natural transformation $\iota : F \Rightarrow \Delta X$. A morphism of cocones $(X, \iota) \to (Y, \tau)$ is a map $f : X \to Y$ with $f \circ \iota_j = \tau_j$.

**Definition (Colimit).** A cocone $(L, \iota)$ is a *colimit* if for each cocone $(X, \tau)$ there is exactly one $u : L \to X$ with $u \circ \iota_j = \tau_j$ for all $j$. That is, it is an initial object of the category of cocones. $C$ is *cocomplete* if it has colimits of all small diagrams.

The dual names of the shapes of Section 2 are these. An *initial object* is a colimit of the empty diagram: an object with exactly one map to each object. A *coproduct* $\coprod_i X_i$ is a colimit of a family, with *injections* $\iota_i$. A *coequalizer* of $f, g : X \to Y$ is a map $q : Y \to Q$ with $q \circ f = q \circ g$, universal among such maps. A *pushout* of $f : Z \to X$ and $g : Z \to Y$ is a colimit of the *span* $X \leftarrow Z \to Y$.

**Definition (Filtered category).** A category $J$ is *filtered* if it is nonempty and

1. for all objects $i, j$ there are an object $k$ and maps $i \to k$, $j \to k$;
2. for all parallel maps $f, g : i \to j$ there is a map $h : j \to k$ with $h \circ f = h \circ g$.

A directed poset, that is, a nonempty poset in which any two elements have an upper bound, is filtered: condition 2 holds because parallel maps in a poset are equal. A colimit of a diagram of filtered shape is a *filtered colimit*.

::: mathlib
`CategoryTheory.Limits.Cocone` · `Mathlib.CategoryTheory.Limits.Cones`

A `Cocone F` has the apex `pt` and `ι : F ⟶ (Functor.const J).obj pt`. `IsColimit t` is the structure with `desc`, `fac` and `uniq`, dual to `IsLimit`. Under `HasColimit F`, the chosen colimit is `colimit F`, with `colimit.ι F j` and `colimit.desc F c`. The lemma `colimit.ι_desc` says `colimit.ι F j ≫ colimit.desc F c = c.ι.app j`.

<?decl CategoryTheory.Limits.Cocone?>
<?decl CategoryTheory.Limits.IsColimit?>
<?decl CategoryTheory.Limits.colimit?>
:::

The shapes have the API of Section 2 with dual names: `IsInitial`, `sigmaObj f` for the coproduct, `coprod X Y` with `coprod.inl` and `coprod.desc`, `Cofork f g` and `coequalizer f g` with `coequalizer.π f g`, and `pushout f g` with `PushoutCocone f g`.

### Theorems and proofs

**Proposition (Duality).** A cocone under $F$ with apex $X$ is the same as a cone over $F^{\mathrm{op}} : J^{\mathrm{op}} \to C^{\mathrm{op}}$ with apex $X$, and $(L, \iota)$ is a colimit of $F$ if and only if it is a limit of $F^{\mathrm{op}}$.

*Proof.* A map $\iota_j : F(j) \to X$ in $C$ is a map $X \to F(j)$ in $C^{\mathrm{op}}$. The cocone condition $\iota_k \circ F(u) = \iota_j$ in $C$ reads $F(u)^{\mathrm{op}} \circ \iota_k = \iota_j$ in $C^{\mathrm{op}}$, which is the cone condition for the map $u^{\mathrm{op}} : k \to j$ of $J^{\mathrm{op}}$. A factorization $u \circ \iota_j = \tau_j$ in $C$ is a factorization $\iota_j \circ u = \tau_j$ in $C^{\mathrm{op}}$. So the two universal properties are the same statement. $\square$

So colimits are unique up to unique isomorphism, and a category with coproducts and coequalizers is cocomplete.

**Theorem (Colimits in sets).** Let $F : J \to \mathbf{Set}$ with $J$ small. Let $\sim$ be the equivalence relation on the disjoint union $\coprod_j F(j) = \{(j, x) : x \in F(j)\}$ generated by $(j, x) \sim (k, F(u)(x))$ for all $u : j \to k$ and $x \in F(j)$. Put $L = \coprod_j F(j) / {\sim}$ and $\iota_j(x) = [j, x]$. Then $(L, \iota)$ is a colimit of $F$.

*Proof.* By the generating relation, $\iota_k(F(u)(x)) = [k, F(u)(x)] = [j, x] = \iota_j(x)$, so $\iota$ is a cocone. Let $(W, \tau)$ be a cocone. Let $\Psi : \coprod_j F(j) \to W$ send $(j, x)$ to $\tau_j(x)$. The relation "$\Psi(a) = \Psi(b)$" is an equivalence relation. It contains the generating pairs, since $\tau_k(F(u)(x)) = \tau_j(x)$ by the cocone condition. So it contains $\sim$, and $\Psi$ induces $\phi : L \to W$ with $\phi([j, x]) = \tau_j(x)$, that is, $\phi \circ \iota_j = \tau_j$. Each element of $L$ is some $[j, x] = \iota_j(x)$, so a map $L \to W$ is determined by its composites with the $\iota_j$. Hence $\phi$ is unique. $\square$

In particular, the initial object of $\mathbf{Set}$ is the empty set, the coproduct is the disjoint union, and the coequalizer of $f, g : X \to Y$ is $Y$ modulo the equivalence relation generated by $f(x) \sim g(x)$.

**Theorem (Filtered colimits in sets).** Let $J$ be filtered and $F : J \to \mathbf{Set}$. For $(i, x)$ and $(j, y)$ in $\coprod_j F(j)$, put $(i, x) \approx (j, y)$ if there are $k$, $f : i \to k$ and $g : j \to k$ with $F(f)(x) = F(g)(y)$. Then $\approx$ is the relation $\sim$ of the previous theorem. So in the colimit $L$, $[i, x] = [j, y]$ if and only if $x$ and $y$ become equal at some later stage.

*Proof.* First, $\approx$ is an equivalence relation. It is reflexive, with $k = i$ and $f = g = 1_i$, and it is symmetric by its form. For transitivity, let $(i, x) \approx (j, y)$ by $f : i \to k$, $g : j \to k$, and $(j, y) \approx (l, z)$ by $g' : j \to m$, $h : l \to m$. By condition 1 there are $a : k \to n$ and $b : m \to n$. The maps $a \circ g$ and $b \circ g'$ from $j$ to $n$ are parallel, so by condition 2 there is $c : n \to p$ with $c \circ a \circ g = c \circ b \circ g'$. Then
$$F(c a f)(x) = F(c a)(F(g)(y)) = F(c a g)(y) = F(c b g')(y) = F(c b)(F(h)(z)) = F(c b h)(z),$$
so $(i, x) \approx (l, z)$ by the maps $c a f$ and $c b h$.

Next, $\approx$ contains the generating pairs: $(j, x) \approx (k, F(u)(x))$ by $u$ and $1_k$. So $\sim$ is contained in $\approx$. Conversely, if $F(f)(x) = F(g)(y)$, then $(i, x) \sim (k, F(f)(x)) = (k, F(g)(y)) \sim (j, y)$. So $\approx$ is contained in $\sim$. $\square$

By condition 1, any finite set of elements of $L$ lies in the image of one $\iota_k$. So algebraic structure passes to filtered colimits; Exercise 4 treats groups.

::: mathlib
`CategoryTheory.Limits.Types.FilteredColimit.colimit_eq_iff` · `Mathlib.CategoryTheory.Limits.Types.Filtered`

The statement is: under `[IsFilteredOrEmpty J]`, `colimit.ι F i xi = colimit.ι F j xj ↔ ∃ k (f : i ⟶ k) (g : j ⟶ k), F.map f xi = F.map g xj`. The class `IsFilteredOrEmpty` has the two fields `cocone_objs` and `cocone_maps`, conditions 1 and 2. The proof does not use that $J$ is nonempty. `IsFiltered` adds `Nonempty J`. The choices of condition 1 and 2 are `IsFiltered.max` and `IsFiltered.coeq`. The instance `isFiltered_of_semilatticeSup_nonempty` makes each nonempty join semilattice filtered.

<?decl CategoryTheory.Limits.Types.FilteredColimit.colimit_eq_iff?>
<?decl CategoryTheory.IsFiltered?>
:::

### Examples

**Counterexample (The relation must be generated).** Let $X = \{1, 2\}$, $Y = \{a, b, c\}$, and $f, g : X \to Y$ with $f(1) = a$, $g(1) = b$, $f(2) = b$, $g(2) = c$. The set of pairs $\{(f(x), g(x))\} = \{(a, b), (b, c)\}$ is not transitive. The coequalizer must identify $a$ with $b$ and $b$ with $c$, so the generated equivalence relation has one class, and the coequalizer is a one-point set. The shape $\bullet \rightrightarrows \bullet$ is not filtered, so the theorem on filtered colimits does not apply.

**Example (A sequential colimit).** Let $F$ be the diagram $\mathbb{Z} \xrightarrow{2} \mathbb{Z} \xrightarrow{2} \mathbb{Z} \to \cdots$ of abelian groups, indexed by the directed poset $\mathbb{N}$. Its colimit is $\mathbb{Z}[1/2]$, with $\iota_n(a) = a / 2^n$. The cocone condition is $\iota_{n+1}(2a) = 2a/2^{n+1} = \iota_n(a)$. In sets, the filtered theorem says $[n, a] = [m, b]$ with $m \ge n$ if and only if $2^{p - n} a = 2^{p - m} b$ for some $p \ge m$, that is, $a/2^n = b/2^m$. So $[n, a] \mapsto a/2^n$ is a bijection from the colimit in sets onto $\mathbb{Z}[1/2]$. For a cocone $\tau_n : \mathbb{Z} \to A$ of groups, the map $a/2^n \mapsto \tau_n(a)$ is well defined by the same computation, and it is additive since two elements lie in a common stage $\iota_m(\mathbb{Z})$. So $\mathbb{Z}[1/2]$ is also the colimit in abelian groups.

**Example (Free products).** The coproduct of two groups $G$ and $H$ is the free product $G * H$: its elements are reduced words in the nontrivial elements of $G$ and $H$, and the injections send an element to the word of length one. Homomorphisms $\phi : G \to K$ and $\psi : H \to K$ induce the map that multiplies out a word in $K$. Its underlying set is not the disjoint union: $\mathbb{Z}/2 * \mathbb{Z}/2$ is infinite.

**Example (Tensor products).** Let $R \to A$ and $R \to B$ be maps of commutative rings. Their pushout is $A \otimes_R B$, with $a \mapsto a \otimes 1$ and $b \mapsto 1 \otimes b$ (Volume 8, Chapter 2). For ring maps $\phi : A \to T$ and $\psi : B \to T$ that agree on $R$, the map $a \otimes b \mapsto \phi(a)\psi(b)$ is well defined, since it comes from an $R$-bilinear map, and it is the unique ring map that restricts to $\phi$ and $\psi$. For instance, $\mathbb{Z}[x] \otimes_{\mathbb{Z}} \mathbb{Z}[y] \cong \mathbb{Z}[x, y]$, and $\mathbb{Q} \otimes_{\mathbb{Z}} \mathbb{F}_2 = 0$, since $1 \otimes 1 = 2 \cdot (\tfrac12 \otimes 1) = \tfrac12 \otimes 2 = 0$.

::: mathlib
`Monoid.Coprod` · `Mathlib.GroupTheory.Coprod.Basic`

`Monoid.Coprod M N` is the free product of monoids, with the universal map `Monoid.Coprod.lift`; for groups it is a group. The index of this edition has no declaration that identifies it with the coproduct in `GrpCat`. The pushout of commutative rings is `CommRingCat.pushoutCocone`, with apex `A ⊗[R] B`, and `CommRingCat.pushoutCoconeIsColimit`. For spaces, `TopCat.coequalizer_isOpen_iff` says that a coequalizer carries the quotient topology. In `Type`, the coequalizer is compared with `Function.Coequalizer` by `Types.coequalizerIso`.

<?decl Monoid.Coprod?>
<?decl CommRingCat.pushoutCoconeIsColimit?>
<?decl TopCat.coequalizer_isOpen_iff?>
:::

### The library around it

For colimits in `Type`, `Mathlib.CategoryTheory.Limits.Types.Colimits` gives `Types.jointly_surjective`, every element of a colimit comes from some `F.obj j`, and `Types.colimit_eq`, which turns an equation in the colimit into `Relation.EqvGen` of the generating relation. The quotient is `Functor.ColimitType`. Duality is `isLimitEquivIsColimitOp`, with the cone `Cocone.op`.

Common errors of a learner:

- Expecting `colimit.ι F i x = colimit.ι F j y` to give one step of the relation. In general it gives only `EqvGen`, a chain of steps. The one step form needs a filtered shape.
- Forgetting that a cocone is a map *from* the diagram: the composite is `F.map f ≫ c.ι.app j' = c.ι.app j`.
- Computing a colimit of groups as a colimit of sets. This fails for coproducts.

### Exercises

1. (A) Show that $\emptyset$ is initial in $\mathbf{Set}$ and in spaces, that the trivial group is initial in groups, and that $\mathbb{Z}$ is initial in rings.
2. (A) Show that a coequalizer is an epimorphism, by duality and directly.
3. (A) Compute the pushout of $\{0\} \leftarrow \{0, 1\} \to \{0\}$ in $\mathbf{Set}$, and the pushout of $\mathbb{Z}/2 \leftarrow \mathbb{Z} \to \mathbb{Z}/3$ in commutative rings.
4. (B) Let $J$ be filtered and $F : J \to \mathbf{Grp}$. Put a group structure on the colimit $L$ in sets: to multiply $[i, x]$ and $[j, y]$, choose $k$ with $f : i \to k$, $g : j \to k$, and put $[i, x][j, y] = [k, F(f)(x) F(g)(y)]$. Show that this is well defined and that $L$ is the colimit in groups.
5. (B) Compute the colimit of $\mathbb{Z}/p \to \mathbb{Z}/p^2 \to \mathbb{Z}/p^3 \to \cdots$, with the maps $a \mapsto pa$, in abelian groups.
6. (C) Show that in $\mathbf{Set}$ filtered colimits commute with finite limits: for $J$ filtered, $I$ finite and $F : I \times J \to \mathbf{Set}$, the canonical map $\mathrm{colim}_j \lim_i F(i, j) \to \lim_i \mathrm{colim}_j F(i, j)$ is a bijection. Hint: treat the terminal object, binary products and equalizers.

### Notes and history

Direct limits of groups were used in algebra and topology before the general notion. Mac Lane's book (1971) treats colimits as the dual of limits, as here. The theorem on filtered colimits in sets and its consequence in Exercise 6 explain why much of algebra behaves well under filtered colimits.

### Reference

<?reference?>
