---
title: Images, kernels, products and units of submonoids
kind: api
modules:
  - Mathlib.Algebra.Group.Submonoid.Operations
  - Mathlib.Algebra.Group.Submonoid.Units
explains:
  E2: [Submonoid.map_le_iff_le_comap, Submonoid.map_comap_eq, MonoidHom.mrange_eq_top, MonoidHom.coe_mker, Submonoid.prod_bot_sup_bot_prod, Submonoid.mem_units_iff, Subgroup.units_ofUnits_eq, ofUnits_le_iff_le_units, Submonoid.unitsEquivUnitsType]
  E1: auto
families: []
requires: [V01.C04, V04.C06, V05.C01, V05.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Images, kernels, products and units of submonoids

### Overview

A homomorphism of monoids moves submonoids in both directions: the image of a submonoid of the domain is a submonoid of the codomain, and the preimage of a submonoid of the codomain is a submonoid of the domain. The range and the kernel of a homomorphism are special cases. Submonoids of two monoids give a submonoid of the product, and a family of submonoids gives a submonoid of a product of a family. This section presents these operations for submonoids. They have the same form as the operations on subgroups in the first section of the chapter, and the names differ by a letter m in a few places.

The second module connects submonoids of $M$ with subgroups of the unit group $M^\times$. A submonoid $S$ gives the subgroup of the units $u$ with $u \in S$ and $u^{-1} \in S$. A subgroup $H$ of $M^\times$ gives the submonoid of the values of its members. The two maps form a Galois coinsertion, so the subgroups of $M^\times$ are a part of the lattice of submonoids of $M$.

### The library around it

#### Image and preimage

The module `Mathlib.Algebra.Group.Submonoid.Operations` defines `Submonoid.map f S` and `Submonoid.comap f T` for any `f : F` in a class `MonoidHomClass F M N`. So the same functions accept monoid homomorphisms, isomorphisms and ring homomorphisms. The carriers are the image and the preimage, by `Submonoid.coe_map` and `Submonoid.coe_comap`, and the membership forms are `Submonoid.mem_map` and `Submonoid.mem_comap`. The two maps form a Galois connection, `Submonoid.gc_map_comap`. Its working form is `Submonoid.map_le_iff_le_comap`:

$$f(S) \le T \iff S \le f^{-1}(T).$$

Both sides say that $f(x) \in T$ for every $x \in S$. The consequences are the same as in the subsemigroup layer: `Submonoid.map_sup` and `Submonoid.map_iSup` for the image, `Submonoid.comap_inf` and `Submonoid.comap_iInf` for the preimage, `Submonoid.map_map` and `Submonoid.comap_comap` for compositions. For an injective $f$, `Submonoid.gciMapComap` is a Galois coinsertion, so `Submonoid.comap_map_eq_of_injective` holds. For a surjective $f$, `Submonoid.giMapComap` is a Galois insertion, so `Submonoid.map_comap_eq_of_surjective` holds. An injective map preserves disjointness, by `Submonoid.disjoint_map`, and a surjective map preserves codisjointness, by `Submonoid.codisjoint_map`. For an isomorphism, the image is the preimage under the inverse, by `Submonoid.map_equiv_eq_comap_symm`.

#### Range and kernel

The range of $f$ is `MonoidHom.mrange f`, with carrier `Set.range f` by `MonoidHom.coe_mrange`. It is `Submonoid.map f ⊤`, by `MonoidHom.mrange_eq_map`. The image of a preimage is the intersection with the range, `Submonoid.map_comap_eq`:

$$f(f^{-1}(T)) = T \sqcap \operatorname{mrange} f.$$

Proof: an element of the left side is $f(x)$ with $f(x) \in T$, so it lies in $T$ and in the range. An element $y$ of the right side is $y = f(x)$ for some $x$, and $f(x) \in T$ puts $x$ in the preimage. The range is `⊤` if and only if $f$ is surjective, by `MonoidHom.mrange_eq_top`. The image of a closure is the closure of the image, by `MonoidHom.map_mclosure`.

The kernel `MonoidHom.mker f` is the preimage of `⊥`. Its carrier is $f^{-1}(\{1\})$, by `MonoidHom.coe_mker`. The kernel of a monoid homomorphism is much weaker than the kernel of a group homomorphism. In a group, $f(x) = f(y)$ gives $f(x y^{-1}) = 1$, so a trivial kernel implies injectivity. In a monoid there is no $y^{-1}$, and a homomorphism with kernel `⊥` can fail to be injective. Exercise 3 gives an example. The kernels of the projections and of the inclusions of a product are computed by `MonoidHom.mker_fst`, `MonoidHom.mker_snd`, `MonoidHom.mker_inl` and `MonoidHom.mker_inr`.

#### Restrictions and inclusions

Several maps change the domain or the codomain of $f$. The map `MonoidHom.domRestrict` restricts $f$ to a submonoid of the domain, and `MonoidHom.restrict` restricts it to a map between submonoids $M' \le M$ and $N' \le N$ when $f$ maps $M'$ into $N'$. The map `MonoidHom.codRestrict` views $f$ as a map into a submonoid that contains all its values, and `MonoidHom.mrangeRestrict` corestricts $f$ to its range. The last map is surjective, by `MonoidHom.mrangeRestrict_surjective`. For an inclusion $S \le T$, `Submonoid.inclusion` is the injective homomorphism from $S$ to $T$. An injective homomorphism is an isomorphism onto the image of each submonoid, by `Submonoid.equivMapOfInjective`, and a homomorphism with a left inverse is an isomorphism onto its range, by `MulEquiv.ofLeftInverse'`. The top submonoid is isomorphic to $M$, by `Submonoid.topEquiv`.

The lemma `Submonoid.surjOn_iff_le_map` translates the set-level statement "$f$ maps $H$ onto $K$" into the lattice statement $K \le f(H)$. A submonoid is `⊥` or has an element other than $1$, by `Submonoid.bot_or_exists_ne_one`, and it is nontrivial as a monoid exactly when it has such an element, by `Submonoid.nontrivial_iff_exists_ne_one`.

#### Products

For $S \le M$ and $T \le N$, the product `Submonoid.prod S T` has the carrier $S \times T$, by `Submonoid.coe_prod`. Its subtype is isomorphic to the product of the subtypes, by `Submonoid.prodEquiv`. The product decomposes in the lattice as a supremum, `Submonoid.prod_bot_sup_bot_prod`:

$$(S \times \{1\}) \sqcup (\{1\} \times T) = S \times T.$$

Proof sketch: the left side is in the right side, because both terms are. Conversely, $(s, t) = (s, 1)(1, t)$, and the two factors lie in the two terms. The ranges of the two inclusions `MonoidHom.inl` and `MonoidHom.inr` are $M \times \{1\}$ and $\{1\} \times N$, by `Submonoid.mrange_inl` and `Submonoid.mrange_inr`, and their supremum is `⊤` by `Submonoid.mrange_inl_sup_mrange_inr`. A product with `⊤` is a preimage under a projection, by `Submonoid.prod_top` and `Submonoid.top_prod`. The image of $S$ under `MonoidHom.inl` is $S \times \{1\}$, by `Submonoid.map_inl`.

For a family of monoids $M_i$, a set $I$ of indices and submonoids $S_i \le M_i$, the submonoid `Submonoid.pi I S` of $\prod_i M_i$ consists of the functions $p$ with $p_i \in S_i$ for $i \in I$, by `Submonoid.mem_pi`. Indices outside $I$ have no condition, so `Submonoid.pi_empty` gives `⊤`. The lemma `Submonoid.mulSingle_mem_pi` places the function `Pi.mulSingle i x` in the product submonoid when $x \in S_i$.

#### Units of a submonoid

The module `Mathlib.Algebra.Group.Submonoid.Units` defines `Submonoid.units S`, a subgroup of $M^\times$. Its members are given by `Submonoid.mem_units_iff`:

$$u \in S^\times \iff u \in S \text{ and } u^{-1} \in S.$$

It is a subgroup: $1$ and $1^{-1} = 1$ lie in $S$, the condition is symmetric in $u$ and $u^{-1}$, and $(u v)^{-1} = v^{-1} u^{-1}$ lies in $S$ when $u^{-1}$ and $v^{-1}$ do. The subgroup $S^\times$ is isomorphic to the unit group of the monoid $S$, by `Submonoid.unitsEquivUnitsType`. The condition $u^{-1} \in S$ is needed: a unit of $M$ that lies in $S$ need not be a unit of $S$.

In the other direction, `Subgroup.ofUnits H` is the submonoid of the values of the members of a subgroup $H \le M^\times$. Its subtype is isomorphic to $H$, by `Subgroup.ofUnitsEquivType`. The two constructions satisfy `Subgroup.units_ofUnits_eq`, $(\operatorname{ofUnits} H)^\times = H$, and `Submonoid.ofUnits_units_le`, $\operatorname{ofUnits}(S^\times) \le S$. They form the Galois connection `ofUnits_le_iff_le_units`:

$$\operatorname{ofUnits} H \le S \iff H \le S^\times.$$

Proof sketch: if the values of $H$ lie in $S$, then for $u \in H$ both $u$ and $u^{-1}$ have values in $S$, since $u^{-1} \in H$. So $u \in S^\times$. The other direction uses `Submonoid.ofUnits_units_le`. Together with `Subgroup.units_ofUnits_eq`, this is the Galois coinsertion `ofUnits_units_gci`. So `Subgroup.ofUnits` is injective (`Subgroup.ofUnits_injective`) and `Submonoid.units` is surjective (`Submonoid.units_surjective`). The lattice operations commute with the constructions where the Galois connection allows: `Submonoid.units_inf` and `Submonoid.units_iInf` for meets, `Subgroup.ofUnits_iSup` for suprema. The submonoid of all the units of $M$ is `IsUnit.submonoid M`, and `Submonoid.unitsTypeEquivIsUnitSubmonoid` identifies it with $M^\times$.

#### Common errors

1. A trivial kernel does not make a monoid homomorphism injective. The lemma `MonoidHom.ker_eq_bot_iff` of the subgroup layer needs groups. For monoids, prove injectivity directly, or use the congruence kernel of Chapter 5.
2. The range and the kernel of monoid homomorphisms are `MonoidHom.mrange` and `MonoidHom.mker`, with the letter m. The names `MonoidHom.range` and `MonoidHom.ker` give subgroups and need groups. In a group both exist, and `MonoidHom.mrange f` and `MonoidHom.range f` have the same carrier but different types.
3. An element $u \in M^\times$ with value in $S$ is not always in `Submonoid.units S`. The inverse must be in $S$ too. Use `Submonoid.mem_units_of_val_mem_inv_val_mem` with both facts.

### Exercises

1. (A) Prove `Submonoid.map_le_iff_le_comap` from `Submonoid.mem_map` and `Submonoid.mem_comap`.
2. (A) Let $f : M \to N$ be surjective. Prove that `Submonoid.map f (Submonoid.comap f T) = T` for every $T$, with `Submonoid.map_comap_eq` and `MonoidHom.mrange_eq_top`.
3. (A) Let $Z = \{0, 1\}$ with the usual multiplication. Show that $f : (\mathbb{N}, +) \to Z$ with $f(0) = 1$ and $f(n) = 0$ for $n \ge 1$ is a monoid homomorphism from `Multiplicative ℕ` to $Z$ with kernel `⊥`, and that $f$ is not injective.
4. (A) Let $S$ be the multiplicative submonoid of $\mathbb{Z}$ of the elements $n \ge 0$. Compute `Submonoid.units S`. Show that here each unit of $\mathbb{Z}$ that lies in $S$ has its inverse in $S$.
5. (B) Let $S$ be the submonoid of the monoid $(\mathbb{Q}, \cdot)$ generated by $2$. Show that $2$ is a unit of $\mathbb{Q}$ that lies in $S$ but that $2$ is not in `Submonoid.units S`.
6. (C) Prove `Subgroup.units_ofUnits_eq` and `Submonoid.ofUnits_units_le`, and deduce `ofUnits_le_iff_le_units`. Then show that `Submonoid.units` is surjective but not injective, with the additive monoid $\mathbb{N}$, whose only unit is $0$.

### Reference

<?reference?>
