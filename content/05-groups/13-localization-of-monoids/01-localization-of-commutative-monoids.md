---
title: Localization of commutative monoids
kind: api
modules:
  - Mathlib.GroupTheory.MonoidLocalization.Basic
  - Mathlib.GroupTheory.MonoidLocalization.Maps
  - Mathlib.GroupTheory.MonoidLocalization.Lemmas
  - Mathlib.GroupTheory.MonoidLocalization.Cardinality
  - Mathlib.GroupTheory.MonoidLocalization.Finite
explains:
  E2: [Submonoid.isLocalizationMap_iff, Submonoid.LocalizationMap.eq, Submonoid.LocalizationMap.injective_iff, Submonoid.LocalizationMap.epic_of_localizationMap, Submonoid.LocalizationMap.lift, Submonoid.LocalizationMap.lift_unique, Submonoid.LocalizationMap.mulEquivOfLocalizations, Localization.fg]
  E1: auto
families: []
requires: [V01, V05.C01, V05.C03, V05.C04, V05.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Localization of commutative monoids

### Overview

Let $M$ be a commutative monoid and let $S$ be a submonoid of $M$. The localization of $M$ at $S$ is the commutative monoid $S^{-1}M$ of formal fractions $x/s$ with $x \in M$ and $s \in S$. Two fractions $a/b$ and $c/d$ are equal when $u d a = u b c$ for some $u \in S$. The factor $u$ is necessary when $M$ is not cancellative: without it the relation is not transitive. The map $x \mapsto x/1$ sends each element of $S$ to a unit, and it is the universal monoid homomorphism with this property. The construction gives the rational numbers from $(\mathbb{Z}, \cdot)$ at the nonzero integers, the group $\mathbb{Z}$ from $(\mathbb{N}, +)$, and the monoid part of each localization of a commutative ring.

The library treats the localization in two layers. The first layer is a characterization: a structure `Submonoid.LocalizationMap S N` holds a homomorphism $M \to N$ with the three properties that make $N$ "a" localization of $M$ at $S$. Most theorems are stated for such a map, so they apply to each model of the localization. The second layer is one concrete model, the type `Localization S`, with its canonical localization map `Localization.monoidOf S`. The library also has the additive versions `AddSubmonoid.LocalizationMap` and `AddLocalization`.

The section uses submonoids from Chapter 3, finitely generated monoids from Chapter 4 and congruences from Chapter 5. The next section of this chapter treats special localizations, localizations of monoids with zero, the Grothendieck group and the Ore localization of a noncommutative monoid.

### The library around it

#### Localization maps

A function $f : M \to N$ to a commutative monoid is a localization map at $S$ when three conditions hold.

1. Each $f(y)$ with $y \in S$ is a unit of $N$.
2. Each $z \in N$ has the form $z f(y) = f(x)$ for some $x \in M$ and $y \in S$.
3. If $f(x) = f(y)$, then $c x = c y$ for some $c \in S$.

The predicate is `Submonoid.IsLocalizationMap S f`, and `Submonoid.isLocalizationMap_iff` states it as this conjunction. The bundled form `Submonoid.LocalizationMap S N` extends a multiplicative map `M →ₙ* N` with a proof of the predicate (the field `Submonoid.LocalizationMap.isLocalizationMap`). It coerces to a function, and `Submonoid.LocalizationMap.toMonoidHom` gives the monoid homomorphism. The three conditions are available as `Submonoid.LocalizationMap.map_units`, `Submonoid.LocalizationMap.surj` and `Submonoid.LocalizationMap.exists_of_eq`. The constructor `MonoidHom.toLocalizationMap` makes a localization map from a monoid homomorphism and the three conditions. Two localization maps are equal when they agree on each element (`Submonoid.LocalizationMap.ext`).

In a commutative group, the identity is a localization map at each submonoid (`Submonoid.isLocalizationMap_id`). More generally, `Submonoid.isLocalizationMap_of_group` says that an injective map $f : M \to G$ to a commutative group is a localization map at $S$ when each element of $G$ is a quotient $f(x)/f(y)$ with $y \in S$.

#### Fractions in the target

For a localization map $f$, the element `f.mk' x y` is $f(x) f(y)^{-1}$, the image of the fraction $x/y$. The defining equation is `Submonoid.LocalizationMap.mk'_spec`: $f.\mathrm{mk'}(x, y) \cdot f(y) = f(x)$. Each element of $N$ has this form (`Submonoid.LocalizationMap.mk'_surjective`). The function `Submonoid.LocalizationMap.sec` chooses a pair $(x, y)$ for each $z \in N$, with `Submonoid.LocalizationMap.sec_spec` and `Submonoid.LocalizationMap.mk'_sec`. The arithmetic of fractions is a family of rewrite lemmas.

| Lean name | Statement |
|---|---|
| `Submonoid.LocalizationMap.mk'_mul` | $\mathrm{mk'}(x_1 x_2, y_1 y_2) = \mathrm{mk'}(x_1, y_1)\,\mathrm{mk'}(x_2, y_2)$ |
| `Submonoid.LocalizationMap.mk'_one` | $\mathrm{mk'}(x, 1) = f(x)$ |
| `Submonoid.LocalizationMap.mk'_self'` | $\mathrm{mk'}(y, y) = 1$ |
| `Submonoid.LocalizationMap.mk'_cancel` | $\mathrm{mk'}(a c, b c) = \mathrm{mk'}(a, b)$ |
| `Submonoid.LocalizationMap.mk'_eq_iff_eq` | $\mathrm{mk'}(x_1, y_1) = \mathrm{mk'}(x_2, y_2) \iff f(y_2 x_1) = f(y_1 x_2)$ |
| `Submonoid.LocalizationMap.mk'_eq_iff_eq_mul` | $\mathrm{mk'}(x, y) = z \iff f(x) = z f(y)$ |

The equality of two fractions in terms of $M$ alone is the central lemma.

**Proposition (`Submonoid.LocalizationMap.eq`).** $f.\mathrm{mk'}(a_1, a_2) = f.\mathrm{mk'}(b_1, b_2)$ if and only if $c\,(b_2 a_1) = c\,(a_2 b_1)$ for some $c \in S$.

*Proof.* By `Submonoid.LocalizationMap.mk'_eq_iff_eq`, the left side is $f(b_2 a_1) = f(a_2 b_1)$. Condition 3 gives the factor $c$. Conversely, $c\,(b_2 a_1) = c\,(a_2 b_1)$ gives $f(c) f(b_2 a_1) = f(c) f(a_2 b_1)$, and $f(c)$ is a unit by condition 1. $\square$

**Proposition (`Submonoid.LocalizationMap.injective_iff`).** A localization map $f$ is injective if and only if each element of $S$ is regular, that is, cancellable.

*Proof.* Let each element of $S$ be regular. If $f(x) = f(y)$, then $c x = c y$ for some $c \in S$ by condition 3, so $x = y$. Conversely, let $f$ be injective and let $c \in S$ with $c x = c y$. Then $f(c) f(x) = f(c) f(y)$. Since $f(c)$ is a unit, $f(x) = f(y)$, so $x = y$. Multiplication is commutative, so this gives both cancellations. $\square$

The case $S = M$ is `Submonoid.LocalizationMap.top_injective_iff`: the localization map at the top submonoid is injective exactly when $M$ is cancellative (`IsCancelMul`). A localization map also preserves regular elements (`Submonoid.LocalizationMap.map_isRegular`), and the target of a localization of a cancellative monoid is cancellative (`Submonoid.LocalizationMap.isCancelMul`).

**Proposition (`Submonoid.LocalizationMap.epic_of_localizationMap`).** A localization map is an epimorphism: two monoid homomorphisms $j, k : N \to P$ with $j \circ f = k \circ f$ are equal.

*Proof.* Let $z \in N$ and write $z f(y) = f(x)$ with $y \in S$. Then $j(z)\,j(f(y)) = j(f(x)) = k(f(x)) = k(z)\,k(f(y))$. The element $f(y)$ is a unit of $N$, so $j(f(y)) = k(f(y))$ is a unit of $P$. Cancel it to get $j(z) = k(z)$. $\square$

A localization map need not be surjective, so this is a real difference between epimorphisms of monoids and surjections. The map $(\mathbb{N}, +) \to (\mathbb{Z}, +)$ is an example.

#### The type `Localization S`

The concrete localization is the type `Localization S`. Its elements are the classes `Localization.mk x y` of pairs $(x, y) \in M \times S$. The relation on pairs is the congruence `Localization.r S`, the smallest congruence on $M \times S$ that relates $1$ to $(y, y)$ for each $y \in S$. The explicit form is `Localization.r' S`: $(a, b) \sim (c, d)$ when $u\,(d a) = u\,(b c)$ for some $u \in S$. The lemma `Localization.r_eq_r'` says that the two congruences are equal, and `Localization.r_iff_exists` states the explicit form directly. The type is an abbreviation of the Ore localization `OreLocalization S M` of the next section, and `Localization.r_iff_oreEqv_r` relates the two relations.

The class map respects the operations: `Localization.mk_mul`, `Localization.mk_one`, `Localization.mk_pow` and `Localization.mk_prod`. The lemma `Localization.mk_self` says that `Localization.mk y y` is $1$. Equality of classes is `Localization.mk_eq_mk_iff`. In a cancellative monoid the factor $u$ goes away, and `Localization.mk_eq_mk_iff'` reads $\mathrm{mk}(a_1, a_2) = \mathrm{mk}(b_1, b_2) \iff b_2 a_1 = a_2 b_1$. Proofs about elements of `Localization S` start with `Localization.induction_on`, `Localization.induction_on₂` or `Localization.induction_on₃`. Functions out of the type come from `Localization.liftOn` and `Localization.liftOn₂`, with a proof that the function respects the relation, and dependent ones from `Localization.rec`.

The canonical localization map is `Localization.monoidOf S`. The lemma `Localization.mk_eq_monoidOf_mk'` identifies `Localization.mk` with `(Localization.monoidOf S).mk'`, and `Localization.mk_one_eq_monoidOf_mk` identifies `Localization.mk x 1` with the image of $x$. These two lemmas move a goal from the concrete type to the general API of localization maps. The map `Localization.mkHom` is the surjective homomorphism $M \times S \to$ `Localization S`.

#### The universal property

Let $f$ be a localization map at $S$ with target $N$, and let $g : M \to P$ be a monoid homomorphism that sends each element of $S$ to a unit. Then `f.lift hg : N →* P` is the unique homomorphism $h$ with $h \circ f = g$. On fractions it is $h(f.\mathrm{mk'}(x, y)) = g(x) g(y)^{-1}$ (`Submonoid.LocalizationMap.lift_mk'`), and on the image of $M$ it is `Submonoid.LocalizationMap.lift_eq`. The uniqueness is `Submonoid.LocalizationMap.lift_unique`, and it follows from the epimorphism property above. The lemmas `Submonoid.LocalizationMap.lift_injective_iff` and `Submonoid.LocalizationMap.lift_surjective_iff` describe when the lift is injective or surjective. The characterization `Submonoid.LocalizationMap.lift_spec` says $h(z) = v$ if and only if $g(x) = g(y)\,v$, where $(x, y)$ is the pair `f.sec z`.

The universal property makes the localization unique up to a unique isomorphism. For two localization maps $f : M \to N$ and $k : M \to P$ at the same $S$, `f.mulEquivOfLocalizations k` is an isomorphism $N \simeq P$ that commutes with the maps. Its function is a lift (`Submonoid.LocalizationMap.mulEquivOfLocalizations_apply`). The special case `Localization.mulEquivOfQuotient f` is the isomorphism from `Localization S` to $N$. In the other direction, `Submonoid.LocalizationMap.ofMulEquivOfLocalizations` composes a localization map with an isomorphism of targets, and `Submonoid.LocalizationMap.ofMulEquivOfDom` precomposes it with an isomorphism of domains.

Localization is a functor. Let $g : M \to P$ send $S$ into a submonoid $T$ of $P$, and let $k$ be a localization map at $T$ with target $Q$. Then `f.map hy k : N →* Q` sends $f.\mathrm{mk'}(x, y)$ to $k.\mathrm{mk'}(g(x), g(y))$ (`Submonoid.LocalizationMap.map_mk'`, `Submonoid.LocalizationMap.map_eq`). The lemmas `Submonoid.LocalizationMap.map_id` and `Submonoid.LocalizationMap.map_comp_map` are the functor laws. An injective $g$ gives an injective map of localizations at $S$ and at the image of $S$ (`Submonoid.LocalizationMap.map_injective_of_injective`), and the same holds for surjective maps (`Submonoid.LocalizationMap.map_surjective_of_surjective`). The isomorphism `Submonoid.LocalizationMap.mulEquivOfMulEquiv` is the map for an isomorphism $M \simeq P$ that sends $S$ onto $T$.

#### Size, finiteness and products

Three small modules give global facts. `Localization.cardinalMk_le` says that `Localization S` has at most the cardinality of $M$. The bound is not the trivial bound from the surjection $M \times S \to S^{-1}M$, because $M \times S$ can have more elements than $M$ when $M$ is finite. The general Ore version is in the next section.

**Proposition (`Localization.fg`).** If $M$ is a finitely generated monoid (`Monoid.FG`) and $S$ is a finitely generated submonoid (`Submonoid.FG`), then `Localization S` is finitely generated.

*Proof.* Let $x_1, \dots, x_m$ generate $M$ and let $s_1, \dots, s_n$ generate $S$. Each element of $S^{-1}M$ is $(x/1)(1/s)$, where $x/1$ is a product of the $x_i/1$ and $1/s$ is a product of the $1/s_j$. So the $m + n$ elements $x_i/1$ and $1/s_j$ generate the localization. $\square$

The instance `Algebra.GrothendieckGroup.instFG` is the case $S = M$ for the Grothendieck group. The module `Mathlib.GroupTheory.MonoidLocalization.Lemmas` has two facts for families. `Submonoid.IsLocalizationMap.pi` says that a product of localization maps is a localization map at the product submonoid. `Submonoid.IsLocalizationMap.surj_pi_of_finite` gives a common denominator: for a finite family $(n_i)$ in $N$ there is one $s \in S$ and elements $x_i$ with $n_i f(s) = f(x_i)$ for each $i$.

#### Common errors

1. `Localization S` is an abbreviation of `OreLocalization S M`. A goal can therefore show the Ore notation `x /ₒ s` and lemmas from the namespace `OreLocalization`. Rewrite with `Localization.mk_eq_monoidOf_mk'` to work with the API of `Localization.monoidOf S` instead.
2. The equality of fractions needs the factor from $S$. In a monoid that is not cancellative, `Localization.mk a b = Localization.mk c d` does not imply $d a = b c$. Use `Submonoid.LocalizationMap.eq` or `Localization.mk_eq_mk_iff`, and keep `Localization.mk_eq_mk_iff'` for an `IsCancelMul` monoid.
3. `Submonoid.LocalizationMap.lift` takes the proof that $g$ sends $S$ to units as an explicit argument, and its definition uses the choice `Submonoid.LocalizationMap.sec`. Compute with `Submonoid.LocalizationMap.lift_eq` and `Submonoid.LocalizationMap.lift_mk'`, not by unfolding the definition.

### Exercises

1. (A) Show that the localization map of $M$ at the trivial submonoid $\bot$ is an isomorphism, and deduce that `Localization ⊥` is isomorphic to $M$.
2. (A) Let $G$ be a commutative group and $S$ a submonoid. Use `Submonoid.isLocalizationMap_id` and `Localization.mulEquivOfQuotient` to show that `Localization S` is isomorphic to $G$.
3. (A) In $(\mathbb{N}, \cdot)$, let $S$ be the powers of $2$. Describe the elements of the localization as fractions and say when $a/2^i = b/2^j$.
4. (B) Let $S$ contain an element $z$ with $z x = z$ for all $x \in M$. Show that the localization at $S$ is the trivial monoid. Hint: compare $f(x)$ and $f(1)$ with condition 3.
5. (B) Let $f : M \to N$ be a localization map at $S$ and let $j : N \to P$ be a monoid homomorphism. Show that $j = f.\mathrm{lift}(j \circ f)$, and find the lemma of the library that says this.
6. (C) Show that the relation $(a, b) \sim (c, d) \iff d a = b c$ on $M \times S$ is transitive when each element of $S$ is regular. Then find a commutative monoid $M$ and a submonoid $S$ for which this relation is not transitive, so that the factor $u$ in `Localization.r'` is necessary.

### Reference

<?reference?>
