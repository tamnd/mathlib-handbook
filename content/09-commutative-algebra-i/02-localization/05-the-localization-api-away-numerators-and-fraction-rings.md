---
title: "The localization API: away, numerators and fraction rings"
kind: api
modules:
  - Mathlib.RingTheory.Localization.Basic
  - Mathlib.RingTheory.Localization.Away.Basic
  - Mathlib.RingTheory.Localization.Away.Lemmas
  - Mathlib.RingTheory.Localization.FractionRing
  - Mathlib.RingTheory.Localization.Integer
  - Mathlib.RingTheory.Localization.NumDen
  - Mathlib.RingTheory.Localization.InvSubmonoid
  - Mathlib.RingTheory.Localization.AsSubring
  - Mathlib.RingTheory.Localization.Rat
  - Mathlib.RingTheory.Localization.Saturation
  - Mathlib.RingTheory.Localization.Cardinality
  - Mathlib.RingTheory.Localization.Pi
explains:
  E2: [IsLocalization.atUnits, "IsFractionRing.mk'_eq_div", IsFractionRing.lift, IsFractionRing.num_den_reduced, IsFractionRing.isUnit_den_iff, IsLocalization.exist_integer_multiples_of_finset, IsLocalization.of_saturation_eq, IsLocalization.cardinalMk_le, Localization.algebraMap_injective_of_span_eq_top]
  E1: auto
families: []
requires: [V06.C02, V09.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The localization API: away, numerators and fraction rings

### Overview

Section 1 gives the characteristic predicate `IsLocalization M S` and the universal property of $M^{-1} R$. The modules of this section build on that predicate. They hold the localization $R_f$ at the powers of one element, the field of fractions of a domain, the elements of $M^{-1} R$ that come from $R$, the reduced fractions over a unique factorization domain, and some general facts: the saturation of $M$, the size of $M^{-1} R$, and the localization of a finite product of rings.

Most results are stated for an arbitrary algebra `S` with `[IsLocalization M S]`, and not for the concrete type `Localization M`. So a result applies to each model of the localization: to `Localization M`, to `FractionRing A`, to `ℚ` over `ℤ`, and to every other ring that satisfies the predicate. The reader needs these modules each time a proof clears denominators, passes to $R_f$, or works in the field of fractions of a domain.

### The library around it

#### Basic constructions

The module `Mathlib.RingTheory.Localization.Basic` holds the consequences of the universal property that Section 1 does not state. When every element of $M$ is already a unit of $R$, the localization map is an isomorphism. This is `IsLocalization.atUnits`, an `R ≃ₐ[R] S` from the hypothesis `M ≤ IsUnit.submonoid R`. The proof is short: by the universal property, the identity of $R$ extends to a map $S \to R$, and the two composites are the identity because they agree on $R$. A special case is `IsLocalization.atOne`, for `IsLocalization.Away 1 S`. For a field $K$ and a submonoid $M$ with $0 \notin M$, `Field.localization_map_bijective` says that $K \to M^{-1} K$ is bijective.

The universal property also has an algebra form. For an $R$-algebra $A$ and a localization $L$ of $A$, `IsLocalization.liftAlgHom` gives an $R$-algebra map out of $L$, and `IsLocalization.algHom_ext` says that two $R$-algebra maps out of $L$ that agree on $A$ are equal. The isomorphism `Localization.algEquiv` compares `Localization M` with any other model `S`. If $R$ is finite, then `IsLocalization.finite` says that $S$ is finite, and the bound in the cardinality module below makes this precise.

#### Localization away from an element

For $x \in R$, the predicate `IsLocalization.Away x S` of Section 1 says that `S` is the localization at the powers of $x$. The module `Mathlib.RingTheory.Localization.Away.Basic` gives its functorial API. A ring map $f : R \to P$ induces `IsLocalization.Away.map` from $R_x$ to $P_{f(x)}$, and on the concrete types this is `Localization.awayMap`. The integer powers of $x$ in $R_x$ are `selfZPow x B n`, with `selfZPow_add`, `selfZPow_natCast` and `selfZPow_neg_natCast` as the rules for sums and signs. If $r$ divides $x$, then `IsLocalization.Away.isUnit_of_dvd` says that $r$ is a unit in $R_x$.

Some results change the element. The predicate depends only on the associate class of the element: this is `IsLocalization.Away.of_associated`. A localization away from $y$ of a localization away from $x$ is a localization away from $x y$, as `IsLocalization.Away.mul` and `IsLocalization.Away.mul_of_associated` state. An idempotent $e$ gives a localization that is also a quotient: `IsLocalization.Away.quotient_of_isIdempotentElem` says that $R/(1 - e)$ is a localization away from $e$, since $e$ maps to $1$ there and $e^n (1 - e) = 0$.

The module also holds the first gluing results. Let $s \subseteq R$ generate the unit ideal. Then the product map $R \to \prod_{a \in s} R_a$ is injective, by `Localization.algebraMap_injective_of_span_eq_top`. The proof: if $r$ maps to $0$ in each $R_a$, then $a^{n_a} r = 0$ for some $n_a$. The powers $a^{n_a}$ also generate the unit ideal, so $1 = \sum c_a a^{n_a}$ and $r = \sum c_a a^{n_a} r = 0$. The existence part, `Localization.existsUnique_algebraMap_eq_of_span_eq_top`, glues a compatible family $(f_a)$ to a unique $r \in R$. The module `Mathlib.RingTheory.Localization.Away.Lemmas` adds `IsLocalization.Away.span_range_mulNumerator_eq_top`, which builds a generating set of the unit ideal of $R$ from generating sets of the unit ideals of the $R_t$, and `Ideal.le_of_map_algebraMap_le`, which compares two ideals through their images in $R_x$.

#### Fraction rings

The module `Mathlib.RingTheory.Localization.FractionRing` treats the localization at `nonZeroDivisors R`. The predicate `IsFractionRing R K` is an abbreviation for `IsLocalization (nonZeroDivisors R) K`, and `FractionRing R` is the concrete model. For a domain $A$, the instance `FractionRing.field` makes `FractionRing A` a field, and `IsFractionRing.toField` gives the field structure on any model. The map $A \to K$ is injective by `IsFractionRing.injective`.

In a field of fractions, a formal fraction is a quotient: `IsFractionRing.mk'_eq_div` says that `mk' K r s = algebraMap A K r / algebraMap A K s`. The proof multiplies both sides by the image of $s$, which is a nonzero element of the field $K$. So every element of $K$ is $x / y$ with $y$ a nonzero divisor, and this is `IsFractionRing.div_surjective`. The universal property takes the classical form: an injective ring map $g : A \to L$ into a field extends to `IsFractionRing.lift hg : K →+* L`, with `IsFractionRing.lift_algebraMap` as its computation rule. The extension exists because $g$ sends nonzero divisors of $A$ to nonzero elements of $L$, and these are units. For an injective $j : A \to B$ between domains, `IsFractionRing.map` is the induced map of fraction fields. Two models are isomorphic by `IsFractionRing.algEquiv`.

Some results characterize fraction rings. A field is its own fraction ring, and more generally `IsFractionRing.self_iff_nonZeroDivisors_le_isUnit` says that `IsFractionRing R R` holds exactly when each nonzero divisor of $R$ is a unit. For a domain, `IsFractionRing.surjective_iff_isField` says that $A \to K$ is surjective exactly when $A$ is a field. The criterion `IsFractionRing.of_field` proves `IsFractionRing R K` for a field $K$ with a faithful action of $R$ in which every element is a quotient of images of $R$. The instance `Rat.isFractionRing` makes $\mathbb{Q}$ the fraction field of $\mathbb{Z}$, and `NNRat.isFractionRing` does the same for $\mathbb{Q}_{\geq 0}$ over $\mathbb{N}$.

#### Integer elements and common denominators

The module `Mathlib.RingTheory.Localization.Integer` names the elements of $S$ that come from $R$. The predicate `IsLocalization.IsInteger R a` says that $a$ is in the range of `algebraMap R S`. It is closed under sums and products: `IsLocalization.isInteger_add` and `IsLocalization.isInteger_mul`. Each element of $S$ becomes an integer after multiplication by an element of $M$, by `IsLocalization.exists_integer_multiple`.

The finite form is the step that clears denominators. For a finite set $s \subseteq S$, `IsLocalization.exist_integer_multiples_of_finset` gives one $b \in M$ with $b a$ an integer for each $a \in s$. Proof: write each $a$ as $r_a / m_a$ and take $b = \prod_a m_a$. Then $b a = r_a \prod_{a' \neq a} m_{a'}$. The chosen $b$ is `IsLocalization.commonDenomOfFinset`, and `IsLocalization.integerMultiple` gives the numerators in $R$.

#### Reduced fractions over a unique factorization domain

The module `Mathlib.RingTheory.Localization.NumDen` takes a domain $A$ with `[UniqueFactorizationMonoid A]` and a fraction field $K$. Each $x \in K$ has a reduced form $x = a / b$ with $a$ and $b$ coprime. The existence statement is `IsFractionRing.exists_reduced_fraction`. The library then chooses a numerator `IsFractionRing.num A x : A` and a denominator `IsFractionRing.den A x`, an element of `nonZeroDivisors A`. The identity `IsFractionRing.mk'_num_den` says that $x = \operatorname{num}(x) / \operatorname{den}(x)$, and `IsFractionRing.num_den_reduced` says that the two parts satisfy `IsRelPrime`. The existence proof divides a fraction $r / s$ by a greatest common divisor of $r$ and $s$. Such a divisor exists in a unique factorization domain.

The choice is unique up to a unit, by `IsFractionRing.num_den_unique`. A consequence is `IsFractionRing.isUnit_den_iff`: the denominator is a unit exactly when $x$ is an integer. One direction is clear. For the other, if $x = a$ with $a \in A$, then $\operatorname{num}(x) = a \operatorname{den}(x)$, so $\operatorname{den}(x)$ divides $\operatorname{num}(x)$. The two are coprime, so $\operatorname{den}(x)$ is a unit. The module `Mathlib.RingTheory.Localization.Rat` compares this choice with the fields of `ℚ`: `Rat.isFractionRingDen` says that the absolute value of `IsFractionRing.den ℤ q` is `Rat.den q`, and `Rat.isLocalizationIsInteger_iff` says that `IsInteger ℤ q` holds exactly when $q$ is the image of an integer.

#### The submonoid of inverses and subrings of the fraction field

The module `Mathlib.RingTheory.Localization.InvSubmonoid` takes the inverses of the images of $M$ as a submonoid `IsLocalization.invSubmonoid M S` of $S$, with the map `IsLocalization.toInvSubmonoid`. These inverses span $S$ as an $R$-module: `IsLocalization.span_invSubmonoid`. As a consequence, `IsLocalization.finiteType_of_monoid_fg` says that $S$ is of finite type over $R$ when $M$ is finitely generated as a monoid. The images of the generators and their inverses generate $S$ as an algebra.

The module `Mathlib.RingTheory.Localization.AsSubring` realizes $M^{-1} A$ inside the fraction field $K$ of $A$ when $M$ contains no zero divisor. The result is `Localization.subalgebra K M hM : Subalgebra A K`, and `Localization.subalgebra.ofField` gives the same subalgebra when $K$ is a field. The map `Localization.mapToFractionRing` is the injective map from a localization into $K$, and the instance `Localization.isFractionRing_range_mapToFractionRing` says that $K$ is again the fraction field of its range.

#### Saturation, cardinality and products

A localization does not see the difference between $M$ and its saturation, the set of $x$ that divide an element of $M$. The module `Mathlib.RingTheory.Localization.Saturation` states this. First, `IsLocalization.mem_saturation_iff_isUnit_algebraMap` says that $x$ is in the saturation of $M$ exactly when the image of $x$ in $S$ is a unit. So `IsLocalization.of_saturation_eq` says that a localization at $M$ is also a localization at $T$ when the saturations of $M$ and $T$ are equal. The units of $S$ that come from $R$ are the same in both cases, and the kernel condition holds because $t x = 0$ with $t \in T$ gives $s x = 0$ for a multiple $s = t u$ in $M$.

The module `Mathlib.RingTheory.Localization.Cardinality` bounds the size of a localization. In a common universe, `IsLocalization.cardinalMk_le` says that $\# S \leq \# R$. The proof: the map $R \times M \to S$, $(r, m) \mapsto r/m$, is surjective, and $\# (R \times M) = \# R$ when $R$ is infinite. For finite $R$, the map $R \to S$ is surjective: the image of $m \in M$ is a nonzero divisor in the finite image of $R$, so it is a unit there. When $M$ contains no zero divisor, the map $R \to S$ is injective, and `IsLocalization.cardinalMk` gives equality. The versions `FractionRing.cardinalMk` and `IsFractionRing.cardinalMk` state this for fraction rings.

The module `Mathlib.RingTheory.Localization.Pi` treats a finite product $\prod_i R_i$. A localization of the product at $M$ is the product of the localizations of the factors at the images of $M$: this is `IsLocalization.iff_map_piEvalRingHom`, for a finite index type. On the concrete types, for a submonoid $S$ of one factor $R_i$, `Localization.mapPiEvalRingHom S` maps the localization of the product at the preimage of $S$ to the localization of $R_i$ at $S$, and `Localization.mapPiEvalRingHom_bijective` says that this map is bijective.

#### Common errors

1. `IsFractionRing.toField` is an abbreviation, not an instance. For a general model `K` of the fraction field, write `[Field K]` in the hypotheses and use the predicate `IsFractionRing A K`. Only the concrete `FractionRing A` has the instance `FractionRing.field`.
2. `IsFractionRing.den A x` is an element of the subtype `nonZeroDivisors A`. Divisibility and unit statements need the coercion to `A`, as in `IsUnit (IsFractionRing.den A x : A)`. The pair of numerator and denominator is a choice, so a statement such as $\operatorname{num}(a/b) = a$ is true only up to a unit.
3. `IsLocalization.Away.map S Q f r` needs two instances: `[IsLocalization.Away r S]` and `[IsLocalization.Away (f r) Q]`. For the concrete types `Localization.Away` both exist, and `Localization.awayMap` is the simpler choice. For other models, add both instances to the hypotheses: the second one does not follow from the first.

### Exercises

1. (A) Use `IsFractionRing.mk'_eq_div` to show that each element of `FractionRing ℤ` is the quotient of two integers, and compare with `IsFractionRing.div_surjective`.
2. (A) Let $u$ be a unit of $R$. Prove that `Localization.Away u` is isomorphic to $R$, with `IsLocalization.atUnits` or with `IsLocalization.Away.of_associated` and `IsLocalization.atOne`.
3. (B) Let $f_1, \dots, f_n$ generate the unit ideal of $R$, and let $r \in R$ be nilpotent in each $R_{f_i}$. Prove that $r$ is nilpotent in $R$, by the method of proof of `Localization.algebraMap_injective_of_span_eq_top`.
4. (B) Let $A$ be a unique factorization domain with fraction field $K$, and let $x \in K$ satisfy $x^2 \in A$. Prove that $x \in A$, with `IsFractionRing.num_den_reduced` and `IsFractionRing.isUnit_den_iff`.
5. (B) Prove that $\mathbb{Z}[1/6]$, the localization of $\mathbb{Z}$ at the powers of $6$, is also the localization at the submonoid generated by $2$ and $3$, with `IsLocalization.of_saturation_eq`.
6. (C) Let $R$ be a countable ring and $M$ a submonoid. Prove that every localization of $R$ at $M$ is countable, from `IsLocalization.cardinalMk_le`, and give an example where the inequality is strict.

### Reference

<?reference?>
