---
title: Rational and birational maps
kind: theory
modules:
  - Mathlib.AlgebraicGeometry.Birational.Birational
  - Mathlib.AlgebraicGeometry.Birational.Composition
  - Mathlib.AlgebraicGeometry.Birational.Dominant
  - Mathlib.AlgebraicGeometry.Birational.RationalMap
  - Mathlib.AlgebraicGeometry.RationalMap
explains:
  E3: [AlgebraicGeometry.Scheme.PartialMap, AlgebraicGeometry.Scheme.PartialMap.equiv, AlgebraicGeometry.Scheme.PartialMap.equiv_iff_of_isSeparated, AlgebraicGeometry.Scheme.RationalMap, AlgebraicGeometry.Scheme.RationalMap.equivFunctionFieldOver, AlgebraicGeometry.Scheme.PartialMap.comp, AlgebraicGeometry.Scheme.RationalMap.comp, AlgebraicGeometry.Scheme.RationalMap.IsDominant, AlgebraicGeometry.Scheme.PartialIso, AlgebraicGeometry.Scheme.Birational, AlgebraicGeometry.Scheme.IsRationalOver]
  E2: [AlgebraicGeometry.Scheme.PartialMap.IsOver, AlgebraicGeometry.Scheme.PartialMap.restrict, AlgebraicGeometry.Scheme.PartialMap.compHom, AlgebraicGeometry.Scheme.Hom.toPartialMap, AlgebraicGeometry.Scheme.PartialMap.id, AlgebraicGeometry.Scheme.PartialMap.fromSpecStalkOfMem, AlgebraicGeometry.Scheme.PartialMap.ofFromSpecStalk, AlgebraicGeometry.Scheme.PartialMap.equivalence_rel, AlgebraicGeometry.Scheme.PartialMap.equiv_iff_of_isSeparated_of_le, AlgebraicGeometry.Scheme.Hom.toRationalMap, AlgebraicGeometry.Scheme.RationalMap.IsOver, AlgebraicGeometry.Scheme.RationalMap.representative, AlgebraicGeometry.Scheme.RationalMap.ofFunctionField, AlgebraicGeometry.Scheme.RationalMap.equivFunctionField, AlgebraicGeometry.Scheme.RationalMap.domain, AlgebraicGeometry.Scheme.RationalMap.dense_domain, AlgebraicGeometry.Scheme.RationalMap.toPartialMap, AlgebraicGeometry.Scheme.PartialMap.isDominant_toRationalMap_iff, AlgebraicGeometry.Scheme.PartialMap.isDominant_hom_iff_of_equiv, AlgebraicGeometry.Scheme.PartialMap.comp_equiv_of_equiv, AlgebraicGeometry.Scheme.PartialMap.comp_assoc, AlgebraicGeometry.Scheme.RationalMap.comp_assoc, AlgebraicGeometry.Scheme.RationalMap.id_comp, AlgebraicGeometry.Scheme.RationalMap.comp_id, AlgebraicGeometry.Scheme.RationalMap.isOver_comp, AlgebraicGeometry.Scheme.PartialIso.symm, AlgebraicGeometry.Scheme.PartialIso.trans, AlgebraicGeometry.Scheme.PartialIso.ofIso, AlgebraicGeometry.Scheme.Birational.trans, AlgebraicGeometry.Scheme.BirationalOver, AlgebraicGeometry.Scheme.Opens.birational_of_dense, AlgebraicGeometry.Scheme.Hom.birational]
  E1: auto
families: []
requires: [V09.C02, V13.C05, V28.C03, V28.C04, V28.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Rational and birational maps

### Overview

A rational map $X \dashrightarrow Y$ is a morphism that is only defined on a dense open subset of $X$, up to the choice of that subset. The map $x \mapsto 1/x$ on the affine line is the model: it is a morphism on $\mathbb{A}^1 \setminus \{0\}$ and has no value at $0$. Two schemes are birational when they have isomorphic dense opens. For integral schemes of finite type over a field, birational schemes have the same function field, and rational maps into $Y$ are points of $Y$ with values in the function field of $X$.

Mathlib defines partial maps as morphisms on dense opens, rational maps as their equivalence classes, and birational schemes through partial isomorphisms. This section proves that the equivalence is an equivalence relation, that on reduced schemes with separated targets equivalent partial maps agree on their common domain, that dominant rational maps compose, and that rational maps from an integral scheme correspond to morphisms from the spectrum of its function field.

### Definitions

**Definition (Partial map).** Let $X$ and $Y$ be schemes. A *partial map* $f$ from $X$ to $Y$ is a pair of a dense open $U = \operatorname{dom} f$ of $X$ and a morphism $f : U \to Y$. Over a base $S$, with structure maps $s_X$ and $s_Y$, the partial map is *over $S$* when $s_Y \circ f = s_X|_U$.

A morphism $X \to Y$ is a partial map with domain $X$. A partial map can be *restricted* to a smaller dense open $V \subseteq U$.

**Definition (Equivalence of partial maps).** Two partial maps $f$ and $g$ from $X$ to $Y$ are *equivalent* when there is a dense open $W \subseteq \operatorname{dom} f \cap \operatorname{dom} g$ with $f|_W = g|_W$.

**Definition (Rational map).** A *rational map* $X \dashrightarrow Y$ is an equivalence class of partial maps from $X$ to $Y$. Its *domain* is the union of the domains of all partial maps in the class.

**Definition (Dominant rational map).** A rational map is *dominant* when one, and so each, of its representatives $f : U \to Y$ has dense image.

**Definition (Partial isomorphism).** A *partial isomorphism* from $X$ to $Y$ is a pair of dense opens $U \subseteq X$ and $V \subseteq Y$ with an isomorphism $U \cong V$. The schemes $X$ and $Y$ are *birational* when a partial isomorphism exists. Over $S$ they are *birational over $S$* when the isomorphism commutes with the structure maps.

**Definition (Rational scheme).** An $S$-scheme $X$ is *rational over $S$* when it is birational over $S$ to the affine space $\mathbb{A}^n_S$ for some index set $n$.

In Mathlib the index set $n$ need not be finite.

### Theorems and proofs

**Lemma (Dense opens).** In a topological space the intersection of an open dense set $U$ and a dense set $V$ is dense.

*Proof.* Let $W$ be a nonempty open set. Then $W \cap U$ is open and nonempty, because $U$ is dense. Since $V$ is dense, $(W \cap U) \cap V$ is nonempty. So $U \cap V$ meets each nonempty open set. $\square$

**Proposition (Equivalence relation).** Equivalence of partial maps is an equivalence relation.

*Proof.* Reflexivity uses $W = \operatorname{dom} f$, and symmetry holds because the definition is symmetric in $f$ and $g$. Let $f \sim g$ on a dense open $W_1$ and $g \sim h$ on a dense open $W_2$. By the lemma $W = W_1 \cap W_2$ is a dense open. On $W$ one has $f|_W = g|_W = h|_W$, and $W$ lies in $\operatorname{dom} f \cap \operatorname{dom} h$. $\square$

**Theorem (Uniqueness on reduced schemes).** Let $X$ be reduced and $Y$ separated over $S$. Let $f$ and $g$ be partial maps over $S$ from $X$ to $Y$. Then $f$ and $g$ are equivalent if and only if they agree on $\operatorname{dom} f \cap \operatorname{dom} g$.

*Proof.* If they agree on the intersection, take $W = \operatorname{dom} f \cap \operatorname{dom} g$, which is a dense open by the lemma.

Conversely let $f$ and $g$ agree on a dense open $W$, and put $U = \operatorname{dom} f \cap \operatorname{dom} g$. Step 1. The pair $(f, g)$ gives $U \to Y \times_S Y$. The diagonal $Y \to Y \times_S Y$ is a closed immersion, because $Y$ is separated over $S$. Its pullback along $(f, g)$ is a closed subscheme $Z \subseteq U$, and a morphism $T \to U$ factors through $Z$ exactly when its composites with $f$ and $g$ agree.

Step 2. The inclusion $W \to U$ factors through $Z$. So the closed set $|Z|$ contains $W$, and so it contains the closure of $W$ in $U$, which is $U$.

Step 3. $U$ is reduced, because it is open in $X$. A closed subscheme of a reduced scheme with the whole space as support is the whole scheme, since its ideal sheaf consists of functions that vanish at each point, so of nilpotent functions. So $Z = U$, and $f|_U = g|_U$. $\square$

Under these hypotheses a rational map has one partial map defined on its whole domain: the representatives agree on overlaps and glue.

**Theorem (Composition).** Let $X$ be irreducible and $Y$ nonempty. Let $f$ be a partial map from $X$ to $Y$ with dense image and $g$ a partial map from $Y$ to $Z$. Then $f^{-1}(\operatorname{dom} g)$ is a dense open of $X$, and $g \circ f$ is a partial map with this domain. Its class depends only on the classes of $f$ and $g$.

*Proof.* Step 1. The set $f^{-1}(\operatorname{dom} g)$ is open in $\operatorname{dom} f$, so it is open in $X$. It is nonempty: $\operatorname{dom} g$ is a nonempty open, since it is dense in the nonempty $Y$, and it meets the dense image of $f$. In the irreducible space $X$ every nonempty open is dense.

Step 2. Let $f' \sim f$ on $W_1$ and $g' \sim g$ on $W_2$. On the set $W = W_1 \cap f^{-1}(W_2)$ the composites $g' \circ f'$ and $g \circ f$ agree. The set $f^{-1}(W_2)$ is a nonempty open by the argument of step 1, so $W$ is a nonempty open, and it is dense since $X$ is irreducible. $\square$

**Counterexample (A non-dominant first map).** Let $k$ be a field, $f : \mathbb{A}^1_k \to \mathbb{A}^2_k$ with $t \mapsto (t, 0)$, and $g : \mathbb{A}^2_k \dashrightarrow \mathbb{A}^1_k$ given by $x/y$ on $D(y)$. Then $f^{-1}(D(y))$ is the set where $0$ is invertible, which is empty. So $g \circ f$ is not a partial map.

With dominance the composition is associative, and the identity is a unit on both sides. This makes integral schemes with dominant rational maps a category.

**Theorem (Rational maps and the function field).** Let $X$ be an integral $S$-scheme and $Y$ an $S$-scheme locally of finite type over $S$. Let $\eta$ be the generic point and $K(X) = \mathcal{O}_{X, \eta}$. Restriction to $\eta$ gives a bijection between rational maps $X \dashrightarrow Y$ over $S$ and $S$-morphisms $\operatorname{Spec} K(X) \to Y$.

*Proof.* Step 1 (the map). Each dense open $U$ contains $\eta$, so a partial map $f : U \to Y$ gives the composite $\operatorname{Spec} K(X) \to U \to Y$. Equivalent partial maps agree on a dense open, which contains $\eta$, so the map is well defined on classes.

Step 2 (injectivity). Let $f$ and $g$ have the same restriction to $\eta$, with image $y$. Choose an affine open $\operatorname{Spec} B \ni y$ of $Y$. The set $f^{-1}(\operatorname{Spec} B) \cap g^{-1}(\operatorname{Spec} B)$ is open and contains $\eta$, so it contains an affine open $\operatorname{Spec} A \ni \eta$. The two maps $B \to A$ have the same composite with $A \to K(X)$. This map is injective, because $A$ is a domain and $K(X)$ is its fraction field. So $f$ and $g$ agree on $\operatorname{Spec} A$, which is dense.

Step 3 (surjectivity). Let $\varphi : \operatorname{Spec} K(X) \to Y$ be an $S$-morphism with image $y$. Choose an affine open $\operatorname{Spec} R \subseteq S$ under $y$, an affine open $\operatorname{Spec} B \ni y$ of $Y$ over $\operatorname{Spec} R$, and an affine open $\operatorname{Spec} A$ of $X$ over $\operatorname{Spec} R$. Then $\varphi$ is an $R$-algebra map $B \to K(X)$. Since $Y$ is locally of finite type, $B$ is generated over $R$ by finitely many $b_1, \dots, b_n$. Write $\varphi(b_i) = a_i / s$ with $a_i, s \in A$ and $s \ne 0$. The image of $R$ lies in $A$, so $\varphi(B) \subseteq A_s$. So $\varphi$ factors through $B \to A_s$, which gives an $S$-morphism $D(s) \to \operatorname{Spec} B \subseteq Y$. The open $D(s)$ is nonempty, so it is dense, and its restriction to $\eta$ is $\varphi$. $\square$

**Corollary (Rational functions).** Let $X$ be an integral $k$-scheme. Rational maps $X \dashrightarrow \mathbb{A}^1_k$ over $k$ are in bijection with the elements of $K(X)$.

*Proof.* A $k$-morphism $\operatorname{Spec} K(X) \to \operatorname{Spec} k[t]$ is a $k$-algebra map $k[t] \to K(X)$, which is fixed by the image of $t$. $\square$

**Proposition (Birationality is an equivalence relation).** Birationality is reflexive, symmetric and transitive.

*Proof.* The identity of $X$ is a partial isomorphism, and the inverse of $U \cong V$ is $V \cong U$. For transitivity let $\alpha : U \cong V$ with $V \subseteq Y$ and $\beta : V' \cong W$ with $V' \subseteq Y$. The set $V \cap V'$ is a dense open of $Y$. Its preimage $\alpha^{-1}(V \cap V')$ is a dense open of $U$, because $\alpha$ is a homeomorphism, so it is dense in $X$. The same holds for $\beta(V \cap V')$ in the target of $\beta$. The restriction of $\beta \circ \alpha$ is an isomorphism between these two dense opens. $\square$

### Examples

**Example (Inversion on the line).** Let $f$ be the partial map on $\mathbb{A}^1_k = \operatorname{Spec} k[x]$ with domain $D(x)$, given by $k[t] \to k[x, x^{-1}]$, $t \mapsto x^{-1}$. Its image is $D(x)$, which is dense, so $f$ is dominant. The composite $f \circ f$ has domain $f^{-1}(D(x)) = D(x)$ and sends $t$ to $(x^{-1})^{-1} = x$. So $f \circ f$ is equivalent to the identity, and $f$ gives a partial isomorphism $D(x) \cong D(x)$. The domain of the class is exactly $D(x)$: a value at $0$ would require $x^{-1} \in k[x]_{(x)}$.

**Example (The projection to the projective line).** The map $(x, y) \mapsto [x : y]$ from $\mathbb{A}^2_k$ to $\mathbb{P}^1_k$ is defined on $D(y)$ by $[x/y : 1]$ and on $D(x)$ by $[1 : y/x]$. On $D(xy)$ the two agree, since $[x/y : 1] = [1 : y/x]$. So the domain contains $D(x) \cup D(y) = \mathbb{A}^2_k \setminus \{0\}$. It does not contain the origin. Suppose a morphism $h$ near the origin extends the map. For $c \in k$ the composite of $h$ with $t \mapsto (t, ct)$ is defined near $t = 0$ and equals $[1 : c]$ for $t \ne 0$. By the uniqueness theorem, with $\mathbb{A}^1$ reduced and $\mathbb{P}^1$ separated, $h(0) = [1 : c]$ for each $c$, which is impossible.

**Example (The line and the projective line).** The open immersion $\mathbb{A}^1_k \to \mathbb{P}^1_k$, $t \mapsto [t : 1]$, has dense image, so it is a partial isomorphism from $\mathbb{A}^1_k$ to $\mathbb{P}^1_k$. So $\mathbb{P}^1_k$ is birational to $\mathbb{A}^1_k$ over $k$, and it is rational over $k$. They are not isomorphic: $\Gamma(\mathbb{P}^1_k, \mathcal{O}) = k$ while $\Gamma(\mathbb{A}^1_k, \mathcal{O}) = k[t]$.

### The library around it

::: mathlib
`AlgebraicGeometry.Scheme.PartialMap` · `Mathlib.AlgebraicGeometry.Birational.RationalMap`

`X.PartialMap Y` has fields `domain : X.Opens`, `dense_domain` and `hom : domain ⟶ Y`. `PartialMap.IsOver` is the condition over `S`, and `PartialMap.restrict` and `PartialMap.compHom` restrict and compose with a morphism. `Hom.toPartialMap` and `PartialMap.id` view morphisms as partial maps. `PartialMap.fromSpecStalkOfMem` and `PartialMap.ofFromSpecStalk` pass between partial maps and morphisms from stalks.

<?decl AlgebraicGeometry.Scheme.PartialMap?>
:::

::: mathlib
`AlgebraicGeometry.Scheme.PartialMap.equiv_iff_of_isSeparated` · `Mathlib.AlgebraicGeometry.Birational.RationalMap`

`PartialMap.equiv` is the relation with a dense open `W` below both domains, and `PartialMap.equivalence_rel` proves the proposition. The lemma `PartialMap.equiv_iff_of_isSeparated` is the uniqueness theorem for `IsReduced X` and `IsSeparated sY`, and `PartialMap.equiv_iff_of_isSeparated_of_le` treats nested domains.

<?decl AlgebraicGeometry.Scheme.PartialMap.equiv_iff_of_isSeparated?>
:::

::: mathlib
`AlgebraicGeometry.Scheme.RationalMap` · `Mathlib.AlgebraicGeometry.Birational.RationalMap`

`X ⤏ Y` is the quotient, a scoped notation. `RationalMap.representative` chooses a partial map, `RationalMap.domain` is the supremum of domains with `RationalMap.dense_domain`, and `RationalMap.toPartialMap` gives the glued partial map for reduced `X` and separated `Y`. The bijection with the function field is `RationalMap.equivFunctionFieldOver`, stated with `RationalMap.IsOver`, and `RationalMap.equivFunctionField` states it with `compHom`. Its inverse is `RationalMap.ofFunctionField`.

<?decl AlgebraicGeometry.Scheme.RationalMap?>
:::

::: mathlib
`AlgebraicGeometry.Scheme.RationalMap.comp` · `Mathlib.AlgebraicGeometry.Birational.Composition`

`PartialMap.comp f g` needs `[IsDominant f.hom]`; it works under `PreirreducibleSpace X` and `Nonempty Y`. Its class is well defined by `PartialMap.comp_equiv_of_equiv`, and `RationalMap.comp` needs `[f.IsDominant]`. `RationalMap.comp_assoc` assumes an irreducible middle scheme and a nonempty last one, and `RationalMap.id_comp`, `RationalMap.comp_id` and `RationalMap.isOver_comp` complete the list. `RationalMap.IsDominant` is in `Birational.Dominant`, with `PartialMap.isDominant_toRationalMap_iff`.

<?decl AlgebraicGeometry.Scheme.RationalMap.comp?>
:::

::: mathlib
`AlgebraicGeometry.Scheme.Birational` · `Mathlib.AlgebraicGeometry.Birational.Birational`

`Scheme.PartialIso X Y` has `source`, `target`, their density and `iso`, with `PartialIso.symm`, `PartialIso.trans` and `PartialIso.ofIso`. `Scheme.Birational X Y` is `Nonempty (PartialIso X Y)`, with `Birational.trans`. `Scheme.BirationalOver` asks the partial isomorphism to be over `S`, and `Scheme.IsRationalOver` asks for an `S`-birational map to `𝔸(n; S)` with `n : Type u`. `Opens.birational_of_dense` and `Hom.birational` give birationality from a dense open and from a dominant open immersion.

<?decl AlgebraicGeometry.Scheme.Birational?>
:::

Common errors of a learner: a rational map is a class, so its value at a point is defined only through a representative and only on the domain. Composition needs the first map to be dominant, and the instance `[f.IsDominant]` must be found by Mathlib. The uniqueness theorem needs both a reduced source and a separated target. The module `AlgebraicGeometry.RationalMap` is deprecated and only imports `Birational.RationalMap`.

### Exercises

1. (A) Find the domain of the rational function $f = (x^2 - 1)/(x - 1)$ on $\mathbb{A}^1_k$, viewed as a rational map to $\mathbb{A}^1_k$. *Hint:* Simplify the fraction in $k(x)$.
2. (A) Show that two dense opens of an irreducible space meet. *Hint:* Use the lemma on dense opens.
3. (B) Show that the map $t \mapsto (t^2, t^3)$ from $\mathbb{A}^1_k$ to the cusp $C = \operatorname{Spec} k[x, y]/(y^2 - x^3)$ is birational. *Hint:* Use $t = y/x$ on $D(x)$.
4. (B) Show that $\mathbb{A}^2_k$ and $\mathbb{P}^1_k \times_k \mathbb{P}^1_k$ are birational. *Hint:* Both contain $\mathbb{A}^1_k \times_k \mathbb{A}^1_k$ as a dense open.
5. (C) Give two partial maps that are equivalent but differ on the intersection of their domains, with $Y$ not separated. *Hint:* Use the line with a doubled origin as $Y$.
6. (C) Let $X$ be integral of finite type over $k$ and $f : X \dashrightarrow X$ birational over $k$. Show that $f$ induces a $k$-automorphism of $K(X)$. *Hint:* Use the bijection with morphisms $\operatorname{Spec} K(X) \to X$ and the composition with the inverse.

### Notes and history

Rational and birational maps are classical in algebraic geometry and were put in scheme language in EGA I. Hartshorne treats them for varieties in Chapter I, and the function field correspondence for integral schemes follows EGA and the Stacks project.

The Mathlib Author of `Birational.RationalMap` is Andrew Yang. The Mathlib Author of `Birational.Birational`, `Birational.Composition` and `Birational.Dominant` is Justus Springer.

### Reference

<?reference?>
