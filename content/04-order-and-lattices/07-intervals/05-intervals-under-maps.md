---
title: Intervals under maps
kind: api
modules:
  - Mathlib.Order.Interval.Set.Image
  - Mathlib.Order.Interval.Set.ProjIcc
  - Mathlib.Order.Interval.Set.Monotone
  - Mathlib.Order.Interval.Set.OrderIso
  - Mathlib.Order.Interval.Set.OrderEmbedding
  - Mathlib.Order.Interval.Set.SurjOn
  - Mathlib.Order.Interval.Set.IsoIoo
  - Mathlib.Order.Interval.Set.WithBotTop
  - Mathlib.Order.Interval.Set.Pi
explains:
  E2: [surjOn_Ioo_of_monotone_surjective, surjOn_Icc_of_monotone_surjective, OrderIso.image_Icc, OrderEmbedding.preimage_Icc, Set.projIcc, Set.IccExtend, orderIsoIooNegOneOne, WithTop.image_coe_Icc, Set.pi_univ_Icc, iUnion_Ioo_of_mono_of_isGLB_of_isLUB]
  E1: auto
families: []
requires: [V04.C01, V04.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Intervals under maps

### Overview

A map between orders can send an interval to an interval, or it can break it. This section is a guide to the files that compute the image and the preimage of an interval under the maps of Chapter 1 and Chapter 2: monotone maps, order isomorphisms, order embeddings, the coercions into `WithTop` and `WithBot`, the coercion of a subtype, and the maps of a product. It also describes two constructions that go in the other direction. The projection `Set.projIcc` sends each point of a linear order to the nearest point of $[a, b]$, and `Set.IccExtend` uses it to extend a function on $[a, b]$ to the whole order.

The main rule is simple. An order isomorphism sends each interval to the interval with the image endpoints. An order embedding does the same for preimages, but not always for images. A monotone map only sends an interval into the interval between the images of the endpoints, and it fills this interval if it is surjective. The last fact is the order form of the intermediate value theorem.

### The library around it

**Monotone maps send intervals into intervals.** The file `Mathlib.Order.Interval.Set.Image` states the inclusions in the language of `Set.MapsTo`. For a monotone map $f$, `Monotone.mapsTo_Icc` says that $f$ sends $[a, b]$ into $[f(a), f(b)]$, and `Monotone.image_Icc_subset` says the same with the image. A strictly monotone map also keeps the open ends: `StrictMono.mapsTo_Ioo` and `StrictMono.image_Ioo_subset`. An antitone map reverses the endpoints: `Antitone.mapsTo_Icc` sends $[a, b]$ into $[f(b), f(a)]$. The versions with `MonotoneOn` need only monotonicity on the interval. The same file has the intervals of a subtype. If $b$ is an element of the subtype `Set.Ici a`, then the image of `Set.Iic b` under `Subtype.val` is `Set.Icc a b.val`, and `Set.preimage_subtypeVal_Icc` and `Set.image_subtypeVal_Icc_subset` give the general rules.

**Surjective monotone maps fill intervals.** Let $f : \alpha \to \beta$ be monotone and surjective, with α a linear order. Then each point strictly between $f(a)$ and $f(b)$ is the image of a point strictly between $a$ and $b$.

$$f \text{ monotone and surjective} \implies f\big((a, b)\big) \supseteq (f(a), f(b)) \qquad (\texttt{surjOn\_Ioo\_of\_monotone\_surjective}).$$

*Proof.* Let $f(a) < p < f(b)$. Since $f$ is surjective, $p = f(x)$ for some $x$. If $x \le a$, then $f(x) \le f(a)$ by monotonicity, a contradiction. So $a < x$ because the order of α is linear. In the same way, $b \le x$ gives $f(b) \le f(x)$, so $x < b$. $\square$

The closed form needs a hypothesis.

$$a \le b \implies f\big([a, b]\big) \supseteq [f(a), f(b)] \qquad (\texttt{surjOn\_Icc\_of\_monotone\_surjective}).$$

For $b < a$, a constant map on a one point codomain gives $[f(a), f(b)] = \{f(a)\}$ but $[a, b] = \emptyset$, so the hypothesis $a \le b$ is necessary. The file `Mathlib.Order.Interval.Set.SurjOn` has the versions for all kinds of intervals, such as `surjOn_Ico_of_monotone_surjective` and `surjOn_Ioi_of_monotone_surjective`. With `Monotone.image_Icc_subset`, the closed form gives equality: a surjective monotone map sends $[a, b]$ onto $[f(a), f(b)]$.

**Order isomorphisms and order embeddings.** For an order isomorphism $e : \alpha \simeq_o \beta$, the image of an interval is the interval of the images, and the preimage is the interval of the inverse images.

$$e\big([a, b]\big) = [e(a), e(b)] \qquad (\texttt{OrderIso.image\_Icc}).$$

The file `Mathlib.Order.Interval.Set.OrderIso` has this rule for all nine kinds of intervals, and `OrderIso.preimage_Icc` gives $e^{-1}([a, b]) = [e^{-1}(a), e^{-1}(b)]$. It also defines `OrderIso.IicTop`, the isomorphism of `Set.Iic ⊤` with the whole order. For an order embedding $e : \alpha \hookrightarrow_o \beta$, only preimages of intervals with endpoints in the range are simple.

$$e^{-1}\big([e(x), e(y)]\big) = [x, y] \qquad (\texttt{OrderEmbedding.preimage\_Icc}).$$

The image of $[x, y]$ under an embedding is only a subset of $[e(x), e(y)]$. For example, the embedding $n \mapsto 2n$ of $\mathbb{N}$ into $\mathbb{N}$ sends $[0, 1]$ to $\{0, 2\}$, which is not $[0, 2]$. The file `Mathlib.Order.Interval.Set.OrderEmbedding` has the preimage rules for the bounded intervals, the rays and `Set.uIcc`, and no rule for images. For an image, the range of the embedding must be order connected, and then the rule follows from the preimage rule.

**The coercions into `WithTop` and `WithBot`.** The file `Mathlib.Order.Interval.Set.WithBotTop` describes intervals of `WithTop α` in terms of intervals of α. The range of the coercion is `Set.Iio ⊤` (the lemma `WithTop.range_coe`), and the coercion sends each interval with endpoints in α to the interval with the coerced endpoints.

$$(\uparrow)\big([a, b]\big) = [\uparrow a, \uparrow b] \qquad (\texttt{WithTop.image\_coe\_Icc}).$$

The rays change their form: `WithTop.image_coe_Ioi` says that the image of $(a, \infty)$ is $(\uparrow a, \top)$, with an open end at ⊤ because ⊤ is not in the range. In the other direction, `WithTop.Ioi_coe` writes `Set.Ioi ↑a` as the image of `Set.Ioi a` together with `{⊤}`. The `WithBot` versions are the duals, and the preimage lemmas, such as `WithTop.preimage_coe_Icc`, complete the file.

**Products and functions.** For a family of orders indexed by ι, the order on the function type is pointwise, and a closed interval of functions is a product of closed intervals.

$$\prod_{i} [x_i, y_i] = [x, y] \qquad (\texttt{Set.pi\_univ\_Icc}).$$

Here the left side is `Set.pi Set.univ fun i ↦ Set.Icc (x i) (y i)`. The open form is only an inclusion: `Set.pi_univ_Ioo_subset` says that the product of the open intervals is a subset of `Set.Ioo x y`, because $x < y$ for functions only needs one coordinate with a strict inequality. The lemma `Set.image_update_Icc` says that changing one coordinate of $f$ along $[a, b]$ gives the interval between the two changed functions. The file `Mathlib.Order.Interval.Set.Pi` has these rules and the multiplicative forms such as `Set.image_mulSingle_Icc`.

**Projection onto a closed interval.** In a linear order, `Set.projIcc a b h` maps each $x$ to the nearest point of $[a, b]$, where `h : a ≤ b`. Its value is an element of the subtype `Set.Icc a b`, and its coercion is $\max(a, \min(b, x))$ (the lemma `Set.coe_projIcc`). Points of $[a, b]$ stay where they are (`Set.projIcc_of_mem`), points below $a$ go to $a$ (`Set.projIcc_of_le_left`) and points above $b$ go to $b$ (`Set.projIcc_of_right_le`). The map is monotone and surjective, and it is strictly monotone on $[a, b]$. The rays have the one sided versions `Set.projIci` and `Set.projIic`.

**Extension from a closed interval.** For a function $f$ on the subtype `Set.Icc a b`, `Set.IccExtend h f` is the composite $f \circ \operatorname{projIcc}$. It is a function on the whole order that agrees with $f$ on $[a, b]$ (`Set.IccExtend_of_mem`) and is constant to the left of $a$ and to the right of $b$. If $f$ is monotone, then `Monotone.IccExtend` says that the extension is monotone too. In analysis, a continuous path on $[0, 1]$ extends in this way to a continuous map on $\mathbb{R}$, which is useful to apply a lemma that is stated for functions on the whole line.

**Families of intervals.** The file `Mathlib.Order.Interval.Set.Monotone` treats intervals as functions of their endpoints. The ray `Set.Iic` is monotone in its endpoint and `Set.Ici` is antitone (`monotone_Iic`, `antitone_Ici`). If the left endpoints decrease and the right endpoints increase, the union of the open intervals is the open interval of the limits.

$$\bigcup_x (f(x), g(x)) = (a, b) \qquad (\texttt{iUnion\_Ioo\_of\_mono\_of\_isGLB\_of\_isLUB}).$$

The hypotheses are that $f$ is antitone, $g$ is monotone, $a$ is the greatest lower bound of the range of $f$ and $b$ is the least upper bound of the range of $g$. For example, in the type `EReal` the union of the intervals $(-n, n)$ for $n \in \mathbb{N}$ is $(\bot, \top)$, the set of the real numbers.

**An open interval as a whole order.** In a linear ordered field 𝕜, the open interval $(-1, 1)$ is order isomorphic to the whole field.

$$𝕜 \simeq_o (-1, 1) \qquad (\texttt{orderIsoIooNegOneOne}).$$

The isomorphism is $x \mapsto x / (1 + |x|)$, and its inverse is $y \mapsto y / (1 - |y|)$. The definition is irreducible, so a proof must use its lemmas and not unfold the formula. The file `Mathlib.Order.Interval.Set.IsoIoo` contains only this definition. With it, each property of 𝕜 that only uses the order also holds for $(-1, 1)$, for example that the interval has no maximum.

#### Common errors

1. Using a deprecated name for a subtype lemma. The lemmas on `Subtype.val` in this file spell the map as *subtypeVal* in one word. Older spellings with two words are deprecated aliases, so use the current form, for example `Set.preimage_subtypeVal_Icc`.
2. Applying `surjOn_Icc_of_monotone_surjective` without the hypothesis $a \le b$. The open version `surjOn_Ioo_of_monotone_surjective` needs no hypothesis, but the closed version does.
3. Expecting `Set.pi_univ_Ioo_subset` to be an equality. The open interval of functions contains functions that are equal to $x$ at some coordinates, so the product of open intervals is strictly smaller in general.

### Exercises

1. (A) Use `OrderIso.image_Icc` to compute the image of $[1, 3]$ under the order isomorphism $x \mapsto x + 5$ of $\mathbb{Z}$.
2. (A) Compute `Set.projIcc 0 1 h x` for $x = -2$, $x = \tfrac{1}{2}$ and $x = 7$ in $\mathbb{Q}$.
3. (B) Prove `surjOn_Ioo_of_monotone_surjective` from the definitions, following the proof in the text.
4. (B) Find an order embedding $e$ of $\mathbb{N}$ into $\mathbb{N}$ and $x \le y$ such that $e([x, y]) \ne [e(x), e(y)]$, and show that the range of $e$ is not order connected.
5. (B) Give two functions $x < y$ on `Fin 2 → ℕ` and a function in `Set.Ioo x y` that is not in the product of the open intervals.
6. (C) Show that `orderIsoIooNegOneOne` implies that a bounded open interval $(a, b)$ of a linear ordered field, with $a < b$, is order isomorphic to the whole field.

### Reference

<?reference?>
