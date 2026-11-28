---
title: Asymptotics in products, completions and topological vector spaces
kind: api
modules:
  - Mathlib.Analysis.Asymptotics.Prod
  - Mathlib.Analysis.Asymptotics.Completion
  - Mathlib.Analysis.Asymptotics.TVS
explains:
  E2: [Asymptotics.isBigO_prod_left, Asymptotics.IsBigO.fiberwise_right, Asymptotics.isBigO_completion_left, Asymptotics.IsLittleOTVS.isBigOTVS, Asymptotics.IsBigOTVS.trans, Asymptotics.isBigOTVS_iff_isBigO]
  E1: auto
families: []
requires: [V13, V14, V15.C01, V15.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Asymptotics in products, completions and topological vector spaces

### Overview

Section 1 of this chapter defines $f = O(g)$ and $f = o(g)$ along a filter for functions with values in normed spaces. This section treats three modules that extend the theory in three directions. The first module treats functions with values in a product $E \times F$ and functions on a product of two filters. The second module shows that the relations do not change when a function takes its values in the completion of a normed group. The third module defines $O$, $o$ and $\Theta$ for functions with values in topological vector spaces, where there is no norm.

The first two modules are small and are used as rewriting tools. The third module is larger. It gives a definition of $f = o(g)$ that depends only on the topology and the scalar field, and it proves that in a normed space the new definition agrees with the old one. The later volume on differential calculus uses this definition for derivatives in spaces without a chosen norm.

### The library around it

#### Products of normed spaces

In Mathlib the norm on a product $E \times F$ is the maximum of the norms of the components: $\|(x, y)\| = \max(\|x\|, \|y\|)$ (`Prod.norm_mk`). The module `Mathlib.Analysis.Asymptotics.Prod` turns this fact into rules for $O$ and $o$. There are three families.

1. *A component is bounded by the pair.* `Asymptotics.isBigOWith_fst_prod` says that $f' = O(( f', g'))$ with the constant $1$, and `Asymptotics.isBigO_fst_prod` and `Asymptotics.isBigO_snd_prod` are the forms without the constant. The primed forms `Asymptotics.isBigO_fst_prod'` and `Asymptotics.isBigO_snd_prod'` take one function `f' : α → E' × F'` and its components.
2. *A pair on the right.* If $f = O(g')$, then $f = O((g', k'))$ for every $k'$ (`Asymptotics.IsBigO.prod_rightl`), and $f = O((f', g'))$ (`Asymptotics.IsBigO.prod_rightr`). The letters `l` and `r` tell the side of the pair that holds the known function. The forms `Asymptotics.IsLittleO.prod_rightl` and `Asymptotics.IsLittleO.prod_rightr` treat $o$.
3. *A pair on the left.* A pair is small exactly when both components are small.

**Theorem.** $(f', g') = O(k')$ if and only if $f' = O(k')$ and $g' = O(k')$.

*Proof.* If the pair is $O(k')$, each component is $O$ of the pair by family 1, and transitivity gives $f' = O(k')$ and $g' = O(k')$. Conversely, suppose eventually $\|f'(x)\| \le c\|k'(x)\|$ and $\|g'(x)\| \le c'\|k'(x)\|$. Then eventually $\max(\|f'(x)\|, \|g'(x)\|) \le \max(c, c')\|k'(x)\|$. $\square$

This is `Asymptotics.isBigO_prod_left`, with the directions `Asymptotics.IsBigO.prod_left`, `Asymptotics.IsBigO.prod_left_fst` and `Asymptotics.IsBigO.prod_left_snd`. The forms with explicit constants are `Asymptotics.IsBigOWith.prod_left_same`, where both components have the same constant, and `Asymptotics.IsBigOWith.prod_left`, with the constant $\max(c, c')$. The rule for $o$ is `Asymptotics.isLittleO_prod_left`.

The module also treats the product filter $l \times l'$ on $\alpha \times \beta$, written `l ×ˢ l'`. A relation along $l$ lifts to the product: if $f = O(g)$ along $l$, then $f \circ \mathrm{fst} = O(g \circ \mathrm{fst})$ along $l \times l'$ (`Asymptotics.IsBigO.comp_fst`, and `Asymptotics.IsBigO.comp_snd` for the second factor). The converse direction restricts a relation on the product to the fibers.

**Theorem.** If $f = O(g)$ along $l \times l'$, then for $l$-almost every $a$, the functions $x \mapsto f(a, x)$ and $x \mapsto g(a, x)$ satisfy $f(a, \cdot) = O(g(a, \cdot))$ along $l'$.

*Proof.* The bound $\|f(p)\| \le c\|g(p)\|$ holds on a set of the product filter. Such a set contains a rectangle $t_1 \times t_2$ with $t_1 \in l$ and $t_2 \in l'$. For $a \in t_1$, the bound holds for all $x \in t_2$, so it holds eventually along $l'$, with the same constant $c$. $\square$

This is `Asymptotics.IsBigO.fiberwise_right`, and `Asymptotics.IsBigO.fiberwise_left` fixes the second coordinate. The constant does not depend on $a$, but the statement keeps only the existence of a constant for each fiber.

#### Completions

A seminormed group $F$ embeds in its completion $\hat F$, the space `UniformSpace.Completion F`, and the embedding keeps the norm: $\|\hat x\| = \|x\|$ (`UniformSpace.Completion.norm_coe`). The module `Mathlib.Analysis.Asymptotics.Completion` has six lemmas, one for each relation and each side.

**Theorem.** For $g : \alpha \to F$, the coerced function $x \mapsto \widehat{g(x)}$ satisfies $\hat g = O(f)$ if and only if $g = O(f)$.

*Proof.* The definition of $O$ uses only the norms $\|\hat g(x)\|$, and these are equal to $\|g(x)\|$. So the two statements are the same inequality. $\square$

This is `Asymptotics.isBigO_completion_left`. The other five are `Asymptotics.isBigO_completion_right`, `Asymptotics.isLittleO_completion_left`, `Asymptotics.isLittleO_completion_right`, `Asymptotics.isTheta_completion_left` and `Asymptotics.isTheta_completion_right`. All six have the attributes `simp` and `norm_cast`, so `simp` or `norm_cast` removes the coercion to the completion from a goal.

#### Asymptotics without a norm

Let $E$ and $F$ be topological vector spaces over a nontrivially normed field $\mathbb{K}$. There is no norm on $E$, but every neighborhood $U$ of $0$ gives a gauge. The *extended gauge* of $U$ at $y$, `egauge 𝕜 U y`, is

$$\operatorname{egauge}_U(y) = \inf\{\|c\| : c \in \mathbb{K},\ y \in c\,U\} \in [0, \infty].$$

A small gauge means that $y$ is deep inside a small multiple of $U$. The gauge is antitone in the set: a larger $U$ gives a smaller gauge (`egauge_anti`). The module `Mathlib.Analysis.Asymptotics.TVS` defines three relations with it.

1. `Asymptotics.IsLittleOTVS 𝕜 l f g`, with the notation `f =o[𝕜; l] g`: for every neighborhood $U$ of $0$ in $E$ there is a neighborhood $V$ of $0$ in $F$ such that for every $\varepsilon > 0$, eventually $\operatorname{egauge}_U(f(x)) \le \varepsilon \operatorname{egauge}_V(g(x))$.
2. `Asymptotics.IsBigOTVS 𝕜 l f g`, with the notation `f =O[𝕜; l] g`: for every $U$ there is a $V$ with eventually $\operatorname{egauge}_U(f(x)) \le \operatorname{egauge}_V(g(x))$. No constant appears, because a constant can be absorbed in the choice of $V$.
3. `Asymptotics.IsThetaTVS 𝕜 l f g`, with the notation `f =Θ[𝕜; l] g`: both `f =O[𝕜; l] g` and `g =O[𝕜; l] f`.

The definitions depend on the field $\mathbb{K}$, which is why it appears in the notation. They do not depend on any choice of norm. The fields of the two structures are `Asymptotics.IsLittleOTVS.exists_eventuallyLE_mul` and `Asymptotics.IsBigOTVS.exists_eventuallyLE`.

**Theorem.** If $f = o(g)$ in the sense of the gauges, then $f = O(g)$.

*Proof.* Given $U$, take the $V$ of the definition of $o$ and the value $\varepsilon = 1$. Then eventually $\operatorname{egauge}_U(f(x)) \le \operatorname{egauge}_V(g(x))$, which is the condition for $O$. $\square$

This is `Asymptotics.IsLittleOTVS.isBigOTVS`. The rules of transitivity have the same pattern.

**Theorem.** If $f = O(g)$ and $g = O(k)$ in the sense of the gauges, then $f = O(k)$.

*Proof.* Let $U$ be a neighborhood of $0$ in $E$. The first relation gives $V$ in $F$ with eventually $\operatorname{egauge}_U(f) \le \operatorname{egauge}_V(g)$. The second relation, applied to $V$, gives $W$ in $G$ with eventually $\operatorname{egauge}_V(g) \le \operatorname{egauge}_W(k)$. The two eventual inequalities combine. $\square$

This is `Asymptotics.IsBigOTVS.trans`. The mixed rules are `Asymptotics.IsLittleOTVS.trans_isBigOTVS`, `Asymptotics.IsBigOTVS.trans_isLittleOTVS`, `Asymptotics.IsLittleOTVS.trans` and the forms with $\Theta$, such as `Asymptotics.IsThetaTVS.trans`. The transitivity instances, for example `Asymptotics.instTransIsBigOTVSIsLittleOTVS`, let a `calc` block chain the relations.

The main theorem of the module compares the new relations with the old ones.

**Theorem.** If $E$ and $F$ are normed spaces over $\mathbb{K}$, then `f =O[𝕜; l] g` holds if and only if `f =O[l] g` holds.

*Proof sketch.* The gauge of a ball is comparable with the norm. For $r > 0$ and a scalar $c$ with $\|c\| > 1$, $\|y\|/r \le \operatorname{egauge}_{B(0,r)}(y) \le \|c\|\,\|y\|/r$ (`div_le_egauge_ball`, `egauge_ball_le_of_one_lt_norm`). Suppose eventually $\|f\| \le C\|g\|$ with $C > 0$, and let $U$ contain the ball $B(0, r)$. Take $V = B(0, \rho)$ with $\rho = r/(C\|c\|)$. Then $\operatorname{egauge}_U(f) \le \|c\|\,\|f\|/r \le \|g\|/\rho \le \operatorname{egauge}_V(g)$. Conversely, apply the gauge relation to $U = B(0, 1)$ and use $\|y\| \le \operatorname{egauge}_{B(0,1)}(y)$ (`le_egauge_unitBall`). The $V$ that the relation gives contains a ball $B(0, r)$, so $\|f\| \le \operatorname{egauge}_V(g) \le (\|c\|/r)\|g\|$. $\square$

This is `Asymptotics.isBigOTVS_iff_isBigO`. The companions are `Asymptotics.isLittleOTVS_iff_isLittleO` and `Asymptotics.isThetaTVS_iff_isTheta`. Their directions have the names `Asymptotics.IsBigO.isBigOTVS`, `Asymptotics.IsBigOTVS.isBigO`, `Asymptotics.IsLittleO.isLittleOTVS`, `Asymptotics.IsTheta.isThetaTVS` and `Asymptotics.IsThetaTVS.isTheta`.

The rest of the module repeats the algebra of Section 1 for the new relations. The table lists the families.

| Lean name | Statement |
|---|---|
| `Asymptotics.IsLittleOTVS.add`, `Asymptotics.IsLittleOTVS.sum` | sums of functions that are $o(g)$ are $o(g)$ |
| `Asymptotics.IsLittleOTVS.neg_left`, `Asymptotics.isLittleOTVS_neg_right` | signs do not matter |
| `Asymptotics.IsLittleOTVS.triangle` | from $f_1 - f_2 = o(g)$ and $f_2 - f_3 = o(g)$ follows $f_1 - f_3 = o(g)$ |
| `Asymptotics.IsLittleOTVS.comp_tendsto`, `Asymptotics.isLittleOTVS_map` | change of the filter by a map |
| `Asymptotics.IsLittleOTVS.mono`, `Asymptotics.isLittleOTVS_sup` | smaller filters and suprema of filters |
| `Asymptotics.IsLittleOTVS.insert` | a point with $f(x) = 0$ can join a punctured neighborhood |
| `Asymptotics.isLittleOTVS_prodMk_left`, `Asymptotics.isLittleOTVS_pi` | a pair or a family is small when each component is small |
| `ContinuousLinearMap.isBigOTVS_comp` | $L \circ f = O(f)$ for a continuous linear map $L$ |
| `ContinuousLinearMap.isThetaTVS_comp` | $L \circ f = \Theta(f)$ when $L$ is an inducing map |
| `Asymptotics.isLittleOTVS_one` | $f = o(1)$ if and only if $f \to 0$ |
| `Asymptotics.isLittleOTVS_iff_tendsto_inv_smul` | for a scalar function $\varphi$, $g = o(\varphi)$ if and only if $\varphi^{-1} g \to 0$, when $g$ vanishes where $\varphi$ vanishes |

To check a relation, it is enough to test $U$ in a basis of neighborhoods of $0$: `Filter.HasBasis.isLittleOTVS_iff` and `Filter.HasBasis.isBigOTVS_iff` state this. The forms `Asymptotics.isLittleOTVS_iff_smallSets` and `Asymptotics.isBigOTVS_iff_smallSets` say that once a $V$ works, every smaller neighborhood works too. The lemma `Asymptotics.IsLittleOTVS.insert` is the step that the definition of the derivative within a set needs: the remainder $f(x) - f(x_0) - L(x - x_0)$ vanishes at the base point $x = x_0$.

#### Common errors

1. Writing `f =o[l] g` for functions with values in a topological vector space. That relation needs norms. The form for topological vector spaces is `f =o[𝕜; l] g`, and the field `𝕜` must be given.
2. Looking for a name IsLittleOTVS.isLittleO with a capital letter. The direction from the gauge relation to the norm relation for $o$ has the name `Asymptotics.isLittleOTVS.isLittleO`, with a lowercase `i`, while the direction for $O$ is `Asymptotics.IsBigOTVS.isBigO`.
3. Reading `Asymptotics.IsBigO.prod_rightl` as a statement about the left factor of the domain. The pair is in the codomain of the right side, and the letter says which component of that pair holds the known function.

### Exercises

1. (A) Show that $(\sin x, x) = O(x)$ along `atTop` on `ℝ`, with values in `ℝ × ℝ`. Name the lemma of the product module that you use.
2. (A) Show that $\operatorname{egauge}_U(0) = 0$ for every neighborhood $U$ of $0$, and deduce that the zero function is $o(g)$ for every $g$.
3. (B) Let $f = O(g)$ along $l \times l'$. Show by an example that the fiber relations of `Asymptotics.IsBigO.fiberwise_right` can fail for some $a$, so that "eventually in $l$" cannot become "for all $a$".
4. (B) Show that $f = o(g)$ in the sense of the gauges implies $f = o(g)$ along every smaller filter, and that $f = o(g)$ along $l_1$ and along $l_2$ implies $f = o(g)$ along $l_1 \sqcup l_2$.
5. (B) Let $L : E \to F$ be a continuous linear map. Show that $L \circ f = O(f)$ in the sense of the gauges. Hint: for a neighborhood $U$ of $0$ in $F$, take $V = L^{-1}(U)$.
6. (C) Prove `Asymptotics.isLittleOTVS_iff_isLittleO` in the direction from the norm relation to the gauge relation. Hint: follow the proof sketch for $O$, and choose the radius of $V$ in terms of $\varepsilon$.

### Reference

<?reference?>
