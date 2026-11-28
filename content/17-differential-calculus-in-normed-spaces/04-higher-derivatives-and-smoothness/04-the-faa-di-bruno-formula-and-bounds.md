---
title: The formula of Faà di Bruno and bounds on iterated derivatives
kind: api
modules:
  - Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
  - Mathlib.Analysis.Calculus.ContDiff.Bounds
explains:
  E2: [OrderedFinpartition, OrderedFinpartition.extendEquiv, FormalMultilinearSeries.compAlongOrderedFinpartition_apply, FormalMultilinearSeries.taylorComp, HasFTaylorSeriesUpToOn.comp, ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear, norm_iteratedFDeriv_mul_le, norm_iteratedFDeriv_comp_le]
  E1: auto
families: []
requires: [V17.C02, V16]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The formula of Faà di Bruno and bounds on iterated derivatives

### Overview

The chain rule gives the first derivative of a composition: $D(g \circ f)(x) = Dg(f(x)) \circ Df(x)$. The formula of Faà di Bruno gives the $n$-th derivative. In one variable it reads
$$(g \circ f)^{(n)}(x) = \sum_{\pi} g^{(|\pi|)}(f(x)) \prod_{B \in \pi} f^{(|B|)}(x),$$
where $\pi$ runs over the partitions of $\{1, \dots, n\}$ into nonempty blocks, $|\pi|$ is the number of blocks and $|B|$ is the size of the block $B$. For $n = 2$ there are two partitions, and the formula is $(g \circ f)'' = g''(f) \, (f')^2 + g'(f) \, f''$.

In normed spaces the same formula holds with multilinear maps. The $n$-th derivative $D^n(g \circ f)(x)$ is a continuous $n$-multilinear map. Its value on $(v_1, \dots, v_n)$ is a sum over the partitions $\pi$. For each $\pi$ with blocks $B_1, \dots, B_k$, the term is $D^k g(f(x))$ applied to the $k$ vectors $D^{|B_j|} f(x)(v_i)_{i \in B_j}$. The blocks must come in a fixed order, because $D^k g(f(x))$ takes its arguments in order, and the vectors inside a block also need an order. Mathlib fixes both orders and calls the result an *ordered finpartition*.

The second module of this section turns the formulas into norm bounds. The rule of Leibniz for a bilinear map $B$ gives
$$\|D^n B(f, g)(x)\| \le \|B\| \sum_{i=0}^{n} \binom{n}{i} \|D^i f(x)\| \, \|D^{n-i} g(x)\|,$$
and a composition with bounds $\|D^i g(f(x))\| \le C$ and $\|D^i f(x)\| \le D^i$ satisfies $\|D^n(g \circ f)(x)\| \le n! \, C \, D^n$. These bounds are the main tools to prove that a function is in a Schwartz space or that a family of smooth functions has uniform bounds.

The section uses the iterated derivative and the Taylor series of Section 2, the chain rule of Chapter 2, and the continuous multilinear maps of Volume 16.

### The library around it

#### Ordered finpartitions

The structure `OrderedFinpartition n` is a partition of `Fin n` with a fixed order. Its fields are:

| Field | Meaning |
|---|---|
| `c.length` | the number $k$ of parts |
| `c.partSize m` | the size of the part $m$, for `m : Fin c.length` |
| `c.partSize_pos m` | each part is nonempty |
| `c.emb m` | the map `Fin (c.partSize m) → Fin n` that lists the part $m$ |
| `c.emb_strictMono m` | each list is increasing |
| `c.parts_strictMono` | the largest elements of the parts increase with $m$ |
| `c.disjoint`, `c.cover` | the parts are disjoint and cover `Fin n` |

The two conditions of monotony make the order unique. Each set partition of `Fin n` has exactly one ordered form: sort each block, then sort the blocks by their largest elements. So the number of ordered finpartitions of $n$ is the Bell number $B_n$, with the values $1, 1, 2, 5, 15, 52$ for $n = 0, \dots, 5$. It is not the number of ordered set partitions, which is much larger.

The instance `OrderedFinpartition.instFintype` makes the sums over partitions finite sums. The instances `OrderedFinpartition.instUniqueZero` and `OrderedFinpartition.instUniqueOne` say that there is one partition for $n = 0$ and for $n = 1$. The lemma `OrderedFinpartition.length_le` gives $k \le n$. The lemmas `OrderedFinpartition.sum_sigma_eq_sum` and `OrderedFinpartition.prod_sigma_eq_prod` say that a sum or a product over all the parts and over the elements of each part is the sum or product over `Fin n`.

The recursion on $n$ uses two constructions. For `c : OrderedFinpartition n`, `c.extendLeft` adds a new element as a part of its own, and `c.extendMiddle m` adds the new element to the part $m$. The equivalence
$$\texttt{OrderedFinpartition.extendEquiv}\ n : (\Sigma\, c,\ \texttt{Option}\ (\texttt{Fin}\ c.\texttt{length})) \simeq \texttt{OrderedFinpartition}\ (n+1)$$
says that every partition of $n + 1$ comes from exactly one pair: a partition $c$ of $n$, and either `none` (a new part) or `some m` (the part $m$). This is the step of the induction in the proof of the formula, and it is also the recursion $B_{n+1} = \sum_{c} (k(c) + 1)$ for the Bell numbers. The partition `OrderedFinpartition.atomic n` has $n$ parts of size $1$.

#### Composition along a partition

For a partition $c$ with $k$ parts, a continuous $k$-multilinear map $f$ and maps $p_m$ that are continuous multilinear in `c.partSize m` variables, `c.compAlongOrderedFinpartition f p` is the continuous $n$-multilinear map
$$v \mapsto f\bigl(p_1(v \circ c.\mathrm{emb}\ 1), \dots, p_k(v \circ c.\mathrm{emb}\ k)\bigr).$$
The inner vector is `c.applyOrderedFinpartition p v`. The bound `OrderedFinpartition.norm_compAlongOrderedFinpartition_le` gives $\|f\| \prod_m \|p_m\|$. The version `OrderedFinpartition.compAlongOrderedFinpartitionL` is the same construction as a continuous multilinear map in $f$ and the $p_m$, and its norm is at most $1$ (`OrderedFinpartition.norm_compAlongOrderedFinpartitionL_le`).

For two formal multilinear series $q$ (of $g$) and $p$ (of $f$), `q.compAlongOrderedFinpartition p c` uses the term `q c.length` and the terms `p (c.partSize m)`. The lemma `FormalMultilinearSeries.compAlongOrderedFinpartition_apply` states
$$(q.\mathrm{compAlongOrderedFinpartition}\ p\ c)\ v = q_{k}\bigl(c.\mathrm{applyOrderedFinpartition}\ (m \mapsto p_{|c_m|})\ v\bigr).$$
Then `FormalMultilinearSeries.taylorComp q p` is the series whose term of degree $n$ is the sum of these maps over all `c : OrderedFinpartition n`. It is the formal series of Faà di Bruno. It differs from the composition `FormalMultilinearSeries.comp` of Chapter 7, which uses compositions of $n$ (ordered sums $n = n_1 + \dots + n_k$) and is suited to power series at $0$.

#### The formula

The main theorem is `HasFTaylorSeriesUpToOn.comp`. If $q$ is a Taylor series of $g$ up to order $n$ on $t$, $p$ is a Taylor series of $f$ up to order $n$ on $s$, and `Set.MapsTo f s t`, then
$$x \mapsto (q(f(x))).\mathrm{taylorComp}\ (p(x))$$
is a Taylor series of $g \circ f$ up to order $n$ on $s$. The theorem needs no condition of unique differentiability, because `HasFTaylorSeriesUpToOn` is a property of a given family of series and does not ask that the family is unique. The order $n$ is of type `WithTop ℕ∞`, so the theorem also covers $n = \infty$ and $n = \omega$.

This theorem is the proof of `ContDiffWithinAt.comp` and of `ContDiff.comp` in Section 3. For iterated derivatives at a point, `iteratedFDeriv_comp` in `Mathlib.Analysis.Calculus.ContDiff.Comp` gives the equality
$$D^i(g \circ f)(x) = (\mathrm{ftaylorSeries}\ g\ (f\ x)).\mathrm{taylorComp}\ (\mathrm{ftaylorSeries}\ f\ x)\ i$$
when $g$ and $f$ are $C^n$ at the relevant points and $i \le n$. In one variable, `iteratedDeriv_comp_eq_sum_orderedFinpartition` writes this as the scalar formula of the overview, and `iteratedDeriv_comp_two` and `iteratedDeriv_comp_three` give the cases $n = 2$ and $n = 3$.

Two further results control `taylorComp` as a function of its inputs. The lemma `analyticOn_taylorComp` says that the terms of `(q (f x)).taylorComp (p x)` are analytic in $x$ when the terms of $q$ and $p$ and the map $f$ are analytic. The lemmas `FormalMultilinearSeries.taylorComp_sub_taylorComp_isBigO` and `FormalMultilinearSeries.taylorComp_sub_taylorComp_isLittleO` say that if two pairs of series are bounded along a filter and differ by $O(f)$ or $o(f)$ up to degree $n$, then their compositions of degree $n$ also differ by $O(f)$ or $o(f)$.

#### Bounds of Leibniz type

The module `Mathlib.Analysis.Calculus.ContDiff.Bounds` proves bounds on $\|D^n\|$ for products and compositions. Each lemma has a global form with `iteratedFDeriv` and `ContDiff`, and a form with `iteratedFDerivWithin` and `ContDiffOn` that also asks for `UniqueDiffOn 𝕜 s` and `x ∈ s`. Each lemma asks for the smoothness of order `N : WithTop ℕ∞` and for `(n : WithTop ℕ∞) ≤ N`.

| Lean name | Bound on $\|D^n h(x)\|$ |
|---|---|
| `ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear` | $h = B(f, g)$: $\|B\| \sum_i \binom{n}{i} \|D^i f\| \|D^{n-i} g\|$ |
| `ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_le_one` | the same without $\|B\|$, when $\|B\| \le 1$ |
| `norm_iteratedFDeriv_smul_le` | $h = f \cdot g$, scalar $f$: the sum of Leibniz |
| `norm_iteratedFDeriv_mul_le` | $h = f g$ in a normed algebra: the sum of Leibniz |
| `norm_iteratedFDeriv_clm_apply` | $h = f(y)(g(y))$ with $f$ operator valued: the sum of Leibniz |
| `norm_iteratedFDeriv_clm_apply_const` | $h = f(y)(c)$: $\|c\| \, \|D^n f\|$ |
| `ContinuousLinearMap.norm_iteratedFDeriv_comp_left` | $h = L \circ f$: $\|L\| \, \|D^n f\|$ |
| `norm_iteratedFDeriv_prod_le` | $h = \prod_{j \in u} f_j$: a sum over `u.sym n` with multinomial coefficients |

The lemmas for products, scalar products and evaluation come from the bilinear one, applied to multiplication, scalar multiplication or evaluation, whose norms are at most $1$. The product lemma `norm_iteratedFDeriv_prod_le` needs a commutative normed algebra with `NormOneClass`. Its sum runs over the multisets $p$ of size $n$ with elements in $u$, and the coefficient `Multiset.countPerms p` is the multinomial coefficient $n! / \prod_j (\mathrm{count}_j p)!$.

#### The bound for compositions

The lemma `norm_iteratedFDeriv_comp_le` takes $g$ and $f$ of class $C^N$, $n \le N$, a point $x$ and two constants:
$$\forall i \le n,\ \|D^i g(f(x))\| \le C, \qquad \forall i,\ 1 \le i \le n \Rightarrow \|D^i f(x)\| \le D^i.$$
Its conclusion is $\|D^n(g \circ f)(x)\| \le n! \, C \, D^n$. The form `norm_iteratedFDerivWithin_comp_le` works on sets $s$ and $t$ with `Set.MapsTo f s t`. The form `norm_iteratedFDeriv_comp_le'` asks only that $g$ is $C^N$ on a set $t$ with unique derivatives that contains the range of $f$. This form helps when $g$ is smooth only on an open set, for example $g = \log$ on $(0, \infty)$.

The factor $n!$ is not sharp. The formula of Faà di Bruno gives the factor $B_n$, and $B_n \le n!$. The constant $n!$ is simpler to use in estimates.

#### Common errors

1. The hypotheses of `norm_iteratedFDeriv_comp_le` have different ranges. The bound on $g$ is for all $i \le n$, including $i = 0$, and it is a single constant $C$. The bound on $f$ is for $1 \le i \le n$ only, and it is $D^i$, not $D$. A proof that gives the hypothesis for $f$ with the constant $D$ does not match. Write $D$ as a maximum of the $i$-th roots, or use $D \ge 1$ and `pow_le_pow_right₀`.
2. The theorem `HasFTaylorSeriesUpToOn.comp` gives *a* Taylor series of $g \circ f$. To identify it with `iteratedFDerivWithin`, unique differentiability is necessary. On sets without unique derivatives the iterated derivative within the set is not determined by the Taylor series. Use `ContDiffOn.ftaylorSeriesWithin` to get the series of $f$ and $g$ from the hypotheses `ContDiffOn` and `UniqueDiffOn`.
3. An `OrderedFinpartition n` is not an arbitrary list of blocks. Two orders of the same blocks are not two partitions, because `parts_strictMono` fixes the order. A count that treats the blocks as ordered freely gives the ordered Bell numbers $1, 1, 3, 13, 75$, not the Bell numbers.

### Exercises

1. (A) Use `iteratedDeriv_comp_two` to compute the second derivative of $x \mapsto e^{\sin x}$ at $0$, and check the result with the formula $(g \circ f)'' = g''(f) (f')^2 + g'(f) f''$.
2. (A) List the five ordered finpartitions of $3$. For each, give `length`, the values of `partSize` and the lists `emb m`, and check that `parts_strictMono` holds.
3. (B) Use `OrderedFinpartition.extendEquiv` to prove that the number of ordered finpartitions of $n + 1$ is $\sum_{c} (c.\mathrm{length} + 1)$, and compute it for $n + 1 = 4$.
4. (B) State in Lean the bound of Leibniz for $\|D^n (f g)(x)\|$ with $f, g : E \to \mathbb{R}$, and derive it from `ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_le_one` with $B$ the multiplication of $\mathbb{R}$.
5. (B) Let $f : \mathbb{R} \to \mathbb{R}$ be smooth with $\|D^i f(x)\| \le 1$ for $1 \le i \le n$. Use `norm_iteratedFDeriv_comp_le` to bound $\|D^n (\sin \circ f)(x)\|$, and give the value of the constant $C$.
6. (C) Prove $B_n \le n!$ for all $n$ from the recursion of exercise 3, and explain why this shows that the factor $n!$ in `norm_iteratedFDeriv_comp_le` follows from the formula of Faà di Bruno and `OrderedFinpartition.norm_compAlongOrderedFinpartition_le`.

### Reference

<?reference?>
