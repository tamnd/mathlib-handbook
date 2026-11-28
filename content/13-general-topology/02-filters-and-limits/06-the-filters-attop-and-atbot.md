---
title: The filters atTop and atBot
kind: api
modules:
  - Mathlib.Order.Filter.AtTopBot.Basic
  - Mathlib.Order.Filter.AtTopBot.Tendsto
  - Mathlib.Order.Filter.AtTopBot.Disjoint
  - Mathlib.Order.Filter.AtTopBot.Map
  - Mathlib.Order.Filter.AtTopBot.Prod
  - Mathlib.Order.Filter.AtTopBot.CompleteLattice
  - Mathlib.Order.Filter.AtTopBot.CountablyGenerated
  - Mathlib.Order.Filter.AtTopBot.Finite
  - Mathlib.Order.Filter.AtTopBot.Finset
  - Mathlib.Order.Filter.AtTopBot.Interval
  - Mathlib.Order.Filter.AtTopBot.BigOperators
  - Mathlib.Order.Filter.AtTopBot.Monoid
  - Mathlib.Order.Filter.AtTopBot.Group
  - Mathlib.Order.Filter.AtTopBot.Ring
  - Mathlib.Order.Filter.AtTopBot.Field
  - Mathlib.Order.Filter.AtTopBot.Archimedean
  - Mathlib.Order.Filter.AtTopBot.Floor
  - Mathlib.Order.Filter.AtTopBot.ModEq
explains:
  E2: [Filter.eventually_atTop, Filter.tendsto_atTop_mono, Filter.tendsto_atTop_atTop_of_monotone, Filter.extraction_of_frequently_atTop, Filter.tendsto_iff_seq_tendsto, Filter.prod_atTop_atTop_eq, Filter.Tendsto.atTop_add_atTop, Filter.Tendsto.atTop_mul_const, tendsto_natCast_atTop_atTop]
  E1: auto
families: []
requires: [V03, V04, V06, V13.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The filters atTop and atBot

### Overview

Section 1 defines the filter `Filter.atTop` on a preorder $\alpha$. Its sets are the sets that contain a tail $[a, \infty) = \{b : a \le b\}$. The filter `Filter.atBot` is the dual filter of the sets that contain $(-\infty, a]$. A sequence $u$ tends to $\ell$ when `Tendsto u atTop (𝓝 ℓ)`, and a real function tends to $+\infty$ at $+\infty$ when `Tendsto f atTop atTop`. So these two filters carry all the limits "at infinity" of classical analysis.

This section describes the library of results about these two filters. The results fall into three groups. The order results describe the sets of `atTop`, the limits of monotone maps, subsequences and products. The finite results describe `atTop` on `Finset α`, the filter of the partial sums of a series. The algebraic results are the rules "if $f \to +\infty$, then $f + c \to +\infty$", "$f g \to +\infty$" and so on, in ordered monoids, groups, rings and fields. The topology of $\mathbb{R}$ is not needed for any of them.

### The library around it

#### Sets, bases and the two words

The module `Mathlib.Order.Filter.AtTopBot.Basic` starts with the translations of "eventually" and "frequently". In a nonempty directed preorder,

$$\forall^{f} x \in \mathrm{atTop},\ p(x) \iff \exists a,\ \forall b \ge a,\ p(b), \qquad \exists^{f} x \in \mathrm{atTop},\ p(x) \iff \forall a,\ \exists b \ge a,\ p(b).$$

These are `Filter.eventually_atTop` and `Filter.frequently_atTop`. The proof of the first is one line: `Filter.atTop_basis` says that the intervals `Set.Ici a` form a basis, and a basis gives the membership criterion at once. The basis is even antitone, by `Filter.hasAntitoneBasis_atTop`, and the strict intervals also form a basis in an order without a maximum (`Filter.atTop_basis_Ioi`). The filter is proper if and only if the type is nonempty and directed (`Filter.atTop_neBot_iff`). In an order with a top element it is the principal filter of the top, `Filter.OrderTop.atTop_eq`, so it says nothing interesting there.

Each lemma has a mirror with `atBot`, `Iic` and `≥` replaced by `atTop`, `Ici` and `≤`. The library proves the `atBot` form by duality with `OrderDual`. A reader who finds one form can guess the name of the other.

The module `Mathlib.Order.Filter.AtTopBot.Disjoint` says that the two ends are far apart: `Filter.disjoint_atTop_atBot` in a nontrivial partial order, and `Filter.disjoint_pure_atTop`, which says that a constant does not tend to infinity in an order with no maximum. The lemma `Filter.disjoint_atTop_principal_Iic` says that a set bounded above is not large for `atTop`.

#### Limits of monotone maps

The basic criterion is `Filter.tendsto_atTop`: $f \to \infty$ along $l$ if and only if, for each $b$, eventually $b \le f(x)$. The module `Mathlib.Order.Filter.AtTopBot.Tendsto` derives the comparison rules.

**Proposition.** If $f \le g$ pointwise and $f \to \infty$ along $l$, then $g \to \infty$ along $l$.

*Proof.* Fix $b$. Eventually $b \le f(x)$, and $f(x) \le g(x)$, so eventually $b \le g(x)$. $\square$

This is `Filter.tendsto_atTop_mono`, and `Filter.tendsto_atTop_mono'` asks for $f \le g$ only eventually. A monotone map $f$ whose range is not bounded above tends to infinity, `Filter.tendsto_atTop_atTop_of_monotone`: given $b$, choose $a$ with $b \le f(a)$, and then $b \le f(a) \le f(x)$ for each $x \ge a$. A strictly monotone map of $\mathbb{N}$ into itself tends to infinity, `StrictMono.tendsto_atTop`. A monotone sequence tends to infinity as soon as a subsequence does, `Filter.tendsto_atTop_of_monotone_of_subseq`.

The converse facts give bounds. If $f \to \infty$, then for each $c$ eventually $c \le f(x)$ (`Filter.Tendsto.eventually_ge_atTop`), and the range is not bounded above (`Filter.not_bddAbove_of_tendsto_atTop`). A constant map does not tend to infinity in an order with no maximum (`Filter.not_tendsto_const_atTop`). The module `Mathlib.Order.Filter.AtTopBot.CompleteLattice` computes a supremum along a limit: if $f$ is monotone and $g \to \infty$, then $\sup_a f(g(a)) = \sup_b f(b)$, as `Monotone.ciSup_comp_tendsto_atTop` in a conditionally complete lattice and `Monotone.iSup_comp_tendsto_atTop` in a complete lattice.

#### Images and change of variables

A Galois connection moves `atTop` from one order to another. The lemma `Filter.map_atTop_eq_of_gc` says that $f_{*}\,\mathrm{atTop} = \mathrm{atTop}$ when $f$ is monotone and has an upper adjoint on a tail. On $\mathbb{N}$ this gives the shift rules `Filter.map_add_atTop_eq_nat` and `Filter.tendsto_add_atTop_iff_nat`: a sequence $u$ and the shifted sequence $n \mapsto u(n + k)$ have the same limits. The module `Mathlib.Order.Filter.AtTopBot.Map` gives the same statements for an order isomorphism, `OrderIso.map_atTop` and `OrderIso.tendsto_atTop_iff`, and for subtypes such as `Set.Ici a` (`Filter.map_val_Ici_atTop`).

#### Subsequences

The extraction lemmas build a strictly monotone $\varphi : \mathbb{N} \to \mathbb{N}$.

**Proposition.** If $P(n)$ holds for infinitely many $n$, then there is a strictly monotone $\varphi$ with $P(\varphi(n))$ for each $n$.

*Proof.* Choose $\varphi(0)$ with $P(\varphi(0))$. Given $\varphi(n)$, the frequently condition gives $m > \varphi(n)$ with $P(m)$. Put $\varphi(n + 1) = m$. $\square$

This is `Filter.extraction_of_frequently_atTop`. Its relatives `Filter.extraction_of_eventually_atTop` and `Filter.extraction_forall_of_eventually` choose one index for each element of a sequence of conditions, and `Filter.Tendsto.subseq_mem` chooses a subsequence that enters a given sequence of sets. In a linear order with no maximum, a sequence that tends to infinity has a strictly increasing subsequence (`Filter.strictMono_subseq_of_tendsto_atTop`), and it takes "record values" infinitely often: `Filter.high_scores` gives $n \ge N$ with $u(k) < u(n)$ for each $k < n$. These two lemmas are in `Mathlib.Order.Filter.AtTopBot.Finite`.

#### Sequences and countably generated filters

The module `Mathlib.Order.Filter.AtTopBot.CountablyGenerated` makes the link with Section 3. A filter is countably generated if it has a countable basis, as the neighbourhood filter of a point of a metric space has.

**Theorem.** Let $k$ be countably generated. Then $f$ tends to $l$ along $k$ if and only if $f \circ x$ tends to $l$ along `atTop` for each sequence $x$ that tends to $k$.

*Proof sketch.* One direction is the composition of limits. For the other, take a decreasing basis $(B_n)$ of $k$ and assume that $f$ does not tend to $l$. Then there is a set $V \in l$ such that the points $x$ with $f(x) \notin V$ meet each $B_n$. Choose $x_n \in B_n$ with $f(x_n) \notin V$. Then $x_n$ tends to $k$, and $f(x_n)$ does not tend to $l$. $\square$

This is `Filter.tendsto_iff_seq_tendsto`. The module also has `Filter.exists_seq_tendsto` (a proper countably generated filter is the limit of a sequence), `Filter.subseq_tendsto_of_neBot` (a sequence with a cluster point in this sense has a subsequence that tends to the filter) and `Filter.tendsto_of_subseq_tendsto`. The instance `Filter.atTop.isCountablyGenerated` says that `atTop` on a countable type is countably generated.

#### Products and Finset

The module `Mathlib.Order.Filter.AtTopBot.Prod` computes `atTop` on a product: `Filter.prod_atTop_atTop_eq` says $\mathrm{atTop} \times \mathrm{atTop} = \mathrm{atTop}$ on $\alpha \times \beta$ with the product order. The proof compares the bases: a tail $[(a, b), \infty)$ of the product is the product $[a, \infty) \times [b, \infty)$ of tails. So a double sequence tends to $\ell$ as $(m, n) \to \infty$ jointly if and only if it does so along the product filter. The diagonal $n \mapsto (n, n)$ tends to infinity (`Filter.tendsto_atTop_diagonal`).

On `Finset α`, ordered by inclusion, `atTop` is the filter of the sets that contain all large finite subsets. A series $\sum_i f(i)$ is summable in Mathlib when the partial sums $\sum_{i \in s} f(i)$ converge along this filter. The module `Mathlib.Order.Filter.AtTopBot.Finset` gives the main tools: `Filter.tendsto_finset_range` says that `Finset.range n` tends to infinity in `Finset ℕ`, `Filter.tendsto_atTop_finset_of_monotone` gives the same for each increasing sequence of finite sets that exhausts $\alpha$, and `Filter.atTop_finset_eq_iInf` writes the filter as $\bigsqcap_x \mathcal{P}(\{s : x \in s\})$. The module `Mathlib.Order.Filter.AtTopBot.BigOperators` compares the images of `atTop` under two families of finite sums, for instance `Function.Injective.map_atTop_finsetSum_eq` for a reindexing by an injective map. The module `Mathlib.Order.Filter.AtTopBot.Interval` says that the intervals `Finset.Icc a b` tend to infinity when $a \to -\infty$ and $b \to +\infty$ (`Finset.tendsto_Icc_atBot_prod_atTop`).

#### Algebra at infinity

The modules `Mathlib.Order.Filter.AtTopBot.Monoid`, `.Group`, `.Ring` and `.Field` hold the rules of computation. The names follow one pattern: `Filter.Tendsto.atTop_add_atTop` is the rule $f \to \infty,\ g \to \infty \implies f + g \to \infty$, and the name of each rule lists the limits of the two arguments. The table gives the main rules.

| Lean name | Statement |
|---|---|
| `Filter.Tendsto.atTop_add_atTop` | $f \to \infty$ and $g \to \infty$ give $f + g \to \infty$ in an ordered monoid |
| `Filter.Tendsto.atTop_add_nonneg` | $f \to \infty$ and $g \ge 0$ give $f + g \to \infty$ |
| `Filter.tendsto_atTop_add_const_right` | $f \to \infty$ gives $f + C \to \infty$ in an ordered group |
| `Filter.tendsto_atTop_add_left_of_le` | $C \le f$ and $g \to \infty$ give $f + g \to \infty$ |
| `Filter.tendsto_neg_atTop_atBot` | $x \mapsto -x$ sends $+\infty$ to $-\infty$ |
| `Filter.Tendsto.atTop_mul_atTop₀` | $f \to \infty$ and $g \to \infty$ give $f g \to \infty$ in an ordered semiring |
| `Filter.tendsto_pow_atTop` | $x^n \to \infty$ as $x \to \infty$, for $n \ne 0$ |
| `Filter.Tendsto.atTop_mul_const` | $f \to \infty$ and $r > 0$ give $f r \to \infty$ in an ordered field |
| `Filter.tendsto_const_mul_atTop_iff_pos` | $r f \to \infty$ if and only if $r > 0$, when $f \to \infty$ |
| `Filter.Tendsto.atTop_div_const` | $f \to \infty$ and $r > 0$ give $f / r \to \infty$ |

The proof of the sum rule shows the pattern. Fix $b$. Eventually $0 \le g(x)$ and eventually $b \le f(x)$. Then eventually $b = b + 0 \le f(x) + g(x)$, by the monotonicity of addition. The field rules need the positivity of $r$, because $r f \to -\infty$ when $r < 0$, and `Filter.Tendsto.atTop_mul_const_of_neg` states this case. A suffix `₀` marks the forms for rings with zero, such as `Filter.Tendsto.atTop_mul_atTop₀`, as opposed to the forms for ordered monoids.

The module `Mathlib.Order.Filter.AtTopBot.Archimedean` treats the casts. In an Archimedean ordered semiring, the cast $\mathbb{N} \to R$ tends to infinity (`tendsto_natCast_atTop_atTop`): given $b$, the Archimedean property gives $n$ with $b \le n$, and the cast is monotone. A sequence of natural numbers tends to infinity if and only if its cast does (`tendsto_natCast_atTop_iff`). The same module gives `atTop_hasCountableBasis_of_archimedean`: the tails $[n, \infty)$ with $n \in \mathbb{N}$ form a countable basis, so `atTop` on $\mathbb{R}$ is countably generated.

The two small modules give arithmetic facts. In `Mathlib.Order.Filter.AtTopBot.ModEq`, `Nat.frequently_modEq` says that each residue class modulo $n \ne 0$ is infinite, and `Nat.frequently_even` is the case of the even numbers. In `Mathlib.Order.Filter.AtTopBot.Floor`, `FloorSemiring.eventually_mul_pow_lt_factorial_sub` says that $a c^n < (n - d)!$ for all large $n$: the factorial beats each exponential. Its natural number form `Nat.eventually_pow_lt_factorial_sub` is in `Mathlib.Order.Filter.AtTopBot.Finite`.

#### Common errors

1. `Tendsto f atTop atTop` on an empty or non-directed type is true for a trivial reason, because `atTop` is then `⊥`. The lemmas `Filter.eventually_atTop` and `Filter.atTop_basis` ask for `[Nonempty α]` and a directed order for this reason.
2. The rule for a product of two maps that tend to infinity is `Filter.Tendsto.atTop_mul_atTop₀` in an ordered semiring. The name without `₀` is the rule for an ordered commutative monoid, written multiplicatively, and it does not apply to $\mathbb{R}$ with its multiplication.
3. On `Finset α` the filter `atTop` uses inclusion, not the cardinality. A sequence of finite sets of growing size need not tend to infinity: it must eventually contain each given element.

### Exercises

1. (A) Prove `Filter.tendsto_add_atTop_iff_nat` directly from `Filter.eventually_atTop`.
2. (A) Show that $n \mapsto n^2 - 5n$ tends to infinity in $\mathbb{Z}$, with `Filter.tendsto_atTop_mono'` and a lower bound valid for large $n$.
3. (B) Prove that a monotone sequence of reals with an unbounded subsequence tends to infinity, and compare the proof with `Filter.tendsto_atTop_of_monotone_of_subseq`.
4. (B) Show that $\mathrm{atTop} \times \mathrm{atTop} = \mathrm{atTop}$ on $\mathbb{N} \times \mathbb{N}$ by comparison of bases, and deduce that $(m, n) \mapsto m + n$ tends to infinity.
5. (B) Show that $n \mapsto \{0, 2, 4, \ldots, 2n\}$ does not tend to `atTop` in `Finset ℕ`, while $n \mapsto$ `Finset.range n` does.
6. (C) Prove `Filter.high_scores`: a sequence of reals that tends to infinity has infinitely many indices $n$ with $u(k) < u(n)$ for each $k < n$.

### Reference

<?reference?>
