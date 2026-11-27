---
title: Sums over the support, maps of the domain and multisets
kind: theory
modules:
  - Mathlib.Algebra.BigOperators.Finsupp.Basic
  - Mathlib.Data.Finsupp.Basic
  - Mathlib.Data.Finsupp.Multiset
explains:
  E3: [Finsupp.sum, Finsupp.mapDomain, Finsupp.sum_add_index']
  E2: [Finsupp.prod, Finsupp.sum_single_index, Finsupp.sum_of_support_subset, Finsupp.sum_fintype, Finsupp.sum_single, Finsupp.prod_add_index, Finsupp.mapDomain_single, Finsupp.mapDomain_add, Finsupp.mapDomain_comp, Finsupp.mapDomain_injective, Finsupp.sum_mapDomain_index, Finsupp.toMultiset, Finsupp.count_toMultiset, Finsupp.card_toMultiset, Multiset.toFinsupp]
  E1: auto
families: []
requires: [V03.C02, V03.C06]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V03/C07/Examples.lean
  - MathlibHandbook/V03/C07/Exercises.lean
  - MathlibHandbook/V03/C07/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Sums over the support, maps of the domain and multisets

### Overview

A finitely supported function $f : X \to_0 M$ carries a finite set, its support. So a sum $\sum_x g(x, f(x))$ over all points of $X$ makes sense when $g(x, 0) = 0$: the terms outside the support are zero, and the sum is the finite sum over the support. This one operation gives the evaluation of a polynomial at a number, the value $\sum_i c_i v_i$ of a linear combination, the number $\prod_p p^{e_p}$ of a factorization and the size of a multiset.

The first part of this section defines the sum and the product over the support and proves the two rules that make them useful: the sum over a single and the sum over a sum $f + g$. The second part moves the points of a finitely supported function along a map $\varphi : X \to Y$. This is the map of the domain, and it adds the values of the points that $\varphi$ sends to the same point. The third part identifies the finitely supported functions $X \to_0 \mathbb{N}$ with the multisets of Chapter 2: a multiset is the function that counts each element.

The main theorem in words: the sum over the support is additive in $f$ when $g$ is additive in its second argument.

### Definitions

**Definition (Sum over the support).** Let $M$ have a zero, let $N$ be an additive commutative monoid, let $f \in X \to_0 M$ and let $g : X \times M \to N$. The *sum of $g$ over $f$* is $$f.\mathrm{sum}(g) = \sum_{x \in \operatorname{supp}(f)} g(x, f(x)).$$ For a commutative monoid $N$ in multiplicative notation, the product $f.\mathrm{prod}(g) = \prod_{x \in \operatorname{supp}(f)} g(x, f(x))$ is the same construction.

The definition sums only over the support, so it is a finite sum for each $g$. The value of $g$ at a point $(x, 0)$ is never used. When $g(x, 0) = 0$ for each $x$, the sum is the sum of $g(x, f(x))$ over all $x$ for which the term is not zero, and the definition is the natural one. When $g(x, 0) \ne 0$, the sum ignores terms that are not zero, and most rules of this section fail. The hypothesis $g(x, 0) = 0$ in the theorems below comes from this point.

::: mathlib
`Finsupp.sum` · `Mathlib.Algebra.BigOperators.Finsupp.Basic`

`f.sum g` is `∑ a ∈ f.support, g a (f a)`. The function `g` has two arguments, the point and the value, because many uses need both: the evaluation of a polynomial uses $g(n, c) = c x^n$. The definition has no hypothesis on `g`. The hypotheses come in the lemmas, as `h a 0 = 0` or `∀ i, g i 0 = 0`. The product form is `Finsupp.prod`, and the attribute `to_additive` makes each lemma about `prod` into the lemma about `sum`.

<?decl Finsupp.sum?>
:::

::: mathlib
`Finsupp.prod` · `Mathlib.Algebra.BigOperators.Finsupp.Basic`

`f.prod g` is `∏ a ∈ f.support, g a (f a)`. The factorization of a natural number $n \ne 0$ is recovered as `n.factorization.prod (fun p e => p ^ e)`. Its hypotheses in the rules are `h a 0 = 1`, the unit of the product.

<?decl Finsupp.prod?>
:::

**Definition (Map of the domain).** Let $M$ be an additive commutative monoid, let $\varphi : X \to Y$ and let $f \in X \to_0 M$. The function $\varphi_* f \in Y \to_0 M$ is $$\varphi_* f = \sum_{x \in \operatorname{supp}(f)} \operatorname{single}(\varphi(x), f(x)).$$ Its value at $y \in Y$ is the sum of the values $f(x)$ over the points $x \in \operatorname{supp}(f)$ with $\varphi(x) = y$.

The formula for the value comes from the definition. The value of $\operatorname{single}(\varphi(x), f(x))$ at $y$ is $f(x)$ if $\varphi(x) = y$ and $0$ otherwise. So the value of the sum at $y$ is $\sum_{x \in \operatorname{supp}(f),\ \varphi(x) = y} f(x)$. The support of $\varphi_* f$ is contained in $\varphi(\operatorname{supp}(f))$, which is finite. The map of the domain is a push forward: the mass $f(x)$ at the point $x$ moves to the point $\varphi(x)$, and masses that land at the same point add.

::: mathlib
`Finsupp.mapDomain` · `Mathlib.Data.Finsupp.Basic`

`Finsupp.mapDomain φ f` is defined as `f.sum (fun a m => single (φ a) m)`, the formula of the definition. The value is `Finsupp.mapDomain_apply` in this sum form, and the support is `Finsupp.mapDomain_support`: it is a subset of `f.support.image φ`. The value at a point outside the range of `φ` is `0` by `Finsupp.mapDomain_of_notMem_range`. In linear algebra the same map, as a linear map, is `Finsupp.lmapDomain`.

<?decl Finsupp.mapDomain?>
:::

**Definition (Multiset of a function to $\mathbb{N}$).** For $f \in X \to_0 \mathbb{N}$, the multiset $\operatorname{ms}(f)$ is $\sum_{x \in \operatorname{supp}(f)} f(x) \cdot \{x\}$, where $\{x\}$ is the multiset with one element and $n \cdot s$ is the sum of $n$ copies of $s$. So $x$ occurs in $\operatorname{ms}(f)$ exactly $f(x)$ times.

::: mathlib
`Finsupp.toMultiset` · `Mathlib.Data.Finsupp.Multiset`

`Finsupp.toMultiset : (α →₀ ℕ) →+ Multiset α` is an additive monoid map, so `map_add` gives `toMultiset (f + g) = toMultiset f + toMultiset g`. The definition is `f.sum (fun a n => n • {a})`, the rule `Finsupp.toMultiset_apply`. The inverse is `Multiset.toFinsupp`, which needs `DecidableEq α` to count.

<?decl Finsupp.toMultiset?>
:::

### Theorems and proofs

**Theorem (Sum over a superset).** Let $f \in X \to_0 M$, let $S \subseteq X$ be finite with $\operatorname{supp}(f) \subseteq S$, and let $g(x, 0) = 0$ for each $x \in S$. Then $f.\mathrm{sum}(g) = \sum_{x \in S} g(x, f(x))$.

*Proof.* Split $S$ into the disjoint parts $\operatorname{supp}(f)$ and $S \setminus \operatorname{supp}(f)$. The sum over $S$ is the sum over the first part plus the sum over the second part. The sum over the first part is $f.\mathrm{sum}(g)$ by the definition. For $x$ in the second part, $f(x) = 0$, so the term is $g(x, 0) = 0$. So the sum over the second part is $0$. $\square$

::: mathlib
`Finsupp.sum_of_support_subset` · `Mathlib.Algebra.BigOperators.Finsupp.Basic`

The theorem in the form `f.support ⊆ s → (∀ i ∈ s, g i 0 = 0) → f.sum g = ∑ x ∈ s, g x (f x)`. The case of a finite type with `s = univ` is `Finsupp.sum_fintype`. These two lemmas change a sum over a support, which moves with `f`, into a sum over a fixed finset, where the rules of Chapter 6 apply.

<?decl Finsupp.sum_of_support_subset?>
:::

**Theorem (Sum over a single).** Let $a \in X$, $b \in M$, and let $g(a, 0) = 0$. Then $\operatorname{single}(a, b).\mathrm{sum}(g) = g(a, b)$.

*Proof.* The support of $\operatorname{single}(a, b)$ is a subset of $\{a\}$. Apply the theorem (Sum over a superset) with $S = \{a\}$. The hypothesis holds, because $g(a, 0) = 0$. The sum over $\{a\}$ is the single term $g(a, \operatorname{single}(a, b)(a)) = g(a, b)$. $\square$

The hypothesis is needed. Let $g(x, m) = m + 1$ on $\mathbb{N} \to_0 \mathbb{N}$, and take $b = 0$. Then $\operatorname{single}(a, 0) = 0$ has the empty support, so the sum is $0$. But $g(a, 0) = 1$.

::: mathlib
`Finsupp.sum_single_index` · `Mathlib.Algebra.BigOperators.Finsupp.Basic`

The statement `h a 0 = 0 → (single a b).sum h = h a b`. With `simp`, the hypothesis is often proved on the spot. The product form `Finsupp.prod_single_index` needs `h a 0 = 1`.

<?decl Finsupp.sum_single_index?>
:::

**Theorem (Additivity of the sum).** Let $M$ be an additive monoid and $N$ an additive commutative monoid. Let $g : X \times M \to N$ satisfy $g(x, 0) = 0$ and $g(x, m + m') = g(x, m) + g(x, m')$ for all $x, m, m'$. Then, for all $f, f' \in X \to_0 M$, $$(f + f').\mathrm{sum}(g) = f.\mathrm{sum}(g) + f'.\mathrm{sum}(g).$$

*Proof.* Let $S = \operatorname{supp}(f) \cup \operatorname{supp}(f')$. This finite set contains the supports of $f$, of $f'$ and of $f + f'$, by Theorem (Support of a sum) of Section 1. Apply the theorem (Sum over a superset) three times with this $S$. Then $$(f + f').\mathrm{sum}(g) = \sum_{x \in S} g(x, f(x) + f'(x)) = \sum_{x \in S} \big(g(x, f(x)) + g(x, f'(x))\big).$$ The second step uses the additivity of $g$ in the second argument. The sum of a sum of two terms over a finset is the sum of the two sums (Chapter 6). So the right side is $\sum_{x \in S} g(x, f(x)) + \sum_{x \in S} g(x, f'(x)) = f.\mathrm{sum}(g) + f'.\mathrm{sum}(g)$. $\square$

The proof shows the method of the whole section: move each sum to one fixed finset that contains all the supports, and then use the rules for sums over a finset.

::: mathlib
`Finsupp.sum_add_index'` · `Mathlib.Algebra.BigOperators.Finsupp.Basic`

The theorem with the hypotheses for all points: `(∀ a, h a 0 = 0) → (∀ a b₁ b₂, h a (b₁ + b₂) = h a b₁ + h a b₂) → (f + g).sum h = f.sum h + g.sum h`. The form without the prime, `Finsupp.sum_add_index`, asks the hypotheses only for the points of `f.support ∪ g.support`, and it needs `DecidableEq α` to form the union. Use the primed form when the hypotheses hold everywhere, which is the usual case. The product form is `Finsupp.prod_add_index`.

<?decl Finsupp.sum_add_index'?>
:::

**Theorem (Properties of the map of the domain).** Let $M$ be an additive commutative monoid, $\varphi : X \to Y$ and $\psi : Y \to Z$.

1. $\varphi_* \operatorname{single}(a, b) = \operatorname{single}(\varphi(a), b)$.
2. $\varphi_*(f + f') = \varphi_* f + \varphi_* f'$.
3. $(\mathrm{id})_* f = f$ and $(\psi \circ \varphi)_* f = \psi_*(\varphi_* f)$.
4. If $\varphi$ is injective, then $(\varphi_* f)(\varphi(x)) = f(x)$ for each $x$, and $\varphi_*$ is injective.

*Proof.* The map $\varphi_*$ is $f \mapsto f.\mathrm{sum}(g)$ with $g(x, m) = \operatorname{single}(\varphi(x), m)$. This $g$ satisfies $g(x, 0) = \operatorname{single}(\varphi(x), 0) = 0$, and it is additive in $m$ because $\operatorname{single}(y, m + m') = \operatorname{single}(y, m) + \operatorname{single}(y, m')$ (Example (Single is additive) of Section 1).

1. By the theorem (Sum over a single), $\varphi_* \operatorname{single}(a, b) = g(a, b) = \operatorname{single}(\varphi(a), b)$.
2. This is the theorem (Additivity of the sum) for this $g$.
3. For $\varphi = \mathrm{id}$, the definition gives $\sum_{x \in \operatorname{supp}(f)} \operatorname{single}(x, f(x))$, which is $f$ by Theorem (Decomposition) of Section 1. For the composition, both sides are additive in $f$ by part 2, and every $f$ is a finite sum of singles by the decomposition. So it is enough to check singles. By part 1, the left side is $\operatorname{single}(\psi(\varphi(a)), b)$, and the right side is $\psi_* \operatorname{single}(\varphi(a), b) = \operatorname{single}(\psi(\varphi(a)), b)$.
4. Let $\varphi$ be injective. The value of $\varphi_* f$ at $\varphi(x)$ is the sum of $f(x')$ over the $x' \in \operatorname{supp}(f)$ with $\varphi(x') = \varphi(x)$. By injectivity the only such $x'$ is $x$. If $x \in \operatorname{supp}(f)$, the sum is $f(x)$. If not, the sum is empty, so it is $0 = f(x)$. Now let $\varphi_* f = \varphi_* f'$. Then $f(x) = (\varphi_* f)(\varphi(x)) = (\varphi_* f')(\varphi(x)) = f'(x)$ for each $x$, and $f = f'$ by extensionality. $\square$

::: mathlib
`Finsupp.mapDomain_injective` · `Mathlib.Data.Finsupp.Basic`

The statement `Function.Injective φ → Function.Injective (mapDomain φ)`. The other parts of the theorem are `Finsupp.mapDomain_single`, `Finsupp.mapDomain_add`, `Finsupp.mapDomain_id` and `Finsupp.mapDomain_comp`. The rule for a sum over a pushed function, `Finsupp.sum_mapDomain_index`, says `(mapDomain φ s).sum h = s.sum (fun a m => h (φ a) m)` when `h` is zero at zero and additive.

<?decl Finsupp.mapDomain_injective?>
:::

**Theorem (Multisets and functions to $\mathbb{N}$).** For $f \in X \to_0 \mathbb{N}$ and $x \in X$, the number of times $x$ occurs in $\operatorname{ms}(f)$ is $f(x)$, and the size of $\operatorname{ms}(f)$ is $\sum_{x \in \operatorname{supp}(f)} f(x)$. The map $f \mapsto \operatorname{ms}(f)$ is a bijection from $X \to_0 \mathbb{N}$ onto the multisets of elements of $X$, and it sends $f + f'$ to $\operatorname{ms}(f) + \operatorname{ms}(f')$.

*Proof.* The count of $x$ in a multiset is additive: $\operatorname{count}_x(s + t) = \operatorname{count}_x(s) + \operatorname{count}_x(t)$ (Chapter 2). The count of $x$ in $n \cdot \{x'\}$ is $n$ if $x' = x$ and $0$ otherwise. So the count of $x$ in $\operatorname{ms}(f) = \sum_{x'} f(x') \cdot \{x'\}$ is the sum of $f(x')$ over the $x' \in \operatorname{supp}(f)$ with $x' = x$. This is $f(x)$, by the same argument as in part 4 above. The size is additive too, and the size of $n \cdot \{x'\}$ is $n$, so the size of $\operatorname{ms}(f)$ is $\sum_{x \in \operatorname{supp}(f)} f(x)$.

For the bijection, define the inverse. For a multiset $s$, let $c_s(x) = \operatorname{count}_x(s)$. Its support is the set of the elements of $s$, a finite set, so $c_s \in X \to_0 \mathbb{N}$. By the first part, $c_{\operatorname{ms}(f)}(x) = f(x)$ for each $x$, so $c_{\operatorname{ms}(f)} = f$. In the other direction, $\operatorname{ms}(c_s)$ and $s$ have the same count at each $x$, so they are equal, because a multiset is determined by its counts (Chapter 2). So the two maps are inverse to each other. The additivity holds because $\operatorname{ms}$ is $f \mapsto f.\mathrm{sum}(g)$ with $g(x, n) = n \cdot \{x\}$, which is zero at zero and additive in $n$. $\square$

::: mathlib
`Finsupp.count_toMultiset` · `Mathlib.Data.Finsupp.Multiset`

The statement `Multiset.count a (toMultiset f) = f a`. The size is `Finsupp.card_toMultiset`: `card (toMultiset f) = f.sum (fun _ => id)`. The inverse map `Multiset.toFinsupp` is an additive equivalence `Multiset α ≃+ (α →₀ ℕ)`, with the value `Multiset.toFinsupp_apply` and the two inverse laws `Finsupp.toMultiset_toFinsupp` and `Multiset.toFinsupp_toMultiset`.

<?decl Finsupp.count_toMultiset?>
:::

### Examples

**Example (The sum of a single).** For $g(x, m) = 2m$, the theorem (Sum over a single) gives $\operatorname{single}(a, b).\mathrm{sum}(g) = 2b$. The hypothesis $g(a, 0) = 0$ holds.

<?lean MathlibHandbook/V03/C07/Examples.lean#sum?>

**Example (The evaluation of a polynomial).** Let $p = \operatorname{single}(0, 3) + \operatorname{single}(5, 2) + \operatorname{single}(7, -1)$ represent $3 + 2X^5 - X^7$, and let $g(n, c) = c \cdot 2^n$. Then $g(n, 0) = 0$ and $g$ is additive in $c$. By additivity and the rule for a single, $$p.\mathrm{sum}(g) = 3 \cdot 2^0 + 2 \cdot 2^5 - 1 \cdot 2^7 = 3 + 64 - 128 = -61.$$ This is the value $p(2)$. The additivity of the sum is the rule $(p + q)(2) = p(2) + q(2)$.

**Example (A map of the domain).** Let $\varphi : \mathbb{N} \to \mathbb{N}$, $\varphi(n) = n \bmod 3$, and $f = \operatorname{single}(0, 1) + \operatorname{single}(3, 2) + \operatorname{single}(4, 5)$ in $\mathbb{N} \to_0 \mathbb{Z}$. By parts 1 and 2 of the theorem, $$\varphi_* f = \operatorname{single}(0, 1) + \operatorname{single}(0, 2) + \operatorname{single}(1, 5) = \operatorname{single}(0, 3) + \operatorname{single}(1, 5).$$ The points $0$ and $3$ go to $0$, and their values add. The map $\varphi$ is not injective, and indeed $\varphi_*$ is not injective: $\varphi_* \operatorname{single}(0, 1) = \varphi_* \operatorname{single}(3, 1)$.

**Example (A product over a factorization).** Let $e = \operatorname{single}(2, 3) + \operatorname{single}(3, 2) + \operatorname{single}(5, 1)$ and $h(p, k) = p^k$. Then $h(p, 0) = 1$ and $h(p, k + k') = h(p, k) h(p, k')$. The product rule for a sum gives $e.\mathrm{prod}(h) = 2^3 \cdot 3^2 \cdot 5^1 = 360$. The rule `Nat.factorization_prod_pow_eq_self` of the volume on numbers says that this product has the factorization $e$ again, when the support consists of primes.

**Counterexample (A function that is not additive).** Let $g(x, m) = m^2$ on $\mathbb{N} \to_0 \mathbb{Z}$, and $f = f' = \operatorname{single}(0, 1)$. Then $(f + f').\mathrm{sum}(g) = 2^2 = 4$, and $f.\mathrm{sum}(g) + f'.\mathrm{sum}(g) = 1 + 1 = 2$. So the theorem (Additivity of the sum) needs the additivity of $g$ in its second argument.

### Common errors

1. A learner forgets the hypothesis $g(x, 0) = 0$. Without it, the sum over the support is not the "sum over all points", and the rules for singles and for sums fail, as the example $g(x, m) = m + 1$ shows.
2. A learner expects $\operatorname{supp}(\varphi_* f) = \varphi(\operatorname{supp}(f))$. Only the inclusion holds, because values can cancel: in $\mathbb{N} \to_0 \mathbb{Z}$ with $\varphi(n) = 0$, the function $\operatorname{single}(1, 1) + \operatorname{single}(2, -1)$ maps to $0$.
3. A learner writes `f.sum (fun a => g a)` with a function of one argument. The function of `Finsupp.sum` takes the point and the value. For a sum of the values alone, write `f.sum (fun _ m => m)`.
4. A learner rewrites with `Finsupp.sum_add_index` and gets goals over `f.support ∪ g.support`. The primed form `Finsupp.sum_add_index'` gives goals for all points, which `simp` often closes.

### The library around it

The file `Mathlib.Algebra.BigOperators.Finsupp.Basic` has the API of `Finsupp.sum` and `Finsupp.prod`, made in pairs by `to_additive`. The rules on the left argument are `Finsupp.sum_zero_index`, `Finsupp.sum_single_index`, `Finsupp.sum_add_index'` and `Finsupp.sum_neg_index`. The rules on the right argument are `Finsupp.sum_add` (a sum of two functions $g_1 + g_2$) and `Finsupp.sum_comm` (two sums exchanged). The bridges to the sums over a fixed finset are `Finsupp.sum_of_support_subset` and `Finsupp.sum_fintype`. The rule `Finsupp.sum_single` is the decomposition of Section 1, and `Finsupp.univ_sum_single` is the same over a finite type. The rule `Finsupp.sum_ite_eq` picks the term at one point. The file `Mathlib.Data.Finsupp.Basic` has `Finsupp.mapDomain` with the rules `_single`, `_add`, `_zero`, `_id`, `_comp`, `_injective`, `_support` and `sum_mapDomain_index`, and it has the other constructions on the domain, for example `Finsupp.comapDomain` along an injective map and `Finsupp.subtypeDomain`. The file `Mathlib.Data.Finsupp.Multiset` has `Finsupp.toMultiset` and `Multiset.toFinsupp` with `Finsupp.toMultiset_single`, `Finsupp.toMultiset_add` and `Finsupp.toMultiset_sum_single`. The scalar multiplication `b • f` and its rule `Finsupp.sum_smul_index` are in `Mathlib.Data.Finsupp.SMul`. The linear forms of these maps, `Finsupp.lsum`, `Finsupp.lmapDomain` and `Finsupp.linearCombination`, are in the volume on linear algebra.

### Exercises

1. (A) Compute $f.\mathrm{sum}(g)$ for $f = \operatorname{single}(1, 4) + \operatorname{single}(2, -3)$ in $\mathbb{N} \to_0 \mathbb{Z}$ and $g(n, m) = n m$.
2. (A) Let $\varphi(n) = 2n$. Compute $\varphi_*(\operatorname{single}(1, 1) + \operatorname{single}(3, 2))$ and its value at $6$ and at $3$.
3. (A) Write the multiset of the prime factors of $360$, with multiplicity, and the corresponding function in $\mathbb{N} \to_0 \mathbb{N}$.
4. (B) Show that $f.\mathrm{sum}(g)$ with $g(x, m) = m$ is the sum of all values of $f$, and that it is additive in $f$ for $M = \mathbb{Z}$.
5. (B) Show that $\varphi_*$ keeps the sum of all values: $(\varphi_* f).\mathrm{sum}(\lambda y\, m.\ m) = f.\mathrm{sum}(\lambda x\, m.\ m)$. Hint: use `Finsupp.sum_mapDomain_index`, or check singles and use additivity.
6. (B) Prove the product rule: if $h(x, 0) = 1$ and $h(x, m + m') = h(x, m) h(x, m')$, then $(f + f').\mathrm{prod}(h) = f.\mathrm{prod}(h) \cdot f'.\mathrm{prod}(h)$. Hint: copy the proof of additivity.
7. (B) Give $\varphi$ and $f$ with $\varphi_* f = 0$ and $f \ne 0$, with values in $\mathbb{Z}$. Show that no such example exists with values in $\mathbb{N}$.
8. (C) Let $M$ be an additive commutative monoid. Show that a map $T : (X \to_0 M) \to N$ that is additive and satisfies $T(\operatorname{single}(x, m)) = g(x, m)$ for all $x, m$ equals $f \mapsto f.\mathrm{sum}(g)$. Conclude the universal property: additive maps out of $X \to_0 M$ are determined by their values on singles. Hint: use the theorem (Induction) of Section 1.

### Notes and history

The sum over the support is the formal form of the convention that a sum with almost all terms zero is a finite sum. The push forward of finitely supported functions along a map is the action of the free module construction on maps: a map of sets $X \to Y$ gives a linear map $R^{(X)} \to R^{(Y)}$, as in Lang, *Algebra*, Chapter III, §4.

In Mathlib, `Finsupp.sum` and `Finsupp.mapDomain` come from the Lean 3 file `data.finsupp` of Johannes Hölzl (2017), with later work of Kim Morrison and many others. The file `Mathlib.Data.Finsupp.Multiset` is also by Johannes Hölzl (2018).

### Reference

<?reference?>
