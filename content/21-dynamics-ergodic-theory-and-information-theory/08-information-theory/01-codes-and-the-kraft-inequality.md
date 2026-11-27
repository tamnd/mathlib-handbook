---
title: Codes and the Kraft-McMillan inequality
kind: theory
modules:
  - Mathlib.InformationTheory.Coding.PrefixFree
  - Mathlib.InformationTheory.Coding.UniquelyDecodable
  - Mathlib.InformationTheory.Coding.Kraft
  - Mathlib.InformationTheory.Coding.KraftMcMillan
explains:
  E3: [InformationTheory.IsPrefixFree, InformationTheory.IsUniquelyDecodable, InformationTheory.IsPrefixFree.finsetSum_one_div_card_pow_length_le_one, InformationTheory.IsUniquelyDecodable.finsetSum_one_div_card_pow_length_le_one]
  E2: [InformationTheory.IsPrefixFree.isUniquelyDecodable, InformationTheory.IsPrefixFree.isUniquelyDecodable_of_nontrivial, InformationTheory.IsUniquelyDecodable.epsilon_notMem, InformationTheory.IsUniquelyDecodable.flatten_injective, InformationTheory.IsPrefixFree.tsum_one_div_card_pow_length_le_one, InformationTheory.IsPrefixFree.summable_one_div_card_pow_length, InformationTheory.IsPrefixFree.anti]
  E1: auto
families: []
requires: [V03, V15]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Codes and the Kraft-McMillan inequality

### Overview

A source emits symbols, and a code writes each symbol as a word over an alphabet of $D$ letters. A good code uses short words for frequent symbols, but a receiver must still decode the concatenated words. The inequality of Kraft and McMillan bounds the lengths: if the code is uniquely decodable, then $\sum_w D^{-|w|} \le 1$. With Gibbs' inequality it gives the lower bound of Shannon for the average length, the entropy of the source divided by $\log D$. This section proves the inequality for prefix-free codes by counting, and for uniquely decodable codes by the power trick of Karush. It proves the converse and the bounds on the average length on paper, and says which parts the index has.

### Definitions

Let $\alpha$ be a finite alphabet with $D \ge 1$ letters. A *word* is a finite list of letters, $|w|$ is its length, $[\,]$ is the empty word, and $uv$ is the concatenation. A *code* is a set $S$ of words.

**Definition (Prefix-free code).** A word $u$ is a *prefix* of $v$ if $v = uw$ for some word $w$. A code $S$ is *prefix-free* if, for $u, v \in S$, $u$ a prefix of $v$ implies $u = v$.

**Definition (Uniquely decodable code).** A code $S$ is *uniquely decodable* if for all finite sequences $(u_1, \ldots, u_r)$ and $(v_1, \ldots, v_s)$ of words of $S$, $u_1 \cdots u_r = v_1 \cdots v_s$ implies $r = s$ and $u_i = v_i$ for all $i$.

A uniquely decodable code does not contain $[\,]$, because $[\,] = [\,][\,]$ gives two decodings. A prefix-free code without $[\,]$ is uniquely decodable: the first word of a decoding is the unique word of $S$ that is a prefix of the string, so a decoder reads the words one by one from the left.

::: mathlib
`InformationTheory.IsPrefixFree` · `Mathlib.InformationTheory.Coding.PrefixFree`

For `S : Set (List α)`, `IsPrefixFree S` is `∀ x ∈ S, ∀ y ∈ S, x <+: y → x = y`, with the prefix relation `<+:` of lists. The implication to unique decodability is `IsPrefixFree.isUniquelyDecodable`, with the hypothesis `[] ∉ S`, and `IsPrefixFree.isUniquelyDecodable_of_nontrivial` replaces it by `S.Nontrivial`. A subset of a prefix-free code is prefix-free (`IsPrefixFree.anti`).

<?decl InformationTheory.IsPrefixFree?>
:::

::: mathlib
`InformationTheory.IsUniquelyDecodable` · `Mathlib.InformationTheory.Coding.UniquelyDecodable`

`IsUniquelyDecodable S` says: for `L₁ L₂ : List (List α)` with all entries in `S`, `L₁.flatten = L₂.flatten → L₁ = L₂`. The lemma `IsUniquelyDecodable.epsilon_notMem` is $[\,] \notin S$, and `IsUniquelyDecodable.flatten_injective` restates the definition as injectivity on the lists of words of `S`.

<?decl InformationTheory.IsUniquelyDecodable?>
:::

### Theorems and proofs

**Theorem (Kraft inequality).** If $S$ is a finite prefix-free code, then $\sum_{w \in S} D^{-|w|} \le 1$.

*Proof.* Let $\ell$ be the largest length of a word of $S$. A word $w \in S$ has exactly $D^{\ell - |w|}$ extensions $wz$ of length $\ell$. If a word of length $\ell$ extends both $w$ and $w'$, then one of $w, w'$ is a prefix of the other, so $w = w'$. Thus the sets of extensions are disjoint subsets of the $D^\ell$ words of length $\ell$, and $\sum_{w \in S} D^{\ell - |w|} \le D^\ell$. Divide by $D^\ell$. $\square$

The same bound holds for an infinite prefix-free code, because each finite subcode is prefix-free and the partial sums are bounded by $1$.

**Theorem (McMillan inequality).** If $S$ is a finite uniquely decodable code, then $K = \sum_{w \in S} D^{-|w|} \le 1$.

*Proof.* If $S = \emptyset$, then $K = 0$. Otherwise let $\ell \ge 1$ be the largest length; $\ell \ge 1$ because $[\,] \notin S$. For $r \ge 1$, expand the power:
$$K^r = \sum_{(w_1, \ldots, w_r) \in S^r} D^{-(|w_1| + \cdots + |w_r|)} = \sum_{m=1}^{r\ell} a_m D^{-m},$$
where $a_m$ is the number of sequences of total length $m$. The map $(w_1, \ldots, w_r) \mapsto w_1 \cdots w_r$ is injective, by unique decodability, and it sends these sequences to words of length $m$. So $a_m \le D^m$ and $K^r \le r\ell$. If $K > 1$, then $K^r$ grows exponentially and $r \ell$ only linearly, a contradiction for large $r$. $\square$

A prefix-free code with $[\,] \in S$ is $S = \{[\,]\}$, with sum $1$. So the theorem of McMillan implies the theorem of Kraft.

::: mathlib
`InformationTheory.IsUniquelyDecodable.finsetSum_one_div_card_pow_length_le_one` · `Mathlib.InformationTheory.Coding.KraftMcMillan`

For `S : Finset (List α)` with `[Fintype α] [Nonempty α]` and `IsUniquelyDecodable ↑S`, the conclusion is `∑ w ∈ S, (1 / Fintype.card α : ℝ) ^ w.length ≤ 1`. The proof is the power trick. The older name `kraft_mcmillan_inequality` is a deprecated alias.

<?decl InformationTheory.IsUniquelyDecodable.finsetSum_one_div_card_pow_length_le_one?>
:::

::: mathlib
`InformationTheory.IsPrefixFree.finsetSum_one_div_card_pow_length_le_one` · `Mathlib.InformationTheory.Coding.Kraft`

The same sum bound for a finite prefix-free code. Mathlib derives it from McMillan's theorem, with the case $S = \{[\,]\}$ apart, as in the remark above. For an arbitrary set `S`, `IsPrefixFree.summable_one_div_card_pow_length` gives summability and `IsPrefixFree.tsum_one_div_card_pow_length_le_one` the bound on the `tsum`.

<?decl InformationTheory.IsPrefixFree.finsetSum_one_div_card_pow_length_le_one?>
:::

**Theorem (Converse of Kraft).** Let $D \ge 2$ and $\ell_1 \le \cdots \le \ell_n$ with $\sum_i D^{-\ell_i} \le 1$. Then there is a prefix-free code with distinct words $c_1, \ldots, c_n$ and $|c_i| = \ell_i$.

*Proof.* Put $s_i = \sum_{j < i} D^{-\ell_j}$. Then $s_i$ is a multiple of $D^{-\ell_i}$, because $\ell_j \le \ell_i$, and $s_i < 1$. So $s_i = 0.d_1 \cdots d_{\ell_i}$ in base $D$, with $\ell_i$ digits; let $c_i = d_1 \cdots d_{\ell_i}$. The real numbers with expansions that start with $c_i$ form the interval $[s_i, s_i + D^{-\ell_i})$. For $i < k$, $s_k \ge s_i + D^{-\ell_i}$, so $c_i$ is not a prefix of $c_k$. $\square$

The index of this edition has no declaration for this converse.

**Definition (Entropy of a distribution).** For a probability vector $p = (p_1, \ldots, p_n)$, the *Shannon entropy* is $H(p) = \sum_i -p_i \log p_i$, with $0 \log 0 = 0$.

**Theorem (Source coding bounds).** Let $c$ be an injective map from $\{1, \ldots, n\}$ to a uniquely decodable code, with lengths $\ell_i = |c(i)|$. Then $\sum_i p_i \ell_i \ge H(p) / \log D$. For $D \ge 2$, some prefix-free code has $\sum_i p_i \ell_i < H(p)/\log D + 1$.

*Proof.* Put $r_i = D^{-\ell_i}$. By McMillan, $\sum_i r_i \le 1$. With $\log x \le x - 1$, summed over the $i$ with $p_i > 0$,
$$H(p) - \log D \sum_i p_i \ell_i = \sum_{p_i > 0} p_i \log \frac{r_i}{p_i} \le \sum_{p_i > 0} (r_i - p_i) \le 0.$$
For the second claim, drop the symbols with $p_i = 0$ and take $\ell_i = \lceil -\log_D p_i \rceil$. Then $D^{-\ell_i} \le p_i$, so the sum of the $D^{-\ell_i}$ is at most $1$, and the converse of Kraft gives a prefix-free code. Its average length is less than $\sum_i p_i(-\log_D p_i + 1) = H(p)/\log D + 1$. $\square$

::: mathlib
`Real.negMulLog` · `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`

`Real.negMulLog x = -x * log x`, with the value $0$ at $0$ (`Real.negMulLog_def`), so $H(p) = \sum_i$ `negMulLog (p i)`. The library has `Real.concaveOn_negMulLog`, and for two symbols `Real.binEntropy` with `Real.binEntropy_le_log_two`. The index of this edition has no declaration for the entropy of a general distribution and no declaration for the source coding theorem of Shannon.

<?decl Real.negMulLog?>
:::

### Examples

**Example (A code that attains the bound).** Let $S = \{0, 10, 110, 111\}$ over $\{0, 1\}$, for the probabilities $(1/2, 1/4, 1/8, 1/8)$. It is prefix-free, and its Kraft sum is $1/2 + 1/4 + 1/8 + 1/8 = 1$. The entropy in bits is $\frac12 \cdot 1 + \frac14 \cdot 2 + 2 \cdot \frac18 \cdot 3 = 1.75$, and the average length is $1.75$ too. The lower bound is an equality because each $p_i$ is a power of $1/2$.

**Example (Unique decodability without the prefix property).** The code $\{0, 01\}$ is not prefix-free. It is uniquely decodable: no word is a suffix of the other, so a decoder reads the words one by one from the right. Its Kraft sum is $3/4$.

**Counterexample (A code that is not uniquely decodable).** The code $\{0, 1, 01\}$ has $01 = 0 \cdot 1$, two decodings of one string. Its Kraft sum is $5/4 > 1$, so McMillan's theorem excludes it from the start.

### The library around it

The files of `Mathlib.InformationTheory.Coding` work with `List α` and `Fintype α`, and state the sums with the real number `1 / Fintype.card α`. They have no notion of a source or of an expected length.

Common errors of a learner:

- McMillan's theorem is stated for a `Finset`. The form with `tsum` for an infinite code exists only for prefix-free codes.
- `IsPrefixFree` allows the code `{[]}`. Unique decodability needs `[] ∉ S`.
- The name `UniquelyDecodable` without `Is` is a deprecated alias.

### Exercises

1. (A) Show that each code of words of one fixed length is prefix-free.
2. (A) Show that a suffix-free code without $[\,]$ is uniquely decodable.
3. (B) Let $D = 1$, with the letter $a$. Show that the nonempty uniquely decodable codes are the sets $\{a^m\}$ with $m \ge 1$, and check McMillan's theorem and its converse in this case.
4. (B) Show that equality holds in the lower bound of the source coding theorem if and only if $p_i = D^{-\ell_i}$ for all $i$.
5. (B) Let $S$ be a finite prefix-free code over $D$ letters with Kraft sum $1$. Show that each infinite sequence of letters starts with exactly one word of $S$.
6. (C) Encode blocks of $k$ independent symbols of law $p$, with the product law on $n^k$ blocks. Show that the optimal average length per symbol tends to $H(p)/\log D$ as $k \to \infty$. Hint: $H$ of the product law is $k H(p)$.

### Notes and history

Shannon founded information theory in 1948 in *A Mathematical Theory of Communication*, with the source coding theorem. Kraft proved the inequality for prefix-free codes in his master's thesis of 1949. McMillan extended it to uniquely decodable codes in 1956, and Karush gave the short proof with powers in 1961.

### Reference

<?reference?>
