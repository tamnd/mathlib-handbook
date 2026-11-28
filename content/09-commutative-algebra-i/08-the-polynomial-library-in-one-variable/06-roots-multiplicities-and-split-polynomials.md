---
title: Roots, multiplicities and split polynomials
kind: api
modules:
  - Mathlib.Algebra.Polynomial.Roots
  - Mathlib.Algebra.Polynomial.Splits
  - Mathlib.Algebra.Polynomial.RuleOfSigns
  - Mathlib.Algebra.Polynomial.Sturm.Sequence
explains:
  E2: [Polynomial.roots_mul, Polynomial.count_roots, Polynomial.card_roots', Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C, Polynomial.zero_of_eval_zero, Polynomial.splits_iff_card_roots, Polynomial.Splits.eval_eq_prod_roots, Polynomial.Splits.nextCoeff_eq_neg_sum_roots_of_monic, Polynomial.roots_countP_pos_le_signVariations, Polynomial.dvd_of_mem_sturmSeq]
  E1: auto
families: []
requires: [V06.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Roots, multiplicities and split polynomials

### Overview

Section 5 defined the multiplicity of a root through division by $X - a$. Over a commutative domain $R$, the roots of a nonzero polynomial $p$ with their multiplicities form a finite multiset of size at most $\deg p$. The library stores this multiset as `Polynomial.roots`. Most facts about roots are statements about this multiset: the roots of a product are the sum of the multisets, and a polynomial with $\deg p$ roots is the product of its leading coefficient and the factors $X - a$.

A polynomial that is such a product is said to split. The file `Mathlib.Algebra.Polynomial.Splits` defines the predicate `Polynomial.Splits` for a polynomial over any semiring, and it gives the formulas for the value, the coefficients and the derivative of a split polynomial in terms of its roots. Two short files treat real roots: the rule of signs bounds the number of positive roots by the sign changes of the coefficients, and the Sturm sequence is a list of remainders that counts real roots.

### The library around it

#### The multiset of roots

For a commutative domain $R$ and $p \in R[X]$, `Polynomial.roots` $p$ is a `Multiset R`. For $p = 0$ it is empty, by `Polynomial.roots_zero`, although every element is a root of $0$. For $p \ne 0$, `Polynomial.mem_roots` says that $a \in \operatorname{roots}(p)$ exactly when $p(a) = 0$, and `Polynomial.count_roots` says that $a$ occurs in the multiset $\operatorname{rootMultiplicity}(a, p)$ times. The size bound is `Polynomial.card_roots'`: $\# \operatorname{roots}(p) \le \operatorname{natDegree}(p)$. The version `Polynomial.card_roots` for $p \ne 0$ uses `degree`.

The multiset comes from `Polynomial.exists_multiset_roots` of Section 5. Proof of that result: induction on the degree. If $p$ has no root, take the empty multiset. If $p(a) = 0$, write $p = (X - a) q$ with $\deg q = \deg p - 1$, take the multiset of $q$ and add $a$. The multiplicities add by `Polynomial.rootMultiplicity_mul`, so each count is right, and the size grows by one while the degree grows by one.

The rule for products is `Polynomial.roots_mul`: for $pq \ne 0$, $\operatorname{roots}(pq) = \operatorname{roots}(p) + \operatorname{roots}(q)$. Proof: two multisets are equal when each element has the same count in both. By `Polynomial.count_roots` the counts are root multiplicities, and these add by `Polynomial.rootMultiplicity_mul`. The same argument gives the rules for the basic polynomials.

| Lean name | Statement |
| --- | --- |
| `Polynomial.roots_X_sub_C` | $\operatorname{roots}(X - a) = \{a\}$ |
| `Polynomial.roots_C_mul` | a nonzero constant factor does not change the roots |
| `Polynomial.roots_pow` | $\operatorname{roots}(p^n) = n \cdot \operatorname{roots}(p)$ |
| `Polynomial.roots_multiset_prod_X_sub_C` | the roots of $\prod_{a \in s} (X - a)$ are $s$ |
| `Polynomial.roots_prod_X_sub_C` | the same for a finite set |
| `Polynomial.roots_comp_neg_X` | the roots of $p(-X)$ are the negatives of the roots of $p$ |
| `Polynomial.roots.le_of_dvd` | $p \mid q$ and $q \ne 0$ give $\operatorname{roots}(p) \le \operatorname{roots}(q)$ |
| `Polynomial.roots_ne_zero_iff_exists_isRoot` | for $p \ne 0$, the multiset is nonempty exactly when $p$ has a root |

#### Factoring out the roots

The product of the factors $X - a$ over the roots divides $p$: this is `Polynomial.prod_multiset_X_sub_C_dvd`, and `Multiset.prod_X_sub_C_dvd_iff_le_roots` says that $\prod_{a \in s} (X - a) \mid p$ exactly when $s \le \operatorname{roots}(p)$. The lemma `Polynomial.exists_prod_multiset_X_sub_C_mul` writes $p$ as this product times a cofactor $q$ that has no roots.

When $p$ has as many roots as its degree, the cofactor is a constant. `Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C` says: if $\# \operatorname{roots}(p) = \operatorname{natDegree}(p)$, then
$$p = \operatorname{lc}(p) \prod_{a \in \operatorname{roots}(p)} (X - a).$$
Proof: by `Polynomial.exists_prod_multiset_X_sub_C_mul`, $p = (\prod (X - a))\, q$ with $\# \operatorname{roots}(p) + \operatorname{natDegree}(q) = \operatorname{natDegree}(p)$. The hypothesis gives $\operatorname{natDegree}(q) = 0$, so $q$ is a constant. The product is monic, so the leading coefficient of $p$ is this constant.

#### Polynomial identities

A nonzero polynomial has finitely many roots, so a polynomial that vanishes on an infinite set is zero. `Polynomial.zero_of_eval_zero` says this for an infinite domain $R$: if $p(x) = 0$ for every $x \in R$, then $p = 0$. Proof: if $p \ne 0$, every element of $R$ lies in $\operatorname{roots}(p)$, whose size is at most $\operatorname{natDegree}(p)$. This contradicts that $R$ is infinite. The form `Polynomial.funext` says that two polynomials over an infinite domain with the same values are equal. For a finite set of roots there is `Polynomial.card_le_degree_of_subset_roots`, and `Polynomial.exists_eval_ne_zero_of_natDegree_lt_card` gives a nonzero value when the degree is less than the cardinality of $R$. Over a finite field the statement is false: $X^q - X$ vanishes on $\mathbb{F}_q$.

The roots of $X^n - a$ are `Polynomial.nthRoots` $n$ $a$, with `Polynomial.mem_nthRoots` for $0 < n$ and the bound `Polynomial.card_nthRoots`. The finite set `Polynomial.nthRootsFinset` is used for roots of unity. The lemma `Polynomial.nthRoots_two_eq_zero_iff` says that $a$ has no square root exactly when the multiset of square roots is empty.

#### Roots in an algebra

For $p \in T[X]$ and a domain $S$ that is a $T$-algebra, `Polynomial.aroots` $p$ $S$ is the multiset of roots of the image of $p$ in $S[X]$ (`Polynomial.aroots_def`). The set `Polynomial.rootSet` $p$ $S$ is the set of its elements (`Polynomial.rootSet_def`), and it is finite by `Polynomial.rootSet_finite`. For a torsion free algebra, `Polynomial.mem_aroots` and `Polynomial.mem_rootSet` say that $a$ is in it exactly when $p \ne 0$ and `aeval a p = 0`. Field theory uses `rootSet` for the roots of a polynomial in a splitting field.

The roots of an image along a ring map $f$ are the images of the roots when $p$ already has all its roots: `Polynomial.roots_map_of_injective_of_card_eq_natDegree` for injective $f$, and `Polynomial.Monic.roots_map_of_card_eq_natDegree` for monic $p$ and any $f$. The test `Polynomial.Monic.irreducible_iff_degree_lt` is the form over a domain of the test in Section 5.

#### Split polynomials

The predicate `Polynomial.Splits` $f$ says that $f$ is a product of a constant and monic polynomials of degree $1$. It is a property of $f$ alone. To say that $f \in K[X]$ splits over an extension $L$, write that the image `map (algebraMap K L) f` splits. Over a commutative ring, `Polynomial.splits_iff_exists_multiset` gives the explicit form: $f = C(\operatorname{lc} f) \prod_{a \in m} (X - a)$ for some multiset $m$.

The closure rules are `Polynomial.Splits.C`, `Polynomial.Splits.X_sub_C`, `Polynomial.Splits.mul`, `Polynomial.Splits.prod` and `Polynomial.Splits.map`. Over a domain, a divisor of a nonzero split polynomial splits (`Polynomial.Splits.of_dvd`), and `Polynomial.splits_prod_iff` says that a product of nonzero factors splits exactly when each factor splits. In low degree there are direct tests: `Polynomial.Splits.of_degree_le_one` over a division semiring, and `Polynomial.Splits.of_degree_eq_two` for a quadratic polynomial with one root in a field.

Over a domain, splitting is a count of roots. `Polynomial.splits_iff_card_roots` says that $f$ splits exactly when $\# \operatorname{roots}(f) = \operatorname{natDegree}(f)$. Proof: if $f = C(c) \prod_{a \in m} (X - a)$, then $\operatorname{roots}(f) = m$ by `Polynomial.roots_C_mul` and `Polynomial.roots_multiset_prod_X_sub_C`, and the degree is $\# m$. Conversely, `Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C` gives the factorization. The form `Polynomial.Splits.natDegree_eq_card_roots` is the forward direction.

For a split polynomial over a domain the roots determine everything:

| Lean name | Statement |
| --- | --- |
| `Polynomial.Splits.eval_eq_prod_roots` | $f(x) = \operatorname{lc}(f) \prod_{a} (x - a)$ |
| `Polynomial.Splits.coeff_zero_eq_prod_roots_of_monic` | for monic $f$, $f_0 = (-1)^n \prod_a a$ |
| `Polynomial.Splits.nextCoeff_eq_neg_sum_roots_of_monic` | for monic $f$, $f_{n-1} = -\sum_a a$ |
| `Polynomial.Splits.eval_derivative` | the value of $f'$ as a sum of products over the roots |
| `Polynomial.Splits.eval_derivative_div_eval_of_ne_zero` | $f'(x)/f(x) = \sum_a 1/(x - a)$ over a field |
| `Polynomial.Splits.dvd_iff_roots_le_roots` | over a field, $f \mid g$ exactly when $\operatorname{roots}(f) \le \operatorname{roots}(g)$ |
| `Polynomial.Splits.degree_eq_one_of_irreducible` | an irreducible split polynomial over a field has degree $1$ |

Proof of `Polynomial.Splits.eval_eq_prod_roots`: by `Polynomial.splits_iff_card_roots` and `Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C`, $f = C(\operatorname{lc} f) \prod (X - a)$. Evaluation at $x$ is a ring map, so it sends the product to $\operatorname{lc}(f) \prod (x - a)$. Proof of `Polynomial.Splits.nextCoeff_eq_neg_sum_roots_of_monic`: expand $\prod_{i=1}^n (X - a_i)$. The coefficient of $X^{n-1}$ comes from the choice of one constant $-a_i$ and $n - 1$ factors $X$, so it is $-\sum_i a_i$. The formulas for all coefficients by elementary symmetric functions are in Chapter 5.

A split polynomial of nonzero degree has a root, chosen by `Polynomial.rootOfSplits`, with `Polynomial.eval_rootOfSplits`. For a map of fields $i \colon R \to S$, `Polynomial.Splits.roots_map` says that the roots of the image are the images of the roots, and `Polynomial.Splits.of_splits_map` brings splitting back to $R$ when all roots of the image lie in the range of $i$.

#### The rule of signs

For a polynomial $P$ over a linearly ordered ring, `Polynomial.signVariations` $P$ is the number of sign changes in the list of its nonzero coefficients, read from `Polynomial.coeffList`. The theorem `Polynomial.roots_countP_pos_le_signVariations` says that the number of positive roots of $P$, counted with multiplicity, is at most this number. Proof: the key step is `Polynomial.succ_signVariations_le_X_sub_C_mul`. For $\eta > 0$ and $P \ne 0$, the product $(X - \eta) P$ has at least one more sign change than $P$. Then induct on the positive roots: each positive root $\eta$ gives $P = (X - \eta) Q$, and $Q$ has one positive root less and at least one sign change less. The lemmas `Polynomial.signVariations_C_mul` and `Polynomial.signVariations_neg` say that a nonzero constant factor does not change the count. With `Polynomial.roots_comp_neg_X` the same bound holds for negative roots and the coefficients of $P(-X)$.

#### Sturm sequences

The file `Mathlib.Algebra.Polynomial.Sturm.Sequence` defines `Polynomial.sturmSeq` $p$ $q$ over a field. It is the list of remainders of a Euclidean algorithm with a change of sign. `Polynomial.sturmSeq_cons` says that for $p \ne 0$ the list is $p$ followed by `sturmSeq q (-p % q)`, and `Polynomial.sturmSeq_zero_left` says that the list for $p = 0$ is empty. So the list starts with $p$ (`Polynomial.head?_sturmSeq`), and no element is zero (`Polynomial.ne_zero_of_mem_sturmSeq`).

The lemma `Polynomial.dvd_of_mem_sturmSeq` says that a common divisor $d$ of $p$ and $q$ divides every element of the list. Proof: induction with `Polynomial.sturmSeq.induct`. If $d \mid p$ and $d \mid q$, then $d$ divides $-p \% q = -(p - q\,(p / q))$, so the hypothesis holds for the next pair. The lemma `Polynomial.sturmSeq_mul_left` says that multiplying $p$ and $q$ by $r \ne 0$ multiplies every element by $r$. With $q = p'$, the last element of the list is a greatest common divisor of $p$ and $p'$, and the sign changes of the list at two points count the distinct real roots between them.

#### Common errors

1. Expecting `Polynomial.mem_roots` for $p = 0$. The roots of $0$ are the empty multiset, so the lemma needs $p \ne 0$.
2. Writing a splitting statement over an extension without `map`. The predicate `Polynomial.Splits` has no ring map argument. For $f \in K[X]$ and an extension $L$, the statement is that `map (algebraMap K L) f` splits.
3. Using `Polynomial.roots` over a ring that is not a domain. The definition needs `IsDomain R`. Over $\mathbb{Z}/8$, the polynomial $X^2 - 1$ has four roots, and no multiset of size $2$ describes them.

### Exercises

1. (A) Compute `Polynomial.roots` of $(X - 1)^2 (X + 2)$ over $\mathbb{Z}$ with `Polynomial.roots_mul` and `Polynomial.roots_pow`.
2. (A) Use `Polynomial.zero_of_eval_zero` to show that $X^2 + X$ is not zero as a function on $\mathbb{Z}$, and explain why it is zero as a function on $\mathbb{Z}/2$.
3. (B) Show with `Polynomial.splits_iff_card_roots` that $X^2 - 2$ splits over $\mathbb{R}$ but not over $\mathbb{Q}$.
4. (B) Let $f$ be monic and split of degree $n$ over a field. Use `Polynomial.Splits.nextCoeff_eq_neg_sum_roots_of_monic` to show that the sum of the roots of $f(X + c)$ is the sum of the roots of $f$ minus $nc$.
5. (B) Show with `Polynomial.roots_countP_pos_le_signVariations` that $X^5 + X^3 + X - 1$ has exactly one positive real root.
6. (C) Prove with `Polynomial.dvd_of_mem_sturmSeq` that for a nonzero $p$ every element of `sturmSeq p (derivative p)` is divisible by $\gcd(p, p')$.

### Reference

<?reference?>
