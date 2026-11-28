---
title: "Multisets of multisets: bind, products, powersets and antidiagonals"
kind: api
modules:
  - Mathlib.Data.Multiset.Bind
  - Mathlib.Data.Multiset.Pi
  - Mathlib.Data.Multiset.Sections
  - Mathlib.Data.Multiset.Powerset
  - Mathlib.Data.Multiset.Antidiagonal
  - Mathlib.Data.Multiset.NatAntidiagonal
  - Mathlib.Data.Multiset.Sum
explains:
  E2: [Multiset.join, Multiset.mem_bind, Multiset.card_bind, Multiset.card_product, Multiset.mem_pi, Multiset.card_sections, Multiset.powerset_cons, Multiset.card_powersetCard, Multiset.mem_antidiagonal, Multiset.Nat.mem_antidiagonal]
  E1: auto
families: []
requires: [V01.C02, V03.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Multisets of multisets: bind, products, powersets and antidiagonals

### Overview

Many constructions on finite collections give a collection of collections, or take one apart. The flattening of a multiset of multisets, the bind of a multiset along a function, the product of two multisets, the dependent functions on a multiset, the choices of one element from each member, the sub multisets of a multiset and the ways to split a multiset into two parts all give multisets. The modules of this section define them on lists and pass them to the quotient.

Each construction has the same three kinds of rules: a membership rule, a rule for the card, and a rule for insertion with `::ₘ`. The rule for insertion is the step of a proof by `Multiset.induction_on`, and the finsets of Chapter 3 and the sums of Chapter 6 get their own rules from it. So the text gives the three rules for each construction, with the card rules as the main results.

### The library around it

#### Join and bind

For a multiset $S$ of multisets, `Multiset.join S` is the sum of the members of $S$: it is the fold of `+` with start $0$. The rules `Multiset.join_zero`, `Multiset.join_cons` and `Multiset.join_add` say that it sends $0$ to $0$, $s ::_m S$ to $s + \operatorname{join}(S)$ and sums to sums. An element is in the join if and only if it is in some member (`Multiset.mem_join`), and the card of the join is the sum of the cards (`Multiset.card_join`).

The bind of $s$ along $f : \alpha \to$ `Multiset β` is the join of the image: `Multiset.bind s f` $= \operatorname{join}(\operatorname{map}(f, s))$. It is the monad bind of Section 4. Its rules are

$$b \in \operatorname{bind}(s, f) \iff \exists a \in s,\ b \in f(a), \qquad |\operatorname{bind}(s, f)| = \sum_{a \in s} |f(a)|.$$

These are `Multiset.mem_bind` and `Multiset.card_bind`. The count of an element is a sum in the same way (`Multiset.count_bind`), and the product of a bind is a product of products (`Multiset.prod_bind`). The rules `Multiset.cons_bind` and `Multiset.add_bind` give the step of an induction, `Multiset.bind_singleton` says that a bind into singletons is a map, and `Multiset.bind_assoc` and `Multiset.bind_bind` give associativity and the exchange of two binds. A bind has no duplicate if and only if each $f(a)$ has none and the values at distinct members are disjoint (`Multiset.nodup_bind`).

#### Products and sigma

The product of $s$ and $t$ is `s ×ˢ t`, through the instance `Multiset.instSProd`, with the definition `Multiset.product`. It contains each pair $(a, b)$ as many times as the product of the counts. The rules are

$$p \in s \times t \iff p_1 \in s \text{ and } p_2 \in t, \qquad |s \times t| = |s| \cdot |t|.$$

These are `Multiset.mem_product` and `Multiset.card_product`. The product distributes over sums on both sides (`Multiset.add_product`, `Multiset.product_add`), and the swap of the pairs gives the product in the other order (`Multiset.map_swap_product`). The rule `Multiset.Nodup.product` says that a product of two multisets with no duplicate has none.

The dependent form is `Multiset.sigma s t`, for $t : (a : \alpha) \to$ `Multiset (σ a)`, with the rules `Multiset.mem_sigma`, `Multiset.card_sigma` and `Multiset.cons_sigma`. Its card is $\sum_{a \in s} |t(a)|$.

#### Dependent functions and sections

For a multiset $m$ and multisets $t(a)$ of values, `Multiset.pi m t` is the multiset of all dependent functions $f$ defined on the members of $m$ with $f(a) \in t(a)$. A function on a multiset has the type `(a : α) → a ∈ m → β a`, because it must be defined only on the members. The membership rule is

$$f \in \operatorname{pi}(m, t) \iff \forall a\ (h : a \in m),\ f(a, h) \in t(a).$$

This is `Multiset.mem_pi`, and `Multiset.card_pi` gives the card $\prod_{a \in m} |t(a)|$. The construction goes by insertion: `Multiset.Pi.cons` extends a function on $m$ to $a ::_m m$ with a value $b$ at $a$, and `Multiset.pi_cons` says that $\operatorname{pi}(a ::_m m, t)$ is the bind of $t(a)$ along these extensions. The rules `Multiset.Pi.cons_same` and `Multiset.Pi.cons_ne` give the value of an extension, and `Multiset.Nodup.pi` gives that the result has no duplicate when $m$ and each $t(a)$ have none. The finset `Finset.pi` of Chapter 3 is built on it.

The non dependent form is `Multiset.Sections S`, for $S$ a multiset of multisets: the multiset of all ways to choose one element from each member of $S$, each choice given as a multiset. The rules are `Multiset.sections_zero` ($\{0\}$), `Multiset.sections_cons` and `Multiset.mem_sections`. Its card is the product of the cards:

$$|\operatorname{Sections}(S)| = \prod_{s \in S} |s|.$$

This is `Multiset.card_sections`. The expansion of a product of sums, $\prod_i \sum_{a \in s_i} a = \sum_{c \in \operatorname{Sections}(S)} \prod c$, uses it (`Multiset.prod_map_sum` in the module on big operators).

#### Powersets

The multiset `Multiset.powerset s` holds all sub multisets of $s$, with one copy for each sublist of a list in the class of $s$. So $\{a, a\}$ has the powerset $\{0, \{a\}, \{a\}, \{a, a\}\}$, with two copies of $\{a\}$. The rules are

$$t \in \operatorname{powerset}(s) \iff t \le s, \qquad |\operatorname{powerset}(s)| = 2^{|s|}.$$

These are `Multiset.mem_powerset` and `Multiset.card_powerset`. The step rule is

$$\operatorname{powerset}(a ::_m s) = \operatorname{powerset}(s) + \operatorname{map}(a ::_m \cdot,\ \operatorname{powerset}(s)).$$

This is `Multiset.powerset_cons`: a sub multiset of $a ::_m s$ either leaves out the new copy of $a$ or contains it. The powerset has no duplicate if and only if $s$ has none (`Multiset.nodup_powerset`), and it is monotone and injective (`Multiset.powerset_mono`, `Multiset.powerset_injective`).

The multiset `Multiset.powersetCard n s` holds the sub multisets of card $n$. Its rules are `Multiset.mem_powersetCard` ($t \le s$ and $|t| = n$) and

$$|\operatorname{powersetCard}(n, s)| = \binom{|s|}{n}.$$

This is `Multiset.card_powersetCard`. The step `Multiset.powersetCard_cons` is the recursion of Pascal's triangle: the sub multisets of card $n + 1$ of $a ::_m s$ are those of $s$, and those of card $n$ of $s$ with $a$ added. The rule `Multiset.powersetCard_eq_empty` gives $0$ for $n > |s|$, and `Multiset.bind_powerset_len` says that the union over all $n$ of these is the powerset. The finset `Finset.powersetCard` of Chapter 3 is built on it.

#### Antidiagonals

The multiset `Multiset.antidiagonal s` holds the pairs $(t, u)$ of multisets with $t + u = s$, one pair for each sub multiset $t$ in the powerset. The rules are

$$x \in \operatorname{antidiagonal}(s) \iff x_1 + x_2 = s, \qquad |\operatorname{antidiagonal}(s)| = 2^{|s|}.$$

These are `Multiset.mem_antidiagonal` and `Multiset.card_antidiagonal`. With decidable equality, `Multiset.antidiagonal_eq_map_powerset` gives the pairs as $(s - t, t)$ for $t$ in the powerset. The rules `Multiset.antidiagonal_cons` and `Multiset.map_swap_antidiagonal` give the step and the symmetry.

For a natural number $n$, the multiset `Multiset.Nat.antidiagonal n` holds the pairs $(i, j)$ of natural numbers with $i + j = n$, each once:

$$x \in \operatorname{antidiagonal}(n) \iff x_1 + x_2 = n.$$

This is `Multiset.Nat.mem_antidiagonal`. The card is $n + 1$ (`Multiset.Nat.card_antidiagonal`), the multiset has no duplicate (`Multiset.Nat.nodup_antidiagonal`), and `Multiset.Nat.antidiagonal_succ` adds $(0, n + 1)$ to the image of the pairs for $n$ under $i \mapsto i + 1$. The antidiagonal finset of $\mathbb{N}$ in Chapter 6, the instance `Finset.Nat.instHasAntidiagonal`, is built on it, and it gives the sums $\sum_{i + j = n}$ in the products of power series.

#### Disjoint sums

The module `Mathlib.Data.Multiset.Sum` gives `Multiset.disjSum s t`, the multiset in $\alpha \oplus \beta$ with the elements of $s$ on the left and those of $t$ on the right. The rules are `Multiset.mem_disjSum`, `Multiset.inl_mem_disjSum`, `Multiset.inr_mem_disjSum` and `Multiset.card_disjSum` ($|s| + |t|$). The operation is monotone in both arguments (`Multiset.disjSum_mono`), and it has no duplicate when $s$ and $t$ have none (`Multiset.Nodup.disjSum`).

#### Common errors

1. A learner expects the powerset of a multiset to have no duplicate. The powerset of $\{a, a\}$ has two copies of $\{a\}$. Only a multiset with no duplicate has a powerset with none (`Multiset.nodup_powerset`).
2. A learner tries to apply an element of `Multiset.pi m t` to a point with no proof of membership. The functions take two arguments: the point $a$ and a proof $h : a \in m$.
3. A learner uses `Multiset.antidiagonal` for the pairs of natural numbers with a given sum. It is about the splits of a multiset. The pairs $(i, j)$ with $i + j = n$ are in `Multiset.Nat.antidiagonal n`.

### Exercises

1. (A) List the members of `Multiset.powerset {1, 1, 2}` with their counts, and check `Multiset.card_powerset`.
2. (A) Compute `Multiset.Nat.antidiagonal 3` and `Multiset.bind {1, 2} (fun n => Multiset.range n)`.
3. (B) Prove `Multiset.card_product` by `Multiset.induction_on` on $s$, with `Multiset.cons_product` and `Multiset.card_bind`.
4. (B) Use `Multiset.card_sections` to count the sections of $\{\{1, 2\}, \{3, 4, 5\}, \{6\}\}$, and list them.
5. (B) Prove $\sum_{n} |\operatorname{powersetCard}(n, s)| = 2^{|s|}$ from `Multiset.card_powersetCard`, `Multiset.bind_powerset_len` and `Multiset.card_powerset`.
6. (C) Use `Multiset.powersetCard_cons` and induction to prove Pascal's rule $\binom{m+1}{n+1} = \binom{m}{n+1} + \binom{m}{n}$ from the cards.

### Reference

<?reference?>
