---
title: Encodable types and primitive recursion
kind: theory
modules:
  - Mathlib.Logic.Encodable.Basic
  - Mathlib.Logic.Encodable.Lattice
  - Mathlib.Logic.Encodable.Pi
  - Mathlib.Computability.Primrec.Basic
  - Mathlib.Computability.Primrec.List
  - Mathlib.Computability.Ackermann
explains:
  E3: [Encodable, Encodable.encode_injective, Encodable.decode₂, Encodable.choose, Encodable.skolem, Nat.Primrec, Primcodable, Primrec, Primrec₂, PrimrecPred, Primrec.nat_iff, Primrec.of_graph, Nat.Primrec', Nat.Primrec'.prim_iff, ack, ack_three, exists_lt_ack_of_nat_primrec, not_primrec₂_ack, computable₂_ack]
  E2: [Encodable.encodek, Encodable.ofLeftInjection, Encodable.ofEquiv, Encodable.ofCountable, Encodable.choose_spec, Encodable.encode_prod_val, Encodable.encodeSum, Encodable.iUnion_decode₂, Encodable.fintypeArrow, Nat.Primrec.add, Nat.Primrec.mul, Nat.Primrec.pred, Primcodable.prim, Primcodable.prod, Primcodable.list, Primrec.comp, Primrec.nat_rec, Primrec.nat_div, Primrec.nat_findGreatest, Primrec.PrimrecBounded, Primrec.list_foldl, Primrec.list_append, Primrec.nat_strong_rec, PrimrecPred.exists_lt, Primrec.nat_sqrt, ack_two, add_lt_ack, ack_succ_right_le_ack_succ_left, ack_ack_lt_ack_max_add_two, ack_pair_lt, ack_add_one_sq_lt_ack_add_three, not_nat_primrec_ack_self, Nat.Partrec.Code.pappAck, Nat.Partrec.Code.eval_pappAck]
  E1: auto
families: []
requires: [V01.C01, V02.C01, V03.C02, V03.C08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Encodable types and primitive recursion

### Overview

Computability theory studies functions on the natural numbers, but programs act on lists, pairs and codes. An encodable type is a type with an injection into $\mathbb{N}$ and a partial inverse. Mathlib states each computability notion on $\mathbb{N}$ first and moves it to other types through such encodings.

The first notion is primitive recursion. A primitive recursive function on $\mathbb{N}$ is built from zero, the successor and the projections of a pairing function, with pairing, composition and primitive recursion. Addition, multiplication, division with remainder, the integer square root and the usual list operations are primitive recursive. The Ackermann function is computable, but it grows faster than each primitive recursive function, so primitive recursion does not capture all algorithms. The next section adds unbounded search.


### Definitions

**Definition (Encodable type).** An encodable type is a type $\alpha$ with maps $\mathrm{encode} : \alpha \to \mathbb{N}$ and $\mathrm{decode} : \mathbb{N} \to \mathrm{Option}\ \alpha$ such that $\mathrm{decode}(\mathrm{encode}\ a) = \mathrm{some}\ a$ for each $a$.

The map decode need not be total, and a number $n$ can decode to some $a$ with $\mathrm{encode}\ a \neq n$. The function $\mathrm{decode}_2\ n$ is $\mathrm{some}\ a$ exactly when $\mathrm{encode}\ a = n$; in Mathlib it is `(decode n).bind (Option.guard fun a => encode a = n)`.

Finite types, $\mathbb{N}$ and $\mathbb{Z}$ are encodable, and so are products, sums, options, sigma types, lists, and functions from a finite type to an encodable type. The encodings are explicit:

- On a sum, $\mathrm{inl}\ a \mapsto 2\,\mathrm{encode}\ a$ and $\mathrm{inr}\ b \mapsto 2\,\mathrm{encode}\ b + 1$.
- On $\mathrm{Option}\ \alpha$, $\mathrm{none} \mapsto 0$ and $\mathrm{some}\ a \mapsto \mathrm{encode}\ a + 1$.
- On a product, $(a, b) \mapsto \mathrm{pair}(\mathrm{encode}\ a, \mathrm{encode}\ b)$.

Here $\mathrm{pair} : \mathbb{N} \times \mathbb{N} \to \mathbb{N}$ is the bijection
$$\mathrm{pair}(a, b) = \begin{cases} b^2 + a & a < b, \\ a^2 + a + b & a \geq b, \end{cases}$$
and $\mathrm{unpair}$ is its inverse. The pairs with $\max(a, b) = k$ fill the interval $[k^2, k^2 + 2k]$, so $\mathrm{pair}$ is a bijection. The function $\mathrm{unpair}$ uses the integer square root: $\mathrm{unpair}(n) = (n - s^2, s)$ if $n - s^2 < s$, and $(s, n - s^2 - s)$ otherwise, where $s = \lfloor \sqrt{n} \rfloor$.

**Definition (Primitive recursive function on $\mathbb{N}$).** The predicate $\mathrm{Primrec}$ on functions $\mathbb{N} \to \mathbb{N}$ is the least predicate with these properties.

1. The constant function $0$, the successor $n \mapsto n + 1$, and the two projections $n \mapsto (\mathrm{unpair}\ n).1$ and $n \mapsto (\mathrm{unpair}\ n).2$ are primitive recursive.
2. If $f$ and $g$ are primitive recursive, then so is $n \mapsto \mathrm{pair}(f n, g n)$.
3. If $f$ and $g$ are primitive recursive, then so is $f \circ g$.
4. If $f$ and $g$ are primitive recursive, then so is the function $h$ with $h(\mathrm{pair}(z, 0)) = f(z)$ and $h(\mathrm{pair}(z, y + 1)) = g(\mathrm{pair}(z, \mathrm{pair}(y, h(\mathrm{pair}(z, y)))))$.

This is the unary form: each function takes one number, and pairing packs several arguments into one. Mathlib also has the classical $n$-ary form and proves that the two forms agree.

**Definition (Primcodable type).** A primcodable type is an encodable type $\alpha$ such that the map $n \mapsto \mathrm{encode}(\mathrm{decode}\ n)$ from $\mathbb{N}$ to $\mathbb{N}$ is primitive recursive. The value uses the encoding of $\mathrm{Option}\ \alpha$.

The condition is necessary. An arbitrary encodable structure can hide a hard problem: an injection of $\mathbb{N}$ into $\mathbb{N}$ that sends the codes of halting programs to even numbers turns the halting problem into a parity test. The primcodable condition makes the test "is $n$ a code" and the clean-up of $\mathrm{decode}$ primitive recursive, so the encoding cannot carry a hidden predicate.

**Definition (Primitive recursive function between primcodable types).** Let $\alpha$ and $\sigma$ be primcodable. A function $f : \alpha \to \sigma$ is primitive recursive if the function $n \mapsto \mathrm{encode}((\mathrm{decode}\ n).\mathrm{map}\ f)$ on $\mathbb{N}$ is primitive recursive. A function of two arguments is primitive recursive if its uncurried form on $\alpha \times \beta$ is. A predicate $p$ on $\alpha$ is primitive recursive if it is decidable and the function $a \mapsto \mathrm{decide}(p\,a) : \alpha \to \mathrm{Bool}$ is primitive recursive.

**Definition (Ackermann function).** The Ackermann function $\mathrm{ack} : \mathbb{N} \to \mathbb{N} \to \mathbb{N}$ is given by
$$\mathrm{ack}(0, n) = n + 1, \quad \mathrm{ack}(m + 1, 0) = \mathrm{ack}(m, 1), \quad \mathrm{ack}(m + 1, n + 1) = \mathrm{ack}(m, \mathrm{ack}(m + 1, n)).$$
The recursion is on the pair $(m, n)$ in the lexicographic order, which is a well-order, so $\mathrm{ack}$ is total.

### Theorems and proofs

**Proposition (Encode is injective).** For an encodable type, $\mathrm{encode}$ is injective.

*Proof.* If $\mathrm{encode}\ a = \mathrm{encode}\ b$, then $\mathrm{some}\ a = \mathrm{decode}(\mathrm{encode}\ a) = \mathrm{decode}(\mathrm{encode}\ b) = \mathrm{some}\ b$, so $a = b$. $\square$

Conversely, if $f : \beta \to \alpha$ has a partial inverse $g$ with $g(f b) = \mathrm{some}\ b$ and $\alpha$ is encodable, then $\beta$ is encodable with $\mathrm{encode}\ b = \mathrm{encode}(f b)$ and $\mathrm{decode}\ n = (\mathrm{decode}\ n).\mathrm{bind}\ g$. Each countable type is encodable, but only by a noncomputable construction.

**Theorem (Choice for encodable types).** Let $\alpha$ be encodable and $p$ a decidable predicate on $\alpha$. If $\exists x, p\,x$, then there is an explicit $x_0$ with $p\,x_0$. As a consequence, for an encodable family $\beta$ and a decidable relation $P$, the statement $\forall x, \exists y, P\,x\,y$ is equivalent to $\exists f, \forall x, P\,x\,(f x)$, without the axiom of choice.

*Proof.* Let $q(n)$ say "$\mathrm{decode}\ n = \mathrm{some}\ a$ with $p\,a$". It is decidable, and if $p\,a$ then $q(\mathrm{encode}\ a)$. So the linear search $n = 0, 1, 2, \ldots$ stops at the least $n$ with $q(n)$, and the decoded value $x_0$ satisfies $p$. For the second statement, let $f x$ be the element found for $P\,x$. The converse direction is trivial. $\square$

**Proposition (Basic primitive recursive functions).** Addition, truncated subtraction, multiplication, the predecessor and powers on $\mathbb{N}$ are primitive recursive.

*Proof.* The identity is $\mathrm{pair}(\mathrm{left}\ n, \mathrm{right}\ n)$, and the constant $k$ is the $k$-fold successor of $0$. Write $\langle z, y\rangle$ for $\mathrm{pair}(z, y)$. Addition is the recursion with base $z$ and step $\langle z, \langle y, r\rangle\rangle \mapsto r + 1$, the successor after two projections. The predecessor is the recursion with base $0$ and step $\langle z, \langle y, r\rangle\rangle \mapsto y$. Truncated subtraction is the recursion $z \mathbin{\dot-} (y + 1) = \mathrm{pred}(z \mathbin{\dot-} y)$. Multiplication is $z \cdot (y + 1) = z \cdot y + z$, and powers are $z^{y+1} = z^y \cdot z$. $\square$

**Theorem (Bounded graph).** Let $f : \alpha \to \mathbb{N}$. Suppose that $f$ is bounded by a primitive recursive function $g$, and that the relation $f(a) = b$ is primitive recursive. Then $f$ is primitive recursive.

*Proof.* For each $a$, the value $f(a)$ is the greatest $b \leq g(a)$ with $f(a) = b$, because there is exactly one such $b$. The bounded search "greatest $b \leq N$ with $R(a, b)$" is primitive recursive for a primitive recursive relation $R$: by recursion on $N$, the result at $N + 1$ is $N + 1$ if $R(a, N + 1)$ holds and the result at $N$ otherwise. Substitute $N = g(a)$. $\square$

Division is an application. The quotient $\lfloor x / y\rfloor$ is bounded by $x$, and for $y > 0$ the graph is $q \cdot y \leq x < (q + 1) \cdot y$, which is primitive recursive.

**Theorem (Equivalence of the two forms).** A function $f$ on vectors of natural numbers of length $n$ is primitive recursive in the classical $n$-ary sense if and only if it is primitive recursive in the unary sense on the primcodable type of vectors.

*Proof.* From $n$-ary to unary, induction on the constructors: the projection $v \mapsto v_i$ is a list lookup, composition builds the vector of values with cons, and the recursion on the head is the unary recursion with the tail as parameter. From unary to $n$-ary, it suffices that $\mathrm{pair}$ and $\mathrm{unpair}$ are $n$-ary primitive recursive. The first uses comparison, multiplication and addition, and the second uses the integer square root, a bounded search. $\square$

**Lemma (Ackermann values).** $\mathrm{ack}(1, n) = n + 2$, $\mathrm{ack}(2, n) = 2n + 3$ and $\mathrm{ack}(3, n) = 2^{n+3} - 3$.

*Proof.* Induction on $n$ in each case. $\mathrm{ack}(1, 0) = \mathrm{ack}(0, 1) = 2$ and $\mathrm{ack}(1, n + 1) = \mathrm{ack}(1, n) + 1$. $\mathrm{ack}(2, 0) = \mathrm{ack}(1, 1) = 3$ and $\mathrm{ack}(2, n + 1) = \mathrm{ack}(2, n) + 2$. $\mathrm{ack}(3, 0) = \mathrm{ack}(2, 1) = 5 = 2^3 - 3$ and $\mathrm{ack}(3, n + 1) = 2\,\mathrm{ack}(3, n) + 3 = 2^{n+4} - 3$. $\square$

**Lemma (Ackermann inequalities).** For all $m, n, k$:

1. $m + n < \mathrm{ack}(m, n)$, and $\mathrm{ack}$ is strictly increasing in each argument.
2. $\mathrm{ack}(m, n + 1) \leq \mathrm{ack}(m + 1, n)$.
3. $\mathrm{ack}(m, \mathrm{ack}(n, k)) < \mathrm{ack}(\max(m, n) + 2, k)$.
4. $(\mathrm{ack}(m, n) + 1)^2 \leq \mathrm{ack}(m + 3, n)$, and $\mathrm{ack}(m, \mathrm{pair}(n, k)) < \mathrm{ack}(m + 4, \max(n, k))$.

*Proof.* Items 1 and 4 are inductions like those of the lemma on values. Item 2: for $n = 0$ both sides are $\mathrm{ack}(m, 1)$. For $n + 1$, the right side is $\mathrm{ack}(m, \mathrm{ack}(m + 1, n))$. By item 1, $\mathrm{ack}(m + 1, n) > m + 1 + n \geq n + 1$, so $\mathrm{ack}(m + 1, n) \geq n + 2$, and monotonicity in the second argument gives $\mathrm{ack}(m, n + 2) \leq \mathrm{ack}(m, \mathrm{ack}(m + 1, n))$. Item 3: put $M = \max(m, n)$. Then $\mathrm{ack}(n, k) < \mathrm{ack}(M + 1, k)$, so $\mathrm{ack}(m, \mathrm{ack}(n, k)) < \mathrm{ack}(M, \mathrm{ack}(M + 1, k)) = \mathrm{ack}(M + 1, k + 1) \leq \mathrm{ack}(M + 2, k)$ by item 2. $\square$

**Theorem (Ackermann dominates primitive recursion).** For each primitive recursive $f : \mathbb{N} \to \mathbb{N}$ there is $m$ with $f(n) < \mathrm{ack}(m, n)$ for all $n$.

*Proof.* Induction on the derivation of $\mathrm{Primrec}\ f$.

- Zero: $0 < \mathrm{ack}(0, n)$. Take $m = 0$.
- Successor: $n + 1 < \mathrm{ack}(1, n) = n + 2$. Take $m = 1$.
- Projections: $(\mathrm{unpair}\ n).i \leq n < n + 1 = \mathrm{ack}(0, n)$. Take $m = 0$.
- Pairing: let $f < \mathrm{ack}(a, \cdot)$ and $g < \mathrm{ack}(b, \cdot)$, and put $M = \max(a, b)$. From the formula, $\mathrm{pair}(x, y) < (\max(x, y) + 1)^2$. Then $\mathrm{pair}(f n, g n) < (\mathrm{ack}(M, n) + 1)^2 \leq \mathrm{ack}(M + 3, n)$ by item 4. Take $m = M + 3$.
- Composition: $f(g n) < \mathrm{ack}(a, g n) < \mathrm{ack}(a, \mathrm{ack}(b, n)) < \mathrm{ack}(M + 2, n)$ by item 3. Take $m = M + 2$.
- Recursion: let $h$ be defined from $f < \mathrm{ack}(a, \cdot)$ and $g < \mathrm{ack}(b, \cdot)$, and put $c = M + 9$. First prove $h\langle z, y\rangle < \mathrm{ack}(c, z + y)$ by induction on $y$. For $y = 0$: $h\langle z, 0\rangle = f(z) < \mathrm{ack}(a, z) \leq \mathrm{ack}(c, z)$. For $y + 1$, let $r = h\langle z, y\rangle$, so $r < \mathrm{ack}(c, z + y)$ by induction. Then $h\langle z, y + 1\rangle = g\langle z, \langle y, r\rangle\rangle < \mathrm{ack}(b, \langle z, w\rangle) < \mathrm{ack}(b + 4, \max(z, w))$ with $w = \langle y, r\rangle$. If $z > w$, the bound is $\mathrm{ack}(b + 4, z) \leq \mathrm{ack}(c, z + y + 1)$. Otherwise it is $\mathrm{ack}(b + 4, \langle y, r\rangle) < \mathrm{ack}(b + 8, \max(y, r))$. If $y > r$, this is at most $\mathrm{ack}(c, z + y + 1)$. If $r \geq y$, then $\mathrm{ack}(b + 8, r) < \mathrm{ack}(c - 1, \mathrm{ack}(c, z + y)) = \mathrm{ack}(c, z + y + 1)$. This closes the induction. Finally $z + y \leq \langle z, y\rangle$ by the formula for $\mathrm{pair}$, so $h(p) < \mathrm{ack}(c, p)$ for each $p$. Take $m = c$. $\square$

**Corollary (Ackermann is not primitive recursive).** The function $n \mapsto \mathrm{ack}(n, n)$ is not primitive recursive. So $\mathrm{ack}$, as a function of two arguments, is not primitive recursive.

*Proof.* If $n \mapsto \mathrm{ack}(n, n)$ were primitive recursive, the theorem gives $m$ with $\mathrm{ack}(n, n) < \mathrm{ack}(m, n)$ for all $n$. At $n = m$ this says $\mathrm{ack}(m, m) < \mathrm{ack}(m, m)$, a contradiction. If $\mathrm{ack}$ were primitive recursive in two arguments, its composition with the diagonal $n \mapsto (n, n)$ would be primitive recursive. $\square$

**Theorem (Ackermann is computable).** The function $\mathrm{ack}$ is computable in the sense of the next section.

*Proof.* Put $c_0 = \mathrm{succ}$, and let $c_{m+1}$ be the code of the function $k$ with $k(0) = c_m(1)$ and $k(n + 1) = c_m(k(n))$, a primitive recursion whose step applies $c_m$. By induction, $c_m$ evaluates to $\mathrm{ack}(m, \cdot)$. The map $m \mapsto c_m$ is primitive recursive, because each step is a fixed combination of code constructors. So $\mathrm{ack}(m, n)$ is the evaluation of $c_m$ at $n$, and evaluation is partial recursive by the universal function theorem. $\square$

### Examples

**Example (Pairing).** From the formula, $\mathrm{pair}(0, 0) = 0$, $\mathrm{pair}(0, 1) = 1$, $\mathrm{pair}(1, 0) = 2$, $\mathrm{pair}(1, 1) = 3$, $\mathrm{pair}(0, 2) = 4$, $\mathrm{pair}(1, 2) = 5$, $\mathrm{pair}(2, 0) = 6$, $\mathrm{pair}(2, 1) = 7$ and $\mathrm{pair}(2, 2) = 8$. The pairs with maximum $2$ fill $[4, 8]$. To decode $n = 7$: $s = 2$, $n - s^2 = 3 \geq s$, so $\mathrm{unpair}(7) = (2, 3 - 2) = (2, 1)$.

**Example (Encodings of composite types).** The element $\mathrm{some}(\mathrm{inr}\ 3)$ of $\mathrm{Option}(\mathrm{Bool} \oplus \mathbb{N})$ has code $(2 \cdot 3 + 1) + 1 = 8$, and the pair $(1, 2) : \mathbb{N} \times \mathbb{N}$ has code $5$. The number $8$ decodes in $\mathbb{N} \times \mathbb{N}$ to $(2, 2)$, and in $\mathrm{Bool}$ to $\mathrm{none}$.

**Example (Ackermann values).** From the lemma, $\mathrm{ack}(2, 3) = 9$, $\mathrm{ack}(3, 2) = 2^5 - 3 = 29$ and $\mathrm{ack}(3, 3) = 61$. Next, $\mathrm{ack}(4, 0) = \mathrm{ack}(3, 1) = 13$ and $\mathrm{ack}(4, 1) = \mathrm{ack}(3, 13) = 2^{16} - 3 = 65533$. The value $\mathrm{ack}(4, 2) = 2^{65536} - 3$ has 19729 decimal digits.

**Example (Primitive recursive list functions).** On lists over a primcodable type, length, append, reverse, map, the folds, lookup by index, flatten and $\mathrm{range}$ are primitive recursive. So are course-of-values recursion on $\mathbb{N}$ and the bounded quantifiers $\exists k < n$ and $\forall k < n$ applied to a primitive recursive predicate.

### The library around it

::: mathlib
`Encodable` · `Mathlib.Logic.Encodable.Basic`

The class `Encodable α` has the fields `encode`, `decode` and `encodek`, and `Encodable.encode_injective` gives injectivity. The constructions are `Encodable.ofLeftInjection`, `Encodable.ofEquiv` and the noncomputable `Encodable.ofCountable`. `Encodable.encode_prod_val` and `Encodable.encodeSum` record the encodings of the text, and `Encodable.choose` with `Encodable.choose_spec` and `Encodable.skolem` give choice for decidable predicates.

<?decl Encodable?>
:::

::: mathlib
`Encodable.iUnion_decode₂` · `Mathlib.Logic.Encodable.Lattice`

This module turns a union over an encodable type into a union over $\mathbb{N}$: `Encodable.iUnion_decode₂` states that the union over `i : ℕ` and `b ∈ decode₂ β i` equals the union over `b`. Measure theory uses it to pass from countable families to sequences. `Mathlib.Logic.Encodable.Pi` gives instances such as `Encodable.fintypeArrow`.

<?decl Encodable.iUnion_decode₂?>
:::

::: mathlib
`Nat.Primrec` · `Mathlib.Computability.Primrec.Basic`

`Nat.Primrec : (ℕ → ℕ) → Prop` has the constructors `zero`, `succ`, `left`, `right`, `pair`, `comp` and `prec`. The recursion case is `unpaired fun z n => n.rec (f z) fun y IH => g (pair z (pair y IH))`, which is item 4 of the definition. The closure lemmas include `Nat.Primrec.add`, `Nat.Primrec.sub`, `Nat.Primrec.mul`, `Nat.Primrec.pred` and `Nat.Primrec.prec1`. The pairing function is `Nat.pair` in `Mathlib.Data.Nat.Pairing`, with `Nat.unpair`.

<?decl Nat.Primrec?>
:::

::: mathlib
`Primrec` · `Mathlib.Computability.Primrec.Basic`

`Primcodable α` extends `Encodable α` with the field `Primcodable.prim`, and instances such as `Primcodable.prod` and `Primcodable.list` cover the usual types. `Primrec`, `Primrec₂` and `PrimrecPred` are the predicates of the text, and `Primrec.nat_iff` identifies `Primrec` with `Nat.Primrec` on ℕ. The closure lemmas include `Primrec.comp`, `Primrec.nat_rec`, `Primrec.nat_div`, `Primrec.nat_findGreatest`, and `Primrec.of_graph` with `Primrec.PrimrecBounded`.

<?decl Primrec?>
:::

::: mathlib
`Nat.Primrec'` · `Mathlib.Computability.Primrec.List`

`Nat.Primrec'` is the classical form on `List.Vector ℕ n → ℕ`, and `Nat.Primrec'.prim_iff` is the equivalence theorem of the text. The module also has `Primrec.list_foldl`, `Primrec.list_append`, `Primrec.nat_strong_rec`, `PrimrecPred.exists_lt` and `Primrec.nat_sqrt`.

<?decl Nat.Primrec'?>
:::

::: mathlib
`exists_lt_ack_of_nat_primrec` · `Mathlib.Computability.Ackermann`

`ack` has the equations `ack_zero`, `ack_succ_zero`, `ack_succ_succ` and the values `ack_two`, `ack_three`. The inequalities are `add_lt_ack`, `ack_succ_right_le_ack_succ_left`, `ack_ack_lt_ack_max_add_two`, `ack_add_one_sq_lt_ack_add_three` and `ack_pair_lt`. `exists_lt_ack_of_nat_primrec` has the constants of the text, and `not_nat_primrec_ack_self` and `not_primrec₂_ack` are the corollaries. `computable₂_ack` uses `Nat.Partrec.Code.pappAck` and `Nat.Partrec.Code.eval_pappAck`.

<?decl exists_lt_ack_of_nat_primrec?>
:::

Common errors of a learner: The first error is to state a computability result for a type with only an `Encodable` instance; the library needs `Primcodable`. The second error is to read `decode` as an inverse of `encode`; it is only a left inverse, and `decode₂` is the right tool when each number must code at most one element. The third error is to apply `Primrec` to a curried function of two arguments; the correct predicate is `Primrec₂`. The fourth error is to forget that `PrimrecPred` contains a `DecidablePred` instance as data.

### Exercises

1. (A) Compute $\mathrm{pair}(3, 1)$, $\mathrm{pair}(1, 3)$ and $\mathrm{unpair}(20)$. Hint: $\mathrm{pair}(3, 1) = 9 + 3 + 1$; for $\mathrm{unpair}(20)$, $s = 4$.
2. (A) Show that the function $n \mapsto n!$ is primitive recursive. Hint: use the recursion $0! = 1$, $(y + 1)! = y! \cdot (y + 1)$ and the closure under multiplication.
3. (A) Compute $\mathrm{ack}(2, 10)$, $\mathrm{ack}(3, 4)$ and $\mathrm{ack}(1, 100)$ from the formulas.
4. (B) Show that the characteristic function of the set of primes is primitive recursive. Hint: $n$ is prime when $n \geq 2$ and no $d$ with $2 \leq d < n$ divides $n$; use the bounded quantifier and the remainder.
5. (B) Show that the predicate "$n$ is the code of an element", that is $\mathrm{decode}\ n \neq \mathrm{none}$, is primitive recursive on $\mathbb{N}$ for each primcodable type. Hint: it is $\mathrm{encode}(\mathrm{decode}\ n) \neq 0$.
6. (C) Show that there is a total computable function that is not primitive recursive by a diagonal argument on an enumeration of derivations. Hint: code the derivation trees by numbers and evaluate the $n$-th function at $n$.

### Notes and history

Gödel used primitive recursive functions in his incompleteness paper of 1931 to arithmetize syntax. Ackermann gave a computable function that is not primitive recursive in 1928, and the two-argument form used here is a later simplification. Kleene fixed the modern presentation in the 1930s.

The Mathlib files are by these authors, read from their headers: `Mathlib.Logic.Encodable.Basic` by Leonardo de Moura and Mario Carneiro, `Mathlib.Logic.Encodable.Lattice` by Floris van Doorn, `Mathlib.Logic.Encodable.Pi`, `Mathlib.Computability.Primrec.Basic` and `Mathlib.Computability.Primrec.List` by Mario Carneiro, and `Mathlib.Computability.Ackermann` by Violeta Hernández Palacios.

### Reference

<?reference?>
