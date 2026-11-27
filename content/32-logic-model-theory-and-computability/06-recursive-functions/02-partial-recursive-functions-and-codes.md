---
title: Partial recursive functions and codes
kind: theory
modules:
  - Mathlib.Computability.Partrec
  - Mathlib.Computability.PartrecCode
  - Mathlib.Computability.PartrecBasis
  - Mathlib.Logic.Godel.GodelBetaFunction
explains:
  E3: [Nat.rfind, Nat.Partrec, Partrec, Computable, Nat.Partrec.Code, Nat.Partrec.Code.eval, Nat.Partrec.Code.exists_code, Nat.Partrec.Code.evaln, Nat.Partrec.Code.eval_eq_rfindOpt, Nat.Partrec.Code.eval_part, Nat.Partrec.Code.smn, Nat.Partrec.Code.fixed_point, Nat.Partrec.Code.fixed_point₂, Nat.Partrec', Nat.beta, Nat.beta_unbeta_coe]
  E2: [Nat.rfind_spec, Nat.rfind_min, Nat.rfindOpt, Nat.Partrec.of_primrec, Nat.Partrec.none, Partrec₂, Computable₂, Primrec.to_comp, Partrec.comp, Partrec.rfind, Partrec.fix, Nat.Partrec.Code.curry, Nat.Partrec.Code.eval_curry, Nat.Partrec.Code.encodeCode, Nat.Partrec.Code.evaln_sound, Nat.Partrec.Code.evaln_complete, Nat.Partrec.Code.evaln_mono, Nat.Partrec.Code.primrec_evaln, Nat.Partrec'.part_iff, Nat.unbeta, Nat.coprime_mul_succ]
  E1: auto
families: []
requires: [V01.C01, V02.C02, V03.C08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Partial recursive functions and codes

### Overview

Primitive recursion gives only total functions, and it misses the Ackermann function. The missing operation is unbounded search: find the least $n$ with $f(a, n) = 0$. A search may run forever, so the new class consists of partial functions. Mathlib writes a partial function as `α →. σ`, a function into `Part σ`; an element of `Part σ` is a proposition, its domain, with a value for each proof of the domain.

The partial recursive functions are the closure of the basic functions under pairing, composition, primitive recursion and unbounded search. In the 1930s Church, Kleene and Turing showed that this class equals the class of functions computed by Turing machines and the class of functions definable in the lambda calculus. The Church-Turing thesis says that it is the class of all functions that an algorithm computes.

This section defines the class on $\mathbb{N}$ and on primcodable types, introduces codes, and proves the universal function theorem, the smn theorem and the recursion theorem. It ends with Gödel's beta function, which codes finite sequences with addition and multiplication only.

### Definitions

**Definition (Unbounded search).** Let $p : \mathbb{N} \to \mathrm{Part}\ \mathrm{Bool}$. The value $\mathrm{rfind}\ p$ is the least $n$ such that $p(n)$ is defined and true and $p(m)$ is defined and false for all $m < n$. If no such $n$ exists, $\mathrm{rfind}\ p$ is undefined.

The condition on smaller $m$ is essential. A machine computes $p(0), p(1), \ldots$ in order, and if $p(0)$ does not terminate, it never reaches $p(1)$.

**Definition (Partial recursive function on $\mathbb{N}$).** The predicate $\mathrm{Partrec}$ on partial functions $\mathbb{N} \to \mathrm{Part}\ \mathbb{N}$ is the least predicate with these properties.

1. The constant $0$, the successor and the two projections of $\mathrm{unpair}$ are partial recursive.
2. If $f$ and $g$ are partial recursive, then so is $n \mapsto \mathrm{pair}(f n, g n)$, defined when both values are defined.
3. If $f$ and $g$ are partial recursive, then so is $n \mapsto f(g(n))$, defined when $g(n)$ is defined and $f$ is defined at that value.
4. Primitive recursion, as in the previous section, with partial values.
5. If $f$ is partial recursive, then so is $\mathrm{pair}(a, \cdot)$-search: $a \mapsto \mathrm{rfind}(n \mapsto [f(\mathrm{pair}(a, n)) = 0])$.

**Definition (Partial recursive and computable functions on types).** Let $\alpha$ and $\sigma$ be primcodable. A partial function $f : \alpha \to \mathrm{Part}\ \sigma$ is partial recursive if the partial function $n \mapsto (\mathrm{decode}\ n).\mathrm{bind}(a \mapsto (f a).\mathrm{map}\ \mathrm{encode})$ on $\mathbb{N}$ is partial recursive. A total function $f : \alpha \to \sigma$ is computable if it is partial recursive as a partial function.

Thus computable means total and partial recursive.

**Definition (Codes).** The type $\mathrm{Code}$ is the inductive type with the constructors $\mathrm{zero}$, $\mathrm{succ}$, $\mathrm{left}$, $\mathrm{right}$, $\mathrm{pair}(c, d)$, $\mathrm{comp}(c, d)$, $\mathrm{prec}(c, d)$ and $\mathrm{rfind'}(c)$. The evaluation $\mathrm{eval} : \mathrm{Code} \to (\mathbb{N} \to \mathrm{Part}\ \mathbb{N})$ follows the constructors:

- $\mathrm{eval}\ \mathrm{zero} = 0$, $\mathrm{eval}\ \mathrm{succ}\ n = n + 1$, $\mathrm{eval}\ \mathrm{left}\ n = (\mathrm{unpair}\ n).1$, $\mathrm{eval}\ \mathrm{right}\ n = (\mathrm{unpair}\ n).2$;
- $\mathrm{eval}(\mathrm{pair}(c, d))\ n = \mathrm{pair}(\mathrm{eval}\ c\ n, \mathrm{eval}\ d\ n)$;
- $\mathrm{eval}(\mathrm{comp}(c, d))\ n = \mathrm{eval}\ d\ n \mathbin{>\!\!>\!\!=} \mathrm{eval}\ c$, so $d$ runs first;
- $\mathrm{eval}(\mathrm{prec}(c, d))$ is the primitive recursion with base $c$ and step $d$;
- $\mathrm{eval}(\mathrm{rfind'}(c))\ \mathrm{pair}(a, m)$ is the least $n \geq m$ with $\mathrm{eval}\ c\ \mathrm{pair}(a, n) = 0$, found by a search from $m$ upward.

The search $\mathrm{rfind'}$ starts at $m$ instead of $0$. A search from $0$ is $\mathrm{rfind'}$ composed with $a \mapsto \mathrm{pair}(a, 0)$.

Codes are numbers. The encoding sends $\mathrm{zero}, \mathrm{succ}, \mathrm{left}, \mathrm{right}$ to $0, 1, 2, 3$, and the compound codes to $4 + 4k + r$ with $r \in \{0, 1, 2, 3\}$ for the four other constructors, where $k$ is the pair of the codes of the parts or the code of the part:
$$\mathrm{pair}(c, d) \mapsto 4\langle c, d\rangle + 4, \quad \mathrm{comp}(c, d) \mapsto 4\langle c, d\rangle + 6, \quad \mathrm{prec}(c, d) \mapsto 4\langle c, d\rangle + 5, \quad \mathrm{rfind'}(c) \mapsto 4c + 7.$$
This is a bijection $\mathrm{Code} \simeq \mathbb{N}$, and $\mathrm{Code}$ is a denumerable type.

**Definition (Bounded evaluation).** For $k \in \mathbb{N}$, $\mathrm{evaln}\ k\ c\ n : \mathrm{Option}\ \mathbb{N}$ runs the code $c$ on $n$, but it fails as soon as an argument, or the depth of a recursion, reaches $k$. It is a total function, and $\mathrm{evaln}\ k\ c\ n = \mathrm{some}\ x$ means that $c$ computes $x$ on $n$ with all intermediate inputs below $k$.

**Definition (Classical basis).** The predicate $\mathrm{Partrec}'$ on partial functions $\mathbb{N}^n \to \mathrm{Part}\ \mathbb{N}$, for vectors of length $n$, is generated by the primitive recursive functions in the $n$-ary sense, by composition with $m$ functions, and by the search $v \mapsto \mathrm{rfind}(k \mapsto [f(k :: v) = 0])$ for a total $f$.

**Definition (Gödel's beta function).** For $n, i \in \mathbb{N}$, write $(a, b) = \mathrm{unpair}(n)$ and define
$$\beta(n, i) = a \bmod ((i + 1) b + 1).$$

### Theorems and proofs

**Theorem (Primitive recursive functions are partial recursive).** If $f$ is primitive recursive on $\mathbb{N}$, then $f$ is partial recursive. If $f : \alpha \to \sigma$ is primitive recursive, then $f$ is computable.

*Proof.* Each constructor of $\mathrm{Primrec}$ is a constructor of $\mathrm{Partrec}$, so the first claim is an induction. For types, $n \mapsto \mathrm{encode}((\mathrm{decode}\ n).\mathrm{map}\ f)$ is primitive recursive, with value $0$ when $\mathrm{decode}\ n = \mathrm{none}$ and $\mathrm{encode}(f a) + 1$ when $\mathrm{decode}\ n = \mathrm{some}\ a$. Composing with the partial predecessor, undefined at $0$, gives the function in the definition of $\mathrm{Partrec}$. The partial predecessor is the search for the least $m$ with $m + 1 = n$. $\square$

**Example (The empty function).** The partial function that is nowhere defined is partial recursive. It is $a \mapsto \mathrm{rfind}(n \mapsto [1 = 0])$, the search with the constant function $1$.

**Theorem (Codes describe the partial recursive functions).** A partial function $f : \mathbb{N} \to \mathrm{Part}\ \mathbb{N}$ is partial recursive if and only if $f = \mathrm{eval}\ c$ for some code $c$.

*Proof.* If $f$ is partial recursive, induction on the derivation produces a code: the four basic functions are the four atomic codes, pairing, composition and recursion are the three binary constructors, and the search from $0$ is $\mathrm{comp}(\mathrm{rfind'}(c), \mathrm{pair}(\mathrm{id}, \mathrm{zero}))$, with $\mathrm{id} = \mathrm{pair}(\mathrm{left}, \mathrm{right})$. Conversely, induction on $c$ shows that $\mathrm{eval}\ c$ is partial recursive. The only new case is $\mathrm{rfind'}$. On input $\mathrm{pair}(a, m)$ it is the search over $n$ of $\mathrm{eval}\ c\ \mathrm{pair}(a, n + m)$, followed by the addition of $m$. Both parts are partial recursive. $\square$

**Lemma (Bounded evaluation).** For all $k$, $c$, $n$, $x$:

1. if $\mathrm{evaln}\ k\ c\ n = \mathrm{some}\ x$, then $n < k$;
2. if $k \leq k'$ and $\mathrm{evaln}\ k\ c\ n = \mathrm{some}\ x$, then $\mathrm{evaln}\ k'\ c\ n = \mathrm{some}\ x$;
3. $x \in \mathrm{eval}\ c\ n$ if and only if $\mathrm{evaln}\ k\ c\ n = \mathrm{some}\ x$ for some $k$;
4. the map $(k, c, n) \mapsto \mathrm{evaln}\ k\ c\ n$ is primitive recursive.

*Proof.* Items 1 and 2 follow from the definition by induction on $k$ and $c$: each clause first checks $n \leq k - 1$, and a larger $k$ only removes failures. In item 3, soundness ($\Leftarrow$) compares each clause with the clause of $\mathrm{eval}$, by induction on $k$ and $c$. Completeness ($\Rightarrow$) is an induction on $c$: the values of the parts come with bounds $k_1, k_2$, and $\max(k_1, k_2, n + 1)$ works for the whole by item 2; for a recursion or a search, take the maximum over the finitely many steps. Item 4 is the technical core of the file. It is a course-of-values recursion on $(k, c)$ in which each step looks up earlier values in a list. $\square$

**Theorem (Kleene normal form).** For each code $c$ and each $n$,
$$\mathrm{eval}\ c\ n = \mathrm{rfindOpt}(k \mapsto \mathrm{evaln}\ k\ c\ n),$$
where $\mathrm{rfindOpt}\ g$ is the first value $\mathrm{some}\ x$ of the total function $g$, found by search.

*Proof.* Let $x \in \mathrm{eval}\ c\ n$. By item 3 there is $k$ with $\mathrm{evaln}\ k\ c\ n = \mathrm{some}\ x$, so the search terminates at the least $k_0$ with a value $\mathrm{some}\ y$. By item 3 again, $y \in \mathrm{eval}\ c\ n$, and a value of a partial function is unique, so $y = x$. Conversely, a value of the search is some $\mathrm{evaln}\ k\ c\ n$, and item 3 gives $x \in \mathrm{eval}\ c\ n$. $\square$

So each partial recursive function is one unbounded search applied to a primitive recursive function. Kleene's form adds a primitive recursive output function $U$ and a primitive recursive predicate $T$; here the $\mathrm{Option}$ value plays both roles.

**Corollary (Universal function).** The map $(c, n) \mapsto \mathrm{eval}\ c\ n$ is partial recursive.

*Proof.* By item 4 the function $(c, n, k) \mapsto \mathrm{evaln}\ k\ c\ n$ is primitive recursive, hence computable. The search $\mathrm{rfindOpt}$ preserves partial recursion. The normal form theorem identifies the result with $\mathrm{eval}$. $\square$

**Theorem (smn).** For a code $c$ and $n \in \mathbb{N}$, put $\mathrm{curry}(c, n) = \mathrm{comp}(c, \mathrm{pair}(\mathrm{const}\ n, \mathrm{id}))$. Then $\mathrm{curry}$ is computable, indeed primitive recursive, and $\mathrm{eval}(\mathrm{curry}(c, n))\ x = \mathrm{eval}\ c\ \mathrm{pair}(n, x)$.

*Proof.* The code $\mathrm{const}\ n$ is $\mathrm{succ}$ composed $n$ times with $\mathrm{zero}$, and $\mathrm{eval}(\mathrm{const}\ n)\ x = n$. Then $\mathrm{eval}(\mathrm{pair}(\mathrm{const}\ n, \mathrm{id}))\ x = \mathrm{pair}(n, x)$, and the composition applies $c$. The map $n \mapsto \mathrm{const}\ n$ is a primitive recursion on codes, and $\mathrm{curry}$ is a fixed combination of constructors, so it is primitive recursive. $\square$

**Theorem (Fixed point theorem).** Let $f : \mathrm{Code} \to \mathrm{Code}$ be computable. Then there is a code $c$ with $\mathrm{eval}(f c) = \mathrm{eval}\ c$.

*Proof.* Identify codes with numbers. Define the partial function $g(x, y) = \mathrm{eval}(\mathrm{eval}\ x\ x)\ y$, which runs program $x$ on its own code and then runs the result on $y$. It is partial recursive by the universal function theorem, so $g = \mathrm{eval}\ c_g$ on pairs for a code $c_g$. Define $F(x) = f(\mathrm{curry}(c_g, x))$. Then $F$ is computable, so $F = \mathrm{eval}\ c_F$ for a code $c_F$, with $\mathrm{eval}\ c_F\ x = F(x)$ for all $x$. Put $c = \mathrm{curry}(c_g, c_F)$. For each $y$,
$$\mathrm{eval}\ c\ y = g(c_F, y) = \mathrm{eval}(\mathrm{eval}\ c_F\ c_F)\ y = \mathrm{eval}(F(c_F))\ y = \mathrm{eval}(f(\mathrm{curry}(c_g, c_F)))\ y = \mathrm{eval}(f c)\ y.$$
The first equality is the smn theorem, and the third is the choice of $c_F$. $\square$

**Corollary (Second recursion theorem).** Let $f : \mathrm{Code} \to \mathbb{N} \to \mathrm{Part}\ \mathbb{N}$ be partial recursive in two arguments. Then there is a code $c$ with $\mathrm{eval}\ c = f(c)$.

*Proof.* The function $f$ is the evaluation of a code $c_f$ on pairs. The map $h(d) = \mathrm{curry}(c_f, d)$ is computable, and $\mathrm{eval}(h(d))\ n = f(d, n)$. The fixed point theorem gives $c$ with $\mathrm{eval}(h c) = \mathrm{eval}\ c$, so $\mathrm{eval}\ c\ n = f(c, n)$. $\square$

The next section uses the recursion theorem to prove Rice's theorem.

**Theorem (Equivalence with the classical basis).** A partial function $f$ on vectors of length $n$ satisfies $\mathrm{Partrec}'$ if and only if it is partial recursive on the primcodable type of vectors.

*Proof.* From $\mathrm{Partrec}'$, induct on the constructors: composition with $m$ partial functions binds the $m$ values in turn, and the search is the search of the definition with the vector as parameter. Conversely, the library shows that $\mathrm{Partrec}'$ is closed under head, tail, cons and binding of a partial value, and then translates each constructor of $\mathrm{Partrec}$; the search case uses $\mathrm{rfindOpt}$. $\square$

**Lemma (Coprime moduli).** If $(m - n) \mid a$, then $\gcd(na + 1, ma + 1) = 1$.

*Proof.* Let $p$ be a prime that divides $na + 1$ and $ma + 1$. Assume $m \geq n$; the other case is symmetric. Then $p$ divides the difference $(m - n) a$. The prime $p$ does not divide $a$, because $p \mid na + 1$. So $p \mid m - n$, and by the hypothesis $p \mid a$, a contradiction. $\square$

**Theorem (Beta function lemma).** For each finite sequence $(a_0, \ldots, a_{m-1})$ of natural numbers there is $n$ with $\beta(n, i) = a_i$ for all $i < m$.

*Proof.* Let $s = \max(m, a_0, \ldots, a_{m-1}) + 1$ and $b = s!$. The moduli are $d_i = (i + 1) b + 1$ for $i < m$. For $i < j < m$, the difference $j - i$ is at most $m < s$, so $j - i$ divides $s! = b$. By the lemma, $d_i$ and $d_j$ are coprime. By the Chinese remainder theorem there is $a$ with $a \equiv a_i \pmod{d_i}$ for all $i < m$. Each $a_i < s \leq b < d_i$, so $a \bmod d_i = a_i$. Put $n = \mathrm{pair}(a, b)$. Then $\mathrm{unpair}(n) = (a, b)$, and $\beta(n, i) = a \bmod ((i + 1) b + 1) = a_i$. $\square$

The function $\beta$ uses only pairing, multiplication, addition and the remainder, which are definable in the language $\{0, 1, +, \cdot\}$ with bounded quantifiers. So a formula of arithmetic can quantify over finite sequences through one number $n$.

### Examples

**Example (A search with an undefined value).** Let $p(0)$ be undefined and $p(n) = \mathrm{true}$ for $n \geq 1$. Then $\mathrm{rfind}\ p$ is undefined. If instead $p(0) = \mathrm{false}$, $p(1) = \mathrm{false}$ and $p(2) = \mathrm{true}$, then $\mathrm{rfind}\ p = 2$, whatever $p$ does at $3$ and above.


**Example (Codes as numbers).** The code $\mathrm{id} = \mathrm{pair}(\mathrm{left}, \mathrm{right})$ has number $4 \cdot \mathrm{pair}(2, 3) + 4 = 4 \cdot 11 + 4 = 48$. The code $\mathrm{comp}(\mathrm{succ}, \mathrm{succ})$, which computes $n \mapsto n + 2$, has number $4 \cdot \mathrm{pair}(1, 1) + 6 = 18$. The number $7$ is $\mathrm{rfind'}(\mathrm{zero})$. On input $\mathrm{pair}(a, m)$ it returns $m$ at once, because $\mathrm{eval}\ \mathrm{zero} = 0$.

**Example (Beta function).** Take the sequence $(1, 0)$. Then $m = 2$, $s = \max(2, 1, 0) + 1 = 3$ and $b = 3! = 6$. The moduli are $d_0 = 7$ and $d_1 = 13$, which are coprime. The number $a = 78$ satisfies $78 = 11 \cdot 7 + 1$ and $78 = 6 \cdot 13$, so $a \equiv 1 \pmod 7$ and $a \equiv 0 \pmod{13}$. With $n = \mathrm{pair}(78, 6) = 78^2 + 78 + 6 = 6168$ the values are $\beta(n, 0) = 78 \bmod 7 = 1$ and $\beta(n, 1) = 78 \bmod 13 = 0$.

### The library around it

::: mathlib
`Partrec` · `Mathlib.Computability.Partrec`

`Nat.rfind p` takes `p : ℕ →. Bool`, with `Nat.rfind_spec` and `Nat.rfind_min`, and `Nat.rfindOpt` searches for a `some`. `Nat.Partrec` has the constructors of the text, with `Nat.Partrec.of_primrec` and the empty function `Nat.Partrec.none`. `Partrec`, `Partrec₂`, `Computable` and `Computable₂` are the predicates on primcodable types, and `Primrec.to_comp` embeds the primitive recursive functions. The closure lemmas include `Partrec.comp`, `Partrec.rfind`, and `Partrec.fix` for the iteration `PFun.fix`.

<?decl Partrec?>
:::

::: mathlib
`Nat.Partrec.Code.eval` · `Mathlib.Computability.PartrecCode`

`Nat.Partrec.Code` is the type of codes, with `Nat.Partrec.Code.const`, `Nat.Partrec.Code.id` and `Nat.Partrec.Code.curry`. `Nat.Partrec.Code.encodeCode` and `Nat.Partrec.Code.ofNatCode` are the bijection with ℕ, packaged in `Nat.Partrec.Code.instDenumerable`. `Nat.Partrec.Code.exists_code` is the theorem `Nat.Partrec f ↔ ∃ c, eval c = f`.

<?decl Nat.Partrec.Code.eval?>
:::

::: mathlib
`Nat.Partrec.Code.eval_part` · `Mathlib.Computability.PartrecCode`

`Nat.Partrec.Code.evaln` is the bounded evaluation, with `Nat.Partrec.Code.evaln_sound`, `Nat.Partrec.Code.evaln_complete`, `Nat.Partrec.Code.evaln_mono` and `Nat.Partrec.Code.primrec_evaln`. `Nat.Partrec.Code.eval_eq_rfindOpt` is the normal form and `Nat.Partrec.Code.eval_part` is the universal function. `Nat.Partrec.Code.smn`, with `Nat.Partrec.Code.eval_curry`, is the smn theorem. `Nat.Partrec.Code.fixed_point` and `Nat.Partrec.Code.fixed_point₂` are the two recursion theorems.

<?decl Nat.Partrec.Code.eval_part?>
:::

::: mathlib
`Nat.Partrec'` · `Mathlib.Computability.PartrecBasis`

`Nat.Partrec'` is the classical basis on `List.Vector ℕ n →. ℕ`, with the constructors `prim`, `comp` and `rfind`, and `Nat.Partrec'.part_iff` is the equivalence with `Partrec`.

<?decl Nat.Partrec'?>
:::

::: mathlib
`Nat.beta_unbeta_coe` · `Mathlib.Logic.Godel.GodelBetaFunction`

`Nat.beta n i` is `n.unpair.1 % ((i + 1) * n.unpair.2 + 1)`, `Nat.unbeta l` builds the number of the proof, and `Nat.beta_unbeta_coe` states `beta (unbeta l) i = l[i]`. `Nat.coprime_mul_succ` is the coprimality lemma. The header calls the file a step toward the first incompleteness theorem; the index of this edition has no declaration for that theorem.

<?decl Nat.beta_unbeta_coe?>
:::

Common errors of a learner: The first error is to treat `Part` like `Option`; the domain of an element of `Part` is a proposition, and `(eval c n).Dom` is not decidable in general. The second error is to expect `Nat.rfind` to skip undefined values; it stops at the first undefined value. The third error is to read `comp cf cg` as "first `cf`"; the code `cg` runs first, as in $f \circ g$. The fourth error is to give a code two arguments without pairing them; a code takes one number, and two arguments enter as `Nat.pair a b`.

### Exercises

1. (A) Compute the numbers of the codes $\mathrm{comp}(\mathrm{left}, \mathrm{right})$ and $\mathrm{pair}(\mathrm{zero}, \mathrm{zero})$, and decode the number $9$. Hint: $9 = 4 \cdot 1 + 5$, so it is a $\mathrm{prec}$ code.
2. (A) Show that the partial function $n \mapsto n / 2$ if $n$ is even, undefined if $n$ is odd, is partial recursive. Hint: search for the least $m$ with $2m = n$ and note that the search does not stop for odd $n$.
3. (A) Find the sequence coded by $n = \mathrm{pair}(5, 1)$ under $\beta$ for $i = 0, 1, 2$. Hint: the moduli are $2, 3, 4$.
4. (B) Prove that there is a code $c$ with $\mathrm{eval}\ c\ n = c$ for all $n$, a program that prints its own code. Hint: apply the second recursion theorem to $f(d, n) = d$.
5. (B) Show that there is no computable total function $h$ with $h(c) = 1$ when $\mathrm{eval}\ c\ c$ is defined and $h(c) = 0$ otherwise. Hint: if there were, define the partial function that diverges when $h(x) = 1$ and returns $0$ otherwise, and apply it to its own code.
6. (C) Prove Kleene's normal form in the classical shape: there are a primitive recursive predicate $T(c, n, k)$ and a primitive recursive $U(k)$ with $\mathrm{eval}\ c\ n = U(\mathrm{rfind}\ k.\ T(c, n, k))$ for all $c$ and $n$. Hint: let $k$ code a pair $(k_1, x)$ and let $T$ say $\mathrm{evaln}\ k_1\ c\ n = \mathrm{some}\ x$.

### Notes and history

Kleene introduced the $\mu$ operator and the class of partial recursive functions in the 1930s, and he proved the normal form theorem, the smn theorem and the recursion theorem. Church proposed his thesis in 1936, and Turing gave his machine model the same year. Gödel introduced the beta function in his 1931 paper on incompleteness. The fixed point theorem for computable maps on codes is often called Rogers' fixed point theorem.

The Mathlib files are by these authors, read from their headers: `Mathlib.Computability.Partrec`, `Mathlib.Computability.PartrecCode` and `Mathlib.Computability.PartrecBasis` by Mario Carneiro, and `Mathlib.Logic.Godel.GodelBetaFunction` by Shogo Saito, adapted for Mathlib by Hunter Monroe.

### Reference

<?reference?>
