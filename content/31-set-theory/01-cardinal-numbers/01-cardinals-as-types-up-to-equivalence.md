---
title: Cardinals as types up to equivalence
kind: theory
modules:
  - Mathlib.SetTheory.Cardinal.Defs
  - Mathlib.SetTheory.Cardinal.SchroederBernstein
  - Mathlib.SetTheory.Cardinal.Embedding
  - Mathlib.SetTheory.Cardinal.UnivLE
explains:
  E3: [Cardinal, Cardinal.mk, Cardinal.lift, Function.Embedding.min_injective, Function.Embedding.total]
  E2: [Cardinal.isEquivalent, Cardinal.sum, Cardinal.prod, Cardinal.add_def, Cardinal.mul_def, Cardinal.power_def, Cardinal.mk_congr, Cardinal.inductionOn, Cardinal.lift_mk_eq', Cardinal.lift_umax, Cardinal.power_add, Cardinal.mk_out, Function.Embedding.schroeder_bernstein, Function.Embedding.antisymm, univLE_iff_cardinal_le]
  E1: auto
families: []
requires: [V01.C03, V04.C01, V04.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Cardinals as types up to equivalence

### Overview

In ZFC a cardinal is the least ordinal in a class of equinumerous sets, so the ordinals and the axiom of choice come first. Mathlib takes the other classical route. A cardinal is a class of the quotient of a universe of types by the relation "there is an equivalence". Each operation on cardinals comes from an operation on types: disjoint sum, product, function space, dependent sum and dependent product.

This section sets up the quotient, the operations, the semiring laws and the order by embeddings. The Schröder-Bernstein theorem gives antisymmetry. Volume 1, Chapter 3 and Volume 4, Chapter 4, Section 2 prove it, and this section only cites it. Comparability, the fact that one of two types embeds in the other, needs Zorn's lemma. This section proves it in full, in the stronger form that Mathlib proves. Section 2 uses the same form for the well-foundedness of the order. Universes add one point: types of different universes have cardinals in different types, and `Cardinal.lift` moves a cardinal to a larger universe.

### Definitions

**Definition (Cardinal number).** Two types $\alpha$, $\beta$ of a universe $u$ are *equinumerous* when there is an equivalence $\alpha \simeq \beta$. This is an equivalence relation, by the identity, the inverse and the composite of equivalences. The type $\mathrm{Cardinal}_u$ is the quotient of `Type u` by equinumerosity. The class of a type $\alpha$ is its *cardinality* $\#\alpha$. Thus $\#\alpha = \#\beta$ if and only if there is an equivalence $\alpha \simeq \beta$.

The quotient lives in `Type (u+1)`, one universe above its members. The function `Quotient.out`, written `c.out`, chooses a representative, and `Cardinal.mk_out` says $\#(c.\mathrm{out}) = c$.

**Definition (Operations).** For types $\alpha$, $\beta$ of universe $u$ put
$$\#\alpha + \#\beta = \#(\alpha \oplus \beta), \qquad \#\alpha \cdot \#\beta = \#(\alpha \times \beta), \qquad \#\alpha^{\#\beta} = \#(\beta \to \alpha).$$
For a family $f : \iota \to \mathrm{Cardinal}$ put
$$\sum_i f(i) = \#\Big(\Sigma\, i,\ (f\,i).\mathrm{out}\Big), \qquad \prod_i f(i) = \#\Big(\Pi\, i,\ (f\,i).\mathrm{out}\Big).$$
The constants are $0 = \#\emptyset$ and $1 = \#\mathrm{Unit}$, up to a lift that Mathlib adds for universe reasons.

The binary operations do not depend on the representatives. If $e : \alpha \simeq \alpha'$ and $e' : \beta \simeq \beta'$, then $e \oplus e'$, $e \times e'$ and $h \mapsto e \circ h \circ e'^{-1}$ are equivalences of the sums, the products and the function types. For a family of types $(\beta_i)$, each $(\#\beta_i).\mathrm{out}$ is equivalent to $\beta_i$, and these equivalences assemble on the sigma type. So $\sum_i \#\beta_i = \#(\Sigma i, \beta_i)$, and the same holds for products.

**Definition (Order).** $\#\alpha \le \#\beta$ when there is an embedding $\alpha \hookrightarrow \beta$, that is an injective map.

Composition with equivalences shows that the relation is well defined. It is reflexive and transitive because injective maps compose.

**Definition (Lift).** For universes $u$, $v$ the map $\mathrm{lift}_{u,v} : \mathrm{Cardinal}_u \to \mathrm{Cardinal}_{\max(u,v)}$ sends $\#\alpha$ to $\#(\mathrm{ULift}\,\alpha)$, where $\mathrm{ULift}\,\alpha$ is a copy of $\alpha$ in the larger universe.

Since $\mathrm{ULift}\,\alpha \simeq \alpha$, the map is well defined and injective, it preserves and reflects $\le$, and it commutes with all the operations. Two lifts in a row equal one lift, and $\mathrm{lift}_{u,u}$ is the identity. Types $\alpha$ of universe $u$ and $\beta$ of universe $v$ are compared through $\mathrm{lift}\,\#\alpha$ and $\mathrm{lift}\,\#\beta$ in universe $\max(u,v)$.

### Theorems and proofs

**Proposition (Commutative semiring).** The cardinals of a universe form a commutative semiring: addition and multiplication are associative and commutative, $0$ and $1$ are neutral, $0 \cdot a = 0$, and multiplication distributes over addition.

*Proof.* Each law is an equivalence of types $\alpha$, $\beta$, $\gamma$. Swapping $\mathrm{inl}$ and $\mathrm{inr}$ gives $\alpha \oplus \beta \simeq \beta \oplus \alpha$, and $(a, b) \mapsto (b, a)$ gives $\alpha \times \beta \simeq \beta \times \alpha$. Regrouping gives the associative laws. No element of $\alpha \oplus \emptyset$ has the form $\mathrm{inr}\,x$, so $\alpha \oplus \emptyset \simeq \alpha$. The map $(a, \star) \mapsto a$ gives $\alpha \times \mathrm{Unit} \simeq \alpha$, and $\emptyset \times \alpha$ is empty. For distributivity, send $(a, \mathrm{inl}\,b)$ to $\mathrm{inl}(a, b)$ and $(a, \mathrm{inr}\,c)$ to $\mathrm{inr}(a, c)$. This is an equivalence $\alpha \times (\beta \oplus \gamma) \simeq (\alpha \times \beta) \oplus (\alpha \times \gamma)$, with the evident inverse. Since each cardinal is $\#\alpha$ for some $\alpha$, the laws hold for all cardinals. $\square$

**Proposition (Laws of exponents).** For cardinals $a$, $b$, $c$ of one universe,
$$a^{b + c} = a^b a^c, \qquad (a^b)^c = a^{bc}, \qquad (ab)^c = a^c b^c, \qquad a^0 = 1, \qquad a^1 = a.$$

*Proof.* Let $a = \#\alpha$, $b = \#\beta$, $c = \#\gamma$. A map $\beta \oplus \gamma \to \alpha$ is a pair of maps on the two summands, which gives the first law. Currying gives $(\gamma \to (\beta \to \alpha)) \simeq (\beta \times \gamma \to \alpha)$, the second law. A map $\gamma \to \alpha \times \beta$ is a pair of maps, the third. There is one map from the empty type, and evaluation at $\star$ gives $(\mathrm{Unit} \to \alpha) \simeq \alpha$. $\square$

**Theorem (Schröder-Bernstein).** If $\alpha \hookrightarrow \beta$ and $\beta \hookrightarrow \alpha$, then $\alpha \simeq \beta$. Hence $\le$ is antisymmetric on cardinals.

Volume 4, Chapter 4, Section 2 proves it by the Knaster-Tarski theorem. For embeddings $f : \alpha \to \beta$ and $g : \beta \to \alpha$, the Mathlib proof takes the least fixed point of $s \mapsto (g[(f[s])^c])^c$ on the subsets of $\alpha$. It uses no choice. The next theorem is comparability in a strong form: in each nonempty family of types, one member embeds in all the others.

**Theorem (Minimal injective member).** Let $\iota$ be a nonempty type and let $(\beta_i)_{i \in \iota}$ be a family of types. There is an index $i$ such that for each $j$ there is an embedding $\beta_i \hookrightarrow \beta_j$.

*Proof.* Write $P = \prod_i \beta_i$ for the type of functions $x$ with $x(i) \in \beta_i$ for each $i$. Call a set $s \subseteq P$ *coordinatewise injective* when for all $x, y \in s$ and every index $i$, $x(i) = y(i)$ implies $x = y$. Let $\mathcal{S}$ be the family of coordinatewise injective sets, ordered by inclusion.

Step 1: $\mathcal{S}$ has a maximal element. Let $\mathcal{C} \subseteq \mathcal{S}$ be a chain and $t = \bigcup \mathcal{C}$. Take $x, y \in t$ and $i$ with $x(i) = y(i)$. Then $x \in s_1$ and $y \in s_2$ with $s_1, s_2 \in \mathcal{C}$. One of $s_1$, $s_2$ contains the other, and the larger one is coordinatewise injective, so $x = y$. Thus $t \in \mathcal{S}$ is an upper bound of $\mathcal{C}$. (For the empty chain, $t = \emptyset$.) By Zorn's lemma (Volume 4, Chapter 1, Section 4) there is a maximal $s \in \mathcal{S}$.

Step 2: some projection of $s$ is onto. For an index $i$ let $\pi_i : s \to \beta_i$ be $x \mapsto x(i)$. Suppose that no $\pi_i$ is surjective. By the axiom of choice, choose for each $i$ an element $b_i \in \beta_i$ outside the image of $\pi_i$, and let $z \in P$ be $i \mapsto b_i$. No $x \in s$ has $x(i) = z(i)$ for any $i$, so $s' = s \cup \{z\}$ is coordinatewise injective. Also $z \notin s$: take any index $i$, which exists since $\iota$ is nonempty, and note that $z(i)$ is not a value of $\pi_i$. Thus $s \subsetneq s' \in \mathcal{S}$, which contradicts the maximality of $s$. So there is an index $i$ with $\pi_i$ surjective.

Step 3: the embeddings. Fix $i$ with $\pi_i$ surjective. Each $\pi_j$ is injective, because $s$ is coordinatewise injective. So $\pi_i$ is a bijection $s \to \beta_i$, and $\pi_j \circ \pi_i^{-1} : \beta_i \to \beta_j$ is an embedding for each $j$. $\square$

**Corollary (Comparability).** For any two types $\alpha$, $\beta$, there is an embedding $\alpha \hookrightarrow \beta$ or an embedding $\beta \hookrightarrow \alpha$. Hence the order of cardinals is total.

*Proof.* For $\alpha$ in universe $u$ and $\beta$ in universe $v$, index a family by the booleans: $\beta_{\mathrm{true}} = \mathrm{ULift}\,\alpha$ and $\beta_{\mathrm{false}} = \mathrm{ULift}\,\beta$, in universe $\max(u, v)$. The theorem gives $\mathrm{ULift}\,\alpha \hookrightarrow \mathrm{ULift}\,\beta$ or the converse. Compose with $\alpha \simeq \mathrm{ULift}\,\alpha$ and $\mathrm{ULift}\,\beta \simeq \beta$. $\square$

With Schröder-Bernstein, $\le$ is a linear order on $\mathrm{Cardinal}_u$. Section 2 applies the theorem to the members of a nonempty set of cardinals and gets a least member.

### Examples

**Example (A finite computation).** Let $\alpha = \mathrm{Fin}\,3$ and $\beta = \mathrm{Fin}\,2$. Then $\#(\beta \to \alpha) = 3^2 = 9$. A map $\mathrm{Fin}\,2 \to \mathrm{Fin}\,3$ is a pair of values, so $(\mathrm{Fin}\,2 \to \mathrm{Fin}\,3) \simeq \mathrm{Fin}\,3 \times \mathrm{Fin}\,3$. The map $(p, q) \mapsto 3p + q$ is a bijection $\mathrm{Fin}\,3 \times \mathrm{Fin}\,3 \to \mathrm{Fin}\,9$. Induction with $\mathrm{Fin}(n+1) \simeq \mathrm{Fin}\,n \oplus \mathrm{Unit}$ gives $\#\mathrm{Fin}\,n = n$ in the semiring, and there the computation reads $3^{1+1} = 3^1 \cdot 3^1 = 9$. In the same way, a subset is a map $\alpha \to \mathrm{Prop}$ and $\mathrm{Prop}$ has two elements, so $\#\,\mathrm{Set}\,\alpha = 2^{\#\alpha}$.

**Counterexample (No cancellation).** In the cardinals, $a + c = b + c$ does not imply $a = b$. Take $a = 1$, $b = 0$ and $c = \#\mathbb{N}$. The map $\mathrm{inl}\,\star \mapsto 0$, $\mathrm{inr}\,n \mapsto n + 1$ is a bijection $\mathrm{Unit} \oplus \mathbb{N} \to \mathbb{N}$. So $1 + \#\mathbb{N} = \#\mathbb{N} = 0 + \#\mathbb{N}$, but $1 \ne 0$. The semiring is not a ring: no cardinal $x$ has $x + 1 = 0$.

**Counterexample (The index type must be nonempty).** For the empty index type the conclusion "there is an index $i$" is false. In the proof, $P$ then has one element, the empty function, and $s = P$ is maximal. Step 2 fails exactly at the claim $z \notin s$.

### The library around it

::: mathlib
`Cardinal` · `Mathlib.SetTheory.Cardinal.Defs`

`Cardinal.{u} : Type (u + 1)` is `Quotient Cardinal.isEquivalent`, where the setoid on `Type u` has the relation `Nonempty (α ≃ β)`. The relation is a `Prop`, so the quotient forgets which equivalence exists. To prove a statement for all cardinals, use `Cardinal.inductionOn`: it reduces a goal about `c` to a goal about `#α`.

<?decl Cardinal?>
:::

::: mathlib
`Cardinal.mk` · `Mathlib.SetTheory.Cardinal.Defs`

`Cardinal.mk : Type u → Cardinal.{u}` is the quotient map. The notation `#α` is scoped: write `open Cardinal` to use it. The lemma `Cardinal.mk_congr` turns an equivalence `α ≃ β` into `#α = #β`, and `Cardinal.eq` states `#α = #β ↔ Nonempty (α ≃ β)`. In the other direction, `Cardinal.mk_out` gives `#c.out = c`.

<?decl Cardinal.mk?>
:::

::: mathlib
`Cardinal.lift` · `Mathlib.SetTheory.Cardinal.Defs`

`Cardinal.lift.{v, u} : Cardinal.{u} → Cardinal.{max u v}` sends `#α` to `#(ULift.{v} α)`. The first universe argument is the universe added. For `α : Type u` and `β : Type v`, `Cardinal.lift_mk_eq'` states `lift.{v} #α = lift.{u} #β ↔ Nonempty (α ≃ β)`. The simp lemma `Cardinal.lift_umax` rewrites `lift.{max u v, u}` to `lift.{v, u}`.

<?decl Cardinal.lift?>
:::

::: mathlib
`Cardinal.sum` · `Mathlib.SetTheory.Cardinal.Defs`

`Cardinal.sum (f : ι → Cardinal.{v}) : Cardinal.{max u v}` for `ι : Type u` is `#(Σ i, (f i).out)`, and `Cardinal.prod` is the same with `Π`. The binary operations come from `Cardinal.add_def`, `Cardinal.mul_def` and `Cardinal.power_def`: `#α + #β = #(α ⊕ β)`, `#α * #β = #(α × β)` and `#α ^ #β = #(β → α)`. The laws of exponents are lemmas such as `Cardinal.power_add`.

<?decl Cardinal.sum?>
:::

The `CommSemiring` instance is `Cardinal.commSemiring` in `Mathlib.SetTheory.Cardinal.Order`, together with the order. The order lemma `Cardinal.le_def` states `#α ≤ #β ↔ Nonempty (α ↪ β)`. Section 2 treats that module.

::: mathlib
`Function.Embedding.min_injective` · `Mathlib.SetTheory.Cardinal.SchroederBernstein`

`min_injective [Nonempty ι] (β : ι → Type u) : ∃ i, Nonempty (∀ j, β i ↪ β j)`. All the types of the family live in one universe. The Mathlib proof follows the three steps above: it applies `zorn_subset` to the sets of functions that are injective in each coordinate.

<?decl Function.Embedding.min_injective?>
:::

::: mathlib
`Function.Embedding.total` · `Mathlib.SetTheory.Cardinal.SchroederBernstein`

`total (α : Type u) (β : Type v) : Nonempty (α ↪ β) ∨ Nonempty (β ↪ α)`, for types of any two universes. The proof is the corollary above. Its partner `Function.Embedding.schroeder_bernstein` takes two injective maps and gives a bijection, and `Function.Embedding.antisymm` gives `Nonempty (α ≃ β)` from two embeddings.

<?decl Function.Embedding.total?>
:::

::: mathlib
`univLE_iff_cardinal_le` · `Mathlib.SetTheory.Cardinal.UnivLE`

The class `UnivLE.{u, v}` says that each type of universe `u` has a copy of the same size in universe `v`. The theorem states `UnivLE.{u, v} ↔ univ.{u, v+1} ≤ univ.{v, u+1}`, with `Cardinal.univ` from Chapter 2, Section 2.

<?decl univLE_iff_cardinal_le?>
:::

Common errors of a learner:

- `#α` needs `open Cardinal`. Without it, `#α` does not parse as a cardinal.
- The types in `#α = #β` must live in one universe. Otherwise use `lift`, as in `Cardinal.lift_mk_eq'`, and let `simp` normalize the lifts.
- A cardinal is not a type. To get a type from a cardinal `c`, use `c.out`, and expect an equivalence, not an equality, with the original type.
- `Cardinal.sum f` uses `out`, so `#(Σ i, β i) = sum (fun i ↦ #(β i))` is a lemma (`Cardinal.mk_sigma`), not a definition.

### Exercises

1. (A) Prove $a \cdot (b + c) = a b + a c$ by writing the equivalence of types and its inverse in full.
2. (A) Show that $\#(\alpha \to \mathrm{Unit}) = 1$ and $\#(\emptyset \to \alpha) = 1$ for each type $\alpha$, and that $0^a = 0$ for $a \ne 0$. Hint: a type with an element has no map to the empty type.
3. (A) Show that $\le$ is compatible with the operations: $a \le b$ implies $a + c \le b + c$, $ac \le bc$ and $a^c \le b^c$. Show also $c^a \le c^b$ when $c \ne 0$. Hint: extend an embedding by the identity, or extend a map by a constant.
4. (B) Show that $\#\mathbb{N} \cdot \#\mathbb{N} = \#\mathbb{N}$ implies $\#(\mathbb{N} \to \mathbb{N}) = 2^{\#\mathbb{N}}$. Hint: $2 \le \#\mathbb{N} \le 2^{\#\mathbb{N}}$, and use the second law of exponents.
5. (B) Let $(\beta_i)$ be a family of types. Show that $\prod_i \#\beta_i = 0$ if and only if some $\beta_i$ is empty. Point out where the proof uses the axiom of choice.
6. (B) Show that $\mathrm{lift}$ is not surjective onto $\mathrm{Cardinal}_{\max(u,v)}$ when $v > u$. Hint: the cardinals of universe $u$ form a set of universe $u + 1$, and Cantor's theorem of Section 2 gives a cardinal above all of them.
7. (C) Deduce the well-ordering of cardinals from the theorem on a minimal injective member: every nonempty set $S$ of cardinals of universe $u$ has a least element. Hint: index a family by the subtype $S$ and take $\beta_c = c.\mathrm{out}$.

### Notes and history

Cantor introduced cardinal numbers as the common size of equinumerous sets, in papers from 1874 to 1897. Frege and Russell defined a cardinal as the class of all sets equinumerous with a given set. In ZFC this is a proper class, and von Neumann's least ordinal replaced it. In Lean the quotient works, because the quotient of `Type u` is a type of the next universe. The comparability of cardinals is equivalent to the axiom of choice, a result of Hartogs from 1915. Jech, *Set Theory*, Chapter 3, and Kunen, *Set Theory*, Chapter I, give the ZFC approach.

### Reference

<?reference?>
