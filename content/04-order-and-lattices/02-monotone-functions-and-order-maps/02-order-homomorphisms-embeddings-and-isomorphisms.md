---
title: Order homomorphisms, embeddings and isomorphisms
kind: theory
modules:
  - Mathlib.Order.Hom.Basic
  - Mathlib.Order.RelIso.Basic
  - Mathlib.Order.RelIso.Set
  - Mathlib.Order.Hom.Order
  - Mathlib.Order.Hom.Set
  - Mathlib.Order.Hom.Lex
  - Mathlib.Order.Hom.PowersetCard
  - Mathlib.Order.CountableDenseLinearOrder
explains:
  E3: [OrderHom, OrderIso, OrderEmbedding]
  E2: [RelIso, RelEmbedding, OrderIso.le_iff_le, OrderIso.symm, OrderHom.comp, OrderEmbedding.ofStrictMono, OrderIso.map_sup, OrderIso.isMin_apply, StrictMono.orderIsoOfSurjective, Equiv.toOrderIso]
  E1: auto
families: []
requires: [V04.C01]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V04/C02/Examples.lean
  - MathlibHandbook/V04/C02/Exercises.lean
  - MathlibHandbook/V04/C02/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Order homomorphisms, embeddings and isomorphisms

### Overview

The previous section treated monotonicity as a property of a function. This section treats monotone maps as objects. There are three kinds. An order homomorphism is a monotone map. An order embedding is a map that both keeps and reflects the order, so that its domain is a copy of a part of its codomain. An order isomorphism is a bijective order embedding. Two order isomorphic sets satisfy the same statements about $\le$.

The section proves that a bijective monotone map need not be an order isomorphism, that a strictly monotone surjection on a linear order is one, and that an order isomorphism keeps least elements, suprema and infima. The last fact gives a method to prove that two orders are not isomorphic: find an order property that one has and the other lacks.

### Definitions

In this section $\alpha$, $\beta$ and $\gamma$ are preorders unless the text says otherwise.

**Definition (Order homomorphism).** An *order homomorphism* from $\alpha$ to $\beta$ is a monotone function $f : \alpha \to \beta$. The set of these maps is written $\alpha \to_o \beta$.

In the bundled form the function and the proof of monotonicity are one object. The set $\alpha \to_o \beta$ carries the pointwise order: $f \le g$ if $f(a) \le g(a)$ for each $a$. With this order, $\alpha \to_o \beta$ is again a preorder, a partial order when $\beta$ is one, and a complete lattice when $\beta$ is one. The fixed point theorem of Chapter 4 is a statement about the maps in $\alpha \to_o \alpha$.

::: mathlib
`OrderHom` · `Mathlib.Order.Hom.Basic`

The structure has two fields, `toFun : α → β` and `monotone' : Monotone toFun`. The notation is `α →o β`. A term `f : α →o β` coerces to a function, so `f a` makes sense, and `f.monotone` is the proof of monotonicity. Two order homomorphisms are equal when the functions are equal, by `OrderHom.ext`. The composition is `OrderHom.comp g f`, the bundled form of $g \circ f$.

<?decl OrderHom?>
:::

**Definition (Order embedding).** An *order embedding* from $\alpha$ to $\beta$ is a function $f : \alpha \to \beta$ such that, for all $a, b \in \alpha$,
$$f(a) \le f(b) \iff a \le b.$$
Mathlib also asks that $f$ is injective, and this is automatic when $\alpha$ is a partial order. Indeed, if $f(a) = f(b)$, then $f(a) \le f(b)$ and $f(b) \le f(a)$, so $a \le b$ and $b \le a$, and $a = b$.

The condition says two things. The direction from right to left says that $f$ is monotone. The direction from left to right says that $f$ *reflects* the order: if the images are comparable, the points are comparable in the same way. A monotone injection need not reflect the order, as the counterexample of the divisors below shows.

::: mathlib
`OrderEmbedding` · `Mathlib.Order.Hom.Basic`

The notation is `α ↪o β`. It is an abbreviation of `RelEmbedding (· ≤ ·) (· ≤ ·)`. A `RelEmbedding` is an injective function, a `Function.Embedding`, with the field `map_rel_iff'`. The lemma `OrderEmbedding.le_iff_le` states the field for an order embedding, and `OrderEmbedding.lt_iff_lt` the strict form. The constructor `OrderEmbedding.ofStrictMono` builds an embedding from a strictly monotone map on a linear order.

<?decl OrderEmbedding?>
:::

**Definition (Order isomorphism).** An *order isomorphism* from $\alpha$ to $\beta$ is a bijection $f : \alpha \to \beta$ with $f(a) \le f(b) \iff a \le b$ for all $a, b$. Two preorders are *order isomorphic*, written $\alpha \cong \beta$, if there is an order isomorphism between them.

An order isomorphism is the same as a bijection $f$ such that both $f$ and $f^{-1}$ are monotone. Indeed, let $f$ be an order isomorphism and let $x \le y$ in $\beta$. Write $x = f(a)$ and $y = f(b)$. Then $f(a) \le f(b)$, so $a \le b$, that is $f^{-1}(x) \le f^{-1}(y)$. Conversely, if $f$ and $f^{-1}$ are monotone and $f(a) \le f(b)$, then $a = f^{-1}(f(a)) \le f^{-1}(f(b)) = b$.

::: mathlib
`OrderIso` · `Mathlib.Order.Hom.Basic`

The notation is `α ≃o β`, an abbreviation of `RelIso (· ≤ ·) (· ≤ ·)`. A `RelIso` is an `Equiv` with the field `map_rel_iff'`, so `e.toEquiv` is the bijection and `e.symm` the inverse, which is again an order isomorphism. The lemma `OrderIso.le_iff_le` states the field. The constructor `Equiv.toOrderIso` takes a bijection and proofs that it and its inverse are monotone, the form of the remark above. The other constructor `OrderIso.ofHomInv` takes two order homomorphisms that are inverse to each other.

<?decl OrderIso?>
:::

**Definition (Relation maps).** Let $r$ be a relation on $\alpha$ and $s$ a relation on $\beta$. A *relation embedding* is an injective function $f$ with $r(a, b) \iff s(f(a), f(b))$, and a *relation isomorphism* is a bijective relation embedding.

Order maps are the case $r = {\le}$ and $s = {\le}$. The general form is used for well-orders and ordinals, where the relation is $<$.

::: mathlib
`RelIso` · `Mathlib.Order.RelIso.Basic`

The structure `RelIso r s` extends `α ≃ β` with `map_rel_iff' : s (f a) (f b) ↔ r a b`. The notation is `r ≃r s`. The structure `RelHom` (`r →r s`) is similar. Since `OrderIso` is an abbreviation and not a new structure, every lemma about `RelIso` applies to an order isomorphism.

<?decl RelIso?>
:::

::: mathlib
`RelEmbedding` · `Mathlib.Order.RelIso.Basic`

The structure extends `α ↪ β`, the injective functions, with the field `map_rel_iff'`.

<?decl RelEmbedding?>
:::

### Theorems and proofs

**Theorem (Composition and inverse).** The composite of two order homomorphisms is an order homomorphism, the composite of two order embeddings is an order embedding, and the composite of two order isomorphisms is an order isomorphism. The inverse of an order isomorphism is an order isomorphism.

*Proof.* The first claim is part 1 of the composition theorem of the previous section. For two embeddings $f : \alpha \to \beta$ and $g : \beta \to \gamma$, the chain of equivalences
$$g(f(a)) \le g(f(b)) \iff f(a) \le f(b) \iff a \le b$$
uses the property of $g$ at the points $f(a)$ and $f(b)$, then the property of $f$. A composite of injections is an injection, and a composite of bijections is a bijection. For the inverse $f^{-1}$ of an isomorphism $f$, let $x, y \in \beta$ and put $a = f^{-1}(x)$, $b = f^{-1}(y)$. Then $x \le y$ means $f(a) \le f(b)$, which is equivalent to $a \le b$. So $f^{-1}(x) \le f^{-1}(y) \iff x \le y$. $\square$

::: mathlib
`OrderIso.symm` · `Mathlib.Order.Hom.Basic`

The inverse is `e.symm : β ≃o α`, and the composite of `e : α ≃o β` and `e' : β ≃o γ` is `e.trans e'`, in the order of the arrows. The composite of order homomorphisms is `OrderHom.comp g f`, in the order of functions.

<?decl OrderIso.symm?>
:::

::: mathlib
`OrderHom.comp` · `Mathlib.Order.Hom.Basic`

The composite `g.comp f` coerces to the function `g ∘ f`, and the simp lemma `OrderHom.comp_coe` says so. The identity is `OrderHom.id`.

<?decl OrderHom.comp?>
:::

**Theorem (A bijective monotone map need not be an isomorphism).** There are partial orders $\alpha$ and $\beta$ and a bijection $f : \alpha \to \beta$ that is monotone and is not an order isomorphism.

*Proof.* Let $\alpha = \{0, 1\}$ with the discrete order: $a \le b$ only when $a = b$. This is a partial order. Let $\beta = \{0, 1\}$ with the usual order $0 \le 1$, and let $f$ be the identity map. It is a bijection. It is monotone, because $a \le b$ in $\alpha$ means $a = b$, and then $f(a) \le f(b)$ by reflexivity. But $f(0) \le f(1)$ holds in $\beta$, and $0 \le 1$ fails in $\alpha$. So $f$ does not reflect the order, and it is not an order isomorphism. $\square$

The example is the order version of a fact in topology: a continuous bijection need not be a homeomorphism.

**Theorem (Strictly monotone surjections).** Let $\alpha$ be a linear order and $\beta$ a preorder. A strictly monotone surjection $f : \alpha \to \beta$ is an order isomorphism.

*Proof.* By the theorem on strictly monotone maps of the previous section, $f$ is injective and $f(a) \le f(b) \iff a \le b$. Those proofs need only a linear order on $\alpha$ and a preorder on $\beta$. With the surjectivity, $f$ is a bijection with the property of an order isomorphism. $\square$

::: mathlib
`StrictMono.orderIsoOfSurjective` · `Mathlib.Order.Hom.Set`

The definition takes the function, a proof of `StrictMono f` and a proof of `Function.Surjective f`, and it gives `α ≃o β`. It is a definition, because the result is data, and its coercion is `f`.

<?decl StrictMono.orderIsoOfSurjective?>
:::

::: mathlib
`OrderEmbedding.ofStrictMono` · `Mathlib.Order.Hom.Basic`

The embedding form of the theorem: a strictly monotone map on a linear order is an order embedding, without the surjectivity.

<?decl OrderEmbedding.ofStrictMono?>
:::

**Theorem (Isomorphisms keep the order properties).** Let $f : \alpha \to \beta$ be an order isomorphism, let $s \subseteq \alpha$ and let $m \in \alpha$.

1. $m$ is a least element of $\alpha$ if and only if $f(m)$ is a least element of $\beta$. The same holds for minimal, greatest and maximal elements.
2. $m$ is an upper bound of $s$ if and only if $f(m)$ is an upper bound of $f(s)$.
3. $m$ is a least upper bound of $s$ if and only if $f(m)$ is a least upper bound of $f(s)$. The same holds for greatest lower bounds.
4. If $\alpha$ and $\beta$ are lattices, then $f(a \sqcup b) = f(a) \sqcup f(b)$ and $f(a \sqcap b) = f(a) \sqcap f(b)$.

*Proof.* 1. Suppose that $m \le a$ for each $a \in \alpha$. Let $y \in \beta$, and write $y = f(a)$, which is possible because $f$ is surjective. Then $m \le a$ gives $f(m) \le f(a) = y$. Conversely, suppose that $f(m) \le y$ for each $y$. For $a \in \alpha$, $f(m) \le f(a)$ gives $m \le a$. The other properties have the same proof: each is a statement about $\le$ with quantifiers over the whole order, and $f$ translates the statement in both directions.

2. $m$ is an upper bound of $s$ when $a \le m$ for each $a \in s$. This is equivalent to $f(a) \le f(m)$ for each $a \in s$, which says that $f(m)$ is an upper bound of $f(s) = \{f(a) : a \in s\}$.

3. By part 2, $f$ maps the set $U$ of upper bounds of $s$ onto the set of upper bounds of $f(s)$: a point $y = f(u)$ is an upper bound of $f(s)$ exactly when $u \in U$. So $f$ restricts to an order isomorphism from $U$ onto the upper bounds of $f(s)$. A least upper bound is a least element of $U$, and part 1, applied to this restriction, gives the claim.

4. In a lattice, $a \sqcup b$ is the least upper bound of $\{a, b\}$. By part 3, $f(a \sqcup b)$ is the least upper bound of $\{f(a), f(b)\}$, which is $f(a) \sqcup f(b)$. The dual argument gives the infimum. $\square$

::: mathlib
`OrderIso.isMin_apply` · `Mathlib.Order.Hom.Basic`

The statement is `IsMin (f x) ↔ IsMin x`. The file has the similar lemmas `OrderIso.isMax_apply`, `OrderIso.map_bot` and `OrderIso.map_top`. The lemmas for bounds of sets, `OrderIso.isLUB_image` and `OrderIso.isGLB_image`, are in `Mathlib.Order.Bounds.OrderIso`, and the lemmas for `sSup` and `iSup` are in the files of complete lattices.

<?decl OrderIso.isMin_apply?>
:::

::: mathlib
`OrderIso.map_sup` · `Mathlib.Order.Hom.Basic`

The statement is `f (x ⊔ y) = f x ⊔ f y` for `f : α ≃o β` between two semilattices. The dual is `OrderIso.map_inf`.

<?decl OrderIso.map_sup?>
:::

### Examples

**Example ($\mathbb{N}$ and $\mathbb{Z}$ are not order isomorphic).** Suppose that $f : \mathbb{N} \to \mathbb{Z}$ is an order isomorphism. The number $0$ is a least element of $\mathbb{N}$. By part 1 of the theorem, $f(0)$ is a least element of $\mathbb{Z}$. But $f(0) - 1 < f(0)$, so $f(0)$ is not least. This contradiction shows that no order isomorphism exists. The same argument shows that $[0, 1]$ and $(0, 1)$ are not order isomorphic: the first has a least element and the second has none.

**Example ($\mathbb{R}$ and $(-1, 1)$ are order isomorphic).** Let $f(x) = x/(1 + |x|)$. Then $|f(x)| = |x|/(1 + |x|) < 1$, so $f$ maps $\mathbb{R}$ into $(-1, 1)$. For $0 \le x < y$,
$$f(y) - f(x) = \frac{y(1 + x) - x(1 + y)}{(1 + x)(1 + y)} = \frac{y - x}{(1 + x)(1 + y)} > 0.$$
So $f$ is strictly monotone on $[0, \infty)$. The function is odd, $f(-x) = -f(x)$, so it is strictly monotone on $(-\infty, 0]$ too. For $x < 0 \le y$, $f(x) < 0 \le f(y)$, because $f(x)$ has the sign of $x$. So $f$ is strictly monotone on $\mathbb{R}$. It is surjective: for $y \in (-1, 1)$ put $x = y/(1 - |y|)$. Then $1 + |x| = 1 + |y|/(1 - |y|) = 1/(1 - |y|)$, and $f(x) = x (1 - |y|) = y$. By the theorem on strictly monotone surjections, $f$ is an order isomorphism. So boundedness in $\mathbb{R}$ is not an order property of the subset on its own.

**Example (The dual order and negation).** The dual $\alpha^{\mathrm{op}}$ of a preorder has the same elements and the order $a \le^{\mathrm{op}} b \iff b \le a$. The map $x \mapsto -x$ is an order isomorphism from $\mathbb{R}$ to $\mathbb{R}^{\mathrm{op}}$, because $-x \le^{\mathrm{op}} -y \iff -y \le -x \iff x \le y$. So the order of $\mathbb{R}$ is isomorphic to its reverse. The order of $\mathbb{N}$ is not: $\mathbb{N}$ has a least element and $\mathbb{N}^{\mathrm{op}}$ has none, because a least element of $\mathbb{N}^{\mathrm{op}}$ would be a greatest natural number. In Mathlib the dual is the type `OrderDual α`, written `αᵒᵈ`.

**Example (The automorphisms of $\mathbb{N}$).** The only order isomorphism $f : \mathbb{N} \to \mathbb{N}$ is the identity. An order isomorphism is strictly monotone, so $n \le f(n)$ for each $n$, by Exercise 5 of the previous section. The inverse $f^{-1}$ is also an order isomorphism, so $n \le f^{-1}(n)$. Apply the monotone map $f$: $f(n) \le f(f^{-1}(n)) = n$. With $n \le f(n)$ this gives $f(n) = n$. In contrast, $\mathbb{Z}$ has the automorphisms $n \mapsto n + k$.

**Counterexample (A monotone bijection of a non linear order).** Let $\alpha$ be the set $\{1, 2, 3, 6\}$ ordered by divisibility and $\beta$ the same set with the usual order. The identity $\alpha \to \beta$ is monotone, since $a \mid b$ gives $a \le b$ for positive integers. It is not an order isomorphism, because $2 \le 3$ and $2 \nmid 3$. Here $\alpha$ is a lattice in which $2 \sqcup 3 = 6$, while in $\beta$, $2 \sqcup 3 = 3$. A monotone bijection can change suprema.

**Example (A bundled map in Lean).** A term of `ℕ →o ℕ` is a function, so it takes an argument, and `rfl` computes the value.

<?lean MathlibHandbook/V04/C02/Examples.lean#orderHom?>

**Example (An order isomorphism in Lean).** The field of an order isomorphism, read with `OrderIso.le_iff_le`.

<?lean MathlibHandbook/V04/C02/Examples.lean#orderIso?>

### The library around it

Use the predicate `Monotone f` when the function is given by a formula and the proof is about this one function. Use the bundled form `α →o β` when the maps themselves are the objects, for example when they form an ordered set, as in the fixed point theorems.

All bundled order maps share the classes `OrderHomClass` and `OrderIsoClass`. A lemma stated for any `F` with `[OrderIsoClass F α β]` applies to `OrderIso`, to the lattice isomorphisms and to the isomorphisms of ordered groups at the same time. The field is `OrderIsoClass.map_le_map_iff`. The map `OrderIso.toOrderEmbedding` forgets the surjectivity, and `OrderEmbedding.subtype` is the inclusion of a subset with the induced order.

The module `Mathlib.Order.RelIso.Set` connects relation maps with subsets. For a relation $r$ on $\alpha$ and a predicate $p$, `Subrel r p` is the restriction of $r$ to the subtype of $p$, and `Subrel.relEmbedding` embeds it back into $r$. `Subrel.inclusionEmbedding` is the embedding for an inclusion $s \subseteq t$, and `RelEmbedding.codRestrict` restricts the codomain of an embedding to a set that holds its range. For an isomorphism $e$, `RelIso.image_eq_preimage_symm` says $e(t) = (e^{-1})^{-1}(t)$, and `RelIso.range_eq` says that the range is the whole type. `RelHomClass.directed` says that a relation map sends a directed family to a directed family. The lemma `wellFounded_iff_wellFounded_subrel` says that a transitive relation is well founded if and only if its restriction to $\{x \mid r(x, b)\}$ is well founded for each $b$.

The module `Mathlib.Order.Hom.Order` puts a lattice structure on the type `α →o β` when $\beta$ is a lattice. The operations act pointwise: `OrderHom.coe_sup` says that $(f \sqcup g)(x) = f(x) \sqcup g(x)$, and for a complete lattice $\beta$, `OrderHom.iSup_apply` and `OrderHom.sSup_apply` give the supremum of a family of maps at a point. The fixed point theorems of Chapter 4 use this complete lattice of monotone maps.

The module `Mathlib.Order.Hom.Set` builds order isomorphisms from sets. A strictly monotone map $f$ on a linear order is an isomorphism onto its range by `StrictMono.orderIso`, and `StrictMono.orderIsoOfSurjective` is the form for a surjective map. `OrderIso.setCongr` and `Set.orderIsoOfEq` move along an equality of sets, and `OrderIso.Iic` and `OrderIso.Icc` restrict an isomorphism of lattices to intervals. In a Boolean algebra the complement is an antitone bijection, and `OrderIso.compl` packs it as an isomorphism from $\alpha$ to the order dual of $\alpha$. The lemma `OrderEmbedding.range_inj_of_wellFoundedLT` says that two order embeddings of a well-ordered type with the same range are equal. Initial segments in the next section give a stronger form of this rigidity.

The module `Mathlib.Order.Hom.Lex` has the isomorphisms of lexicographic orders. `OrderIso.sumLexIioIci` cuts a linear order at a point $x$: it is the isomorphism from the lexicographic sum of $(-\infty, x)$ and $[x, \infty)$ to $\alpha$. `Prod.Lex.prodLexAssoc` is the associativity of the lexicographic product, and `Prod.Lex.sumLexProdLexDistrib` distributes a lexicographic product over a lexicographic sum. The module `Mathlib.Order.Hom.PowersetCard` treats the type of subsets of size $n$ of a linear order: `Set.powersetCard.orderIsoOfFin` lists the elements of such a subset $s$ in increasing order as an isomorphism from `Fin n` to $s$.

The module `Mathlib.Order.CountableDenseLinearOrder` proves the theorem of Cantor on countable dense orders by the back-and-forth method. `Order.iso_of_countable_dense` says that two countable, nonempty, dense linear orders without a least or a greatest element are isomorphic. The example is $\mathbb{Q}$: each such order is isomorphic to it. `Order.embedding_from_countable_to_dense` says that each countable linear order embeds into each nontrivial dense linear order. The proof works with finite partial isomorphisms, of type `Order.PartialIso α β`. The step lemma `Order.PartialIso.exists_across` extends a finite partial isomorphism to one more point $a$: the new image $b$ must lie in the same gap between the old images as $a$ lies between the old points, and density with no endpoints gives such a $b$. An enumeration of the two countable types alternates steps forward and backward, and the union of the finite partial maps is the isomorphism.

### Exercises

1. (A) Show that $x \mapsto 2x + 1$ is an order isomorphism from $\mathbb{R}$ to $\mathbb{R}$, and give its inverse.
2. (A) Show that $[0, 1]$ and $[0, 1)$ are not order isomorphic. *Hint:* a greatest element.
3. (B) Show that $\mathbb{Z}$ and $\mathbb{Q}$ are not order isomorphic. *Hint:* in $\mathbb{Z}$, the point $0$ has an immediate successor; in $\mathbb{Q}$ no point has one, because $(a + b)/2$ lies strictly between $a$ and $b$.
4. (B) Show that an order embedding $\alpha \to \beta$ between partial orders is the same as an order isomorphism from $\alpha$ onto its image $f(\alpha)$ with the induced order.
5. (B) Let $f : \alpha \to \beta$ be an order isomorphism between lattices. Show that $\alpha$ is distributive if and only if $\beta$ is. *Hint:* use part 4 of the theorem on order properties.
6. (B) Find all order isomorphisms $\mathbb{Z} \to \mathbb{Z}$. *Hint:* show that $f(n + 1) = f(n) + 1$ by the fact that $n + 1$ is the least element above $n$.
7. (C) Let $\alpha$ be a finite linear order with $n$ elements. Show that $\alpha$ is order isomorphic to $\{0, 1, \ldots, n - 1\}$ with the usual order. *Hint:* induction on $n$; remove the greatest element.
8. (C) Show that the subsets of $\{1, 2, 3\}$ with inclusion and the divisors of $30$ with divisibility are order isomorphic. *Hint:* $30 = 2 \cdot 3 \cdot 5$; send a set $S$ to the product of the primes with index in $S$.

### Notes and history

The notion of order type, the class of an ordered set up to order isomorphism, is due to Cantor (1895). Cantor also proved that every countable dense linear order without a least and a greatest element is order isomorphic to $\mathbb{Q}$. Mathlib has this theorem as `Order.iso_of_countable_dense`.

In Mathlib, the relation maps `RelHom`, `RelEmbedding` and `RelIso` come from the Lean 3 library, where they served the theory of ordinals. The bundled `OrderHom` had the name `preorder_hom` in Lean 3. The file `Mathlib/Order/Hom/Basic.lean` was started by Johan Commelin in 2020.

### Reference

<?reference?>
