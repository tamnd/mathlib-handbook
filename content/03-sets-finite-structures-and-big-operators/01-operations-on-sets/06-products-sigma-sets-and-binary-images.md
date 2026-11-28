---
title: Products, sigma sets and binary images of sets
kind: api
modules:
  - Mathlib.Data.Set.Prod
  - Mathlib.Data.Set.Sigma
  - Mathlib.Data.Set.NAry
  - Mathlib.Data.Set.Functor
explains:
  E2: [Set.prod_inter_prod, Set.prod_subset_prod_iff, Set.compl_prod_eq_union, Set.offDiag_insert, Set.pi_nonempty_iff, Set.univ_pi_subset_univ_pi_iff, Set.sigma_eq_biUnion, Set.image2_subset_iff, Set.image_prod, Set.bind_def]
  E1: auto
families: []
requires: [V01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Products, sigma sets and binary images of sets

### Overview

From two sets $s \subseteq \alpha$ and $t \subseteq \beta$ the library makes the product $s \times t \subseteq \alpha \times \beta$, written `s ×ˢ t`. From a family of sets $t_i \subseteq \alpha_i$ it makes the product `Set.pi s t` of the sets $t_i$ for $i \in s$, a set of dependent functions, and the sigma set `Set.sigma s t`, a set of dependent pairs. From a function of two arguments $f : \alpha \to \beta \to \gamma$ it makes the binary image `Set.image2 f s t` $= \{f(a, b) \mid a \in s,\ b \in t\}$. The modules of this section give the API of these four constructions, and the structure of a monad on `Set`.

The rules are of the same kind as the rules for union, intersection and image in the earlier sections of this chapter: membership, monotonicity, the empty set, singletons, unions and intersections. The text gives the rules that have a condition or a surprise, and lists the others by their pattern.

### The library around it

#### The product of two sets

The product and its membership rule are in `Mathlib.Data.Set.Operations`: `Set.mem_prod` says that $p \in s \times t$ if and only if $p_1 \in s$ and $p_2 \in t$. The module `Mathlib.Data.Set.Prod` holds about 200 results. Most of them are distributive laws:

$$(s_1 \times t_1) \cap (s_2 \times t_2) = (s_1 \cap s_2) \times (t_1 \cap t_2), \qquad s \times (t_1 \cup t_2) = (s \times t_1) \cup (s \times t_2).$$

These are `Set.prod_inter_prod` and `Set.prod_union`, with `Set.union_prod`, `Set.inter_prod` and `Set.prod_inter` for the other sides. The union of two products is not a product, and the complement of a product is a union of two products:

$$(s \times t)^c = (s^c \times \beta) \cup (\alpha \times t^c).$$

This is `Set.compl_prod_eq_union`. The rules with an empty factor need care. The product is empty if and only if one factor is empty (`Set.prod_eq_empty_iff`), and so the inclusion of products has an extra case:

$$s \times t \subseteq s_1 \times t_1 \iff (s \subseteq s_1 \text{ and } t \subseteq t_1) \text{ or } s = \varnothing \text{ or } t = \varnothing.$$

This is `Set.prod_subset_prod_iff`. The easy direction is `Set.prod_mono`, which needs no condition. In the same way, `Set.fst_image_prod` gives $\pi_1(s \times t) = s$ only when $t$ is nonempty, and `Set.prod_eq_prod_iff` describes when two products are equal. Two products are disjoint if and only if the first factors are disjoint or the second factors are disjoint (`Set.disjoint_prod`).

The products with a singleton are images: `Set.prod_singleton` gives $s \times \{b\} = \{(a, b) \mid a \in s\}$. The products of images and ranges are images and ranges of a product map: `Set.prod_image_image_eq` and `Set.prod_range_range_eq`.

#### The diagonal and the off diagonal

The diagonal `Set.diagonal α` is the set of pairs $(x, x)$, and `Set.offDiag s` is the set of pairs $(x, y)$ in $s \times s$ with $x \ne y$. Their membership rules are `Set.mem_diagonal_iff` and `Set.mem_offDiag`. The two sets split the square: `Set.prod_sdiff_diagonal` says $(s \times s) \setminus \Delta = \operatorname{offDiag}(s)$. The off diagonal grows by two strips when a point is added:

$$a \notin s \implies \operatorname{offDiag}(s \cup \{a\}) = \operatorname{offDiag}(s) \cup (\{a\} \times s) \cup (s \times \{a\}).$$

This is `Set.offDiag_insert`. For finsets it gives the count $|s|(|s| - 1)$ of the off diagonal by induction. The graph of a function on a set, `Set.graphOn f s`, is the set of pairs $(x, f(x))$ with $x \in s$, and `Set.graphOn_univ_eq_range` says that the graph on the whole type is a range.

#### Products of a family

For an index set $s \subseteq \iota$ and sets $t_i \subseteq \alpha_i$, `Set.pi s t` is the set of dependent functions $f$ with $f(i) \in t_i$ for each $i \in s$. The rule is `Set.mem_pi`, and `Set.mem_univ_pi` is the case $s = $ `Set.univ`, written `Set.univ.pi t`. The product distributes over intersections (`Set.pi_inter_distrib`), and is monotone in $t$ (`Set.pi_mono`).

The empty case is the source of the conditions. The product is nonempty if and only if for each $i$ some point of $\alpha_i$ satisfies the condition for $i$:

$$\operatorname{pi}(s, t) \ne \varnothing \iff \forall i,\ \exists x,\ i \in s \to x \in t_i.$$

This is `Set.pi_nonempty_iff`, and it uses the axiom of choice to pick one point in each $t_i$. The dual rule `Set.pi_eq_empty_iff` says that the product is empty if and only if some $\alpha_i$ is empty, or some $t_i$ with $i \in s$ is empty. So the inclusion of products over all indices also has an extra case:

$$\operatorname{pi}(\alpha, t_1) \subseteq \operatorname{pi}(\alpha, t_2) \iff (\forall i,\ t_1(i) \subseteq t_2(i)) \text{ or } \exists i,\ t_1(i) = \varnothing.$$

This is `Set.univ_pi_subset_univ_pi_iff`. The module also gives the images of a product under an evaluation (`Set.eval_image_pi`) and the preimages of a product under `Function.update` (`Set.update_preimage_pi`).

#### Sigma sets

For dependent pairs, `Set.sigma s t` is the set of pairs $\langle i, x \rangle$ with $i \in s$ and $x \in t_i$, with the rule `Set.mem_sigma_iff`. It is the disjoint union of the sets $t_i$ for $i \in s$:

$$\operatorname{sigma}(s, t) = \bigcup_{i \in s} \{\langle i, x \rangle \mid x \in t_i\}.$$

This is `Set.sigma_eq_biUnion`. Unlike the product, the sigma set is empty only when each $t_i$ with $i \in s$ is empty (`Set.sigma_eq_empty_iff`), so no condition of nonemptiness appears in its rules. The other results of `Mathlib.Data.Set.Sigma` are distributive laws (`Set.sigma_union`, `Set.sigma_inter_sigma`), rules for singletons and insertion, and the rules `Set.biUnion_sigma` and `Set.biInter_sigma` that split a union over a sigma set into two unions.

#### Binary images

The module `Mathlib.Data.Set.NAry` gives the image of two sets under a function of two arguments. Its membership rule `Set.mem_image2` is in `Mathlib.Data.Set.Operations`: $c \in \operatorname{image2}(f, s, t)$ if and only if $c = f(a, b)$ for some $a \in s$ and $b \in t$. The pointwise sum $s + t$ and product $s \cdot t$ of sets in an algebraic structure are binary images, so the rules of this module apply to them.

The binary image is the image of the product under the uncurried function:

$$\{f(p_1, p_2) \mid p \in s \times t\} = \operatorname{image2}(f, s, t).$$

This is `Set.image_prod`, with `Set.image_uncurry_prod` as the form with the uncurried function, and `Set.image2_mk_eq_prod` says that the binary image of the pair map $(a, b) \mapsto (a, b)$ is the product. The table gives the main rules.

| Lean name | Statement |
|---|---|
| `Set.image2_subset_iff` | $\operatorname{image2}(f, s, t) \subseteq u \iff \forall a \in s,\ \forall b \in t,\ f(a, b) \in u$ |
| `Set.image2_subset` | monotone in $s$ and $t$ |
| `Set.image2_union_left` | $\operatorname{image2}(f, s \cup s', t) = \operatorname{image2}(f, s, t) \cup \operatorname{image2}(f, s', t)$ |
| `Set.image2_inter_subset_left` | for an intersection only an inclusion holds |
| `Set.image2_singleton_left` | $\operatorname{image2}(f, \{a\}, t) = f(a, \cdot)(t)$ |
| `Set.image2_swap` | swap the arguments and the sets |
| `Set.image_image2` | $g(\operatorname{image2}(f, s, t)) = \operatorname{image2}(g \circ f, s, t)$ |

A second group of results transfers an identity of functions to an identity of binary images. For example, `Set.image2_assoc` turns an associativity law $f(g(a, b), c) = f'(a, g'(b, c))$ into the equality of the two ways to form the binary image of three sets, and `Set.image2_comm` does the same for a commutativity law. `Set.image_image2_distrib` transfers a law $g(f(a, b)) = f'(g_1(a), g_2(b))$. The pointwise operations on sets get their associativity and commutativity from these rules.

#### Sets as a monad

The module `Mathlib.Data.Set.Functor` makes `Set` an alternative and a commutative applicative functor, with lawful instances. It also defines a monad structure `Set.monad`, but not as a global instance, because it has no computational content. A proof that needs `>>=` on sets adds `attribute [local instance] Set.monad`, or works in the type `SetM`, a copy of `Set` with the monad as an instance. The operations are the familiar operations on sets:

1. `Set.fmap_eq_image`: `f <$> s` is the image $f(s)$;
2. `Set.pure_def`: `pure a` is $\{a\}$;
3. `Set.bind_def`: `s >>= f` is $\bigcup_{i \in s} f(i)$;
4. `Set.seq_eq_set_seq`: `s <*> t` is `Set.seq s t`, the set of values $f(x)$ with $f \in s$ and $x \in t$.

The module also gives the coercion of a set of points of a subset to a set of the type, with the rules `Set.mem_image_val_of_mem` and `Set.image_val_subset`. The finiteness of these monad operations is in Chapter 5.

#### Common errors

1. A learner applies `Set.fst_image_prod` and gets a goal that asks for $t$ to be nonempty. The image $\pi_1(s \times t)$ is empty when $t$ is empty. Prove that $t$ is nonempty, or use `Set.fst_image_prod_subset`, which needs no condition.
2. A learner tries to prove $s \times t \subseteq s_1 \times t_1 \to s \subseteq s_1$ with no condition. It is false when $t$ is empty. Use `Set.prod_subset_prod_iff` and handle the empty cases.
3. A learner writes `s >>= f` for a set and gets an error that no `Bind` instance is found. The monad on `Set` is not a global instance. Add `attribute [local instance] Set.monad`, or write the union $\bigcup_{i \in s} f(i)$ directly.

### Exercises

1. (A) Prove `Set.prod_inter_prod` with `ext` and `Set.mem_prod`.
2. (A) Find sets $s_1, s_2 \subseteq \mathbb{N}$ and $t_1, t_2 \subseteq \mathbb{N}$ such that $(s_1 \times t_1) \cup (s_2 \times t_2)$ is not a product of two sets.
3. (A) Compute `Set.image2 (· + ·) {1, 2} {10, 20}` in $\mathbb{N}$.
4. (B) Use `Set.offDiag_insert` to show that the off diagonal of a set with $n$ points has $n(n - 1)$ points.
5. (B) Show that `Set.univ.pi t` with $t_i = \varnothing$ for one index is empty, and give the condition of `Set.pi_eq_empty_iff` that holds.
6. (C) Use `Set.image2_assoc` to prove $(s + t) + u = s + (t + u)$ for sets of natural numbers written as binary images.

### Reference

<?reference?>
