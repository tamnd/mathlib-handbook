---
title: The Boolean algebra of sets, images and preimages
kind: theory
modules:
  - Mathlib.Data.Set.Image
  - Mathlib.Basic.SetLike.Basic
explains:
  E3: [Set.image_subset_iff]
  E2: [Set.image_preimage_subset, Set.subset_preimage_image, Set.image_inter_subset, Set.preimage_union, Set.image_union]
  E1: auto
families: []
requires: [V01.C02, V01.C03]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V03/C01/Examples.lean
  - MathlibHandbook/V03/C01/Exercises.lean
  - MathlibHandbook/V03/C01/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The Boolean algebra of sets, images and preimages

### Overview

Volume 1 shows that a set `s : Set α` is a predicate on the type `α`. A point `x` is in `s` when the proposition `s x` is true. So the operations on sets are the operations of logic in another form. The union is "or", the intersection is "and", the complement is "not" and the inclusion is "implies". Each law of sets, for example the law of De Morgan, is a law of propositional logic about one point. This fact is the main method of the section: to prove an equality of sets, take a point, write out what it means for the point to be in each side, and compare two propositions.

A function $f : \alpha \to \beta$ moves sets in two directions. The image $f(s)$ moves a set of $\alpha$ forward to $\beta$. The preimage $f^{-1}(t)$ moves a set of $\beta$ back to $\alpha$. The two operations do not behave in the same way. The preimage keeps every operation of the Boolean algebra. The image keeps the unions, but it can make an intersection larger and it does not keep the complement. The main theorem of the section explains this difference: the image is the left adjoint of the preimage, that is, $f(s) \subseteq t$ if and only if $s \subseteq f^{-1}(t)$. After this section the reader can prove each standard identity of images and preimages, can say which identities need an injective or a surjective function, and can use the lemmas `Set.image_subset_iff`, `Set.preimage_union` and their relatives in Mathlib.

### Definitions

In this section $\alpha$ and $\beta$ are types, $s, s_1, s_2$ are sets of $\alpha$, and $t, t_1, t_2$ are sets of $\beta$.

**Definition (Union, intersection, complement, difference).** The union, the intersection, the complement and the difference are the sets $$s_1 \cup s_2 = \{x \mid x \in s_1 \lor x \in s_2\}, \quad s_1 \cap s_2 = \{x \mid x \in s_1 \land x \in s_2\}, \quad s^c = \{x \mid x \notin s\}, \quad s_1 \setminus s_2 = \{x \mid x \in s_1 \land x \notin s_2\}.$$

The complement is taken in the type $\alpha$. There is no "universe" outside the type. This is one place where Mathlib differs from a text that works inside one large set. The difference is not a new operation: $s_1 \setminus s_2 = s_1 \cap s_2^c$, and Mathlib proves this as `Set.sdiff_eq`.

**Definition (Inclusion and equality).** The set $s_1$ is a subset of $s_2$, written $s_1 \subseteq s_2$, when each $x \in s_1$ is in $s_2$. Two sets are equal when they have the same elements. This is the principle of extensionality, and in Lean the tactic `ext x` starts a proof of it.

**Definition (Image).** For $f : \alpha \to \beta$, the image of $s$ is $$f(s) = \{y \in \beta \mid \exists x \in s,\ f(x) = y\}.$$ The range of $f$ is $f(\alpha)$, the image of the whole type.

**Definition (Preimage).** For $f : \alpha \to \beta$, the preimage of $t$ is $$f^{-1}(t) = \{x \in \alpha \mid f(x) \in t\}.$$

*Remarks.* The notation $f^{-1}(t)$ does not need an inverse function. It is defined for each function. The membership in a preimage is a direct condition, $x \in f^{-1}(t) \iff f(x) \in t$, with no quantifier. The membership in an image has an existential quantifier. This difference is the reason why the preimage is easier to work with, and why many proofs about images start by a move to preimages.

::: mathlib
`Set.mem_preimage` · `Mathlib.Data.Set.Operations`

In Mathlib the image is written `f '' s` and the preimage `f ⁻¹' t`. The marks `''` and `⁻¹'` keep the notation apart from the application `f s`. The membership lemma `Set.mem_preimage` is true by definition, so `simp` and `rfl` both use it. The membership lemma for the image, `Set.mem_image`, has the form `y ∈ f '' s ↔ ∃ x, x ∈ s ∧ f x = y`. Note the order `f x = y` in the equation: `rintro ⟨x, hx, rfl⟩` then replaces `y` by `f x`.

<?decl Set.mem_preimage?>
:::

### Theorems and proofs

**Theorem (The laws of a Boolean algebra).** For all sets $s_1, s_2, s_3$ of $\alpha$, the following laws hold.

1. $s_1 \cap (s_2 \cup s_3) = (s_1 \cap s_2) \cup (s_1 \cap s_3)$ and $s_1 \cup (s_2 \cap s_3) = (s_1 \cup s_2) \cap (s_1 \cup s_3)$.
2. $(s_1 \cup s_2)^c = s_1^c \cap s_2^c$ and $(s_1 \cap s_2)^c = s_1^c \cup s_2^c$.
3. $(s^c)^c = s$, $s \cup s^c = \alpha$ and $s \cap s^c = \emptyset$.

*Proof.* Each law is an equality of sets, so it is enough to show that a point $x$ is in the left side if and only if it is in the right side. Write $p_i$ for the proposition $x \in s_i$. Then the membership in the left side and in the right side of each law becomes a formula of propositional logic in $p_1, p_2, p_3$. For the first law of 1, the formulas are $p_1 \land (p_2 \lor p_3)$ and $(p_1 \land p_2) \lor (p_1 \land p_3)$. These have the same truth value for each of the eight choices of truth values of $p_1, p_2, p_3$. For the first law of 2, the formulas are $\lnot(p_1 \lor p_2)$ and $\lnot p_1 \land \lnot p_2$, and they agree in each of the four cases. The other laws are the same, with the laws $\lnot \lnot p \iff p$, $p \lor \lnot p$ and $\lnot(p \land \lnot p)$ of classical logic for 3. $\square$

**Theorem (Image and preimage are adjoint).** For $f : \alpha \to \beta$, $s \subseteq \alpha$ and $t \subseteq \beta$, $$f(s) \subseteq t \iff s \subseteq f^{-1}(t).$$

*Proof.* Suppose first that $f(s) \subseteq t$. Let $x \in s$. Then $f(x) \in f(s)$, with the witness $x$. So $f(x) \in t$, and this means $x \in f^{-1}(t)$. Thus $s \subseteq f^{-1}(t)$.

Now suppose that $s \subseteq f^{-1}(t)$. Let $y \in f(s)$. By the definition of the image there is $x \in s$ with $f(x) = y$. Since $x \in f^{-1}(t)$, $f(x) \in t$, so $y \in t$. Thus $f(s) \subseteq t$. $\square$

The adjunction is the reason for most of the rules below. A statement $f(s) \subseteq t$ has a hidden existential quantifier. The adjunction changes it into the statement "for each $x \in s$, $f(x) \in t$", which has none.

::: mathlib
`Set.image_subset_iff` · `Mathlib.Data.Set.Image`

The lemma is the adjunction in the form `f '' s ⊆ t ↔ s ⊆ f ⁻¹' t`. A proof of `f '' s ⊆ t` usually starts with `rw [Set.image_subset_iff]`, then `intro x hx`. In the language of Volume 4 the lemma says that `Set.image f` and `Set.preimage f` form a Galois connection, and Mathlib records this as `Set.image_preimage`. All the general facts about Galois connections then apply: the left adjoint keeps the suprema (unions), and the right adjoint keeps the infima (intersections).

<?decl Set.image_subset_iff?>
:::

**Theorem (The two round trips).** For each $s \subseteq \alpha$ and $t \subseteq \beta$, $$s \subseteq f^{-1}(f(s)) \quad \text{and} \quad f(f^{-1}(t)) \subseteq t.$$ If $f$ is injective, the first inclusion is an equality. If $f$ is surjective, the second inclusion is an equality.

*Proof.* For the first inclusion apply the adjunction to the true statement $f(s) \subseteq f(s)$. For the second apply it, from right to left, to the true statement $f^{-1}(t) \subseteq f^{-1}(t)$.

Assume that $f$ is injective, and let $x \in f^{-1}(f(s))$. Then $f(x) \in f(s)$, so there is $x' \in s$ with $f(x') = f(x)$. By injectivity $x' = x$, so $x \in s$. This gives $f^{-1}(f(s)) \subseteq s$.

Assume that $f$ is surjective, and let $y \in t$. There is $x$ with $f(x) = y$. Then $f(x) \in t$, so $x \in f^{-1}(t)$, and $y = f(x) \in f(f^{-1}(t))$. This gives $t \subseteq f(f^{-1}(t))$. $\square$

In general $f(f^{-1}(t)) = t \cap f(\alpha)$. The image of a preimage loses exactly the points of $t$ that $f$ does not reach. The lemma is `Set.image_preimage_eq_inter_range`.

::: mathlib
`Set.subset_preimage_image` · `Mathlib.Data.Set.Image`

The first round trip, with no hypothesis. The equality forms are `Set.preimage_image_eq`, which takes `Function.Injective f`, and `Set.image_preimage_eq`, which takes `Function.Surjective f`. The hypothesis is an explicit argument, so a proof writes `Set.preimage_image_eq s hf`.

<?decl Set.subset_preimage_image?>
:::

**Theorem (The preimage keeps all operations).** For $f : \alpha \to \beta$, $$f^{-1}(t_1 \cup t_2) = f^{-1}(t_1) \cup f^{-1}(t_2), \quad f^{-1}(t_1 \cap t_2) = f^{-1}(t_1) \cap f^{-1}(t_2), \quad f^{-1}(t^c) = f^{-1}(t)^c.$$ The preimage is also monotone: $t_1 \subseteq t_2$ implies $f^{-1}(t_1) \subseteq f^{-1}(t_2)$.

*Proof.* Let $x \in \alpha$. The point $x$ is in $f^{-1}(t_1 \cup t_2)$ if and only if $f(x) \in t_1 \cup t_2$, that is, $f(x) \in t_1$ or $f(x) \in t_2$. This is the condition $x \in f^{-1}(t_1)$ or $x \in f^{-1}(t_2)$, that is, $x \in f^{-1}(t_1) \cup f^{-1}(t_2)$. The intersection is the same with "and" in place of "or". For the complement, $x \in f^{-1}(t^c)$ if and only if $f(x) \notin t$, if and only if $x \notin f^{-1}(t)$. For the monotonicity, if $f(x) \in t_1$ then $f(x) \in t_2$. $\square$

**Theorem (The image keeps unions).** For $f : \alpha \to \beta$, $$f(s_1 \cup s_2) = f(s_1) \cup f(s_2) \quad \text{and} \quad f(s_1 \cap s_2) \subseteq f(s_1) \cap f(s_2).$$ If $f$ is injective, the inclusion is an equality.

*Proof.* Let $y \in f(s_1 \cup s_2)$, with $y = f(x)$ and $x \in s_1 \cup s_2$. If $x \in s_1$ then $y \in f(s_1)$, and if $x \in s_2$ then $y \in f(s_2)$. Conversely, the image is monotone, because $s \subseteq s'$ and $y = f(x)$ with $x \in s$ give $x \in s'$. Since $s_1$ and $s_2$ are subsets of $s_1 \cup s_2$, both $f(s_1)$ and $f(s_2)$ are subsets of $f(s_1 \cup s_2)$, and so is their union.

For the intersection, $s_1 \cap s_2$ is a subset of $s_1$ and of $s_2$, so by monotonicity its image is a subset of $f(s_1)$ and of $f(s_2)$.

Now let $f$ be injective, and let $y \in f(s_1) \cap f(s_2)$. There are $x_1 \in s_1$ and $x_2 \in s_2$ with $f(x_1) = y = f(x_2)$. By injectivity $x_1 = x_2$, so this point is in $s_1 \cap s_2$, and $y \in f(s_1 \cap s_2)$. $\square$

::: mathlib
`Set.image_inter_subset` · `Mathlib.Data.Set.Image`

The inclusion needs no hypothesis. The equality is `Set.image_inter`, with the hypothesis `Function.Injective f`. A weaker hypothesis is enough: $f(x) = f(y)$ implies $x = y$ for $x \in s_2$ and $y \in s_1$. This is the lemma `Set.image_inter_on`. Mathlib often has such a local form, and also the predicate `Set.InjOn f s` for a function that is injective on a set, because in analysis a function is often injective only on a part of its domain.

<?decl Set.image_inter_subset?>
:::

::: mathlib
`Set.preimage_union` · `Mathlib.Data.Set.Image`

The preimage of a union. The lemma has the `simp` attribute, as do `Set.preimage_inter` and `Set.preimage_compl`. So `simp` pushes a preimage inside each Boolean operation. The image lemma `Set.image_union` has the same form, but there is no simp lemma that pushes an image inside an intersection, because the equality is false in general.

<?decl Set.preimage_union?>
:::

### Examples

**Example (Operations as logic).** The equality $(s \cup t) \setminus s = t \setminus s$ is the law $(p \lor q) \land \lnot p \iff q \land \lnot p$ for one point. After `simp` unfolds the membership, `tauto` proves the law of logic.

<?lean MathlibHandbook/V03/C01/Examples.lean#set_ops?>

**Example (De Morgan).** The complement of a union is the intersection of the complements. In $\mathbb{N}$, take $s$ the even numbers and $t$ the multiples of $3$. Then $(s \cup t)^c$ is the set of numbers that are prime to $6$, that is $\{1, 5, 7, 11, 13, \ldots\}$, and $s^c \cap t^c$ is the set of odd numbers that are not multiples of $3$, the same set.

<?lean MathlibHandbook/V03/C01/Examples.lean#compl_union?>

**Example (An image).** The image of $\mathbb{N}$ under $n \mapsto 2n$ is the set of even numbers. The proof shows both inclusions. A point $2k$ of the image is even with the witness $k$. An even number $n = k + k$ is the image of $k$.

<?lean MathlibHandbook/V03/C01/Examples.lean#image?>

**Example (A preimage).** Let $f(n) = n + 1$ on $\mathbb{N}$. The preimage of $\{0, 1, 2\} = \{n \mid n < 3\}$ is the set of $n$ with $n + 1 < 3$, that is $\{0, 1\}$. The point $0$ of the target has no preimage, so $f(f^{-1}(\{0, 1, 2\})) = \{1, 2\}$, a proper subset of $\{0, 1, 2\}$. This is the second round trip with a function that is not surjective, and $\{1, 2\} = \{0, 1, 2\} \cap f(\mathbb{N})$ as the general rule says.

<?lean MathlibHandbook/V03/C01/Examples.lean#preimage?>

**Example (A computation with the square).** Let $f : \mathbb{Z} \to \mathbb{Z}$, $f(x) = x^2$, and $s = \{1, 2\}$. Then $f(s) = \{1, 4\}$ and $f^{-1}(\{1, 4\}) = \{-2, -1, 1, 2\}$. So $s \subsetneq f^{-1}(f(s))$: the first round trip is strict, because $f$ is not injective. With $t = \{-1, 0, 1, 2\}$, $f^{-1}(t) = \{-1, 0, 1\}$ and $f(f^{-1}(t)) = \{0, 1\}$, so the second round trip removes $-1$ and $2$, the points of $t$ that are not squares.

**Example (The adjunction).** The statement of the adjunction in Mathlib is one lemma.

<?lean MathlibHandbook/V03/C01/Examples.lean#galois?>

**Counterexample (The image of an intersection).** The hypothesis of injectivity in the equality $f(s_1 \cap s_2) = f(s_1) \cap f(s_2)$ is needed. The constant function $0$ sends $\{0\}$ and $\{1\}$ to $\{0\}$. The intersection $\{0\} \cap \{1\}$ is empty, so its image is empty, but the intersection of the two images is $\{0\}$.

<?lean MathlibHandbook/V03/C01/Examples.lean#image_inter?>

**Counterexample (The image of a complement).** For the same constant function on $\mathbb{N}$ and $s = \{0\}$, $f(s^c) = \{0\}$ and $f(s)^c = \mathbb{N} \setminus \{0\}$. Neither set contains the other. With an injective function, $f(s^c) \subseteq f(s)^c$ holds; with a surjective function, $f(s)^c \subseteq f(s^c)$ holds; with a bijection the two are equal.

### Common errors

A learner often writes $f^{-1}$ and thinks of an inverse function. The preimage exists for each function, and $f^{-1}(\{y\})$ can be empty or have many points. A second error is to use the equality $f(s_1 \cap s_2) = f(s_1) \cap f(s_2)$ with no check of injectivity. A third error, special to Lean, is to forget that `s ⊆ t` unfolds to `∀ x, x ∈ s → x ∈ t`: the tactic `intro x hx` works on a goal `s ⊆ t` directly. A fourth error is to try `rw` with `Set.mem_image` when the goal is an inclusion of images; first use `Set.image_subset_iff`, or take a point with `rintro _ ⟨x, hx, rfl⟩`.

### The library around it

Each operation has a membership lemma: `Set.mem_union`, `Set.mem_inter_iff`, `Set.mem_compl_iff`, `Set.mem_sdiff`, `Set.mem_image`, `Set.mem_preimage` and `Set.mem_range`. The older name `Set.mem_diff` is deprecated in favour of `Set.mem_sdiff`. The lemmas for the image have the prefix `Set.image_`, and the lemmas for the preimage have the prefix `Set.preimage_`: `Set.image_empty`, `Set.image_singleton`, `Set.image_univ`, `Set.preimage_inter`, `Set.preimage_compl` and `Set.preimage_mono`. The lemma `Set.image_comp` gives $(g \circ f)(s) = g(f(s))$, and `Set.preimage_comp` gives $(g \circ f)^{-1}(u) = f^{-1}(g^{-1}(u))$. The laws of a Boolean algebra, such as `Set.compl_union` and `compl_compl`, come from the instance of a complete Boolean algebra on `Set α`, so the general lemmas of Volume 4 for lattices also apply, for example `inf_sup_left` for the distributive law. The image of a nonempty set is nonempty, `Set.Nonempty.image`. The indexed operations `⋃ i, s i` and `⋂ i, s i` are the subject of the next section. The table at the end of the section lists the declarations.

Many types of Mathlib are sets with more structure: finsets, subgroups, submodules and subrings. The file `Mathlib.Basic.SetLike.Basic` gives them one interface. A type $A$ has an instance `SetLike A B` when it has a coercion `SetLike.coe` to `Set B` that is injective, by `SetLike.coe_injective`. The instance gives a membership relation, with `SetLike.mem_coe` for $x \in (p : \mathrm{Set}\ B) \leftrightarrow x \in p$, and a coercion of $p$ to a type, with `SetLike.coe_mem` for the elements of that type. Two elements with the same members are equal, by `SetLike.ext`. The order comes from the inclusion of sets: `PartialOrder.ofSetLike` makes $A$ a partial order, the classes `IsMemLE` and `IsConcreteLE` say that an order on $A$ agrees with the inclusion, `SetLike.le_def` unfolds $p \le q$ to the inclusion of members, `SetLike.coe_subset_coe` turns an inclusion of the coerced sets into $p \le q$, and `SetLike.exists_of_lt` gives an element of $q$ that is not in $p$ when $p < q$. So each rule of this section for sets applies to a set-like type after one rewrite with `SetLike.mem_coe`.

### Exercises

1. (A) Write the set of the natural numbers that are even and not divisible by four with the operations of this section, and list its elements below $20$.
2. (A) Give a function $f$ and a set $t$ such that $f(f^{-1}(t)) \neq t$. Hint: take $f$ not surjective, and $t$ that contains a point outside the range.
3. (A) For $f : \mathbb{Z} \to \mathbb{Z}$, $f(x) = |x|$, compute $f(\{-3, -1, 2\})$, $f^{-1}(\{0, 1\})$ and $f^{-1}(\{-1\})$.
4. (B) Show that $f(s_1 \cap s_2) = f(s_1) \cap f(s_2)$ for all $s_1, s_2$ if and only if $f$ is injective. Hint: for the converse, take $s_1 = \{x_1\}$ and $s_2 = \{x_2\}$ with $f(x_1) = f(x_2)$.
5. (B) Show that $f^{-1}(t^c) = (f^{-1}(t))^c$, and show that $f(s^c) \supseteq f(s)^c$ for each $s$ if and only if $f$ is surjective.
6. (B) Prove that $f(s) \cap t = f(s \cap f^{-1}(t))$. This is the projection formula. Hint: take a point of each side and use the witness of the image.
7. (C) Let $f : \alpha \to \beta$. Show that the map $s \mapsto f(s)$ from the subsets of $\alpha$ to the subsets of $\beta$ is injective if and only if $f$ is injective, and surjective if and only if $f$ is surjective.
8. (L) Prove that $s \cap t \subseteq s$. The solution is `inter_subset_left_example`.
9. (L) Prove that the preimage of a union is the union of the preimages. The solution is `preimage_union_example`.
10. (L) Prove that $s \subseteq f^{-1}(f(s))$. The solution is `subset_preimage_image_example`.
11. (L) Prove that $f(f^{-1}(t)) \subseteq t$. The solution is `image_preimage_subset_example`.

### Notes and history

Boole gave the algebra of classes in *The Laws of Thought* (1854), and De Morgan stated his laws for propositions and classes at about the same time. The axioms of a Boolean algebra in the modern form are due to Huntington (1904). The image and the preimage are as old as the notion of a function on sets, but the clear separation of the two, with the rules for each operation, is from Hausdorff, *Grundzüge der Mengenlehre* (1914). The adjunction of the image and the preimage is a standard first example of a Galois connection, and of an adjoint pair of functors between two posets.

The notation `f '' s` for the image and `f ⁻¹' t` for the preimage comes from the first library of Lean 3. The two marks keep the notation apart from the application `f s` of a function to a term. In Mathlib, `Set α` is the type `α → Prop`, and the membership `x ∈ s` unfolds to `s x`. The file `Mathlib/Data/Set/Image.lean` was split from the original file of sets of Lean 3 by the Mathlib community, and it now holds several hundred lemmas.

### Reference

<?reference?>
