---
title: The Boolean algebra of sets, images and preimages
kind: theory
modules:
  - Mathlib.Data.Set.Image
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

Volume 1 shows that a set `s : Set α` is a predicate on the type `α`. So the operations on sets are the operations of logic: the union is `or`, the intersection is `and`, and the complement is `not`. The sets of a type are a complete Boolean algebra, and the lemmas of Volume 4 for lattices apply to them. A function `f : α → β` moves a set forward with the image `f '' s` and moves a set back with the preimage `f ⁻¹' t`. This section gives the operations, the rules that connect the image and the preimage, and the cases where a rule needs a hypothesis.

### Definitions

**Definition (Union, intersection, complement, difference).** For sets `s` and `t` of `α`, the union `s ∪ t` is `{x | x ∈ s ∨ x ∈ t}`, the intersection `s ∩ t` is `{x | x ∈ s ∧ x ∈ t}`, the complement `sᶜ` is `{x | x ∉ s}`, and the difference `s \ t` is `{x | x ∈ s ∧ x ∉ t}`.

**Definition (Image).** For `f : α → β` and `s : Set α`, the image `f '' s` is the set of the `y : β` such that `f x = y` for some `x ∈ s`. The range `Set.range f` is the image of the whole type.

**Definition (Preimage).** For `f : α → β` and `t : Set β`, the preimage `f ⁻¹' t` is the set of the `x : α` such that `f x ∈ t`.

### Theorems and proofs

**Theorem (Image and preimage are adjoint).** For $f : \alpha \to \beta$, $s \subseteq \alpha$ and $t \subseteq \beta$, $f(s) \subseteq t$ if and only if $s \subseteq f^{-1}(t)$.

*Proof.* Suppose that $f(s) \subseteq t$ and $x \in s$. Then $f(x) \in f(s)$, so $f(x) \in t$, and $x \in f^{-1}(t)$. Now suppose that $s \subseteq f^{-1}(t)$, and let $y \in f(s)$. Then $y = f(x)$ for some $x \in s$, and $f(x) \in t$. $\square$

**Theorem (The two round trips).** For every $s$ and $t$, $s \subseteq f^{-1}(f(s))$ and $f(f^{-1}(t)) \subseteq t$.

*Proof.* Apply the adjunction to $f(s) \subseteq f(s)$ for the first inclusion, and to $f^{-1}(t) \subseteq f^{-1}(t)$ for the second. $\square$

The first inclusion is an equality when $f$ is injective (`Set.preimage_image_eq`). The second is an equality when $f$ is surjective (`Set.image_preimage_eq`).

**Theorem (The preimage keeps all operations).** The preimage of a union, an intersection or a complement is the union, the intersection or the complement of the preimages.

*Proof.* Each side has the same membership condition after the definitions unfold. For example, $x \in f^{-1}(t_1 \cup t_2)$ means $f(x) \in t_1 \lor f(x) \in t_2$. $\square$

**Theorem (The image keeps unions).** The image satisfies $f(s_1 \cup s_2) = f(s_1) \cup f(s_2)$ and $f(s_1 \cap s_2) \subseteq f(s_1) \cap f(s_2)$.

*Proof.* A point $f(x)$ with $x \in s_1 \cup s_2$ is in $f(s_1)$ or in $f(s_2)$, and the converse is the same argument. For the intersection, a point $f(x)$ with $x \in s_1 \cap s_2$ is in both images. $\square$

::: mathlib
`Set.image_subset_iff` · `Mathlib.Data.Set.Image`

The adjunction between the image and the preimage. A proof of `f '' s ⊆ t` usually starts with `rw [Set.image_subset_iff]`, because a statement about the preimage is a statement about each point of `s`.

<?decl Set.image_subset_iff?>
:::

::: mathlib
`Set.image_inter_subset` · `Mathlib.Data.Set.Image`

The image of an intersection is a subset of the intersection of the images. The equality needs an injective function, and the lemma for it is `Set.image_inter`.

<?decl Set.image_inter_subset?>
:::

### Examples

**Example (Operations as logic).** After `simp` unfolds the membership, the statement is a statement of propositional logic, and `tauto` proves it.

<?lean MathlibHandbook/V03/C01/Examples.lean#set_ops?>

**Example (De Morgan).** The complement of a union is the intersection of the complements.

<?lean MathlibHandbook/V03/C01/Examples.lean#compl_union?>

**Example (An image).** The image of `ℕ` under $n \mapsto 2n$ is the set of even numbers.

<?lean MathlibHandbook/V03/C01/Examples.lean#image?>

**Example (A preimage).** The preimage of $\{n \mid n < 3\}$ under $n \mapsto n + 1$ is $\{n \mid n < 2\}$.

<?lean MathlibHandbook/V03/C01/Examples.lean#preimage?>

**Example (The adjunction).**

<?lean MathlibHandbook/V03/C01/Examples.lean#galois?>

**Counterexample (The image of an intersection).** The constant function $0$ sends $\{0\}$ and $\{1\}$ to $\{0\}$. The intersection $\{0\} \cap \{1\}$ is empty, so its image is empty, but the intersection of the two images is $\{0\}$.

<?lean MathlibHandbook/V03/C01/Examples.lean#image_inter?>

### The library around it

Each operation has a membership lemma: `Set.mem_union`, `Set.mem_inter_iff`, `Set.mem_compl_iff`, `Set.mem_sdiff`, `Set.mem_image` and `Set.mem_preimage`. The older name `Set.mem_diff` is deprecated. The lemmas for the image have the prefix `Set.image_`, and the lemmas for the preimage have the prefix `Set.preimage_`. The lemma `Set.image_comp` gives the image under a composition, and `Set.preimage_comp` gives the preimage. The laws of a Boolean algebra, such as `Set.compl_union` and `compl_compl`, come from the instance of the Boolean algebra on `Set α`, so the general lemmas of Volume 4 also apply. The indexed union `⋃ i, s i` and the indexed intersection `⋂ i, s i` have the membership lemmas `Set.mem_iUnion` and `Set.mem_iInter`.

### Exercises

1. (A) Write the set of the natural numbers that are even and not divisible by four, with the operations of this section.
2. (A) Give a function $f$ and a set $t$ such that $f(f^{-1}(t)) \neq t$.
3. (B) Show that $f(s_1 \cap s_2) = f(s_1) \cap f(s_2)$ when $f$ is injective.
4. (B) Show that $f^{-1}(t^c) = (f^{-1}(t))^c$.
5. (L) Prove that $s \cap t \subseteq s$. The solution is `inter_subset_left_example`.
6. (L) Prove that the preimage of a union is the union of the preimages. The solution is `preimage_union_example`.
7. (L) Prove that $s \subseteq f^{-1}(f(s))$. The solution is `subset_preimage_image_example`.
8. (L) Prove that $f(f^{-1}(t)) \subseteq t$. The solution is `image_preimage_subset_example`.

### Notes and history

The notation `f '' s` for the image and `f ⁻¹' t` for the preimage comes from the first library of Lean 3. The two marks keep the notation apart from the application `f s` of a function to a term. The adjunction of the image and the preimage is the simplest example of a Galois connection, and Volume 4 shows the general idea.

### Reference

<?reference?>
