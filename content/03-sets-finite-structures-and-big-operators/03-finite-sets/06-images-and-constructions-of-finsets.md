---
title: Images, preimages and the constructions of finsets
kind: api
modules:
  - Mathlib.Data.Finset.Image
  - Mathlib.Data.Finset.PImage
  - Mathlib.Data.Finset.Preimage
  - Mathlib.Data.Finset.Option
  - Mathlib.Data.Finset.Sigma
  - Mathlib.Data.Finset.Sum
  - Mathlib.Data.Finset.Functor
  - Mathlib.Data.Finset.Fin
  - Mathlib.Data.Finset.Finsupp
  - Mathlib.Data.Finset.Pi
  - Mathlib.Data.Finset.PiInduction
  - Mathlib.Data.Finset.Piecewise
  - Mathlib.Data.Finset.Update
explains:
  E2: [Finset.mem_image, Finset.map_eq_image, Finset.image_subset_iff_subset_preimage, Finset.insertNone_eraseNone, Finset.card_disjSum, Finset.card_toLeft_add_card_toRight, Finset.pi_insert, Finset.card_finsupp, Finset.piecewise_insert]
  E1: auto
families: []
requires: [V03.C01, V03.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Images, preimages and the constructions of finsets

### Overview

Chapter 1 gave the image $f(s)$ and the preimage $f^{-1}(t)$ of a set. A finset needs the same operations, but each operation must produce a list with no repeated element, so each one has a cost in decidable equality or in a hypothesis of injectivity. The modules of this section give these operations for finsets: the image `Finset.image` and the map `Finset.map`, the image under a partial function, the preimage, and the constructions that build a finset of a new type from finsets of old types: the finsets of `Option α`, of a sigma type, of a sum type, of `Fin n`, of dependent functions and of finitely supported functions.

The section also gives two operations on functions that a finset controls: `Finset.piecewise`, which takes one function on $s$ and another outside $s$, and `Function.updateFinset`, which changes a function on the points of $s$. Sections 4 and 5 gave insert, erase, union, filter and difference. Each construction here is computed by them.

### The library around it

#### Image and map

For $f : \alpha \to \beta$ and a finset $s$ of $\alpha$, the image `Finset.image f s` is the finset of the values $f(a)$ with $a \in s$. Its multiset is `(Multiset.map f s.val).dedup`, by `Finset.image_val`, so it needs `DecidableEq β` to remove the repeated values. The map `Finset.map f s` takes an embedding `f : α ↪ β`. An embedding is injective, so the values are already distinct, and `Finset.map` needs no decidable equality. The two operations have the same elements.

**Theorem.** $b \in f(s) \iff \exists a \in s,\ f(a) = b$ (`Finset.mem_image`), and for an embedding $f$, `Finset.map f s = Finset.image f s` (`Finset.map_eq_image`).

*Proof.* An element is in a dedup of a multiset exactly when it is in the multiset, and $b$ is in the map of $s$ exactly when $b = f(a)$ for some $a \in s$. This gives the first claim. For the second, `Finset.mem_map` gives the same condition $\exists a \in s,\ f(a) = b$ for the map. Two finsets with the same elements are equal by extensionality. $\square$

The rule of thumb is the same as for `insert` and `Finset.cons`, or for `∪` and `Finset.disjUnion`: use `Finset.map` when an embedding is at hand and the proof should not depend on `DecidableEq`, and use `Finset.image` in all other cases. The simp normal form of a map along an embedding is `Finset.map`, and `Finset.map_eq_image` turns it into an image when a lemma needs one.

The names follow one pattern, as in `Finset.image_union` and `Finset.map_union`: the first part names the image or the map, and the second part names the operation that it commutes with. The table gives the main rules.

| Lean name | Statement |
|---|---|
| `Finset.coe_image` | $\uparrow f(s) = f '' \uparrow s$ as sets |
| `Finset.image_insert` | $f(\{a\} \cup s) = \{f(a)\} \cup f(s)$ |
| `Finset.image_union` | $f(s_1 \cup s_2) = f(s_1) \cup f(s_2)$ |
| `Finset.image_inter_subset` | $f(s \cap t) \subseteq f(s) \cap f(t)$ |
| `Finset.image_inter_of_injOn` | equality when $f$ is injective on $s \cup t$ |
| `Finset.image_sdiff` | $f(s \setminus t) = f(s) \setminus f(t)$ for an injective $f$ |
| `Finset.image_image` | $g(f(s)) = (g \circ f)(s)$ |
| `Finset.image_subset_iff` | $f(s) \subseteq t \iff \forall x \in s,\ f(x) \in t$ |
| `Finset.filter_image` | the filter of an image is the image of a filter |
| `Finset.image_const` | the image of a nonempty $s$ under a constant $b$ is $\{b\}$ |

The bridge to the language of sets is in `Finset.mapsTo_iff_image_subset` and `Finset.surjOn_iff_subset_image`. The lemma `Finset.fiber_nonempty_iff_mem_image` says that the fiber $\{x \in s : f(x) = y\}$ is nonempty exactly when $y \in f(s)$. For the card, `Finset.card_map` gives $|f(s)| = |s|$ for an embedding, and `Finset.card_image_of_injOn` gives the same for a map that is injective on $s$. These two are in the module of Section 1.

Two other operations go from a finset of $\alpha$ to a finset of a related type. `Finset.subtype p s` is the finset of the elements of $s$ that satisfy $p$, seen in the subtype `{x // p x}`, and `Finset.subtype_map` maps it back to the filter of $s$. `Finset.filterMap f s` applies $f : \alpha \to \mathrm{Option}\ \beta$ and keeps the values `some b`. The equivalences `Equiv.finsetCongr` and `Finset.equivMap` transport finsets along an equivalence of types.

#### Partial images and preimages

The module `Mathlib.Data.Finset.PImage` gives the image under a partial function `f : α →. β`. The finset `Finset.pimage f s` holds the values of $f$ at the points of $s$ where $f$ is defined, and `Finset.mem_pimage` states this: $b \in$ `pimage f s` exactly when $b \in f(a)$ for some $a \in s$. The finset `Part.toFinset o` of a partial value has one element or none.

The preimage of a finset is harder, because a preimage of a finite set can be infinite. Take the map $\mathbb{N} \to \mathrm{Unit}$: the preimage of the one point is all of $\mathbb{N}$. So `Finset.preimage s f hf` asks for a proof `hf : Set.InjOn f (f ⁻¹' s)`. Then each point of $s$ has at most one point above it, and the preimage is finite. Its membership rule is `Finset.mem_preimage`: $x \in f^{-1}(s) \iff f(x) \in s$.

**Theorem (Adjunction).** Let $f$ be injective on $f^{-1}(t)$. Then $f(s) \subseteq t \iff s \subseteq f^{-1}(t)$ (`Finset.image_subset_iff_subset_preimage`).

*Proof.* Both sides say that $f(x) \in t$ for each $x \in s$: the left side by `Finset.image_subset_iff`, and the right side by the membership rule of the preimage. $\square$

The other rules are the rules of Chapter 1 with the hypothesis of injectivity carried along: `Finset.preimage_union`, `Finset.preimage_inter`, `Finset.preimage_compl` for an injective map of finite types, and `Finset.image_preimage`, which says that $f(f^{-1}(s))$ is the part of $s$ in the range of $f$. The card follows: `Finset.card_preimage` gives $|f^{-1}(s)| = |\{x \in s : x \in \mathrm{range}\, f\}|$. For a sigma type, `Finset.sigma_preimage_mk` cuts a finset of $\Sigma a, \beta a$ into its fibers.

#### Finsets of Option, sums and Fin

The module `Mathlib.Data.Finset.Option` passes between `Finset α` and `Finset (Option α)`. The map `Finset.insertNone` sends $s$ to $\{\mathrm{none}\} \cup \mathrm{some}(s)$, and `Finset.eraseNone` keeps the $a$ with $\mathrm{some}\ a \in s$. Both maps are monotone, and the library bundles them as an order embedding and an order homomorphism. The card rules are `Finset.card_insertNone`, $|\mathrm{insertNone}\ s| = |s| + 1$, and `Finset.card_eraseNone_of_mem`, $|\mathrm{eraseNone}\ s| = |s| - 1$ when $\mathrm{none} \in s$.

**Theorem.** `insertNone (eraseNone s) = insert none s` for each finset $s$ of `Option α` (`Finset.insertNone_eraseNone`).

*Proof.* Compare the elements. The point $\mathrm{none}$ is on both sides. A point $\mathrm{some}\ a$ is on the left exactly when $a \in \mathrm{eraseNone}\ s$, that is when $\mathrm{some}\ a \in s$. It is on the right exactly when $\mathrm{some}\ a \in s$, because $\mathrm{some}\ a \ne \mathrm{none}$. $\square$

The module `Mathlib.Data.Finset.Sum` builds the finset `s.disjSum t` of `α ⊕ β` from finsets $s$ of $\alpha$ and $t$ of $\beta$. Its membership rule is `Finset.mem_disjSum`. The maps `Finset.toLeft` and `Finset.toRight` go back: they keep the left and the right parts of a finset $u$ of `α ⊕ β`. The two directions are an order isomorphism `Finset.sumEquiv : Finset (α ⊕ β) ≃o Finset α × Finset β`, and `Finset.gc_map_inl_toLeft` says that the map along `inl` is the left adjoint of `toLeft`.

**Theorem.** $|s \sqcup t| = |s| + |t|$ (`Finset.card_disjSum`), and $|u_{\mathrm{left}}| + |u_{\mathrm{right}}| = |u|$ for each finset $u$ of `α ⊕ β` (`Finset.card_toLeft_add_card_toRight`).

*Proof.* The finset `s.disjSum t` is the disjoint union of the maps of $s$ along `inl` and of $t$ along `inr`. The two maps are embeddings, so they keep the card, and the card of a disjoint union is the sum of the cards. For the second claim, $u$ is `u.toLeft.disjSum u.toRight` by `Finset.toLeft_disjSum_toRight`, and the first claim applies. $\square$

The module `Mathlib.Data.Finset.Fin` turns a finset $s$ of $\mathbb{N}$ with all elements below $n$ into a finset of `Fin n`. The finset is `Finset.attachFin s h`, with `h : ∀ m ∈ s, m < n`, and it has the same card by `Finset.card_attachFin`.

#### Sigma finsets

For a finset $s$ of $\iota$ and finsets $t_i$ of $\alpha_i$, `s.sigma t` is the finset of the pairs $\langle i, a \rangle$ with $i \in s$ and $a \in t_i$, by `Finset.mem_sigma`. It is the dependent form of the product $s \times t$, and `Finset.sigma_eq_biUnion` writes it as the union of the maps of the $t_i$ along $a \mapsto \langle i, a \rangle$. Section 2 of Chapter 6 sums over it. The module also gives `Finset.sigmaLift`, which lifts a function of two arguments in one fiber to the sigma types, with the value $\emptyset$ for two points in different fibers. Its card is `Finset.card_sigmaLift`.

#### Finsets of functions

For a finset $s$ of $\alpha$ and a finset $t_a$ for each $a$, the finset `s.pi t` holds the dependent functions $f$ with $f(a) \in t_a$ for each $a \in s$. The functions are defined only on $s$: their type is `(a : α) → a ∈ s → β a`. The membership rule is `Finset.mem_pi`. For the empty finset there is one function, `Finset.Pi.empty`, and `Finset.pi_empty` states this. The step of an induction adds one point.

**Theorem.** For $a \notin s$, `(insert a s).pi t` is the union over $b \in t_a$ of the images of `s.pi t` under the map that extends a function by the value $b$ at $a$ (`Finset.pi_insert`).

*Proof.* A function on $s \cup \{a\}$ is a pair of a value $b$ at $a$ and a function on $s$. The map `Finset.Pi.cons s a b` builds the function from the pair, and `Finset.Pi.cons_same` gives its value at $a$. Each function of `(insert a s).pi t` comes from its value at $a$, which is in $t_a$, and its restriction to $s$, which is in `s.pi t`. Conversely, each such pair gives a function of the left side. $\square$

With the insert rule for sums, this proof gives $|s.\mathrm{pi}\ t| = \prod_{a \in s} |t_a|$, which is `Finset.card_pi` in a later file. The module `Mathlib.Data.Finset.Finsupp` gives the same construction for finitely supported functions. The finset `s.finsupp t` holds the $f : \iota \to_0 \alpha$ with support in $s$ and $f(i) \in t_i$ for $i \in s$, by `Finset.mem_finsupp_iff`.

**Theorem.** $|s.\mathrm{finsupp}\ t| = \prod_{i \in s} |t_i|$ (`Finset.card_finsupp`).

*Proof.* A finitely supported function with support in $s$ is determined by its values on $s$, and each choice of values $f(i) \in t_i$ for $i \in s$ gives one. So `s.finsupp t` is in bijection with `s.pi t`, and the card of `s.pi t` is the product. $\square$

The module `Mathlib.Data.Finset.Pi` also gives the restriction `Finset.restrict s f` of a function to the subtype of $s$, the double restriction `Finset.restrict₂` for $s \subseteq t$, and `Finset.piDiag s ι`, the finset of the constant functions $\iota \to \alpha$ with value in $s$. The module `Mathlib.Data.Finset.PiInduction` gives induction on a family $g : \forall i, \mathrm{Finset}\ (\alpha_i)$ over a finite index type. `Finset.induction_on_pi` starts from the family of empty finsets and adds one point to one $g(i)$ in each step. The forms `Finset.induction_on_pi_max` and `Finset.induction_on_pi_min` add a point above, or below, all the points of $g(i)$.

#### Piecewise functions and updates

For a finset $s$ and functions $f, g$, `s.piecewise f g` is the function with value $f(i)$ for $i \in s$ and $g(i)$ for $i \notin s$. The two rules `Finset.piecewise_eq_of_mem` and `Finset.piecewise_eq_of_notMem` compute it, and `Finset.piecewise_coe` says that it agrees with `Set.piecewise` on the coerced set. The edge cases are `Finset.piecewise_empty`, with value $g$, and `Finset.piecewise_univ`, with value $f$.

**Theorem.** `(insert j s).piecewise f g = Function.update (s.piecewise f g) j (f j)` (`Finset.piecewise_insert`).

*Proof.* Compare the values at a point $i$. For $i = j$, both sides give $f(j)$. For $i \ne j$, the update does not change the value, and $i \in \{j\} \cup s \iff i \in s$, so both sides give $f(i)$ for $i \in s$ and $g(i)$ for $i \notin s$. $\square$

The special case `Finset.update_eq_piecewise` writes an update at one point as a piecewise function on $\{i\}$. The order rules `Finset.piecewise_le_piecewise` and `Finset.piecewise_mem_Icc` say that a piecewise function of $f \le g$ lies between $f$ and $g$. The module `Mathlib.Data.Finset.Update` generalizes the update to a finset. `Function.updateFinset x s y` takes the values of $y$ on $s$ and the values of $x$ outside $s$, by `Function.updateFinset_def`. The rule `Function.update_eq_updateFinset` writes a single update in this form, and `Function.updateFinset_updateFinset` combines two updates on disjoint finsets.

#### Finset as a functor

The module `Mathlib.Data.Finset.Functor` makes `Finset` a functor, an applicative and a monad. The instances use classical decidable equality, because the classes quantify over all types. The rules give the meaning of each operation: `Finset.fmap_def` says that `f <$> s` is `Finset.image f s`, `Finset.bind_def` says that `>>=` is `Finset.sup`, a union, and `Finset.image₂_def` writes the binary image with `<*>`. The module also gives `Finset.traverse`. In proofs, `Finset.image` and `Finset.biUnion` are the normal forms.

#### Common errors

1. A lemma on `Finset.image` does not apply to a goal with `Finset.map`, even when the two finsets are equal. Rewrite with `Finset.map_eq_image` first, or use the twin lemma for `Finset.map`, which often needs no injectivity hypothesis because the embedding carries it.
2. The rule $f(s \cap t) = f(s) \cap f(t)$ is false for a map that is not injective. For $f = 0$ on $s = \{1\}$ and $t = \{2\}$, the left side is empty and the right side is $\{0\}$. Use `Finset.image_inter_subset`, or prove injectivity for `Finset.image_inter_of_injOn`.
3. The elements of `s.pi t` are functions with two arguments, a point and a proof of membership. A function `f : ∀ a, β a` is not an element. Pass to it with `fun a _ ↦ f a`, as in `Finset.pi_singletons`, or use `Fintype.piFinset` for total functions on a finite type.

### Exercises

1. (A) Compute `Finset.image (fun n ↦ n % 3) (Finset.range 7)` and its card, and compare with the card of `Finset.range 7`.
2. (A) Prove that $f(s) = \emptyset \iff s = \emptyset$, and find the name of this rule in `Mathlib.Data.Finset.Image`.
3. (B) Prove $|f(s)| \le |s|$ by induction on $s$ with `Finset.image_insert`, and show that equality holds exactly when $f$ is injective on $s$.
4. (B) Let $f : \mathbb{Z} \to \mathbb{Z}$ be $f(x) = x^2$ and $s = \{1, 4, 9\}$. Explain why `Finset.preimage s f` needs a proof of injectivity that can not be given, and compute the set preimage instead.
5. (B) Prove $|s.\mathrm{pi}\ t| = \prod_{a \in s} |t_a|$ by induction on $s$ with `Finset.pi_insert`. Show first that the images in the union are pairwise disjoint.
6. (B) Let $f$ be the constant function $\mathrm{true}$ and $g$ the constant function $\mathrm{false}$ on $\iota$. Prove that `s.piecewise f g = t.piecewise f g` implies $s = t$.

### Reference

<?reference?>
