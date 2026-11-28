---
title: "The operations of finsets: insert, erase and the lattice"
kind: api
modules:
  - Mathlib.Data.Finset.Defs
  - Mathlib.Data.Finset.Attr
  - Mathlib.Data.Finset.Empty
  - Mathlib.Data.Finset.Insert
  - Mathlib.Data.Finset.Erase
  - Mathlib.Data.Finset.Attach
  - Mathlib.Data.Finset.Dedup
  - Mathlib.Data.Finset.Lattice.Basic
explains:
  E2: [Finset.ext, Finset.mem_insert, Finset.cons_induction, Finset.Nonempty.cons_induction, Finset.mem_erase, Finset.inter_union_distrib_left, Finset.toList_toFinset]
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

## The operations of finsets: insert, erase and the lattice

### Overview

Section 1 defined a finset as a multiset with no repeated element, and it used the operations of finsets to count. This section is the reference for the first layer of the library under that section. It gives the structure `Finset` with its order and its coercion to sets, the empty finset and the predicate `Finset.Nonempty`, the singleton, `insert` and `Finset.cons`, the principles of induction, the operation `Finset.erase`, the finset `Finset.attach` of the subtype, the passage from lists and multisets to finsets, and the lattice of finsets with the union and the intersection.

Each operation is defined on the underlying multiset of Chapter 2, and each one comes with a membership lemma of the form `Finset.mem_<op>`. These membership lemmas are the main tool. With them, `ext` and `simp` reduce an identity of finsets to a statement of logic about one element, as in Chapter 1 for sets. The next section continues with the filter, the difference and the Boolean algebra of finsets.

### The library around it

#### The structure and its order

The module `Mathlib.Data.Finset.Defs` defines the structure `Finset` with the two fields `Finset.val`, a multiset, and `Finset.nodup`, a proof that the multiset has no repetition. The constructor is `Finset.mk`, and the lemmas `Finset.mem_def` and `Finset.mem_mk` say that membership is membership in the multiset. The map `Finset.val` is injective: `Finset.val_inj` states $s.\mathrm{val} = t.\mathrm{val} \iff s = t$.

**Theorem (Extensionality).** If $a \in s \iff a \in t$ for each $a$, then $s = t$. This is `Finset.ext`, and `Finset.ext_iff` is the form with an iff.

*Proof sketch.* A multiset with no repetition gives each element the count $0$ or $1$, and the count $1$ exactly to its members. So $s.\mathrm{val}$ and $t.\mathrm{val}$ have the same count function, and they are equal. Then `Finset.val_inj` gives $s = t$. $\square$

The instance `Finset.instSetLike` makes `Finset α` a set-like type. So a finset coerces to `Set α`, and the coercion is injective (`Finset.coe_injective`, `Finset.coe_inj`). The lemma `Finset.mem_coe` turns `a ∈ (s : Set α)` into `a ∈ s`. The order on finsets is inclusion: the instance `Finset.instPartialOrder` has `≤` equal to `⊆`, and `Finset.le_iff_subset` records this. The rule `Finset.subset_iff` unfolds `s ⊆ t` to `∀ x, x ∈ s → x ∈ t`, and `Finset.val_le_iff` says that inclusion of finsets is the order of multisets. The coercion is an order embedding, `Finset.coeEmb`, and `Finset.coe_subset` moves an inclusion across it. The strict inclusion is well founded (`Finset.isWellFounded_ssubset`, `Finset.wellFoundedLT`), so a proof can use strong induction on $\subset$.

The module also gives the decidability instances. Membership `a ∈ s` is decidable when `α` has decidable equality (`Finset.decidableMem`), and so is the equality of two finsets (`Finset.decidableEq`). A bounded quantifier `∀ a ∈ s, p a` is decidable when `p` is (`Finset.decidableDforallFinset`). These instances let `decide` check a statement about a small explicit finset. The instance `Multiset.canLiftFinset` lets the tactic `lift` turn a multiset with no repetition into a finset.

#### The empty finset and nonempty finsets

The module `Mathlib.Data.Finset.Empty` gives `Finset.empty`, written `∅`, with `Finset.empty_val` (its multiset is $0$) and `Finset.notMem_empty`. The empty finset is the bottom of the order: `Finset.bot_eq_empty` and `Finset.empty_subset`. The predicate `Finset.Nonempty s` is `∃ x, x ∈ s`, by `Finset.nonempty_def`. It is the positive form of $s \ne \emptyset$, and `Finset.nonempty_iff_ne_empty` connects the two. Mathlib prefers `s.Nonempty` in hypotheses, because it gives a witness at once with `Finset.Nonempty.exists_mem`. The lemma `Finset.Nonempty.mono` says that a superset of a nonempty finset is nonempty, and `Finset.coe_nonempty` moves the predicate to sets.

The module `Mathlib.Data.Finset.Attr` has no declaration. It declares the Aesop rule set `finsetNonempty`. The function `Mathlib.Meta.proveFinsetNonempty` of `Mathlib.Data.Finset.Empty` runs these rules, and the extension of the tactic `positivity` for finsets uses it, for example to prove that the card of a finset is positive.

#### Singletons, insert and cons

The module `Mathlib.Data.Finset.Insert` adds one element to a finset. There are two forms. The function `insert a s` needs `DecidableEq α`, because it tests whether $a$ is already in $s$. Its multiset is `Multiset.ndinsert a s.val` (`Finset.insert_def`). The function `Finset.cons a s h` takes a proof `h : a ∉ s` instead, so it needs no equality test, and its multiset is `a ::ₘ s.val` (`Finset.cons_val`). The two agree: `Finset.cons_eq_insert`. The notation `{a, b, c}` is `insert a (insert b {c})`.

**Theorem (Membership in an insert).** $b \in \operatorname{insert} a\, s \iff b = a \lor b \in s$. This is `Finset.mem_insert`, and `Finset.mem_cons` is the same rule for `cons`.

*Proof sketch.* The multiset of `insert a s` is $s.\mathrm{val}$ if $a \in s$, and $a ::ₘ s.\mathrm{val}$ if not. In the first case, $b = a$ implies $b \in s$, so both sides say $b \in s$. In the second case, membership in $a ::ₘ m$ is $b = a \lor b \in m$. $\square$

The rest of the API follows this lemma. The table gives the main rules.

| Lean name | Statement |
|---|---|
| `Finset.mem_singleton` | $b \in \{a\} \iff b = a$ |
| `Finset.singleton_inj` | $\{a\} = \{b\} \iff a = b$ |
| `Finset.insert_eq_of_mem` | $a \in s \to \operatorname{insert} a\, s = s$ |
| `Finset.insert_comm` | $\operatorname{insert} a (\operatorname{insert} b\, s) = \operatorname{insert} b (\operatorname{insert} a\, s)$ |
| `Finset.insert_idem` | $\operatorname{insert} a (\operatorname{insert} a\, s) = \operatorname{insert} a\, s$ |
| `Finset.pair_comm` | $\{a, b\} = \{b, a\}$ |
| `Finset.insert_subset_iff` | $\operatorname{insert} a\, s \subseteq t \iff a \in t \land s \subseteq t$ |
| `Finset.ssubset_insert` | $a \notin s \to s \subset \operatorname{insert} a\, s$ |
| `Finset.coe_insert` | the coercion of `insert a s` is `insert a ↑s` |

The predicate `Finset.Nontrivial s` says that $s$ has two distinct elements. A nonempty finset is a singleton or nontrivial (`Finset.Nonempty.exists_eq_singleton_or_nontrivial`), and `Finset.nontrivial_iff_ne_singleton` gives the test $s \ne \{a\}$ for an $a \in s$. The equivalence `Finset.subtypeInsertEquivOption` identifies the subtype of `insert x t` with `Option` of the subtype of `t` when $x \notin t$. The maps `Finset.insertPiProd` and `Finset.consPiProdEquiv` split a dependent function on `insert a s` into its value at $a$ and its restriction to $s$.

#### Induction on finsets

Each finset is built from $\emptyset$ by insertions of new elements. The module states this as several principles of induction.

**Theorem (Induction by cons).** Let $P$ be a property of finsets. If $P(\emptyset)$ holds, and $P(s)$ implies $P(\operatorname{cons} a\, s\, h)$ for each $a \notin s$, then $P(s)$ holds for each finset $s$. This is `Finset.cons_induction`.

*Proof sketch.* Use induction on the multiset $s.\mathrm{val}$, by the induction principle of multisets of Chapter 2. A multiset $a ::ₘ m$ with no repetition has $a \notin m$, and $m$ has no repetition. So each step of the induction on multisets is a step $s \mapsto \operatorname{cons} a\, s\, h$. $\square$

With `DecidableEq α`, `Finset.induction_on` is the same principle with `insert`, and Section 1 used it for the card. The form `Finset.induction_on'` keeps the hypotheses $a \in S$ and $s \subseteq S$ for a fixed finset $S$, which helps when the step needs a property of the elements of $S$. For nonempty finsets the base case is a singleton.

**Theorem (Induction on nonempty finsets).** If $P(\{a\})$ holds for each $a$, and $P(s)$ implies $P(\operatorname{cons} a\, s\, h)$ for each nonempty $s$ and each $a \notin s$, then $P(s)$ holds for each nonempty finset $s$. This is `Finset.Nonempty.cons_induction`.

*Proof sketch.* Apply `Finset.cons_induction` to the property "if $s$ is nonempty, then $P(s)$". The case $\emptyset$ is empty. In the step from $s$ to $\operatorname{cons} a\, s\, h$, either $s = \emptyset$, and then the new finset is $\{a\}$, or $s$ is nonempty, and the hypothesis applies. $\square$

The principle for nonempty finsets is the right tool for the maximum and the minimum of a finset, which have no value on $\emptyset$.

#### Erase

The module `Mathlib.Data.Finset.Erase` defines `Finset.erase s a`, the finset $s \setminus \{a\}$. It needs `DecidableEq α`, and its multiset is the erase of the multiset.

**Theorem (Membership in an erase).** $b \in \operatorname{erase} s\, a \iff b \ne a \land b \in s$. This is `Finset.mem_erase`.

*Proof sketch.* The multiset $s.\mathrm{val}$ has at most one copy of $a$. Erasing one copy of $a$ removes $a$ and keeps every other element. $\square$

The other lemmas are the expected ones: `Finset.erase_subset`, `Finset.erase_eq_of_notMem` (erasing a non member does nothing), `Finset.erase_ne_self` (erasing changes $s$ exactly when $a \in s$), `Finset.erase_idem`, `Finset.erase_right_comm` and `Finset.erase_subset_erase`. The lemma `Finset.erase_injOn` says that $a \mapsto \operatorname{erase} s\, a$ is injective on $s$. The coercion lemma is `Finset.coe_erase`. The rules that mix insert and erase, such as `Finset.insert_erase` and `Finset.erase_insert`, are in `Mathlib.Data.Finset.Basic`, and the next section treats them.

#### Attach

The module `Mathlib.Data.Finset.Attach` defines `Finset.attach s`, a finset of the subtype `{x // x ∈ s}`. It has every element of the subtype, by `Finset.mem_attach`, and its coercion is `Set.univ` (`Finset.coe_attach`). It serves when a function needs the proof $x \in s$, for example a sum $\sum_{x \in s} f(x, h_x)$ where $f$ uses the membership proof.

#### From lists and multisets to finsets

The module `Mathlib.Data.Finset.Dedup` connects finsets with lists and multisets. The function `Multiset.toFinset` removes the repeated entries of a multiset, with `Multiset.toFinset_val` equal to the dedup and `Multiset.mem_toFinset` for membership. The function `List.toFinset` does the same for a list, with `List.mem_toFinset`. Two lists give the same finset exactly when their dedups are permutations of each other (`List.toFinset_eq_iff_perm_dedup`).

In the other direction, `Finset.toList s` is a list of the elements of $s$ with no repetition (`Finset.nodup_toList`, `Finset.mem_toList`). It is noncomputable, because a finset has no preferred order of its elements. For a type with a linear order, `Finset.sort` gives a computable sorted list.

**Theorem (Round trip).** $(\operatorname{toList} s).\operatorname{toFinset} = s$. This is `Finset.toList_toFinset`.

*Proof sketch.* Both sides have the same members, by `List.mem_toFinset` and `Finset.mem_toList`. Extensionality ends the proof. $\square$

The converse round trip is false. The list `[1, 2]` gives the finset $\{1, 2\}$, but `Finset.toList` can return `[2, 1]`. The true statement is `Finset.perm_toList`: two finsets are equal if and only if their lists are permutations of each other.

#### The lattice of finsets

The module `Mathlib.Data.Finset.Lattice.Basic` defines the union $s \cup t$ and the intersection $s \cap t$. Both need `DecidableEq α`. Their multisets are `Multiset.ndunion` and `Multiset.ndinter` of the two multisets (`Finset.union_val_nd`, `Finset.inter_val_nd`). The membership lemmas are `Finset.mem_union` ($a \in s \cup t \iff a \in s \lor a \in t$) and `Finset.mem_inter` ($a \in s \cap t \iff a \in s \land a \in t$). The instances `Finset.instLattice` and `Finset.instDistribLattice` make `Finset α` a distributive lattice, with `⊔` equal to `∪` and `⊓` equal to `∩` (`Finset.sup_eq_union`, `Finset.inf_eq_inter`).

**Theorem (Distributivity).** $s \cap (t \cup u) = (s \cap t) \cup (s \cap u)$. This is `Finset.inter_union_distrib_left`.

*Proof sketch.* By `Finset.ext`, take an element $a$. By the membership lemmas, the claim is $p \land (q \lor r) \iff (p \land q) \lor (p \land r)$ for the three propositions $a \in s$, $a \in t$, $a \in u$. This is a law of logic. $\square$

The proof is the model for the whole module. Each identity has a name that describes its shape, as for sets: `Finset.union_comm`, `Finset.union_assoc`, `Finset.union_self`, `Finset.inter_comm`, `Finset.inter_assoc`, `Finset.inter_self`, and the four distributive laws `Finset.inter_union_distrib_left`, `Finset.inter_union_distrib_right`, `Finset.union_inter_distrib_left` and `Finset.union_inter_distrib_right`. The order rules are `Finset.subset_union_left`, `Finset.inter_subset_left`, `Finset.union_subset_iff`, `Finset.subset_inter_iff`, `Finset.union_eq_left` ($s \cup t = s \iff t \subseteq s$) and `Finset.inter_eq_left` ($s \cap t = s \iff s \subseteq t$). The coercion lemmas `Finset.coe_union` and `Finset.coe_inter` move the operations to sets. A general lattice lemma also applies to finsets through `Finset.sup_eq_union`.

#### Common errors

1. To use `insert` or `∪` in a general proof with no `DecidableEq α`. Lean then reports a missing instance. Put `classical` at the start of the proof, or use `Finset.cons` and `Finset.disjUnion`, which need a proof of disjointness instead of an equality test.
2. To prove $s \ne \emptyset$ when the next step needs an element. State the hypothesis as `s.Nonempty`, and get the element with `obtain ⟨x, hx⟩ := hs`.
3. To expect `(l.toFinset).toList = l` for a list with no repetition. The order can change, so the true statement is only a permutation, by `Finset.perm_toList` or `Finset.toList_toFinset` in the other direction.

### Exercises

1. (A) Prove $\operatorname{insert} a\, s = s \iff a \in s$ with `Finset.ext` and `Finset.mem_insert`, and find the name of this lemma in the module `Mathlib.Data.Finset.Insert`.
2. (A) Compute the finsets $\{1, 2, 3\} \cup \{3, 4\}$, $\{1, 2, 3\} \cap \{3, 4\}$ and $\operatorname{erase} \{1, 2, 3\}\, 2$, and give the card of each.
3. (A) Prove that $\operatorname{erase} (\operatorname{insert} a\, s)\, a = s$ when $a \notin s$, with the membership lemmas only.
4. (B) Prove $(s \cup t) \cap (s \cup u) = s \cup (t \cap u)$ for finsets. Then prove it a second time from `Finset.inter_union_distrib_left` and the absorption laws, with no use of elements.
5. (B) Use `Finset.Nonempty.cons_induction` to prove that each nonempty finset of $\mathbb{N}$ has an element $m$ with $x \le m$ for each $x \in s$.
6. (B) Give two lists $l_1 \ne l_2$ with no repetition and $l_1.\operatorname{toFinset} = l_2.\operatorname{toFinset}$. Explain why `Finset.toList` can not be a left inverse of `List.toFinset` on such lists.

### Reference

<?reference?>
