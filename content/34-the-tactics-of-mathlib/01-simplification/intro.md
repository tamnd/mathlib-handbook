# Simplification

This chapter is about the tactics that rewrite a goal with equations: `simp`, `norm_num`, `push_cast`, `norm_cast`, `rw`, `nth_rw` and `conv`. Most proofs in Mathlib use one of them in some step. They all rest on one principle, the substitution of equals: if $a = b$, then a statement about $a$ is equivalent to the same statement about $b$.

The three sections differ in who chooses the equations. In the first section, `simp` chooses them from a large set of lemmas with the attribute `@[simp]`, and it rewrites until no lemma applies. In the second section, `norm_num` adds procedures that evaluate numerals, and the cast tactics use the lemmas that move the maps $\mathbb{N} \to \mathbb{Z} \to \mathbb{Q} \to \mathbb{R}$. In the third section, `rw` uses only the equations of the user, once each, in the order of the list.

The chapter needs only Volume 0: the reader must know how to read a goal state and how a hypothesis is named. The tactics of this chapter come back in each later chapter. A proof with `ring` or `linarith` often starts with a `rw` or a `push_cast` that puts the goal into the form that the tactic needs. The proofs by induction of Chapter 5 use `rw [Finset.sum_range_succ]` in almost each step.
