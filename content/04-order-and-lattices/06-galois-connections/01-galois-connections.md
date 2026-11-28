---
title: Galois connections
kind: theory
modules:
  - Mathlib.Order.GaloisConnection.Defs
  - Mathlib.Order.GaloisConnection.Basic
  - Mathlib.Order.Rel.GaloisConnection
explains:
  E3: [GaloisConnection]
  E2: [GaloisConnection.monotone_l, GaloisConnection.l_u_le, GaloisConnection.le_u_l, GaloisConnection.l_sup, GaloisConnection.monotone_intro, GaloisConnection.l_unique, GaloisConnection.isLUB_l_image, Int.gc_coe_floor]
  E1: [GaloisConnection.monotone_u, GaloisConnection.le_iff_le, GaloisConnection.u_l_u_eq_u, GaloisConnection.l_u_l_eq_l, GaloisConnection.u_inf, GaloisConnection.compose, GaloisConnection.dual, GaloisConnection.l_bot, GaloisConnection.u_top, GaloisConnection.u_unique, GaloisConnection.l_iSup, GaloisConnection.l_sSup, Set.image_subset_iff, Int.le_floor, Int.gc_ceil_coe]
families: []
requires: [V04.C02, V04.C03, V04.C04]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V04/C06/Examples.lean
  - MathlibHandbook/V04/C06/Exercises.lean
  - MathlibHandbook/V04/C06/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Galois connections

### Overview

Many pairs of maps in mathematics satisfy one and the same condition:
$$l(a) \le b \iff a \le u(b).$$
The image and the preimage of a function satisfy it, with inclusion as the order. The cast from $\mathbb{Z}$ to $\mathbb{R}$ and the floor function satisfy it. Multiplication by a positive integer $k$ and the division by $k$ with rounding down satisfy it on $\mathbb{N}$. A pair with this property is a *Galois connection*. The condition fixes each of the two maps in terms of the other, and its consequences hold in all the examples at once.

This section proves the main consequences of the condition: the lower map $l$ keeps every supremum that exists, the upper map $u$ keeps every infimum, and each of the two maps determines the other. The next section studies the composite $u \circ l$, which is a closure operator.

### Definitions

In this section $\alpha$ and $\beta$ are preorders unless the text says otherwise.

**Definition (Galois connection).** A pair of functions $l : \alpha \to \beta$ and $u : \beta \to \alpha$ is a *Galois connection* if
$$l(a) \le b \iff a \le u(b) \quad \text{for all } a \in \alpha \text{ and } b \in \beta.$$
The map $l$ is the *lower adjoint* of $u$, and $u$ is the *upper adjoint* of $l$.

A good way to read the condition: $u(b)$ is the largest element whose image under $l$ stays below $b$, and $l(a)$ is the smallest element whose image under $u$ stays above $a$. Some books call $l$ the left adjoint and $u$ the right adjoint, from category theory, where a Galois connection is an adjunction between two preorders.

Ore used an antitone form: two antitone maps $f : \alpha \to \beta$ and $g : \beta \to \alpha$ with $b \le f(a) \iff a \le g(b)$. This is a Galois connection in the sense above between $\alpha$ and the dual order $\beta^{\mathrm{op}}$. Mathlib uses only the monotone form, and it gets the antitone form from the dual order.

::: mathlib
`GaloisConnection` · `Mathlib.Order.GaloisConnection.Defs`

The definition is the plain proposition `∀ a b, l a ≤ b ↔ a ≤ u b`. It is not a structure, so `Iff.rfl` unfolds it, and a proof `gc : GaloisConnection l u` applies to two points: `(gc a b).mp h`. The form with implicit points, for `rw`, is `GaloisConnection.le_iff_le`.

<?decl GaloisConnection?>
:::

### Theorems and proofs

**Theorem (Unit and counit).** For a Galois connection, $a \le u(l(a))$ for each $a \in \alpha$, and $l(u(b)) \le b$ for each $b \in \beta$. The first inequality is the *unit* and the second is the *counit*.

*Proof.* With $b = l(a)$, the condition gives $l(a) \le l(a) \iff a \le u(l(a))$, and the left side holds by reflexivity. With $a = u(b)$, it gives $l(u(b)) \le b \iff u(b) \le u(b)$, and the right side holds. $\square$

::: mathlib
`GaloisConnection.le_u_l` · `Mathlib.Order.GaloisConnection.Defs`

The unit is `gc.le_u_l a : a ≤ u (l a)`.

<?decl GaloisConnection.le_u_l?>
:::

::: mathlib
`GaloisConnection.l_u_le` · `Mathlib.Order.GaloisConnection.Defs`

The counit is `gc.l_u_le b : l (u b) ≤ b`.

<?decl GaloisConnection.l_u_le?>
:::

**Theorem (Monotonicity).** The maps $l$ and $u$ of a Galois connection are monotone.

*Proof.* Let $a_1 \le a_2$ in $\alpha$. By the unit, $a_2 \le u(l(a_2))$, so $a_1 \le u(l(a_2))$ by transitivity. The condition, with $a = a_1$ and $b = l(a_2)$, turns this into $l(a_1) \le l(a_2)$. For $u$, let $b_1 \le b_2$ in $\beta$. By the counit, $l(u(b_1)) \le b_1 \le b_2$. The condition, with $a = u(b_1)$ and $b = b_2$, turns this into $u(b_1) \le u(b_2)$. $\square$

::: mathlib
`GaloisConnection.monotone_l` · `Mathlib.Order.GaloisConnection.Defs`

The statement is `Monotone l`, and `GaloisConnection.monotone_u` is the statement for `u`.

<?decl GaloisConnection.monotone_l?>
:::

**Theorem (An equivalent definition).** Two functions $l : \alpha \to \beta$ and $u : \beta \to \alpha$ form a Galois connection if and only if $l$ and $u$ are monotone, $a \le u(l(a))$ for each $a$, and $l(u(b)) \le b$ for each $b$.

*Proof.* If $l$ and $u$ form a Galois connection, the four properties are the two theorems above. Conversely, suppose that the four properties hold, and let $a \in \alpha$ and $b \in \beta$. If $l(a) \le b$, then $u(l(a)) \le u(b)$ because $u$ is monotone, and the unit gives $a \le u(l(a)) \le u(b)$. If $a \le u(b)$, then $l(a) \le l(u(b))$ because $l$ is monotone, and the counit gives $l(a) \le l(u(b)) \le b$. $\square$

::: mathlib
`GaloisConnection.monotone_intro` · `Mathlib.Order.GaloisConnection.Defs`

The arguments are `Monotone u`, `Monotone l`, the unit `∀ a, a ≤ u (l a)` and the counit `∀ b, l (u b) ≤ b`, in this order.

<?decl GaloisConnection.monotone_intro?>
:::

**Theorem (Triangle identities).** Let $\alpha$ and $\beta$ be partial orders. For a Galois connection, $u(l(u(b))) = u(b)$ and $l(u(l(a))) = l(a)$.

*Proof.* The unit at the point $u(b)$ gives $u(b) \le u(l(u(b)))$. The counit gives $l(u(b)) \le b$, and $u$ is monotone, so $u(l(u(b))) \le u(b)$. Antisymmetry in $\alpha$ gives the first equality. For the second, the unit $a \le u(l(a))$ and the monotonicity of $l$ give $l(a) \le l(u(l(a)))$. The counit at the point $l(a)$ gives $l(u(l(a))) \le l(a)$. Antisymmetry in $\beta$ gives the second equality. $\square$

**Theorem (Each adjoint determines the other).** Let $l : \alpha \to \beta$ and $u : \beta \to \alpha$ form a Galois connection.

1. For each $a$, $l(a)$ is the least element of the set $\{b \in \beta : a \le u(b)\}$.
2. For each $b$, $u(b)$ is the greatest element of the set $\{a \in \alpha : l(a) \le b\}$.
3. If $\beta$ is a partial order and $l'$ is another lower adjoint of $u$, then $l' = l$. If $\alpha$ is a partial order and $u'$ is another upper adjoint of $l$, then $u' = u$.

*Proof.* 1. The unit says that $a \le u(l(a))$, so $l(a)$ is in the set. If $b$ is in the set, then $a \le u(b)$, and the condition gives $l(a) \le b$. So $l(a)$ is below each element of the set.

2. The counit says that $l(u(b)) \le b$, so $u(b)$ is in the set. If $l(a) \le b$, then $a \le u(b)$ by the condition.

3. Both $l(a)$ and $l'(a)$ are least elements of the same set $\{b : a \le u(b)\}$, by part 1. So $l(a) \le l'(a)$ and $l'(a) \le l(a)$, and antisymmetry in $\beta$ gives $l(a) = l'(a)$. The proof for $u$ is the same with part 2. $\square$

So a map $l$ has an upper adjoint only if each set $\{a : l(a) \le b\}$ has a greatest element. The counterexample below uses this test.

::: mathlib
`GaloisConnection.l_unique` · `Mathlib.Order.GaloisConnection.Defs`

The statement takes two connections `gc : GaloisConnection l u` and `gc' : GaloisConnection l' u'` and a proof that `u` and `u'` agree at each point, and it gives `l b = l' b`. The dual is `GaloisConnection.u_unique`.

<?decl GaloisConnection.l_unique?>
:::

**Theorem (The lower adjoint keeps suprema).** Let $l : \alpha \to \beta$ and $u : \beta \to \alpha$ form a Galois connection, and let $s \subseteq \alpha$ have a least upper bound $m$. Then $l(m)$ is a least upper bound of $l(s) = \{l(a) : a \in s\}$. In particular, in lattices, $l(a_1 \sqcup a_2) = l(a_1) \sqcup l(a_2)$, and $l(\bot) = \bot$ when $\alpha$ and $\beta$ have least elements and $\beta$ is a partial order. Dually, $u$ keeps the greatest lower bounds, $u(b_1 \sqcap b_2) = u(b_1) \sqcap u(b_2)$, and $u(\top) = \top$.

*Proof.* For each $b \in \beta$ the following statements are equivalent:

- $b$ is an upper bound of $l(s)$, that is $l(a) \le b$ for each $a \in s$;
- $a \le u(b)$ for each $a \in s$, by the condition;
- $u(b)$ is an upper bound of $s$;
- $m \le u(b)$, because $m$ is the least upper bound of $s$;
- $l(m) \le b$, by the condition.

So the upper bounds of $l(s)$ are exactly the elements above $l(m)$. With $b = l(m)$, $l(m)$ is an upper bound of $l(s)$, and it is below every other upper bound.

For two elements, $a_1 \sqcup a_2$ is the least upper bound of $\{a_1, a_2\}$, and its image is the least upper bound of $\{l(a_1), l(a_2)\}$, which is $l(a_1) \sqcup l(a_2)$. The least upper bound of $\emptyset$ is $\bot$, and $l(\emptyset) = \emptyset$, so $l(\bot)$ and $\bot$ are both least upper bounds of $\emptyset$ in $\beta$, and they are equal by antisymmetry. The statements for $u$ are the same statements for the dual orders, since $u : \beta^{\mathrm{op}} \to \alpha^{\mathrm{op}}$ is a lower adjoint of $l$ there. $\square$

The theorem has a converse in complete lattices. If $\alpha$ and $\beta$ are complete lattices and $l$ keeps all suprema, then $l$ has an upper adjoint, namely $u(b) = \sup\{a : l(a) \le b\}$. Let $S_b = \{a : l(a) \le b\}$. If $l(a) \le b$, then $a \in S_b$, so $a \le u(b)$. Conversely, $l(u(b)) = \sup l(S_b)$ because $l$ keeps suprema, and each element of $l(S_b)$ is $\le b$, so $l(u(b)) \le b$. If $a \le u(b)$, then $l(a) \le l(u(b)) \le b$, because a map that keeps suprema of pairs is monotone. This is the order form of the adjoint functor theorem.

::: mathlib
`GaloisConnection.isLUB_l_image` · `Mathlib.Order.GaloisConnection.Basic`

The statement is `IsLUB s a → IsLUB (l '' s) (l a)`, for preorders, with no completeness. The forms for lattices and complete lattices are `GaloisConnection.l_sup`, `GaloisConnection.l_sSup` and `GaloisConnection.l_iSup`. The duals for `u` are `GaloisConnection.u_inf` and its variants, and `GaloisConnection.l_bot` and `GaloisConnection.u_top` are the empty cases.

<?decl GaloisConnection.isLUB_l_image?>
:::

::: mathlib
`GaloisConnection.l_sup` · `Mathlib.Order.GaloisConnection.Basic`

The lemma needs two join semilattices.

<?decl GaloisConnection.l_sup?>
:::

**Theorem (Composition).** If $l_1 : \alpha \to \beta$, $u_1 : \beta \to \alpha$ and $l_2 : \beta \to \gamma$, $u_2 : \gamma \to \beta$ are Galois connections, then $l_2 \circ l_1$ and $u_1 \circ u_2$ form a Galois connection.

*Proof.* For $a \in \alpha$ and $c \in \gamma$, $l_2(l_1(a)) \le c \iff l_1(a) \le u_2(c) \iff a \le u_1(u_2(c))$, by the second connection and then the first. $\square$

### Examples

**Example (Image and preimage).** Let $f : X \to Y$ be a function. For $A \subseteq X$ and $B \subseteq Y$,
$$f(A) \subseteq B \iff A \subseteq f^{-1}(B).$$
Indeed, both sides say that $f(x) \in B$ for each $x \in A$. So the image $f_*$ is the lower adjoint of the preimage $f^{-1}$ between the lattices of subsets. The theorems above give, with no further work: $f(A_1 \cup A_2) = f(A_1) \cup f(A_2)$, $f(\bigcup_i A_i) = \bigcup_i f(A_i)$ and $f(\emptyset) = \emptyset$, and dually $f^{-1}(B_1 \cap B_2) = f^{-1}(B_1) \cap f^{-1}(B_2)$ and $f^{-1}(Y) = X$.

<?lean MathlibHandbook/V04/C06/Examples.lean#image?>

**Counterexample (The lower adjoint does not keep infima).** The image keeps unions, but not intersections. Let $f : \{0, 1\} \to \{0\}$ be the constant map. Then $f(\{0\} \cap \{1\}) = f(\emptyset) = \emptyset$, while $f(\{0\}) \cap f(\{1\}) = \{0\}$.

**Example (The floor).** Let $\iota : \mathbb{Z} \to \mathbb{R}$ be the cast. For $n \in \mathbb{Z}$ and $x \in \mathbb{R}$,
$$\iota(n) \le x \iff n \le \lfloor x \rfloor.$$
Both sides say that $n$ is one of the integers below $x$. So the cast is the lower adjoint of the floor. The theorems give that the floor is monotone and keeps infima: $\lfloor \min(x, y) \rfloor = \min(\lfloor x \rfloor, \lfloor y \rfloor)$. The floor does not keep suprema of infinite sets: the set $\{1 - 1/k : k \ge 1\}$ has supremum $1$, its floors are all $0$, and $\lfloor 1 \rfloor = 1$. This does not contradict the theory, because the floor is an upper adjoint.

<?lean MathlibHandbook/V04/C06/Examples.lean#floor?>

**Example (Integer division).** Let $k \ge 1$ and let $b \div k$ be the division with rounding down on $\mathbb{N}$, so $b \div k$ is the largest $q$ with $kq \le b$. For $a, b \in \mathbb{N}$,
$$k a \le b \iff a \le b \div k.$$
If $ka \le b$, then $a \le b \div k$ by the definition of $b \div k$. If $a \le b \div k$, then $ka \le k (b \div k) \le b$. So $a \mapsto ka$ is the lower adjoint of $b \mapsto b \div k$. The theorems give $(b \div k) \div m = b \div (km)$ for $m \ge 1$, by the uniqueness of adjoints. Apply the composition theorem with $l_1(a) = ma$ and $l_2(a) = ka$: the composite $a \mapsto k(ma)$ has the upper adjoint $b \mapsto (b \div k) \div m$, and $a \mapsto (km)a$ has the upper adjoint $b \mapsto b \div (km)$. The two lower adjoints are equal, so the upper adjoints are equal. For $b = 100$, $k = 3$, $m = 7$: $100 \div 3 = 33$, $33 \div 7 = 4$, and $100 \div 21 = 4$.

**Counterexample (A monotone map with no upper adjoint).** Let $l : \mathbb{R} \to \mathbb{R}$ be $l(x) = x$ for $x < 0$ and $l(x) = x + 1$ for $x \ge 0$. It is strictly monotone. Suppose that it has an upper adjoint $u$. By part 2 of the theorem on uniqueness, the set $S = \{x : l(x) \le \tfrac12\}$ has a greatest element $u(\tfrac12)$. For $x \ge 0$, $l(x) \ge 1 > \tfrac12$, and for $x < 0$, $l(x) = x < \tfrac12$. So $S = (-\infty, 0)$, which has no greatest element. This contradiction shows that $l$ has no upper adjoint.

**Example (Polarities and Galois theory).** Let $R \subseteq X \times Y$ be a relation. For $A \subseteq X$ put $A^{\triangleright} = \{y : x R y \text{ for each } x \in A\}$, and for $B \subseteq Y$ put $B^{\triangleleft} = \{x : x R y \text{ for each } y \in B\}$. Then
$$B \subseteq A^{\triangleright} \iff x R y \text{ for all } x \in A, y \in B \iff A \subseteq B^{\triangleleft}.$$
So $A \mapsto A^{\triangleright}$ is a Galois connection from the subsets of $X$ to the dual of the subsets of $Y$, with upper adjoint $B \mapsto B^{\triangleleft}$. For $X = Y = \mathbb{R}^n$ and $x R y \iff x \cdot y = 0$, the maps are the orthogonal complements. For a field extension $L/K$, $X = L$, $Y$ the automorphisms of $L$ over $K$, and $x R \sigma \iff \sigma(x) = x$, the maps send a set of elements to the automorphisms that fix it, and a set of automorphisms to its fixed field. For a finite Galois extension, the fundamental theorem of Galois theory says that this connection is a bijection between the intermediate fields and the subgroups.

**Example (Monotonicity, unit and counit in Lean).**

<?lean MathlibHandbook/V04/C06/Examples.lean#monotone?>

<?lean MathlibHandbook/V04/C06/Examples.lean#unit?>

**Example (The definition and the supremum in Lean).** The definition unfolds by `Iff.rfl`, and `gc.l_sup` gives $l(a_1 \sqcup a_2) = l(a_1) \sqcup l(a_2)$.

<?lean MathlibHandbook/V04/C06/Examples.lean#def?>

<?lean MathlibHandbook/V04/C06/Examples.lean#sup?>

### The library around it

The lemmas that need only preorders or partial orders are in `Mathlib.Order.GaloisConnection.Defs`. They include the triangle identities `GaloisConnection.u_l_u_eq_u` and `GaloisConnection.l_u_l_eq_l`, the composition `GaloisConnection.compose`, and `GaloisConnection.dual`, which exchanges the roles of $l$ and $u$ on the dual orders. The lemmas about suprema and infima are in `Mathlib.Order.GaloisConnection.Basic`.

The examples are in the files of their objects. Image and preimage give `Set.image_subset_iff`. The floor and the ceiling are `Int.gc_coe_floor` and `Int.gc_ceil_coe`, and `Int.le_floor` is the condition with implicit points.

Each relation gives a Galois connection. In `Mathlib.Order.Rel.GaloisConnection`, a relation $R$ between $\alpha$ and $\beta$ has the maps `SetRel.leftDual` and `SetRel.rightDual`. For $J \subseteq \alpha$, the set $\operatorname{leftDual}(J)$ is $\{b \mid a \mathrel{R} b \text{ for each } a \in J\}$, and `SetRel.rightDual` is the same construction from the other side. Both maps reverse inclusion, so `SetRel.gc_leftDual_rightDual` states the connection between `Set α` and the order dual of `Set β`. The fixed points of the two closures are `SetRel.leftFixedPoints` and `SetRel.rightFixedPoints`, and `SetRel.equivFixedPoints` is the bijection between them. This is the abstract form of the correspondence between closed sets and their duals, as in formal concept analysis or the Galois correspondence of field theory.

### Exercises

1. (A) State the condition of a Galois connection for `Set.image f` and `Set.preimage f`, and deduce $f(\emptyset) = \emptyset$ from the theorems of the section.
2. (A) Compute $\lfloor \min(2.7, -1.2) \rfloor$ and $\min(\lfloor 2.7 \rfloor, \lfloor -1.2 \rfloor)$. Explain why the floor also keeps $\max$ of two numbers, although it is an upper adjoint. *Hint:* a monotone map on a linear order keeps $\max$.
3. (B) Show that $u \circ l \circ u = u$ for a Galois connection between partial orders, without the triangle identities. *Hint:* two inequalities.
4. (B) Show that the ceiling $\lceil \cdot \rceil : \mathbb{R} \to \mathbb{Z}$ is the lower adjoint of the cast from `ℤ` to `ℝ`. Deduce $\lceil \max(x, y) \rceil = \max(\lceil x \rceil, \lceil y \rceil)$.
5. (B) Let $f : X \to Y$. Prove that $A \mapsto \{y : f^{-1}(\{y\}) \subseteq A\}$ is an upper adjoint of the preimage $f^{-1}$, and deduce that the preimage keeps arbitrary unions. *Hint:* $f^{-1}(B) \subseteq A$ says that each $y \in B$ has all its preimages in $A$.
6. (B) In the polarity example, show that $A \subseteq A^{\triangleright\triangleleft}$ and that $A^{\triangleright\triangleleft\triangleright} = A^{\triangleright}$.
7. (C) Let $\alpha$ and $\beta$ be complete lattices and let $l : \alpha \to \beta$ keep all suprema. Show that $u(b) = \sup\{a : l(a) \le b\}$ is an upper adjoint of $l$, and give an example that shows that it is needed that $l$ keeps the supremum of the empty set. *Hint:* the remark after the theorem on suprema.
8. (L) Prove the counit $l(u(b)) \le b$. The solution is `l_u_le_example`.
9. (L) Prove that the upper adjoint keeps the infimum. The solution is `u_inf_example`.
10. (L) Prove that the image of a union is the union of the images. The solution is `image_union_example`.

### Notes and history

Ore introduced Galois connections in 1944, in the paper "Galois connexions" in the *Transactions of the American Mathematical Society*. He used the antitone form and named it after the correspondence of Galois theory. Birkhoff had studied polarities of a relation in the first edition of *Lattice Theory* (1940). Kan introduced adjoint functors in 1958, and the monotone form is the case of preorders.

In Mathlib, the file on Galois connections came from Lean 3, where Johannes Hölzl wrote the first version in 2017.

### Reference

<?reference?>
