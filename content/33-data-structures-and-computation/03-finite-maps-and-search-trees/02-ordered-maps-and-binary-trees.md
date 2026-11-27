---
title: Ordered maps and binary trees
kind: theory
modules:
  - Mathlib.Data.Tree.Basic
  - Mathlib.Data.Tree.Get
  - Mathlib.Data.Tree.Traversable
  - Mathlib.Data.Ordmap.Ordnode
  - Mathlib.Data.Ordmap.Invariants
  - Mathlib.Data.Ordmap.Ordset
explains:
  E3: [BinaryTree, BinaryTree.numLeaves_eq_numNodes_succ, BinaryTree.height_le_numNodes, BinaryTree.get, BinaryTree.indexOf, Ordnode, Ordnode.insert, Ordnode.balanceR, Ordnode.Sized, Ordnode.BalancedSz, Ordnode.Balanced, Ordnode.Bounded, Ordnode.toList_node, Ordnode.rotateL, Ordnode.node3L, Ordnode.Valid', Ordnode.Valid'.rotateL, Ordnode.insert.valid, Ordset]
  E2: [BinaryTree.numNodes, BinaryTree.numLeaves, BinaryTree.height, BinaryTree.instLawfulTraversable, Ordnode.size, Ordnode.node', Ordnode.delta, Ordnode.ratio, Ordnode.toBinaryTree, Ordnode.toList, Ordnode.balanceL, Ordnode.erase, Ordnode.node4L, Ordnode.balance', Ordnode.Raised, Ordnode.Valid, Ordnode.Valid'.rotateL_lemma₁, Ordnode.Valid'.rotateL_lemma₂, Ordnode.Valid'.rotateL_lemma₃, Ordnode.Valid'.balanceL, Ordnode.Valid'.balanceR, Ordnode.insertWith.valid_aux, Ordnode.erase.valid, Ordset.insert]
  E1: auto
families: []
requires: [V03.C02, V04.C01, V33.C01, V33.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Ordered maps and binary trees

### Overview

A lookup in an association list may test every entry. A binary search tree for ordered keys does better: smaller keys go to the left, larger keys go to the right, and a search follows one path from the root. The length of that path is at most the height of the tree. A tree with all keys on one side has a height equal to its size, so a search tree must stay balanced.

This section starts with plain binary trees, `BinaryTree α`, and then studies `Ordnode α`, the size balanced trees of Adams. Each node stores its size. A valid tree has correct sizes, children whose sizes are within a factor of three, and keys in order. The section proves that a valid tree has a sorted in-order list and a logarithmic height, and that rotation and insertion keep validity.

### Definitions

**Definition (Binary tree).** The inductive type `BinaryTree α` has two constructors: `nil`, the empty tree, and `node a l r` with a value `a` and two subtrees. The counts are defined by recursion: `numNodes` is $0$ on `nil` and $n_l + n_r + 1$ on a node, `numLeaves` is $1$ on `nil` and the sum of the two counts on a node, and `height` is $0$ on `nil` and $\max(h_l, h_r) + 1$ on a node. The older name Tree is a deprecated alias.

**Definition (Address of a node).** A positive binary numeral (`PosNum`) is `one`, `bit0 n` or `bit1 n`. The function `BinaryTree.get n t` reads the address $n$ from its lowest bit: `one` returns the value at the root, `bit0 n` goes to the left child and continues with $n$, and `bit1 n` goes to the right child and continues with $n$. The function `indexOf lt x t` computes the address of $x$ in a search tree, one comparison per step.

**Definition (Ordnode).** The type `Ordnode α` has the constructors `nil` and `node s l x r`, where $s : \mathbb{N}$ is the stored size. The function `size` reads the stored value, with `size nil = 0`, and the smart constructor `node' l x r` computes the size $\operatorname{size} l + \operatorname{size} r + 1$. The in-order list `toList` satisfies $\operatorname{toList}(\operatorname{node} s\, l\, x\, r) = \operatorname{toList} l \mathbin{+\!\!+} x :: \operatorname{toList} r$ (`Ordnode.toList_node`). The map `toBinaryTree` forgets the sizes; it defines the height of an `Ordnode`.

**Definition (Invariants).** Let $\delta = 3$ (`Ordnode.delta`) and $\rho = 2$ (`Ordnode.ratio`).

1. `Sized t`: at every node, the stored size equals $\operatorname{size} l + \operatorname{size} r + 1$.
2. `BalancedSz a b` holds if $a + b \leq 1$, or if $a \leq 3b$ and $b \leq 3a$. `Balanced t` asks this for the sizes of the children at every node.
3. `Bounded t lo hi`, with $lo$ in `WithBot α` and $hi$ in `WithTop α`, holds on `nil` if $lo < hi$ (true when a bound is infinite), and on `node s l x r` if `Bounded l lo x` and `Bounded r x hi`.

A tree is `Valid' lo t hi` if it is bounded by $lo$ and $hi$, sized and balanced, and `Valid t` is `Valid' ⊥ t ⊤`.

**Definition (Rotation).** The single left rotation is `node3L l x m y r = node' (node' l x m) y r`. The function `rotateL l x (node _ m y r)` chooses the single rotation if $\operatorname{size} m < 2\operatorname{size} r$ and the double rotation `node4L` otherwise. The function `balance' l x r` returns `node' l x r` if the sizes are small or within the factor $3$, and calls `rotateL` if $\operatorname{size} r > 3\operatorname{size} l$, and the mirror `rotateR` in the mirror case. The faster `balanceL` and `balanceR` compute the same tree when only one side changed by one (`Ordnode.balance_eq_balance'`).

**Definition (Insertion).** `Ordnode.insert x t` is `ι x` on `nil`. On `node s l y r` it compares $x$ with $y$: if $x < y$ it returns `balanceL (insert x l) y r`, if $x$ and $y$ are equivalent it replaces $y$ by $x$, and if $x > y$ it returns `balanceR l y (insert x r)`. Erasure is similar and joins the two children with `glue` at the node it removes.

**Definition (Ordset).** For a preorder $\alpha$, `Ordset α` is the subtype `{t : Ordnode α // t.Valid}`. The functions `Ordset.insert`, `Ordset.erase` and `Ordset.find` apply the tree functions and the proofs of validity.

### Theorems and proofs

**Theorem (Counts of a binary tree).** For every binary tree $t$, $\operatorname{numLeaves} t = \operatorname{numNodes} t + 1$ and $\operatorname{height} t \leq \operatorname{numNodes} t$.

*Proof.* Induction on $t$. For `nil`: $1 = 0 + 1$ and $0 \leq 0$. For `node a l r`, the hypotheses of induction give $(n_l + 1) + (n_r + 1) = (n_l + n_r + 1) + 1$, and $\max(h_l, h_r) + 1 \leq \max(n_l, n_r) + 1 \leq n_l + n_r + 1$. $\square$

**Theorem (A bounded tree has a sorted in-order list).** Let $\alpha$ be a preorder. If `Bounded t lo hi`, then every element $y$ of $\operatorname{toList} t$ satisfies $lo < y < hi$, and $\operatorname{toList} t$ is strictly increasing. The index of this edition has no declaration for the second statement; the proof follows.

*Proof.* First, `Bounded t lo hi` implies $lo < hi$, by induction on $t$. For `nil` this is the definition, since an infinite bound makes the comparison true. For a node with key $x$, the hypotheses of induction give $lo < x$ and $x < hi$, and transitivity gives $lo < hi$. Second, induction on $t$ for the main claim. For `nil` the list is empty. For `node s l x r`, the list is $\operatorname{toList} l \mathbin{+\!\!+} x :: \operatorname{toList} r$. By the hypothesis of induction for `Bounded l lo x`, each element of $\operatorname{toList} l$ lies strictly between $lo$ and $x$, and the list is strictly increasing. By the hypothesis of induction for `Bounded r x hi`, each element of $\operatorname{toList} r$ lies strictly between $x$ and $hi$, and the list is strictly increasing. The first step gives $lo < x < hi$. So every element of the whole list lies between $lo$ and $hi$. For the order, take two positions $i < j$ in the list. If both are in $\operatorname{toList} l$ or both in $\operatorname{toList} r$, the hypothesis of induction applies. Otherwise the earlier element is in $\operatorname{toList} l$ or equals $x$, the later one equals $x$ or is in $\operatorname{toList} r$, and the chain $y < x < z$ gives $y < z$. $\square$

**Theorem (Height of a valid tree).** If $t$ is sized and balanced with $n = \operatorname{size} t \geq 1$, then $h = \operatorname{height}(\operatorname{toBinaryTree} t)$ satisfies $(4/3)^{h-1} \leq n$. So $h \leq 1 + \log_{4/3} n \leq 1 + 2.41\log_2 n$. The index of this edition has no declaration for this bound; the proof follows.

*Proof.* Strong induction on $n$. Let $t = \operatorname{node} s\, l\, x\, r$ with $a = \operatorname{size} l$ and $b = \operatorname{size} r$, so $n = a + b + 1$ by `Sized`. Let $c$ be a child of maximal height, of size $m$, so $h = \operatorname{height} c + 1$. If $m = 0$, then $c$ is `nil`, $h = 1$ and $(4/3)^0 = 1 \leq n$. If $a + b \leq 1$, then $m = 1$, the child is a single node of height $1$, so $h = 2$ and $(4/3)^1 \leq 2 = n$. Otherwise $a \leq 3b$ and $b \leq 3a$. From $b \leq 3a$ follows $4b \leq 3(a + b) = 3(n - 1)$, and in the same way $4a \leq 3(n - 1)$. So $m \leq \frac{3}{4}(n - 1) < \frac{3}{4}n$. The child is sized and balanced with $1 \leq m < n$, so the hypothesis of induction gives $(4/3)^{h - 2} \leq m < \frac{3}{4}n$. Multiply by $4/3$: $(4/3)^{h-1} < n$. The last claim uses $\log_2(4/3) > 0.415$. $\square$

**Lemma (A rotation keeps the in-order list).** For all trees, $\operatorname{toList}(\operatorname{node3L} l\, x\, m\, y\, r) = \operatorname{toList}(\operatorname{node'} l\, x\, (\operatorname{node'} m\, y\, r))$.

*Proof.* By `toList_node` twice on each side, the left side is $(L \mathbin{+\!\!+} x :: M) \mathbin{+\!\!+} y :: R$ and the right side is $L \mathbin{+\!\!+} x :: (M \mathbin{+\!\!+} y :: R)$, with $L, M, R$ the lists of $l, m, r$. Append is associative, and $(x :: M) \mathbin{+\!\!+} K = x :: (M \mathbin{+\!\!+} K)$. $\square$

**Theorem (A single rotation restores balance).** Let $l$, $m$, $r$ be balanced trees with sizes $a$, $b$, $c$, and let $m$ and $r$ be the children of a balanced node, with $b + c \geq 2$. Assume that the node $\operatorname{node'} l\, x\, (\operatorname{node'} m\, y\, r)$ is right heavy, $3a < b + c + 1$, that it came from a balanced state by one step, $2(b + c + 1) \leq 9a + 5$, and that the single rotation is chosen, $b < 2c$. Then $\operatorname{node3L} l\, x\, m\, y\, r$ is balanced.

*Proof.* The hypotheses give $3a \leq b + c$, $2(b + c) \leq 9a + 3$ and $b < 2c$, and the balance of the old right child gives $b \leq 3c$ and $c \leq 3b$. The new inner node has children of sizes $a$ and $b$, and the new root has children of sizes $a + b + 1$ and $c$. Four inequalities remain.

1. $a \leq 3b$: from $3a \leq b + c \leq b + 3b = 4b$ follows $a \leq \frac{4}{3}b \leq 3b$. This is `Valid'.rotateL_lemma₁`.
2. $b \leq 3a$: from $b < 2c$ follows $3b < 2b + 2c \leq 9a + 3$, so $b < 3a + 1$. This is `Valid'.rotateL_lemma₂`.
3. $a + b + 1 \leq 3c$: from $3a \leq b + c$ follows $3(a + b) \leq 4b + c < 8c + c = 9c$, so $a + b < 3c$. This is `Valid'.rotateL_lemma₃`.
4. $c \leq 3(a + b + 1)$: from $c \leq 3b$.

The subtrees $l$, $m$, $r$ do not change, so they stay balanced. $\square$

The hypothesis $2\operatorname{size} r \leq 9a + 5$ is the third hypothesis of `Valid'.rotateL`. It holds after an insertion: before the step $\operatorname{size} r - 1 \leq 3a$, so $2\operatorname{size} r \leq 6a + 2$. It holds after an erasure on the left with $a \geq 1$: before the step $\operatorname{size} r \leq 3(a + 1)$, so $2\operatorname{size} r \leq 6a + 6 \leq 9a + 5$. For $a = 0$, Mathlib uses the alternative $\operatorname{size} r \leq 3$. The file checks the double rotation and the cases with $b + c \leq 1$ with `node4L_lemma₁` to `node4L_lemma₅`.

**Theorem (Insertion keeps validity).** If $\alpha$ is a total preorder and $t$ is valid, then `Ordnode.insert x t` is valid.

*Proof.* Show a stronger claim by induction on $t$: if `Valid' lo t hi` and $lo < x < hi$, then $t' = \operatorname{insert} x\, t$ is `Valid' lo t' hi`, and $\operatorname{size} t'$ equals $\operatorname{size} t$ or $\operatorname{size} t + 1$ (`Raised`). For `nil`, $t' = \iota x$ has size $1$, is balanced, and is bounded by the hypothesis on $x$. For $t = \operatorname{node} s\, l\, y\, r$ with $x < y$: the left child is `Valid' lo l y` and $lo < x < y$, so the hypothesis of induction gives a valid $l'$ whose size is raised from $\operatorname{size} l$. The old sizes of $l$ and $r$ satisfy `BalancedSz`, and the left side moved by at most one. This is the hypothesis of `Valid'.balanceL`, whose proof is the rotation arithmetic above, so `balanceL l' y r` is valid, and its size is $\operatorname{size} l' + \operatorname{size} r + 1$, raised from $s$. The case $x > y$ is the mirror with `Valid'.balanceR`. This claim is `Ordnode.insertWith.valid_aux`. If $x$ and $y$ are equivalent, the tree keeps its shape and size, and the comparisons of $x$ with the bounds are the comparisons of $y$, since the preorder is transitive. For $t$ valid, apply the claim with $lo = \bot$ and $hi = \top$. $\square$

### Examples

**Example (Insert 1 to 5).** Insert $1, 2, 3, 4, 5$ in this order into the empty `Ordnode ℕ`, and follow the code of `balanceR`.

1. Insert $1$: the tree is $\iota 1$.
2. Insert $2$: $2 > 1$, so `balanceR nil 1 (ι 2)`. The left side is empty and the right child has no children, so the result is `node 2 nil 1 (ι 2)`: the key $1$ with the right child $2$.
3. Insert $3$: the insertion into the right child gives `node 2 nil 2 (ι 3)`. Then `balanceR nil 1 (node 2 nil 2 (ι 3))` sees an empty left side and a right child with only a right child, and returns `node 3 (ι 1) 2 (ι 3)`. The root is now $2$.
4. Insert $4$: the right child becomes `node 2 nil 3 (ι 4)` of size $2$. At the root, $2 > 3 \cdot 1$ is false, so no rotation: the root $2$ has children of sizes $1$ and $2$.
5. Insert $5$: in the right child, `balanceR nil 3 (node 2 nil 4 (ι 5))` rotates to `node 3 (ι 3) 4 (ι 5)`. At the root, $3 > 3 \cdot 1$ is false, so the tree is the root $2$ with the left child $1$ and the right child $4$, and $4$ has the children $3$ and $5$.

The in-order list is $[1, 2, 3, 4, 5]$, the height is $3$, and the root has children of sizes $1$ and $3$, with $1 \leq 9$ and $3 \leq 3$. One more insertion of $6$ makes the right child of size $4 > 3 \cdot 1$, and `balanceR` with $\operatorname{size}(\iota 3) = 1 < 2 \cdot 2$ does a single rotation: the new root is $4$, with the left child $2$ (children $1$ and $3$) and the right child $5$ (right child $6$).

**Example (Addresses).** Take the tree of the last example before the insertion of $6$, as a `BinaryTree ℕ`. It has $5$ nodes and $6$ leaves. The address `one` (the number $1$) gives $2$. The address `bit0 one` (binary $10$) goes left and gives $1$. The address `bit1 one` (binary $11$) gives $4$. The key $3$ lies right then left, so its address is `bit1 (bit0 one)`, binary $101$, the number $5$; the key $5$ has the address binary $111$. Check with `indexOf (· < ·) 3`: $3 > 2$ adds `bit1`, $3 < 4$ adds `bit0`, and $3 = 3$ gives `one`.

### The library around it

::: mathlib
`BinaryTree` · `Mathlib.Data.Tree.Basic`

Binary trees with values at the nodes. The file has `numNodes`, `numLeaves`, `height`, `numLeaves_eq_numNodes_succ`, `height_le_numNodes`, `map`, and the notation `a △ b` for a tree of `BinaryTree Unit`. 

<?decl BinaryTree?>
:::

::: mathlib
`BinaryTree.instLawfulTraversable` · `Mathlib.Data.Tree.Traversable`

Binary trees form a lawful traversable functor, with the laws `id_traverse` (from `traverse_pure`), `comp_traverse` and `naturality`. Chapter 6 of this volume studies the class.

<?decl BinaryTree.instLawfulTraversable?>
:::

::: mathlib
`Ordnode.Valid'.rotateL` · `Mathlib.Data.Ordmap.Ordset`

The main lemma of the balance proof; its hypotheses are `¬size l + size r ≤ 1`, `delta * size l < size r` and `2 * size r ≤ 9 * size l + 5 ∨ size r ≤ 3`.

<?decl Ordnode.Valid'.rotateL?>
:::

::: mathlib
`Ordset` · `Mathlib.Data.Ordmap.Ordset`

The subtype of valid trees, with `Ordset.insert`, `Ordset.erase`, `Ordset.mem`, `Ordset.find` and `Ordset.map`. Insertion needs `Std.Total (· ≤ ·)` and decidable `≤`.

<?decl Ordset?>
:::

Common errors of a learner: The first error is to use the old names with the prefix Tree; they are deprecated, and the current names start with `BinaryTree`. The second error is to read `BinaryTree.get` with the highest bit first; the path starts at the lowest bit. The third error is to trust the stored size of an `Ordnode` without `Sized`; a term such as `node 7 nil x nil` is a legal value, and the lemmas need the invariant. The fourth error is to assume a linear order; `Ordnode` works over a preorder, where two keys may be equivalent without being equal, and insertion replaces an equivalent key.

### Exercises

1. (A) Draw the `BinaryTree` with $7$ nodes and height $3$, and check the two count formulas on it. Hint: it has $8$ leaves.
2. (A) Insert $5, 4, 3, 2, 1$ in this order into the empty `Ordnode ℕ`, and compare the result with the example. Hint: the mirror function `balanceL` acts; the result is the mirror image.
3. (A) Give the addresses of all keys of the tree after the insertion of $6$ in the example. Hint: the root $4$ has the address $1$.
4. (B) Prove that `get (indexOf (· < ·) x t) t = some x` when $x$ is a key of a search tree $t$ over a linear order. Hint: induction on $t$, following the comparisons.
5. (B) Prove that a perfect binary tree of height $h$ has $2^h - 1$ nodes, and show that every binary tree satisfies $\operatorname{numNodes} t \leq 2^{\operatorname{height} t} - 1$. Hint: induction with $\max$.
6. (B) Check the four inequalities of the single rotation on the sizes $a = 1$, $b = 1$, $c = 3$, and show that the hypothesis $b < 2c$ fails for $a = 1$, $b = 3$, $c = 1$. Hint: in the second case the double rotation applies.
7. (C) For $h = 1, 2, 3, 4$, find a sized and balanced tree of height $h$ with the fewest nodes, prove that no smaller tree exists, and compare the sizes with the bound $(4/3)^{h-1}$. Hint: the sizes are $1$, $2$, $4$ and $7$; a child of height $h - 1$ forces a lower bound on the size of the other child.

### Notes and history

Binary search trees with a balance condition start with the AVL trees of Adelson-Velsky and Landis, 1962, which bound the difference of the heights of the two children. Nievergelt and Reingold introduced trees of bounded balance in 1973, with a condition on the sizes instead of the heights; the header of `Mathlib.Data.Ordmap.Ordnode` cites their work. Adams described size balanced trees for functional languages in 1993, and the header says that the code is ported from the Haskell library `Data.Set`. Knuth treats search trees in Volume 3 of The Art of Computer Programming.

The Mathlib files are by these authors, read from their headers: `Mathlib.Data.Tree.Basic` and `Mathlib.Data.Tree.Get` by Mario Carneiro and Wojciech Nawrocki, `Mathlib.Data.Tree.Traversable` by Edward van de Meent, and `Mathlib.Data.Ordmap.Ordnode`, `Mathlib.Data.Ordmap.Invariants` and `Mathlib.Data.Ordmap.Ordset` by Mario Carneiro.

### Reference

<?reference?>
