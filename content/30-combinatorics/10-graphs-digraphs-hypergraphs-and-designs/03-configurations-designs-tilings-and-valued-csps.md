---
title: Configurations, designs, tilings and valued constraint problems
kind: api
modules:
  - Mathlib.Combinatorics.Configuration
  - Mathlib.Combinatorics.Design.Defs
  - Mathlib.Combinatorics.Tiling.Tile
  - Mathlib.Combinatorics.Optimization.ValuedCSP
explains:
  E2: [Configuration.sum_lineCount_eq_sum_pointCount, Configuration.HasLines.pointCount_le_lineCount, Configuration.HasLines.card_le, Configuration.ProjectivePlane.card_points, IncidenceSystem.toHypergraph_ofHypergraph, IncidenceSystem.IsUniform.nonempty_block, DiscreteTiling.PlacedTile.coe_smul, DiscreteTiling.PlacedTile.mem_smul_iff_smul_inv_mem, ValuedCSP.Instance.IsOptimumSolution, Function.HasMaxCutProperty.forbids_commutativeFractionalPolymorphism]
  E1: auto
families: []
requires: [V30.C04, V30.C07, V03.C04, V03.C06, V05.C04, V05.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Configurations, designs, tilings and valued constraint problems

### Overview

This section collects four small modules. Each one gives a combinatorial structure on sets: incidences between points and lines, blocks of an incidence system, copies of tiles under a group action, and sums of cost functions on tuples.

The first module has the most theory. It counts points and lines in a finite configuration and proves that a finite projective plane of order $n$ has $n^2 + n + 1$ points. The other three modules give mainly definitions with a short API, and one theorem on valued constraint problems.

### The library around it

#### Configurations of points and lines

In `Mathlib.Combinatorics.Configuration`, the points are a type `P`, the lines are a type `L`, and an instance `Membership P L` says which points are on which lines. The class `Configuration.Nondegenerate` asks for three conditions. Each line misses some point, each point misses some line, and two distinct points are together on at most one line. The last condition, in the field `eq_or_eq`, also says that two distinct lines meet in at most one point.

| Lean name | Extra condition |
|---|---|
| `Configuration.HasPoints` | two distinct lines meet in a point `mkPoint` |
| `Configuration.HasLines` | two distinct points lie on a line `mkLine` |
| `Configuration.ProjectivePlane` | both, and three points and three lines in the position of the field `exists_config` |

The uniqueness forms are `Configuration.HasPoints.existsUnique_point` and `Configuration.HasLines.existsUnique_line`. The type synonym `Configuration.Dual P` exchanges the roles of points and lines. The instances `Configuration.Dual.hasLines` and `Configuration.Dual.hasPoints` exchange the two classes, so each theorem about `HasLines` gives a theorem about `HasPoints`.

For a point $p$, the number $r(p)$ = `Configuration.lineCount L p` is the number of lines through $p$. For a line $l$, the number $k(l)$ = `Configuration.pointCount P l` is the number of points on $l$. Both are `Nat.card` of a subtype, so they are $0$ for an infinite set.

**Theorem.** In a finite configuration, $\sum_p r(p) = \sum_l k(l)$.

*Proof.* Both sides count the incident pairs $(p, l)$ with $p \in l$. The left side groups them by the point and the right side by the line. $\square$

This is `Configuration.sum_lineCount_eq_sum_pointCount`, the double counting principle of Chapter 8.

**Theorem.** Let `HasLines P L` hold, let $p \notin l$, and let $p$ be on finitely many lines. Then $k(l) \le r(p)$.

*Proof.* Each point $q$ of $l$ differs from $p$, so the line $pq$ exists. Let $q \ne q'$ be points of $l$ with $pq = pq'$. Then the lines $l$ and $pq$ both contain $q$ and $q'$, so they are equal. This is false, because $p \notin l$. So $q \mapsto pq$ is an injection from the points of $l$ to the lines through $p$. $\square$

This is `Configuration.HasLines.pointCount_le_lineCount`, and `Configuration.HasPoints.lineCount_le_pointCount` is the dual.

**Theorem.** Let `HasLines P L` hold with `P` and `L` finite. Then $|P| \le |L|$.

*Proof.* Assume $|L| < |P|$. By the theorem of Hall from Chapter 4, `Configuration.Nondegenerate.exists_injective_of_card_le` gives an injective $f : L \to P$ with $f(l) \notin l$ for each $l$. By the two theorems above,
$$\sum_p r(p) = \sum_l k(l) \le \sum_l r(f(l)).$$
The right side is a sum over the image of $f$. That image misses some point $p_0$, because $|L| < |P|$, and $r(p_0) > 0$, because a line through $p_0$ exists. So the right side is less than $\sum_p r(p)$, which is a contradiction. $\square$

This is `Configuration.HasLines.card_le`, and `Configuration.HasPoints.card_le` is the dual. Two of the three conditions `HasLines`, `HasPoints` and $|P| = |L|$ give the third. `Configuration.HasLines.hasPoints` and `Configuration.HasPoints.hasLines` construct the missing class from the equality of the cardinalities. They are definitions and not instances, because they need the hypothesis on the cardinalities.

#### Projective planes

In a projective plane, all points are on the same number of lines (`Configuration.ProjectivePlane.lineCount_eq_lineCount`), and all lines have the same number of points as points have lines (`Configuration.ProjectivePlane.lineCount_eq_pointCount`). The order `Configuration.ProjectivePlane.order P L` is this number minus one. So $r(p) = n + 1$ (`Configuration.ProjectivePlane.lineCount_eq`) and $k(l) = n + 1$ (`Configuration.ProjectivePlane.pointCount_eq`) for the order $n$. The dual plane has the same order (`Configuration.ProjectivePlane.Dual.order`), and $n \ge 2$ (`Configuration.ProjectivePlane.one_lt_order`).

**Theorem.** A finite projective plane of order $n$ has $n^2 + n + 1$ points and $n^2 + n + 1$ lines.

*Proof.* Fix a point $p$. Each other point $q$ is on exactly one line through $p$. There are $n + 1$ lines through $p$, and each has $n$ points other than $p$. So there are $1 + (n + 1)n$ points. The dual plane has the same order, so the count of lines is the same. $\square$

These are `Configuration.ProjectivePlane.card_points` and `Configuration.ProjectivePlane.card_lines`. `Configuration.ProjectivePlane.card_points_eq_card_lines` is the equality $|P| = |L|$, and it comes directly from `card_le` and its dual.

For a field $K$, the library has an instance of `ProjectivePlane` on the projective space of $K^3$, with the points and the lines both given by `ℙ K (Fin 3 → K)`. A point $v$ is on a line $w$ if they are orthogonal for the dot product (`Configuration.ofField.mem_iff`, `Projectivization.orthogonal`). The intersection point and the joining line are both given by the cross product. For the field with $q$ elements this is the plane of order $q$.

#### Incidence systems

The module `Mathlib.Combinatorics.Design.Defs` defines the structure `IncidenceSystem α β`. It has a carrier set `IncidenceSystem.carrier` in `α`, an index set `IncidenceSystem.blockSet` in `β`, and a function `IncidenceSystem.block` from `β` to `Set α`. The axiom `IncidenceSystem.block_subset` says that each indexed block is in the carrier. The index type lets two indices have the same block, so an incidence system can have repeated blocks.

| Lean name | Description |
|---|---|
| `IncidenceSystem.discrete s` | the carrier $s$ and the blocks $\{x\}$ for $x \in s$ |
| `IncidenceSystem.indiscrete s b` | the carrier $s$ and the single block $s$ with the index $b$ |
| `IncidenceSystem.IsSimple` | `block` is injective on `blockSet` |
| `IncidenceSystem.IsUniform d k` | each block has `Set.ncard` equal to $k$ |

The function `IncidenceSystem.ofHypergraph` sends a hypergraph of Section 2 to the incidence system with the edges as blocks, each edge indexed by itself. `IncidenceSystem.toHypergraph` goes back, with the edge set equal to the image of `blockSet` under `block`. It merges the repeated blocks.

**Theorem.** For each hypergraph $H$, `(ofHypergraph H).toHypergraph = H`.

*Proof.* The carrier of `ofHypergraph H` is $V(H)$, and its blocks are the edges of $H$ with the identity as the index function. The image of $E(H)$ under the identity is $E(H)$. So both hypergraphs have the same vertex sets and edge sets. $\square$

This is `IncidenceSystem.toHypergraph_ofHypergraph`. The other round trip changes the index type, so it is not an equality. The systems `ofHypergraph H`, `discrete s` and `indiscrete s b` are simple (`IncidenceSystem.IsSimple.ofHypergraph`, `IncidenceSystem.IsSimple.discrete`, `IncidenceSystem.IsSimple.indiscrete`). The discrete system is $1$-uniform, and the indiscrete system is `s.ncard`-uniform.

**Theorem.** If $d$ is $k$-uniform with $k \ne 0$, then each block is nonempty and finite.

*Proof.* The function `Set.ncard` is $0$ on the empty set and on each infinite set. A block has `ncard` equal to $k \ne 0$, so it is neither. $\square$

These are `IncidenceSystem.IsUniform.nonempty_block` and `IncidenceSystem.IsUniform.finite_block`. The module does not yet define the balanced designs, in which each set of $t$ points is in the same number of blocks.

#### Tiles under a group action

The module `Mathlib.Combinatorics.Tiling.Tile` works with a group $G$ that acts on a space $X$, in the namespace `DiscreteTiling`. A `DiscreteTiling.Prototile G X` has a set `carrier` of points and a subgroup `symmetries` of the stabilizer `MulAction.stabilizer G carrier`. Two images of the tile under elements of $G$ that differ by a symmetry are the same placed tile. A `DiscreteTiling.Protoset G X ιₚ` is an indexed family of prototiles. Two indices can carry equal prototiles, and this models marked tiles.

A `DiscreteTiling.PlacedTile ps` has an index `i` and a left coset $gS$ of the symmetries $S$ of the tile `ps i`, in the field `groupElts`. Its set of points is `DiscreteTiling.PlacedTile.coeSet`, used as a coercion: the placed tile $\langle i, gS \rangle$ is the set $g \cdot \mathrm{ps}(i)$ (`DiscreteTiling.PlacedTile.coe_mk_mk`). This is well defined because each symmetry fixes the carrier as a set. The lemmas `DiscreteTiling.PlacedTile.ext_iff_of_exists` and `DiscreteTiling.PlacedTile.ext_iff_of_preimage` compare two placed tiles without a heterogeneous equality, and `DiscreteTiling.PlacedTile.induction_on` reduces a statement to a pair of an index and a group element.

The group acts on placed tiles by $h \cdot \langle i, gS \rangle = \langle i, hgS \rangle$ (`DiscreteTiling.PlacedTile.smul_mk_mk`). The action does not change the index (`DiscreteTiling.PlacedTile.smul_index`), and it is a `MulAction`.

**Theorem.** $(h \cdot t)$ as a set of points is $h \cdot t$, the image of the set of points of $t$.

*Proof.* Write $t = \langle i, gS \rangle$. Then $h \cdot t = \langle i, hgS \rangle$, and its set of points is $(hg) \cdot \mathrm{ps}(i) = h \cdot (g \cdot \mathrm{ps}(i))$ by the axiom of the action. $\square$

This is `DiscreteTiling.PlacedTile.coe_smul`. With it, `DiscreteTiling.PlacedTile.mem_smul_iff_smul_inv_mem` says that $x \in h \cdot t$ if and only if $h^{-1} \cdot x \in t$. A placed tile is nonempty or finite if and only if its prototile is (`DiscreteTiling.PlacedTile.coe_nonempty_iff`, `DiscreteTiling.PlacedTile.coe_finite_iff`). The module defines the tiles only, and not yet the tilings.

#### Valued constraint satisfaction problems

The module `Mathlib.Combinatorics.Optimization.ValuedCSP` works with a domain $D$ and an ordered additive monoid $C$ of costs. A template `ValuedCSP D C` is a set of cost functions $f : D^n \to C$, each with its arity $n$. A `ValuedCSP.Term Γ ι` applies one function of the template to $n$ of the variables in `ι`, and `ValuedCSP.Term.evalSolution` evaluates it at an assignment $x : ι \to D$. An instance `ValuedCSP.Instance Γ ι` is a multiset of terms, and `ValuedCSP.Instance.evalSolution` is the sum of the values of its terms. The predicate `ValuedCSP.Instance.IsOptimumSolution I x` says that $x$ has the least cost among all assignments.

A fractional operation `FractionalOperation D m` is a multiset $\omega$ of operations $D^m \to D$. It is valid (`FractionalOperation.IsValid`) if it is nonempty, and it is symmetric (`FractionalOperation.IsSymmetric`) if each operation in it gives the same value on two permutations of one tuple. For $m$ tuples $x_1, \ldots, x_m \in D^n$, `FractionalOperation.tt` applies each $g \in \omega$ coordinatewise. The cost function $f$ admits $\omega$ (`Function.AdmitsFractional`) if
$$m \sum_{g \in \omega} f(g(x_1, \ldots, x_m)) \le |\omega| \sum_{i=1}^m f(x_i)$$
for all $x_1, \ldots, x_m$. So the average cost after $\omega$ is at most the average cost before. A fractional polymorphism of $\Gamma$ is admitted by each function of $\Gamma$ (`FractionalOperation.IsFractionalPolymorphismFor`).

A binary $f$ has the Max-Cut property at $a \ne b$ (`Function.HasMaxCutPropertyAt`) if $f(a, b) = f(b, a)$ and the minimum of $f$ is attained exactly at $(a, b)$ and $(b, a)$.

**Theorem.** Let $C$ be an ordered cancellative monoid. A binary cost function with the Max-Cut property admits no valid symmetric fractional operation of arity $2$.

*Proof.* Take $x_1 = (a, b)$ and $x_2 = (b, a)$. For $g \in \omega$, the output is the pair $(g(a, b), g(b, a))$. By symmetry both coordinates are equal to one value $c$. The pair $(c, c)$ is neither $(a, b)$ nor $(b, a)$, because $a \ne b$, so $f(c, c) > f(a, b)$. The multiset $\omega$ is nonempty, so the left side of the inequality is greater than $2 |\omega| f(a, b)$. The right side is $|\omega|(f(a, b) + f(b, a)) = 2|\omega| f(a, b)$. $\square$

This is `Function.HasMaxCutProperty.forbids_commutativeFractionalPolymorphism`. So no template that contains such a function has a symmetric fractional polymorphism of arity $2$.

#### Common errors

1. A learner reads `Configuration.lineCount L p` as the number of points on a line. It is the number of lines through the point $p$, and `pointCount P l` is the number of points on $l$. The explicit arguments `L` and `P` name the type that is counted.
2. A learner uses `IncidenceSystem.IsUniform d 0` for a system with empty blocks only. Each infinite block also has `ncard` equal to $0$, so a $0$-uniform system can have infinite blocks.
3. A learner applies `Configuration.HasLines.hasPoints` with `inferInstance`. It is a definition with the hypothesis $|P| = |L|$, so it must be called with that proof, for example in a `letI`.

### Exercises

1. (A) Show that the Fano plane, with $7$ points and $7$ lines of $3$ points each, is a projective plane of order $2$. Check `Configuration.ProjectivePlane.card_points`.
2. (A) Show that `IncidenceSystem.discrete s` is $1$-uniform and simple. Compute `(discrete s).toHypergraph`.
3. (A) Let $G = \mathbb{Z}$ act on $X = \mathbb{Z}$ by addition, and let the prototile be $\{0, 1\}$ with trivial symmetries. Describe the placed tiles, and find the placed tiles that contain the point $5$.
4. (B) Show that a projective plane of order $n$ has $(n^2 + n + 1)(n + 1)$ incident pairs, with `Configuration.sum_lineCount_eq_sum_pointCount`.
5. (B) Give a nondegenerate configuration with `HasLines P L` and $|P| < |L|$. Why does it not have `HasPoints P L`?
6. (C) Let $D = \{0, 1\}$, $C = \mathbb{N}$ and $f(x, y) = 0$ if $x \ne y$ and $1$ if $x = y$. Show that $f$ has the Max-Cut property. Show directly that the fractional operation $\{\min, \max\}$ is not admitted by $f$.

### Reference

<?reference?>
