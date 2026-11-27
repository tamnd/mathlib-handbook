# Flows and limit sets

Chapter 1 iterated one map. A flow gathers all times into one object: a jointly continuous action of a topological monoid of times, such as $\mathbb{N}$, $\mathbb{Z}$ or $\mathbb{R}$, on a topological space. The iterates of a continuous map, the powers of a homeomorphism and the solutions of an autonomous differential equation are all flows, and Mathlib treats them with one structure, `Flow`.

Section 1 defines flows, invariant and forward invariant sets, orbits and the maps between flows: semiconjugacies and factors. It shows that the time maps of a flow of a group are homeomorphisms, that closures of invariant sets are invariant, and how flows of $\mathbb{N}$ and $\mathbb{Z}$ come from a single map. The linear equation $x' = ax$ is the running example. Section 2 studies the $\omega$-limit set, the set of points that an orbit approaches again and again. On a compact space it is closed, nonempty and invariant, and it absorbs the orbit: every open set that contains it eventually contains the orbit. For flows of $\mathbb{R}$ it is also connected; the section proves this on paper, since the index has no declaration for it, and treats a planar limit cycle.

The chapter needs Volume 13 for filters, compactness and connectedness, and Chapter 1 for fixed points, periodic points and semiconjugacies. Chapter 3 uses its invariant sets to define minimal systems.
