# Colourings, cliques and extremal graphs

This chapter studies two opposite kinds of structure in a graph. A colouring splits the vertices into classes with no edge inside a class, and the chromatic number is the least number of classes that suffices. A clique is a set of vertices with every edge inside it. A clique of size $k$ needs $k$ colours, so cliques give lower bounds for the chromatic number. The bound is not sharp: the five-cycle and the Petersen graph have no triangle but need three colours.

Section 1 defines colourings as homomorphisms to a complete graph, following Mathlib, and the chromatic number as a value in $\mathbb{N} \cup \{\infty\}$. It computes the chromatic numbers of complete graphs, paths, cycles and the Petersen graph. It proves that a graph is bipartite if and only if it has no closed walk of odd length, the theorem of König, and that a bipartite graph on $n$ vertices has at most $n^2/4$ edges. It proves the greedy bound $\chi(G) \le \Delta(G) + 1$, which the index of this edition does not have.

Section 2 defines cliques, $n$-cliques, clique-free graphs and independent sets. It then asks how many edges a graph on $n$ vertices can have without a clique of size $r + 1$. The answer is the theorem of Turán: the maximum is attained by the complete $r$-partite graph with parts as equal as possible, and only by it. The case $r = 2$ is the theorem of Mantel, with the bound $n^2/4$ for triangle-free graphs. The section proves Mantel by double counting and Turán by the symmetrisation of Zykov, and introduces the extremal numbers $\operatorname{ex}(n, H)$ of Mathlib.

Section 3 studies complete multipartite graphs: their characterization by the transitivity of non-adjacency, the five-wheel-like structures behind the theorem of Andrásfai, Erdős and Sós, and the asymptotic extremal results: the Turán density, the Zarankiewicz function and the minimum-degree form of the Erdős-Stone theorem.

The chapter needs Chapters 1 and 2, in particular walks and connected components. Chapter 5 returns to cliques and independent sets in Ramsey theory, and Chapter 6 uses triangle-free graphs in the removal lemma.
