# Simple graphs

This chapter sets up the objects of the first three chapters of the volume. A simple graph on a set $V$ is a symmetric and irreflexive relation on $V$: two vertices are adjacent or not, a vertex is never adjacent to itself, and there is at most one edge between two vertices. Mathlib takes this as its definition. The structure `SimpleGraph V` holds the relation `Adj`, a proof that it is symmetric and a proof that it is irreflexive. The edges, the neighbours and the degrees are all derived from the relation.

Section 1 defines the neighbour sets, the edge set as a set of unordered pairs, the degree of a vertex, and the complete graph and the empty graph as the top and the bottom of a lattice of graphs. It proves the degree-sum formula: the sum of the degrees is twice the number of edges. The proof counts darts, that is edges with a direction, in two ways. The handshake lemma follows: the number of vertices of odd degree is even. The running example is the Petersen graph, which this chapter and the next two use again and again.

Section 2 studies the ways to compare two graphs. It defines subgraphs, induced subgraphs and the deletion of edges, then homomorphisms, embeddings and isomorphisms, and the notion of a copy of one graph inside another. It ends with the adjacency matrix. The matrix is symmetric, its trace is zero, and the diagonal of its square holds the degrees. The entries of its powers count walks, which Chapter 2 defines.

Section 3 collects the constructions of new graphs: box products, disjoint sums, the addition of an edge and the replacement of a vertex, line graphs, Cayley and circulant graphs, Hasse diagrams and path graphs, star graphs, unit-distance embeddings and strongly regular graphs.

The chapter needs finite sets, finite types and big operators from Volume 3, Chapters 3, 4 and 6, and lattices from Volume 4, Chapter 3. Section 2 uses matrices from Volume 7, Chapter 3. Chapter 2 builds walks and connectivity on these definitions, and Chapter 3 builds colourings and cliques.
