# Walks, connectivity and trees

This chapter studies how a graph holds together. Its basic object is a walk: a finite sequence of vertices in which each vertex is adjacent to the next. Mathlib defines a walk from $u$ to $v$ as an inductive type with two constructors, the empty walk at a vertex and a step followed by a walk. Most proofs about walks are inductions along this definition. Trails, paths and cycles are walks with conditions on the repetition of edges and vertices.

Section 1 defines walks and their length, their vertices and their edges, the operations of reversal and concatenation, and the trails, paths and cycles. It shows that each walk contains a path with the same ends. It then proves the theorem of Euler: a finite connected graph has a closed trail through every edge if and only if each degree is even. The index has the necessary direction of this theorem, and the section proves both.

Section 2 defines reachability, connected graphs and connected components. Reachability is an equivalence relation, and its classes are the components. The section defines the distance between two vertices as the length of a shortest walk, proves the triangle inequality, and studies the eccentricity, the radius and the diameter. The Petersen graph has diameter 2.

Section 3 studies acyclic graphs and trees. It proves that a graph is a tree if and only if any two vertices are joined by exactly one path, that a tree on $n$ vertices has $n - 1$ edges, that a finite tree with at least two vertices has at least two leaves, and that each finite connected graph has a spanning tree. Trees are bipartite, which leads to Chapter 3.

Section 4 is the API of walks: the vertices of a walk by position, maps of walks along homomorphisms and inclusions, the cut of a walk at a vertex and the rotation of closed walks, subwalks, the finite sets of walks of a given length, and chordless walks.

Section 5 defines Hamiltonian paths and cycles and Hamiltonian graphs, the cycle graphs $C_n$ on `Fin n`, and the girth, and proves that the girth is at most $2\operatorname{diam} + 1$.

Section 6 studies connected subgraphs and induced subgraphs, odd components and sets of representatives for Tutte's theorem, $k$-edge-connectivity and bridges, and the ends of infinite graphs.

The chapter needs Chapter 1 and the finite sets and lists of Volume 3. Chapter 3 uses walks for its proof that a graph is bipartite if and only if it has no odd cycle. The other chapters use connectivity and paths where they need them.
