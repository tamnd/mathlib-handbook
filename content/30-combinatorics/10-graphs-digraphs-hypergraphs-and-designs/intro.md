# Graphs with edge sets, digraphs, hypergraphs and designs

The simple graphs of Chapters 1 to 4 have no loops, no parallel edges and no names for their edges. This chapter describes the other incidence structures of the combinatorics library: graphs with an explicit edge set, directed graphs, hypergraphs, configurations of points and lines, incidence systems, tiles under a group action and valued constraint problems. Most of these modules are young and give definitions with a short API, so the three sections are reference sections.

Section 1 describes the type `Graph α β` of graphs with a vertex set, an edge set and an incidence relation, which allows loops and parallel edges. It treats the spanning, induced and closed subgraphs, the deletion of edges and vertices, the intersection of two graphs, the images under maps of vertices, the comparison with `SimpleGraph`, and the edge cuts, bridges and bonds.

Section 2 describes the digraphs, which are relations on a type and form a complete atomic Boolean algebra, and the two ways to forget the orientation of a digraph. It then describes the hypergraphs, with edges that are arbitrary subsets of the vertex set, and their isolated vertices, loops, trivial, complete and linear hypergraphs, and images.

Section 3 describes four small modules. It proves the counting theorems for configurations of points and lines and the count $n^2 + n + 1$ of the points of a finite projective plane of order $n$. It then describes incidence systems with indexed blocks, prototiles and placed tiles under a group action, and valued constraint satisfaction problems with the theorem that a Max-Cut cost function has no symmetric binary fractional polymorphism.

All sections need finite sets from Volume 3, Chapter 3, and the simple graphs of Chapter 1. Section 1 also uses the connectivity of Chapter 2 and the lattices of Volume 4, Chapter 3. Section 3 uses finite types and big operators from Volume 3, Chapters 4 and 6, the theorem of Hall from Chapter 4, cosets and group actions from Volume 5, Chapters 4 and 6, and the set families of Chapter 7. The level is a first undergraduate course in combinatorics.
