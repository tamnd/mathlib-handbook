# Operations on sets

The sets of a type form a Boolean algebra, and the laws of this algebra are the laws of logic applied to one point at a time. This chapter makes that idea precise and uses it to prove the standard identities of sets.

The first section treats the union, the intersection, the complement and the difference of two sets, and the image and the preimage of a set under a function. Its main theorem is the adjunction $f(s) \subseteq t \iff s \subseteq f^{-1}(t)$. The adjunction explains why the preimage keeps every Boolean operation while the image keeps only the unions, and why some identities need an injective or a surjective function.

The second section passes to families of sets: the indexed union and intersection, the laws of De Morgan for families, the pairwise disjoint families and the partitions. It proves that the classes of an equivalence relation form a partition, and that the fibers of a function form one.

The chapter needs Chapter 2 and Chapter 3 of Volume 1: sets as predicates, subtypes, functions, and equivalence relations. In Lean, each operation has a membership lemma, so `simp` can reduce a statement about sets to a statement of logic. The next chapters use this chapter all the time. Chapter 2 uses the quotient by an equivalence relation to make multisets. Chapter 3 counts the elements of a finite union. Chapter 6 cuts a finite set into the fibers of a function and adds the sums over the pieces. Chapter 8 proves that a countable union of countable sets is countable.
