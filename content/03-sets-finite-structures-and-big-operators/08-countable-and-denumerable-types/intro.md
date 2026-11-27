# Countable and denumerable types

After the finite types come the countable types: the types with an injective map to $\mathbb{N}$. A countable set can be listed as a sequence, and the closure rules of countability are the ones that measure theory and topology use most: subsets, images, finite products and countable unions of countable sets are countable.

Section 1 defines the class `Countable` and the predicate `Set.Countable`, proves that an injection into $\mathbb{N}$ and a surjection from $\mathbb{N}$ give the same notion, computes the pairing function `Nat.pair` of $\mathbb{N} \times \mathbb{N}$, and proves the closure rules, with $\mathbb{Z}$, $\mathbb{Q}$ and the finite subsets of $\mathbb{N}$ as examples. Section 2 proves the theorem of Cantor, the uncountability of the binary sequences and of the real numbers, and the fact that each countably infinite type is in bijection with $\mathbb{N}$. It explains the data classes `Encodable` and `Denumerable` next to the proposition `Countable`.

The chapter needs the finite and infinite sets of Chapter 5. The cardinals of the volume on set theory measure the sizes beyond the countable one, and the volumes on measure theory and topology use the countable unions of this chapter.
