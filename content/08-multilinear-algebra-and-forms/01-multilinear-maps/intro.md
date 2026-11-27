# Bilinear, multilinear and alternating maps

Linear algebra studies maps that are linear in one vector. Many maps of interest take several vectors and are linear in each of them separately: the product in a ring, the dot product, the evaluation of a linear form, the composition of linear maps and the determinant of the columns of a matrix. This chapter is the general theory of such maps over a commutative ring.

Section 1 treats bilinear maps. It shows the curried form that Mathlib uses, where a bilinear map $M \times N \to P$ is a linear map $M \to \operatorname{Hom}(N, P)$, and it proves that a bilinear map on free modules is a matrix. Section 2 treats multilinear maps of any finite number of arguments. Its main tool is the expansion of a multilinear map on sums, which gives the values on free modules and the dimension of the space of multilinear maps. Section 3 treats alternating maps, which vanish when two arguments are equal. It proves the sign rule for permutations, builds the alternatization and the product of two alternating forms, and shows that on a free module of rank $n$ each alternating map of $n$ arguments is a multiple of the determinant.

The chapter needs modules, linear maps and bases from Volume 7, Chapters 1 and 2, the determinant from Volume 7, Chapter 4, and the sign of a permutation from Volume 5, Chapter 7.

Chapter 2 builds the tensor product, the module on which bilinear maps become linear maps. Chapters 3 and 4 do the same for multilinear and alternating maps: tensor powers and the tensor algebra turn multilinear maps into linear maps, and the exterior algebra does it for alternating maps. Chapter 5 studies the bilinear forms $M \times M \to R$ and the sesquilinear forms in detail.
