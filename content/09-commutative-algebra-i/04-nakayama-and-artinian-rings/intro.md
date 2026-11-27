# Nakayama's lemma and Artinian rings

This chapter has two subjects that meet in the last section. The first is Nakayama's lemma, a statement about finitely generated modules over a ring with a given Jacobson radical. The second is the class of Artinian rings, the rings in which every descending chain of ideals stops.

Section 1 proves the determinant trick: an endomorphism $\varphi$ of a finitely generated module with $\varphi(M) \subseteq IM$ satisfies a monic equation with coefficients in the powers of $I$. Nakayama's lemma follows: if $I$ lies in the Jacobson radical and $IM = M$, then $M = 0$. The same trick proves the theorem of Vasconcelos that a surjective endomorphism of a finitely generated module is injective.

Section 2 defines Artinian modules and rings, and proves the three basic facts about an Artinian ring: every prime ideal is maximal, there are finitely many maximal ideals, and the Jacobson radical is nilpotent. Finite rings and finite-dimensional algebras over a field are the main examples. The Prüfer group shows that an Artinian module need not be Noetherian.

Section 3 proves that an Artinian ring is a finite product of local Artinian rings, and the theorem of Akizuki and Hopkins: a ring is Artinian exactly when it is Noetherian and every prime ideal is maximal. So Artinian rings are the Noetherian rings of dimension $0$, the rings whose spectrum is a finite discrete set of points.

The chapter needs the Jacobson radical, the nilradical and the Chinese remainder theorem of Chapter 1, the local rings and the spectrum of Chapter 2, and the Noetherian rings and primary decomposition of Chapter 3. It also uses Volume 7, Chapters 1, 2 and 4. Volume 10 continues with the Krull dimension, the length of a module and the Krull intersection theorem.

In Mathlib the Nakayama lemmas are stated for submodules with the ideal `Ring.jacobson R`, and the Artinian theory copies the Noetherian one with `WellFoundedLT` in place of `WellFoundedGT`.
