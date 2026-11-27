# Algebra

This chapter is about the tactics for the algebra of rings and fields: `ring`, `ring_nf`, `linear_combination`, `field_simp`, `positivity`, `gcongr`, and the `calc` block that puts their steps into a chain. They prove the identities and the inequalities that a mathematician writes as "by a short computation" or "since each term is positive".

The first section proves the theorem that makes `ring` a decision procedure: an identity holds in all commutative rings if and only if the two sides have the same normal form as polynomials. It also explains `linear_combination` as the check of a certificate of membership in an ideal. The second section is about fractions and signs: the rules that `field_simp`, `positivity` and `gcongr` use, and the side conditions that come with them. The third section is about `calc`, the form of a proof by a chain of relations.

The chapter needs Chapter 1, because the tactics of this chapter often follow a `rw` or a `push_cast`. It prepares Chapter 3: `linarith` and `nlinarith` use the normal form of `ring` to compare the hypotheses, and a proof by `calc` often has a step that `linarith` closes.
