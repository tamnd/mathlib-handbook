# Well-orders and ordinals

A cardinal measures the size of a set and forgets all structure. An ordinal measures the length of a well-order. Two well-orders have the same ordinal when there is an order isomorphism between them. The ordinals continue the counting numbers past the finite: after $0, 1, 2, \dots$ comes $\omega$, then $\omega + 1$, and so on without end.

Section 1 studies well-orders, initial segments and principal segments. It proves that an isomorphism of well-orders is unique when it exists, and it defines an ordinal as the type of a well-order up to isomorphism. It defines the order on the ordinals, the position `typein` of an element in its well-order, the cardinal of an ordinal and the least ordinal `Cardinal.ord` of a cardinal. Section 2 takes the ordinals of one universe as a single well-ordered type. A small family of ordinals has a supremum, but the type of all ordinals is not small: this is the paradox of Burali-Forti, which Lean meets with universes. The section ends with the rank of a well-founded relation and with transfinite induction and recursion in three cases: zero, successor and limit.

The chapter needs Volume 4 for well-founded relations and order isomorphisms, and Section 1 of Chapter 1 for cardinals. Chapter 3 defines the arithmetic of the ordinals by the recursion of Section 2.
