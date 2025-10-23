# `NThese`: A heterogeneous, n-ary generalisation of `These`

`NThese` is an n-ary generalisation of the [`These`](https://hackage.haskell.org/package/these/docs/Data-These.html#t:These) datatype,
written in [`sop-core`](https://hackage.haskell.org/package/sop-core) style.

`NThese f as` is parametrised by a type constructor `f` and a type level list `as` of types.
`NThese f [a1, a2, a3, ...]` contains at least one of `f a1`, `f a2`, and so on,
and potentially all of them.
As such, it populates a middle ground between the n-ary product `NP` (which contains exactly `n` elements)
and the n-ary sum `NS` (which contains exacty 1 element).

The library provides generalisations of [`align`](https://hackage.haskell.org/package/semialign/docs/Data-Semialign.html#v:align)
and [`unalign`](https://hackage.haskell.org/package/semialign/docs/Data-Semialign.html#v:unalign)
from the [`semialign`](https://hackage.haskell.org/package/semialign) package,
and implementations of the typical type classes from `sop-core` to traverse and combine `NThese` structures.
