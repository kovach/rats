We can "differentiate" a query by an atom
The derivative is a set of queries that update the query result when passed a new tuple:
  if D is a database, Q a query, t a tuple, and Q(D) is the result of applying a query to a database, then
    Q(D+t) = Q(D) + delta(Q,t)(D)

Example
  query = (p A B, q B C)
  suppose we differentiate by `p a b`
  the diff is: \D -> for (q b C in D) {A=a,B=b,C}

Example
query = (p A B, p B C)
suppose we differentiate by `p x y`
the diff is:
  for (p y C in D) {A=x,B=y,C} +
  for (p A x in D) {A,B=x,C=y} +
  if (x=y) {A=x,B=x,C=x}

  - Note: the third case is the case where we unify `p x y` with both atoms in the query.
    so we unify `A=x, B=y` and simultaneously `B=x, C=y`, forcing x=y as a precondition

Note that if we think of the terms in the atom to differentiate by as being special variables, the end result we get is a symbolic expression.
When we actually get a `p` tuple, we can substitute its values for (x,y) and then iterate D to get the bindings.

This is a shorthand version of how to differentiate:
```
  single-atom case:
    d[p x y](p X Y) = [{X=x,Y=y}]
    d[p x y](q _ _) = [] (assuming p != q)
    d[p x y](! ...) = [] (ignore negative literals)
  join case:
    d[atom](x * y) = d[atom](x) * y + x * d[atom](y) + d[atom](x) * d[atom](y)
```
