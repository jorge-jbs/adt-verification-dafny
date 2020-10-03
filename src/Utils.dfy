function method BigUnion<A>(S: set<set<A>>): set<A>
{
  set X, x | X in S && x in X :: x
}

function method elems<A>(l: array<A>): set<A>
  reads l
{
  set x | x in l[..]
}

function rev<A>(xs: seq<A>): seq<A>
{
  if |xs| == 0 then
    []
  else
    rev(xs[1..]) + [xs[0]]
}
