predicate IsPreorder<A>(le: (A, A) -> bool, s:set<A>)
{
  (forall a | a in s :: le(a, a)) &&
  (forall a, b, c | a in s && b in s && c in s && le(a, b) && le(b, c) :: le(a, c))
}

predicate IsTotalPreorder<A>(le: (A, A) -> bool, s:set<A>)
{
  IsPreorder(le,s) &&
  (forall a, b | a in s && b in s :: le(a, b) || le(b, a))
}

predicate IsPartialOrder<A>(le: (A, A) -> bool, s:set<A>)
{
  (forall a | a in s :: le(a, a)) &&
  (forall a, b | a in s && b in s && le(a, b) && le(b, a) :: a == b) &&
  (forall a, b, c | a in s && b in s && c in s && le(a, b) && le(b, c) :: le(a, c))
}

predicate IsTotalOrder<A>(le: (A, A) -> bool, s:set<A>)
{
  IsTotalPreorder(le,s) &&
  (forall a, b | a in s && b in s && le(a, b) && le(b, a) :: a == b)
}

lemma PartialOrderAndTotalPreorder<A>(le: (A, A) -> bool, s:set<A>)
  requires IsTotalPreorder(le,s)
  requires IsPartialOrder(le,s)
  ensures IsTotalOrder(le,s)
{
}

predicate Ordered<A>(xs: seq<A>, le: (A, A) -> bool)
  requires IsTotalOrder(le,(set x | x in xs))
{
  forall i, j | 0 <= i < j < |xs| :: le(xs[i], xs[j])
}

predicate OrderedInt(xs: seq<int>)
{
  //forall i, j | 0 <= i < j < |xs| :: xs[i] < xs[j]
  Ordered<int>(xs,(x,y) => x<= y)
}

