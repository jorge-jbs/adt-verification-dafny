predicate IsPreorder<A(!new)>(le: (A, A) -> bool)
{
  (forall a :: le(a, a)) &&
  (forall a, b, c | le(a, b) && le(b, c) :: le(a, c))
}

predicate IsTotalPreorder<A(!new)>(le: (A, A) -> bool)
{
  IsPreorder(le) &&
  (forall a, b :: le(a, b) || le(b, a))
}

predicate IsPartialOrder<A(!new)>(le: (A, A) -> bool)
{
  (forall a :: le(a, a)) &&
  (forall a, b | le(a, b) && le(b, a) :: a == b) &&
  (forall a, b, c | le(a, b) && le(b, c) :: le(a, c))
}

predicate IsTotalOrder<A(!new)>(le: (A, A) -> bool)
{
  IsTotalPreorder(le) &&
  (forall a, b | le(a, b) && le(b, a) :: a == b)
}

lemma PartialOrderAndTotalPreorder<A(!new)>(le: (A, A) -> bool)
  requires IsTotalPreorder(le)
  requires IsPartialOrder(le)
  ensures IsTotalOrder(le)
{
}

predicate Ordered<A>(xs: seq<A>, le: (A, A) -> bool)
  requires IsTotalOrder(le)
{
  forall i, j | 0 <= i < j < |xs| :: le(xs[i], xs[j])
}

predicate OrderedInt(xs: seq<int>)
{
  //forall i, j | 0 <= i < j < |xs| :: xs[i] < xs[j]
  Ordered<int>(xs,(x,y) => x<= y)
}

