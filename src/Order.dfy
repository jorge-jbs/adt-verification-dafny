predicate isPreorder<A(!new)>(le: (A, A) -> bool)
{
  (forall a :: le(a, a)) &&
  (forall a, b, c | le(a, b) && le(b, c) :: le(a, c))
}

predicate isTotalPreorder<A(!new)>(le: (A, A) -> bool)
{
  isPreorder(le) &&
  (forall a, b :: le(a, b) || le(b, a))
}

predicate isPartialOrder<A(!new)>(le: (A, A) -> bool)
{
  (forall a :: le(a, a)) &&
  (forall a, b | le(a, b) && le(b, a) :: a == b) &&
  (forall a, b, c | le(a, b) && le(b, c) :: le(a, c))
}

predicate isTotalOrder<A(!new)>(le: (A, A) -> bool)
{
  isTotalPreorder(le) &&
  (forall a, b | le(a, b) && le(b, a) :: a == b)
}

lemma partialOrderAndTotalPreorder<A(!new)>(le: (A, A) -> bool)
  requires isTotalPreorder(le)
  requires isPartialOrder(le)
  ensures isTotalOrder(le)
{
}

predicate Ordered<A>(xs: seq<A>, le: (A, A) -> bool)
  requires isTotalOrder(le)
{
  forall i | 0 <= i < |xs|-1 :: le(xs[i], xs[i+1])
}

predicate OrderedInt(xs: seq<int>)
{
  forall i | 0 <= i < |xs|-1 :: xs[i] < xs[i+1]
}
