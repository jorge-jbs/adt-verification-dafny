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
