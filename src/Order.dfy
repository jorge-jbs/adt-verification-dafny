module Order{

ghost predicate IsPreorder<A(!new)>(le: (A, A) -> bool)
{
  (forall a :: le(a, a)) &&
  (forall a, b, c | le(a, b) && le(b, c) :: le(a, c))
}

ghost predicate IsStrictPreorder<A(!new)>(ls: (A, A) -> bool)
{
  (forall a :: !ls(a, a)) &&
  (forall a, b, c | ls(a, b) && ls(b, c) :: ls(a, c))
}

ghost predicate IsTotalPreorder<A(!new)>(le: (A, A) -> bool)
{
  IsPreorder(le) &&
  (forall a, b :: le(a, b) || le(b, a))
}

ghost predicate IsPartialOrder<A(!new)>(le: (A, A) -> bool)
{
  (forall a :: le(a, a)) &&
  (forall a, b | le(a, b) && le(b, a) :: a == b) &&
  (forall a, b, c | le(a, b) && le(b, c) :: le(a, c))
}

ghost predicate IsTotalOrder<A(!new)>(le: (A, A) -> bool)
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

ghost predicate Ordered<A>(xs: seq<A>, le: (A, A) -> bool)
  requires IsTotalOrder(le)
{
  forall i, j | 0 <= i < j < |xs| :: le(xs[i], xs[j])
}

ghost predicate StrictOrdered<A>(xs: seq<A>, ls: (A, A) -> bool)
  requires IsStrictPreorder(ls)
{
  forall i, j | 0 <= i < j < |xs| :: ls(xs[i], xs[j])
}
ghost predicate OrderedInt(xs: seq<int>)
{
  //forall i, j | 0 <= i < j < |xs| :: xs[i] < xs[j]
  Ordered<int>(xs,(x,y) => x<= y)
}
ghost predicate StrictOrderedInt(xs: seq<int>)
{
  StrictOrdered<int>(xs,(x,y) => x < y)
}

//Versiones simples y equivalentes 
ghost predicate Sorted(xs:seq<int>)
{ forall i, j | 0 <= i < j < |xs| :: xs[i] <= xs[j]}


ghost predicate StrictSorted(xs:seq<int>)
{ forall i,j | 0 <= i < j < |xs| :: xs[i]<xs[j]}
 
lemma OrderEquiv(xs:seq<int>)
ensures Sorted(xs) <==> OrderedInt(xs)
{}

lemma StrictOrderEquiv(xs:seq<int>)
ensures StrictSorted(xs) <==> StrictOrderedInt(xs)
{}

}
