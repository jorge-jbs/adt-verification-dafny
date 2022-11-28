include "../src/linear/layer1/List.dfy"
include "../src/linear/layer3/LinkedListImpl.dfy"

method ListOfObjects() returns (l: List<object>)
  ensures l.Valid()
  ensures l.Model() == [l, l]
  ensures fresh(l.Repr())
  ensures allocated(l.Repr())
{
  l := new LinkedListImpl();
  l.PushBack(l);
  assert l.Valid();
  assert |l.Model()| == 1;
  assert l.Model() == [l];
  var o: object := l.Front();
  assert o == l;
  assert o is List<object>;
  var l' := o as List<object>;
  l'.PushBack(l);  // We could write: l'.PushBack(l');
}
