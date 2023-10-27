include "../../src/List/ListSpec.dfy"
include "../../src/ArrayList/ArrayListImpl.dfy"
//include "../src/LinkedList/LinkedListImpl.dfy"

module ListOfObjects{
  import opened ListSpec
  import opened ArrayListImpl

  
method ListOfObjects() returns (l: List<object>)
  ensures l.Valid()
  ensures l.Model() == [l, l]
  ensures fresh(l.Repr())
  ensures allocated(l.Repr())
{
  //l := new LinkedListImpl();
  l := new ArrayListImpl();
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

}